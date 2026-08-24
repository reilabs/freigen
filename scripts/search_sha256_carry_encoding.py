#!/usr/bin/env python3
"""Analyze six-bit affine encodings of coupled SHA-256 carries.

The current fused schedule/round block has carries

    qW in [0,3], qE in [0,5], qA in [0,3].

The first check deterministically constructs and re-evaluates concrete 32-bit
SHA witnesses until it has certificates for 65 distinct carry triples.  More
than 64 reachable triples rules out every carry-only six-bit encoding,
independently of how its affine decoder is chosen.

The second part exhaustively enumerates the relaxed 32-bit word-range relation.
After eliminating the source words, feasibility is a conjunction of vertical,
horizontal, and diagonal half-planes in two integer variables.  Testing the
boundaries, their intersections, and one integer point on either side visits
every cell of that arrangement.  It then asks whether the 11-state E/A factor
of a maximal shape fits in an affine image of four Boolean bits.  The two
ordinary qW bits then give a six-bit conditional encoding:

    base + b0*v0 + ... + b5*v5.

This synthesis is also finite and exhaustive.  The selected E/A instance has
11 target points.  Any four-bit map covering them assigns fewer than 8 of its
16 Boolean inputs outside the target set.  For each generator vi, the Boolean
cube has 8 edges in direction vi, so at least one edge has both endpoints in
the target set.  Consequently every vi is a difference of two target points.
At least one Boolean input maps to a target; complementing input coordinates
makes that point the base.  It is therefore complete to enumerate bases in S
and generators in S-S, which is exactly what the SMT query below does.

The third part enumerates every sign- and order-normalized four-generator
family allowed by that difference argument and minimizes a constant base
dictionary over all output-conditioned E/A shapes.  Finally, a direct
fully-coupled construction covers the entire carry union with six cube bits
and one base-selection bit.  Together with the 65-state lower bound, this
shows that a witnessed affine carry encoding needs exactly seven bits: it can
change basis, but it cannot improve on the current witness count.

Run with a Z3 executable on PATH, for example:

    nix shell nixpkgs#z3 -c python3 scripts/search_sha256_carry_encoding.py
"""

from __future__ import annotations

import re
import shutil
import subprocess
import sys
from itertools import combinations, combinations_with_replacement, product
from random import Random


B = 1 << 32
K0 = 0x428A2F98


MASK = B - 1


def ror(x: int, n: int) -> int:
    return ((x >> n) | (x << (32 - n))) & MASK


def concrete_carries(words: list[int]) -> tuple[int, int, int]:
    w0, w1, w2, w3, a, b, c, d, e, f, g, h = words
    ss0 = ror(w1, 7) ^ ror(w1, 18) ^ (w1 >> 3)
    ss1 = ror(w3, 17) ^ ror(w3, 19) ^ (w3 >> 10)
    swide = w0 + ss0 + w2 + ss1
    w, qw = swide & MASK, swide >> 32
    big_s1 = ror(e, 6) ^ ror(e, 11) ^ ror(e, 25)
    ch = (e & f) ^ ((~e) & g) & MASK
    ewide = d + h + big_s1 + K0 + w + ch
    new_e, qe = ewide & MASK, ewide >> 32
    big_s0 = ror(a, 2) ^ ror(a, 13) ^ ror(a, 22)
    maj = (a & b) ^ (a & c) ^ (b & c)
    awide = new_e + big_s0 + maj - d + B
    return qw, qe, awide >> 32


def concrete_certificate() -> set[tuple[int, int, int]]:
    rng = Random(0)
    result: set[tuple[int, int, int]] = set()
    for _ in range(2_000_000):
        result.add(concrete_carries([rng.getrandbits(32) for _ in range(12)]))
        if len(result) >= 65:
            return result
    raise RuntimeError("deterministic search did not recover 65 concrete triples")


def relaxed_points(
    size: int, k: int, w: int, e: int, a: int,
) -> tuple[tuple[int, int, int], ...]:
    base = 1 << size
    result = []
    for qw, qe, qa in product(range(4), range(6), range(4)):
        if not 0 <= w + base * qw <= 4 * (base - 1):
            continue
        target = e - w - k + base * qe
        d_lo, d_hi = max(0, target - 3 * (base - 1)), min(base - 1, target)
        offset = a - e - base + base * qa
        a_lo, a_hi = max(0, -offset), min(base - 1, 2 * (base - 1) - offset)
        if max(d_lo, a_lo) <= min(d_hi, a_hi):
            result.append((qw, qe, qa))
    return tuple(result)


def exact_shapes(base: int) -> set[tuple[tuple[int, int, int], ...]]:
    """Enumerate every relaxed output-conditioned carry shape exactly.

    Write t = e-w-k and u = a-e-B.  For fixed (qe, qa), eliminating d gives

      0 <= t+B*qe <= 4(B-1)
      -(B-1) <= u+B*qa <= 2(B-1)
      0 <= t+u+B*(qe+qa) <= 5(B-1).

    These predicates only change at finitely many vertical, horizontal, and
    diagonal boundaries.  The two w ranges distinguish whether qW=3 is
    possible.  Their realizability conditions have the same three slopes.
    """
    vertical: set[int] = set()
    horizontal: set[int] = {-2 * base + 1, -1}
    diagonal: set[int] = set()
    for qe, qa in product(range(6), range(4)):
        vertical.update((-base * qe, 4 * (base - 1) - base * qe))
        horizontal.update((-(base - 1) - base * qa,
                           2 * (base - 1) - base * qa))
        diagonal.update((-base * (qe + qa),
                         5 * (base - 1) - base * (qe + qa)))

    # w <= B-4 permits all qW values; the final three w values forbid qW=3.
    categories = ((0, base - 4, range(4)),
                  (base - 3, base - 1, range(3)))
    for lo, hi, _ in categories:
        vertical.update((-hi - base + 1, base - 1 - lo))
        diagonal.update((-2 * base - hi + 1, -1 - lo))

    # Intersections of diagonal and horizontal boundaries are precisely the
    # t-values where their order can change.
    t_boundaries = vertical | {d - h for d in diagonal for h in horizontal}
    t_candidates = {t + delta for t in t_boundaries for delta in (-1, 0, 1)}
    shapes: set[tuple[tuple[int, int, int], ...]] = set()

    for t in t_candidates:
        u_boundaries = horizontal | {d - t for d in diagonal}
        u_candidates = {u + delta for u in u_boundaries for delta in (-1, 0, 1)}
        for u in u_candidates:
            pairs = tuple(
                (qe, qa) for qe, qa in product(range(6), range(4))
                if 0 <= t + base * qe <= 4 * (base - 1)
                and -(base - 1) <= u + base * qa <= 2 * (base - 1)
                and 0 <= t + u + base * (qe + qa) <= 5 * (base - 1)
            )
            for lo, hi, qws in categories:
                # This is the nonempty intersection condition after
                # eliminating e, a, k, and w constrained to [lo, hi].
                if (-2 * base + 1 <= u <= -1
                        and -hi - base + 1 <= t <= base - 1 - lo
                        and -2 * base - hi + 1 <= t + u <= -1 - lo):
                    shapes.add(tuple((qw, qe, qa) for qw in qws
                                     for qe, qa in pairs))
    return shapes


def brute_shapes(base: int) -> set[tuple[tuple[int, int, int], ...]]:
    """Reference enumeration used to check the arrangement algorithm."""
    shapes = set()
    for k, w, e, a in product(range(base), repeat=4):
        qws = tuple(qw for qw in range(4)
                    if w + base * qw <= 4 * (base - 1))
        points = relaxed_points(base.bit_length() - 1, k, w, e, a)
        block_size = len(points) // len(qws)
        pairs = tuple((qe, qa) for _, qe, qa in points[:block_size])
        # relaxed_points is ordered qW-major; extract the first qW block.
        shapes.add(tuple((qw, qe, qa) for qw in qws for qe, qa in pairs))
    return shapes


def covering_bases(
    points: frozenset[tuple[int, int]],
    generators: tuple[tuple[int, int], ...],
) -> set[tuple[int, int]]:
    offsets = {
        tuple(sum(bits[j] * generators[j][c] for j in range(len(generators)))
              for c in range(2))
        for bits in product((0, 1), repeat=len(generators))
    }
    candidates: set[tuple[int, int]] | None = None
    for point in points:
        point_candidates = {(point[0] - v[0], point[1] - v[1])
                            for v in offsets}
        candidates = (point_candidates if candidates is None
                      else candidates & point_candidates)
    return candidates or set()


def minimum_base_cover(
    covers: tuple[frozenset[tuple[int, int]], ...],
) -> tuple[tuple[int, int], ...]:
    """Find a minimum set of bases intersecting every per-shape base set."""
    unique = tuple(sorted(set(covers), key=len))
    universe = sorted(set().union(*unique))
    for size in range(1, len(universe) + 1):
        for selected in combinations(universe, size):
            selected_set = set(selected)
            if all(selected_set & candidates for candidates in unique):
                return selected
    raise AssertionError("all nonempty finite covers have a hitting set")


def exhaustive_generator_search(
    pair_shapes: set[frozenset[tuple[int, int]]],
    maximal: frozenset[tuple[int, int]],
) -> tuple[int, tuple[tuple[int, int], ...], tuple[tuple[int, int], ...], int]:
    """Minimize the base dictionary over every complete generator candidate."""
    differences = {tuple(x - y for x, y in zip(p, q))
                   for p in maximal for q in maximal}

    def canonical(vector: tuple[int, int]) -> tuple[int, int]:
        negative = (-vector[0], -vector[1])
        return min(vector, negative)

    # Generator order is immaterial, and changing a generator's sign merely
    # complements its Boolean coordinate and translates the base.
    candidates = sorted({canonical(vector) for vector in differences})
    best: tuple[int, tuple[tuple[int, int], ...],
                tuple[tuple[int, int], ...]] | None = None
    viable = 0
    for generators in combinations_with_replacement(candidates, 4):
        if not covering_bases(maximal, generators):
            continue
        covers = tuple(frozenset(covering_bases(shape, generators))
                       for shape in pair_shapes)
        if not all(covers):
            continue
        viable += 1
        dictionary = minimum_base_cover(covers)
        result = (len(dictionary), generators, dictionary)
        if best is None or result < best:
            best = result
    if best is None:
        raise AssertionError("the synthesized generator family must be viable")
    return best[0], best[1], best[2], viable


def smt_query(points: tuple[tuple[int, ...], ...], bits: int) -> str:
    differences = sorted(
        {tuple(x - y for x, y in zip(p, q)) for p in points for q in points}
    )
    lines = [
        "(set-logic QF_LIA)",
        "(set-option :produce-models true)",
        "(set-option :timeout 300000)",
        "(declare-const base Int)",
    ]
    for j in range(bits):
        lines.append(f"(declare-const v{j} Int)")
    lines.append(f"(assert (and (<= 0 base) (< base {len(points)})))")
    for j in range(bits):
        lines.append(f"(assert (and (<= 0 v{j}) (< v{j} {len(differences)})))")
    for j in range(bits - 1):
        lines.append(f"(assert (<= v{j} v{j + 1}))")

    def select(index: str, values: list[int]) -> str:
        return "(+ " + " ".join(
            f"(ite (= {index} {i}) {value} 0)" for i, value in enumerate(values)
        ) + ")"

    dimensions = len(points[0])
    base_coords = [select("base", [p[c] for p in points]) for c in range(dimensions)]
    vector_coords = [
        [select(f"v{j}", [d[c] for d in differences]) for j in range(bits)]
        for c in range(dimensions)
    ]
    for t, point in enumerate(points):
        for j in range(bits):
            lines.append(f"(declare-const bit_{t}_{j} Bool)")
        for c in range(dimensions):
            terms = " ".join(
                f"(ite bit_{t}_{j} {vector_coords[c][j]} 0)" for j in range(bits)
            )
            lines.append(f"(assert (= {point[c]} (+ {base_coords[c]} {terms})))")
    names = "base " + " ".join(f"v{j}" for j in range(bits))
    lines.extend(["(check-sat)", f"(get-value ({names}))", "(get-info :reason-unknown)"])
    return "\n".join(lines) + "\n"


def main() -> int:
    z3 = shutil.which("z3")
    if z3 is None:
        print("error: z3 is not on PATH", file=sys.stderr)
        return 2

    concrete = concrete_certificate()
    print(f"concretely verified exact carry triples: {len(concrete)}")
    print("six-bit carry-only encoding: impossible")
    assert exact_shapes(16) == brute_shapes(16)
    print("arrangement enumeration: checked against exhaustive 4-bit search")
    all_shapes = exact_shapes(B)
    maximum = max(map(len, all_shapes))
    print(f"exhaustive relaxed 32-bit shapes: {len(all_shapes)}; "
          f"maximum states: {maximum}")

    full_points = relaxed_points(32, K0, 0, 0, 1)
    points = tuple(sorted({(qe, qa) for _, qe, qa in full_points}))
    assert len(full_points) == 44 and len(points) == 11
    query = smt_query(points, 4)
    completed = subprocess.run(
        [z3, "-in"], input=query, text=True, capture_output=True, check=False
    )
    print(f"maximal fixed-output E/A states: {len(points)}")
    difference_count = len({tuple(x - y for x, y in zip(p, q))
                            for p in points for q in points})
    print(f"difference vectors: {difference_count}")
    print(completed.stdout.strip())
    values = {name: int(value) for name, value in
              re.findall(r"\((base|v[0-9]+) ([0-9]+)\)", completed.stdout)}
    expected_names = {"base", *(f"v{j}" for j in range(4))}
    if not completed.stdout.startswith("sat\n") or values.keys() != expected_names:
        print("error: affine synthesis did not return the expected SAT model",
              file=sys.stderr)
        return 1
    else:
        differences = sorted({tuple(x - y for x, y in zip(p, q))
                              for p in points for q in points})
        generators = tuple(differences[values[f'v{j}']] for j in range(4))
        print(f"decoded base: {points[values['base']]}")
        print("decoded generators: " + repr(list(generators)))
        pair_shapes = {
            frozenset((qe, qa) for _, qe, qa in shape) for shape in all_shapes
        }
        covers = {shape: covering_bases(shape, generators)
                  for shape in pair_shapes}
        print(f"distinct E/A shapes: {len(pair_shapes)}")
        print(f"shapes covered by shared generators: "
              f"{sum(bool(bases) for bases in covers.values())}")
        print(f"distinct covering bases: "
              f"{len(set().union(*covers.values()))}")
        common_bases = set.intersection(*covers.values())
        print(f"bases covering every shape: {len(common_bases)}")
        minimum, best_generators, dictionary, viable = exhaustive_generator_search(
            pair_shapes, frozenset(points))
        print(f"exhaustive viable generator families: {viable}")
        print(f"minimum constant base dictionary: {minimum}")
        print(f"best generators: {list(best_generators)}")
        print(f"best base dictionary: {list(dictionary)}")
        union = {point for shape in all_shapes for point in shape}
        full_generators = ((1, 0, 0), (2, 0, 0),
                           (0, -1, 0), (0, -2, 0),
                           (0, 0, -1), (0, 0, -2))
        full_bases = ((0, 3, 3), (0, 5, 3))
        full_cover = {
            tuple(base[c] + sum(bits[j] * full_generators[j][c]
                                for j in range(6))
                  for c in range(3))
            for base in full_bases for bits in product((0, 1), repeat=6)
        }
        assert union <= full_cover
        print(f"fully coupled union states: {len(union)}")
        print("fully coupled minimum: six cube bits plus one base bit")
        print(f"fully coupled generators: {list(full_generators)}")
        print(f"fully coupled bases: {list(full_bases)}")
    if completed.stderr:
        print(completed.stderr.strip(), file=sys.stderr)
    return completed.returncode


if __name__ == "__main__":
    raise SystemExit(main())
