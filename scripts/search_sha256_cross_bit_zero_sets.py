#!/usr/bin/env python3
"""Search cross-bit SHA-256 zero-set encodings with Z3.

The first search couples two independent CH bits.  The existing integer
identity uses two new parity rows per bit, hence four rows for the pair.  We
ask whether one arbitrary Boolean witness lets three parity rows suffice.

The driver first enumerates every triple from the affine span of the four
existing CH characters and the auxiliary character, then the complete
character space modulo the symmetry `aux := aux XOR sourceParity`.  For each
fixed tuple, Z3 chooses:

* the complete 64-entry witness truth table;
* a linear expression for CH_0 + 2*CH_1; and
* one linear zero-set equation cutting out exactly the chosen witness graph.

The equation is an unrestricted exact rational linear equation, matching a
linear R1CS assertion over M-row outputs.  Denominators can be cleared to lift
every solution to an integer constraint.  One equation is without loss of
generality: over the rationals, a generic linear combination of any finite
family of separating equations is nonzero on every invalid point.

The script also searches CH+MAJ and Sigma+CH with one auxiliary, two CH bits
with two auxiliaries, and their full-rank auxiliary cases.  Sigma+MAJ is
checked in the full-rank one-row case.  Adjacent-round CH and MAJ terms are
searched on their actual four-input overlap: CH attempts four rows to three,
while MAJ attempts two rows to one.  A five-input chain of three consecutive
MAJ terms additionally attempts three rows to two.  Together, the canonical
rank-one enumerations and the normalized full-rank checks cover arbitrary
Boolean auxiliaries for the attempted row reductions; rank zero is the
original Walsh representation and cannot improve its sparsity.

For the larger three-round CH chain, `--three-ch-candidates` exhausts 117
distinct low-complexity auxiliary truth tables and lets Z3 select any five
rows from the complete parity-character space.  The symbolic and CEGIS modes
are retained as bounded exploratory searches over an arbitrary one-bit truth
table; unlike the fixed-mask and fixed-candidate searches, they may return
inconclusive.

Run with:

    nix shell nixpkgs#z3 -c python3 scripts/search_sha256_cross_bit_zero_sets.py
    nix shell nixpkgs#z3 -c python3 scripts/search_sha256_cross_bit_zero_sets.py \
      --three-ch-candidates
"""

from __future__ import annotations

import re
import shutil
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor
from itertools import combinations, product
from typing import Callable


def parity(bits: tuple[int, ...], mask: int) -> int:
    return sum(bit for i, bit in enumerate(bits) if mask >> i & 1) & 1


def ch(u: int, v: int, w: int) -> int:
    return (u & v) ^ ((1 ^ u) & w)


def maj(u: int, v: int, w: int) -> int:
    return (u & v) ^ (u & w) ^ (v & w)


def sigma(x: int, y: int, z: int) -> int:
    return x ^ y ^ z


def target_input_count(target_name: str) -> int:
    if target_name in ("adjacent_ch", "adjacent_maj"):
        return 4
    if target_name == "three_maj":
        return 5
    if target_name == "three_ch":
        return 5
    return 6


def target_value(target_name: str, inputs: tuple[int, ...]) -> int:
    if target_name == "two_ch":
        return ch(*inputs[:3]) + 2 * ch(*inputs[3:])
    if target_name == "adjacent_ch":
        return ch(*inputs[:3]) + 2 * ch(inputs[3], inputs[0], inputs[1])
    if target_name == "adjacent_maj":
        return maj(*inputs[:3]) + 2 * maj(inputs[3], inputs[0], inputs[1])
    if target_name == "three_maj":
        return (maj(*inputs[:3]) + 2 * maj(inputs[3], inputs[0], inputs[1])
                + 4 * maj(inputs[4], inputs[3], inputs[0]))
    if target_name == "three_ch":
        return (ch(*inputs[:3]) + 2 * ch(inputs[3], inputs[0], inputs[1])
                + 4 * ch(inputs[4], inputs[3], inputs[0]))
    if target_name == "ch_maj":
        return ch(*inputs[:3]) + maj(*inputs[3:])
    if target_name == "sigma_ch":
        return sigma(*inputs[:3]) + ch(*inputs[3:])
    if target_name == "sigma_maj":
        return sigma(*inputs[:3]) + maj(*inputs[3:])
    raise ValueError(f"unknown target {target_name}")


def linear_expression(
    names: list[str], inputs: tuple[int, ...], rows: list[str],
) -> str:
    terms = [names[0]]
    terms.extend(f"(* {names[i + 1]} {bit})"
                 for i, bit in enumerate(inputs) if bit)
    terms.extend(f"(* {names[1 + len(inputs) + j]} {row})"
                 for j, row in enumerate(rows))
    return "(+ " + " ".join(terms) + ")"


def fixed_aux_sparse_query(
    aux_values: tuple[int, ...], target_name: str, row_limit: int,
    include_model: bool = False, timeout_ms: int = 10_000,
) -> str:
    """Select a sparse parity basis for one fixed auxiliary truth table."""
    input_count = target_input_count(target_name)
    masks = [
        mask for mask in range(1, 1 << (input_count + 1))
        if mask & (mask - 1) or mask == 1 << input_count
    ]
    prefix = "fa"
    lines = [
        "(set-logic QF_LIRA)",
        "(set-option :produce-models true)",
        f"(set-option :timeout {timeout_ms})",
    ]
    out_free = [f"{prefix}_out_free_{i}" for i in range(input_count + 1)]
    eq_free = [f"{prefix}_eq_free_{i}" for i in range(input_count + 1)]
    for name in (*out_free, *eq_free):
        lines.append(f"(declare-const {name} Real)")
    for mask in masks:
        lines.extend([
            f"(declare-const {prefix}_use_{mask} Bool)",
            f"(declare-const {prefix}_out_{mask} Real)",
            f"(declare-const {prefix}_eq_{mask} Real)",
            f"(assert (=> (not {prefix}_use_{mask}) "
            f"(and (= {prefix}_out_{mask} 0) (= {prefix}_eq_{mask} 0))))",
        ])
    cardinality = "(+ " + " ".join(
        f"(ite {prefix}_use_{mask} 1 0)" for mask in masks) + ")"
    lines.append(f"(assert (<= {cardinality} {row_limit}))")

    def expression(
        free: list[str], coefficients: str, inputs: tuple[int, ...], aux: int,
    ) -> str:
        terms = [free[0]]
        terms.extend(f"(* {free[i + 1]} {bit})"
                     for i, bit in enumerate(inputs) if bit)
        terms.extend(
            f"(* {prefix}_{coefficients}_{mask} "
            f"{parity((*inputs, aux), mask)})" for mask in masks)
        return "(+ " + " ".join(terms) + ")"

    assignments = list(product((0, 1), repeat=input_count))
    if len(aux_values) != len(assignments):
        raise ValueError("auxiliary truth table has the wrong size")
    for index, inputs in enumerate(assignments):
        valid_aux = aux_values[index]
        valid_eq = expression(eq_free, "eq", inputs, valid_aux)
        invalid_eq = expression(eq_free, "eq", inputs, 1 ^ valid_aux)
        output = expression(out_free, "out", inputs, valid_aux)
        lines.append(
            f"(assert (and (= {valid_eq} 0) (not (= {invalid_eq} 0)) "
            f"(= {output} {target_value(target_name, inputs)})))")
    lines.append("(check-sat)")
    if include_model:
        uses = " ".join(f"{prefix}_use_{mask}" for mask in masks)
        lines.append(f"(get-value ({uses}))")
        lines.append("(get-model)")
    return "\n".join(lines) + "\n"


def three_ch_auxiliary_candidates() -> list[tuple[str, tuple[int, ...]]]:
    assignments = list(product((0, 1), repeat=5))
    predicates: list[tuple[str, Callable[[tuple[int, ...]], int]]] = []
    for size in (2, 3):
        for indices in combinations(range(5), size):
            suffix = "".join(map(str, indices))
            predicates.append((f"and_{suffix}", lambda xs, js=indices:
                               int(all(xs[j] for j in js))))
            predicates.append((f"or_{suffix}", lambda xs, js=indices:
                               int(any(xs[j] for j in js))))
    for u, v, w in product(range(5), repeat=3):
        if len({u, v, w}) != 3:
            continue
        predicates.append((f"ch_{u}{v}{w}", lambda xs, i=u, j=v, k=w:
                           ch(xs[i], xs[j], xs[k])))
    for indices in combinations(range(5), 3):
        predicates.append(("maj_" + "".join(map(str, indices)),
                           lambda xs, js=indices: maj(*(xs[j] for j in js))))

    def outputs(xs: tuple[int, ...]) -> tuple[int, int, int]:
        return (ch(*xs[:3]), ch(xs[3], xs[0], xs[1]),
                ch(xs[4], xs[3], xs[0]))

    for bits in range(1, 8):
        predicates.append((f"ch_xor_{bits}", lambda xs, mask=bits:
                           parity(outputs(xs), mask)))
    predicates.extend([
        ("ch_and", lambda xs: int(all(outputs(xs)))),
        ("ch_or", lambda xs: int(any(outputs(xs)))),
        ("ch_maj", lambda xs: maj(*outputs(xs))),
    ])
    unique: dict[tuple[int, ...], str] = {}
    for name, predicate in predicates:
        table = tuple(predicate(inputs) for inputs in assignments)
        unique.setdefault(table, name)
    return sorted((name, table) for table, name in unique.items())


def symbolic_linear_expression(
    names: list[str], inputs: tuple[int, ...], rows: list[str],
) -> str:
    terms = [names[0]]
    terms.extend(f"(* {names[i + 1]} {bit})"
                 for i, bit in enumerate(inputs) if bit)
    terms.extend(f"(ite {row} {names[1 + len(inputs) + j]} 0)"
                 for j, row in enumerate(rows))
    return "(+ " + " ".join(terms) + ")"


def xor_expr(terms: list[str]) -> str:
    if not terms:
        return "false"
    if len(terms) == 1:
        return terms[0]
    return "(xor " + " ".join(terms) + ")"


def symbolic_two_ch_query(
    include_model: bool = False, timeout_ms: int = 300_000,
    assignment_indices: set[int] | None = None,
    target_name: str = "two_ch", row_count: int = 3,
) -> str:
    """Search all 127 affine characters without nonlinear mask selection."""
    input_count = target_input_count(target_name)
    dimension = 1 + input_count + row_count
    lines = [
        "(set-logic QF_LIRA)",
        "(set-option :produce-models true)",
        f"(set-option :timeout {timeout_ms})",
    ]
    for row, bit in product(range(row_count), range(input_count + 1)):
        lines.append(f"(declare-const mask_{row}_{bit} Bool)")
    for row in range(row_count):
        nonzero = " ".join(f"mask_{row}_{bit}"
                           for bit in range(input_count + 1))
        lines.append(f"(assert (or {nonzero}))")
    mask_values = [
        "(+ " + " ".join(f"(ite mask_{row}_{bit} {1 << bit} 0)"
                          for bit in range(input_count + 1)) + ")"
        for row in range(row_count)
    ]
    for row in range(row_count - 1):
        lines.append(f"(assert (< {mask_values[row]} {mask_values[row + 1]}))")

    output_names = [f"sym_out_{i}" for i in range(dimension)]
    equation_names = [f"sym_eq_{i}" for i in range(dimension)]
    for name in [*output_names, *equation_names]:
        lines.append(f"(declare-const {name} Real)")

    assignments = list(product((0, 1), repeat=input_count))
    for index, inputs in enumerate(assignments):
        if assignment_indices is not None and index not in assignment_indices:
            continue
        lines.append(f"(declare-const sym_aux_{index} Bool)")
        rows_by_aux: list[list[str]] = [[], []]
        for row in range(row_count):
            source_terms = [f"mask_{row}_{bit}" for bit in range(input_count)
                            if inputs[bit]]
            at_zero = xor_expr(source_terms)
            at_one = xor_expr([at_zero, f"mask_{row}_{input_count}"])
            rows_by_aux[0].append(at_zero)
            rows_by_aux[1].append(at_one)

        eq_zero = symbolic_linear_expression(
            equation_names, inputs, rows_by_aux[0])
        eq_one = symbolic_linear_expression(
            equation_names, inputs, rows_by_aux[1])
        lines.append(f"(assert (= (ite sym_aux_{index} {eq_one} {eq_zero}) 0))")
        lines.append(
            f"(assert (not (= (ite sym_aux_{index} {eq_zero} {eq_one}) 0)))"
        )

        out_zero = symbolic_linear_expression(
            output_names, inputs, rows_by_aux[0])
        out_one = symbolic_linear_expression(
            output_names, inputs, rows_by_aux[1])
        target = target_value(target_name, inputs)
        lines.append(
            f"(assert (= (ite sym_aux_{index} {out_one} {out_zero}) {target}))"
        )

    lines.append("(check-sat)")
    if include_model:
        names = " ".join(f"mask_{row}_{bit}" for row in range(row_count)
                         for bit in range(input_count + 1))
        lines.append(f"(get-value ({names}))")
        lines.append("(get-model)")
    return "\n".join(lines) + "\n"


def two_ch_query(
    masks: tuple[int, ...], include_model: bool = False,
    timeout_ms: int = 2_000, unsat_core: bool = False,
    target_name: str = "two_ch",
) -> str:
    input_count = target_input_count(target_name)
    row_count = len(masks)
    dimension = 1 + input_count + row_count
    lines = [
        "(set-logic QF_LRA)",
        "(set-option :produce-models true)",
        f"(set-option :timeout {timeout_ms})",
    ]
    if unsat_core:
        lines.append("(set-option :produce-unsat-cores true)")

    output_names = [f"out_{i}" for i in range(dimension)]
    constraint_names = [
        [f"eq_{equation}_{i}" for i in range(dimension)]
        for equation in range(1)
    ]
    for name in [*output_names,
                 *(name for equation in constraint_names for name in equation)]:
        lines.append(f"(declare-const {name} Real)")

    assignments = list(product((0, 1), repeat=input_count))
    for index, inputs in enumerate(assignments):
        lines.append(f"(declare-const aux_{index} Bool)")
        rows_by_aux = []
        for aux in (0, 1):
            bits = (*inputs, aux)
            rows_by_aux.append([str(parity(bits, mask)) for mask in masks])

        valid_equations = []
        invalid_equations = []
        for names in constraint_names:
            at_zero = linear_expression(names, inputs, rows_by_aux[0])
            at_one = linear_expression(names, inputs, rows_by_aux[1])
            valid_equations.append(f"(ite aux_{index} {at_one} {at_zero})")
            invalid_equations.append(f"(ite aux_{index} {at_zero} {at_one})")
        clauses = [f"(= {equation} 0)" for equation in valid_equations]
        exclusion = " ".join(f"(not (= {equation} 0))"
                             for equation in invalid_equations)
        clauses.append(f"(or {exclusion})")

        at_zero = linear_expression(output_names, inputs, rows_by_aux[0])
        at_one = linear_expression(output_names, inputs, rows_by_aux[1])
        target = target_value(target_name, inputs)
        clauses.append(f"(= (ite aux_{index} {at_one} {at_zero}) {target})")
        conjunction = "(and " + " ".join(clauses) + ")"
        if unsat_core:
            lines.append(f"(assert (! {conjunction} :named assignment_{index}))")
        else:
            lines.append(f"(assert {conjunction})")

    lines.append("(check-sat)")
    if include_model:
        lines.append("(get-model)")
    if unsat_core:
        lines.append("(get-unsat-core)")
    return "\n".join(lines) + "\n"


def two_row_query(
    target_name: str, masks: tuple[int, int], include_model: bool = False,
    timeout_ms: int = 2_000,
) -> str:
    """Couple two bit functions using two parity rows."""
    input_count = target_input_count(target_name)
    row_count = 2
    dimension = 1 + input_count + row_count
    lines = [
        "(set-logic QF_LRA)",
        "(set-option :produce-models true)",
        f"(set-option :timeout {timeout_ms})",
    ]
    prefix = "tr_" + target_name
    output_names = [f"{prefix}_out_{i}" for i in range(dimension)]
    equation_names = [f"{prefix}_eq_{i}" for i in range(dimension)]
    for name in [*output_names, *equation_names]:
        lines.append(f"(declare-const {name} Real)")

    for index, inputs in enumerate(product((0, 1), repeat=input_count)):
        lines.append(f"(declare-const {prefix}_aux_{index} Bool)")
        rows_by_aux = [
            [str(parity((*inputs, aux), mask)) for mask in masks]
            for aux in (0, 1)
        ]
        eq_zero = linear_expression(equation_names, inputs, rows_by_aux[0])
        eq_one = linear_expression(equation_names, inputs, rows_by_aux[1])
        out_zero = linear_expression(output_names, inputs, rows_by_aux[0])
        out_one = linear_expression(output_names, inputs, rows_by_aux[1])
        target = target_value(target_name, inputs)
        lines.append(
            "(assert (and "
            f"(= (ite {prefix}_aux_{index} {eq_one} {eq_zero}) 0) "
            f"(not (= (ite {prefix}_aux_{index} {eq_zero} {eq_one}) 0)) "
            f"(= (ite {prefix}_aux_{index} {out_one} {out_zero}) {target})))"
        )
    lines.append("(check-sat)")
    if include_model:
        lines.append("(get-model)")
    return "\n".join(lines) + "\n"


def two_ch_two_aux_query(
    third_mask: int, include_model: bool = False,
    timeout_ms: int = 5_000, target_name: str = "two_ch",
) -> str:
    """Encode two CH bits with two auxiliaries and three parity rows."""
    input_count = target_input_count(target_name)
    row_masks = (1 << input_count, 1 << (input_count + 1), third_mask)
    dimension = 1 + input_count + len(row_masks)
    lines = [
        "(set-logic QF_LRA)",
        "(set-option :produce-models true)",
        f"(set-option :timeout {timeout_ms})",
    ]
    output_names = [f"ca_out_{i}" for i in range(dimension)]
    equation_names = [f"ca_eq_{i}" for i in range(dimension)]
    for name in [*output_names, *equation_names]:
        lines.append(f"(declare-const {name} Real)")

    for index, inputs in enumerate(product((0, 1), repeat=input_count)):
        lines.append(f"(declare-const ca_aux0_{index} Bool)")
        lines.append(f"(declare-const ca_aux1_{index} Bool)")
        rows_by_aux = {}
        for aux in product((0, 1), repeat=2):
            rows_by_aux[aux] = [
                str(parity((*inputs, *aux), mask)) for mask in row_masks
            ]
        valid_cases = []
        for aux in product((0, 1), repeat=2):
            condition = (f"(and (= ca_aux0_{index} {'true' if aux[0] else 'false'}) "
                         f"(= ca_aux1_{index} {'true' if aux[1] else 'false'}))")
            equation = linear_expression(
                equation_names, inputs, rows_by_aux[aux])
            output = linear_expression(output_names, inputs, rows_by_aux[aux])
            target = target_value(target_name, inputs)
            invalid = []
            for other in product((0, 1), repeat=2):
                if other == aux:
                    continue
                other_equation = linear_expression(
                    equation_names, inputs, rows_by_aux[other])
                invalid.append(f"(not (= {other_equation} 0))")
            body = (f"(and (= {equation} 0) {' '.join(invalid)} "
                    f"(= {output} {target}))")
            valid_cases.append(f"(and {condition} {body})")
        lines.append(f"(assert (or {' '.join(valid_cases)}))")
    lines.append("(check-sat)")
    if include_model:
        lines.append("(get-model)")
    return "\n".join(lines) + "\n"


def full_rank_query(
    target_name: str, row_count: int, include_model: bool = False,
    timeout_ms: int = 300_000,
) -> str:
    """Check a full-rank auxiliary-to-row map in canonical coordinates."""
    input_count = target_input_count(target_name)
    row_masks = tuple(1 << (input_count + row) for row in range(row_count))
    dimension = 1 + input_count + row_count
    prefix = "fr_" + target_name
    lines = [
        "(set-logic QF_LRA)",
        "(set-option :produce-models true)",
        f"(set-option :timeout {timeout_ms})",
    ]
    output_names = [f"{prefix}_out_{i}" for i in range(dimension)]
    equation_names = [f"{prefix}_eq_{i}" for i in range(dimension)]
    for name in [*output_names, *equation_names]:
        lines.append(f"(declare-const {name} Real)")

    for index, inputs in enumerate(product((0, 1), repeat=input_count)):
        for aux_index in range(row_count):
            lines.append(f"(declare-const {prefix}_aux{aux_index}_{index} Bool)")
        rows_by_aux = {
            aux: [str(parity((*inputs, *aux), mask)) for mask in row_masks]
            for aux in product((0, 1), repeat=row_count)
        }
        target = target_value(target_name, inputs)
        valid_cases = []
        for aux in product((0, 1), repeat=row_count):
            conditions = " ".join(
                f"(= {prefix}_aux{j}_{index} {'true' if bit else 'false'})"
                for j, bit in enumerate(aux))
            equation = linear_expression(
                equation_names, inputs, rows_by_aux[aux])
            output = linear_expression(output_names, inputs, rows_by_aux[aux])
            invalid = []
            for other in product((0, 1), repeat=row_count):
                if other == aux:
                    continue
                other_equation = linear_expression(
                    equation_names, inputs, rows_by_aux[other])
                invalid.append(f"(not (= {other_equation} 0))")
            valid_cases.append(
                f"(and {conditions} (= {equation} 0) {' '.join(invalid)} "
                f"(= {output} {target}))")
        lines.append(f"(assert (or {' '.join(valid_cases)}))")
    lines.append("(check-sat)")
    if include_model:
        lines.append("(get-model)")
    return "\n".join(lines) + "\n"


def decode_symbolic_masks(
    output: str, row_count: int = 3, input_count: int = 6,
) -> tuple[int, ...]:
    values = {(int(row), int(bit)): value == "true"
              for row, bit, value in re.findall(
                  r"\(mask_([0-9]+)_([0-9]+) (true|false)\)", output)}
    if len(values) != row_count * (input_count + 1):
        raise ValueError("symbolic model did not contain all mask bits")
    return tuple(sum((1 << bit) for bit in range(input_count + 1)
                     if values[row, bit]) for row in range(row_count))


def cegis_two_ch(
    z3: str, max_iterations: int = 64, target_name: str = "two_ch",
    row_count: int = 3,
) -> tuple[str, str]:
    input_count = target_input_count(target_name)
    alternating = sum(1 << bit for bit in range(0, input_count, 2))
    samples = {0, alternating, ((1 << input_count) - 1) ^ alternating,
               (1 << input_count) - 1}
    transcript = []
    for iteration in range(1, max_iterations + 1):
        proposal = subprocess.run(
            [z3, "-in"],
            input=symbolic_two_ch_query(
                include_model=True, timeout_ms=120_000,
                assignment_indices=samples, target_name=target_name,
                row_count=row_count),
            text=True, capture_output=True, check=False,
        )
        if proposal.stdout.startswith("unsat\n"):
            transcript.append(
                f"iteration {iteration}: UNSAT on {len(samples)} samples")
            return "unsat", "\n".join(transcript)
        if not proposal.stdout.startswith("sat\n"):
            status = proposal.stdout.splitlines()[0] if proposal.stdout else "empty"
            transcript.append(f"iteration {iteration}: symbolic {status}")
            return "unknown", "\n".join(transcript)
        masks = decode_symbolic_masks(
            proposal.stdout, row_count=row_count, input_count=input_count)
        check = subprocess.run(
            [z3, "-in"],
            input=two_ch_query(masks, timeout_ms=30_000, unsat_core=True,
                               target_name=target_name),
            text=True, capture_output=True, check=False,
        )
        if check.stdout.startswith("sat\n"):
            transcript.append(f"iteration {iteration}: SAT masks {masks}")
            return "sat", "\n".join(transcript)
        if not check.stdout.startswith("unsat\n"):
            status = check.stdout.splitlines()[0] if check.stdout else "empty"
            transcript.append(f"iteration {iteration}: fixed check {status}")
            return "unknown", "\n".join(transcript)
        core = {int(index) for index in re.findall(
            r"assignment_([0-9]+)", check.stdout)}
        added = core - samples
        chosen = {min(added)} if added else set()
        transcript.append(
            f"iteration {iteration}: reject {masks}; "
            f"core {len(core)}; add {sorted(chosen)}")
        if not chosen:
            return "unknown", "\n".join(transcript)
        samples |= chosen
    return "unknown", "\n".join(transcript)


def structured_masks() -> list[int]:
    """Span the four existing CH characters, optionally XORed with aux."""
    generators = ((1 << 0) | (1 << 1), (1 << 0) | (1 << 2),
                  (1 << 3) | (1 << 4), (1 << 3) | (1 << 5))
    source_span = {
        generators[0] * bits[0] ^ generators[1] * bits[1]
        ^ generators[2] * bits[2] ^ generators[3] * bits[3]
        for bits in product((0, 1), repeat=4)
    }
    return sorted((source_span - {0}) | {mask | (1 << 6) for mask in source_span})


def canonical_mask_triples(input_count: int = 6) -> list[tuple[int, int, int]]:
    """All triples up to replacing aux by aux XOR a source parity."""
    auxiliary = 1 << input_count
    others = [mask for mask in range(1, 1 << (input_count + 1))
              if mask != auxiliary]
    return sorted({tuple(sorted((auxiliary, *pair)))
                   for pair in combinations(others, 2)})


def main() -> int:
    z3 = shutil.which("z3")
    if z3 is None:
        print("error: z3 is not on PATH", file=sys.stderr)
        return 2
    if "--three-ch-candidates" in sys.argv:
        candidates = three_ch_auxiliary_candidates()

        def solve_candidate(
            item: tuple[str, tuple[int, ...]],
        ) -> tuple[str, tuple[int, ...], str]:
            name, table = item
            try:
                completed = subprocess.run(
                    [z3, "-in"], input=fixed_aux_sparse_query(
                        table, "three_ch", 5),
                    text=True, capture_output=True, check=False,
                    timeout=15,
                )
            except subprocess.TimeoutExpired:
                return name, table, "unknown\n"
            return name, table, completed.stdout

        unknown = 0
        with ThreadPoolExecutor(max_workers=8) as executor:
            for name, table, stdout in executor.map(solve_candidate, candidates):
                if stdout.startswith("sat\n"):
                    model = subprocess.run(
                        [z3, "-in"], input=fixed_aux_sparse_query(
                            table, "three_ch", 5, include_model=True,
                            timeout_ms=60_000),
                        text=True, capture_output=True, check=False,
                        timeout=65,
                    )
                    print("three adjacent-round CH terms: SAT six rows -> five")
                    print(f"auxiliary: {name}")
                    print(model.stdout.strip())
                    return model.returncode
                if not stdout.startswith("unsat\n"):
                    unknown += 1
        print("three adjacent-round CH terms: no five-row candidate encoding")
        print(f"candidate truth tables: {len(candidates)}; unknown: {unknown}")
        return 1 if unknown else 0
    if "--three-ch-cegis" in sys.argv:
        status, transcript = cegis_two_ch(
            z3, target_name="three_ch", row_count=5)
        print("three adjacent-round CH terms: CEGIS six rows -> five rows")
        print(transcript)
        if status in ("sat", "unsat"):
            return 0
        print("error: three-CH CEGIS search was inconclusive", file=sys.stderr)
        return 1
    if "--three-ch-symbolic" in sys.argv:
        completed = subprocess.run(
            [z3, "-in"], input=symbolic_two_ch_query(
                include_model=True, timeout_ms=600_000,
                target_name="three_ch", row_count=5),
            text=True, capture_output=True, check=False,
        )
        print("three adjacent-round CH terms: symbolic six rows -> five rows")
        print(completed.stdout.strip())
        if completed.stderr:
            print(completed.stderr.strip(), file=sys.stderr)
        return completed.returncode if completed.stdout.startswith(("sat\n", "unsat\n")) else 1

    def solve(
        target_name: str, masks: tuple[int, int, int],
    ) -> tuple[tuple[int, int, int], str]:
        completed = subprocess.run(
            [z3, "-in"], input=two_ch_query(masks, target_name=target_name), text=True,
            capture_output=True, check=False,
        )
        return masks, completed.stdout

    def enumerate_triples(
        target_name: str, label: str, triples: list[tuple[int, int, int]],
    ) -> tuple[str, int]:
        def solve_target(
            masks: tuple[int, int, int],
        ) -> tuple[tuple[int, int, int], str]:
            return solve(target_name, masks)

        unknown = 0
        with ThreadPoolExecutor(max_workers=8) as executor:
            for masks, stdout in executor.map(solve_target, triples):
                if stdout.startswith("sat\n"):
                    model = subprocess.run(
                        [z3, "-in"],
                        input=two_ch_query(masks, include_model=True,
                                           target_name=target_name),
                        text=True, capture_output=True, check=False,
                    )
                    print(f"{label}: SAT four rows -> three rows with one auxiliary")
                    print(f"masks: {masks}")
                    print(model.stdout.strip())
                    return "sat", unknown
                if not stdout.startswith("unsat\n"):
                    unknown += 1
        print(f"{label}: no three-row encoding")
        print(f"triples: {len(triples)}; unknown: {unknown}")
        return ("unknown" if unknown else "unsat"), unknown

    if "--cegis-only" not in sys.argv:
        pool = structured_masks()
        structured, _ = enumerate_triples(
            "two_ch", "two CH bits in structured auxiliary span",
            list(combinations(pool, 3)))
        if structured == "sat":
            return 0
        if structured == "unknown":
            return 1

        canonical, _ = enumerate_triples(
            "two_ch", "two CH bits in complete canonical character space",
            canonical_mask_triples())
        if canonical == "sat":
            return 0
        if canonical != "unsat":
            return 1

        adjacent, _ = enumerate_triples(
            "adjacent_ch", "adjacent-round CH pair",
            canonical_mask_triples(4))
        if adjacent == "sat":
            return 0
        if adjacent != "unsat":
            return 1

        for target_name, input_count, label in (
            ("ch_maj", 6, "CH + MAJ"),
            ("sigma_ch", 6, "Sigma + CH"),
            ("three_maj", 5, "three adjacent-round MAJ terms"),
        ):
            auxiliary = 1 << input_count
            pairs = [(auxiliary, mask)
                     for mask in range(1, 1 << (input_count + 1))
                     if mask != auxiliary]

            def solve_two_row(
                masks: tuple[int, int],
            ) -> tuple[tuple[int, int], str]:
                completed = subprocess.run(
                    [z3, "-in"], input=two_row_query(target_name, masks),
                    text=True, capture_output=True, check=False,
                )
                return masks, completed.stdout

            two_row_unknown = 0
            with ThreadPoolExecutor(max_workers=8) as executor:
                for masks, stdout in executor.map(solve_two_row, pairs):
                    if stdout.startswith("sat\n"):
                        model = subprocess.run(
                            [z3, "-in"],
                            input=two_row_query(target_name, masks,
                                                include_model=True),
                            text=True, capture_output=True, check=False,
                        )
                        print(f"{label}: SAT three rows -> two rows "
                              "with one auxiliary")
                        print(f"masks: {masks}")
                        print(model.stdout.strip())
                        return model.returncode
                    if not stdout.startswith("unsat\n"):
                        two_row_unknown += 1
            print(f"{label}: no two-row encoding in complete canonical space")
            print(f"pairs: {len(pairs)}; unknown: {two_row_unknown}")
            if two_row_unknown:
                return 1

        for target_name, input_count, label in (
            ("two_ch", 6, "two CH bits"),
            ("adjacent_ch", 4, "adjacent-round CH pair"),
        ):
            aux0, aux1 = 1 << input_count, 1 << (input_count + 1)
            third_masks = [mask for mask in range(1, 1 << (input_count + 2))
                           if mask not in (aux0, aux1)]

            def solve_two_aux(mask: int) -> tuple[int, str]:
                completed = subprocess.run(
                    [z3, "-in"], input=two_ch_two_aux_query(
                        mask, target_name=target_name),
                    text=True, capture_output=True, check=False,
                )
                return mask, completed.stdout

            two_aux_unknown = 0
            with ThreadPoolExecutor(max_workers=8) as executor:
                for mask, stdout in executor.map(solve_two_aux, third_masks):
                    if stdout.startswith("sat\n"):
                        model = subprocess.run(
                            [z3, "-in"], input=two_ch_two_aux_query(
                                mask, include_model=True,
                                target_name=target_name),
                            text=True, capture_output=True, check=False,
                        )
                        print(f"{label}: SAT four rows -> three rows "
                              "with two auxiliaries")
                        print(f"third mask: {mask}")
                        print(model.stdout.strip())
                        return model.returncode
                    if not stdout.startswith("unsat\n"):
                        two_aux_unknown += 1
            print(f"{label}: no three-row encoding with two auxiliaries")
            print(f"canonical third masks: {len(third_masks)}; "
                  f"unknown: {two_aux_unknown}")
            if two_aux_unknown:
                return 1

        for target_name, row_count, label in (
            ("sigma_maj", 1, "Sigma + MAJ full-rank one-auxiliary encoding"),
            ("ch_maj", 2, "CH + MAJ full-rank two-auxiliary encoding"),
            ("sigma_ch", 2, "Sigma + CH full-rank two-auxiliary encoding"),
            ("adjacent_maj", 1,
             "adjacent-round MAJ full-rank one-auxiliary encoding"),
            ("three_maj", 2,
             "three adjacent-round MAJ full-rank two-auxiliary encoding"),
            ("two_ch", 3, "two CH bits full-rank three-auxiliary encoding"),
            ("adjacent_ch", 3,
             "adjacent-round CH full-rank three-auxiliary encoding"),
        ):
            full_rank = subprocess.run(
                [z3, "-in"], input=full_rank_query(target_name, row_count),
                text=True, capture_output=True, check=False,
            )
            print(label + ":")
            print(full_rank.stdout.strip())
            if full_rank.stdout.startswith("sat\n"):
                model = subprocess.run(
                    [z3, "-in"],
                    input=full_rank_query(target_name, row_count,
                                          include_model=True),
                    text=True, capture_output=True, check=False,
                )
                print(model.stdout.strip())
                return model.returncode
            if not full_rank.stdout.startswith("unsat\n"):
                return 1
        return 0

    status, transcript = cegis_two_ch(z3)
    print("two CH bits: CEGIS over all 127 affine characters")
    print(transcript)
    if status == "unsat":
        return 0
    if status == "sat":
        return 0
    print("error: CEGIS search was inconclusive", file=sys.stderr)
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
