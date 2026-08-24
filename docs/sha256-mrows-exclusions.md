# SHA-256 `mRows` search: exact exclusions

This note records the SHA-256 row reductions that have been ruled out exactly.
It deliberately separates exhaustive lower bounds from targeted searches and
solver runs that were inconclusive.

The circuit baseline after schedule/round loop fusion is:

```text
{ mRows := 20262, mCols := 6898, r1csRows := 180, cost := 148732 }
```

Here `cost = 7 * mRows + mCols`.

## Model covered by the zero-set searches

The searches keep R1CS linear.  A candidate encoding may introduce arbitrary
Boolean witness functions and may use affine linear expressions in:

- the source Boolean inputs;
- the selected parity-character (`M`) row outputs; and
- constants.

The decoder and witness-graph equation use unrestricted exact rational
coefficients (`Real` in QF_LRA), not floating-point approximations.  Therefore
`UNSAT` over the rationals also excludes integer-coefficient encodings.  A
rational solution would lift to integers by clearing denominators.

For every source assignment, the chosen witness assignment must make the graph
equation zero and every other witness assignment must make it nonzero.  One
equation is without loss of generality for a finite invalid set: a generic
rational linear combination of finitely many separating equations remains
nonzero on every invalid point.  Multiple Boolean outputs are packed with
radix weights, such as `f0 + 2*f1`, so recovering the packed value recovers
each output.

Auxiliary-coordinate changes normalize rank-one rows to one auxiliary basis
character and full-rank cases to the auxiliary coordinate basis.  The searches
then enumerate every remaining parity-character mask.  Rank zero is the
original Walsh representation; uniqueness of the Walsh-Hadamard expansion
rules out a sparser witness-free representation.  An attempted result with
`r` rows cannot benefit from more than `r` effective auxiliary directions,
because every used witness direction itself has to occur in those rows.

## Exactly excluded Boolean factorizations

All entries below completed with zero solver `unknown` results.

| Expression family | Existing rows | Excluded target | Exact auxiliary-rank coverage |
| --- | ---: | ---: | --- |
| Two independent `Ch` bits | 4 | 3 | Rank 1: all 7,875 canonical triples; rank 2: all 253 canonical third masks; rank 3: normalized full-rank query |
| Consecutive `Ch(e,f,g)` and `Ch(newE,e,f)` | 4 | 3 | Rank 1: all 435 canonical triples; rank 2: all 61 canonical third masks; rank 3: normalized full-rank query |
| Disjoint `Ch + Maj` | 3 | 2 | Rank 1: all 126 canonical pairs; rank 2: normalized full-rank query |
| Disjoint `Sigma + Ch` | 3 | 2 | Rank 1: all 126 canonical pairs; rank 2: normalized full-rank query |
| Disjoint `Sigma + Maj` | 2 | 1 | Normalized rank-one query |
| Consecutive `Maj(a,b,c)` and `Maj(newA,a,b)` | 2 | 1 | Normalized rank-one query |
| Three consecutive `Maj` terms on their five-variable state-shift overlap | 3 | 2 | Rank 1: all 62 canonical pairs; rank 2: normalized full-rank query |

Consequently, these reductions are impossible even when the auxiliary bits are
arbitrary truth tables, not merely named predicates such as `Ch`, `Maj`, AND,
OR, or XOR.

The first independent-`Ch` search also checked all 4,495 triples in the span
of the four existing `Ch` characters and the auxiliary character.  This is a
strict subset of the complete 7,875-case canonical search and is retained as a
regression check.

## Ordinary-round optimality status

An isolated compilation of `roundStep` with nine already-committed 32-bit
input words gives 229 additional `M` rows.  Compiling the 288 Boolean interface
bits as `U 32` values and then executing the round gives `mRows = 518`: 288
interface-conversion rows, 229 internal rows, and the one extra row in the
statistics convention.

The internal accounting is:

| Round component | Current rows |
| --- | ---: |
| `Sigma1(e)` | 32 |
| `Ch(e,f,g)` | 64 |
| `Sigma0(a)` | 32 |
| `Maj(a,b,c)` | 32 |
| `newE` output and quotient | 35 |
| `newA` output and quotient | 34 |
| **Total** | **229** |

The exact exclusions above prove optimality of the individual Boolean
identities and several two- and three-expression couplings.  They are strong
evidence that the 229-row construction is locally optimal.  They do **not**
prove that the entire round is globally optimal.

The strongest currently checked unrestricted semantic bound for one round is
64 internal rows.  A deterministic exact computation found 64 linearly
independent second-derivative vectors of the 64-bit `(newA,newE)` function
(rank 64 was reached after 69 candidate derivatives).  This shows that no
nonzero linear combination of those outputs is affine in the 288 round inputs.
Turning this computation into a repository-grade lower bound still requires a
checked certificate and the abstract factorization theorem for Freigen's `M`
semantics.

The missing 229-row theorem would have to exclude a 228-row encoding in which
an arbitrary Boolean witness depends jointly on all 288 round inputs and its
parity rows simultaneously encode rotations, `Ch`, `Maj`, both modular
additions, output bits, and quotient bits.  The existing local `UNSAT`
certificates cannot simply be added: a global parity row can span multiple bit
positions or expression families.  No direct-sum theorem for this unrestricted
linear zero-set extension model has been established here.

Accordingly, the supported claim is:

- **proved exactly:** the listed local and cross-expression exclusions;
- **verified construction:** 229 internal rows per ordinary round;
- **computed unrestricted lower-bound candidate:** 64 rows, pending a checked
  derivative certificate and the abstract factorization theorem; and
- **not proved:** global optimality of 229 rows under arbitrary witnesses and
  unbounded `mCols`.

## Exactly excluded carry encodings

For the fused schedule/round block, the three carries have ranges

```text
qW in [0,3], qE in [0,5], qA in [0,3].
```

The carry search established:

- 65 distinct carry triples were produced and re-evaluated from concrete
  32-bit SHA-256 witnesses.  Therefore no carry-only encoding using six
  Boolean bits can be injective, regardless of decoder form.
- Exact half-plane arrangement enumeration found all 84 relaxed 32-bit
  output-conditioned shapes, with at most 44 states per shape.  The arrangement
  algorithm agrees with exhaustive enumeration in the four-bit reference case.
- The 84 shapes induce 47 distinct `(qE,qA)` shapes.  For the maximal 11-state
  shape, four affine cube bits are sufficient, but no single base covers every
  output-conditioned shape.
- Exhausting all sign- and order-normalized viable four-generator families
  found exactly 14 viable families and a minimum constant base dictionary of
  three entries.  In particular, dictionaries of size one or two are excluded
  in this conditional four-generator model.
- The fully coupled carry union contains 88 states.  The 65-state concrete
  lower bound excludes six bits, while an explicit six-generator construction
  plus one base-selection bit covers the union.  Thus seven Boolean bits are
  necessary and sufficient for this witnessed affine carry encoding model.

This rules out reducing the current seven coupled carry bits merely by changing
their affine basis, including a basis with rational coefficients.

## Exact schedule-basis observation

Both SHA-256 small-sigma maps are invertible 32-by-32 GF(2) maps.  Their inverse
row weights total 525 for `sigma0` and 571 for `sigma1`; individual inverse rows
have weights 14--21 and 11--23, respectively.  Choosing either sigma output as
the committed basis leaves 32 inverse-word characters and 32 characters for
the other sigma, with no duplicates between those sets.

More generally, the word bits, `sigma0` bits, and `sigma1` bits are 96 distinct
nonzero linear characters.  An invertible change of the 32 committed basis
bits preserves distinctness.  Therefore a pure linear basis substitution can
move these 96 rows but cannot reduce their count.  Avoiding schedule-word rows
requires a genuinely nonlinear cross-expression encoding, not merely
committing to a different invertible transform.

## Exhaustive only for a named candidate family

For three consecutive `Ch` terms, the six-to-five-row search was also run for
117 distinct low-complexity auxiliary truth tables.  The family contains:

- all two- and three-input AND and OR monomials over the five shared inputs;
- every ordered three-distinct-input `Ch` predicate;
- every three-input `Maj` predicate;
- every nonempty XOR of the three `Ch` outputs; and
- AND, OR, and majority of the three `Ch` outputs.

For each fixed truth table, Z3 selected from the complete parity-character
space and proved that no set of at most five rows supports both an exact
zero-set equation and decoder.  All 117 cases were `UNSAT`, with zero unknowns.

This result is exhaustive for those 117 truth tables only.  It does **not**
exclude all possible one-bit witnesses for the three-`Ch` chain.

## Not excluded

The following remain open and must not be cited as lower bounds:

- an arbitrary one-bit witness for three consecutive `Ch` terms: the fully
  symbolic and CEGIS mask searches were stopped without a result;
- arbitrary higher-rank auxiliary encodings for the three-`Ch` chain;
- a fully coupled 228-row encoding of an ordinary round with an arbitrary
  global witness truth table;
- larger cross-round expressions not listed in the exact table;
- encodings that add nonlinear R1CS constraints; and
- reductions that change the surrounding circuit semantics rather than only
  its linear zero-set encoding.

## Reproduction

The recorded SMT runs used Z3 4.16.0.

```sh
nix shell nixpkgs#z3 -c python3 scripts/search_sha256_carry_encoding.py
nix shell nixpkgs#z3 -c python3 scripts/search_sha256_cross_bit_zero_sets.py
nix shell nixpkgs#z3 -c python3 scripts/search_sha256_cross_bit_zero_sets.py \
  --three-ch-candidates
python3 scripts/analyze_sha256_schedule_basis.py
```

The exact search implementations were introduced in commits `69221e4`,
`1229410`, `6ac8492`, and `b42adb2`.
