import Freigen.Reflect
import Freigen.Examples.Circuit.Basic

/-!
# Poseidon over the BN254 scalar field, for 4 inputs

A faithful implementation of the **Poseidon** permutation and sponge hash over
`Fr := ZMod Bn254Fr` (the BN254 / alt-bn128 scalar field), specialised to **4 input elements**.

The structure follows the Poseidon paper (HADESMiR) exactly:

* state width `t = 5` (rate 4 + capacity 1), S-box `x ↦ x⁵`;
* `R_F = 8` **full** rounds (4 at the start, 4 at the end) and `R_P = 60` **partial** rounds;
* each round is *Add-Round-Constants → S-box layer → MDS mixing*; full rounds apply the S-box to
  every lane, partial rounds only to lane 0.

The **MDS matrix is genuinely MDS**: it is a Cauchy matrix `M[i][j] = 1/(x_i + y_j)` with the
`x_i`, `y_j` chosen distinct and all sums non-zero — Cauchy matrices are provably MDS over a
field, which is exactly the construction the Poseidon reference uses.

The **round constants** here are produced by a simple deterministic field formula (documented
below).  This makes the file self-contained and reproducible, but it is *not* the Grain-LFSR
sequence used by a specific deployment (e.g. circomlib).  The permutation/sponge *structure* is
the real thing; to match a particular reference's known-answer test vectors, drop that
reference's official constants into `roundConst` (and confirm `t`, `R_F`, `R_P`, and the input
layout match).  No known-answer test is asserted here precisely because the constants are ours.

The hash is exposed three ways:

* `poseidon4 : Vector Fr 4 → Fr` — the pure mathematical hash (the spec / denotation);
* `poseidon4F` — it wrapped as a trivial `Free (Effect CircOp)` computation, runnable by `runCirc`;
* `knowsPreimage` / `poseidonHinted` — small **circuits** that exercise `assert` (a preimage
  check that can *fail*) and `hint` (advice = the off-circuit hash), run with `runCirc`.

This is also the headline consumer of the new `Vector` support: the whole permutation is phrased
over `Vector Fr t` and `Vector (Vector Fr t) t` (the state and the MDS matrix).
-/

namespace Freigen
namespace Poseidon

/-! ## The field and parameters -/

/-- The BN254 (alt-bn128) scalar field modulus `r`. -/
def Bn254Fr : Nat :=
  21888242871839275222246405745257275088548364400416034343698204186575808495617

/-- The BN254 scalar field, the field Poseidon hashes over. -/
abbrev Fr : Type := ZMod Bn254Fr

/-- State width: 4 inputs (rate) + 1 capacity lane. -/
abbrev t : Nat := 5
/-- Number of **full** rounds (S-box on every lane): 4 at the start + 4 at the end. -/
abbrev rF : Nat := 8
/-- Number of **partial** rounds (S-box on lane 0 only). -/
abbrev rP : Nat := 60
/-- Total rounds. -/
abbrev rounds : Nat := rF + rP

/-! ## The S-box, round constants, and MDS matrix -/

/-- The Poseidon S-box for BN254: `x ↦ x⁵` (the smallest `α` with `gcd(α, r-1) = 1`). -/
def sbox (x : Fr) : Fr := x ^ 5

/-- A deterministic round-constant schedule (see the file header: reproducible, but *not* the
    official Grain-LFSR constants — substitute those to match a specific reference). -/
def roundConst (k : Nat) : Fr := ((k : Fr) + 1) ^ 5 + 5 * (k : Fr) + 7

/-- The `i`-th add-round-constant for round `round`. -/
def ark (round i : Nat) : Fr := roundConst (round * t + i)

/-- The MDS matrix as a Cauchy matrix `M[i][j] = 1/(x_i + y_j)` with `x_i = i`, `y_j = t + j`:
    the `x_i` are distinct, the `y_j` are distinct, and every `x_i + y_j ∈ [t, 3t-2]` is non-zero
    in `Fr`, so the matrix is invertible and MDS. -/
def mds : Vector (Vector Fr t) t :=
  Vector.ofFn (fun i => Vector.ofFn (fun j => ((i.val : Fr) + (t : Fr) + (j.val : Fr))⁻¹))

/-! ## The permutation -/

/-- Add the round constants of `round` to the state. -/
def addRoundConstants (round : Nat) (s : Vector Fr t) : Vector Fr t :=
  Vector.ofFn (fun i => s[i] + ark round i.val)

/-- The multiply-by-MDS mixing layer: `s' i = ∑ⱼ M[i][j] · s[j]`. -/
def applyMds (s : Vector Fr t) : Vector Fr t :=
  Vector.ofFn (fun i => (List.finRange t).foldl (fun acc j => acc + mds[i][j] * s[j]) 0)

/-- One round.  Full rounds (the first and last `R_F/2`) apply the S-box to every lane; partial
    rounds (the middle `R_P`) apply it to lane 0 only. -/
def round (r : Nat) (s : Vector Fr t) : Vector Fr t :=
  let s := addRoundConstants r s
  let s := if r < rF / 2 || r ≥ rF / 2 + rP
           then s.map sbox                                       -- full S-box layer
           else Vector.ofFn (fun i => if i.val = 0 then sbox s[i] else s[i])  -- partial
  applyMds s

/-- The Poseidon permutation on a width-`t` state: all `R_F + R_P` rounds, in order. -/
def perm (s0 : Vector Fr t) : Vector Fr t :=
  (List.range rounds).foldl (fun s r => round r s) s0

/-! ## The sponge hash for 4 inputs -/

/-- Load 4 inputs into a fresh state: lane 0 is the (zero) capacity, lanes 1–4 the inputs. -/
def absorb (xs : Vector Fr 4) : Vector Fr t :=
  ⟨#[0, xs[0], xs[1], xs[2], xs[3]], rfl⟩

/-- **Poseidon hash of 4 field elements** (the pure spec): absorb the inputs, run the
    permutation once (rate 4 covers all inputs), and squeeze lane 0. -/
def poseidon4 (xs : Vector Fr 4) : Fr := (perm (absorb xs))[0]

/-! ## Circuit phrasings (run with the `runCirc` semantics) -/

/-- The hash as a (trivial, effect-free) circuit computation. -/
def poseidon4F (xs : Vector Fr 4) : Free (Effect CircOp) Fr := pure (poseidon4 xs)

/-- A **preimage-knowledge** circuit: compute the hash of `xs` and `assert` it equals the public
    `target`.  Under `runCirc` this returns `some target` exactly when `xs` is a preimage of
    `target`, and `none` otherwise (the `assert` is the potential failure). -/
def knowsPreimage (target : Fr) (xs : Vector Fr 4) : Free (Effect CircOp) Fr := do
  let h := poseidon4 xs
  let _ ← assert (h == target)
  pure h

/-- A circuit using **both** effects: `hint` supplies the hash as off-circuit *advice* (the
    `hint`'s evaluator is the hash itself), then we `assert` that advice matches a recomputation
    — i.e. advice is constrained.  Under `runCirc` this always yields `some (poseidon4 xs)`. -/
def poseidonHinted (xs : Vector Fr 4) : Free (Effect CircOp) Fr := do
  let h ← hintF xs poseidon4
  let _ ← assert (h == poseidon4 xs)
  pure h

/-! ## Why Poseidon is *run* (via `runCirc`) rather than *reflected*

Vectors are now a first-class object *type* (`reflect%` happily reifies `Vector Fr 4`), but the
elaborator still has no way to lower vector *operations* — indexing `v[i]`, `Vector.ofFn`,
`Vector.map`, the MDS `foldl` — into AST nodes (there is no `vecGet`/`vecMap`/… primitive, and
`set`/`map`/`fold` would need new ternary/higher-order constructors).  So reflecting the hash
**fails**, and it fails on exactly that boundary: the result/argument *types* reify fine, but the
body hits a vector op on a bound variable with no matching object primitive.  (This is the "hard
part" — see the module header of `Circuit`.) -/
#check_failure (reflect% poseidon4F)

/-- A sample input vector `[1, 2, 3, 4]`. -/
def sample : Vector Fr 4 := ⟨#[1, 2, 3, 4], rfl⟩

-- The pure hash computes to a concrete BN254 field element:
#eval IO.println s!"poseidon4 [1,2,3,4] = {(poseidon4 sample).val}"

-- The effect-free phrasing runs to `some` of that same value (definitionally, no evaluation):
example : runCirc (poseidon4F sample) = some (poseidon4 sample) := rfl

-- Preimage check: succeeds for the true preimage, fails (`none`) for a wrong target.  These
-- compare concrete field elements, so they are discharged by `native_decide` (which compiles and
-- runs the permutation) rather than `rfl` (which would evaluate it in the kernel).
example : runCirc (knowsPreimage (poseidon4 sample) sample) = some (poseidon4 sample) := by
  native_decide
example : runCirc (knowsPreimage (poseidon4 sample + 1) sample) = none := by
  native_decide

-- The hint-plus-assert phrasing always succeeds (advice = recomputation):
example : runCirc (poseidonHinted sample) = some (poseidon4 sample) := by native_decide

#eval IO.println s!"runCirc (knowsPreimage h [1,2,3,4]) with correct h ⇒ \
  {(runCirc (knowsPreimage (poseidon4 sample) sample)).map (·.val)}"
#eval IO.println s!"runCirc (knowsPreimage (h+1) [1,2,3,4]) ⇒ isSome = \
  {(runCirc (knowsPreimage (poseidon4 sample + 1) sample)).isSome}"

end Poseidon
end Freigen
