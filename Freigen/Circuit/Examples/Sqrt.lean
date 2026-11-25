import Freigen.Circuit.Lift

/-!
A square root, computed in a hint and checked in constraints: certified by
hand from the certificate rules only, and lifted by the macro, which produces
the same AST. The AST does not depend on the prime or the circuit context; the
certificate holds for all of them.

Then programs that compute with `Cert`s, which the AST erases.
-/

namespace Freigen.Circuit.Examples.Sqrt

open Ast Lift

variable {P : Nat} [ctx : Context P]

noncomputable def srcSqrt (x : ctx.W) : Circuit P ctx.W := do
  let r ← Circuit.hint #v[x] fun inputs => pure #v[fsqrt inputs[0]]
  let _ ← Circuit.assertR1C r[0] r[0] x
  pure r[0]

abbrev wireAbi : Lift.AbiTp := .base .wire

def sqrtAst {V : language.Tp → Type} : Program language Scope.constraint wireAbi wireAbi V :=
  .main fun x =>
    .builtin (.vecLit 1) h![x] fun xs =>
    .op (L := language) (γ := Scope.constraint) (ConstraintOp.hint 1 1) xs
      (fun _ ins =>
        .builtin (.vecGet 1 0 (by decide)) h![ins] fun v =>
        .builtin (.prim .fSqrt) h![v] fun s =>
        .builtin (.vecLit 1) h![s] fun v => .ret v)
      fun rs =>
    .builtin (.vecGet 1 0 (by decide)) h![rs] fun r =>
    assertR1CAst r r x fun _ =>
    .builtin (.vecGet 1 0 (by decide)) h![rs] fun r' => .ret r'

theorem sqrtCert : ProgramCert (lift P) (fun _ => Rep.self (P := P) wireAbi) sqrtAst (srcSqrt (P := P)) := by
  refine .of_progCert <| .main (fun x => ?_)
  refine ExprCert.builtin (spec := simSpec P) (γ := Scope.constraint) (o := .base .wire)
    (R := Eq) (b := .vecLit 1) (args := h![x]) (r := #v[x]) rfl ?_
  refine Rules.hint (n := 1) (m := 1) (args := #v[x])
    (body := fun ins =>
      .builtin (.vecGet 1 0 (by decide)) h![ins] fun v =>
      .builtin (.prim .fSqrt) h![v] fun s =>
      .builtin (.vecLit 1) h![s] fun v => .ret v)
    (src := fun (ins : Vector (ZMod P) 1) => pure #v[fsqrt ins[0]])
    (k := fun rs =>
      .builtin (.vecGet 1 0 (by decide)) h![rs] fun r =>
      assertR1CAst r r x fun _ =>
      .builtin (.vecGet 1 0 (by decide)) h![rs] fun r' => .ret r')
    (tk := fun rs => Circuit.assertR1C rs[0] rs[0] x >>= fun _ => pure rs[0])
    (fun (ins : Vector (ZMod P) 1) => ?_) fun (rs : Vector ctx.W 1) => ?_
  · refine ExprCert.builtin (spec := simSpec P) (γ := Scope.hint) (o := .vec 1 (.base .field))
      (R := Eq) (b := .vecGet (a := Tp.field) 1 0 (by decide)) (r := ins[0]) rfl ?_
    refine ExprCert.builtin (spec := simSpec P) (γ := Scope.hint) (o := .vec 1 (.base .field))
      (R := Eq) (b := .prim .fSqrt) (r := fsqrt ins[0]) rfl ?_
    exact ExprCert.builtin (spec := simSpec P) (γ := Scope.hint) (o := .vec 1 (.base .field))
      (R := Eq) (b := .vecLit 1) (r := #v[fsqrt ins[0]]) rfl (.ret rfl)
  · refine ExprCert.builtin (spec := simSpec P) (γ := Scope.constraint) (o := .base .wire)
      (R := Eq) (b := .vecGet (a := Tp.wire) 1 0 (by decide)) (r := rs[0]) rfl ?_
    refine Rules.assertR1C fun _ _ => ?_
    exact ExprCert.builtin (spec := simSpec P) (γ := Scope.constraint) (o := .base .wire)
      (R := Eq) (b := .vecGet (a := Tp.wire) 1 0 (by decide)) (r := rs[0]) rfl (.ret rfl)

/-- info: 'Freigen.Circuit.Examples.Sqrt.sqrtCert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms sqrtCert

/--
info: (program
  (main constraint (v0 wire) wire
    (let v1 (vecLit v0))
    (let v2
      (op (hint 1 1) v1
        (block body (v3)
          (let v4 (vecGet 0 v3))
          (let v5 (fSqrt v4))
          (let v6 (vecLit v5))
          (ret v6))))
    (let v7 (vecGet 0 v2))
    (let v8 (pair v7 v0))
    (let v9 (pair v7 v8))
    (let v10 (op assertR1C v9))
    (let v11 (vecGet 0 v2))
    (ret v11)))
-/
#guard_msgs in #eval IO.println (sqrtAst (V := fun _ => String)).pretty

/-! ## Lifted by the macro -/

lift_program liftedSqrt := srcSqrt via lift

/--
info: Freigen.Circuit.Examples.Sqrt.liftedSqrt.cert (P : ℕ) [ctx : Context P] :
  ProgramCert (lift P) (fun x => Rep.self (AbiTp.base Base.wire ⋯)) (fun {V} => liftedSqrt.ast) srcSqrt
-/
#guard_msgs in #check liftedSqrt.cert

/-- info: 'Freigen.Circuit.Examples.Sqrt.liftedSqrt.cert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms liftedSqrt.cert

/-- The macro's AST is the hand-written one. -/
example : @liftedSqrt.ast = @sqrtAst := rfl

/-! ## More programs -/

/-- A hint returning two witnesses, field and wire arithmetic, a `let` used twice, and
a range check whose result is ignored. -/
def srcMore (x : ctx.W) : Circuit P ctx.W := do
  let ys ← Circuit.hint #v[x] fun ins => do
    let a := ins[0] * ins[0] + ins[0]
    let b := -ins[0]
    pure #v[a, b]
  let s := ys[0] - ys[1] + x
  let _ ← Circuit.rangeCheck 8 s
  pure (-s)

lift_program liftedMore := srcMore via lift

/--
info: Freigen.Circuit.Examples.Sqrt.liftedMore.cert (P : ℕ) [ctx : Context P] :
  ProgramCert (lift P) (fun x => Rep.self (AbiTp.base Base.wire ⋯)) (fun {V} => liftedMore.ast) srcMore
-/
#guard_msgs in #check liftedMore.cert

/--
info: (program
  (main constraint (v0 wire) wire
    (let v1 (vecLit v0))
    (let v2
      (op (hint 1 2) v1
        (block body (v3)
          (let v4 (vecGet 0 v3))
          (let v5 (fMul v4 v4))
          (let v6 (vecGet 0 v3))
          (let v7 (fAdd v5 v6))
          (let v8 (vecGet 0 v3))
          (let v9 (fNeg v8))
          (let v10 (vecLit v7 v9))
          (ret v10))))
    (let v11 (vecGet 0 v2))
    (let v12 (vecGet 1 v2))
    (let v13 (wSub v11 v12))
    (let v14 (wAdd v13 v0))
    (let v15 (op (rangeCheck 8) v14))
    (let v16 (wNeg v14))
    (ret v16)))
-/
#guard_msgs in #eval IO.println (liftedMore.ast (V := fun _ => String)).pretty

/-- A hint returning six witnesses: vector literals have no length limit. -/
def srcSix (x : ctx.W) : Circuit P ctx.W := do
  let ys ← Circuit.hint #v[x, x + x] fun ins =>
    pure #v[ins[0], ins[1], ins[0] * ins[1], -ins[0], ins[1] - ins[0], ins[0] + ins[1]]
  pure (ys[0] + ys[5])

lift_program liftedSix := srcSix via lift

/-- info: 'Freigen.Circuit.Examples.Sqrt.liftedSix.cert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms liftedSix.cert

/--
info: (program
  (main constraint (v0 wire) wire
    (let v1 (wAdd v0 v0))
    (let v2 (vecLit v0 v1))
    (let v3
      (op (hint 2 6) v2
        (block body (v4)
          (let v5 (vecGet 0 v4))
          (let v6 (vecGet 1 v4))
          (let v7 (vecGet 0 v4))
          (let v8 (vecGet 1 v4))
          (let v9 (fMul v7 v8))
          (let v10 (vecGet 0 v4))
          (let v11 (fNeg v10))
          (let v12 (vecGet 1 v4))
          (let v13 (vecGet 0 v4))
          (let v14 (fSub v12 v13))
          (let v15 (vecGet 0 v4))
          (let v16 (vecGet 1 v4))
          (let v17 (fAdd v15 v16))
          (let v18 (vecLit v5 v6 v9 v11 v14 v17))
          (ret v18))))
    (let v19 (vecGet 0 v3))
    (let v20 (vecGet 5 v3))
    (let v21 (wAdd v19 v20))
    (ret v21)))
-/
#guard_msgs in #eval IO.println (liftedSix.ast (V := fun _ => String)).pretty

/-! ## Computing with certificates

Certificates are erased: a source may keep them, transform them and return
them, and the AST computes with their representatives. -/

/-- A boolean wire, returned with its certificate rephrased by `Cert.map`. -/
def srcBool (x : ctx.W) : Circuit P (CertW (P := P) fun b ρ => ρ b = ρ b * ρ b) := do
  let bs ← Circuit.hint #v[x] fun ins => pure #v[ins[0] * ins[0]]
  let b := bs[0]
  let c ← Circuit.assertR1C b b b
  let c' : Cert (fun ρ => ρ b = ρ b * ρ b) := Cert.map (fun _ h => h.symm) c
  pure ⟨b, c'⟩

lift_program liftedBool := srcBool via lift

/-- The result is a `CertW`, represented by its wire: the AST returns the
wire of the source's `CertW`. -/
example (P : Nat) [Context P] :
    ProgramCert (lift P) (fun _ => Rep.certW (P := P) fun b ρ => ρ b = ρ b * ρ b) liftedBool.ast
      (srcBool (P := P)) :=
  liftedBool.cert P

/-- info: 'Freigen.Circuit.Examples.Sqrt.liftedBool.cert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms liftedBool.cert

/--
info: (program
  (main constraint (v0 wire) wire
    (let v1 (vecLit v0))
    (let v2
      (op (hint 1 1) v1
        (block body (v3)
          (let v4 (vecGet 0 v3))
          (let v5 (fMul v4 v4))
          (let v6 (vecLit v5))
          (ret v6))))
    (let v7 (vecGet 0 v2))
    (let v8 (pair v7 v7))
    (let v9 (pair v7 v8))
    (let v10 (op assertR1C v9))
    (ret v7)))
-/
#guard_msgs in #eval IO.println (liftedBool.ast (V := fun _ => String)).pretty

/-- A certificate about a computed wire, returned with it. -/
def srcSumCert (x : ctx.W) : Circuit P (CertW (P := P) fun r => R1CSAssertion r r r) := do
  let w := x + x
  let c ← Circuit.assertR1C w w w
  pure ⟨w, c⟩

lift_program liftedSumCert := srcSumCert via lift

/-- info: 'Freigen.Circuit.Examples.Sqrt.liftedSumCert.cert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms liftedSumCert.cert

/--
info: (program
  (main constraint (v0 wire) wire
    (let v1 (wAdd v0 v0))
    (let v2 (pair v1 v1))
    (let v3 (pair v1 v2))
    (let v4 (op assertR1C v3))
    (ret v1)))
-/
#guard_msgs in #eval IO.println (liftedSumCert.ast (V := fun _ => String)).pretty


/-- A range-checked wire, used through its value and returned. -/
def srcRange (x : ctx.W) : Circuit P (WUInt P 8) := do
  let w ← Circuit.rangeCheck 8 x
  let y := w.val + w.val
  let _ ← Circuit.assertR1C y y w.val
  pure w

lift_program liftedRange := srcRange via lift

/--
info: Freigen.Circuit.Examples.Sqrt.liftedRange.cert (P : ℕ) [ctx : Context P] :
  ProgramCert (lift P) (fun x => Rep.certW (RangeAssertion 8)) (fun {V} => liftedRange.ast) srcRange
-/
#guard_msgs in #check liftedRange.cert

/-- info: 'Freigen.Circuit.Examples.Sqrt.liftedRange.cert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms liftedRange.cert

/--
info: (program
  (main constraint (v0 wire) wire
    (let v1 (op (rangeCheck 8) v0))
    (let v2 (wAdd v0 v0))
    (let v3 (pair v2 v0))
    (let v4 (pair v2 v3))
    (let v5 (op assertR1C v4))
    (ret v0)))
-/
#guard_msgs in #eval IO.println (liftedRange.ast (V := fun _ => String)).pretty

/-- Helpers taking and returning `WUInt`s: their function certificates erase
them to their wires, and the AST passes the wires. -/
def checkByte (x : ctx.W) : Circuit P (WUInt P 8) := Circuit.rangeCheck 8 x

def double (w : WUInt P 8) : Circuit P ctx.W := pure (w.val + w.val)

def srcHelpers (x : ctx.W) : Circuit P ctx.W := do
  let w ← checkByte x
  double w

lift_program liftedHelpers := srcHelpers via lift using [checkByte, double]

/-- info: 'Freigen.Circuit.Examples.Sqrt.liftedHelpers.cert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms liftedHelpers.cert

/--
info: (program
  (define f0 constraint (v1 wire) wire (let v2 (op (rangeCheck 8) v1)) (ret v1))
  (define f3 constraint (v4 wire) wire (let v5 (wAdd v4 v4)) (ret v5))
  (main constraint (v6 wire) wire
    (let v7 (app f0 v6))
    (let v8 (app f3 v7))
    (ret v8)))
-/
#guard_msgs in #eval IO.println (liftedHelpers.ast (V := fun _ => String)).pretty

/-! ## Results that depend on the argument -/

/-- A gadget whose certificate is about its argument. -/
def srcDependent (x : ctx.W) : Circuit P (CertW (P := P) fun r => R1CSAssertion x x r) := do
  let c ← Circuit.assertR1C x x x
  pure ⟨x, c⟩

lift_program liftedDependent := srcDependent via lift

/-! The source's result type, and so its representation, depends on the input; it is
erased to the wire. -/

/--
info: Freigen.Circuit.Examples.Sqrt.liftedDependent.cert (P : ℕ) [ctx : Context P] :
  ProgramCert (lift P) (fun x => Rep.certW fun r => R1CSAssertion x x r) (fun {V} => liftedDependent.ast) srcDependent
-/
#guard_msgs in #check liftedDependent.cert

/-- As a helper, called on its own result. -/
def srcUseDependent (x : ctx.W) : Circuit P ctx.W := do
  let w ← srcDependent x
  let w' ← srcDependent w.val
  pure (w.val + w'.val)

lift_program liftedUseDependent := srcUseDependent via lift using [srcDependent]

/--
info: Freigen.Circuit.Examples.Sqrt.liftedUseDependent.cert (P : ℕ) [ctx : Context P] :
  ProgramCert (lift P) (fun x => Rep.self (AbiTp.base Base.wire ⋯)) (fun {V} => liftedUseDependent.ast) srcUseDependent
-/
#guard_msgs in #check liftedUseDependent.cert

/-- info: 'Freigen.Circuit.Examples.Sqrt.liftedUseDependent.cert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms liftedUseDependent.cert

/--
info: (program
  (define f0 constraint (v1 wire) wire
    (let v2 (pair v1 v1))
    (let v3 (pair v1 v2))
    (let v4 (op assertR1C v3))
    (ret v1))
  (main constraint (v5 wire) wire
    (let v6 (app f0 v5))
    (let v7 (app f0 v6))
    (let v8 (wAdd v6 v7))
    (ret v8)))
-/
#guard_msgs in #eval IO.println (liftedUseDependent.ast (V := fun _ => String)).pretty

/-! ## Branches -/

/-- A branch on a boolean input, joined before an assertion. -/
def srcSelect (p : ctx.W × Bool) : Circuit P ctx.W := do
  let w ← if p.2 then pure (p.1 + p.1) else pure p.1
  let _ ← Circuit.assertR1C w w w
  pure w

lift_program liftedSelect := srcSelect via lift

/-- info: 'Freigen.Circuit.Examples.Sqrt.liftedSelect.cert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms liftedSelect.cert

/--
info: (program
  (main constraint (v0 (prod wire bool)) wire
    (let f1
      (fun (v2 wire)
        (let v3 (pair v2 v2))
        (let v4 (pair v2 v3))
        (let v5 (op assertR1C v4))
        (ret v2)))
    (let v6 (snd v0))
    (let v7
      (if v6
        (do
          (let v8 (fst v0))
          (let v9 (wAdd v8 v8))
          (let v10 (app f1 v9))
          (ret v10))
        (do (let v11 (fst v0)) (let v12 (app f1 v11)) (ret v12))))
    (ret v7)))
-/
#guard_msgs in #eval IO.println (liftedSelect.ast (V := fun _ => String)).pretty

/-! ## Arrays after assertions

The second access is in the continuation of an assertion, whose certificate
may not exist; its bounds proof is the bounds check. -/

def srcCertGet (p : Array ctx.W × UInt32) : Circuit P Unit :=
  if h : p.2 < p.1.size.toUInt32 then do
    let w := p.1[p.2.toNat]'(Ast.toNat_lt_size h)
    let _ ← Circuit.assertR1C w w w
    let v := p.1[p.2.toNat]'(Ast.toNat_lt_size h)
    let _ ← Circuit.assertR1C v v w
    pure ()
  else pure ()

lift_program liftedCertGet := srcCertGet via lift

/-- info: 'Freigen.Circuit.Examples.Sqrt.liftedCertGet.cert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms liftedCertGet.cert

/--
info: (program
  (main constraint (v0 (prod (array wire) u32)) unit
    (let v1 (snd v0))
    (let v2 (fst v0))
    (let v3 (arrLen v2))
    (let v4 (uLt v1 v3))
    (let v5
      (if v4
        (do
          (let v6 (fst v0))
          (let v7 (arrGet v6 v1))
          (let v8 (pair v7 v7))
          (let v9 (pair v7 v8))
          (let v10 (op assertR1C v9))
          (let v11 (fst v0))
          (let v12 (arrGet v11 v1))
          (let v13 (pair v12 v7))
          (let v14 (pair v12 v13))
          (let v15 (op assertR1C v14))
          (let v16 (lit unit ()))
          (ret v16))
        (do (let v17 (lit unit ())) (ret v17))))
    (ret v5)))
-/
#guard_msgs in #eval IO.println (liftedCertGet.ast (V := fun _ => String)).pretty

/-! ## Proofs through certificates -/

/-- A bounds proof that mentions a certificate it does not need. -/
theorem boundWith {A : Assertion (ZMod P) ctx.W} (_ : Cert A) {i : UInt32} {xs : Array ctx.W}
    (h : i < xs.size.toUInt32) : i.toNat < xs.size :=
  Ast.toNat_lt_size h

/-- The second access is proved in bounds through the certificate `c`. The
continuation is only certified where `c` exists, so it may use it. -/
def srcCertBound (p : Array ctx.W × UInt32) : Circuit P Unit :=
  if h : p.2 < p.1.size.toUInt32 then do
    let w := p.1[p.2.toNat]'(Ast.toNat_lt_size h)
    let c ← Circuit.assertR1C w w w
    let v := p.1[p.2.toNat]'(boundWith c h)
    let _ ← Circuit.assertR1C v v v
    pure ()
  else pure ()

lift_program liftedCertBound := srcCertBound via lift

/-- info: 'Freigen.Circuit.Examples.Sqrt.liftedCertBound.cert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms liftedCertBound.cert

/-! ## Rejected sources -/

-- A hint can only return field elements: anything else is a type error.
/--
error: Application type mismatch: The argument
  3
has type
  ℕ
but is expected to have type
  Vector (ZMod P) 1
in the application
  pure 3
-/
#guard_msgs in
example (x : ctx.W) : Circuit P (Vector ctx.W 1) :=
  Circuit.hint #v[x] fun _ => pure (3 : Nat)

end Freigen.Circuit.Examples.Sqrt
