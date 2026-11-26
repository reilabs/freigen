import Freigen.Ast.JoinPoints.Alg
import Freigen.Ast.JoinPoints.Eutt
import Freigen.Ast.Cert

/-!
Join-point elimination preserves the meaning of well-formed programs, in
every model of a language whose primitives do not handle references: on every
input, the translation is equivalent to the program up to silent steps. So
every certificate of the program is one of its translation.
-/

namespace Freigen.Ast

open JoinPoints

variable {L : Language} [L.Blocks] {γ : L.Ctx} {iT oT : L.AbiTp}

/-- Join-point elimination does not change what a program does. -/
theorem Program.joinPoints_eutt (hprim : L.PrimFnFree) {M : L.Model}
    {p : ∀ {V : L.Tp → Type}, Program L γ iT oT V} (hp : Program.Wf p) (x : M.V iT.val) :
    CompM.Eutt (p.denote x) ((Program.joinPoints p).denote x) :=
  (Program.joinPoints_jp hp M.V).eutt hprim x

/-- Certificates survive join-point elimination. -/
theorem ProgramCert.joinPoints (hprim : L.PrimFnFree) {M : L.Model} {ℓ : Lift.{u, w} L M}
    {α : M.V iT.val → Type} {r : (i : M.V iT.val) → ℓ.Rep oT (α i)}
    {p : ∀ {V : L.Tp → Type}, Program L γ iT oT V} {t : (i : M.V iT.val) → Free ℓ.SrcOp γ (α i)}
    (hp : Program.Wf p) (h : ProgramCert ℓ r p t) :
    ProgramCert ℓ r (Program.joinPoints p) t :=
  fun i => (h i).of_eutt (Program.joinPoints_eutt hprim hp i)

end Freigen.Ast
