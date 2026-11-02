import Freigen.Ast.Eval
import Freigen.Ast.Examples.Basic

/-!
Unfolding sample programs into silent steps, operations and binds, using the
evaluator equations only.
-/

namespace Freigen.Ast.Examples

open CompM (tick)

/-- A helper defined once and called twice. -/
example (x : UInt32) :
    (doubleTwice (V := Tp.denote)).denote x =
      tick >>= fun _ => tick >>= fun _ => tick >>= fun _ =>
      tick >>= fun _ => tick >>= fun _ => tick >>= fun _ =>
      tick >>= fun _ => pure (x + x + (x + x)) := by
  simp only [Program.denote_eq, doubleTwice, Program.denote'_go_define,
    Program.denote'_go_main, Expr.denote_app_eq, Program.lookup_define,
    Expr.denote_builtin_eq, Builtin.denote, Expr.denote_ret, bind_assoc,
    pure_bind, map_bind, map_pure]

/-- An effect with a block: the block is an independent evaluation. -/
example (x : UInt32) :
    (hintSquare (V := Tp.denote)).denote x =
      CompM.op (E := EvalEff sig) (γ := Scope.main)
          (.inr (.inr (Sigma.mk (MainOp.hint : sig.tag Scope.main) x)))
          (fun _ (y : UInt32) =>
            tick >>= fun _ => tick >>= fun _ => pure (y * y)) >>=
        fun r => tick >>= fun _ => pure r := by
  simp only [Program.denote_eq, hintSquare, Program.denote'_go_main, hint,
    Expr.denote_op, Expr.denote_ret, map_bind, map_pure]
  congr 2
  funext t y
  cases t
  dsimp only
  -- The block lives in a context only reducible through `sig`, which `rw`
  -- does not see through.
  erw [Expr.denote_builtin_eq]
  simp only [Builtin.denote, map_bind]
  erw [Expr.denote_ret]
  simp only [map_bind, map_pure]

end Freigen.Ast.Examples
