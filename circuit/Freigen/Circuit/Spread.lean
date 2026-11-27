import Mathlib.Data.ZMod.Basic

namespace Freigen.Circuit.Spread

def _root_.Nat.spread : Nat → Nat := Nat.binaryRec 0 (fun b n => 4*n + if b then 1 else 0)

def _root_.ZMod.spread {n} : ZMod n → ZMod n := fun x => x.val.spread

end Freigen.Circuit.Spread
