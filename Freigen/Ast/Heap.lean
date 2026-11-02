import Freigen.Ast.Defs

/-!
Heap discipline: allocation extends the heap with a fresh reference, and
lookups are stable under extension. After this file nothing mentions the
underlying hash map.
-/

namespace Freigen.Ast

variable {eff : EffSig} {γ : eff.Ctx} {i o : Tp}

namespace Heap

/-- Allocation extends the heap. -/
theorem le_alloc (s : Heap eff)
    (f : Tp.denote (.fn i o) → Tp.denote i → Expr eff Tp.denote γ o) :
    s ≤ (s.alloc f).1 := by
  refine ⟨Nat.le_succ _, fun id hid => ?_⟩
  simp only [alloc, Std.ExtHashMap.get?_eq_getElem?,
    Std.ExtHashMap.getElem?_insert]
  grind

/-- The allocated reference did not resolve before. -/
theorem lookup_alloc_ref (s : Heap eff)
    (f : Tp.denote (.fn i o) → Tp.denote i → Expr eff Tp.denote γ o)
    {γ' : eff.Ctx} {i' o' : Tp} :
    s.lookup (γ := γ') (i := i') (o := o') (s.alloc f).2 = none := by
  have : s.env[s.next]? = none := by
    rw [← Option.not_isSome_iff_eq_none,
      ← Std.ExtHashMap.contains_eq_isSome_getElem?, ← s.env_supp]
    exact Nat.lt_irrefl _
  simp [alloc, lookup, this]

/-- A freshly allocated reference resolves to what was allocated. -/
@[simp]
theorem lookup_alloc (s : Heap eff)
    (f : Tp.denote (.fn i o) → Tp.denote i → Expr eff Tp.denote γ o) :
    (s.alloc f).1.lookup (s.alloc f).2 = some (f (s.alloc f).2) := by
  simp [alloc, lookup]

/-- Lookup is stable under extension. -/
theorem lookup_mono {s s' : Heap eff} (hs : s ≤ s') {r : FnRef}
    {g : Tp.denote i → Expr eff Tp.denote γ o}
    (hl : s.lookup r = some g) : s'.lookup r = some g := by
  have hget : s'.env.get? r = s.env.get? r := by
    refine (hs.2 r ?_).symm
    rw [s.env_supp]
    rcases h : s.env.get? r with _ | entry
    · simp only [Std.ExtHashMap.get?_eq_getElem?] at h
      simp [lookup, h] at hl
    · rw [Std.ExtHashMap.contains_eq_isSome_getElem?,
        ← Std.ExtHashMap.get?_eq_getElem?, h]
      rfl
  have : s'.lookup (γ := γ) (i := i) (o := o) r = s.lookup r := by
    simp only [lookup, hget]
  rw [this, hl]

end Heap

end Freigen.Ast
