import Freigen.IxPoly.Defs
import Freigen.IxPoly.Constructions

/-!
The simple unindexed case, to check we're making sense: defining lists and streams
as the W / M constructions of F X = 1 + A * X
-/

namespace Freigen.IxPoly

def ListP (A : Type) : Unit ⟹ₚ Unit := 1 + (C (fun _ => A) * X id)

def ListP_action {A Y} : (ListP A) Y () ≃ Unit ⊕ (A × Y ()) := by
  apply Iso.trans add_action
  apply Iso.sumCongr one_action
  apply Iso.trans mul_action
  apply Iso.prodCongr C_action X_action

def WList (A : Type) : Type := W (ListP A) ()

def StreamP (A : Type) : Unit ⟹ₚ Unit := C (fun _ => A) * X id

def StreamP_action {A Y} : (StreamP A) Y () ≃ A × Y () := by
  apply Iso.trans mul_action
  apply Iso.prodCongr C_action X_action

def Stream (A : Type) : Type := (StreamP A).M ()

def Stream.head {A} (s : Stream A) : A :=
  ((M.observe s)).1.1

def Stream.tail {A} (s : Stream A) : Stream A :=
  (StreamP_action (M.observe s)).2

def Stream.corec {A B} (f : A → (B × A)) (a : A) : Stream B :=
  M.corec (fun _ a => StreamP_action.symm (f a)) a

theorem Stream.head_corec:
    (Stream.corec f x).head = (f x).1 := by
  rfl

theorem Stream.tail_corec:
    (Stream.corec f x).tail = Stream.corec f ((f x).2) := by
  rfl

private theorem StreamP_liftR_iff:
  M.LiftR (StreamP A) R () x y ↔
    ((StreamP_action x).1 = (StreamP_action y).1 ∧ R () (StreamP_action x).2 (StreamP_action y).2) := by
  rcases x with ⟨hx, tx⟩
  rcases y with ⟨hy, ty⟩
  apply Iff.intro
  · intro h
    rcases h
    apply And.intro rfl
    apply_assumption
  · rintro ⟨h1, h2⟩
    rcases hy with ⟨hy, ⟨⟩⟩
    rcases hx with ⟨hx, ⟨⟩⟩
    cases h1
    constructor
    intro a
    rcases a with a|a
    · cases a
    exact h2

def Stream.bisim {A a b} (R : Stream A → Stream A → Prop)
  (h_stable : ∀x y, R x y → x.head = y.head ∧ R x.tail y.tail)
  (h : R a b) : a = b := by
  apply M.Bisim.coind (R := fun _ x y => R x y)
  · rintro ⟨⟩ ta tb ht
    simp only [M.bisimOp]
    rw [StreamP_liftR_iff]
    exact h_stable _ _ ht
  · exact h

def Stream.take (s : Stream A): Nat → List A
| 0 => []
| n + 1 => Stream.head s :: Stream.take (Stream.tail s) n

def allNats : Stream Nat := Stream.corec (fun n => (n, n + 1)) 0

#eval allNats.take 10

def iterate (f : A → A) (a : A) : Stream A :=
  Stream.corec (fun a => (a, f a)) a

def allEvens := iterate (fun n => n + 2) 0

#eval allEvens.take 10

def Stream.map {A B} (f : A → B): Stream A → Stream B :=
  Stream.corec (fun a => (f a.head, a.tail))

theorem Stream.head_map {A B} (f : A → B) (s : Stream A):
    (Stream.map f s).head = f (s.head) := by
  rfl

theorem Stream.tail_map {A B} (f : A → B) (s : Stream A):
    (Stream.map f s).tail = Stream.map f (s.tail) := by
  rfl

#eval (allNats.map (fun n => n * 2)).take 10

example : allNats.map (· * 2) = allEvens := by
  apply Stream.bisim (R :=
    fun x y => ∃ n,
      y = iterate (fun n => n + 2) (n * 2) ∧
      x = Stream.map (· * 2) (iterate (fun n => n + 1) n))
  · intro x y hex
    rcases hex with ⟨n, rfl, rfl⟩
    simp only [iterate, Stream.head_corec, Stream.tail_corec, Stream.head_map, Stream.tail_map]
    exists True.intro, n + 1
    apply And.intro <;> congr 1 ; omega
  · exists 0

inductive HList (I : Type) (A : I → Type) : List I → Type where
| nil : HList I A []
| cons {i : I} {is : List I}: A i → HList I A is → HList I A (i :: is)

def HStreamP (I : Type) (A : I → Type) : Stream I ⟹ₚ Stream I := C (fun i => A i.head) * X (fun i => i.tail)

end Freigen.IxPoly
