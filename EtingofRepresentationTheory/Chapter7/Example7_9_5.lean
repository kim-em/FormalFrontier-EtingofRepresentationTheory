import Mathlib.RepresentationTheory.Maschke

/-!
# Example 7.9.5: Representations of Finite Groups are Semisimple

The category of representations of a finite group G over a field of characteristic
not dividing |G| (or characteristic 0) is semisimple.

## Mathlib correspondence

This is Maschke's theorem. Mathlib has `IsSemisimpleModule` and related results
in `Mathlib.RepresentationTheory.Maschke`.
-/

/-- The category of representations of a finite group G over a field of
characteristic not dividing |G| is semisimple: the group algebra k[G] is a
semisimple ring. (Etingof Example 7.9.5)

This is Maschke's theorem, corresponding to Theorem 4.1.1(i). -/
theorem Etingof.maschke_semisimple
    (k : Type*) (G : Type*) [Field k] [Group G] [Fintype G]
    [DecidableEq G] (h : IsUnit (Fintype.card G : k)) :
    IsSemisimpleRing (MonoidAlgebra k G) := by
  haveI : NeZero (Nat.card G : k) := by
    rw [neZero_iff]
    rw [Fintype.card_eq_nat_card] at h
    exact h.ne_zero
  infer_instance
