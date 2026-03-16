import Mathlib.Algebra.Ring.Basic

/-!
# Proposition 2.2.3: Uniqueness of Unit

If a unit exists in an algebra, it is unique.

**Proof.** Let 1, 1' be two units. Then 1 = 1·1' = 1'. □

## Mathlib correspondence

Exact match. This is a consequence of the uniqueness of identity elements in monoids/rings,
which Mathlib handles via the `Unique` instance on `{1 : M}` for monoids.
-/

/-- If an algebra has a unit, it is unique. (Etingof Proposition 2.2.3)
In Mathlib, this follows from the fact that a monoid has a unique identity element. -/
theorem Etingof.Proposition_2_2_3 (M : Type*) [MulOneClass M] (e : M)
    (he_left : ∀ a, e * a = a) (he_right : ∀ a, a * e = a) : e = 1 := by
  have := he_left 1
  simp at this
  exact this
