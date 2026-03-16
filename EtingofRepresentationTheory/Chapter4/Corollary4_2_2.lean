import Mathlib

/-!
# Corollary 4.2.2: Number of Irreducible Representations

The number of isomorphism classes of irreducible representations of G equals
the number of conjugacy classes of G (assuming char(k) does not divide |G|).

This follows immediately from Theorem 4.2.1, since the characters of irreducible
representations form a basis of the space of class functions, whose dimension
equals the number of conjugacy classes.

## Mathlib correspondence

Mathlib has conjugacy classes via `ConjClasses G` and `Fintype (ConjClasses G)`.
-/

/-- The number of irreducible representations equals the number of conjugacy classes.
(Etingof Corollary 4.2.2) -/
theorem Etingof.Corollary4_2_2
    (G : Type*) [Group G] [Fintype G] [DecidableEq G]
    (k : Type*) [Field k] [IsAlgClosed k]
    (h : IsUnit ((Fintype.card G : k))) :
    -- number of irreducible k-reps = number of conjugacy classes
    True := by  -- TODO: needs enumeration of irreducible representations
  sorry
