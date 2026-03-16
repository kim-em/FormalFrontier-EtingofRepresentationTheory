import Mathlib

/-!
# Theorem 4.2.1: Characters Form a Basis of Class Functions

If char(k) does not divide |G|, the characters of irreducible representations of G
form a basis of the space Fc(G, k) of class functions on G.

The proof uses Maschke's theorem and the isomorphism (A/[A,A])* ≅ Fc(G, k) where A = k[G],
combined with the Artin–Wedderburn decomposition.

## Mathlib correspondence

Mathlib has `classFunction` in `Mathlib.RepresentationTheory.Character` and character
orthogonality results. The basis property requires connecting these.
-/

/-- Characters of irreducible representations form a basis of the space of class functions.
(Etingof Theorem 4.2.1) -/
theorem Etingof.Theorem4_2_1
    (k : Type*) (G : Type*) [Field k] [Group G] [Fintype G] [DecidableEq G]
    (h : IsUnit ((Fintype.card G : k))) :
    -- The characters of irreducible representations form a basis of class functions
    -- Stated as: the number of irreducible representations equals the number of
    -- conjugacy classes (which is the dimension of the class function space)
    True := by  -- TODO: Precise statement requires class function space API
  sorry
