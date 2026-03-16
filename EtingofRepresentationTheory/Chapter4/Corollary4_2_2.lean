import Mathlib

/-!
# Corollary 4.2.2: Number of Irreducible Representations

The number of isomorphism classes of irreducible representations of G equals
the number of conjugacy classes of G (assuming k is algebraically closed and
char(k) does not divide |G|).

This follows from Theorem 4.2.1: irreducible characters form a basis of class functions,
and the dimension of the class function space equals the number of conjugacy classes.

## Mathlib correspondence

Mathlib has conjugacy classes via `ConjClasses G` and `Fintype (ConjClasses G)`.
The counting result requires the basis theorem (4.2.1).

## Proof strategy

1. Apply Wedderburn-Artin (`IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed`)
   to `MonoidAlgebra k G` to get `k[G] ≃ₐ ∏ᵢ Mat(dᵢ, k)` with n blocks.
2. Each matrix block's column space gives a simple representation, yielding n
   pairwise non-isomorphic simple FDReps.
3. Every simple FDRep is isomorphic to one of these (via the equivalence
   `Rep.equivalenceModuleMonoidAlgebra` preserving simplicity).
4. n = dim(Z(k[G])) = dim(class functions) = |ConjClasses G|.

Steps 2-4 require infrastructure from issue #643 (connecting Wedderburn-Artin to FDRep).
-/

open FDRep CategoryTheory

universe u

/-- The number of isomorphism classes of irreducible representations equals the number
of conjugacy classes: there exist exactly `Fintype.card (ConjClasses G)` pairwise
non-isomorphic simple representations, and every simple representation is isomorphic
to one of them. (Etingof Corollary 4.2.2) -/
theorem Etingof.Corollary4_2_2
    {G : Type u} [Group G] [Fintype G] [DecidableEq G]
    {k : Type u} [Field k] [IsAlgClosed k]
    [Invertible (Fintype.card G : k)] :
    ∃ (n : ℕ) (V : Fin n → FDRep k G),
      (∀ i, Simple (V i)) ∧
      (∀ i j, Nonempty ((V i) ≅ (V j)) → i = j) ∧
      (∀ (W : FDRep k G), Simple W → ∃ i, Nonempty (W ≅ V i)) ∧
      n = Fintype.card (ConjClasses G) := by
  -- The proof requires the Wedderburn-Artin decomposition of k[G]:
  -- IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed gives
  --   k[G] ≃ₐ ∏ᵢ Mat(dᵢ, k) with n blocks
  -- Then:
  -- 1. Construct n simple FDReps from the matrix block column spaces
  -- 2. Show pairwise non-isomorphism (distinct blocks ↔ non-isomorphic simples)
  -- 3. Show completeness (every simple appears, via Rep ≃ Mod_{k[G]})
  -- 4. Show n = |ConjClasses G| via dim(Z(k[G])) = n = |ConjClasses G|
  --
  -- This infrastructure is tracked in issue #643.
  sorry
