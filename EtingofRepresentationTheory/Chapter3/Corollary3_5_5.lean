import Mathlib.RingTheory.Jacobson.Ideal
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Corollary 3.5.5: Sum of Squares of Dimensions Bounded by dim A

∑ᵢ (dim Vᵢ)² ≤ dim A, where the Vᵢ are the irreducible representations of A.

This follows from Theorem 3.5.4: dim A - dim Rad(A) = ∑ᵢ dim End(Vᵢ) = ∑ᵢ (dim Vᵢ)²,
and dim Rad(A) ≥ 0.
-/

open Finset in
/-- The sum of squares of dimensions of irreducible representations is at most dim A.
Given a complete set of pairwise nonisomorphic irreducible representations Vᵢ of a
finite dimensional algebra A over an algebraically closed field,
∑ᵢ (dim Vᵢ)² ≤ dim A. Etingof Corollary 3.5.5. -/
theorem Etingof.sum_dim_sq_le_dim (k : Type*) (A : Type*)
    [Field k] [IsAlgClosed k] [Ring A] [Algebra k A] [FiniteDimensional k A]
    (ι : Type*) [Fintype ι]
    (V : ι → Type*) [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
    [∀ i, Module A (V i)] [∀ i, IsScalarTower k A (V i)]
    [∀ i, FiniteDimensional k (V i)] [∀ i, IsSimpleModule A (V i)]
    (h_noniso : ∀ i j, i ≠ j → IsEmpty (V i ≃ₗ[A] V j))
    (h_complete : ∀ (W : Type*) [AddCommGroup W] [Module k W] [Module A W]
      [IsScalarTower k A W] [FiniteDimensional k W] [IsSimpleModule A W],
      ∃ i, Nonempty (W ≃ₗ[A] V i)) :
    ∑ i : ι, (Module.finrank k (V i)) ^ 2 ≤ Module.finrank k A := by
  sorry
