import Mathlib.RingTheory.Jacobson.Ideal
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.Dimension.Constructions
import EtingofRepresentationTheory.Chapter3.Theorem3_2_2

/-!
# Corollary 3.5.5: Sum of Squares of Dimensions Bounded by dim A

∑ᵢ (dim Vᵢ)² ≤ dim A, where the Vᵢ are the irreducible representations of A.

This follows from the density theorem (Theorem 3.2.2): the map A → ∏ᵢ End(Vᵢ)
is surjective, so dim(∏ᵢ End(Vᵢ)) ≤ dim A. Since dim(End(Vᵢ)) = (dim Vᵢ)²,
the result follows.
-/

open Finset Module in
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
    ∑ i : ι, (finrank k (V i)) ^ 2 ≤ finrank k A := by
  -- The combined map A → ∏ᵢ End_k(Vᵢ) is surjective by the density theorem
  have hsurj := Etingof.density_theorem_part2 k A ι V h_noniso
  -- Package as a k-linear map
  let φ : A →ₗ[k] (∀ i, End k (V i)) :=
    LinearMap.pi (fun i => (Algebra.lsmul k k (V i)).toLinearMap)
  -- φ is surjective (same underlying function as in density theorem)
  have hφ_surj : Function.Surjective φ := by
    intro f
    obtain ⟨a, ha⟩ := hsurj f
    exact ⟨a, funext fun i => congr_fun ha i⟩
  -- finrank of codomain ≤ finrank of domain via surjectivity
  have h1 : finrank k (∀ i, End k (V i)) ≤ finrank k A := by
    calc finrank k (∀ i, End k (V i))
        = finrank k (LinearMap.range φ) := by
          rw [φ.range_eq_top.mpr hφ_surj, finrank_top]
      _ ≤ finrank k A := LinearMap.finrank_range_le φ
  -- Rewrite finrank of Pi type and endomorphism algebras
  calc ∑ i : ι, (finrank k (V i)) ^ 2
      = ∑ i : ι, finrank k (End k (V i)) := by
        congr 1; ext i
        rw [sq, ← finrank_linearMap (R := k) (S := k) (M := V i) (N := V i)]
    _ = finrank k (∀ i, End k (V i)) := (finrank_pi_fintype (R := k)).symm
    _ ≤ finrank k A := h1
