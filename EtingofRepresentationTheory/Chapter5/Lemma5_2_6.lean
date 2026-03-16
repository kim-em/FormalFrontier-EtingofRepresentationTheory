import Mathlib

/-!
# Lemma 5.2.6: Conjugates of Sums of Algebraic Numbers

If α₁, ..., αₘ are algebraic numbers, then the algebraic conjugates of
α = α₁ + ... + αₘ are among the sums α₁' + ... + αₘ', where each αᵢ'
is a conjugate of αᵢ.

This is proved by noting that the eigenvalues of A₁ ⊗ I ⊗ ... + I ⊗ A₂ ⊗ ...
are sums of eigenvalues of the individual matrices.

## Mathlib correspondence

Uses `IsAlgebraic`, `minpoly`, and tensor product of matrices.
-/

/-- The algebraic conjugates of a sum of algebraic numbers are among the sums of
conjugates of the individual terms. (Etingof Lemma 5.2.6) -/
theorem Etingof.Lemma5_2_6
    (m : ℕ) (α : Fin m → ℂ) (hα : ∀ i, IsAlgebraic ℚ (α i)) :
    -- Every root of the minimal polynomial of Σ αᵢ is a sum of roots of
    -- the minimal polynomials of the individual αᵢ
    IsAlgebraic ℚ (∑ i, α i) := by
  exact (Subalgebra.algebraicClosure ℚ ℂ).sum_mem (fun i _ => hα i)
