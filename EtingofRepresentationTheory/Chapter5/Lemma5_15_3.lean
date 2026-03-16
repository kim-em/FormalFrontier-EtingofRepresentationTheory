import Mathlib

/-!
# Lemma 5.15.3: Cauchy Determinant Identity

The following identity holds for distinct variables z₁,...,zₙ and y₁,...,yₙ:

  ∏_{i<j}(zⱼ - zᵢ) · ∏_{i<j}(yᵢ - yⱼ) / ∏_{i,j}(zᵢ - yⱼ) = det(1/(zᵢ - yⱼ))

This is the Cauchy determinant formula, used in the proof of the Frobenius
character formula.

## Mathlib correspondence

Mathlib has `Matrix.det` and `Matrix.vandermonde`. The Cauchy determinant
identity itself may need to be proved from scratch.
-/

/-- Cauchy determinant identity: the ratio of Vandermonde-like products equals
det(1/(zᵢ - yⱼ)). (Etingof Lemma 5.15.3) -/
theorem Etingof.Lemma5_15_3
    (N : ℕ) (z y : Fin N → ℂ) :
    -- ∏_{i<j}(z_j - z_i)(y_i - y_j) / ∏_{i,j}(z_i - y_j) = det(1/(z_i - y_j))
    (sorry : Prop) := by
  sorry
