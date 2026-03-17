import Mathlib

/-!
# Lemma 5.15.3: Cauchy Determinant Identity

The following identity holds for distinct variables z₁,...,zₙ and y₁,...,yₙ:

  det(1/(zᵢ - yⱼ)) = ∏_{i<j}(zⱼ - zᵢ) · ∏_{i<j}(yᵢ - yⱼ) / ∏_{i,j}(zᵢ - yⱼ)

This is the Cauchy determinant formula, used in the proof of the Frobenius
character formula.

## Mathlib correspondence

Mathlib has `Matrix.det` and `Matrix.vandermonde`. The Cauchy determinant
identity itself may need to be proved from scratch.
-/

open Matrix Finset

/-- Cauchy determinant identity (multiplicative form): clearing denominators, the identity becomes
  `∏_{i,j}(zᵢ - yⱼ) · det(1/(zᵢ - yⱼ)) = ∏_{i<j}(zⱼ - zᵢ) · ∏_{i<j}(yᵢ - yⱼ)`.
(Etingof Lemma 5.15.3) -/
theorem Etingof.Lemma5_15_3
    (N : ℕ) (z y : Fin N → ℂ)
    (hzy : ∀ i j, z i ≠ y j) :
    (∏ i : Fin N, ∏ j : Fin N, (z i - y j)) *
      (Matrix.of (fun i j : Fin N => (z i - y j)⁻¹)).det =
    (∏ i : Fin N, ∏ j ∈ Ioi i, (z j - z i)) *
    (∏ i : Fin N, ∏ j ∈ Ioi i, (y i - y j)) := by
  sorry
