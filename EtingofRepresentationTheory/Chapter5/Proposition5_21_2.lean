import Mathlib

/-!
# Proposition 5.21.2: Schur Polynomials at Geometric Progressions

S_λ(1, z, z², …, z^{N-1}) = ∏_{1 ≤ i < j ≤ n} (z^{λᵢ-i} - z^{λⱼ-j}) / (z^{-i} - z^{-j})

In the limit z → 1 (by L'Hôpital):
S_λ(1, …, 1) = ∏_{1 ≤ i < j ≤ n} (λᵢ - λⱼ + j - i) / (j - i)

## Mathlib correspondence

Uses Vandermonde determinant (`Matrix.det_vandermonde` exists in Mathlib).
Schur polynomials themselves are not yet in Mathlib.
-/

/-- Schur polynomial at a geometric progression:
S_λ(1, z, …, z^{N-1}) = ∏_{i<j} (z^{λᵢ-i} - z^{λⱼ-j})/(z^{-i} - z^{-j}).
(Etingof Proposition 5.21.2) -/
theorem Etingof.Proposition5_21_2_geometric
    (N : ℕ) (lam : Fin N → ℕ) :
    -- S_λ(1, z, z², …, z^{N-1}) = product formula
    (sorry : Prop) := by
  sorry

/-- Schur polynomial dimension formula:
S_λ(1, …, 1) = ∏_{i<j} (λᵢ - λⱼ + j - i)/(j - i).
(Etingof Proposition 5.21.2) -/
theorem Etingof.Proposition5_21_2_dimension
    (N : ℕ) (lam : Fin N → ℕ) :
    -- S_λ(1, …, 1) = ∏_{i<j} (λᵢ - λⱼ + j - i)/(j - i)
    (sorry : Prop) := by
  sorry
