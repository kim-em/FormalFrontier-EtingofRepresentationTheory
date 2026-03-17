import Mathlib
import EtingofRepresentationTheory.Chapter5.Proposition5_21_1

/-!
# Proposition 5.21.2: Schur Polynomials at Geometric Progressions

S_λ(1, z, z², …, z^{N-1}) = ∏_{1 ≤ i < j ≤ N} (z^{λᵢ-i} - z^{λⱼ-j}) / (z^{-i} - z^{-j})

In the limit z → 1 (by L'Hôpital):
S_λ(1, …, 1) = ∏_{1 ≤ i < j ≤ N} (λᵢ - λⱼ + j - i) / (j - i)

## Mathlib correspondence

Uses `MvPolynomial.eval` for evaluation and `Finset.prod` for the product formula.
Schur polynomials are defined in `Proposition5_21_1`.
-/

open Finset MvPolynomial

noncomputable section

namespace Etingof

/-- Evaluation of an `MvPolynomial` at a geometric progression (1, z, z², …, z^{N-1}). -/
def evalGeometric (N : ℕ) (z : ℚ) : MvPolynomial (Fin N) ℚ →+* ℚ :=
  MvPolynomial.eval (fun i => z ^ (i : ℕ))

/-- Schur polynomial at a geometric progression:
S_λ(1, z, …, z^{N-1}) = ∏_{i<j} (z^{λᵢ + N - 1 - i} - z^{λⱼ + N - 1 - j}) /
                          ∏_{i<j} (z^{N - 1 - i} - z^{N - 1 - j}).

Here we state this for `z` in `ℚ` (away from roots of unity where the denominator vanishes).
The product is over pairs `(i, j)` with `i < j` in `Fin N`.
(Etingof Proposition 5.21.2, first part) -/
theorem Proposition5_21_2_geometric
    (N : ℕ) (lam : Fin N → ℕ) (z : ℚ)
    (hN : 1 ≤ N)
    -- z is not a root of unity (ensures the Vandermonde denominator is nonzero)
    (hz : ∀ (i j : Fin N), i < j → z ^ (N - 1 - (i : ℕ)) - z ^ (N - 1 - (j : ℕ)) ≠ 0) :
    evalGeometric N z (schurPoly N lam) =
      (∏ p ∈ Finset.filter (fun p : Fin N × Fin N => p.1 < p.2) Finset.univ,
        (z ^ (lam p.1 + N - 1 - (p.1 : ℕ)) - z ^ (lam p.2 + N - 1 - (p.2 : ℕ)))) /
      (∏ p ∈ Finset.filter (fun p : Fin N × Fin N => p.1 < p.2) Finset.univ,
        (z ^ (N - 1 - (p.1 : ℕ)) - z ^ (N - 1 - (p.2 : ℕ)))) := by
  sorry

/-- Schur polynomial dimension formula (specialization at z = 1):
S_λ(1, …, 1) = ∏_{i<j} (λᵢ - λⱼ + j - i) / (j - i).

This follows from `Proposition5_21_2_geometric` by L'Hôpital's rule (or a
direct Vandermonde determinant argument). Here `lam` is a weakly decreasing
sequence (partition), so `λᵢ - λⱼ + j - i > 0` whenever `i < j`.

We state this as evaluation of the Schur polynomial at the all-ones vector.
(Etingof Proposition 5.21.2, second part) -/
theorem Proposition5_21_2_dimension
    (N : ℕ) (lam : Fin N → ℕ) (hlam : Antitone lam) :
    MvPolynomial.eval (fun _ : Fin N => (1 : ℚ)) (schurPoly N lam) =
      (∏ p ∈ Finset.filter (fun p : Fin N × Fin N => p.1 < p.2) Finset.univ,
        ((lam p.1 : ℚ) - (lam p.2 : ℚ) + ((p.2 : ℕ) : ℚ) - ((p.1 : ℕ) : ℚ))) /
      (∏ p ∈ Finset.filter (fun p : Fin N × Fin N => p.1 < p.2) Finset.univ,
        (((p.2 : ℕ) : ℚ) - ((p.1 : ℕ) : ℚ))) := by
  sorry

end Etingof
