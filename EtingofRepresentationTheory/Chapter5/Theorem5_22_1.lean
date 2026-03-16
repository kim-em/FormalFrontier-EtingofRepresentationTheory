import Mathlib

/-!
# Theorem 5.22.1: Weyl Character Formula

The Weyl character formula: The representation Lλ of GL(V) is zero iff N < p
(where p = number of parts of λ). If N ≥ p, the character of Lλ is the
Schur polynomial Sλ(x), and:

  dim Lλ = ∏_{1 ≤ i < j ≤ n} (λᵢ - λⱼ + j - i)/(j - i)

## Mathlib correspondence

Vandermonde determinant is in Mathlib (`Matrix.det_vandermonde`).
Schur-Weyl duality and Schur polynomials are not.
-/

/-- Weyl character formula: the character of Lλ is the Schur polynomial Sλ(x),
and dim Lλ = ∏_{i<j} (λᵢ - λⱼ + j - i)/(j - i).
(Etingof Theorem 5.22.1) -/
theorem Etingof.Theorem5_22_1
    {k : Type*} [Field k] [IsAlgClosed k]
    {V : Type*} [AddCommGroup V] [Module k V] [Module.Finite k V]
    (N : ℕ) (lam : Fin N → ℕ) :
    -- char(Lλ) = Sλ(x) and dim Lλ = ∏_{i<j} (λᵢ - λⱼ + j - i)/(j - i)
    (sorry : Prop) := by
  sorry
