import Mathlib

/-!
# Proposition 5.21.1: Character Expansion in Schur Polynomials

The product ∏_m (x₁ᵐ + ⋯ + xₙᵐ)^{i_m} equals Σ_{λ : p ≤ N} χ_λ(C_i) S_λ(x),
where S_λ are Schur polynomials and χ_λ(C_i) are character values on
conjugacy classes indexed by the partition i.

## Mathlib correspondence

Requires Schur polynomial infrastructure (`MvPolynomial.esymm`, `MvPolynomial.psum`
exist but Schur polynomials are not yet in Mathlib).
-/

/-- Character expansion: ∏_m (x₁ᵐ + ⋯ + xₙᵐ)^{i_m} = Σ_λ χ_λ(C_i) S_λ(x).
(Etingof Proposition 5.21.1) -/
theorem Etingof.Proposition5_21_1
    (N n : ℕ) :
    -- The power-sum product indexed by a partition equals a
    -- linear combination of Schur polynomials with character values as coefficients
    (sorry : Prop) := by
  sorry
