import Mathlib
import EtingofRepresentationTheory.Chapter5.Theorem5_14_3
import EtingofRepresentationTheory.Chapter5.Theorem5_12_2

/-!
# Theorem 5.15.1: Frobenius Character Formula for Specht Modules

The character of the Specht module V_λ evaluated at conjugacy class C_i is:

  χ_{V_λ}(C_i) = coefficient of x^{λ+ρ} in Δ(x) · ∏_{m≥1} p_m(x)^{i_m}

where ρ = (n-1, n-2, ..., 1, 0), Δ(x) = ∏_{i<j} (xⱼ - xᵢ) is the
Vandermonde determinant, and p_m are power sum symmetric polynomials.

## Formalization approach

The character of the Specht module V_λ is defined as the trace of left
multiplication by σ on V_λ ⊆ ℂ[S_n]. The Vandermonde polynomial and the
shift vector ρ are defined as multivariate polynomial / finsupp respectively.

The formula relates three objects:
1. The LHS: trace of the S_n-action on the Specht module (left ideal of ℂ[S_n])
2. The Vandermonde factor Δ(x), which accounts for the antisymmetrization in
   the Young symmetrizer
3. The power sum polynomial product from Theorem 5.14.3, shifted by ρ

## Mathlib correspondence

- `MvPolynomial.psum`: power sum symmetric polynomials p_m = Σᵢ xᵢᵐ
- `MvPolynomial.X`: polynomial variables
- `MvPolynomial.coeff`: coefficient extraction
- `LinearMap.trace`: trace of a linear endomorphism
-/

namespace Etingof

/-- The Vandermonde polynomial Δ(x) = ∏_{i<j} (xⱼ - xᵢ) in n variables.
This is the polynomial form of the Vandermonde determinant. -/
noncomputable def vandermondePoly (n : ℕ) : MvPolynomial (Fin n) ℂ :=
  ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (MvPolynomial.X j - MvPolynomial.X i)

/-- The shift vector ρ = (n-1, n-2, ..., 1, 0) used in the Frobenius character formula.
Component i equals n - 1 - i. -/
noncomputable def rhoShift (n : ℕ) : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => n - 1 - i.val)

/-- The left multiplication action of σ ∈ S_n on the Specht module V_λ.
Since V_λ is a left ideal of ℂ[S_n], left multiplication by `of σ` preserves it. -/
noncomputable def spechtModuleAction (n : ℕ) (la : Nat.Partition n)
    (σ : Equiv.Perm (Fin n)) : ↥(SpechtModule n la) →ₗ[ℂ] ↥(SpechtModule n la) where
  toFun := fun ⟨m, hm⟩ => ⟨MonoidAlgebra.of ℂ _ σ * m,
    (SpechtModule n la).smul_mem (MonoidAlgebra.of ℂ _ σ) hm⟩
  map_add' := fun ⟨a, _⟩ ⟨b, _⟩ => Subtype.ext (mul_add _ a b)
  map_smul' := fun _ ⟨_, _⟩ => Subtype.ext (Algebra.mul_smul_comm _ _ _)

/-- The character of the Specht module V_λ at a permutation σ ∈ S_n, defined as the
trace of left multiplication by σ restricted to V_λ ⊆ ℂ[S_n]. -/
noncomputable def spechtModuleCharacter (n : ℕ) (la : Nat.Partition n)
    (σ : Equiv.Perm (Fin n)) : ℂ :=
  LinearMap.trace ℂ _ (spechtModuleAction n la σ)

/-- **Theorem 5.15.1** (Frobenius character formula): The character of the Specht module
V_λ at a permutation σ with cycle type i = (i₁, i₂, ...) equals the coefficient
of x^{λ+ρ} in Δ(x) · ∏_{m≥1} p_m(x)^{i_m}, where Δ is the Vandermonde polynomial,
ρ = (n-1, ..., 1, 0), and p_m is the power sum symmetric polynomial.
(Etingof Theorem 5.15.1) -/
theorem Theorem5_15_1
    (n : ℕ) (la : Nat.Partition n) (σ : Equiv.Perm (Fin n)) :
    spechtModuleCharacter n la σ =
      MvPolynomial.coeff (Nat.Partition.toFinsupp la + rhoShift n)
        (vandermondePoly n * cycleTypePsumProduct n σ) := by
  sorry

end Etingof
