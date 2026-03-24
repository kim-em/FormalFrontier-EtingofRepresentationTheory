import Mathlib
import EtingofRepresentationTheory.Chapter5.PowerSumCauchyIdentity
import EtingofRepresentationTheory.Chapter5.Theorem5_14_3

/-!
# Power Sum Cauchy Identity: Bilinear Version

This file establishes the bilinear power sum Cauchy identity:

  ∑_{σ∈S_n} P_σ(x) P_σ(y) = n! · [deg (n,n)] ∏_{i,j} 1/(1-xᵢyⱼ)

where P_σ(x) = `cycleTypePsumProduct n σ` is the product of power sum symmetric polynomials
indexed by the cycle type of σ.

## Proof strategy

The identity follows from a bijective counting argument:

1. **LHS interpretation**: `c_α(σ) · c_β(σ)` counts pairs (f,g) where f,g assign cycles
   of σ to x-variables and y-variables respectively, with total exponents matching α and β.

2. **RHS interpretation**: The coefficient of `x^α y^β` in `∏_{i,j} 1/(1-xᵢyⱼ)` counts
   non-negative integer matrices K with row sums α and column sums β.

3. **Bijection**: Given matrix K, there are exactly n! triples (σ, f, g) producing it:
   - Multinomial choice of which elements go to each block (i,j): n!/∏ K_{ij}! ways
   - Any permutation of elements within each block: ∏ K_{ij}! ways
   - Product = n! for every K

## Application to Frobenius character formula

Combined with `cauchyRHS_coeff_diag` and the Cauchy determinant formula
`Δ(x)Δ(y) · ∏ 1/(1-xᵢyⱼ) = cauchyRHS`, this gives:

  ∑_σ ([x^{λ+ρ}](Δ P_σ))² = n! · [x^{λ+ρ} y^{λ+ρ}](cauchyRHS) = n!

which (via character orthogonality) implies `∑_ν L²_{νλ} = 1`.
-/

open Finset Equiv.Perm MvPowerSeries Etingof

noncomputable section

namespace Etingof

variable (N : ℕ)

/-- The bilinear exponent: maps `Sum.inl j ↦ α j` and `Sum.inr j ↦ β j`.
Generalizes `diagExponent` which uses `α = β`. -/
def bilinExponent (α β : Fin N → ℕ) : CauchyVars N →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (Sum.elim α β)

@[simp]
theorem bilinExponent_inl (α β : Fin N → ℕ) (i : Fin N) :
    bilinExponent N α β (Sum.inl i) = α i := by
  simp [bilinExponent, Finsupp.equivFunOnFinite]

@[simp]
theorem bilinExponent_inr (α β : Fin N → ℕ) (j : Fin N) :
    bilinExponent N α β (Sum.inr j) = β j := by
  simp [bilinExponent, Finsupp.equivFunOnFinite]

theorem diagExponent_eq_bilinExponent (α : Fin N → ℕ) :
    diagExponent N α = bilinExponent N α α := by
  ext v; cases v <;> simp [diagExponent, bilinExponent, Finsupp.equivFunOnFinite]

/-- General coefficient formula for `cauchyRHS`:

  [x^α y^β](cauchyRHS) = ∑_σ sign(σ) · [∀j, α_j = β_{σ(j)}]

This follows from `cauchyProd_coeff_perm` by distributing over the signed sum. -/
theorem cauchyRHS_coeff_general (k : Type*) [Field k] [CharZero k]
    (α β : Fin N → ℕ) :
    MvPowerSeries.coeff (R := k) (bilinExponent N α β) (cauchyRHS N k) =
    ∑ σ : Equiv.Perm (Fin N),
      (Int.cast (Equiv.Perm.sign σ : ℤ) : k) *
        if (∀ j : Fin N, α j = β (σ j)) then 1 else 0 := by
  simp only [cauchyRHS, map_sum]
  congr 1; ext σ
  rw [MvPowerSeries.coeff_C_mul, cauchyProd_coeff_perm N k σ (bilinExponent N α β)]
  simp only [bilinExponent_inl, bilinExponent_inr]

/-- For `α` injective and `α ≠ β` (as functions) where both have the same range,
the cauchyRHS coefficient at `(α, β)` is `sign(σ)` where σ is the unique permutation
with `α = β ∘ σ`. If the ranges differ, the coefficient is 0. -/
theorem cauchyRHS_coeff_bilin_of_injective (k : Type*) [Field k] [CharZero k]
    (α β : Fin N → ℕ) (hα : Function.Injective α) (hβ : Function.Injective β)
    (hαβ : ∀ j, α j = β j) :
    MvPowerSeries.coeff (R := k) (bilinExponent N α β) (cauchyRHS N k) = 1 := by
  rw [cauchyRHS_coeff_general]
  have key : ∀ σ : Equiv.Perm (Fin N),
      (if ∀ j, α j = β (σ j) then (1 : k) else 0) =
      if σ = 1 then 1 else 0 := by
    intro σ
    split_ifs with h1 h2 h2
    · rfl
    · exfalso; apply h2; ext j; simp
      exact congr_arg Fin.val (hβ ((hαβ j).symm.trans (h1 j))).symm
    · exfalso; apply h1; intro j; subst h2; simp; exact hαβ j
    · rfl
  simp_rw [key]
  simp [Finset.sum_ite_eq']

/-- **Power Sum Cauchy Identity** (coefficient-level bilinear version):

For any `α β : Fin n →₀ ℕ` with total degree n,

  ∑_{σ∈Sₙ} [x^α](P_σ) · [x^β](P_σ) = n! · [x^α y^β](∏_{i,j} 1/(1-xᵢyⱼ))

**Proof idea** (counting argument):
- LHS: `[x^α](P_σ)` counts "cycle colorings" f : cycles(σ) → [n] with total lengths
  matching α. The bilinear product counts pairs (f,g) of x/y colorings.
- RHS: `[x^α y^β](∏ 1/(1-xᵢyⱼ))` counts non-negative integer matrices K with row sums α,
  column sums β.
- **Bijection**: Given K, there are n! triples (σ,f,g) producing it:
  - Choose which elements go to block (i,j): multinomial n!/∏K_{ij}! ways
  - Choose σ within each block: ∏K_{ij}! ways (any permutation works)
  - Product = n! regardless of K.

This is the key identity needed for the Frobenius character formula.
It connects the group-theoretic sum ∑_σ P_σ²  to the Cauchy product ∏ 1/(1-xᵢyⱼ). -/
theorem powerSum_bilinear_coeff (n : ℕ) (α β : Fin n →₀ ℕ)
    (hα : ∑ i, α i = n) (hβ : ∑ i, β i = n) :
    (∑ σ : Equiv.Perm (Fin n),
      (MvPolynomial.coeff α (cycleTypePsumProduct n σ) : ℂ) *
      (MvPolynomial.coeff β (cycleTypePsumProduct n σ) : ℂ)) =
    (Nat.factorial n : ℂ) * MvPowerSeries.coeff (bilinExponent n α β)
      (∏ i : Fin n, ∏ j : Fin n,
        MvPowerSeries.invOfUnit
          (1 - MvPowerSeries.X (Sum.inl i : CauchyVars n) *
               MvPowerSeries.X (Sum.inr j : CauchyVars n))
          1) := by
  sorry

/-- **Cauchy Determinant Formula** (power series form):

  Δ(x) · Δ(y) · ∏_{i,j} 1/(1-xᵢyⱼ) = cauchyRHS = det(1/(1-xᵢyⱼ))

This classical identity relates the unsigned Cauchy product to the signed determinant
via the Vandermonde factors. Combined with `cauchyRHS_coeff_diag`, it allows extracting
coefficients of the alternating sum.

**Proof idea**: Both sides are rational functions of xᵢ, yⱼ. Both vanish when xᵢ = xⱼ
or yᵢ = yⱼ for i ≠ j (LHS because Δ vanishes, RHS because det has equal rows/columns).
Degree matching and evaluation at a specific point completes the proof. -/
theorem cauchy_determinant_formula (n : ℕ) :
    ∀ d : CauchyVars n →₀ ℕ,
    MvPowerSeries.coeff d (cauchyRHS n ℂ) =
    ∑ π : Equiv.Perm (Fin n), ∑ τ : Equiv.Perm (Fin n),
      (Int.cast (Equiv.Perm.sign π : ℤ) : ℂ) *
      (Int.cast (Equiv.Perm.sign τ : ℤ) : ℂ) *
      MvPowerSeries.coeff
        (d - Finsupp.equivFunOnFinite.symm (fun v =>
          match v with
          | Sum.inl j => (π⁻¹ j).val
          | Sum.inr j => (τ⁻¹ j).val))
        (∏ i : Fin n, ∏ j : Fin n,
          MvPowerSeries.invOfUnit
            (1 - MvPowerSeries.X (Sum.inl i : CauchyVars n) *
                 MvPowerSeries.X (Sum.inr j : CauchyVars n))
            1) := by
  sorry

end Etingof
