import Mathlib
import EtingofRepresentationTheory.Chapter5.Corollary5_15_4

/-!
# Power Sum Cauchy Identity and Coefficient Extraction

This file provides coefficient extraction results for the Cauchy determinant
`det(1/(1-xᵢyⱼ))`, which is the key ingredient in the proof of the
Frobenius character formula (Theorem 5.15.1).

## Main results

- `cauchyRHS_coeff_diag`: For `α` with distinct entries, the coefficient of
  `x^α y^α` in `cauchyRHS` (= `det(1/(1-xᵢyⱼ))`) equals 1.

## Proof strategy

The coefficient of `x^α y^β` in `∏_j 1/(1-x_j·y_{σ(j)})` equals 1 iff
`β = α ∘ σ⁻¹` (each geometric series factor `∑_k (x_j y_{σ(j)})^k` forces
the x_j-exponent to equal the y_{σ(j)}-exponent). When summing
`∑_σ sign(σ) (...)` and setting `β = α`, we need `α = α ∘ σ⁻¹`, i.e.,
`σ` fixes all entries. If `α` is injective, only `σ = id` works, giving 1.

## Connection to Theorem 5.15.1

The Frobenius formula proof uses this coefficient extraction together with
the power sum Cauchy identity:

  (1/n!) ∑_{σ ∈ S_n} P_σ(x) · P_σ(y) = [degree n part of ∏_{i,j} 1/(1-xᵢyⱼ)]

and the Cauchy determinant identity:

  det(1/(1-xᵢyⱼ)) = Δ(x) · Δ(y) · ∏_{i,j} 1/(1-xᵢyⱼ)

to establish `(1/n!) ∑_σ [x^{λ+ρ}](Δ·P_σ)² = 1`, which then gives
`∑_ν L²_{νλ} = 1` via Parseval.
-/

open Finset Equiv.Perm MvPowerSeries Etingof

noncomputable section

namespace Etingof

variable (N : ℕ) (k : Type*) [Field k]

/-! ### Diagonal exponent for coefficient extraction -/

/-- The diagonal exponent in `CauchyVars N`: given `α : Fin N → ℕ`, this is the
finsupp on `Fin N ⊕ Fin N` that assigns `α i` to `Sum.inl i` and `α j` to `Sum.inr j`. -/
def diagExponent (α : Fin N → ℕ) : CauchyVars N →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (Sum.elim α α)

@[simp]
theorem diagExponent_inl (α : Fin N → ℕ) (i : Fin N) :
    diagExponent N α (Sum.inl i) = α i := by
  simp [diagExponent, Finsupp.equivFunOnFinite]

@[simp]
theorem diagExponent_inr (α : Fin N → ℕ) (j : Fin N) :
    diagExponent N α (Sum.inr j) = α j := by
  simp [diagExponent, Finsupp.equivFunOnFinite]

/-! ### Coefficient of the Cauchy product at diagonal exponents -/

/-- The coefficient of `x^α y^β` in `∏_j 1/(1-x_j·y_{σ(j)})` is 1 when
`β_{σ(j)} = α_j` for all `j` (so `β = α ∘ σ⁻¹`), and 0 otherwise.

This is because each factor `1/(1-x_j y_{σ(j)}) = ∑_k x_j^k y_{σ(j)}^k`
contributes independently to the x_j and y_{σ(j)} exponents, forcing them
to be equal.

**Proof approach**: Each factor `invOfUnit (1 - x_j y_{σ(j)}) 1` is
determined by the equation `(1 - x_j y_{σ(j)}) * inv = 1`. Taking
coefficients: `coeff d inv = coeff (d - e_j - e_{σ(j)}) inv` when
`e_j + e_{σ(j)} ≤ d` and `d ≠ 0`, showing that nonzero coefficients
occur exactly at `d = n·(e_j + e_{σ(j)})`. For the product over
disjoint variable pairs, the coefficient factors. -/
theorem cauchyProd_coeff_perm (σ : Equiv.Perm (Fin N))
    (d : CauchyVars N →₀ ℕ) :
    MvPowerSeries.coeff (R := k) d
      (∏ j : Fin N,
        MvPowerSeries.invOfUnit
          (1 - MvPowerSeries.X (Sum.inl j) * MvPowerSeries.X (Sum.inr (σ j)))
          1) =
    if (∀ j : Fin N, d (Sum.inl j) = d (Sum.inr (σ j))) then 1 else 0 := by
  sorry

/-- **Coefficient extraction from cauchyRHS**: For `α : Fin N → ℕ` with
distinct entries (i.e., `Function.Injective α`), the coefficient of
`x^α · y^α` in `cauchyRHS N k` equals 1.

**Proof**: `cauchyRHS = ∑_σ sign(σ) ∏_j 1/(1-x_j·y_{σ(j)})`.
By `cauchyProd_coeff_perm`, each term's coefficient at `(α, α)` is
`sign(σ)` when `α_j = α_{σ(j)}` for all `j`, which (by injectivity of `α`)
forces `σ = id`. So the sum reduces to `sign(id) · 1 = 1`. -/
theorem cauchyRHS_coeff_diag [CharZero k]
    (α : Fin N → ℕ) (hα : Function.Injective α) :
    MvPowerSeries.coeff (R := k) (diagExponent N α) (cauchyRHS N k) = 1 := by
  simp only [cauchyRHS, map_sum]
  -- Rewrite each summand using cauchyProd_coeff_perm
  have key : ∀ σ : Equiv.Perm (Fin N),
      MvPowerSeries.coeff (R := k) (diagExponent N α)
        (MvPowerSeries.C (Int.cast (Equiv.Perm.sign σ : ℤ) : k) *
          ∏ j : Fin N,
            MvPowerSeries.invOfUnit
              (1 - MvPowerSeries.X (Sum.inl j) * MvPowerSeries.X (Sum.inr (σ j)))
              1) =
      (Int.cast (Equiv.Perm.sign σ : ℤ) : k) *
        (if ∀ j, α j = α (σ j) then 1 else 0) := by
    intro σ
    rw [MvPowerSeries.coeff_C_mul,
        cauchyProd_coeff_perm N k σ (diagExponent N α)]
    simp only [diagExponent_inl, diagExponent_inr]
  simp_rw [key]
  -- Only σ = id satisfies α j = α (σ j) for all j (by injectivity)
  have honly_id : ∀ σ : Equiv.Perm (Fin N),
      (if ∀ j, α j = α (σ j) then (1 : k) else 0) =
      if σ = 1 then 1 else 0 := by
    intro σ
    split_ifs with h1 h2 h2
    · rfl
    · exfalso; apply h2
      ext j
      simp only [Equiv.Perm.coe_one, id_eq]
      exact congrArg Fin.val ((hα (h1 j)).symm)
    · exfalso; apply h1
      intro j; simp [h2]
    · rfl
  simp_rw [honly_id]
  simp [Finset.sum_ite_eq', Finset.mem_univ]

end Etingof
