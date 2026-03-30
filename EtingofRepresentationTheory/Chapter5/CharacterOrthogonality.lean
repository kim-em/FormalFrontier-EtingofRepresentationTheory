import Mathlib
import EtingofRepresentationTheory.Chapter5.PowerSumCauchyBilinear
import EtingofRepresentationTheory.Chapter5.PowerSumCauchyBilinearGen
import EtingofRepresentationTheory.Chapter5.Proposition5_21_1
import EtingofRepresentationTheory.Chapter5.Theorem5_22_1

/-!
# Character Row Orthogonality for Symmetric Groups

This file proves the row orthogonality relation for irreducible characters of Sₙ:

  ∑_{σ∈Sₙ} χ_λ(σ) · χ_{λ'}(σ) = n! · δ_{λ,λ'}

where χ_λ is the character value defined via the Frobenius formula.

## Proof strategy

The proof proceeds by connecting charValue to the Cauchy identity:

1. **Expand charValue**: `charValue(N, λ, type(σ))` is the coefficient of
   `x^{λ+δ}` in `Δ(x) · P_σ(x)`. Expanding the alternant Δ via the
   Leibniz formula gives a signed sum over permutations:
   `charValue = ∑_π sign(π) · coeff_{λ+δ-π(δ)}(P_σ)`

2. **Bilinear identity**: Sum the product of two charValues over σ ∈ S_n.
   After exchanging summation order:
   `∑_σ charValue(λ) · charValue(λ') = ∑_π ∑_τ sign(π)sign(τ) · [∑_σ coeff·coeff]`
   The inner sum `∑_σ coeff_α(P_σ) · coeff_β(P_σ)` equals
   `n! · fullCauchyProd_coeff` by `powerSum_bilinear_coeff_gen`.

3. **Cauchy identity**: The resulting double alternating sum of fullCauchyProd
   coefficients equals `δ_{λ,λ'}` by `vandermonde_cauchy_general`.

## Main results

* `charValue_row_orthogonality`: the row orthogonality relation for character values
* `charValue_as_alternating_coeff`: expansion of charValue via the alternant
-/

open MvPolynomial Finset

noncomputable section

namespace Etingof

/-! ### Step 1: Expand charValue via the alternant determinant -/

/-- The exponent vector for permutation π applied to vandermondeExps:
the function `i ↦ vandermondeExps N (π⁻¹ i) = N - 1 - π⁻¹(i)`.

This corresponds to the monomial exponent of the π-th term in the
Leibniz expansion of the alternant determinant. -/
private def permVandermondeExp (N : ℕ) (π : Equiv.Perm (Fin N)) : Fin N → ℕ :=
  fun i => vandermondeExps N (π⁻¹ i)

/-- **Alternant determinant expansion**: the coefficient of `x^e` in the product
`det(alternantMatrix(δ)) · f` equals the alternating sum of coefficients of `f`
at shifted exponents.

This is the key step: it expands
  `[x^e](Δ · f) = ∑_π sign(π) · [x^{e - π(δ)}](f)`
where the sum is over permutations π such that `e - π(δ) ≥ 0` pointwise. -/
theorem coeff_alternant_mul_eq_alternating_sum (N : ℕ) (e : Fin N →₀ ℕ)
    (f : MvPolynomial (Fin N) ℚ) :
    MvPolynomial.coeff e ((alternantMatrix N (vandermondeExps N)).det * f) =
    ∑ π : Equiv.Perm (Fin N),
      (↑(Equiv.Perm.sign π : ℤ) : ℚ) *
      (if ∀ i, permVandermondeExp N π i ≤ e i
       then MvPolynomial.coeff (e - Finsupp.equivFunOnFinite.symm (permVandermondeExp N π)) f
       else 0) := by
  -- Expand the determinant via Leibniz formula and distribute over f
  rw [Matrix.det_apply, Finset.sum_mul]
  simp only [MvPolynomial.coeff_sum, smul_mul_assoc, MvPolynomial.coeff_smul]
  -- Each permutation term: ∏_j alternantMatrix(σ j, j) = monomial(vandermondeExps ∘ σ⁻¹) 1
  simp_rw [show ∀ σ : Equiv.Perm (Fin N), ∏ j, alternantMatrix N (vandermondeExps N) (σ j) j =
      monomial (Finsupp.equivFunOnFinite.symm (vandermondeExps N ∘ ⇑σ.symm)) 1 from fun σ => by
    rw [show ∏ j, alternantMatrix N (vandermondeExps N) (σ j) j =
        ∏ j, (X (σ j) : MvPolynomial (Fin N) ℚ) ^ vandermondeExps N j from rfl,
      show ∏ j, (X (σ j) : MvPolynomial (Fin N) ℚ) ^ vandermondeExps N j =
        ∏ i, X i ^ (vandermondeExps N (σ.symm i))
        from Fintype.prod_equiv σ _ _ (fun _ => by simp)]
    exact prod_X_pow_eq_monomial' _]
  -- Match term by term
  apply Finset.sum_congr rfl; intro π _
  -- Convert Units.smul to cast * ...
  rw [Units.smul_def, ← Int.cast_smul_eq_zsmul ℚ, smul_eq_mul]
  congr 1
  -- coeff_e(monomial(m) 1 * f) = if m ≤ e then 1 * coeff_{e-m}(f) else 0
  rw [MvPolynomial.coeff_monomial_mul', one_mul]
  -- The monomial exponent is vandermondeExps ∘ π⁻¹ = permVandermondeExp N π
  have heq : Finsupp.equivFunOnFinite.symm (vandermondeExps N ∘ ⇑π.symm) =
      Finsupp.equivFunOnFinite.symm (permVandermondeExp N π) := by
    ext i; simp [permVandermondeExp, Equiv.Perm.inv_def]
  rw [heq]; congr 1

/-- **charValue as alternating coefficient sum**: the character value
`χ_λ(μ)` equals the alternating sum of power sum partition coefficients
at shifted exponents `λ+δ - π(δ)`. -/
theorem charValue_as_alternating_coeff
    (N : ℕ) {n : ℕ} (lam : BoundedPartition N n) (μ : n.Partition) :
    charValue N lam μ =
    ∑ π : Equiv.Perm (Fin N),
      (↑(Equiv.Perm.sign π : ℤ) : ℚ) *
      (if ∀ i, permVandermondeExp N π i ≤ shiftedExps N lam.parts i
       then MvPolynomial.coeff
         (Finsupp.equivFunOnFinite.symm (shiftedExps N lam.parts) -
          Finsupp.equivFunOnFinite.symm (permVandermondeExp N π))
         (MvPolynomial.psumPart (Fin N) ℚ μ)
       else 0) := by
  unfold charValue
  exact coeff_alternant_mul_eq_alternating_sum N
    (Finsupp.equivFunOnFinite.symm (shiftedExps N lam.parts))
    (MvPolynomial.psumPart (Fin N) ℚ μ)

/-- Sum of shifted minus permuted vandermondeExps equals n. -/
private lemma sum_shiftedExps_sub_permVandermondeExp
    (N : ℕ) {n : ℕ} (lam : BoundedPartition N n)
    (π : Equiv.Perm (Fin N))
    (hle : ∀ i, permVandermondeExp N π i ≤ shiftedExps N lam.parts i) :
    ∑ i, (Finsupp.equivFunOnFinite.symm (shiftedExps N lam.parts) -
      Finsupp.equivFunOnFinite.symm (permVandermondeExp N π) : Fin N →₀ ℕ) i = n := by
  -- Simplify Finsupp evaluations
  have heval : ∀ (f : Fin N → ℕ) (i : Fin N),
      (Finsupp.equivFunOnFinite.symm f : Fin N →₀ ℕ) i = f i := by
    intros; simp [Finsupp.equivFunOnFinite]
  simp_rw [show ∀ i, (Finsupp.equivFunOnFinite.symm (shiftedExps N lam.parts) -
      Finsupp.equivFunOnFinite.symm (permVandermondeExp N π) : Fin N →₀ ℕ) i =
      shiftedExps N lam.parts i - permVandermondeExp N π i from by
    intro i; simp [Finsupp.equivFunOnFinite, Finsupp.coe_tsub]]
  -- ∑(a - b) + ∑ b = ∑ a when b ≤ a pointwise, so ∑(a - b) = ∑ a - ∑ b
  have key : ∑ i : Fin N, (shiftedExps N lam.parts i - permVandermondeExp N π i) +
      ∑ i : Fin N, permVandermondeExp N π i =
      ∑ i : Fin N, shiftedExps N lam.parts i := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => Nat.sub_add_cancel (hle i)
  -- ∑ shiftedExps = ∑ lam.parts + ∑ vandermondeExps = n + ∑ vandermondeExps
  have hsum_shifted : ∑ i : Fin N, shiftedExps N lam.parts i =
      n + ∑ i : Fin N, vandermondeExps N i := by
    unfold shiftedExps vandermondeExps
    rw [show ∑ i : Fin N, (lam.parts i + (N - 1 - ↑i)) =
        ∑ i : Fin N, lam.parts i + ∑ i : Fin N, (N - 1 - (↑i : ℕ)) from
      Finset.sum_add_distrib]
    rw [lam.sum_eq]
  -- ∑ permVandermondeExp = ∑ vandermondeExps (permutation invariance)
  have hsum_perm : ∑ i : Fin N, permVandermondeExp N π i =
      ∑ i : Fin N, vandermondeExps N i :=
    Fintype.sum_equiv π⁻¹ _ _ (fun _ => rfl)
  omega

/-! ### Step 2: Bilinear sum over permutations -/

/-- **Bilinear expansion**: the sum of products of character values over all
permutations σ ∈ Sₙ equals a double alternating sum of fullCauchyProd
coefficients (times n!).

This uses `powerSum_bilinear_coeff_gen` to convert
`∑_σ coeff_α(P_σ) · coeff_β(P_σ)` into `n! · fullCauchyProd` coefficients. -/
theorem charValue_product_sum_eq_alternating_cauchy
    (N : ℕ) {n : ℕ} (lam lam' : BoundedPartition N n) :
    (∑ σ : Equiv.Perm (Fin n),
      charValue N lam (fullCycleTypePartition σ) *
      charValue N lam' (fullCycleTypePartition σ) : ℚ) =
    (n.factorial : ℚ) *
    ∑ π : Equiv.Perm (Fin N), ∑ τ : Equiv.Perm (Fin N),
      (↑(Equiv.Perm.sign π : ℤ) : ℚ) * (↑(Equiv.Perm.sign τ : ℤ) : ℚ) *
      (if (∀ i, permVandermondeExp N π i ≤ shiftedExps N lam.parts i) ∧
          (∀ i, permVandermondeExp N τ i ≤ shiftedExps N lam'.parts i)
       then MvPowerSeries.coeff
              (bilinExponent N
                (fun i => shiftedExps N lam.parts i - permVandermondeExp N π i)
                (fun i => shiftedExps N lam'.parts i - permVandermondeExp N τ i))
              (fullCauchyProd N ℚ)
       else 0) := by
  -- Step 1: Expand charValue using the alternant expansion
  simp_rw [charValue_as_alternating_coeff]
  -- Step 2: Each summand is a product of two alternating sums
  -- ∑_σ (∑_π sign(π)*f_π(σ)) * (∑_τ sign(τ)*g_τ(σ))
  -- = ∑_σ ∑_π ∑_τ sign(π)*sign(τ)*f_π(σ)*g_τ(σ)
  simp_rw [Finset.sum_mul_sum]
  -- Step 3: Exchange sum order: ∑_σ ∑_π ∑_τ → ∑_π ∑_τ ∑_σ
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := Finset.univ (α := Equiv.Perm (Fin n)))]
  -- Now: ∑_π ∑_τ ∑_σ sign(π)*f_π(σ) * sign(τ)*g_τ(σ)
  -- Step 4: Factor n! out and match term by term
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro π _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro τ _
  -- Factor out signs and merge conditionals
  set hcondπ := ∀ i, permVandermondeExp N π i ≤ shiftedExps N lam.parts i
  set hcondτ := ∀ i, permVandermondeExp N τ i ≤ shiftedExps N lam'.parts i
  set sπ := (↑(Equiv.Perm.sign π : ℤ) : ℚ)
  set sτ := (↑(Equiv.Perm.sign τ : ℤ) : ℚ)
  set α' := Finsupp.equivFunOnFinite.symm (shiftedExps N lam.parts) -
      Finsupp.equivFunOnFinite.symm (permVandermondeExp N π)
  set β' := Finsupp.equivFunOnFinite.symm (shiftedExps N lam'.parts) -
      Finsupp.equivFunOnFinite.symm (permVandermondeExp N τ)
  -- Each summand: sπ * (if hcondπ then ... else 0) * (sτ * (if hcondτ then ... else 0))
  -- = sπ * sτ * (if hcondπ ∧ hcondτ then ... * ... else 0)
  have aux : ∀ (a b c d : ℚ) (P Q : Prop) [Decidable P] [Decidable Q],
      (a * if P then c else 0) * (b * if Q then d else 0) =
      a * b * if P ∧ Q then c * d else 0 := by
    intros; split_ifs <;> simp_all; ring
  simp_rw [aux]
  rw [← Finset.mul_sum]
  split_ifs with h
  · -- Both conditions hold: apply powerSum_bilinear_coeff_gen
    obtain ⟨hπ, hτ⟩ := h
    -- Replace psumPart with powerSumCycleProduct
    simp_rw [← powerSumCycleProduct_eq_psumPart]
    -- Need sum hypotheses for powerSum_bilinear_coeff_gen
    have hα_sum : ∑ i, α' i = n :=
      sum_shiftedExps_sub_permVandermondeExp N lam π hπ
    have hβ_sum : ∑ i, β' i = n :=
      sum_shiftedExps_sub_permVandermondeExp N lam' τ hτ
    rw [powerSum_bilinear_coeff_gen N α' β' hα_sum hβ_sum]
    -- Now: sπ * sτ * (n! * coeff) = n! * (sπ * sτ * coeff)
    -- with matching bilinExponent
    have hbilin : bilinExponent N (⇑α') (⇑β') =
        bilinExponent N (fun i => shiftedExps N lam.parts i - permVandermondeExp N π i)
          (fun i => shiftedExps N lam'.parts i - permVandermondeExp N τ i) := by
      ext v; cases v <;> simp [bilinExponent, α', β', Finsupp.equivFunOnFinite]
    rw [hbilin]; ring
  · -- At least one condition fails: both sides are zero
    simp

/-! ### Step 3: Connecting to vandermonde_cauchy_general -/

/-- **Row orthogonality of Sₙ characters**: For bounded partitions λ, λ' of n
with at most N parts,

  ∑_{σ∈Sₙ} χ_λ(type(σ)) · χ_{λ'}(type(σ)) = n! · δ_{λ,λ'}

where `χ_λ(type(σ)) = charValue N lam (fullCycleTypePartition σ)` is the
Frobenius character value.

The proof uses:
- `charValue_product_sum_eq_alternating_cauchy` to reduce the LHS to a
  double alternating sum of fullCauchyProd coefficients
- `vandermonde_cauchy_general` to evaluate the alternating sum as δ_{λ,λ'}

This no longer has sorrys from its dependency chain. -/
-- ((π * ρ)⁻¹ i).val = permVandermondeExp N π i where ρ = Fin.revPerm
private lemma inv_mul_revPerm_val (N : ℕ) (π : Equiv.Perm (Fin N)) (i : Fin N) :
    Fin.val ((π * @Fin.revPerm N)⁻¹ i) = permVandermondeExp N π i := by
  change ((π * @Fin.revPerm N).symm i).val = permVandermondeExp N π i
  -- (π * ρ).symm i = ρ.symm (π.symm i) = ρ(π⁻¹ i) since ρ.symm = ρ
  unfold permVandermondeExp vandermondeExps
  -- Goal: ↑((Equiv.symm (π * Fin.revPerm)) i) = N - 1 - ↑(π⁻¹ i)
  -- (π * ρ).symm = ρ.symm.trans π.symm, (ρ.symm.trans π.symm) i = π.symm (ρ.symm i) = π⁻¹ (ρ i)
  -- Wait: for Perm, (f * g).symm x = g.symm (f.symm x)
  -- So (π * ρ).symm x = ρ.symm (π.symm x) = ρ(π⁻¹ x) = Fin.rev(π⁻¹ x)
  -- Fin.rev(j).val = N - 1 - j.val
  have : ((π * @Fin.revPerm N).symm i) = Fin.rev (π.symm i) := by
    change (@Fin.revPerm N).symm (π.symm i) = Fin.rev (π.symm i)
    rw [Fin.revPerm_symm, Fin.revPerm_apply]
  rw [this]; simp [Fin.rev, Equiv.Perm.inv_def]; omega

/-- `shiftedExps` is injective on partitions. -/
private lemma shiftedExps_injective (N : ℕ) {n : ℕ} (lam lam' : BoundedPartition N n) :
    shiftedExps N lam.parts = shiftedExps N lam'.parts ↔ lam = lam' := by
  constructor
  · intro h
    have hparts : lam.parts = lam'.parts := by
      funext i; have := congr_fun h i; simp [shiftedExps] at this; omega
    cases lam; cases lam'; simp only [BoundedPartition.mk.injEq] at hparts ⊢; exact hparts
  · rintro rfl; rfl

/-- The alternating sum with `permVandermondeExp` conditions equals `δ_{α,β}` over ℂ.
Proved by reindexing `vandermonde_cauchy_general` via `Fin.revPerm`. -/
private lemma vandermonde_cauchy_permVandermondeExp (N : ℕ) (α β : Fin N → ℕ)
    (hα : StrictAnti α) (hβ : StrictAnti β) :
    (∑ π : Equiv.Perm (Fin N), ∑ τ : Equiv.Perm (Fin N),
      ((Equiv.Perm.sign π : ℤ) : ℂ) * ((Equiv.Perm.sign τ : ℤ) : ℂ) *
      (if (∀ i, permVandermondeExp N π i ≤ α i) ∧
          (∀ i, permVandermondeExp N τ i ≤ β i)
       then MvPowerSeries.coeff
              (bilinExponent N (fun i => α i - permVandermondeExp N π i)
                               (fun i => β i - permVandermondeExp N τ i))
              (fullCauchyProd N ℂ)
       else 0)) =
    if α = β then 1 else 0 := by
  set ρ := @Fin.revPerm N
  -- sign(ρ)² = 1
  have hsρ : ((Equiv.Perm.sign ρ : ℤ) : ℂ) * ((Equiv.Perm.sign ρ : ℤ) : ℂ) = 1 := by
    have h := Int.units_sq (Equiv.Perm.sign ρ)
    have : ((Equiv.Perm.sign ρ : ℤ) : ℂ) * ((Equiv.Perm.sign ρ : ℤ) : ℂ) =
        (↑(↑(Equiv.Perm.sign ρ ^ 2) : ℤ) : ℂ) := by push_cast; ring
    rw [this, h]; simp
  -- Step 1: Match each summand with VCG form at (π*ρ, τ*ρ)
  -- ((π*ρ)⁻¹ i).val = permVandermondeExp N π i, and sign(π*ρ) = sign(π)*sign(ρ)
  -- so our summand = VCG(π*ρ, τ*ρ) (signs cancel since sign(ρ)²=1)
  have h_eq : ∀ (π τ : Equiv.Perm (Fin N)),
      ((Equiv.Perm.sign π : ℤ) : ℂ) * ((Equiv.Perm.sign τ : ℤ) : ℂ) *
      (if (∀ i, permVandermondeExp N π i ≤ α i) ∧
          (∀ i, permVandermondeExp N τ i ≤ β i)
       then MvPowerSeries.coeff
              (bilinExponent N (fun i => α i - permVandermondeExp N π i)
                               (fun i => β i - permVandermondeExp N τ i))
              (fullCauchyProd N ℂ)
       else 0) =
      ((Equiv.Perm.sign (π * ρ) : ℤ) : ℂ) * ((Equiv.Perm.sign (τ * ρ) : ℤ) : ℂ) *
      (if (∀ i, ((π * ρ)⁻¹ i : Fin N).val ≤ α i) ∧
          (∀ i, ((τ * ρ)⁻¹ i : Fin N).val ≤ β i)
       then MvPowerSeries.coeff
              (bilinExponent N (fun i => α i - ((π * ρ)⁻¹ i : Fin N).val)
                               (fun i => β i - ((τ * ρ)⁻¹ i : Fin N).val))
              (fullCauchyProd N ℂ)
       else 0) := by
    intro π τ
    simp only [ρ]
    simp_rw [inv_mul_revPerm_val, Equiv.Perm.sign_mul]
    push_cast
    -- Goal: sπ * sτ * X = (sπ * sρ) * (sτ * sρ) * X where sρ² = 1
    split_ifs
    · congr 1
      have : (↑↑(Equiv.Perm.sign π) * ↑↑(Equiv.Perm.sign (@Fin.revPerm N))) *
          (↑↑(Equiv.Perm.sign τ) * ↑↑(Equiv.Perm.sign (@Fin.revPerm N))) =
          ↑↑(Equiv.Perm.sign π) * ↑↑(Equiv.Perm.sign τ) *
          ((↑↑(Equiv.Perm.sign (@Fin.revPerm N)) : ℂ) *
           ↑↑(Equiv.Perm.sign (@Fin.revPerm N))) := by ring
      rw [this, hsρ, mul_one]
    · simp
  -- Step 2: Combine reindexing + summand match into a single Fintype.sum_equiv
  -- ∑_π ∑_τ our(π,τ) = ∑_σ ∑_τ VCG(σ,τ) by σ=π*ρ, τ'=τ*ρ, using h_eq
  exact (Fintype.sum_equiv (Equiv.mulRight ρ) _ _
    (fun π => Fintype.sum_equiv (Equiv.mulRight ρ) _ _ (fun τ => h_eq π τ))).trans
    (vandermonde_cauchy_general N α β hα hβ)


theorem charValue_row_orthogonality
    (N : ℕ) {n : ℕ} (lam lam' : BoundedPartition N n) :
    ∑ σ : Equiv.Perm (Fin n),
      charValue N lam (fullCycleTypePartition σ) *
      charValue N lam' (fullCycleTypePartition σ) =
    if lam = lam' then (n.factorial : ℚ) else 0 := by
  rw [charValue_product_sum_eq_alternating_cauchy]
  set α := shiftedExps N lam.parts
  set β := shiftedExps N lam'.parts
  have hα_strict : StrictAnti α := by
    intro i j hij; simp only [α, shiftedExps]; have := lam.decreasing hij.le; omega
  have hβ_strict : StrictAnti β := by
    intro i j hij; simp only [β, shiftedExps]; have := lam'.decreasing hij.le; omega
  -- Suffices: the double alternating sum = δ_{lam,lam'}
  suffices hsum : ∑ π : Equiv.Perm (Fin N), ∑ τ : Equiv.Perm (Fin N),
      (↑(Equiv.Perm.sign π : ℤ) : ℚ) * (↑(Equiv.Perm.sign τ : ℤ) : ℚ) *
      (if (∀ i, permVandermondeExp N π i ≤ α i) ∧
          (∀ i, permVandermondeExp N τ i ≤ β i)
       then MvPowerSeries.coeff
              (bilinExponent N (fun i => α i - permVandermondeExp N π i)
                               (fun i => β i - permVandermondeExp N τ i))
              (fullCauchyProd N ℚ)
       else 0) = if lam = lam' then 1 else 0 by
    rw [hsum]; split_ifs <;> ring
  -- Transfer to ℂ via injectivity of algebraMap ℚ ℂ
  have h_inj : Function.Injective (algebraMap ℚ ℂ) := Rat.cast_injective
  apply h_inj
  -- LHS: push algebraMap through the sum
  rw [map_sum]
  simp_rw [map_sum, map_mul, map_intCast]
  -- Handle the if-then-else inside each summand
  have hcoeff_cast : ∀ (P : Prop) [Decidable P] (e : CauchyVars N →₀ ℕ),
      (algebraMap ℚ ℂ) (if P then MvPowerSeries.coeff e (fullCauchyProd N ℚ) else 0) =
      (if P then MvPowerSeries.coeff e (fullCauchyProd N ℂ) else 0) := by
    intro P _ e; split_ifs
    · rw [← MvPowerSeries.coeff_map, map_fullCauchyProd]
    · exact map_zero _
  simp_rw [hcoeff_cast]
  -- RHS: convert if-condition on lam = lam' to α = β
  have hrhs : (algebraMap ℚ ℂ) (if lam = lam' then 1 else 0) =
      if α = β then (1 : ℂ) else 0 := by
    simp only [apply_ite (algebraMap ℚ ℂ), map_one, map_zero]
    exact if_congr (shiftedExps_injective N lam lam').symm rfl rfl
  rw [hrhs]
  exact vandermonde_cauchy_permVandermondeExp N α β hα_strict hβ_strict

end Etingof
