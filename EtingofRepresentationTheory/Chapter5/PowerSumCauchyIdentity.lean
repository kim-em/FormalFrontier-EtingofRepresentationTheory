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
private lemma coeff_invOfUnit_single (j : Fin N) (σ : Equiv.Perm (Fin N))
    (e : CauchyVars N →₀ ℕ) :
    MvPowerSeries.coeff (R := k) e
      (MvPowerSeries.invOfUnit
        (1 - MvPowerSeries.X (Sum.inl j) * MvPowerSeries.X (Sum.inr (σ j)))
        1) =
    if e.support ⊆ {Sum.inl j, Sum.inr (σ j)} ∧ e (Sum.inl j) = e (Sum.inr (σ j))
    then 1 else 0 := by
  classical
  set g := MvPowerSeries.invOfUnit
    (1 - MvPowerSeries.X (Sum.inl j) * MvPowerSeries.X (Sum.inr (σ j)) :
      MvPowerSeries (CauchyVars N) k) 1
  set a : CauchyVars N := Sum.inl j
  set b : CauchyVars N := Sum.inr (σ j)
  have hab : a ≠ b := Sum.inl_ne_inr
  set eab : CauchyVars N →₀ ℕ := Finsupp.single a 1 + Finsupp.single b 1
  -- Key recurrence: g = 1 + Xa*Xb*g, from (1-Xa*Xb)*g = 1
  have hmul : (1 - MvPowerSeries.X a * MvPowerSeries.X b :
      MvPowerSeries (CauchyVars N) k) * g = 1 :=
    MvPowerSeries.mul_invOfUnit _ 1 (by simp [MvPowerSeries.constantCoeff_X])
  have hg_rec : g = 1 + MvPowerSeries.X a * MvPowerSeries.X b * g :=
    sub_eq_iff_eq_add.mp (by rwa [sub_mul, one_mul] at hmul)
  -- Xa*Xb = monomial eab 1
  have ht_mono : MvPowerSeries.X a * MvPowerSeries.X b =
      (MvPowerSeries.monomial eab (1 : k)) := by
    change MvPowerSeries.monomial (Finsupp.single a 1) (1 : k) *
         MvPowerSeries.monomial (Finsupp.single b 1) (1 : k) = _
    rw [MvPowerSeries.monomial_mul_monomial, one_mul]
  -- For e ≠ 0, coeff e g = if eab ≤ e then coeff (e - eab) g else 0
  have hcoeff_rec : ∀ e' : CauchyVars N →₀ ℕ, e' ≠ 0 →
      MvPowerSeries.coeff (R := k) e' g =
      if eab ≤ e' then MvPowerSeries.coeff (R := k) (e' - eab) g else 0 := by
    intro e' hne
    conv_lhs => rw [hg_rec]
    rw [map_add, MvPowerSeries.coeff_one, if_neg hne, zero_add, ht_mono,
        MvPowerSeries.coeff_monomial_mul, one_mul]
  -- eab value lemmas
  have eab_a : eab a = 1 := by simp [eab, hab]
  have eab_b : eab b = 1 := by simp [eab, hab.symm]
  have eab_other : ∀ v, v ≠ a → v ≠ b → eab v = 0 := by
    intro v hva hvb; simp [eab, hva, hvb]
  -- Helper: the "balanced on {a,b}" condition for e is equivalent for e and e - eab
  -- when eab ≤ e
  have hcond_iff : ∀ e' : CauchyVars N →₀ ℕ, eab ≤ e' →
      ((e'.support ⊆ {a, b} ∧ e' a = e' b) ↔
      ((e' - eab).support ⊆ {a, b} ∧ (e' - eab) a = (e' - eab) b)) := by
    intro e' hle
    have hsub_v : ∀ v, (e' - eab) v = e' v - eab v := by
      intro v; simp only [Finsupp.tsub_apply]
    constructor <;> intro ⟨hs, hv⟩
    · constructor
      · intro v hvm
        rw [Finsupp.mem_support_iff] at hvm
        rw [hsub_v] at hvm
        by_cases hva : v = a
        · exact Finset.mem_insert.mpr (Or.inl hva)
        · by_cases hvb : v = b
          · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr hvb))
          · exfalso
            have hns : v ∉ e'.support := fun h => by have := hs h; simp [hva, hvb] at this
            simp only [Finsupp.mem_support_iff, ne_eq, not_not] at hns
            rw [eab_other v hva hvb, Nat.sub_zero] at hvm
            exact hvm hns
      · rw [hsub_v, hsub_v, eab_a, eab_b]; omega
    · constructor
      · intro v hvm
        rw [Finsupp.mem_support_iff] at hvm
        by_cases hva : v = a
        · exact Finset.mem_insert.mpr (Or.inl hva)
        · by_cases hvb : v = b
          · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr hvb))
          · exfalso
            have hsub_eq : (e' - eab) v = e' v := by rw [hsub_v, eab_other v hva hvb, Nat.sub_zero]
            have : v ∈ (e' - eab).support := Finsupp.mem_support_iff.mpr (hsub_eq ▸ hvm)
            have := hs this; simp [hva, hvb] at this
      · have ha_le : 1 ≤ e' a := eab_a ▸ hle a
        have hb_le : 1 ≤ e' b := eab_b ▸ hle b
        rw [hsub_v, hsub_v, eab_a, eab_b] at hv; omega
  -- Main proof by induction on e a
  suffices key : ∀ (m : ℕ) (e' : CauchyVars N →₀ ℕ), e' a = m →
      MvPowerSeries.coeff (R := k) e' g =
      if e'.support ⊆ {a, b} ∧ e' a = e' b then 1 else 0 from key _ e rfl
  intro m
  induction m with
  | zero =>
    intro e' he'
    by_cases he0 : e' = 0
    · subst he0
      simp only [Finsupp.support_zero, Finset.empty_subset, true_and,
        Finsupp.coe_zero, Pi.zero_apply, ite_true]
      exact MvPowerSeries.constantCoeff_invOfUnit _ _
    · -- e' ≠ 0, e' a = 0: eab ≤/ e' (since eab a = 1 > 0 = e' a)
      rw [hcoeff_rec e' he0, if_neg (by intro h; have := h a; rw [eab_a] at this; omega)]
      -- RHS: condition fails since e' a = 0 and e' ≠ 0 means either e' b ≠ 0 or support ⊄ {a,b}
      symm; rw [if_neg]
      intro ⟨hsup, heq⟩
      have heb0 : e' b = 0 := by omega
      apply he0; ext v
      by_cases hva : v = a; · subst hva; exact he'
      by_cases hvb : v = b; · subst hvb; exact heb0
      have : v ∉ e'.support := fun h => by have := hsup h; simp [hva, hvb] at this
      simp only [Finsupp.mem_support_iff, ne_eq, not_not] at this
      exact this
  | succ n ih =>
    intro e' he'
    have hne0 : e' ≠ 0 := by intro h; simp [h] at he'
    rw [hcoeff_rec e' hne0]
    by_cases heb : e' b = 0
    · -- e' b = 0: eab ≤/ e' (since eab b = 1 > 0 = e' b)
      rw [if_neg (by intro h; have := h b; rw [eab_b] at this; omega)]
      symm; rw [if_neg]; intro ⟨_, h⟩; omega
    · -- e' b ≥ 1: eab ≤ e', apply IH
      have hle : eab ≤ e' := by
        intro v; by_cases hva : v = a
        · subst hva; rw [eab_a]; omega
        · by_cases hvb : v = b
          · subst hvb; rw [eab_b]; omega
          · rw [eab_other v hva hvb]; exact Nat.zero_le _
      rw [if_pos hle]
      have he_sub : (e' - eab) a = n := by
        rw [Finsupp.tsub_apply, eab_a]; omega
      rw [ih (e' - eab) he_sub]
      -- Conditions are equivalent by hcond_iff
      exact if_congr (hcond_iff e' hle).symm rfl rfl

theorem cauchyProd_coeff_perm (σ : Equiv.Perm (Fin N))
    (d : CauchyVars N →₀ ℕ) :
    MvPowerSeries.coeff (R := k) d
      (∏ j : Fin N,
        MvPowerSeries.invOfUnit
          (1 - MvPowerSeries.X (Sum.inl j) * MvPowerSeries.X (Sum.inr (σ j)))
          1) =
    if (∀ j : Fin N, d (Sum.inl j) = d (Sum.inr (σ j))) then 1 else 0 := by
  classical
  rw [MvPowerSeries.coeff_prod]
  simp_rw [coeff_invOfUnit_single]
  simp_rw [Finset.prod_boole]
  simp only [Finset.mem_univ, true_implies]
  -- Goal: ∑ l ∈ finsuppAntidiag univ d,
  --   if (∀ j, (l j).support ⊆ {inl j, inr (σ j)} ∧ (l j)(inl j) = (l j)(inr (σ j)))
  --   then 1 else 0
  -- = if ∀ j, d(inl j) = d(inr(σ j)) then 1 else 0
  -- Key: if all conditions hold, d(inl j) = d(inr(σ j)) and l is uniquely determined
  -- Forward: conditions on l imply condition on d
  have forward : ∀ l ∈ Finset.finsuppAntidiag Finset.univ d,
      (∀ j : Fin N, (l j).support ⊆ {Sum.inl j, Sum.inr (σ j)} ∧
        (l j) (Sum.inl j) = (l j) (Sum.inr (σ j))) →
      ∀ j : Fin N, d (Sum.inl j) = d (Sum.inr (σ j)) := by
    intro l hl hconds j
    rw [Finset.mem_finsuppAntidiag] at hl
    -- d = ∑ i, l i, so d(inl j) = ∑ i, (l i)(inl j)
    have hd_eq := hl.1
    have eval_inl : d (Sum.inl j) = ∑ i : Fin N, (l i) (Sum.inl j) := by
      have := congr_fun (congr_arg DFunLike.coe hd_eq) (Sum.inl j)
      simp only [Finsupp.finset_sum_apply] at this
      exact this.symm
    have eval_inr : d (Sum.inr (σ j)) = ∑ i : Fin N, (l i) (Sum.inr (σ j)) := by
      have := congr_fun (congr_arg DFunLike.coe hd_eq) (Sum.inr (σ j))
      simp only [Finsupp.finset_sum_apply] at this
      exact this.symm
    -- For i ≠ j: (l i)(inl j) = 0 (since inl j ∉ {inl i, inr(σ i)})
    have zero_inl : ∀ i, i ≠ j → (l i) (Sum.inl j) = 0 := by
      intro i hi
      have hsup := (hconds i).1
      by_contra h
      have hmem : Sum.inl j ∈ (l i).support := Finsupp.mem_support_iff.mpr h
      have := hsup hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with h1 | h2
      · exact hi (Sum.inl_injective h1).symm
      · exact Sum.inl_ne_inr h2
    -- For i ≠ j: (l i)(inr(σ j)) = 0 (since inr(σ j) ∉ {inl i, inr(σ i)} as σ injective)
    have zero_inr : ∀ i, i ≠ j → (l i) (Sum.inr (σ j)) = 0 := by
      intro i hi
      have hsup := (hconds i).1
      by_contra h
      have hmem : Sum.inr (σ j) ∈ (l i).support := Finsupp.mem_support_iff.mpr h
      have := hsup hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with h1 | h2
      · exact Sum.inr_ne_inl h1
      · exact hi (σ.injective (Sum.inr_injective h2)).symm
    -- So d(inl j) = (l j)(inl j) and d(inr(σ j)) = (l j)(inr(σ j))
    rw [eval_inl, eval_inr]
    rw [Finset.sum_eq_single j (fun i _ hi => zero_inl i hi) (by simp)]
    rw [Finset.sum_eq_single j (fun i _ hi => zero_inr i hi) (by simp)]
    exact (hconds j).2
  by_cases hcond : ∀ j : Fin N, d (Sum.inl j) = d (Sum.inr (σ j))
  · rw [if_pos hcond]
    -- Helper: extract value of (l i)(v) = 0 when v ∉ {inl i, inr(σ i)}
    -- from the support condition
    have support_zero (l : Fin N →₀ (CauchyVars N →₀ ℕ))
        (hcl : ∀ i : Fin N, (l i).support ⊆ {Sum.inl i, Sum.inr (σ i)} ∧
          (l i) (Sum.inl i) = (l i) (Sum.inr (σ i)))
        (i : Fin N) (v : CauchyVars N) (hv : v ≠ Sum.inl i) (hv' : v ≠ Sum.inr (σ i)) :
        (l i) v = 0 := by
      by_contra h
      have := (hcl i).1 (Finsupp.mem_support_iff.mpr h)
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      exact this.elim hv hv'
    -- Helper: if l satisfies conditions and ∑ l = d, then (l j)(inl j) = d(inl j)
    have diag_val (l : Fin N →₀ (CauchyVars N →₀ ℕ))
        (hsum : Finset.univ.sum l = d)
        (hcl : ∀ i : Fin N, (l i).support ⊆ {Sum.inl i, Sum.inr (σ i)} ∧
          (l i) (Sum.inl i) = (l i) (Sum.inr (σ i)))
        (j : Fin N) : (l j) (Sum.inl j) = d (Sum.inl j) := by
      have h := congr_fun (congr_arg DFunLike.coe hsum) (Sum.inl j)
      simp only [Finsupp.finset_sum_apply] at h
      rw [← h, Finset.sum_eq_single j _ (by simp)]
      intro i _ hi
      exact support_zero l hcl i (Sum.inl j)
        (fun h => hi (Sum.inl_injective h).symm) (fun h => Sum.inl_ne_inr h)
    -- Define l₀: the unique decomposition
    set l₀ : Fin N →₀ (CauchyVars N →₀ ℕ) := Finsupp.equivFunOnFinite.symm
      (fun j => Finsupp.single (Sum.inl j) (d (Sum.inl j)) +
                Finsupp.single (Sum.inr (σ j)) (d (Sum.inr (σ j))))
    have l₀_val : ∀ j, l₀ j = Finsupp.single (Sum.inl j) (d (Sum.inl j)) +
        Finsupp.single (Sum.inr (σ j)) (d (Sum.inr (σ j))) :=
      fun j => by simp [l₀, Finsupp.equivFunOnFinite]
    have l₀_apply : ∀ j v, (l₀ j) v =
        (if Sum.inl j = v then d (Sum.inl j) else 0) +
        (if Sum.inr (σ j) = v then d (Sum.inr (σ j)) else 0) := by
      intro j v; rw [l₀_val]; simp [Finsupp.single_apply]
    -- l₀ satisfies conditions
    have l₀_conds : ∀ j : Fin N,
        (l₀ j).support ⊆ {Sum.inl j, Sum.inr (σ j)} ∧
        (l₀ j) (Sum.inl j) = (l₀ j) (Sum.inr (σ j)) := by
      intro j; constructor
      · intro v hv
        rw [Finsupp.mem_support_iff] at hv
        rw [l₀_apply] at hv
        by_contra habs
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at habs
        simp only [show Sum.inl j ≠ v from Ne.symm habs.1,
                    show Sum.inr (σ j) ≠ v from Ne.symm habs.2, ite_false, add_zero] at hv
        exact hv rfl
      · simp [l₀_apply, Sum.inl_ne_inr, hcond j]
    -- l₀ is in the antidiagonal: ∑ j, l₀ j = d
    have l₀_mem : l₀ ∈ Finset.finsuppAntidiag Finset.univ d := by
      rw [Finset.mem_finsuppAntidiag]
      refine ⟨?_, fun _ _ => Finset.mem_univ _⟩
      ext v; simp only [Finsupp.finset_sum_apply, l₀_apply]
      cases v with
      | inl i =>
        rw [Finset.sum_eq_single i _ (by simp)]
        · simp
        · intro j _ hj; simp [show Sum.inl j ≠ Sum.inl i from
            fun h => hj (Sum.inl_injective h), Sum.inr_ne_inl]
      | inr i =>
        rw [Finset.sum_eq_single (σ.symm i) _ (by simp)]
        · simp [σ.apply_symm_apply]
        · intro j _ hj; simp [Sum.inl_ne_inr, show Sum.inr (σ j) ≠ Sum.inr i from
            fun h => hj (σ.apply_eq_iff_eq_symm_apply.mp (Sum.inr_injective h))]
    -- l₀ is unique
    have l₀_unique : ∀ l ∈ Finset.finsuppAntidiag Finset.univ d,
        (∀ j : Fin N, (l j).support ⊆ {Sum.inl j, Sum.inr (σ j)} ∧
          (l j) (Sum.inl j) = (l j) (Sum.inr (σ j))) → l = l₀ := by
      intro l hl hcl
      rw [Finset.mem_finsuppAntidiag] at hl
      ext j v; rw [l₀_apply]
      have hsup := (hcl j).1
      have hbal := (hcl j).2
      by_cases hv1 : Sum.inl j = v
      · subst hv1; simp [diag_val l hl.1 hcl j]
      · by_cases hv2 : Sum.inr (σ j) = v
        · subst hv2; simp [← hbal, diag_val l hl.1 hcl j, hcond j]
        · simp [hv1, hv2, support_zero l hcl j v (Ne.symm hv1) (Ne.symm hv2)]
    -- Collapse sum to single term
    rw [Finset.sum_eq_single l₀
      (fun l hl hne => if_neg (fun h => hne (l₀_unique l hl h)))
      (fun h => absurd l₀_mem h),
      if_pos l₀_conds]
  · rw [if_neg hcond]
    apply Finset.sum_eq_zero
    intro l hl
    rw [if_neg (fun h => hcond (forward l hl h))]

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
