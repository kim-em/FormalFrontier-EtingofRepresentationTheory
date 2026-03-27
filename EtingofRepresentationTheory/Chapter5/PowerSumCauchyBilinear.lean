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

The identity follows from a double-counting argument. Both sides count the same set
`ElementBicoloring n α β` (element-level bicolorings compatible with some permutation):

- **LHS grouping**: Group by permutation σ, count compatible bicolorings for each σ.
  This gives ∑_σ #{cycle colorings for α} × #{cycle colorings for β}.
- **RHS grouping**: Group by the induced matrix K (with row sums α, col sums β).
  For each K, there are n!/∏K_{ij}! multinomial partitions × ∏K_{ij}! block permutations = n!.
  Total: n! × #{matrices with given margins}.

## Application to Frobenius character formula

Combined with `cauchyRHS_coeff_diag` and the Cauchy determinant formula, this gives:

  ∑_σ ([x^{λ+ρ}](Δ P_σ))² = n! · [x^{λ+ρ} y^{λ+ρ}](cauchyRHS) = n!

which (via character orthogonality) implies `∑_ν L²_{νλ} = 1`.
-/

open Finset Equiv.Perm MvPowerSeries Etingof

noncomputable section

namespace Etingof

variable (N : ℕ)

/-! ### Bilinear exponent infrastructure -/

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

/-! ### cauchyRHS coefficient formulas -/

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

/-- For `α = β` both injective, the cauchyRHS coefficient at `(α, β)` is 1. -/
theorem cauchyRHS_coeff_bilin_of_injective (k : Type*) [Field k] [CharZero k]
    (α β : Fin N → ℕ) (_hα : Function.Injective α) (hβ : Function.Injective β)
    (hαβ : ∀ j, α j = β j) :
    MvPowerSeries.coeff (R := k) (bilinExponent N α β) (cauchyRHS N k) = 1 := by
  rw [cauchyRHS_coeff_general]
  have key : ∀ σ : Equiv.Perm (Fin N),
      (if ∀ j, α j = β (σ j) then (1 : k) else 0) =
      if σ = 1 then 1 else 0 := by
    intro σ
    split_ifs with h1 h2 h2
    · rfl
    · exfalso; apply h2; ext j
      simp only [Equiv.Perm.coe_one, id_eq]
      exact congr_arg Fin.val (hβ ((hαβ j).symm.trans (h1 j))).symm
    · exfalso; apply h1; intro j; subst h2
      simp only [Equiv.Perm.coe_one, id_eq]; exact hαβ j
    · rfl
  simp_rw [key]
  simp [Finset.sum_ite_eq']

/-! ### Full Cauchy product -/

/-- The full Cauchy product ∏_{i,j} 1/(1-xᵢyⱼ) as an MvPowerSeries. -/
def fullCauchyProd (n : ℕ) (k : Type*) [CommRing k] : MvPowerSeries (CauchyVars n) k :=
  ∏ i : Fin n, ∏ j : Fin n,
    MvPowerSeries.invOfUnit
      (1 - MvPowerSeries.X (Sum.inl i : CauchyVars n) *
           MvPowerSeries.X (Sum.inr j : CauchyVars n))
      1

/-! ### Single geometric factor coefficient characterization -/

/-- Monomial exponent for the product xᵢ · yⱼ. -/
private abbrev xyPairMon (n : ℕ) (i j : Fin n) : CauchyVars n →₀ ℕ :=
  Finsupp.single (Sum.inl i) 1 + Finsupp.single (Sum.inr j) 1

@[simp]
private theorem xyPairMon_inl (n : ℕ) (i j : Fin n) (i' : Fin n) :
    xyPairMon n i j (Sum.inl i') = if i = i' then 1 else 0 := by
  simp [xyPairMon, Finsupp.single_apply]

@[simp]
private theorem xyPairMon_inr (n : ℕ) (i j : Fin n) (j' : Fin n) :
    xyPairMon n i j (Sum.inr j') = if j = j' then 1 else 0 := by
  simp [xyPairMon, Finsupp.single_apply]

/-- Target series for 1/(1 - xᵢyⱼ): coefficient = 1 at multiples of eᵢ + eⱼ, else 0. -/
private def geomTarget (n : ℕ) (i j : Fin n) : MvPowerSeries (CauchyVars n) ℂ :=
  fun e => if e = e (Sum.inl i) • xyPairMon n i j then 1 else 0

@[simp]
private theorem coeff_geomTarget (n : ℕ) (i j : Fin n) (e : CauchyVars n →₀ ℕ) :
    MvPowerSeries.coeff e (geomTarget n i j) =
    if e = e (Sum.inl i) • xyPairMon n i j then 1 else 0 := rfl

private theorem xyPairMon_ne_zero (n : ℕ) (i j : Fin n) : xyPairMon n i j ≠ 0 := by
  intro h
  have := DFunLike.congr_fun h (Sum.inl i)
  simp at this

private theorem nsmul_xyPairMon_apply (n : ℕ) (i j : Fin n) (k : ℕ) (v : CauchyVars n) :
    (k • xyPairMon n i j) v = k * (xyPairMon n i j v) :=
  Finsupp.smul_apply k _ v

/-- The key multiplication identity: (1 - xᵢyⱼ) · geomTarget = 1. -/
private theorem one_sub_xy_mul_geomTarget (n : ℕ) (i j : Fin n) :
    (1 - MvPowerSeries.X (Sum.inl i : CauchyVars n) *
         MvPowerSeries.X (Sum.inr j : CauchyVars n) :
      MvPowerSeries (CauchyVars n) ℂ) * geomTarget n i j = 1 := by
  have hXX : (MvPowerSeries.X (Sum.inl i : CauchyVars n) *
    MvPowerSeries.X (Sum.inr j : CauchyVars n) :
      MvPowerSeries (CauchyVars n) ℂ) =
    MvPowerSeries.monomial (xyPairMon n i j) 1 := by
    simp [xyPairMon, MvPowerSeries.X, MvPowerSeries.monomial_mul_monomial]
  ext e
  rw [sub_mul, one_mul, map_sub, hXX, MvPowerSeries.coeff_monomial_mul, one_mul]
  simp only [coeff_geomTarget, MvPowerSeries.coeff_one]
  set m := xyPairMon n i j with hm_def
  have hm_inl : m (Sum.inl i) = 1 := by simp [m]
  have hm_ne_zero : m ≠ 0 := hm_def ▸ xyPairMon_ne_zero n i j
  -- Case 1: e = 0
  by_cases h0 : e = 0
  · subst h0
    have hle : ¬(m ≤ 0) := fun h => hm_ne_zero (le_antisymm h (zero_le m))
    simp only [Finsupp.coe_zero, Pi.zero_apply, zero_smul, ite_true, if_neg hle, sub_zero]
  -- Cases 2 and 3: e ≠ 0
  · rw [if_neg h0]
    by_cases hm : e = e (Sum.inl i) • m
    · -- Case 2: e = k • m with k > 0
      have hk : 0 < e (Sum.inl i) := by
        by_contra hle; push_neg at hle
        rw [Nat.le_zero.mp hle, zero_smul] at hm; exact h0 hm
      rw [if_pos hm]
      have hle : m ≤ e := by
        rw [hm]; intro v
        simp only [Finsupp.smul_apply, smul_eq_mul]
        exact le_mul_of_one_le_left (Nat.zero_le _) hk
      rw [if_pos hle]
      have hsub : e - m = (e (Sum.inl i) - 1) • m := by
        rw [hm]; ext v
        simp only [Finsupp.smul_apply, smul_eq_mul, Finsupp.tsub_apply, hm_inl,
          mul_one, Nat.sub_mul, one_mul]
      have hsub_val : (e - m) (Sum.inl i) = e (Sum.inl i) - 1 := by
        rw [hsub, Finsupp.smul_apply, smul_eq_mul, hm_inl, mul_one]
      rw [hsub_val, if_pos hsub]; ring
    · -- Case 3: e ≠ k • m
      rw [if_neg hm]
      by_cases hle : m ≤ e
      · rw [if_pos hle]
        have hsub_ne : ¬(e - m = (e - m) (Sum.inl i) • m) := by
          intro hsub; apply hm
          -- Reconstruct e = (e - m) + m, then factor
          have h1 : e = (e - m) + m := (tsub_add_cancel_of_le hle).symm
          rw [hsub, show (e - m) (Sum.inl i) • m + m =
            ((e - m) (Sum.inl i) + 1) • m from by rw [add_smul, one_smul]] at h1
          have h3 : e (Sum.inl i) = (e - m) (Sum.inl i) + 1 := by
            have := DFunLike.congr_fun h1 (Sum.inl i)
            simp only [Finsupp.smul_apply, smul_eq_mul, hm_inl, mul_one] at this
            exact this
          exact h3.symm ▸ h1
        rw [if_neg hsub_ne]; ring
      · rw [if_neg hle]; ring

/-- Uniqueness: invOfUnit(1 - xᵢyⱼ, 1) = geomTarget. -/
private theorem invOfUnit_eq_geomTarget (n : ℕ) (i j : Fin n) :
    MvPowerSeries.invOfUnit
      (1 - MvPowerSeries.X (Sum.inl i : CauchyVars n) *
           MvPowerSeries.X (Sum.inr j : CauchyVars n))
      (1 : ℂˣ) =
    geomTarget n i j := by
  have h1 := one_sub_xy_mul_geomTarget n i j
  have hconst : (MvPowerSeries.constantCoeff :
      MvPowerSeries (CauchyVars n) ℂ →+* ℂ)
      (1 - MvPowerSeries.X (Sum.inl i) * MvPowerSeries.X (Sum.inr j)) = ↑(1 : ℂˣ) := by
    simp [map_sub, map_one, map_mul, MvPowerSeries.constantCoeff_X, Units.val_one]
  have h2 := MvPowerSeries.mul_invOfUnit
    (1 - MvPowerSeries.X (Sum.inl i : CauchyVars n) *
         MvPowerSeries.X (Sum.inr j : CauchyVars n)) 1 hconst
  have hU : IsUnit (1 - MvPowerSeries.X (Sum.inl i : CauchyVars n) *
      MvPowerSeries.X (Sum.inr j : CauchyVars n) :
        MvPowerSeries (CauchyVars n) ℂ) :=
    ⟨⟨_, _, h1, by rw [mul_comm]; exact h1⟩, rfl⟩
  exact hU.mul_left_cancel (h2.trans h1.symm)

/-- Coefficient formula for a single geometric factor: coeff at e is 1 if
e is a multiple of eᵢ + eⱼ, else 0. -/
theorem coeff_invOfUnit_one_sub_xy (n : ℕ) (i j : Fin n) (e : CauchyVars n →₀ ℕ) :
    MvPowerSeries.coeff e
      (MvPowerSeries.invOfUnit
        (1 - MvPowerSeries.X (Sum.inl i : CauchyVars n) *
             MvPowerSeries.X (Sum.inr j : CauchyVars n))
        (1 : ℂˣ)) =
    if e = e (Sum.inl i) • xyPairMon n i j then 1 else 0 := by
  rw [invOfUnit_eq_geomTarget]; rfl

/-! ### Coefficient formula for the full Cauchy product

The coefficient of x^α y^β in ∏_{i,j} 1/(1-xᵢyⱼ) counts the number of
non-negative integer matrices with row sums α and column sums β.
-/

/-- A non-negative integer matrix with prescribed row and column sums.
Entries are bounded by `n + 1` (since row sums equal α_i ≤ n) to ensure finiteness. -/
def NNMatrixWithMargins (n : ℕ) (α β : Fin n → ℕ) : Type :=
  { K : Fin n → Fin n → Fin (n + 1) //
    (∀ i, ∑ j, (K i j : ℕ) = α i) ∧ (∀ j, ∑ i, (K i j : ℕ) = β j) }

instance (n : ℕ) (α β : Fin n → ℕ) : Fintype (NNMatrixWithMargins n α β) :=
  Subtype.fintype _

/-- The full Cauchy product as a product over pairs, for use with coeff_prod. -/
private theorem fullCauchyProd_eq_prod_pairs (n : ℕ) :
    fullCauchyProd n ℂ = ∏ p : Fin n × Fin n,
      MvPowerSeries.invOfUnit
        (1 - MvPowerSeries.X (Sum.inl p.1 : CauchyVars n) *
             MvPowerSeries.X (Sum.inr p.2 : CauchyVars n))
        (1 : ℂˣ) := by
  change (∏ i : Fin n, ∏ j : Fin n, _) = _
  rw [← Fintype.prod_prod_type']

/-- Map from NNMatrixWithMargins to the finsuppAntidiag: each matrix K gives
a decomposition where entry (i,j) contributes K_{ij} copies of the (i,j) monomial. -/
private def matrixToAntidiag (n : ℕ) (α β : Fin n → ℕ)
    (K : NNMatrixWithMargins n α β) :
    (Fin n × Fin n) →₀ (CauchyVars n →₀ ℕ) :=
  Finsupp.equivFunOnFinite.symm (fun p => (K.1 p.1 p.2 : ℕ) • xyPairMon n p.1 p.2)

/-- matrixToAntidiag lies in the finsuppAntidiag. -/
private lemma matrixToAntidiag_mem (n : ℕ) (α β : Fin n → ℕ)
    (K : NNMatrixWithMargins n α β) :
    matrixToAntidiag n α β K ∈
      Finset.univ.finsuppAntidiag (bilinExponent n α β) := by
  rw [Finset.mem_finsuppAntidiag]
  refine ⟨?_, Finset.subset_univ _⟩
  have key : ∀ p, (matrixToAntidiag n α β K) p =
      (K.1 p.1 p.2 : ℕ) • xyPairMon n p.1 p.2 := fun p => by
    simp [matrixToAntidiag]
  ext v; cases v with
  | inl i =>
    simp only [Finsupp.coe_finset_sum, Finset.sum_apply, key,
      Finsupp.smul_apply, smul_eq_mul, xyPairMon_inl, mul_ite, mul_one, mul_zero,
      bilinExponent_inl]
    rw [Fintype.sum_prod_type, Finset.sum_eq_single i
      (fun i' _ hi' => by simp [hi']) (fun h => absurd (Finset.mem_univ i) h)]
    simp [K.2.1 i]
  | inr j =>
    simp only [Finsupp.coe_finset_sum, Finset.sum_apply, key,
      Finsupp.smul_apply, smul_eq_mul, xyPairMon_inr, mul_ite, mul_one, mul_zero,
      bilinExponent_inr]
    rw [Fintype.sum_prod_type, Finset.sum_comm, Finset.sum_eq_single j
      (fun j' _ hj' => by simp [hj']) (fun h => absurd (Finset.mem_univ j) h)]
    simp [K.2.2 j]

/-- matrixToAntidiag satisfies the validity condition. -/
private lemma matrixToAntidiag_valid (n : ℕ) (α β : Fin n → ℕ)
    (K : NNMatrixWithMargins n α β) (p : Fin n × Fin n) :
    (matrixToAntidiag n α β K) p =
    ((matrixToAntidiag n α β K) p) (Sum.inl p.1) •
      xyPairMon n p.1 p.2 := by
  simp only [matrixToAntidiag, Finsupp.coe_equivFunOnFinite_symm,
    Finsupp.smul_apply, smul_eq_mul, xyPairMon_inl, ite_true, mul_one]

/-- For valid antidiag elements, row sums of entries equal α. -/
private lemma extract_row_sum (n : ℕ) (α β : Fin n → ℕ)
    (x : (Fin n × Fin n) →₀ (CauchyVars n →₀ ℕ))
    (hx_mem : x ∈ Finset.univ.finsuppAntidiag (bilinExponent n α β))
    (hx_valid : ∀ p : Fin n × Fin n, x p = (x p) (Sum.inl p.1) • xyPairMon n p.1 p.2)
    (i : Fin n) : ∑ j : Fin n, (x (i, j)) (Sum.inl i) = α i := by
  have h := DFunLike.congr_fun (Finset.mem_finsuppAntidiag.mp hx_mem).1 (Sum.inl i)
  simp only [Finsupp.coe_finset_sum, Finset.sum_apply, bilinExponent_inl] at h
  rw [Fintype.sum_prod_type, Finset.sum_eq_single i _ _] at h
  · exact h
  · intro i' _ hi'
    exact Finset.sum_eq_zero fun j _ => by
      have := DFunLike.congr_fun (hx_valid (i', j)) (Sum.inl i)
      simp [hi'] at this; exact this
  · exact fun h' => absurd (Finset.mem_univ i) h'

/-- For valid antidiag elements, column sums of entries equal β. -/
private lemma extract_col_sum (n : ℕ) (α β : Fin n → ℕ)
    (x : (Fin n × Fin n) →₀ (CauchyVars n →₀ ℕ))
    (hx_mem : x ∈ Finset.univ.finsuppAntidiag (bilinExponent n α β))
    (hx_valid : ∀ p : Fin n × Fin n, x p = (x p) (Sum.inl p.1) • xyPairMon n p.1 p.2)
    (j : Fin n) : ∑ i : Fin n, (x (i, j)) (Sum.inl i) = β j := by
  have h := DFunLike.congr_fun (Finset.mem_finsuppAntidiag.mp hx_mem).1 (Sum.inr j)
  simp only [Finsupp.coe_finset_sum, Finset.sum_apply, bilinExponent_inr] at h
  rw [Fintype.sum_prod_type, Finset.sum_comm, Finset.sum_eq_single j _ _] at h
  · rwa [show (∑ i : Fin n, (x (i, j)) (Sum.inr j)) =
        ∑ i : Fin n, (x (i, j)) (Sum.inl i) from
      Finset.sum_congr rfl fun i _ => by
        have := DFunLike.congr_fun (hx_valid (i, j)) (Sum.inr j)
        simp at this; exact this] at h
  · intro j' _ hj'
    exact Finset.sum_eq_zero fun i _ => by
      have := DFunLike.congr_fun (hx_valid (i, j')) (Sum.inr j)
      simp [hj'] at this; exact this
  · exact fun h' => absurd (Finset.mem_univ j) h'

/-- Forward map: valid antidiag element → NNMatrixWithMargins. -/
private def antidiagToMatrix (n : ℕ) (α β : Fin n → ℕ) (hα : ∀ i, α i ≤ n)
    (x : (Fin n × Fin n) →₀ (CauchyVars n →₀ ℕ))
    (hrow : ∀ i, ∑ j : Fin n, (x (i, j)) (Sum.inl i) = α i)
    (hcol : ∀ j, ∑ i : Fin n, (x (i, j)) (Sum.inl i) = β j) :
    NNMatrixWithMargins n α β :=
  ⟨fun i j => ⟨(x (i, j)) (Sum.inl i),
    Nat.lt_succ_of_le ((hrow i ▸ Finset.single_le_sum (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ j)).trans (hα i))⟩,
   hrow, hcol⟩

/-- The coefficient of x^α y^β in the full Cauchy product equals the number of
non-negative integer matrices with row sums α and column sums β.
Requires α_i ≤ n for entries to fit in Fin(n+1). -/
theorem fullCauchyProd_coeff_eq_card (n : ℕ) (α β : Fin n → ℕ)
    (hα : ∀ i, α i ≤ n) :
    MvPowerSeries.coeff (bilinExponent n α β) (fullCauchyProd n ℂ) =
    ↑(Fintype.card (NNMatrixWithMargins n α β)) := by
  rw [fullCauchyProd_eq_prod_pairs]
  simp_rw [invOfUnit_eq_geomTarget]
  rw [MvPowerSeries.coeff_prod]
  simp_rw [coeff_geomTarget, Finset.prod_boole, Finset.mem_univ, forall_true_left,
    Finset.sum_boole]
  norm_cast
  -- Bijection: valid antidiag elements ↔ NNMatrixWithMargins
  change #_ = #(Finset.univ : Finset (NNMatrixWithMargins n α β))
  apply Finset.card_bij'
    (fun x hx =>
      antidiagToMatrix n α β hα x
        (extract_row_sum n α β x (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hx).2)
        (extract_col_sum n α β x (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hx).2))
    (fun K _ => matrixToAntidiag n α β K)
    (fun _ _ => Finset.mem_univ _)
    (fun K _ => Finset.mem_filter.mpr
      ⟨matrixToAntidiag_mem n α β K, matrixToAntidiag_valid n α β K⟩)
    (fun x hx => by
      apply DFunLike.ext; intro ⟨i, j⟩
      simp only [matrixToAntidiag, antidiagToMatrix, Finsupp.coe_equivFunOnFinite_symm]
      exact ((Finset.mem_filter.mp hx).2 (i, j)).symm)
    (fun K _ => by
      refine Subtype.ext (funext fun i => funext fun j => Fin.ext ?_)
      simp [antidiagToMatrix, matrixToAntidiag])

/-! ### Counting argument: the core of the proof

The key identity is proved by double counting. Define:
- An "element bicoloring" is a function h : Fin n → Fin n × Fin n
  together with a permutation σ that is compatible (monochromatic) with h.
- Grouping by σ gives ∑_σ #{cycle colorings α} × #{cycle colorings β}
- Grouping by the induced matrix K gives n! × #{matrices}
-/

/-- A cycle coloring for a composition α assigns each cycle of σ a "color" (variable index)
such that the total cycle lengths for each color match α.
This generalizes `MonochromaticColoring` from partitions to compositions. -/
def CycleColoring (n : ℕ) (α : Fin n →₀ ℕ) (σ : Equiv.Perm (Fin n)) : Type :=
  { f : Fin (fullCycleType n σ).toList.length → Fin n //
    ∀ j : Fin n, (Finset.univ.filter (fun i => f i = j)).sum
      (fun i => ((fullCycleType n σ).toList[↑i])) = α j }

instance (n : ℕ) (α : Fin n →₀ ℕ) (σ : Equiv.Perm (Fin n)) :
    Fintype (CycleColoring n α σ) := by
  unfold CycleColoring
  exact Subtype.fintype _

/-- The MvPolynomial coefficient of P_σ at a composition α equals the number of
cycle colorings. This generalizes `coeff_psum_prod_eq_card_colorings` from
partitions to compositions. -/
private lemma finsupp_sum_single_iff' (n : ℕ) (α : Fin n →₀ ℕ) (σ : Equiv.Perm (Fin n))
    (f : Fin (fullCycleType n σ).toList.length → Fin n) :
    (∑ i, Finsupp.single (f i) ((fullCycleType n σ).toList[(↑i : ℕ)]) = α) ↔
    (∀ j : Fin n, (Finset.univ.filter (fun i => f i = j)).sum
      (fun i => (fullCycleType n σ).toList[(↑i : ℕ)]) = α j) := by
  constructor
  · intro heq j
    have hj := DFunLike.congr_fun heq j
    simp only [Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.single_apply] at hj
    rw [← hj, Finset.sum_filter]
  · intro hall
    ext j
    simp only [Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.single_apply]
    rw [← Finset.sum_filter]
    exact hall j

theorem coeff_cycleTypePsumProduct_eq_card (n : ℕ) (α : Fin n →₀ ℕ)
    (σ : Equiv.Perm (Fin n)) :
    MvPolynomial.coeff α (cycleTypePsumProduct n σ) =
    ↑(Fintype.card (CycleColoring n α σ)) := by
  rw [cycleTypePsumProduct_eq_fullCycleType]
  rw [← Multiset.prod_map_toList, ← List.ofFn_getElem_eq_map, List.prod_ofFn]
  simp_rw [psum_eq_sum_monomial]
  rw [Finset.prod_univ_sum]
  simp_rw [← MvPolynomial.monomial_sum_one]
  rw [MvPolynomial.coeff_sum]
  simp_rw [MvPolynomial.coeff_monomial, Finset.sum_boole, Fintype.piFinset_univ]
  norm_cast
  -- Goal: card of filter {f | ∑ single (f i) ... = α} = card CycleColoring
  -- Both count functions f with the marginal condition; they differ in how
  -- the condition is stated (finsupp sum vs pointwise).
  have equiv : CycleColoring n α σ ≃
      { f : Fin (fullCycleType n σ).toList.length → Fin n //
        (∑ i, Finsupp.single (f i) ((fullCycleType n σ).toList[(↑i : ℕ)])) = α } := by
    unfold CycleColoring
    exact Equiv.subtypeEquiv (Equiv.refl _) (fun f => (finsupp_sum_single_iff' n α σ f).symm)
  rw [show Fintype.card (CycleColoring n α σ) = Fintype.card
      { f : Fin (fullCycleType n σ).toList.length → Fin n //
        (∑ i, Finsupp.single (f i) ((fullCycleType n σ).toList[(↑i : ℕ)])) = α }
    from Fintype.card_congr equiv]
  simp only [Fintype.card_subtype, Finset.card_filter]

/-! ### Double counting infrastructure

The key identity `∑_σ |CycleCol(α,σ)| × |CycleCol(β,σ)| = n! × |NNMat|`
is proved by going through an intermediate type of "compatible pairs" (h, σ):
- h : Fin n → Fin n × Fin n has marginals (α, β)
- σ ∈ Perm(Fin n) preserves h-fibers

Grouping by σ gives the LHS (via orbit index). Grouping by h and using
orbit-stabilizer gives the RHS.
-/

/-- Element bicoloring with prescribed row/column sums. -/
private def ElemBicol (n : ℕ) (α β : Fin n →₀ ℕ) : Type :=
  { h : Fin n → Fin n × Fin n //
    (∀ i : Fin n, (Finset.univ.filter fun x => (h x).1 = i).card = α i) ∧
    (∀ j : Fin n, (Finset.univ.filter fun x => (h x).2 = j).card = β j) }

private instance (n : ℕ) (α β : Fin n →₀ ℕ) : Fintype (ElemBicol n α β) :=
  Subtype.fintype _

/-- Permutation preserving fibers of h. -/
private def FiberPerm {n : ℕ} (h : Fin n → Fin n × Fin n) : Type :=
  { σ : Equiv.Perm (Fin n) // ∀ x, h (σ x) = h x }

private instance {n : ℕ} (h : Fin n → Fin n × Fin n) : Fintype (FiberPerm h) :=
  Subtype.fintype _

/-- Construct an element bicoloring from cycle colorings using orbit index. -/
private def cycleColToBicol (n : ℕ) (α β : Fin n →₀ ℕ)
    (σ : Equiv.Perm (Fin n)) (fg : CycleColoring n α σ × CycleColoring n β σ) :
    ElemBicol n α β :=
  let π := (exists_orbIdx σ).choose
  have hπ := (exists_orbIdx σ).choose_spec
  ⟨fun x => (fg.1.val (π x), fg.2.val (π x)),
   ⟨fun i => by
      rw [show (Finset.univ.filter fun x : Fin n => fg.1.val (π x) = i) =
          (Finset.univ.filter fun j => fg.1.val j = i).biUnion
            (fun j => Finset.univ.filter fun x => π x = j) from by
        ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
        exact ⟨fun h => ⟨π x, h, rfl⟩, fun ⟨j, hj, hjx⟩ => hjx ▸ hj⟩]
      rw [Finset.card_biUnion (fun i₁ hi₁ i₂ hi₂ hij =>
        Finset.disjoint_filter.mpr (fun x _ h₁ h₂ => hij (h₁ ▸ h₂)))]
      conv_lhs => arg 2; ext j; rw [hπ.2 j]
      exact fg.1.prop i,
    fun j => by
      rw [show (Finset.univ.filter fun x : Fin n => fg.2.val (π x) = j) =
          (Finset.univ.filter fun k => fg.2.val k = j).biUnion
            (fun k => Finset.univ.filter fun x => π x = k) from by
        ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
        exact ⟨fun h => ⟨π x, h, rfl⟩, fun ⟨k, hk, hkx⟩ => hkx ▸ hk⟩]
      rw [Finset.card_biUnion (fun i₁ hi₁ i₂ hi₂ hij =>
        Finset.disjoint_filter.mpr (fun x _ h₁ h₂ => hij (h₁ ▸ h₂)))]
      conv_lhs => arg 2; ext k; rw [hπ.2 k]
      exact fg.2.prop j⟩⟩

/-- The permutation σ preserves the bicoloring constructed from its cycle colorings. -/
private lemma cycleColToBicol_compat (n : ℕ) (α β : Fin n →₀ ℕ)
    (σ : Equiv.Perm (Fin n)) (fg : CycleColoring n α σ × CycleColoring n β σ) :
    ∀ x, (cycleColToBicol n α β σ fg).val (σ x) = (cycleColToBicol n α β σ fg).val x := by
  intro x
  simp only [cycleColToBicol]
  let π := (exists_orbIdx σ).choose
  have hπ := (exists_orbIdx σ).choose_spec
  show (fg.1.val (π (σ x)), fg.2.val (π (σ x))) = (fg.1.val (π x), fg.2.val (π x))
  have hkey : π (σ x) = π x := (hπ.1 (σ x) x).mpr ⟨-1, by simp⟩
  rw [hkey]

/-- **Part A**: The sigma type over CycleCol pairs has the same cardinality as
the sigma type over compatible (h, σ) pairs. -/
private lemma card_sigma_CycleCol_eq_card_sigma_fiberPerm (n : ℕ) (α β : Fin n →₀ ℕ)
    (hα : ∑ i, α i = n) (hβ : ∑ i, β i = n) :
    Fintype.card (Σ σ : Equiv.Perm (Fin n), CycleColoring n α σ × CycleColoring n β σ) =
    Fintype.card (Σ hb : ElemBicol n α β, FiberPerm hb.val) := by
  classical
  -- Forward map: (σ, f, g) → (h, σ) where h(x) = (f(π(x)), g(π(x)))
  -- Backward map: (h, σ) → (σ, f, g) where f(i) = (h(rep(i))).1
  -- Both use the orbit index from exists_orbIdx.
  apply Fintype.card_congr
  exact {
    toFun := fun ⟨σ, fg⟩ =>
      ⟨cycleColToBicol n α β σ fg,
       ⟨σ, cycleColToBicol_compat n α β σ fg⟩⟩
    invFun := fun p =>
      -- Use projections instead of pattern matching to avoid iota-reduction issues in left_inv
      let h := p.1.val
      let hrow := p.1.property.1
      let hcol := p.1.property.2
      let σ := p.2.val
      let hcompat : ∀ x, h (σ x) = h x := p.2.property
      let π := (exists_orbIdx σ).choose
      have hπ := (exists_orbIdx σ).choose_spec
      have hne : ∀ i : Fin (fullCycleType n σ).toList.length,
          (Finset.univ.filter (fun k : Fin n => π k = i)).Nonempty := by
        intro i; by_contra hemp
        rw [Finset.not_nonempty_iff_eq_empty] at hemp
        have h1 := hπ.2 i; rw [hemp, Finset.card_empty] at h1
        have h2 := fullCycleType_pos σ _ (Multiset.mem_toList.mp (List.getElem_mem i.isLt))
        omega
      let rep := fun i => (Finset.univ.filter (fun k : Fin n => π k = i)).min' (hne i)
      have hrep : ∀ i, π (rep i) = i := fun i =>
        (Finset.mem_filter.mp (Finset.min'_mem _ (hne i))).2
      have hc : ∀ x, h (σ x) = h x := hcompat
      have hiter : ∀ (m : ℕ) (y : Fin n), h ((σ ^ m) y) = h y := by
        intro m; induction m with
        | zero => intro y; simp
        | succ m ih => intro y; rw [pow_succ, Equiv.Perm.mul_apply, ih, hc]
      have hconst : ∀ k₁ k₂, π k₁ = π k₂ → h k₁ = h k₂ := by
        intro k₁ k₂ hk
        obtain ⟨m, -, hm⟩ := ((hπ.1 k₁ k₂).mp hk).exists_pow_eq'
        exact (hiter m k₁).symm.trans (congrArg h hm)
      ⟨σ,
        ⟨fun i => (h (rep i)).1, fun j => by
          dsimp only
          trans (Finset.univ.filter (fun i => (h (rep i)).1 = j)).sum
            (fun i => (Finset.univ.filter (fun k : Fin n => π k = i)).card)
          · exact Finset.sum_congr rfl (fun i _ => (hπ.2 i).symm)
          rw [← Finset.card_biUnion (fun i₁ hi₁ i₂ hi₂ hij =>
            Finset.disjoint_filter.mpr (fun k _ h₁ h₂ => hij (h₁ ▸ h₂)))]
          suffices heq : (Finset.univ.filter (fun i => (h (rep i)).1 = j)).biUnion
              (fun i => Finset.univ.filter (fun k : Fin n => π k = i)) =
              Finset.univ.filter (fun x => (h x).1 = j) by rw [heq]; exact hrow j
          ext k; simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · rintro ⟨i, hi, hk⟩
            rw [← hk] at hi; rwa [hconst _ _ (hrep (π k))] at hi
          · intro hk; exact ⟨π k, by rwa [← hconst k (rep (π k)) (hrep (π k)).symm], rfl⟩⟩,
        ⟨fun i => (h (rep i)).2, fun j => by
          dsimp only
          trans (Finset.univ.filter (fun i => (h (rep i)).2 = j)).sum
            (fun i => (Finset.univ.filter (fun k : Fin n => π k = i)).card)
          · exact Finset.sum_congr rfl (fun i _ => (hπ.2 i).symm)
          rw [← Finset.card_biUnion (fun i₁ hi₁ i₂ hi₂ hij =>
            Finset.disjoint_filter.mpr (fun k _ h₁ h₂ => hij (h₁ ▸ h₂)))]
          suffices heq : (Finset.univ.filter (fun i => (h (rep i)).2 = j)).biUnion
              (fun i => Finset.univ.filter (fun k : Fin n => π k = i)) =
              Finset.univ.filter (fun x => (h x).2 = j) by rw [heq]; exact hcol j
          ext k; simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · rintro ⟨i, hi, hk⟩
            rw [← hk] at hi; rwa [hconst _ _ (hrep (π k))] at hi
          · intro hk; exact ⟨π k, by rwa [← hconst k (rep (π k)) (hrep (π k)).symm], rfl⟩⟩⟩
    left_inv := fun ⟨σ, fg⟩ => by
      -- invFun uses projections, so we can reason about the components
      let π := (exists_orbIdx σ).choose
      have hπ := (exists_orbIdx σ).choose_spec
      have hne : ∀ i : Fin (fullCycleType n σ).toList.length,
          (Finset.univ.filter (fun k : Fin n => π k = i)).Nonempty := by
        intro i; by_contra hemp
        rw [Finset.not_nonempty_iff_eq_empty] at hemp
        have h1 := hπ.2 i; rw [hemp, Finset.card_empty] at h1
        have h2 := fullCycleType_pos σ _ (Multiset.mem_toList.mp (List.getElem_mem i.isLt))
        omega
      have hrep : ∀ i, π ((Finset.univ.filter (fun k : Fin n => π k = i)).min' (hne i)) = i :=
        fun i => (Finset.mem_filter.mp (Finset.min'_mem _ (hne i))).2
      -- Goal: ⟨σ, (⟨f', _⟩, ⟨g', _⟩)⟩ = ⟨σ, fg⟩ where f'(i) = (bicol(rep(i))).1
      -- Since σ matches, reduce to product equality
      refine Sigma.ext rfl (heq_of_eq ?_)
      simp only [cycleColToBicol]
      apply Prod.ext
      · apply Subtype.ext; funext i; exact congrArg fg.1.val (hrep i)
      · apply Subtype.ext; funext i; exact congrArg fg.2.val (hrep i)
    right_inv := fun ⟨⟨h, hrow, hcol⟩, ⟨σ, hcompat⟩⟩ => by
      simp only [cycleColToBicol]
      let π := (exists_orbIdx σ).choose
      have hπ := (exists_orbIdx σ).choose_spec
      have hne : ∀ i : Fin (fullCycleType n σ).toList.length,
          (Finset.univ.filter (fun k : Fin n => π k = i)).Nonempty := by
        intro i; by_contra hemp
        rw [Finset.not_nonempty_iff_eq_empty] at hemp
        have h1 := hπ.2 i; rw [hemp, Finset.card_empty] at h1
        have h2 := fullCycleType_pos σ _ (Multiset.mem_toList.mp (List.getElem_mem i.isLt))
        omega
      have hrep : ∀ i, π ((Finset.univ.filter (fun k : Fin n => π k = i)).min' (hne i)) = i :=
        fun i => (Finset.mem_filter.mp (Finset.min'_mem _ (hne i))).2
      have hc : ∀ x, h (σ x) = h x := hcompat
      have hiter : ∀ (m : ℕ) (y : Fin n), h ((σ ^ m) y) = h y := by
        intro m; induction m with
        | zero => intro y; simp
        | succ m ih =>
          intro y; rw [pow_succ, Equiv.Perm.mul_apply, ih, hc]
      have hconst : ∀ k₁ k₂, π k₁ = π k₂ → h k₁ = h k₂ := by
        intro k₁ k₂ hk
        obtain ⟨m, -, hm⟩ := ((hπ.1 k₁ k₂).mp hk).exists_pow_eq'
        exact (hiter m k₁).symm.trans (congrArg h hm)
      -- Need to show the round trip (h', σ') = (h, σ)
      ext1
      · -- h is recovered: h'(x) = (h(rep(π x)).1, h(rep(π x)).2) = h(x)
        apply Subtype.ext; funext x
        have key := hconst _ x (hrep (π x))
        simp only [Prod.mk.eta]; exact key
      · -- σ is recovered (trivially, since the invFun outputs σ directly)
        rfl
  }

/-! ### MulAction of permutations on element bicolorings -/

/-- Precomposing a filter with a permutation preserves cardinality. -/
private lemma filter_card_comp_perm {n : ℕ} (P : Fin n → Prop) [DecidablePred P]
    (σ : Equiv.Perm (Fin n)) :
    (Finset.univ.filter (fun x => P (σ x))).card = (Finset.univ.filter P).card := by
  apply Finset.card_bij' (fun x _ => σ x) (fun x _ => σ⁻¹ x)
  · intro x hx; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢; exact hx
  · intro x hx; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    convert hx using 1; simp
  · intro x _; simp
  · intro x _; simp

private noncomputable def permSmulElemBicol {n : ℕ} {α β : Fin n →₀ ℕ}
    (σ : Equiv.Perm (Fin n)) (hb : ElemBicol n α β) : ElemBicol n α β :=
  ⟨hb.val ∘ ⇑σ⁻¹, by
    constructor
    · intro i
      have h1 : (Finset.univ.filter (fun x => ((hb.val ∘ ⇑σ⁻¹) x).1 = i)).card =
          (Finset.univ.filter (fun x => (hb.val x).1 = i)).card :=
        filter_card_comp_perm (fun x => (hb.val x).1 = i) σ⁻¹
      rw [h1]; exact hb.2.1 i
    · intro j
      have h1 : (Finset.univ.filter (fun x => ((hb.val ∘ ⇑σ⁻¹) x).2 = j)).card =
          (Finset.univ.filter (fun x => (hb.val x).2 = j)).card :=
        filter_card_comp_perm (fun x => (hb.val x).2 = j) σ⁻¹
      rw [h1]; exact hb.2.2 j⟩

@[simp]
private lemma permSmulElemBicol_val {n : ℕ} {α β : Fin n →₀ ℕ}
    (σ : Equiv.Perm (Fin n)) (hb : ElemBicol n α β) :
    (permSmulElemBicol σ hb).val = hb.val ∘ ⇑σ⁻¹ := rfl

private noncomputable instance permMulActionElemBicol {n : ℕ} {α β : Fin n →₀ ℕ} :
    MulAction (Equiv.Perm (Fin n)) (ElemBicol n α β) where
  smul := permSmulElemBicol
  one_smul hb := Subtype.ext (funext fun _ => by
    show (permSmulElemBicol 1 hb).val _ = hb.val _
    simp [permSmulElemBicol_val, Function.comp])
  mul_smul σ τ hb := Subtype.ext (funext fun x => by
    show (permSmulElemBicol (σ * τ) hb).val x = (permSmulElemBicol σ (permSmulElemBicol τ hb)).val x
    simp [permSmulElemBicol_val, Function.comp, mul_inv_rev, Equiv.Perm.mul_apply])

/-- The stabilizer of h under the Perm action equals FiberPerm h. -/
private lemma mem_stabilizer_iff_fiberPerm {n : ℕ} {α β : Fin n →₀ ℕ}
    (hb : ElemBicol n α β) (σ : Equiv.Perm (Fin n)) :
    σ ∈ MulAction.stabilizer (Equiv.Perm (Fin n)) hb ↔ ∀ x, hb.val (σ x) = hb.val x := by
  simp only [MulAction.mem_stabilizer_iff]
  constructor
  · intro h x
    have h1 := congr_arg Subtype.val h  -- (σ • hb).val = hb.val
    rw [show (σ • hb).val = hb.val ∘ ⇑σ⁻¹ from permSmulElemBicol_val σ hb] at h1
    have := congr_fun h1 (σ x)         -- hb.val (σ⁻¹ (σ x)) = hb.val (σ x)
    simp at this; exact this.symm
  · intro h
    apply Subtype.ext
    rw [show (σ • hb).val = hb.val ∘ ⇑σ⁻¹ from permSmulElemBicol_val σ hb]
    funext x
    have := h (σ⁻¹ x)                 -- hb.val (σ (σ⁻¹ x)) = hb.val (σ⁻¹ x)
    simp at this; exact this.symm

/-- Fiber size matrix: maps an element bicoloring to its fiber size matrix. -/
private noncomputable def fiberSizes {n : ℕ} {α β : Fin n →₀ ℕ}
    (hb : ElemBicol n α β) : NNMatrixWithMargins n (⇑α) (⇑β) :=
  ⟨fun i j => ⟨(Finset.univ.filter fun x => hb.val x = (i, j)).card,
    Nat.lt_succ_of_le <| (Finset.card_filter_le _ _).trans <| by simp [Fintype.card_fin]⟩,
   fun i => by
     simp only [Fin.val_natCast]
     rw [← hb.2.1 i]
     rw [← Finset.card_biUnion (fun j₁ _ j₂ _ hj =>
       Finset.disjoint_filter.mpr (fun x _ h₁ h₂ => hj (by
         have := h₁.symm.trans h₂; exact Prod.ext_iff.mp this |>.2)))]
     congr 1; ext x
     simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and, Prod.ext_iff]
     exact ⟨fun ⟨j, ⟨h1, h2⟩⟩ => h1, fun h => ⟨(hb.val x).2, ⟨h, rfl⟩⟩⟩,
   fun j => by
     simp only [Fin.val_natCast]
     rw [← hb.2.2 j]
     rw [← Finset.card_biUnion (fun i₁ _ i₂ _ hi =>
       Finset.disjoint_filter.mpr (fun x _ h₁ h₂ => hi (by
         have := h₁.symm.trans h₂; exact Prod.ext_iff.mp this |>.1)))]
     congr 1; ext x
     simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and, Prod.ext_iff]
     exact ⟨fun ⟨i, ⟨h1, h2⟩⟩ => h2, fun h => ⟨(hb.val x).1, ⟨rfl, h⟩⟩⟩⟩

@[simp]
private lemma smul_val {n : ℕ} {α β : Fin n →₀ ℕ}
    (σ : Equiv.Perm (Fin n)) (hb : ElemBicol n α β) :
    (σ • hb).val = hb.val ∘ ⇑σ⁻¹ :=
  permSmulElemBicol_val σ hb

/-- Precomposing a filter with an equiv preserves cardinality (between different types). -/
private lemma filter_card_comp_equiv {α' β' : Type*} [Fintype α'] [Fintype β']
    (e : α' ≃ β') (P : β' → Prop) [DecidablePred P] :
    (Finset.univ.filter (fun x => P (e x))).card = (Finset.univ.filter P).card := by
  apply Finset.card_bij' (fun x _ => e x) (fun y _ => e.symm y)
  · intro x hx; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢; exact hx
  · intro y hy; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    convert hy using 1; simp
  · intro x _; simp
  · intro y _; simp

/-- Fiber sizes are invariant under the Perm action. -/
private lemma fiberSizes_smul_eq {n : ℕ} {α β : Fin n →₀ ℕ}
    (σ : Equiv.Perm (Fin n)) (hb : ElemBicol n α β) :
    fiberSizes (σ • hb) = fiberSizes hb := by
  apply Subtype.ext; funext i; funext j; apply Fin.ext
  simp only [fiberSizes, smul_val]
  exact filter_card_comp_perm (fun x => hb.val x = (i, j)) σ⁻¹

/-- Two bicolorings with the same fiber sizes are in the same orbit. -/
private lemma same_fiberSizes_same_orbit {n : ℕ} {α β : Fin n →₀ ℕ}
    (h₁ h₂ : ElemBicol n α β) (heq : fiberSizes h₁ = fiberSizes h₂) :
    h₁ ∈ MulAction.orbit (Equiv.Perm (Fin n)) h₂ := by
  classical
  -- For each pair, the fibers have the same size
  have hcard : ∀ p : Fin n × Fin n,
      Fintype.card { x // h₁.val x = p } = Fintype.card { x // h₂.val x = p } := by
    intro ⟨i, j⟩
    simp only [Fintype.card_subtype, Finset.card_filter]
    have := congr_arg (fun K => (K.1 i j : ℕ)) heq
    simpa [fiberSizes] using this
  -- Build a permutation matching fibers via Equiv.ofFiberEquiv
  let σ : Equiv.Perm (Fin n) :=
    Equiv.ofFiberEquiv (f := h₁.val) (g := h₂.val)
      (fun p => Fintype.equivOfCardEq (hcard p))
  -- σ satisfies h₂(σ x) = h₁(x) by ofFiberEquiv_map
  have hσ : ∀ x, h₂.val (σ x) = h₁.val x := Equiv.ofFiberEquiv_map _
  -- So h₁ = σ⁻¹ • h₂ (since (σ⁻¹ • h₂)(x) = h₂(σ x) = h₁(x))
  refine ⟨σ⁻¹, Subtype.ext (funext fun x => ?_)⟩
  simp only [smul_val, Function.comp, inv_inv]
  exact hσ x

/-- Counting lemma: for a sigma type `Σ (ij : A × B), F ij`, filtering by first
    component gives the sum of fiber sizes. -/
private lemma sigma_filter_fst_card {n : ℕ} (K : Fin n → Fin n → ℕ) (i : Fin n) :
    (Finset.univ.filter (fun (s : Σ ij : Fin n × Fin n, Fin (K ij.1 ij.2)) =>
      s.1.1 = i)).card = ∑ j, K i j := by
  rw [← Fintype.card_subtype,
      show ∑ j, K i j = Fintype.card (Σ j : Fin n, Fin (K i j)) from
        by simp [Fintype.card_sigma, Fintype.card_fin]]
  exact Fintype.card_congr {
    toFun := fun ⟨⟨⟨i', j⟩, k⟩, (hi : i' = i)⟩ => ⟨j, hi ▸ k⟩
    invFun := fun ⟨j, k⟩ => ⟨⟨(i, j), k⟩, rfl⟩
    left_inv := fun ⟨⟨⟨i', j⟩, k⟩, hi⟩ => by subst hi; rfl
    right_inv := fun ⟨j, k⟩ => rfl }

/-- Same as `sigma_filter_fst_card` but for the second component. -/
private lemma sigma_filter_snd_card {n : ℕ} (K : Fin n → Fin n → ℕ) (j : Fin n) :
    (Finset.univ.filter (fun (s : Σ ij : Fin n × Fin n, Fin (K ij.1 ij.2)) =>
      s.1.2 = j)).card = ∑ i, K i j := by
  rw [← Fintype.card_subtype,
      show ∑ i, K i j = Fintype.card (Σ i : Fin n, Fin (K i j)) from
        by simp [Fintype.card_sigma, Fintype.card_fin]]
  exact Fintype.card_congr {
    toFun := fun ⟨⟨⟨i, j'⟩, k⟩, (hj : j' = j)⟩ => ⟨i, hj ▸ k⟩
    invFun := fun ⟨i, k⟩ => ⟨⟨(i, j), k⟩, rfl⟩
    left_inv := fun ⟨⟨⟨i, j'⟩, k⟩, hj⟩ => by subst hj; rfl
    right_inv := fun ⟨i, k⟩ => rfl }

/-- Fiber counting: the filter for exact pair (i,j) has cardinality K i j. -/
private lemma sigma_filter_pair_card {n : ℕ} (K : Fin n → Fin n → ℕ) (i j : Fin n) :
    (Finset.univ.filter (fun (s : Σ ij : Fin n × Fin n, Fin (K ij.1 ij.2)) =>
      s.1 = (i, j))).card = K i j := by
  have : Finset.univ.filter (fun (s : Σ ij : Fin n × Fin n, Fin (K ij.1 ij.2)) =>
      s.1 = (i, j)) =
    (Finset.univ : Finset (Fin (K i j))).map
      ⟨fun k => ⟨(i, j), k⟩, fun k₁ k₂ h => by simpa using h⟩ := by
    ext ⟨⟨i', j'⟩, k⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Function.Embedding.coeFn_mk]
    constructor
    · intro h; obtain ⟨rfl, rfl⟩ := Prod.mk.inj h; exact ⟨k, rfl⟩
    · rintro ⟨k', hk'⟩; exact (congr_arg Sigma.fst hk').symm
  rw [this, Finset.card_map, Finset.card_fin]

/-- The equiv used by `elemBicolOfMatrix` to distribute elements to fibers. -/
private noncomputable def elemBicolOfMatrix_equiv {n : ℕ} {α β : Fin n →₀ ℕ}
    (hα : ∑ i, α i = n) (K : NNMatrixWithMargins n (⇑α) (⇑β)) :
    Fin n ≃ (Σ ij : Fin n × Fin n, Fin (K.1 ij.1 ij.2 : ℕ)) :=
  Fintype.equivOfCardEq (by
    simp only [Fintype.card_sigma, Fintype.card_fin, Fintype.sum_prod_type]
    simp_rw [K.2.1]; rw [hα])

/-- Construct an ElemBicol from a NNMatrixWithMargins by distributing elements
    to fibers according to the matrix entries. -/
private noncomputable def elemBicolOfMatrix {n : ℕ} {α β : Fin n →₀ ℕ}
    (hα : ∑ i, α i = n) (K : NNMatrixWithMargins n (⇑α) (⇑β)) :
    ElemBicol n α β :=
  ⟨fun x => (elemBicolOfMatrix_equiv hα K x).1,
   ⟨fun i => by
      classical
      rw [filter_card_comp_equiv (elemBicolOfMatrix_equiv hα K) (fun s => s.1.1 = i)]
      rw [sigma_filter_fst_card (fun i j => (K.1 i j : ℕ)) i]
      exact K.2.1 i,
    fun j => by
      classical
      rw [filter_card_comp_equiv (elemBicolOfMatrix_equiv hα K) (fun s => s.1.2 = j)]
      rw [sigma_filter_snd_card (fun i j => (K.1 i j : ℕ)) j]
      exact K.2.2 j⟩⟩

@[simp]
private lemma elemBicolOfMatrix_val {n : ℕ} {α β : Fin n →₀ ℕ}
    (hα : ∑ i, α i = n) (K : NNMatrixWithMargins n (⇑α) (⇑β)) :
    (elemBicolOfMatrix hα K).val = fun x => (elemBicolOfMatrix_equiv hα K x).1 := rfl

/-- The fiber sizes of `elemBicolOfMatrix` equal the original matrix K. -/
private lemma fiberSizes_elemBicolOfMatrix {n : ℕ} {α β : Fin n →₀ ℕ}
    (hα : ∑ i, α i = n) (K : NNMatrixWithMargins n (⇑α) (⇑β)) :
    fiberSizes (elemBicolOfMatrix hα K) = K := by
  classical
  apply Subtype.ext; funext i; funext j; apply Fin.ext
  simp only [fiberSizes, elemBicolOfMatrix_val]
  rw [filter_card_comp_equiv (elemBicolOfMatrix_equiv hα K) (fun s => s.1 = (i, j))]
  exact sigma_filter_pair_card (fun i j => (K.1 i j : ℕ)) i j

/-- **Part B**: The total count of compatible (h, σ) pairs equals n! × card(NNMat).

**Proof strategy**: Define a `MulAction` of `Equiv.Perm (Fin n)` on `ElemBicol n α β` by
`(σ • h)(x) = h(σ⁻¹ x)`. Then:
1. The stabilizer of h equals `FiberPerm h` (both are `{σ | h ∘ σ = h}`).
2. The orbits are classified by fiber-size matrices: two h's are in the same orbit
   iff they have the same fiber sizes `K_{ij} = |h⁻¹(i,j)|`, giving `Ω ≃ NNMatrixWithMargins`.
3. By the orbit-stabilizer equivalence (`MulAction.sigmaFixedByEquivOrbitsProdGroup`):
   `(Σ h, stabilizer h) ≃ Ω × Perm(Fin n)`, so
   `card(Σ h, FiberPerm h) = card(NNMat) × n!`.

Alternatively, construct a direct equiv
`(Σ h : ElemBicol, FiberPerm h) ≃ Equiv.Perm (Fin n) × NNMatrixWithMargins`
via the backward map `(τ, K) ↦ (h, σ)` where `h(x) = blockAssign(K, τ⁻¹ x)` assigns elements
to blocks based on K's cumulative sums, and `σ(eₘ) = τ(cum(i,j) + m)` for the m-th sorted
element eₘ of each fiber h⁻¹(i,j). -/
private lemma card_sigma_fiberPerm_eq_factorial_mul (n : ℕ) (α β : Fin n →₀ ℕ)
    (hα : ∑ i, α i = n) (hβ : ∑ i, β i = n) :
    Fintype.card (Σ hb : ElemBicol n α β, FiberPerm hb.val) =
    n.factorial * Fintype.card (NNMatrixWithMargins n (⇑α) (⇑β)) := by
  classical
  -- Step 1: FiberPerm h ≃ stabilizer h (as subtypes of Perm)
  have step1 : Fintype.card (Σ hb : ElemBicol n α β, FiberPerm hb.val) =
      Fintype.card (Σ hb : ElemBicol n α β,
        MulAction.stabilizer (Equiv.Perm (Fin n)) hb) := by
    apply Fintype.card_congr
    exact Equiv.sigmaCongrRight (fun hb =>
      Equiv.subtypeEquiv (Equiv.refl _) (fun σ =>
        (mem_stabilizer_iff_fiberPerm hb σ).symm))
  rw [step1]
  -- Step 2: Swap sigma: (Σ h, stab h) has same card as (Σ σ, fixedBy σ)
  have step2 : Fintype.card (Σ hb : ElemBicol n α β,
      MulAction.stabilizer (Equiv.Perm (Fin n)) hb) =
    Fintype.card (Σ σ : Equiv.Perm (Fin n),
      MulAction.fixedBy (ElemBicol n α β) σ) := by
    apply Fintype.card_congr
    calc (Σ hb : ElemBicol n α β, MulAction.stabilizer (Equiv.Perm (Fin n)) hb)
      ≃ { p : ElemBicol n α β × Equiv.Perm (Fin n) // p.2 ∈ MulAction.stabilizer _ p.1 } :=
        (Equiv.subtypeProdEquivSigmaSubtype
          (fun (hb : ElemBicol n α β) (σ : Equiv.Perm (Fin n)) =>
            σ ∈ MulAction.stabilizer _ hb)).symm
      _ ≃ { p : Equiv.Perm (Fin n) × ElemBicol n α β // p.1 ∈ MulAction.stabilizer _ p.2 } :=
        (Equiv.prodComm _ _).subtypeEquiv (fun ⟨hb, σ⟩ => Iff.rfl)
      _ ≃ { p : Equiv.Perm (Fin n) × ElemBicol n α β // p.2 ∈ MulAction.fixedBy _ p.1 } :=
        Equiv.subtypeEquivRight (fun ⟨σ, hb⟩ => by
          simp [MulAction.mem_stabilizer_iff, MulAction.mem_fixedBy])
      _ ≃ (Σ σ : Equiv.Perm (Fin n), MulAction.fixedBy (ElemBicol n α β) σ) :=
        Equiv.subtypeProdEquivSigmaSubtype
          (fun (σ : Equiv.Perm (Fin n)) (hb : ElemBicol n α β) =>
            hb ∈ MulAction.fixedBy _ σ)
  rw [step2]
  -- Step 3: Apply Burnside's lemma
  rw [show Fintype.card (Σ σ : Equiv.Perm (Fin n), MulAction.fixedBy (ElemBicol n α β) σ) =
    ∑ σ : Equiv.Perm (Fin n), Fintype.card (MulAction.fixedBy (ElemBicol n α β) σ) from
    Fintype.card_sigma]
  rw [MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group]
  rw [Fintype.card_perm, Fintype.card_fin]
  -- Goal: card(Orbits) * n! = n! * card(NNMat)
  rw [mul_comm]
  congr 1
  -- Step 4: Orbits ≃ NNMatrixWithMargins via fiberSizes
  apply Fintype.card_congr
  letI := MulAction.orbitRel (Equiv.Perm (Fin n)) (ElemBicol n α β)
  exact Equiv.ofBijective
    (Quotient.lift fiberSizes (fun a b (hab : a ∈ MulAction.orbit _ b) => by
      obtain ⟨g, rfl⟩ := hab; exact fiberSizes_smul_eq g b))
    ⟨fun q₁ q₂ => Quotient.inductionOn₂ q₁ q₂ (fun a b heq =>
        Quotient.sound (same_fiberSizes_same_orbit a b heq)),
     fun K => ⟨Quotient.mk' (elemBicolOfMatrix hα K),
              fiberSizes_elemBicolOfMatrix hα K⟩⟩

/-- **Double counting lemma**: The total number of (σ, f, g) triples equals
n! times the number of matrices with given margins.

This is the combinatorial core. For each matrix K with given margins:
- There are n!/∏K_{ij}! ways to partition [n] into blocks of sizes K_{ij}
- There are ∏K_{ij}! permutations within each block
- Product = n! independent of K -/
theorem double_counting (n : ℕ) (α β : Fin n →₀ ℕ)
    (hα : ∑ i, α i = n) (hβ : ∑ i, β i = n) :
    ∑ σ : Equiv.Perm (Fin n),
      Fintype.card (CycleColoring n α σ) * Fintype.card (CycleColoring n β σ) =
    n.factorial * Fintype.card (NNMatrixWithMargins n (⇑α) (⇑β)) := by
  -- Step 1: Rewrite LHS as card of sigma type
  have h1 : ∑ σ : Equiv.Perm (Fin n),
      Fintype.card (CycleColoring n α σ) * Fintype.card (CycleColoring n β σ) =
    Fintype.card (Σ σ : Equiv.Perm (Fin n), CycleColoring n α σ × CycleColoring n β σ) := by
    simp_rw [← Fintype.card_prod]; exact Fintype.card_sigma.symm
  rw [h1]
  -- Step 2: Part A equivalence + Part B cardinality
  rw [card_sigma_CycleCol_eq_card_sigma_fiberPerm n α β hα hβ]
  exact card_sigma_fiberPerm_eq_factorial_mul n α β hα hβ

/-- **Power Sum Cauchy Identity** (coefficient-level bilinear version):

For any `α β : Fin n →₀ ℕ` with total degree n,

  ∑_{σ∈Sₙ} [x^α](P_σ) · [x^β](P_σ) = n! · [x^α y^β](∏_{i,j} 1/(1-xᵢyⱼ))

The proof reduces to the `double_counting` lemma: both sides count the same
set of (permutation, bicoloring) triples with different groupings. -/
theorem powerSum_bilinear_coeff (n : ℕ) (α β : Fin n →₀ ℕ)
    (hα : ∑ i, α i = n) (hβ : ∑ i, β i = n) :
    (∑ σ : Equiv.Perm (Fin n),
      (MvPolynomial.coeff α (cycleTypePsumProduct n σ) : ℂ) *
      (MvPolynomial.coeff β (cycleTypePsumProduct n σ) : ℂ)) =
    (Nat.factorial n : ℂ) * MvPowerSeries.coeff (bilinExponent n α β)
      (fullCauchyProd n ℂ) := by
  -- Rewrite each MvPolynomial coefficient as card of CycleColoring
  simp_rw [coeff_cycleTypePsumProduct_eq_card]
  -- Rewrite Cauchy product coefficient as card of NNMatrixWithMargins
  have hα' : ∀ i, (α : Fin n → ℕ) i ≤ n := by
    intro i
    have := Finset.single_le_sum (f := (⇑α : Fin n → ℕ)) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ i)
    omega
  rw [fullCauchyProd_coeff_eq_card n (⇑α) (⇑β) hα']
  -- Both sides are natural number casts; reduce to ℕ equality
  simp only [← Nat.cast_mul, ← Nat.cast_sum]
  congr 1
  exact double_counting n α β hα hβ

/-- **Vandermonde-Cauchy diagonal coefficient identity**.

For injective `α : Fin N → ℕ`, the double alternating sum of `fullCauchyProd` coefficients
equals 1. This encodes the coefficient-level content of the identity
`Δ_x · Δ_y · ∏_{i,j} 1/(1-xᵢyⱼ) = cauchyRHS`, evaluated at the diagonal exponent `(α, α)`.

The proof requires the formal power series Cauchy determinant identity
(connecting `fullCauchyProd` to `cauchyRHS` via Vandermonde polynomials)
together with `cauchyRHS_coeff_bilin_of_injective`. -/
theorem vandermonde_cauchy_diagonal (N : ℕ) (α : Fin N → ℕ)
    (hα_inj : Function.Injective α) :
    (∑ π : Equiv.Perm (Fin N), ∑ τ : Equiv.Perm (Fin N),
      ((Equiv.Perm.sign π : ℤ) : ℂ) * ((Equiv.Perm.sign τ : ℤ) : ℂ) *
      (if (∀ i, (π⁻¹ i : Fin N).val ≤ α i) ∧ (∀ i, (τ⁻¹ i : Fin N).val ≤ α i)
       then MvPowerSeries.coeff
              (bilinExponent N (fun i => α i - (π⁻¹ i : Fin N).val)
                               (fun i => α i - (τ⁻¹ i : Fin N).val))
              (fullCauchyProd N ℂ)
       else 0)) = 1 := by
  sorry

end Etingof
