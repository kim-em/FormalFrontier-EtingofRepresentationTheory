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
  sorry

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

end Etingof
