import Mathlib
import EtingofRepresentationTheory.Chapter5.Corollary5_15_4

/-!
# Power Sum Cauchy Identity and Coefficient Extraction
-/

open Finset Equiv.Perm MvPowerSeries Etingof

noncomputable section

namespace Etingof

variable (N : ℕ) (k : Type*) [Field k]

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

private theorem prod_mul_prod_invOfUnit_eq_one (σ : Equiv.Perm (Fin N)) :
    (∏ j : Fin N,
      (1 - MvPowerSeries.X (Sum.inl j) * MvPowerSeries.X (Sum.inr (σ j)) :
        MvPowerSeries (CauchyVars N) k)) *
    (∏ j : Fin N,
      MvPowerSeries.invOfUnit
        (1 - MvPowerSeries.X (Sum.inl j) * MvPowerSeries.X (Sum.inr (σ j)))
        1) = 1 := by
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro j _
  exact MvPowerSeries.mul_invOfUnit _ _ (by simp [MvPowerSeries.constantCoeff_X])

private theorem isUnit_prod_one_sub (σ : Equiv.Perm (Fin N)) :
    IsUnit (∏ j : Fin N,
      (1 - MvPowerSeries.X (Sum.inl j) * MvPowerSeries.X (Sum.inr (σ j)) :
        MvPowerSeries (CauchyVars N) k)) := by
  rw [MvPowerSeries.isUnit_iff_constantCoeff]
  simp [map_prod, MvPowerSeries.constantCoeff_X]

private def cauchyProdTarget (σ : Equiv.Perm (Fin N)) :
    MvPowerSeries (CauchyVars N) k :=
  fun d => if (∀ j : Fin N, d (Sum.inl j) = d (Sum.inr (σ j))) then 1 else 0

/-! ### Telescoping proof infrastructure -/

-- A partial target series parameterized by a subset S of Fin N.
-- For S = ∅, this is 1. For S = univ, this is cauchyProdTarget.
private def partialTarget (σ : Equiv.Perm (Fin N)) (S : Finset (Fin N)) :
    MvPowerSeries (CauchyVars N) k :=
  fun d => if (∀ j ∈ S, d (Sum.inl j) = d (Sum.inr (σ j))) ∧
               (∀ j : Fin N, j ∉ S → d (Sum.inl j) = 0 ∧ d (Sum.inr (σ j)) = 0)
           then 1 else 0

@[simp]
private theorem partialTarget_coeff (σ : Equiv.Perm (Fin N)) (S : Finset (Fin N))
    (d : CauchyVars N →₀ ℕ) :
    MvPowerSeries.coeff (R := k) d (partialTarget N k σ S) =
    if (∀ j ∈ S, d (Sum.inl j) = d (Sum.inr (σ j))) ∧
       (∀ j : Fin N, j ∉ S → d (Sum.inl j) = 0 ∧ d (Sum.inr (σ j)) = 0)
    then 1 else 0 := rfl

private abbrev xyMon (σ : Equiv.Perm (Fin N)) (j : Fin N) : CauchyVars N →₀ ℕ :=
  Finsupp.single (Sum.inl j) 1 + Finsupp.single (Sum.inr (σ j)) 1

private theorem coeff_one_sub_XmulX_mul (σ : Equiv.Perm (Fin N)) (j : Fin N)
    (f : MvPowerSeries (CauchyVars N) k) (d : CauchyVars N →₀ ℕ) :
    MvPowerSeries.coeff (R := k) d
      ((1 - MvPowerSeries.X (Sum.inl j) * MvPowerSeries.X (Sum.inr (σ j))) * f) =
    MvPowerSeries.coeff (R := k) d f -
      if xyMon N σ j ≤ d then MvPowerSeries.coeff (R := k) (d - xyMon N σ j) f else 0 := by
  have hXX : (MvPowerSeries.X (Sum.inl j) * MvPowerSeries.X (Sum.inr (σ j)) :
      MvPowerSeries (CauchyVars N) k) =
    MvPowerSeries.monomial (R := k) (xyMon N σ j) 1 := by
    simp [xyMon, MvPowerSeries.X, MvPowerSeries.monomial_mul_monomial]
  rw [sub_mul, one_mul, map_sub, hXX, MvPowerSeries.coeff_monomial_mul]
  simp

-- Main telescoping step: multiplying by (1 - X_j Y_{σj}) removes slot j from partialTarget
private theorem one_sub_mul_partialTarget (σ : Equiv.Perm (Fin N)) (S : Finset (Fin N))
    (j : Fin N) (hj : j ∉ S) :
    (1 - MvPowerSeries.X (Sum.inl j) * MvPowerSeries.X (Sum.inr (σ j)) :
      MvPowerSeries (CauchyVars N) k) *
      partialTarget N k σ (insert j S) = partialTarget N k σ S := by
  apply MvPowerSeries.ext; intro d
  rw [coeff_one_sub_XmulX_mul]
  simp only [partialTarget_coeff]
  by_cases hS : (∀ i ∈ S, d (Sum.inl i) = d (Sum.inr (σ i))) ∧
      (∀ i, i ∉ S → d (Sum.inl i) = 0 ∧ d (Sum.inr (σ i)) = 0)
  · -- S-condition holds → d at slot j is zero
    have hj0 := (hS.2 j hj).1
    have hj0' := (hS.2 j hj).2
    have hA : (∀ i ∈ insert j S, d (Sum.inl i) = d (Sum.inr (σ i))) ∧
        (∀ i, i ∉ insert j S → d (Sum.inl i) = 0 ∧ d (Sum.inr (σ i)) = 0) :=
      ⟨fun i hi => by
        rcases Finset.mem_insert.mp hi with rfl | hiS
        · rw [hj0, hj0']
        · exact hS.1 i hiS,
       fun i hi => by
        rw [Finset.mem_insert, not_or] at hi
        exact hS.2 i hi.2⟩
    have hle : ¬(xyMon N σ j ≤ d) := by
      intro h; have := h (Sum.inl j); simp [xyMon] at this; omega
    simp only [if_pos hA, if_neg hle, sub_zero, if_pos hS]
  · -- S-condition fails
    simp only [if_neg hS]
    by_cases hA : (∀ i ∈ insert j S, d (Sum.inl i) = d (Sum.inr (σ i))) ∧
        (∀ i, i ∉ insert j S → d (Sum.inl i) = 0 ∧ d (Sum.inr (σ i)) = 0)
    · -- Insert-cond holds, S-cond fails → j-slot nonzero and diagonal
      have hj_eq : d (Sum.inl j) = d (Sum.inr (σ j)) := hA.1 j (Finset.mem_insert_self j S)
      have hj_pos : 0 < d (Sum.inl j) := by
        by_contra h; push_neg at h
        have hj0 : d (Sum.inl j) = 0 := by omega
        apply hS
        exact ⟨fun i hiS => hA.1 i (Finset.mem_insert_of_mem hiS),
               fun i hiS => by
                 by_cases hij : i = j
                 · exact hij ▸ ⟨hj0, hj_eq ▸ hj0⟩
                 · exact hA.2 i (by rw [Finset.mem_insert, not_or]; exact ⟨hij, hiS⟩)⟩
      simp only [if_pos hA]
      have hle : xyMon N σ j ≤ d := by
        intro v; simp only [xyMon, Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply]
        cases v with
        | inl i =>
          by_cases h : i = j
          · subst h; simp; omega
          · simp [Ne.symm h]
        | inr i =>
          by_cases h : i = σ j
          · subst h; simp; omega
          · simp [Ne.symm h]
      simp only [if_pos hle]
      have hA' : (∀ i ∈ insert j S,
          (d - xyMon N σ j) (Sum.inl i) = (d - xyMon N σ j) (Sum.inr (σ i))) ∧
          (∀ i, i ∉ insert j S →
            (d - xyMon N σ j) (Sum.inl i) = 0 ∧
            (d - xyMon N σ j) (Sum.inr (σ i)) = 0) := by
        refine ⟨fun i hi => ?_, fun i hi => ?_⟩
        · rcases Finset.mem_insert.mp hi with rfl | hiS
          · simp [xyMon, hj_eq]
          · have hij : i ≠ j := fun h => hj (h ▸ hiS)
            simp [xyMon, hij, σ.injective.ne hij,
              hA.1 i (Finset.mem_insert_of_mem hiS)]
        · rw [Finset.mem_insert, not_or] at hi
          have ⟨hz1, hz2⟩ := hA.2 i (by rw [Finset.mem_insert, not_or]; exact hi)
          simp [xyMon, hi.1, σ.injective.ne hi.1, hz1, hz2]
      simp only [if_pos hA']; ring
    · -- Both conditions fail; show subtracted term also zero
      have : ∀ hle' : xyMon N σ j ≤ d,
          ¬((∀ i ∈ insert j S,
            (d - xyMon N σ j) (Sum.inl i) = (d - xyMon N σ j) (Sum.inr (σ i))) ∧
            (∀ i, i ∉ insert j S →
              (d - xyMon N σ j) (Sum.inl i) = 0 ∧
              (d - xyMon N σ j) (Sum.inr (σ i)) = 0)) := by
        intro hle' ⟨hdiag', hzero'⟩
        apply hA
        refine ⟨fun i hi => ?_, fun i hi => ?_⟩
        · rcases Finset.mem_insert.mp hi with h_eq | hiS
          · rw [h_eq]
            have h1 := hdiag' j (Finset.mem_insert_self j S)
            simp [xyMon] at h1
            have h2 := hle' (Sum.inl j); simp [xyMon] at h2
            have h3 := hle' (Sum.inr (σ j)); simp [xyMon] at h3
            omega
          · have hij : i ≠ j := fun h => hj (h ▸ hiS)
            have := hdiag' i (Finset.mem_insert_of_mem hiS)
            simp [xyMon, hij, σ.injective.ne hij] at this
            exact this
        · rw [Finset.mem_insert, not_or] at hi
          have := hzero' i (by rw [Finset.mem_insert, not_or]; exact hi)
          simp [xyMon, hi.1, σ.injective.ne hi.1] at this
          exact this
      rw [if_neg hA]
      by_cases hle' : xyMon N σ j ≤ d
      · rw [if_pos hle', if_neg (this hle')]; ring
      · rw [if_neg hle']; ring

-- Induction combining all factors
private theorem prod_one_sub_mul_partialTarget (σ : Equiv.Perm (Fin N)) (S : Finset (Fin N)) :
    (∏ j ∈ S,
      (1 - MvPowerSeries.X (Sum.inl j) * MvPowerSeries.X (Sum.inr (σ j)) :
        MvPowerSeries (CauchyVars N) k)) *
    partialTarget N k σ S = partialTarget N k σ ∅ := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, mul_assoc, mul_left_comm,
        one_sub_mul_partialTarget N k σ s a ha, ih]

private theorem partialTarget_empty_eq_one (σ : Equiv.Perm (Fin N)) :
    partialTarget N k σ ∅ = 1 := by
  apply MvPowerSeries.ext; intro d
  simp only [partialTarget_coeff, MvPowerSeries.coeff_one, Finset.notMem_empty,
    not_false_eq_true, forall_const, IsEmpty.forall_iff, true_and]
  congr 1
  apply propext
  constructor
  · intro ⟨_, h⟩; ext v; cases v with
    | inl j => exact (h j).1
    | inr i =>
      have := (h (σ⁻¹ i)).2
      rwa [Equiv.Perm.apply_inv_self] at this
  · intro h; subst h; exact ⟨fun _ => trivial, fun j => ⟨Finsupp.zero_apply, Finsupp.zero_apply⟩⟩

private theorem partialTarget_univ_eq (σ : Equiv.Perm (Fin N)) :
    partialTarget N k σ Finset.univ = cauchyProdTarget N k σ := by
  apply MvPowerSeries.ext; intro d
  simp only [partialTarget_coeff, Finset.mem_univ, true_implies, not_true_eq_false,
    IsEmpty.forall_iff, implies_true, and_true]
  rfl

private theorem prod_one_sub_mul_target_eq_one (σ : Equiv.Perm (Fin N)) :
    (∏ j : Fin N,
      (1 - MvPowerSeries.X (Sum.inl j) * MvPowerSeries.X (Sum.inr (σ j)) :
        MvPowerSeries (CauchyVars N) k)) *
    cauchyProdTarget N k σ = 1 := by
  have h1 := prod_one_sub_mul_partialTarget N k σ Finset.univ
  rw [partialTarget_empty_eq_one] at h1
  rwa [partialTarget_univ_eq] at h1

theorem cauchyProd_coeff_perm (σ : Equiv.Perm (Fin N))
    (d : CauchyVars N →₀ ℕ) :
    MvPowerSeries.coeff (R := k) d
      (∏ j : Fin N,
        MvPowerSeries.invOfUnit
          (1 - MvPowerSeries.X (Sum.inl j) * MvPowerSeries.X (Sum.inr (σ j)))
          1) =
    if (∀ j : Fin N, d (Sum.inl j) = d (Sum.inr (σ j))) then 1 else 0 := by
  have hF := prod_mul_prod_invOfUnit_eq_one N k σ
  have hG := prod_one_sub_mul_target_eq_one N k σ
  have hU := isUnit_prod_one_sub N k σ
  have heq : (∏ j : Fin N,
      MvPowerSeries.invOfUnit
        (1 - MvPowerSeries.X (Sum.inl j) * MvPowerSeries.X (Sum.inr (σ j)))
        1) = cauchyProdTarget N k σ :=
    hU.mul_left_cancel (by rw [hF, hG])
  simp only [heq]; rfl

theorem cauchyRHS_coeff_diag [CharZero k]
    (α : Fin N → ℕ) (hα : Function.Injective α) :
    MvPowerSeries.coeff (R := k) (diagExponent N α) (cauchyRHS N k) = 1 := by
  simp only [cauchyRHS, map_sum]
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
    rw [MvPowerSeries.coeff_C_mul, cauchyProd_coeff_perm N k σ (diagExponent N α)]
    simp only [diagExponent_inl, diagExponent_inr]
  simp_rw [key]
  have honly_id : ∀ σ : Equiv.Perm (Fin N),
      (if ∀ j, α j = α (σ j) then (1 : k) else 0) =
      if σ = 1 then 1 else 0 := by
    intro σ
    split_ifs with h1 h2 h2
    · rfl
    · exfalso; apply h2; ext j; simp [Equiv.Perm.coe_one]
      exact congrArg Fin.val ((hα (h1 j)).symm)
    · exfalso; apply h1; intro j; simp [h2]
    · rfl
  simp_rw [honly_id]
  simp [Finset.sum_ite_eq', Finset.mem_univ]

end Etingof
