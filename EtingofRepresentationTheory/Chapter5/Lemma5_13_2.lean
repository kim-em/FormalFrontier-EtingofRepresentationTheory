import EtingofRepresentationTheory.Chapter5.Lemma5_13_1

/-!
# Lemma 5.13.2: Young Projector Vanishing for Distinct Partitions

If λ > μ in the dominance order on partitions of n, then
a_λ · ℂ[S_n] · b_μ = 0. The proof uses the pigeonhole principle: if λ > μ,
then for any Young tableaux of shapes λ and μ, some row of the λ-tableau
must contain two elements that belong to the same column of the μ-tableau.

## Mathlib correspondence

Requires Young symmetrizer infrastructure (Definition 5.12.1) and the dominance
order on partitions (defined here since Mathlib lacks it).
-/

open Etingof

/-- The dominance order on partitions: λ dominates μ if for all k,
the sum of the first k parts of λ (sorted descending) is ≥ the sum of
the first k parts of μ (sorted descending). -/
def Nat.Partition.Dominates {n : ℕ} (la mu : Nat.Partition n) : Prop :=
  ∀ k : ℕ, (mu.sortedParts.take k).sum ≤ (la.sortedParts.take k).sum

/-- Strict dominance: λ strictly dominates μ if λ dominates μ and λ ≠ μ. -/
def Nat.Partition.StrictDominates {n : ℕ} (la mu : Nat.Partition n) : Prop :=
  la.Dominates mu ∧ la ≠ mu

namespace Etingof

/-- A swap of two elements in the same row belongs to the row subgroup. -/
private theorem swap_mem_RowSubgroup {n : ℕ} {la : Nat.Partition n}
    {i j : Fin n} (hrow : rowOfPos la.sortedParts i.val = rowOfPos la.sortedParts j.val) :
    Equiv.swap i j ∈ RowSubgroup n la := by
  intro k
  simp only [Equiv.swap_apply_def]
  split_ifs with h1 h2
  · subst h1; exact hrow.symm
  · subst h2; exact hrow
  · rfl

/-- A swap of two elements in the same column belongs to the column subgroup. -/
private theorem swap_mem_ColumnSubgroup {n : ℕ} {mu : Nat.Partition n}
    {i j : Fin n} (hcol : colOfPos mu.sortedParts i.val = colOfPos mu.sortedParts j.val) :
    Equiv.swap i j ∈ ColumnSubgroup n mu := by
  intro k
  simp only [Equiv.swap_apply_def]
  split_ifs with h1 h2
  · subst h1; exact hcol.symm
  · subst h2; exact hcol
  · rfl

/-- Conjugation of a swap: σ⁻¹ * swap(i,j) * σ = swap(σ⁻¹ i, σ⁻¹ j). -/
private theorem conj_swap_eq {n : ℕ} (σ : Equiv.Perm (Fin n)) (i j : Fin n) :
    σ⁻¹ * Equiv.swap i j * σ = Equiv.swap (σ⁻¹ i) (σ⁻¹ j) := by
  ext k
  simp only [Equiv.Perm.coe_mul, Function.comp_apply]
  by_cases hki : k = σ.symm i
  · subst hki
    simp [Equiv.swap_apply_left, Equiv.apply_symm_apply]
  · by_cases hkj : k = σ.symm j
    · subst hkj
      simp [Equiv.swap_apply_right, Equiv.apply_symm_apply]
    · have hσki : σ k ≠ i := fun h => hki (by rw [← h]; simp)
      have hσkj : σ k ≠ j := fun h => hkj (by rw [← h]; simp)
      simp [Equiv.swap_apply_of_ne_of_ne hσki hσkj,
            Equiv.swap_apply_of_ne_of_ne hki hkj]

theorem pigeonhole_transposition (n : ℕ) (la mu : Nat.Partition n)
    (hdom : la.StrictDominates mu) (σ : Equiv.Perm (Fin n)) :
    ∃ (t : Equiv.Perm (Fin n)),
      t ∈ RowSubgroup n la ∧ σ⁻¹ * t * σ ∈ ColumnSubgroup n mu ∧
      Equiv.Perm.sign t = -1 := by
  -- Step 1: Suffices to find i ≠ j in same row of la with σ⁻¹(i), σ⁻¹(j) in same column of mu
  suffices ∃ i j : Fin n, i ≠ j ∧
      rowOfPos la.sortedParts i.val = rowOfPos la.sortedParts j.val ∧
      colOfPos mu.sortedParts (σ⁻¹ i).val = colOfPos mu.sortedParts (σ⁻¹ j).val by
    obtain ⟨i, j, hij, hrow, hcol⟩ := this
    exact ⟨Equiv.swap i j, swap_mem_RowSubgroup hrow,
      conj_swap_eq σ i j ▸ swap_mem_ColumnSubgroup hcol, Equiv.Perm.sign_swap hij⟩
  -- Step 2: Pigeonhole argument — if no such pair, derive contradiction with strict dominance
  sorry

/-- For a basis element of(σ): if λ strictly dominates μ, then a_λ · of(σ) · b_μ = 0. -/
theorem basis_vanishing (n : ℕ) (la mu : Nat.Partition n)
    (hdom : la.StrictDominates mu)
    (σ : Equiv.Perm (Fin n)) :
    RowSymmetrizer n la * MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) σ *
      ColumnAntisymmetrizer n mu = 0 := by
  obtain ⟨t, ht_row, hconj_col, ht_sign⟩ := pigeonhole_transposition n la mu hdom σ
  -- Abbreviations
  let of' := MonoidAlgebra.of ℂ (Equiv.Perm (Fin n))
  set a := RowSymmetrizer n la
  set b := ColumnAntisymmetrizer n mu
  set val := a * of' σ * b
  -- sign(σ⁻¹·t·σ) = sign(t) = -1
  have hconj_sign : (↑(↑(Equiv.Perm.sign (σ⁻¹ * t * σ)) : ℤ) : ℂ) = -1 := by
    simp [Equiv.Perm.sign_mul, ht_sign]
  -- Row absorption: a * of'(t) = a
  have hab : a * of' t = a := RowSymmetrizer_mul_of_row t ht_row
  -- Column absorption: of'(σ⁻¹tσ) * b = sign(σ⁻¹tσ) • b
  have hcol := of_col_mul_ColumnAntisymmetrizer (σ⁻¹ * t * σ) hconj_col
  -- Show val = (-1) • val via:
  --   val = a * of'(σ) * b
  --       = a * of'(t) * of'(σ) * b     [hab.symm applied to a]
  --       = a * of'(t*σ) * b             [map_mul]
  --       = a * of'(σ*(σ⁻¹*t*σ)) * b    [group identity]
  --       = a * of'(σ) * of'(σ⁻¹*t*σ) * b [map_mul]
  --       = a * of'(σ) * (sign(σ⁻¹tσ) • b) [column absorption]
  --       = (-1) • val                    [scalar out]
  have hval_neg : val = (-1 : ℂ) • val := by
    have step : a * of' σ = a * of' σ * of' (σ⁻¹ * t * σ) := by
      conv_lhs => rw [show a = a * of' t from hab.symm]
      rw [mul_assoc a (of' t) (of' σ), ← map_mul of' t σ,
          show t * σ = σ * (σ⁻¹ * t * σ) from by group,
          map_mul of' σ (σ⁻¹ * t * σ), ← mul_assoc]
    change a * of' σ * b = (-1 : ℂ) • (a * of' σ * b)
    conv_lhs => rw [step, mul_assoc (a * of' σ) (of' (σ⁻¹ * t * σ)) b, hcol]
    rw [mul_smul_comm, hconj_sign]
  -- val = -val implies val = 0 (char 0)
  rw [neg_one_smul] at hval_neg
  have hadd : val + val = 0 := by nth_rw 1 [hval_neg]; exact neg_add_cancel val
  have h2 : (2 : ℂ) • val = 0 := by rwa [two_smul]
  exact (smul_eq_zero.mp h2).resolve_left (by norm_num)

/-- If λ strictly dominates μ in the dominance order, then a_λ · x · b_μ = 0
for all x ∈ ℂ[S_n]. (Etingof Lemma 5.13.2) -/
theorem Lemma5_13_2
    (n : ℕ) (la mu : Nat.Partition n)
    (hdom : la.StrictDominates mu)
    (x : MonoidAlgebra ℂ (Equiv.Perm (Fin n))) :
    RowSymmetrizer n la * x * ColumnAntisymmetrizer n mu = 0 := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy =>
    rw [mul_add, add_mul, hx, hy, add_zero]
  | single g c =>
    have h : (Finsupp.single g c : MonoidAlgebra ℂ (Equiv.Perm (Fin n))) =
        c • MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) g := by
      simp [MonoidAlgebra.of_apply, mul_one]
    rw [h, mul_smul_comm, smul_mul_assoc, basis_vanishing n la mu hdom g, smul_zero]

end Etingof
