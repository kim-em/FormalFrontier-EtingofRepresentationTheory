import Mathlib
import EtingofRepresentationTheory.Chapter5.TabloidModule

/-!
# Specht Module Dimension Theorem

This file proves `finrank_spechtModule_eq_card_syt'`: dim V_λ = |SYT(λ)|,
combining:
- `finrank_spechtModule_ge_card_syt` (from TabloidModule.lean): dim V_λ ≥ |SYT(λ)|
- `finrank_spechtModule_le_card_syt` (proved here): dim V_λ ≤ |SYT(λ)|

The ≤ direction uses the tabloid-level straightening theorem
(`generalizedPolytabloidTab_mem_span_polytabloidTab`), which says every
generalized polytabloidTab lies in the ℂ-span of standard polytabloidTabs.
This implies the image ψ(V_λ) ⊆ span{polytabloidTab(T)}, giving the
dimension bound via injectivity of ψ on V_λ.

## Main results

* `Etingof.generalizedPolytabloidTab_mem_span_polytabloidTab` — straightening (2 sorries)
* `Etingof.finrank_spechtModule_le_card_syt` — dim V_λ ≤ |SYT(λ)|
* `Etingof.finrank_spechtModule_eq_card_syt'` — dim V_λ = |SYT(λ)|

## References

* James, "The Representation Theory of the Symmetric Groups", Chapter 7-8
* Fulton, "Young Tableaux", Chapter 7
-/

namespace Etingof

noncomputable section

variable {n : ℕ} {la : Nat.Partition n}

/-! ### Tabloid-level straightening theorem

The straightening theorem: every generalized polytabloidTab ψ_σ lies in the
ℂ-span of the standard polytabloidTabs {e_T : T ∈ SYT(λ)}.

The proof proceeds in two stages:
1. **Column standardization**: Reduce to column-standard σ using Q_λ-equivariance.
   For any σ, there exists q₀ ∈ Q_λ such that q₀σ is column-standard, and
   ψ_σ = sign(q₀)·ψ_{q₀σ} by `generalizedPolytabloidTab_col_mul`.
2. **Column-standard straightening**: For column-standard σ, show ψ_σ ∈ span{e_T}
   using the tabloid-level Garnir identity (`garnirAnnihilate_tabloid`) and
   well-founded induction on the dominance order. This is the core mathematical
   content (James Ch. 7-8, Fulton Ch. 7).
-/

/-- swap(p₁, p₂) preserves columns when p₁ and p₂ are in the same column. -/
private theorem swap_mem_columnSubgroup (p₁ p₂ : Fin n)
    (hcol : colOfPos la.sortedParts p₁.val = colOfPos la.sortedParts p₂.val) :
    Equiv.swap p₁ p₂ ∈ ColumnSubgroup n la := by
  intro k
  simp only [Equiv.swap_apply_def]
  split_ifs with h1 h2
  · subst h1; exact hcol.symm
  · subst h2; exact hcol
  · rfl

/-- Swapping a column inversion strictly decreases the column inversion count.

The proof constructs an injection g from "after-inversion pairs" into
"before-inversion pairs minus (p₁,p₂)". The key insight: for most pairs the
identity works; the only remapping needed is (a,p₁) ↦ (a,p₂) when
σ⁻¹(a) is between σ⁻¹(p₂) and σ⁻¹(p₁), and (p₂,b) ↦ (p₁,b) when
σ⁻¹(b) is between σ⁻¹(p₂) and σ⁻¹(p₁). -/
private theorem columnInvCount'_swap_lt (σ : Equiv.Perm (Fin n))
    (p₁ p₂ : Fin n)
    (hcol : colOfPos la.sortedParts p₁.val = colOfPos la.sortedParts p₂.val)
    (hrow : rowOfPos la.sortedParts p₁.val < rowOfPos la.sortedParts p₂.val)
    (hinv : σ.symm p₂ < σ.symm p₁)
    (hne : p₁ ≠ p₂) :
    columnInvCount' n la (Equiv.swap p₁ p₂ * σ) < columnInvCount' n la σ := by
  unfold columnInvCount'
  set parts := la.sortedParts
  have hsymm : ∀ x, (Equiv.swap p₁ p₂ * σ).symm x = σ.symm (Equiv.swap p₁ p₂ x) := by
    intro x; change (Equiv.swap p₁ p₂ * σ)⁻¹ x = σ⁻¹ (Equiv.swap p₁ p₂ x)
    rw [mul_inv_rev]; simp [Equiv.Perm.mul_apply]
  let g : Fin n × Fin n → Fin n × Fin n := fun ⟨a, b⟩ =>
    if b = p₁ ∧ σ.symm a < σ.symm p₁ then (a, p₂)
    else if a = p₂ ∧ σ.symm p₂ < σ.symm b then (p₁, b)
    else (a, b)
  let isInv : Equiv.Perm (Fin n) → Fin n × Fin n → Prop := fun τ ⟨a, b⟩ =>
    colOfPos parts a.val = colOfPos parts b.val ∧
    rowOfPos parts a.val < rowOfPos parts b.val ∧ τ.symm b < τ.symm a
  have hp : (p₁, p₂) ∈ Finset.univ.filter (fun pp => isInv σ pp) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcol, hrow, hinv⟩
  suffices h_le : (Finset.univ.filter (fun pp => isInv (Equiv.swap p₁ p₂ * σ) pp)).card ≤
      ((Finset.univ.filter (fun pp => isInv σ pp)).erase (p₁, p₂)).card by
    exact Nat.lt_of_le_of_lt h_le (Finset.card_erase_lt_of_mem hp)
  apply Finset.card_le_card_of_injOn g
  · -- MapsTo: g maps after-inversions into before-inversions \ {(p₁,p₂)}
    intro ⟨a, b⟩ hmem
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    obtain ⟨hcol_ab, hrow_ab, hinv_ab⟩ := hmem
    rw [hsymm, hsymm] at hinv_ab
    show g (a, b) ∈ _
    simp only [g]
    split_ifs with h1 h2
    · -- Branch 1: b = p₁, σ.symm a < σ.symm p₁ → g(a,b) = (a, p₂)
      obtain ⟨hbeq1, ha_lt⟩ := h1
      rw [eq_comm] at hbeq1; subst hbeq1
      have ha_ne_p1 : a ≠ p₁ := by intro h; rw [h] at ha_lt; exact absurd ha_lt (lt_irrefl _)
      have ha_ne_p2 : a ≠ p₂ := by
        intro h; rw [h] at hrow_ab; exact absurd (lt_trans hrow_ab hrow) (lt_irrefl _)
      rw [Equiv.swap_apply_left,
          Equiv.swap_apply_of_ne_of_ne ha_ne_p1 ha_ne_p2] at hinv_ab
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
      · exact fun heq => ha_ne_p1 (Prod.ext_iff.mp heq).1
      · exact ⟨hcol_ab.trans hcol, lt_trans hrow_ab hrow, hinv_ab⟩
    · -- Branch 2: a = p₂, σ.symm p₂ < σ.symm b → g(a,b) = (p₁, b)
      obtain ⟨haeq2, hb_gt⟩ := h2
      rw [eq_comm] at haeq2; subst haeq2
      have hb_ne_p2 : b ≠ p₂ := by intro h; rw [h] at hrow_ab; exact absurd hrow_ab (lt_irrefl _)
      have hb_ne_p1 : b ≠ p₁ := by
        intro h; rw [h] at hrow_ab; exact absurd (lt_trans hrow hrow_ab) (lt_irrefl _)
      rw [Equiv.swap_apply_of_ne_of_ne hb_ne_p1 hb_ne_p2,
          Equiv.swap_apply_right] at hinv_ab
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
      · exact fun heq => hb_ne_p2 (Prod.ext_iff.mp heq).2
      · exact ⟨hcol.trans hcol_ab, lt_trans hrow hrow_ab, hinv_ab⟩
    · -- Branch 3: identity → g(a,b) = (a, b)
      push_neg at h1 h2
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
      · intro heq; obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp heq
        rw [Equiv.swap_apply_right, Equiv.swap_apply_left] at hinv_ab
        exact absurd hinv_ab (Nat.not_lt.mpr hinv.le)
      · refine ⟨hcol_ab, hrow_ab, ?_⟩
        by_cases ha1 : a = p₁
        · rw [eq_comm] at ha1; subst ha1
          have hb_ne_p1 : b ≠ p₁ := by
            intro h; rw [h] at hrow_ab; exact absurd hrow_ab (lt_irrefl _)
          by_cases hb2 : b = p₂
          · rw [eq_comm] at hb2; subst hb2
            rw [Equiv.swap_apply_right, Equiv.swap_apply_left] at hinv_ab
            exact absurd hinv_ab (Nat.not_lt.mpr hinv.le)
          · rw [Equiv.swap_apply_left,
                Equiv.swap_apply_of_ne_of_ne hb_ne_p1 hb2] at hinv_ab
            exact lt_trans hinv_ab hinv
        · by_cases ha2 : a = p₂
          · rw [eq_comm] at ha2; subst ha2
            have hb_ne_p2 : b ≠ p₂ := by
              intro h; rw [h] at hrow_ab; exact absurd hrow_ab (lt_irrefl _)
            have hb_ne_p1 : b ≠ p₁ := by
              intro h; rw [h] at hrow_ab; exact absurd (lt_trans hrow hrow_ab) (lt_irrefl _)
            rw [Equiv.swap_apply_of_ne_of_ne hb_ne_p1 hb_ne_p2,
                Equiv.swap_apply_right] at hinv_ab
            exact lt_of_le_of_ne (h2 rfl) (fun h => hb_ne_p2 (σ.symm.injective h))
          · rw [Equiv.swap_apply_of_ne_of_ne ha1 ha2] at hinv_ab
            by_cases hb1 : b = p₁
            · rw [eq_comm] at hb1; subst hb1
              rw [Equiv.swap_apply_left] at hinv_ab
              exact lt_of_le_of_ne (h1 rfl) (fun h => ha1 (σ.symm.injective h.symm))
            · by_cases hb2 : b = p₂
              · rw [eq_comm] at hb2; subst hb2
                rw [Equiv.swap_apply_right] at hinv_ab
                exact lt_trans hinv hinv_ab
              · rwa [Equiv.swap_apply_of_ne_of_ne hb1 hb2] at hinv_ab
  · -- InjOn: g is injective on after-inversions
    intro ⟨a₁, b₁⟩ hmem₁ ⟨a₂, b₂⟩ hmem₂ heq
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hmem₁ hmem₂
    show (a₁, b₁) = (a₂, b₂)
    simp only [g] at heq
    by_cases h1a : b₁ = p₁ ∧ σ.symm a₁ < σ.symm p₁
    · -- Pair 1 in branch 1: g(a₁,b₁) = (a₁, p₂)
      simp only [h1a, and_self, ↓reduceIte] at heq
      by_cases h1b : b₂ = p₁ ∧ σ.symm a₂ < σ.symm p₁
      · -- (1,1)
        simp only [h1b, and_self, ↓reduceIte] at heq
        have ha : a₁ = a₂ := congr_arg Prod.fst heq
        subst ha; exact Prod.ext rfl (h1a.1.trans h1b.1.symm)
      · simp only [h1b, ↓reduceIte] at heq
        by_cases h2b : a₂ = p₂ ∧ σ.symm p₂ < σ.symm b₂
        · -- (1,2)
          simp only [h2b, and_self, ↓reduceIte] at heq
          exfalso
          have ha : a₁ = p₁ := congr_arg Prod.fst heq
          subst ha; exact absurd h1a.2 (lt_irrefl _)
        · -- (1,3)
          simp only [h2b, ↓reduceIte] at heq
          exfalso
          have ha : a₁ = a₂ := congr_arg Prod.fst heq
          have hb : p₂ = b₂ := congr_arg Prod.snd heq
          subst ha; subst hb
          have ha_ne_p1 : a₁ ≠ p₁ := by
            intro h; subst h; exact absurd h1a.2 (lt_irrefl _)
          have ha_ne_p2 : a₁ ≠ p₂ := by
            intro h; subst h; exact absurd hmem₂.2.1 (lt_irrefl _)
          have hinv₂ := hmem₂.2.2
          rw [hsymm, hsymm] at hinv₂
          rw [Equiv.swap_apply_right,
              Equiv.swap_apply_of_ne_of_ne ha_ne_p1 ha_ne_p2] at hinv₂
          exact absurd (lt_trans h1a.2 hinv₂) (lt_irrefl _)
    · simp only [h1a, ↓reduceIte] at heq
      by_cases h2a : a₁ = p₂ ∧ σ.symm p₂ < σ.symm b₁
      · -- Pair 1 in branch 2: g(a₁,b₁) = (p₁, b₁)
        simp only [h2a, and_self, ↓reduceIte] at heq
        by_cases h1b : b₂ = p₁ ∧ σ.symm a₂ < σ.symm p₁
        · -- (2,1)
          simp only [h1b, and_self, ↓reduceIte] at heq
          exfalso
          have ha : p₁ = a₂ := congr_arg Prod.fst heq
          subst ha; exact absurd h1b.2 (lt_irrefl _)
        · simp only [h1b, ↓reduceIte] at heq
          by_cases h2b : a₂ = p₂ ∧ σ.symm p₂ < σ.symm b₂
          · -- (2,2)
            simp only [h2b, and_self, ↓reduceIte] at heq
            have hb : b₁ = b₂ := congr_arg Prod.snd heq
            subst hb; exact Prod.ext (h2a.1.trans h2b.1.symm) rfl
          · -- (2,3)
            simp only [h2b, ↓reduceIte] at heq
            exfalso
            have ha : p₁ = a₂ := congr_arg Prod.fst heq
            have hb : b₁ = b₂ := congr_arg Prod.snd heq
            subst ha; subst hb
            have hb_ne_p1 : b₁ ≠ p₁ := by
              intro h; subst h; exact absurd hmem₂.2.1 (lt_irrefl _)
            have hb_ne_p2 : b₁ ≠ p₂ := by
              intro h; subst h; exact absurd h2a.2 (lt_irrefl _)
            have hinv₂ := hmem₂.2.2
            rw [hsymm, hsymm] at hinv₂
            rw [Equiv.swap_apply_of_ne_of_ne hb_ne_p1 hb_ne_p2,
                Equiv.swap_apply_left] at hinv₂
            exact absurd (lt_trans hinv₂ h2a.2) (lt_irrefl _)
      · -- Pair 1 in branch 3: g(a₁,b₁) = (a₁, b₁)
        simp only [h2a, ↓reduceIte] at heq
        by_cases h1b : b₂ = p₁ ∧ σ.symm a₂ < σ.symm p₁
        · -- (3,1)
          simp only [h1b, and_self, ↓reduceIte] at heq
          exfalso
          have ha : a₁ = a₂ := congr_arg Prod.fst heq
          have hb : b₁ = p₂ := congr_arg Prod.snd heq
          subst ha; rw [eq_comm] at hb; subst hb
          have ha_ne_p1 : a₁ ≠ p₁ := by
            intro h; subst h; exact absurd h1b.2 (lt_irrefl _)
          have ha_ne_p2 : a₁ ≠ p₂ := by
            intro h; subst h; exact absurd hmem₁.2.1 (lt_irrefl _)
          have hinv₁' := hmem₁.2.2
          rw [hsymm, hsymm] at hinv₁'
          rw [Equiv.swap_apply_right,
              Equiv.swap_apply_of_ne_of_ne ha_ne_p1 ha_ne_p2] at hinv₁'
          exact absurd (lt_trans h1b.2 hinv₁') (lt_irrefl _)
        · simp only [h1b, ↓reduceIte] at heq
          by_cases h2b : a₂ = p₂ ∧ σ.symm p₂ < σ.symm b₂
          · -- (3,2)
            simp only [h2b, and_self, ↓reduceIte] at heq
            exfalso
            have ha : a₁ = p₁ := congr_arg Prod.fst heq
            have hb : b₁ = b₂ := congr_arg Prod.snd heq
            rw [eq_comm] at ha; subst ha; subst hb
            have hb_ne_p1 : b₁ ≠ p₁ := by
              intro h; subst h; exact absurd hmem₁.2.1 (lt_irrefl _)
            have hb_ne_p2 : b₁ ≠ p₂ := by
              intro h; subst h; exact absurd h2b.2 (lt_irrefl _)
            have hinv₁' := hmem₁.2.2
            rw [hsymm, hsymm] at hinv₁'
            rw [Equiv.swap_apply_of_ne_of_ne hb_ne_p1 hb_ne_p2,
                Equiv.swap_apply_left] at hinv₁'
            exact absurd (lt_trans hinv₁' h2b.2) (lt_irrefl _)
          · -- (3,3)
            simp only [h2b, ↓reduceIte] at heq
            exact heq

/-- For any permutation σ, there exists q₀ ∈ Q_λ such that q₀ * σ is
column-standard (entries increase down each column). The column-sorting
permutation permutes entries within each column, hence lies in Q_λ. -/
private theorem exists_column_standard_mul (σ : Equiv.Perm (Fin n)) :
    ∃ q₀ ∈ ColumnSubgroup n la, isColumnStandard' n la (q₀ * σ) := by
  -- Strong induction on the column inversion count
  suffices ∀ (τ : Equiv.Perm (Fin n)) (m : ℕ), m = columnInvCount' n la τ →
      ∃ q₀ ∈ ColumnSubgroup n la, isColumnStandard' n la (q₀ * τ) from
    this σ _ rfl
  intro τ m
  induction m using Nat.strongRecOn generalizing τ with
  | _ m ih =>
  intro hm
  by_cases hcs : isColumnStandard' n la τ
  · exact ⟨1, (ColumnSubgroup n la).one_mem, by rwa [one_mul]⟩
  · -- Find a column inversion and swap it
    obtain ⟨p₁, p₂, hcol_inv, hrow_inv, hinv_inv⟩ := exists_column_inversion n la τ hcs
    have hne : p₁ ≠ p₂ := by intro h; rw [h] at hrow_inv; exact Nat.lt_irrefl _ hrow_inv
    have hswap_mem : Equiv.swap p₁ p₂ ∈ ColumnSubgroup n la :=
      swap_mem_columnSubgroup p₁ p₂ hcol_inv
    have hcount : columnInvCount' n la (Equiv.swap p₁ p₂ * τ) < m := by
      rw [hm]; exact columnInvCount'_swap_lt τ p₁ p₂ hcol_inv hrow_inv hinv_inv hne
    obtain ⟨q₀, hq₀, hcs'⟩ := ih _ hcount (Equiv.swap p₁ p₂ * τ) rfl
    exact ⟨q₀ * Equiv.swap p₁ p₂,
      (ColumnSubgroup n la).mul_mem hq₀ hswap_mem,
      by rwa [mul_assoc]⟩

/-! ### Row inversion count infrastructure

The row inversion count measures how far a column-standard permutation is from
being a standard Young tableau permutation. It counts pairs of positions in the
same row where column order and entry order disagree.
-/

/-- The number of "row inversions" in the filling defined by σ: pairs (p₁, p₂)
in the same row with col(p₁) < col(p₂) but σ⁻¹(p₁) > σ⁻¹(p₂). -/
private def rowInvCount' (σ : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.filter fun pp : Fin n × Fin n =>
    rowOfPos la.sortedParts pp.1.val = rowOfPos la.sortedParts pp.2.val ∧
    colOfPos la.sortedParts pp.1.val < colOfPos la.sortedParts pp.2.val ∧
    σ.symm pp.2 < σ.symm pp.1).card

/-- A filling is row-standard if all rows are increasing left-to-right. -/
private def isRowStandard' (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ p₁ p₂ : Fin n,
    rowOfPos la.sortedParts p₁.val = rowOfPos la.sortedParts p₂.val →
    colOfPos la.sortedParts p₁.val < colOfPos la.sortedParts p₂.val →
    σ.symm p₁ < σ.symm p₂

/-- Row inversion count is 0 iff the filling is row-standard. -/
private theorem rowInvCount'_eq_zero_iff (σ : Equiv.Perm (Fin n)) :
    rowInvCount' (la := la) σ = 0 ↔ isRowStandard' (la := la) σ := by
  constructor
  · intro h
    rw [rowInvCount', Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h
    intro p₁ p₂ hrow hcol
    by_contra hlt
    push_neg at hlt
    have hne : p₁ ≠ p₂ := by intro heq; rw [heq] at hcol; exact Nat.lt_irrefl _ hcol
    have hne' : σ.symm p₁ ≠ σ.symm p₂ := σ.symm.injective.ne hne
    have hlt' : σ.symm p₂ < σ.symm p₁ := lt_of_le_of_ne hlt hne'.symm
    exact absurd ⟨hrow, hcol, hlt'⟩ (h (Finset.mem_univ (p₁, p₂)))
  · intro h
    rw [rowInvCount', Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro ⟨p₁, p₂⟩ _
    simp only [not_and]
    intro hrow hcol hinv
    exact absurd hinv (Nat.not_lt.mpr (Nat.le_of_lt (h p₁ p₂ hrow hcol)))

/-- Two row-standard permutations with the same tabloid are equal.
Within each row, both arrange the same set of entries in increasing order,
so they must assign entries identically. -/
private theorem eq_of_rowStandard_of_toTabloid_eq
    (σ₁ σ₂ : Equiv.Perm (Fin n))
    (h₁ : isRowStandard' (la := la) σ₁)
    (h₂ : isRowStandard' (la := la) σ₂)
    (ht : toTabloid n la σ₁ = toTabloid n la σ₂) :
    σ₁ = σ₂ := by
  by_contra hne
  -- Find the minimal entry where σ₁ and σ₂ disagree
  have hne' : ∃ k : Fin n, σ₁ k ≠ σ₂ k := by
    by_contra hall; push_neg at hall; exact hne (Equiv.ext hall)
  set S := Finset.univ.filter (fun k : Fin n => σ₁ k ≠ σ₂ k) with hS_def
  have hS_nonempty : S.Nonempty :=
    let ⟨k, hk⟩ := hne'; ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ k, hk⟩⟩
  set k := S.min' hS_nonempty
  have hk_mem : k ∈ S := Finset.min'_mem S hS_nonempty
  have hk_ne : σ₁ k ≠ σ₂ k := (Finset.mem_filter.mp hk_mem).2
  have hmin : ∀ j : Fin n, σ₁ j ≠ σ₂ j → k ≤ j :=
    fun j hj => Finset.min'_le S j (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩)
  -- Same row by same tabloid
  have hrow_assign := (toTabloid_eq_iff_rowAssign σ₁ σ₂).mp ht
  have hrow : rowOfPos la.sortedParts (σ₁ k).val = rowOfPos la.sortedParts (σ₂ k).val :=
    hrow_assign k
  -- Different positions in same row → different columns
  have hsum : la.sortedParts.sum = n := sortedParts_sum_eq n la
  have hcol_ne : colOfPos la.sortedParts (σ₁ k).val ≠ colOfPos la.sortedParts (σ₂ k).val := by
    intro heq
    exact hk_ne (Fin.ext (rowOfPos_colOfPos_injective la.sortedParts (σ₁ k).val (σ₂ k).val
      (by omega) (by omega) hrow heq))
  -- Either col(σ₁ k) < col(σ₂ k) or col(σ₂ k) < col(σ₁ k)
  rcases Nat.lt_or_gt_of_ne hcol_ne with hcol | hcol
  · -- Case: col(σ₁ k) < col(σ₂ k). Row-standard for σ₂ gives σ₂⁻¹(σ₁ k) < k.
    have hlt : σ₂.symm (σ₁ k) < k := by
      have := h₂ (σ₁ k) (σ₂ k) hrow hcol
      rwa [Equiv.symm_apply_apply] at this
    -- Let j = σ₂⁻¹(σ₁ k). By minimality σ₁ j = σ₂ j.
    set j := σ₂.symm (σ₁ k)
    have hjeq : σ₁ j = σ₂ j := by
      by_contra hjne; exact absurd (hmin j hjne) (not_le.mpr hlt)
    -- But σ₂ j = σ₁ k, so σ₁ j = σ₁ k, so j = k, contradicting j < k.
    have : σ₂ j = σ₁ k := Equiv.apply_symm_apply σ₂ (σ₁ k)
    have : σ₁ j = σ₁ k := hjeq.trans this
    exact absurd (σ₁.injective this) (Fin.ne_of_lt hlt)
  · -- Case: col(σ₂ k) < col(σ₁ k). Row-standard for σ₁ gives σ₁⁻¹(σ₂ k) < k.
    have hlt : σ₁.symm (σ₂ k) < k := by
      have := h₁ (σ₂ k) (σ₁ k) hrow.symm hcol
      rwa [Equiv.symm_apply_apply] at this
    set j := σ₁.symm (σ₂ k)
    have hjeq : σ₁ j = σ₂ j := by
      by_contra hjne; exact absurd (hmin j hjne) (not_le.mpr hlt)
    have : σ₁ j = σ₂ k := Equiv.apply_symm_apply σ₁ (σ₂ k)
    have : σ₂ j = σ₂ k := hjeq.symm.trans this
    exact absurd (σ₂.injective this) (Fin.ne_of_lt hlt)

/-- A column-standard, row-standard permutation equals sytPerm T for some SYT T. -/
private theorem column_row_standard_is_syt
    (σ : Equiv.Perm (Fin n))
    (hcs : isColumnStandard' n la σ)
    (hrs : isRowStandard' (la := la) σ) :
    ∃ T : StandardYoungTableau n la, σ = sytPerm n la T := by
  obtain ⟨T, p, hp, hσ⟩ := column_standard_coset_has_syt' n la σ hcs
  refine ⟨T, ?_⟩
  -- σ = p * sytPerm T with p ∈ P_λ. Since [σ] = [σ_T] and both are row-standard,
  -- σ = sytPerm T by uniqueness.
  have hσT_rs : isRowStandard' (la := la) (sytPerm n la T) := by
    intro p₁ p₂ hrow hcol
    -- (sytPerm T).symm p = T.val (canonicalFilling p)
    have hsymm : ∀ p, (sytPerm n la T).symm p =
        (Equiv.ofBijective T.val T.prop.1) ((canonicalFilling n la) p) := by
      intro p; simp only [sytPerm, Equiv.symm_trans_apply, Equiv.symm_symm]
    rw [hsymm, hsymm]
    -- canonicalFilling maps positions to cells, preserving row/col
    set c₁ := (canonicalFilling n la) p₁
    set c₂ := (canonicalFilling n la) p₂
    -- Same row and column ordering for cells
    have hrow' : c₁.val.1 = c₂.val.1 := hrow
    have hcol' : c₁.val.2 < c₂.val.2 := hcol
    -- ofBijective T just applies T.val
    simp only [Equiv.ofBijective_apply]
    -- Apply SYT row-increasing property
    exact T.prop.2.1 c₁ c₂ hrow' hcol'
  have ht_eq : toTabloid n la σ = toTabloid n la (sytPerm n la T) := by
    rw [toTabloid_eq_iff, hσ, mul_assoc, mul_inv_cancel, mul_one]
    exact hp
  exact eq_of_rowStandard_of_toTabloid_eq σ (sytPerm n la T) hrs hσT_rs ht_eq

/-! ### Garnir set

The Garnir set for a row inversion pair (p₁, p₂) consists of:
- All positions in column(p₁) at rows ≥ row(p₁)
- All positions in column(p₂) at rows ≤ row(p₂)

Since p₁ and p₂ are in the same row, the set spans two columns and
contains enough positions to force cross-column permutations.

Reference: James, "The Representation Theory of the Symmetric Groups", Chapter 7.
-/

/-- The Garnir set for positions p₁, p₂ in a Young diagram. Given positions in the same
row with col(p₁) < col(p₂), this is the set of positions in column(p₁) at or below
row(p₁,p₂) together with positions in column(p₂) at or above row(p₁,p₂).

This cross-column set ensures that non-identity G-supported permutations include
cross-column shuffles that are NOT in the row subgroup, which is essential for the
dominance argument in the Garnir straightening theorem. -/
private def garnirSet (p₁ p₂ : Fin n) : Finset (Fin n) :=
  let parts := la.sortedParts
  let r := rowOfPos parts p₁.val
  let j₁ := colOfPos parts p₁.val
  let j₂ := colOfPos parts p₂.val
  Finset.univ.filter fun p =>
    (colOfPos parts p.val = j₁ ∧ r ≤ rowOfPos parts p.val) ∨
    (colOfPos parts p.val = j₂ ∧ rowOfPos parts p.val ≤ r)

private theorem mem_garnirSet_left (p₁ p₂ : Fin n) :
    p₁ ∈ garnirSet (la := la) p₁ p₂ := by
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl ⟨rfl, ?_⟩⟩
  exact Nat.le_refl _

private theorem mem_garnirSet_right (p₁ p₂ : Fin n)
    (hrow : rowOfPos la.sortedParts p₁.val = rowOfPos la.sortedParts p₂.val) :
    p₂ ∈ garnirSet (la := la) p₁ p₂ := by
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr ⟨rfl, ?_⟩⟩
  exact hrow ▸ Nat.le_refl _

/-! ### Garnir straightening step

The key technical result: for column-standard σ with row inversions,
ψ_σ can be expressed via Garnir relations in terms of generalized
polytabloidTabs with strictly fewer row inversions. This uses:
1. `garnirAnnihilate_tabloid` — the tabloid-level Garnir identity
2. Dominance analysis — Garnir permutations produce more dominant tabloids
3. Column re-standardization — reducing back to column-standard form

## Proof strategy

Given column-standard σ with rowInvCount' > 0:
1. Find a row inversion pair (p₁, p₂): same row, col(p₁) < col(p₂), σ⁻¹(p₁) > σ⁻¹(p₂).
2. Construct the proper Garnir set G spanning columns col(p₁) and col(p₂).
   G contains p₁ and p₂ (a row pair), enabling `garnirAnnihilate_tabloid`.
3. Apply the Garnir identity to each tabloid [q⁻¹σ] in ψ_σ's expansion:
     0 = Σ_w sign(w) · [w·q⁻¹·σ]   (for each q ∈ Q_λ)
4. Sum over q with sign(q) and exchange sum order to get:
     ψ_σ = -Σ_{w≠1} sign(w) · f_w(σ)
   where f_w(σ) = Σ_{q ∈ Q_λ} sign(q) · [w·q⁻¹·σ] is a "twisted polytabloid"
   (column antisymmetrization of w·σ over the conjugated column subgroup wQ_λw⁻¹).
5. Show each twisted polytabloid f_w(σ) is in the span of {ψ_τ : τ column-standard,
   rowInvCount'(τ) < rowInvCount'(σ)}, using dominance theory.

## Sorry decomposition

The proof is decomposed into two sub-problems:
- `garnir_polytabloid_identity`: the algebraic identity from step 4
- `garnir_twisted_in_lower_span`: the combinatorial bound from step 5
-/

/-- When rowInvCount' > 0, there exists a row inversion pair: two positions
in the same row with increasing column but decreasing entry. -/
private lemma exists_row_inversion_pair (σ : Equiv.Perm (Fin n))
    (h : 0 < rowInvCount' (la := la) σ) :
    ∃ p₁ p₂ : Fin n,
      rowOfPos la.sortedParts p₁.val = rowOfPos la.sortedParts p₂.val ∧
      colOfPos la.sortedParts p₁.val < colOfPos la.sortedParts p₂.val ∧
      σ.symm p₂ < σ.symm p₁ := by
  rw [rowInvCount', Finset.card_pos] at h
  obtain ⟨⟨p₁, p₂⟩, hp⟩ := h
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
  exact ⟨p₁, p₂, hp⟩

/-- The "twisted polytabloid" f_w(σ): the column antisymmetrization of σ
with respect to a Garnir permutation w. When w = 1, this equals ψ_σ.
When w ≠ 1, this is a sum over the conjugated column subgroup wQ_λw⁻¹. -/
private noncomputable def twistedPolytabloid
    (w σ : Equiv.Perm (Fin n)) : TabloidRepresentation n la :=
  haveI : DecidablePred (· ∈ ColumnSubgroup n la) := Classical.decPred _
  ∑ q : ↥(ColumnSubgroup n la),
    ((↑(↑(Equiv.Perm.sign q.val) : ℤ) : ℂ) •
      Finsupp.single (toTabloid n la (w * q.val⁻¹ * σ)) 1)

/-- When w = 1, the twisted polytabloid equals the generalized polytabloid. -/
private theorem twistedPolytabloid_one (σ : Equiv.Perm (Fin n)) :
    twistedPolytabloid (la := la) 1 σ =
      generalizedPolytabloidTab (n := n) (la := la) σ := by
  simp [twistedPolytabloid, generalizedPolytabloidTab, one_mul]

/-- **Garnir polytabloid identity** (sub-sorry 1 of 2):
The Garnir identity, applied to each tabloid in ψ_σ's expansion and regrouped,
expresses ψ_σ as a negated sum of "twisted polytabloids":
  ψ_σ = -Σ_{w ≠ 1, w supported on G} sign(w) · f_w(σ)

This follows from `garnirAnnihilate_tabloid` by:
1. For each q ∈ Q_λ: Σ_w sign(w) · [w·q⁻¹·σ] = 0
2. Multiply by sign(q) and sum over q: Σ_q sign(q) Σ_w sign(w) · [wq⁻¹σ] = 0
3. Exchange sum order: Σ_w sign(w) · f_w(σ) = 0
4. Extract w=1 term: ψ_σ + Σ_{w≠1} sign(w) · f_w(σ) = 0

Difficulty: 5. Purely algebraic sum manipulation using `garnirAnnihilate_tabloid`. -/
private theorem garnir_polytabloid_identity
    (σ : Equiv.Perm (Fin n))
    (G : Finset (Fin n)) (t : Equiv.Perm (Fin n))
    (ht_row : t ∈ RowSubgroup n la) (ht_supp : ∀ x, x ∉ G → t x = x)
    (ht_sign : Equiv.Perm.sign t = -1) :
    generalizedPolytabloidTab (n := n) (la := la) σ =
      -(∑ w : {w : Equiv.Perm (Fin n) // (∀ x, x ∉ G → w x = x) ∧ w ≠ 1},
        ((↑(↑(Equiv.Perm.sign w.val) : ℤ) : ℂ) •
          twistedPolytabloid (la := la) w.val σ)) := by
  -- Type abbreviation for the subtype of G-supported permutations
  set S := { w : Equiv.Perm (Fin n) // ∀ x, x ∉ G → w x = x }
  -- Step 1: Each garnirAnnihilate_tabloid application gives a zero inner sum
  have h_garnir_q : ∀ q : ↥(ColumnSubgroup n la),
      ∑ w : S, ((↑(↑(Equiv.Perm.sign w.val) : ℤ) : ℂ) •
        Finsupp.single (toTabloid n la (w.val * (q.val⁻¹ * σ))) (1 : ℂ)) = 0 := by
    intro q
    exact garnirAnnihilate_tabloid (la := la) (q.val⁻¹ * σ) G t ht_row ht_supp ht_sign
  -- Step 2: The total alternating sum of twisted polytabloids is zero.
  have h_total : ∑ w : S, ((↑(↑(Equiv.Perm.sign w.val) : ℤ) : ℂ) •
      twistedPolytabloid (la := la) w.val σ) = 0 := by
    simp only [twistedPolytabloid, Finset.smul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro q _
    simp_rw [smul_comm (↑(↑(Equiv.Perm.sign _) : ℤ) : ℂ)
      (↑(↑(Equiv.Perm.sign q.val) : ℤ) : ℂ)]
    rw [← Finset.smul_sum]
    simp_rw [mul_assoc]
    rw [h_garnir_q q, smul_zero]
  -- Step 3: Split the sum via S ≃ Option T where T = {w // supp ∧ w ≠ 1}
  -- Equivalence between S and Option T
  set T := {w : Equiv.Perm (Fin n) // (∀ x, x ∉ G → w x = x) ∧ w ≠ 1} with hT_def
  let e : S ≃ Option T :=
    { toFun := fun s => if h : s.val = 1 then none else some ⟨s.val, s.property, h⟩
      invFun := fun o => o.casesOn ⟨1, fun _ _ => rfl⟩ (fun w => ⟨w.val, w.property.1⟩)
      left_inv := fun ⟨w, hw⟩ => by
        simp only
        split_ifs with h
        · exact Subtype.ext h.symm
        · rfl
      right_inv := fun o => by
        cases o with
        | none => simp
        | some w => simp [w.property.2] }
  -- Decompose the S-sum as Option-sum
  have h_sum_decomp : ∑ w : S, ((↑(↑(Equiv.Perm.sign w.val) : ℤ) : ℂ) •
        twistedPolytabloid (la := la) w.val σ) =
      generalizedPolytabloidTab (n := n) (la := la) σ +
      ∑ w : T, ((↑(↑(Equiv.Perm.sign w.val) : ℤ) : ℂ) •
        twistedPolytabloid (la := la) w.val σ) := by
    -- Reindex via e : S ≃ Option T
    rw [show ∑ w : S, ((↑(↑(Equiv.Perm.sign w.val) : ℤ) : ℂ) •
        twistedPolytabloid (la := la) w.val σ) =
        ∑ o : Option T, ((↑(↑(Equiv.Perm.sign ((e.symm o).val)) : ℤ) : ℂ) •
          twistedPolytabloid (la := la) (e.symm o).val σ) from
      (Equiv.sum_comp e.symm _).symm]
    rw [Fintype.sum_option]
    congr 1
    · -- The none term: e.symm none = ⟨1, _⟩
      show ((↑(↑(Equiv.Perm.sign (e.symm none).val) : ℤ) : ℂ) •
        twistedPolytabloid (la := la) (e.symm none).val σ) = _
      have : (e.symm none).val = 1 := rfl
      rw [this]; simp [twistedPolytabloid_one]
  rw [h_sum_decomp] at h_total
  exact eq_neg_of_add_eq_zero_left h_total

/-- When w ∈ Q_λ, the twisted polytabloid equals ψ_{wσ} = sign(w) · ψ_σ.
This is because the substitution q ↦ w⁻¹qw (conjugation) gives a bijection
on Q_λ that transforms the twisted sum into the standard polytabloid sum. -/
private theorem twistedPolytabloid_col_eq (w : Equiv.Perm (Fin n))
    (hw : w ∈ ColumnSubgroup n la) (σ : Equiv.Perm (Fin n)) :
    twistedPolytabloid (la := la) w σ =
      ((↑(↑(Equiv.Perm.sign w) : ℤ) : ℂ) •
        generalizedPolytabloidTab (n := n) (la := la) σ) := by
  -- f_w(σ) = Σ_q sign(q) · [w·q⁻¹·σ]
  -- Change variable: r = wqw⁻¹, so q = w⁻¹rw, q⁻¹ = w⁻¹r⁻¹w
  -- Then w·q⁻¹·σ = w·w⁻¹·r⁻¹·w·σ = r⁻¹·(wσ)
  -- sign(q) = sign(w⁻¹rw) = sign(r)
  -- So f_w(σ) = Σ_{r ∈ wQw⁻¹} sign(r) · [r⁻¹·(wσ)]
  -- Since w ∈ Q, wQw⁻¹ = Q, so f_w(σ) = ψ_{wσ}
  -- By generalizedPolytabloidTab_col_mul: ψ_{wσ} = sign(w) · ψ_σ
  -- Step 1: f_w(σ) = ψ_{wσ} by reindexing via conjugation q ↦ wqw⁻¹
  suffices h : twistedPolytabloid (la := la) w σ =
      generalizedPolytabloidTab (n := n) (la := la) (w * σ) by
    rw [h, generalizedPolytabloidTab_col_mul w hw σ]
  -- Step 2: Show the sums are equal by reindexing
  -- f_w(σ) = Σ_q sign(q) · [wq⁻¹σ] and ψ_{wσ} = Σ_q sign(q) · [q⁻¹wσ]
  -- Reindex ψ_{wσ} via conjugation φ : q ↦ wqw⁻¹ to get f_w(σ)
  classical
  simp only [twistedPolytabloid, generalizedPolytabloidTab]
  -- Conjugation bijection on Q_λ: q ↦ w * q * w⁻¹
  set φ : ↥(ColumnSubgroup n la) ≃ ↥(ColumnSubgroup n la) :=
    ⟨fun q => ⟨w * q.val * w⁻¹, (ColumnSubgroup n la).mul_mem
        ((ColumnSubgroup n la).mul_mem hw q.prop)
        ((ColumnSubgroup n la).inv_mem hw)⟩,
     fun q => ⟨w⁻¹ * q.val * w, (ColumnSubgroup n la).mul_mem
        ((ColumnSubgroup n la).mul_mem
          ((ColumnSubgroup n la).inv_mem hw) q.prop) hw⟩,
     fun ⟨q, _⟩ => Subtype.ext (by group),
     fun ⟨q, _⟩ => Subtype.ext (by group)⟩
  refine Fintype.sum_equiv φ _ _ (fun ⟨q, hq⟩ => ?_)
  -- φ q = w * q * w⁻¹, so (φ q)⁻¹ * (w * σ) = w * q⁻¹ * σ
  have hφ_val : (φ ⟨q, hq⟩ : ↥(ColumnSubgroup n la)).val = w * q * w⁻¹ := rfl
  simp only [hφ_val]
  congr 1
  · -- sign(q) = sign(w * q * w⁻¹)
    have hsign : Equiv.Perm.sign (w * q * w⁻¹) = Equiv.Perm.sign q := by
      rw [map_mul, map_mul, map_inv, mul_inv_cancel_comm]
    simp [hsign]
  · -- toTabloid (w * q⁻¹ * σ) = toTabloid ((w * q * w⁻¹)⁻¹ * (w * σ))
    congr 1
    group

/-- When w ∈ P_λ (row-preserving), the twisted polytabloid equals ψ_σ.
The sum is term-by-term equal: `[w * q⁻¹ * σ] = [q⁻¹ * σ]` because
`(w * q⁻¹ * σ) * (q⁻¹ * σ)⁻¹ = w ∈ P_λ` (tabloid equivalence is left
multiplication by P_λ). -/
private theorem twistedPolytabloid_row_eq (w : Equiv.Perm (Fin n))
    (hw : w ∈ RowSubgroup n la) (σ : Equiv.Perm (Fin n)) :
    twistedPolytabloid (la := la) w σ =
      generalizedPolytabloidTab (n := n) (la := la) σ := by
  classical
  simp only [twistedPolytabloid, generalizedPolytabloidTab]
  refine Finset.sum_congr rfl (fun ⟨q, hq⟩ _ => ?_)
  congr 2
  rw [toTabloid_eq_iff]
  have heq : (w * q⁻¹ * σ) * (q⁻¹ * σ)⁻¹ = w := by group
  rw [heq]; exact hw

/-- **Twisted polytabloid in lower span** (sub-sorry 2 of 2):
For column-standard σ with row inversion, each Garnir permutation w that is
**neither** column-preserving nor row-preserving produces a "twisted polytabloid"
f_w(σ) that lies in the span of
{ψ_τ : τ column-standard, rowInvCount'(τ) < rowInvCount'(σ)}.

Both exclusions are essential to avoid circularity:
- For w ∈ Q_λ, `twistedPolytabloid_col_eq` gives f_w(σ) = sign(w) · ψ_σ.
- For w ∈ P_λ, `twistedPolytabloid_row_eq` gives f_w(σ) = ψ_σ.
Proving ψ_σ is in the lower span from either special case would be circular.
The algebraic splitting of these cases is handled in `garnir_straightening_step`.

The proof requires:
1. Column-restandardize wσ: find q₀ ∈ Q_λ with q₀·w·σ column-standard.
2. Express f_w(σ) as a ℂ-combination of standard generalized polytabloids.
3. Use dominance theory to show the resulting tabloids are strictly more
   dominant, giving strictly fewer row inversions after restandardization.

Difficulty: 8. Combinatorial heart of the straightening theorem
(James Ch. 7-8 / Fulton Ch. 7). -/
private theorem garnir_twisted_in_lower_span
    (σ : Equiv.Perm (Fin n)) (hcs : isColumnStandard' n la σ)
    (hrp : 0 < rowInvCount' (la := la) σ)
    (G : Finset (Fin n))
    (w : Equiv.Perm (Fin n)) (hw_supp : ∀ x, x ∉ G → w x = x)
    (hw_ne : w ≠ 1) (hw_col : w ∉ ColumnSubgroup n la)
    (hw_row : w ∉ RowSubgroup n la) :
    twistedPolytabloid (la := la) w σ ∈
    Submodule.span ℂ (Set.range (fun τ : {τ : Equiv.Perm (Fin n) //
        isColumnStandard' n la τ ∧ rowInvCount' (la := la) τ < rowInvCount' (la := la) σ} =>
      generalizedPolytabloidTab (n := n) (la := la) τ.val)) := by
  sorry

set_option maxHeartbeats 1200000 in
-- The long proof involves many module-level rewrites over a large sum,
-- and the three-way case split pushes Lean's default heartbeat budget.
/-- **Garnir straightening step**:
For column-standard σ with positive row inversion count, the generalized
polytabloidTab ψ_σ lies in the ℂ-span of {ψ_{σ'} : σ' column-standard,
rowInvCount'(σ') < rowInvCount'(σ)}.

Proof: combine `garnir_polytabloid_identity` with `garnir_twisted_in_lower_span`.
The identity expresses ψ_σ as a negated sum of twisted polytabloids. We split
the sum `∑_{w ∈ T}` (T = non-identity permutations supported on G) into three
disjoint parts using `T ∩ P ∩ Q = ∅` (since P ∩ Q = {1}):
- **Q part** (w ∈ Q_λ): `f_w(σ) = sign(w)·ψ_σ` by `twistedPolytabloid_col_eq`,
  so `sign(w)·f_w(σ) = ψ_σ`. These k terms contribute k·ψ_σ.
- **P\\Q part** (w ∈ P_λ \\ Q_λ): `f_w(σ) = ψ_σ` by `twistedPolytabloid_row_eq`
  (tabloids are unchanged by left multiplication by P_λ). So `sign(w)·f_w(σ) =
  sign(w)·ψ_σ`. By a sign-cancellation argument (involution w ↦ w·swap on
  S_G ∩ P_λ), `∑_{w ∈ (S_G ∩ P_λ) \\ {1}} sign(w) = -1`, contributing `-ψ_σ`.
- **Neither part** (w ∉ P_λ ∪ Q_λ): `sign(w)·f_w(σ) ∈ L` by
  `garnir_twisted_in_lower_span`.
Rearranging: `k·ψ_σ = -(neither sum) ∈ L`. If k ≥ 1, divide by k to get ψ_σ ∈ L.
If k = 0 (which happens iff row(p₁) = 0 and col(p₁) has length 1), a separate
swap-based argument is needed — this case is deferred as a sorry. -/
private theorem garnir_straightening_step
    (σ : Equiv.Perm (Fin n)) (hcs : isColumnStandard' n la σ)
    (hrp : 0 < rowInvCount' (la := la) σ) :
    generalizedPolytabloidTab (n := n) (la := la) σ ∈
      Submodule.span ℂ (Set.range (fun τ : {τ : Equiv.Perm (Fin n) //
          isColumnStandard' n la τ ∧ rowInvCount' (la := la) τ < rowInvCount' (la := la) σ} =>
        generalizedPolytabloidTab (n := n) (la := la) τ.val)) := by
  -- Step 1: Find the row inversion pair
  obtain ⟨p₁, p₂, hrow_eq, hcol_lt, hinv⟩ := exists_row_inversion_pair σ hrp
  -- Step 2: Use the proper Garnir set spanning columns col(p₁) and col(p₂),
  -- with t = swap(p₁, p₂) as row transposition
  have hne : p₁ ≠ p₂ := by intro h; rw [h] at hcol_lt; exact Nat.lt_irrefl _ hcol_lt
  set G := garnirSet (la := la) p₁ p₂
  set t := Equiv.swap p₁ p₂ with ht_def
  have ht_row : t ∈ RowSubgroup n la := by
    intro k; simp only [t, Equiv.swap_apply_def]
    split_ifs with h1 h2
    · subst h1; exact hrow_eq.symm
    · subst h2; exact hrow_eq
    · rfl
  have hp₁_mem : p₁ ∈ G := mem_garnirSet_left p₁ p₂
  have hp₂_mem : p₂ ∈ G := mem_garnirSet_right p₁ p₂ hrow_eq
  have ht_supp : ∀ x, x ∉ G → t x = x := by
    intro x hx
    have hx1 : x ≠ p₁ := fun h => hx (h ▸ hp₁_mem)
    have hx2 : x ≠ p₂ := fun h => hx (h ▸ hp₂_mem)
    simp [t, Equiv.swap_apply_of_ne_of_ne hx1 hx2]
  have ht_sign : Equiv.Perm.sign t = -1 := by
    simp [t, Equiv.Perm.sign_swap hne]
  have ht_ne : t ≠ 1 := by
    intro h
    have hsign1 := congr_arg Equiv.Perm.sign h
    rw [ht_sign, map_one] at hsign1
    exact absurd hsign1 (by decide)
  -- swap is not in ColumnSubgroup since col(p₁) ≠ col(p₂)
  have ht_not_col : t ∉ ColumnSubgroup n la := by
    intro hmem
    have := hmem p₁
    simp only [t, Equiv.swap_apply_left] at this
    exact absurd this.symm (Nat.ne_of_lt hcol_lt)
  -- Step 3: Apply the Garnir polytabloid identity
  have h_id := garnir_polytabloid_identity σ G t ht_row ht_supp ht_sign
  -- Abbreviations
  set ψ := generalizedPolytabloidTab (n := n) (la := la) σ with hψ_def
  set L := Submodule.span ℂ (Set.range (fun τ : {τ : Equiv.Perm (Fin n) //
      isColumnStandard' n la τ ∧ rowInvCount' (la := la) τ < rowInvCount' (la := la) σ} =>
    generalizedPolytabloidTab (n := n) (la := la) τ.val))
  classical
  -- Set up subtype and predicates
  set T := {w : Equiv.Perm (Fin n) // (∀ x, x ∉ G → w x = x) ∧ w ≠ 1} with hT_def
  set p_col : T → Prop := fun w => w.val ∈ ColumnSubgroup n la with hp_col_def
  set p_row : T → Prop := fun w => w.val ∈ RowSubgroup n la with hp_row_def
  haveI hp_col_dec : DecidablePred p_col := fun w => Classical.dec (p_col w)
  haveI hp_row_dec : DecidablePred p_row := fun w => Classical.dec (p_row w)
  let f : T → TabloidRepresentation n la := fun w =>
    ((↑(↑(Equiv.Perm.sign w.val) : ℤ) : ℂ) •
      twistedPolytabloid (la := la) w.val σ)
  -- t = swap(p₁, p₂) viewed as a T-element
  set t_elem : T := ⟨t, ht_supp, ht_ne⟩ with ht_elem_def
  -- The "neither" sum is in L (uses fixed garnir_twisted_in_lower_span with hw_row)
  have h_neither_mem :
      -(∑ w ∈ Finset.univ.filter (fun w : T => ¬p_col w ∧ ¬p_row w), f w) ∈ L := by
    apply Submodule.neg_mem
    apply Submodule.sum_mem
    intro ⟨w, hw_supp, hw_ne⟩ hmem
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hp_col_def,
      hp_row_def] at hmem
    show f ⟨w, hw_supp, hw_ne⟩ ∈ L
    apply Submodule.smul_mem
    exact garnir_twisted_in_lower_span σ hcs hrp G w hw_supp hw_ne hmem.1 hmem.2
  -- The Q part: each term equals ψ (since sign(w)² = 1 and twistedPolytabloid_col_eq)
  have h_col_term : ∀ w : T, p_col w → f w = ψ := by
    intro ⟨w, hw_supp, hw_ne⟩ hw_col
    show f ⟨w, hw_supp, hw_ne⟩ = ψ
    simp only [f]
    rw [twistedPolytabloid_col_eq w hw_col σ, smul_smul, ← hψ_def]
    have : (↑(↑(Equiv.Perm.sign w) : ℤ) : ℂ) * (↑(↑(Equiv.Perm.sign w) : ℤ) : ℂ) = 1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign w) with h | h <;>
        simp [show (Equiv.Perm.sign w : ℤ) = _ from congr_arg Units.val h]
    rw [this, one_smul]
  have h_col_sum : ∑ w ∈ Finset.univ.filter p_col, f w =
    ((Finset.univ.filter p_col).card : ℂ) • ψ := by
    rw [Finset.sum_eq_card_nsmul (s := Finset.univ.filter p_col)
      (b := ψ) (fun w hw => h_col_term w (Finset.mem_filter.mp hw).2)]
    rw [← Nat.cast_smul_eq_nsmul ℂ]
  -- Structural lemma: only swap(p₁, p₂) is a row-preserving, non-identity
  -- G-supported permutation. The proof uses:
  -- (1) w preserves G (since supp(w) ⊂ G ⟹ w fixes Gᶜ),
  -- (2) row r₀ := row(p₁) ∩ G = {p₁, p₂},
  -- (3) for r ≠ r₀: row r ∩ G has at most 1 element.
  have hsum : la.sortedParts.sum = n := sortedParts_sum_eq n la
  have hG_row_r₀ : ∀ p ∈ G,
      rowOfPos la.sortedParts p.val = rowOfPos la.sortedParts p₁.val →
      p = p₁ ∨ p = p₂ := by
    intro p hp hrow_p
    simp only [G, garnirSet, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    rcases hp with ⟨hcol_p, _⟩ | ⟨hcol_p, _⟩
    · left; exact Fin.ext (rowOfPos_colOfPos_injective la.sortedParts p.val p₁.val
        (by omega) (by omega) hrow_p hcol_p)
    · right
      have : rowOfPos la.sortedParts p.val = rowOfPos la.sortedParts p₂.val :=
        hrow_p.trans hrow_eq
      exact Fin.ext (rowOfPos_colOfPos_injective la.sortedParts p.val p₂.val
        (by omega) (by omega) this hcol_p)
  have hG_row_other : ∀ a ∈ G, ∀ b ∈ G,
      rowOfPos la.sortedParts a.val = rowOfPos la.sortedParts b.val →
      rowOfPos la.sortedParts a.val ≠ rowOfPos la.sortedParts p₁.val →
      a = b := by
    intro a ha b hb hrow_ab hrow_ne
    simp only [G, garnirSet, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    rcases ha with ⟨hcol_a, hr_a⟩ | ⟨hcol_a, hr_a⟩ <;>
      rcases hb with ⟨hcol_b, hr_b⟩ | ⟨hcol_b, hr_b⟩
    · exact Fin.ext (rowOfPos_colOfPos_injective la.sortedParts a.val b.val
        (by omega) (by omega) hrow_ab (hcol_a.trans hcol_b.symm))
    · exfalso
      have ha_le : rowOfPos la.sortedParts a.val ≤ rowOfPos la.sortedParts p₁.val :=
        hrow_ab.symm ▸ hr_b
      have : rowOfPos la.sortedParts a.val = rowOfPos la.sortedParts p₁.val :=
        Nat.le_antisymm ha_le hr_a
      exact hrow_ne this
    · exfalso
      have ha_le : rowOfPos la.sortedParts a.val ≤ rowOfPos la.sortedParts p₁.val := hr_a
      have ha_ge : rowOfPos la.sortedParts p₁.val ≤ rowOfPos la.sortedParts a.val :=
        hrow_ab.symm ▸ hr_b
      have : rowOfPos la.sortedParts a.val = rowOfPos la.sortedParts p₁.val :=
        Nat.le_antisymm ha_le ha_ge
      exact hrow_ne this
    · exact Fin.ext (rowOfPos_colOfPos_injective la.sortedParts a.val b.val
        (by omega) (by omega) hrow_ab (hcol_a.trans hcol_b.symm))
  have h_w_eq_swap : ∀ w : Equiv.Perm (Fin n),
      (∀ x, x ∉ G → w x = x) → w ≠ 1 → w ∈ RowSubgroup n la → w = t := by
    intro w hw_supp hw_ne hw_row
    -- w preserves G
    have hw_preserves_G : ∀ x ∈ G, w x ∈ G := by
      intro x hx
      by_contra hwx_notin
      have hy : w (w x) = w x := hw_supp (w x) hwx_notin
      have hwx_eq : w x = x := w.injective hy
      rw [hwx_eq] at hwx_notin
      exact hwx_notin hx
    -- w p₁ ∈ {p₁, p₂}
    have hw_p₁_mem : w p₁ = p₁ ∨ w p₁ = p₂ := by
      refine hG_row_r₀ (w p₁) (hw_preserves_G p₁ hp₁_mem) ?_
      exact hw_row p₁
    -- w p₂ ∈ {p₁, p₂}
    have hw_p₂_mem : w p₂ = p₁ ∨ w p₂ = p₂ := by
      refine hG_row_r₀ (w p₂) (hw_preserves_G p₂ hp₂_mem) ?_
      rw [hw_row p₂]; exact hrow_eq.symm
    -- w fixes x ∉ {p₁, p₂}
    have hw_fixed : ∀ x : Fin n, x ≠ p₁ → x ≠ p₂ → w x = x := by
      intro x hxp1 hxp2
      by_cases hxG : x ∈ G
      · by_cases hrow_x : rowOfPos la.sortedParts x.val =
            rowOfPos la.sortedParts p₁.val
        · rcases hG_row_r₀ x hxG hrow_x with rfl | rfl
          · exact absurd rfl hxp1
          · exact absurd rfl hxp2
        · refine hG_row_other (w x) (hw_preserves_G x hxG) x hxG (hw_row x) ?_
          rw [hw_row x]; exact hrow_x
      · exact hw_supp x hxG
    -- Combine: w must be the swap
    have hw_p₁_eq : w p₁ = p₂ := by
      rcases hw_p₁_mem with hfix | hswap
      · -- w fixes p₁; show w = 1, contradicting hw_ne
        exfalso; apply hw_ne
        ext x
        by_cases hxp1 : x = p₁
        · subst hxp1; rw [hfix, Equiv.Perm.one_apply]
        by_cases hxp2 : x = p₂
        · subst hxp2
          -- w p₂ ∈ {p₁, p₂}. If w p₂ = p₁, but w p₁ = p₁, injectivity fails.
          rcases hw_p₂_mem with h | h
          · exact absurd (w.injective (h.trans hfix.symm)) hne.symm
          · rw [h, Equiv.Perm.one_apply]
        · rw [hw_fixed x hxp1 hxp2, Equiv.Perm.one_apply]
      · exact hswap
    have hw_p₂_eq : w p₂ = p₁ := by
      rcases hw_p₂_mem with hswap | hfix
      · exact hswap
      · -- w p₂ = p₂; combined with w p₁ = p₂, injectivity gives p₁ = p₂
        exact absurd (w.injective (hw_p₁_eq.trans hfix.symm)) hne
    ext x
    by_cases hx1 : x = p₁
    · subst hx1; rw [hw_p₁_eq, ht_def, Equiv.swap_apply_left]
    by_cases hx2 : x = p₂
    · subst hx2; rw [hw_p₂_eq, ht_def, Equiv.swap_apply_right]
    · rw [hw_fixed x hx1 hx2, ht_def, Equiv.swap_apply_of_ne_of_ne hx1 hx2]
  -- The P\Q filter is exactly the singleton {t_elem}
  have hfilter_PmQ : Finset.univ.filter (fun w : T => ¬p_col w ∧ p_row w) = {t_elem} := by
    apply Finset.ext
    intro ⟨w, hw_supp, hw_ne⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
      hp_col_def, hp_row_def]
    refine ⟨fun ⟨_, hw_row⟩ => ?_, fun heq => ?_⟩
    · exact Subtype.ext (h_w_eq_swap w hw_supp hw_ne hw_row)
    · have hval : w = t := congr_arg Subtype.val heq
      rw [hval]
      exact ⟨ht_not_col, ht_row⟩
  -- The P\Q sum equals -ψ
  have h_p_minus_q_sum :
      ∑ w ∈ Finset.univ.filter (fun w : T => ¬p_col w ∧ p_row w), f w = -ψ := by
    rw [hfilter_PmQ, Finset.sum_singleton]
    show f t_elem = -ψ
    simp only [f, t_elem]
    rw [twistedPolytabloid_row_eq t ht_row σ, ← hψ_def, ht_sign]
    have : ((↑(↑(-1 : ℤˣ) : ℤ) : ℂ)) = -1 := by norm_cast
    rw [this, neg_one_smul]
  -- Three-way split of the T-sum, via two applications of sum_filter_add_sum_filter_not
  have h_split : ∑ w : T, f w =
      ∑ w ∈ Finset.univ.filter p_col, f w +
      ∑ w ∈ Finset.univ.filter (fun w : T => ¬p_col w ∧ p_row w), f w +
      ∑ w ∈ Finset.univ.filter (fun w : T => ¬p_col w ∧ ¬p_row w), f w := by
    have step1 : ∑ w : T, f w =
        ∑ w ∈ Finset.univ.filter p_col, f w +
          ∑ w ∈ Finset.univ.filter (fun w : T => ¬p_col w), f w :=
      (Finset.sum_filter_add_sum_filter_not Finset.univ p_col f).symm
    have step2 : ∑ w ∈ Finset.univ.filter (fun w : T => ¬p_col w), f w =
        ∑ w ∈ Finset.univ.filter (fun w : T => ¬p_col w ∧ p_row w), f w +
        ∑ w ∈ Finset.univ.filter (fun w : T => ¬p_col w ∧ ¬p_row w), f w := by
      have h2a : (Finset.univ.filter (fun w : T => ¬p_col w)).filter p_row =
          Finset.univ.filter (fun w : T => ¬p_col w ∧ p_row w) := by
        ext w; simp
      have h2b : (Finset.univ.filter (fun w : T => ¬p_col w)).filter (fun w => ¬p_row w) =
          Finset.univ.filter (fun w : T => ¬p_col w ∧ ¬p_row w) := by
        ext w; simp
      rw [← h2a, ← h2b]
      exact (Finset.sum_filter_add_sum_filter_not _ p_row f).symm
    rw [step1, step2, add_assoc]
  -- Set k = |Q part|
  set k := (Finset.univ.filter p_col).card with hk_def
  -- Key algebraic identity: k•ψ = -Σ_{neither} f ∈ L.
  set S_neither := ∑ w ∈ Finset.univ.filter (fun w : T => ¬p_col w ∧ ¬p_row w), f w
    with hS_neither_def
  have h_sum_T : ∑ w : T, f w = (k : ℂ) • ψ + -ψ + S_neither := by
    rw [h_split, h_col_sum, h_p_minus_q_sum]
  have h_k_psi_mem_L : (k : ℂ) • ψ ∈ L := by
    -- From h_id and h_sum_T: ψ = -(↑k•ψ + -ψ + S_neither)
    -- Add (↑k•ψ + -ψ + S_neither) both sides: ψ + (...) = 0
    -- Simplify (-ψ + ψ) = 0: ↑k•ψ + S_neither = 0
    -- Hence ↑k•ψ = -S_neither ∈ L
    have h2 : ψ + ((k : ℂ) • ψ + -ψ + S_neither) = 0 := by
      rw [← h_sum_T]; rw [h_id]; exact neg_add_cancel _
    -- Manual rearrangement avoiding `abel`
    have hrearrange : ψ + ((k : ℂ) • ψ + -ψ + S_neither) = (k : ℂ) • ψ + S_neither := by
      rw [show ((k : ℂ) • ψ + -ψ + S_neither) =
          ((k : ℂ) • ψ + (-ψ + S_neither)) from add_assoc _ _ _]
      rw [show ψ + ((k : ℂ) • ψ + (-ψ + S_neither)) =
          ((k : ℂ) • ψ) + (ψ + (-ψ + S_neither)) from by
        rw [← add_assoc ψ ((k : ℂ) • ψ) (-ψ + S_neither),
            add_comm ψ ((k : ℂ) • ψ),
            add_assoc]]
      rw [show ψ + (-ψ + S_neither) = S_neither from by
        rw [← add_assoc, add_neg_cancel, zero_add]]
    rw [hrearrange] at h2
    have h_kpsi_eq : (k : ℂ) • ψ = -S_neither := eq_neg_of_add_eq_zero_left h2
    rw [h_kpsi_eq]; exact h_neither_mem
  -- Case split: k = 0 vs k ≥ 1
  by_cases hk_zero : k = 0
  · -- k = 0 case: deferred to follow-up issue.
    -- In this case, the Garnir identity only gives 0 = -(Σ_neither) ∈ L, no info about ψ.
    -- The fix is: since k = 0 iff r₀ = row(p₁) = 0 and col(p₁) has length 1,
    -- use σ' = swap(p₁, p₂) · σ which stays in the span (needs separate proof).
    -- TODO: resolve via follow-up issue (k = 0 requires swap-based argument).
    sorry
  · -- k ≥ 1 case: divide by k.
    have hk_ne : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hk_zero
    have : ψ = ((k : ℂ)⁻¹) • ((k : ℂ) • ψ) := by
      rw [smul_smul, inv_mul_cancel₀ hk_ne, one_smul]
    rw [this]
    exact Submodule.smul_mem L _ h_k_psi_mem_L

/-- For column-standard σ, the generalized polytabloidTab ψ_σ lies in the
span of standard polytabloidTabs. This is the core of the straightening
theorem.

The proof uses strong induction on `rowInvCount'`:
- **Base case** (rowInvCount' = 0): σ is both column- and row-standard,
  hence σ = sytPerm T for some SYT T, and ψ_σ = polytabloidTab T ∈ span.
- **Inductive case** (rowInvCount' > 0): By `garnir_straightening_step`,
  ψ_σ is in the span of {ψ_{σ'}} where each σ' is column-standard with
  strictly fewer row inversions. By the induction hypothesis, each
  ψ_{σ'} ∈ span{polytabloidTab T}, so ψ_σ ∈ span{polytabloidTab T}.

References: James Ch. 7-8, Fulton Ch. 7. -/
private theorem polytabloidTab_column_standard_in_span
    (σ : Equiv.Perm (Fin n)) (hcs : isColumnStandard' n la σ) :
    generalizedPolytabloidTab (n := n) (la := la) σ ∈
      Submodule.span ℂ (Set.range (fun T : StandardYoungTableau n la =>
        polytabloidTab (n := n) (la := la) T)) := by
  -- Strong induction on rowInvCount'
  suffices ∀ (k : ℕ) (τ : Equiv.Perm (Fin n)),
      k = rowInvCount' (la := la) τ →
      isColumnStandard' n la τ →
      generalizedPolytabloidTab (n := n) (la := la) τ ∈
        Submodule.span ℂ (Set.range (fun T : StandardYoungTableau n la =>
          polytabloidTab (n := n) (la := la) T)) from
    this _ σ rfl hcs
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
  intro τ hk hcs_τ
  by_cases hrz : k = 0
  · -- Base case: rowInvCount' = 0 means row-standard, hence SYT
    subst hrz
    have hrs := (rowInvCount'_eq_zero_iff (la := la) τ).mp (by omega)
    obtain ⟨T, rfl⟩ := column_row_standard_is_syt τ hcs_τ hrs
    have : generalizedPolytabloidTab (sytPerm n la T) = polytabloidTab T :=
      generalizedPolytabloidTab_eq_polytabloidTab T
    rw [this]
    exact Submodule.subset_span ⟨T, rfl⟩
  · -- Inductive case: use Garnir straightening step
    have hrp : 0 < rowInvCount' (la := la) τ := by omega
    have h_step := garnir_straightening_step τ hcs_τ hrp
    -- ψ_τ ∈ span{ψ_{τ'} : τ' column-standard, rowInvCount'(τ') < k}
    -- Each ψ_{τ'} ∈ span{e_T} by induction hypothesis
    -- Therefore ψ_τ ∈ span{e_T}
    set S_syt := Set.range (fun T : StandardYoungTableau n la =>
      polytabloidTab (n := n) (la := la) T)
    -- Show the Garnir span is contained in the SYT span
    have h_sub : Set.range (fun τ' : {τ' : Equiv.Perm (Fin n) //
        isColumnStandard' n la τ' ∧ rowInvCount' (la := la) τ' <
          rowInvCount' (la := la) τ} =>
      generalizedPolytabloidTab (n := n) (la := la) τ'.val) ⊆
        ↑(Submodule.span ℂ S_syt) := by
      rintro _ ⟨⟨τ', hτ'_cs, hτ'_lt⟩, rfl⟩
      exact ih (rowInvCount' (la := la) τ') (hk ▸ hτ'_lt) τ' rfl hτ'_cs
    exact (Submodule.span_le.mpr h_sub) h_step

/-- The tabloid-level straightening theorem: for any permutation σ, the
generalized polytabloidTab ψ_σ = Σ_{q ∈ Q_λ} sign(q)·[q⁻¹σ] lies in the
ℂ-span of the standard polytabloidTabs {e_T : T ∈ SYT(λ)}.

This is the key ingredient for dim V_λ ≤ |SYT(λ)|. The proof reduces to the
column-standard case via Q_λ-equivariance, then uses the Garnir identity. -/
theorem generalizedPolytabloidTab_mem_span_polytabloidTab (σ : Equiv.Perm (Fin n)) :
    generalizedPolytabloidTab (n := n) (la := la) σ ∈
      Submodule.span ℂ (Set.range (fun T : StandardYoungTableau n la =>
        polytabloidTab (n := n) (la := la) T)) := by
  -- Step 1: Find q₀ ∈ Q_λ such that q₀ * σ is column-standard
  obtain ⟨q₀, hq₀, hcs⟩ := exists_column_standard_mul (la := la) σ
  -- Step 2: ψ_σ = sign(q₀⁻¹) · ψ_{q₀σ} by Q_λ-equivariance
  -- From ψ_{q₀σ} = sign(q₀) · ψ_σ, we get ψ_σ = sign(q₀)⁻¹ · ψ_{q₀σ}
  -- Since sign(q₀) ∈ {±1}, sign(q₀)⁻¹ = sign(q₀)
  have hq₀σ_mem := polytabloidTab_column_standard_in_span (q₀ * σ) hcs
  have hcol := generalizedPolytabloidTab_col_mul q₀ hq₀ σ
  -- ψ_{q₀σ} = sign(q₀) · ψ_σ, so ψ_σ = sign(q₀) · ψ_{q₀σ}
  -- (because sign(q₀)² = 1, i.e., sign(q₀) · sign(q₀) · ψ_σ = ψ_σ)
  have hsign_sq : ((↑(Equiv.Perm.sign q₀) : ℤ) : ℂ) *
      ((↑(Equiv.Perm.sign q₀) : ℤ) : ℂ) = 1 := by
    have : Equiv.Perm.sign q₀ = 1 ∨ Equiv.Perm.sign q₀ = -1 :=
      Int.units_eq_one_or q₀.sign
    rcases this with h | h <;> simp [h]
  rw [hcol] at hq₀σ_mem
  -- ψ_σ = sign(q₀) · ψ_{q₀σ} and sign(q₀) · ψ_{q₀σ} = sign(q₀) · (sign(q₀) · ψ_σ)
  -- So we need: sign(q₀) · ψ_{q₀σ} ∈ span ← from hq₀σ_mem smul
  -- Actually, ψ_{q₀σ} ∈ span implies sign(q₀) · ψ_{q₀σ} ∈ span (span is a submodule)
  -- And ψ_{q₀σ} = sign(q₀) · ψ_σ, so sign(q₀) · ψ_{q₀σ} = sign(q₀)² · ψ_σ = ψ_σ
  -- But we need to go the other way: from ψ_{q₀σ} ∈ span to ψ_σ ∈ span
  -- ψ_{q₀σ} = sign(q₀) · ψ_σ ∈ span, and sign(q₀)·(sign(q₀)·ψ_σ) = ψ_σ ∈ span
  have : generalizedPolytabloidTab (n := n) (la := la) σ =
      ((↑(Equiv.Perm.sign q₀) : ℤ) : ℂ) •
        generalizedPolytabloidTab (n := n) (la := la) (q₀ * σ) := by
    rw [hcol, smul_smul, hsign_sq, one_smul]
  rw [this]
  exact Submodule.smul_mem _ _ (polytabloidTab_column_standard_in_span (q₀ * σ) hcs)

/-! ### Dimension upper bound -/

/-- The image of V_λ under tabloidProjection is contained in the span of
standard polytabloidTabs. This follows from the straightening theorem:
every ψ(of(σ) * c_λ) = |P_λ| · ψ_{σ⁻¹} lies in span{e_T}. -/
private theorem tabloidProjection_spechtModule_le_span :
    Submodule.map (tabloidProjection (n := n) (la := la))
      ((SpechtModule n la).restrictScalars ℂ) ≤
    Submodule.span ℂ (Set.range (fun T : StandardYoungTableau n la =>
      polytabloidTab (n := n) (la := la) T)) := by
  rw [Submodule.map_le_iff_le_comap]
  intro v hv
  rw [Submodule.mem_comap]
  -- v ∈ V_λ = ℂ[S_n] · c_λ, so v = a * c_λ for some a
  have hv' : v ∈ SpechtModule n la := hv
  rw [SpechtModule, Submodule.mem_span_singleton] at hv'
  obtain ⟨a, rfl⟩ := hv'
  -- ψ(a * c_λ) = Σ_{σ ∈ supp(a)} a(σ) · ψ(of(σ) * c_λ)
  -- Each ψ(of(σ) * c_λ) = |P_λ| · ψ_{σ⁻¹} ∈ span{e_T} by straightening
  show tabloidProjection (a • YoungSymmetrizer n la) ∈ _
  -- Decompose a • c_λ = Σ a(σ) • (of(σ) * c_λ)
  have key : a • YoungSymmetrizer n la =
      a.sum (fun g c => c • (MonoidAlgebra.of ℂ _ g * YoungSymmetrizer n la)) := by
    conv_lhs => rw [show a • YoungSymmetrizer n la =
        a * YoungSymmetrizer n la from rfl]
    conv_lhs => rw [← Finsupp.sum_single a]
    simp only [Finsupp.sum, Finset.sum_mul]
    congr 1; ext σ
    simp [MonoidAlgebra.of_apply]
  rw [key, Finsupp.sum, map_sum]
  apply Submodule.sum_mem
  intro σ _
  rw [map_smul, tabloidProjection_of_mul_youngSymmetrizer]
  apply Submodule.smul_mem
  apply Submodule.smul_mem
  exact generalizedPolytabloidTab_mem_span_polytabloidTab σ⁻¹

/-- dim V_λ ≤ |SYT(λ)|.

The proof uses:
1. ψ: V_λ → M^λ is injective (by irreducibility of V_λ, Theorem 5.12.2)
2. Image ψ(V_λ) ⊆ span{polytabloidTab(T)} (from the straightening theorem)
3. span{polytabloidTab(T)} has dimension ≤ |SYT(λ)| (at most |SYT| generators) -/
theorem finrank_spechtModule_le_card_syt :
    Module.finrank ℂ (SpechtModule n la) ≤
      Fintype.card (StandardYoungTableau n la) := by
  -- Define the restricted map ψ|_{V_λ}: V_λ → M^λ
  let ψ_res : (SpechtModule n la).restrictScalars ℂ →ₗ[ℂ] TabloidRepresentation n la :=
    (tabloidProjection (n := n) (la := la)).comp
      ((SpechtModule n la).restrictScalars ℂ).subtype
  -- ψ_res is injective
  have h_inj : Function.Injective ψ_res := by
    intro ⟨v, hv⟩ ⟨w, hw⟩ heq
    simp only [ψ_res, LinearMap.comp_apply, Submodule.subtype_apply] at heq
    have : (v : SymGroupAlgebra n) - w = 0 := by
      apply tabloidProjection_injective_on_spechtModule (n := n) (la := la)
      · exact ((SpechtModule n la).restrictScalars ℂ).sub_mem hv hw
      · rw [map_sub]; exact sub_eq_zero.mpr heq
    exact Subtype.ext (sub_eq_zero.mp this)
  -- dim(V_λ) = dim(range ψ_res) by injectivity
  have h_finrank_eq : Module.finrank ℂ (SpechtModule n la) =
      Module.finrank ℂ (LinearMap.range ψ_res) :=
    (LinearMap.finrank_range_of_inj h_inj).symm
  -- range ψ_res = image = Submodule.map ψ (V_λ.restrictScalars ℂ)
  have h_range : LinearMap.range ψ_res =
      Submodule.map (tabloidProjection (n := n) (la := la))
        ((SpechtModule n la).restrictScalars ℂ) := by
    simp only [ψ_res, LinearMap.range_comp, Submodule.range_subtype]
  -- image ⊆ span{e_T} by the straightening
  have hS_le := tabloidProjection_spechtModule_le_span (n := n) (la := la)
  -- dim(image) ≤ dim(span{e_T}) ≤ |SYT|
  calc Module.finrank ℂ (SpechtModule n la)
      = Module.finrank ℂ (LinearMap.range ψ_res) := h_finrank_eq
    _ = Module.finrank ℂ (Submodule.map (tabloidProjection (n := n) (la := la))
          ((SpechtModule n la).restrictScalars ℂ)) := by rw [h_range]
    _ ≤ Module.finrank ℂ (Submodule.span ℂ (Set.range (fun T : StandardYoungTableau n la =>
          polytabloidTab (n := n) (la := la) T))) :=
        Submodule.finrank_mono hS_le
    _ ≤ Fintype.card (StandardYoungTableau n la) :=
        finrank_range_le_card _

/-- dim V_λ = |SYT(λ)|.

This is the main dimension theorem: the Specht module V_λ has dimension
equal to the number of standard Young tableaux of shape λ.

Combines the two directions:
- ≥: from `finrank_spechtModule_ge_card_syt` (TabloidModule.lean)
- ≤: from `finrank_spechtModule_le_card_syt` (above, via straightening) -/
theorem finrank_spechtModule_eq_card_syt' (n : ℕ) (la : Nat.Partition n) :
    Module.finrank ℂ (SpechtModule n la) =
      Fintype.card (StandardYoungTableau n la) :=
  le_antisymm finrank_spechtModule_le_card_syt finrank_spechtModule_ge_card_syt

end

end Etingof
