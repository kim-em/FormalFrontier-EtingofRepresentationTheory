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
  sorry

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

/-! ### Garnir straightening step

The key technical result: for column-standard σ with row inversions,
ψ_σ can be expressed via Garnir relations in terms of generalized
polytabloidTabs with strictly fewer row inversions. This uses:
1. `garnirAnnihilate_tabloid` — the tabloid-level Garnir identity
2. Dominance analysis — Garnir permutations produce more dominant tabloids
3. Column re-standardization — reducing back to column-standard form
-/

/-- **Garnir straightening step** (key sorry):
For column-standard σ with positive row inversion count, the generalized
polytabloidTab ψ_σ lies in the ℂ-span of {ψ_{σ'} : σ' column-standard,
rowInvCount'(σ') < rowInvCount'(σ)}.

This is the core combinatorial content of the straightening theorem.
The proof requires:
1. Finding a row descent in σ (exists since rowInvCount' > 0)
2. Applying the tabloid-level Garnir identity to each term of ψ_σ
3. Showing the regrouped terms are column-antisymmetrized sums over
   strictly more dominant tabloids (twisted polytabloids)
4. Showing each twisted polytabloid can be column-re-standardized to give
   standard generalized polytabloidTabs with fewer row inversions

See issue for detailed decomposition of the remaining proof obligations. -/
private theorem garnir_straightening_step
    (σ : Equiv.Perm (Fin n)) (hcs : isColumnStandard' n la σ)
    (hrp : 0 < rowInvCount' (la := la) σ) :
    generalizedPolytabloidTab (n := n) (la := la) σ ∈
      Submodule.span ℂ (Set.range (fun τ : {τ : Equiv.Perm (Fin n) //
          isColumnStandard' n la τ ∧ rowInvCount' (la := la) τ < rowInvCount' (la := la) σ} =>
        generalizedPolytabloidTab (n := n) (la := la) τ.val)) := by
  sorry

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
