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

/-! ## Helper lemmas for rowOfPos/colOfPos -/

/-- For the canonical position at (row r, col c) in a Young diagram: rowOfPos and colOfPos
give back r and c. The position is (parts.take r).sum + c. -/
private lemma rowOfPos_colOfPos_canonical (parts : List ℕ) (r c : ℕ)
    (hr : r < parts.length) (hc : c < parts[r]) :
    Etingof.rowOfPos parts ((parts.take r).sum + c) = r ∧
    Etingof.colOfPos parts ((parts.take r).sum + c) = c := by
  induction parts generalizing r with
  | nil => simp at hr
  | cons a rest ih =>
    cases r with
    | zero =>
      simp only [List.take_zero, List.sum_nil, Nat.zero_add, List.getElem_cons_zero] at hc
      constructor
      · simp [Etingof.rowOfPos]; omega
      · simp [Etingof.colOfPos]; omega
    | succ r' =>
      simp only [List.length_cons] at hr
      simp only [List.getElem_cons_succ] at hc
      have hr' : r' < rest.length := by omega
      obtain ⟨ih1, ih2⟩ := ih r' hr' hc
      simp only [List.take_succ_cons, List.sum_cons]
      have hge : ¬ ((a + (rest.take r').sum + c) < a) := by omega
      have hsub : a + (rest.take r').sum + c - a = (rest.take r').sum + c := by omega
      constructor
      · simp [Etingof.rowOfPos, hge, hsub, ih1]; omega
      · simp [Etingof.colOfPos, hge, hsub, ih2]

/-- Canonical position is within bounds. -/
private lemma canonical_pos_lt_sum (parts : List ℕ) (r c : ℕ)
    (hr : r < parts.length) (hc : c < parts[r]) :
    (parts.take r).sum + c < parts.sum := by
  have h1 : (parts.take r).sum + parts[r] ≤ (parts.take (r + 1)).sum := by
    rw [List.take_succ_eq_append_getElem hr, List.sum_append, List.sum_cons, List.sum_nil]
    omega
  have h2 : (parts.take (r + 1)).sum ≤ parts.sum :=
    List.Sublist.sum_le_sum (List.take_sublist (r + 1) parts) (fun _ _ => Nat.zero_le _)
  omega

/-- For sorted descending parts, c < parts[r] implies c < parts[r'] for r' ≤ r. -/
private lemma col_exists_earlier_row (parts : List ℕ) (hSorted : parts.Sorted (· ≥ ·))
    (r r' c : ℕ) (hr : r < parts.length) (hr' : r' < parts.length) (hle : r' ≤ r)
    (hc : c < parts[r]) : c < parts[r'] := by
  have : parts[r] ≤ parts[r'] := by
    rcases eq_or_lt_of_le hle with rfl | hlt
    · omega
    · exact List.pairwise_iff_getElem.mp hSorted r' r hr' hr hlt
  omega

/-! ## Helper lemmas for the pigeonhole counting argument -/

private theorem sortedParts_sum {n : ℕ} (la : Nat.Partition n) :
    la.sortedParts.sum = n := by
  have h := la.parts_sum
  have hsort : (la.sortedParts : Multiset ℕ) = la.parts := la.parts.sort_eq (· ≥ ·)
  have : la.sortedParts.sum = la.parts.sum := by rw [← Multiset.sum_coe, hsort]
  omega

theorem sortedParts_pos (la : Nat.Partition n) :
    ∀ x ∈ la.sortedParts, 0 < x := fun x hx =>
  la.parts_pos ((Multiset.mem_sort _).mp hx)

private theorem sortedParts_sorted (la : Nat.Partition n) :
    la.sortedParts.Pairwise (· ≥ ·) := la.parts.pairwise_sort (· ≥ ·)

/-- rowOfPos characterization: position j is in the first k rows iff j < take(k).sum. -/
private theorem rowOfPos_lt_iff (parts : List ℕ) (j k : ℕ) (hj : j < parts.sum) :
    Etingof.rowOfPos parts j < k ↔ j < (parts.take k).sum := by
  induction parts generalizing j k with
  | nil => simp at hj
  | cons p ps ih =>
    cases k with
    | zero =>
      simp only [List.take_zero, List.sum_nil, Etingof.rowOfPos]
      split_ifs with h <;> omega
    | succ k =>
      simp only [List.take_succ_cons, List.sum_cons, Etingof.rowOfPos]
      split_ifs with h
      · omega
      · have hj' : j - p < ps.sum := by simp [List.sum_cons] at hj; omega
        have := ih (j - p) k hj'
        omega

/-- rowOfPos is bounded by parts.length for valid positions. -/
private theorem rowOfPos_lt_length (parts : List ℕ) (j : ℕ) (hj : j < parts.sum) :
    Etingof.rowOfPos parts j < parts.length := by
  induction parts generalizing j with
  | nil => simp at hj
  | cons p ps ih =>
    simp only [Etingof.rowOfPos, List.length_cons]
    split_ifs with h
    · omega
    · have := ih (j - p) (by simp [List.sum_cons] at hj; omega); omega

/-- colOfPos gives a value less than the row width (getElem version). -/
private theorem colOfPos_lt_getElem (parts : List ℕ) (j : ℕ) (hj : j < parts.sum) :
    Etingof.colOfPos parts j < parts[Etingof.rowOfPos parts j]'(rowOfPos_lt_length parts j hj) := by
  have h := Etingof.colOfPos_lt_getD parts j hj
  simp [List.getD] at h
  rw [List.getElem?_eq_getElem (rowOfPos_lt_length parts j hj)] at h
  simpa using h

/-- colOfPos is bounded by headD 0 for sorted descending parts. -/
private theorem colOfPos_lt_headD (parts : List ℕ) (j : ℕ) (hj : j < parts.sum)
    (hSorted : parts.Pairwise (· ≥ ·)) :
    Etingof.colOfPos parts j < parts.headD 0 := by
  induction parts generalizing j with
  | nil => simp at hj
  | cons p ps ih =>
    simp only [List.headD, Etingof.colOfPos]
    split_ifs with h
    · exact h
    · have hj' : j - p < ps.sum := by simp [List.sum_cons] at hj; omega
      have hps_sorted := List.Pairwise.tail hSorted
      calc Etingof.colOfPos ps (j - p) < ps.headD 0 := ih (j - p) hj' hps_sorted
      _ ≤ p := by
        cases ps with
        | nil => simp [List.headD]
        | cons q qs =>
          simp [List.headD]
          exact (List.pairwise_cons.mp hSorted).1 q (by simp)

/-- Column height: number of rows with width > c. -/
private def colHeight (parts : List ℕ) (c : ℕ) : ℕ := (parts.filter (· > c)).length

private theorem colHeight_eq_zero_of_ge_headD (parts : List ℕ) (c : ℕ)
    (hSorted : parts.Pairwise (· ≥ ·)) (hc : parts.headD 0 ≤ c) :
    colHeight parts c = 0 := by
  simp only [colHeight]; apply List.length_eq_zero_iff.mpr
  apply List.filter_eq_nil_iff.mpr
  intro x hx; simp only [decide_eq_true_eq, not_lt]
  cases parts with
  | nil => simp at hx
  | cons p ps =>
    simp [List.headD] at hc
    rcases List.mem_cons.mp hx with rfl | hm
    · omega
    · exact le_trans (List.rel_of_pairwise_cons hSorted hm) hc

private theorem colHeight_cons_gt {p : ℕ} {ps : List ℕ} {c : ℕ} (h : c < p) :
    colHeight (p :: ps) c = 1 + colHeight ps c := by
  simp [colHeight, List.filter, show p > c from h]; omega

/-- For sorted descending parts, if parts[r] > c then r < colHeight(parts, c). -/
private theorem row_lt_colHeight_of_gt (parts : List ℕ) (r c : ℕ)
    (hSorted : parts.Pairwise (· ≥ ·))
    (hr : r < parts.length) (hgt : parts[r] > c) :
    r < colHeight parts c := by
  induction parts generalizing r with
  | nil => simp at hr
  | cons p ps ih =>
    have hps_sorted : ps.Pairwise (· ≥ ·) := List.Pairwise.tail hSorted
    have hp_gt : p > c := by
      cases r with
      | zero => simpa using hgt
      | succ r' =>
        simp only [List.length_cons] at hr; simp only [List.getElem_cons_succ] at hgt
        exact lt_of_lt_of_le hgt
          (List.rel_of_pairwise_cons hSorted (List.getElem_mem (by omega)))
    simp only [colHeight, List.filter, show decide (p > c) = true from by simp [hp_gt],
      List.length_cons]
    cases r with
    | zero => omega
    | succ r' =>
      simp only [List.length_cons] at hr; simp only [List.getElem_cons_succ] at hgt
      exact Nat.succ_lt_succ (ih r' hps_sorted (by omega) hgt)

/-- Double counting identity: Σ_{c < headD} min(k, colHeight(parts, c)) = take(k).sum. -/
private theorem sum_min_colHeight (parts : List ℕ) (k : ℕ)
    (hSorted : parts.Pairwise (· ≥ ·)) :
    ∑ c ∈ Finset.range (parts.headD 0),
      min k (colHeight parts c) = (parts.take k).sum := by
  induction parts generalizing k with
  | nil => simp [colHeight]
  | cons p ps ih =>
    cases k with
    | zero => simp
    | succ k =>
      simp only [List.headD, List.take_succ_cons, List.sum_cons]
      have hstep : ∀ c ∈ Finset.range p, min (k + 1) (colHeight (p :: ps) c) =
          1 + min k (colHeight ps c) := by
        intro c hc; rw [Finset.mem_range] at hc; rw [colHeight_cons_gt hc]; omega
      rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib, Finset.sum_const,
        Finset.card_range, smul_eq_mul, mul_one]
      have hps_sorted : ps.Pairwise (· ≥ ·) := List.Pairwise.tail hSorted
      rw [← ih k hps_sorted]; congr 1
      have hle : ps.headD 0 ≤ p := by
        cases ps with
        | nil => simp [List.headD]
        | cons q qs =>
          simp [List.headD]; exact (List.pairwise_cons.mp hSorted).1 q (by simp)
      rw [← Finset.sum_sdiff (Finset.range_mono hle)]
      suffices h : ∑ c ∈ Finset.range p \ Finset.range (ps.headD 0),
          min k (colHeight ps c) = 0 by omega
      apply Finset.sum_eq_zero
      intro c hc
      rw [Finset.mem_sdiff, Finset.mem_range, Finset.mem_range] at hc
      rw [colHeight_eq_zero_of_ge_headD ps c hps_sorted (by omega)]; simp

/-- Cardinality of {i : Fin n | i.val < m} is m. -/
private theorem card_filter_val_lt (n m : ℕ) (hm : m ≤ n) :
    ((Finset.univ : Finset (Fin n)).filter (fun i => i.val < m)).card = m := by
  have hs_eq : (Finset.univ : Finset (Fin n)).filter (fun i => i.val < m) =
      Finset.image (fun j : Fin m => (⟨j.val, by omega⟩ : Fin n)) Finset.univ := by
    ext ⟨i, hi⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Fin.exists_iff]
    constructor
    · intro h; exact ⟨i, by omega, by simp⟩
    · rintro ⟨j, hj, heq⟩; simp at heq; omega
  rw [hs_eq, Finset.card_image_of_injective _ (fun a b h => by ext; simp at h; exact h),
    Finset.card_fin]

/-- The number of positions in the first k rows equals take(k).sum. -/
private theorem card_first_k_rows (la : Nat.Partition n) (k : ℕ) :
    ((Finset.univ : Finset (Fin n)).filter (fun i =>
      Etingof.rowOfPos la.sortedParts i.val < k)).card =
    (la.sortedParts.take k).sum := by
  have hconv : (Finset.univ : Finset (Fin n)).filter (fun i =>
      Etingof.rowOfPos la.sortedParts i.val < k) =
    (Finset.univ : Finset (Fin n)).filter (fun i =>
      i.val < (la.sortedParts.take k).sum) := by
    ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact rowOfPos_lt_iff la.sortedParts i.val k (by rw [sortedParts_sum]; exact i.isLt)
  rw [hconv]
  exact card_filter_val_lt n _ (by
    have h1 : (la.sortedParts.take k).sum ≤ la.sortedParts.sum :=
      List.Sublist.sum_le_sum (List.take_sublist k la.sortedParts) (fun _ _ => Nat.zero_le _)
    have h2 := sortedParts_sum la
    omega)

/-- Lists with all positive elements and equal partial sums are equal. -/
theorem list_eq_of_take_sum_eq {l₁ l₂ : List ℕ}
    (hpos₁ : ∀ x ∈ l₁, 0 < x) (hpos₂ : ∀ x ∈ l₂, 0 < x)
    (h : ∀ k, (l₁.take k).sum = (l₂.take k).sum) : l₁ = l₂ := by
  have hlen : l₁.length = l₂.length := by
    by_contra hne
    wlog hlt : l₁.length < l₂.length with H
    · exact H hpos₂ hpos₁ (fun k => (h k).symm) (by omega) (by omega)
    have hstep := h (l₁.length + 1)
    rw [List.take_of_length_le (by omega : l₁.length ≤ l₁.length + 1)] at hstep
    rw [List.take_succ_eq_append_getElem hlt] at hstep
    simp only [List.sum_append, List.sum_cons, List.sum_nil] at hstep
    have hk := h l₁.length
    rw [List.take_length] at hk
    have := hpos₂ l₂[l₁.length] (List.getElem_mem (by omega))
    omega
  apply List.ext_getElem hlen
  intro i h₁ h₂
  have hk := h (i + 1); have hk' := h i
  rw [List.take_succ_eq_append_getElem h₁, List.sum_append, List.sum_cons, List.sum_nil] at hk
  rw [List.take_succ_eq_append_getElem h₂, List.sum_append, List.sum_cons, List.sum_nil] at hk
  omega

/-- Partitions with equal partial sums of sorted parts are equal. -/
theorem partition_eq_of_partial_sums (la mu : Nat.Partition n)
    (h : ∀ k, (la.sortedParts.take k).sum = (mu.sortedParts.take k).sum) :
    la = mu := by
  apply Nat.Partition.ext
  have h1 : (la.sortedParts : Multiset ℕ) = la.parts := la.parts.sort_eq (· ≥ ·)
  have h2 : (mu.sortedParts : Multiset ℕ) = mu.parts := mu.parts.sort_eq (· ≥ ·)
  rw [← h1, ← h2]
  exact congrArg _ (list_eq_of_take_sum_eq (sortedParts_pos la) (sortedParts_pos mu) h)

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
    (hdom : ¬ mu.Dominates la) (σ : Equiv.Perm (Fin n)) :
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
  -- Step 2: Pigeonhole — by contradiction, derive la = mu from injectivity + dominance
  by_contra h_no
  push_neg at h_no
  -- From h_no: within each row of la, the column-in-mu map is injective.
  -- The counting argument proves mu.Dominates la, contradicting hdom.
  exact hdom fun k => by
    rw [← sum_min_colHeight mu.sortedParts k (sortedParts_sorted mu)]
    rw [← card_first_k_rows la k]
    -- Decompose S_k by column value g(i) = colOfPos(mu, σ⁻¹(i))
    set g := fun (i : Fin n) => colOfPos mu.sortedParts (σ⁻¹ i).val
    set S_k := (Finset.univ : Finset (Fin n)).filter (fun i =>
      rowOfPos la.sortedParts i.val < k)
    set T := Finset.range (mu.sortedParts.headD 0)
    have hmaps : Set.MapsTo g ↑S_k ↑T := fun i hi => by
      rw [Finset.mem_coe, Finset.mem_filter] at hi; rw [Finset.mem_coe, Finset.mem_range]
      exact colOfPos_lt_headD mu.sortedParts _ (by rw [sortedParts_sum]; exact (σ⁻¹ i).isLt)
        (sortedParts_sorted mu)
    rw [Finset.card_eq_sum_card_fiberwise hmaps]
    apply Finset.sum_le_sum; intro c _
    -- Each fiber {i ∈ S_k : g(i) = c} has card ≤ min(k, colHeight(mu, c))
    have hfilt_eq : S_k.filter (fun i => g i = c) =
        Finset.univ.filter (fun i : Fin n =>
          rowOfPos la.sortedParts i.val < k ∧
          colOfPos mu.sortedParts (σ⁻¹ i).val = c) := by
      ext i; simp [S_k, g, Finset.mem_filter]
    rw [hfilt_eq]
    set F := Finset.univ.filter (fun i : Fin n =>
      rowOfPos la.sortedParts i.val < k ∧
      colOfPos mu.sortedParts (σ⁻¹ i).val = c)
    apply Nat.le_min.mpr; constructor
    · -- Bound 1: ≤ k (distinct row values via injection into Finset.range k)
      have hmaps1 : Set.MapsTo (fun i : Fin n => rowOfPos la.sortedParts i.val) ↑F ↑(Finset.range k) := by
        intro i hi
        rw [Finset.mem_coe, Finset.mem_filter] at hi
        exact Finset.mem_range.mpr hi.2.1
      have hinj1 : Set.InjOn (fun i : Fin n => rowOfPos la.sortedParts i.val) ↑F := by
        intro i hi j hj heq
        rw [Finset.mem_coe, Finset.mem_filter] at hi hj
        by_contra hne; exact h_no i j hne heq (by rw [hi.2.2, hj.2.2])
      have h1 := Finset.card_le_card_of_injOn _ hmaps1 hinj1
      rw [Finset.card_range] at h1; exact h1
    · -- Bound 2: ≤ colHeight(mu, c) (inject σ⁻¹ into column c of mu)
      have hmaps2 : Set.MapsTo (fun i : Fin n => rowOfPos mu.sortedParts (σ⁻¹ i).val)
          ↑F ↑(Finset.range (colHeight mu.sortedParts c)) := by
        intro i hi
        rw [Finset.mem_coe, Finset.mem_filter] at hi
        rw [Finset.mem_coe, Finset.mem_range]
        have hv : (σ⁻¹ i).val < mu.sortedParts.sum := by rw [sortedParts_sum]; exact (σ⁻¹ i).isLt
        have hrow := rowOfPos_lt_length mu.sortedParts _ hv
        have hcol := colOfPos_lt_getElem mu.sortedParts _ hv
        rw [hi.2.2] at hcol
        exact row_lt_colHeight_of_gt mu.sortedParts _ c (sortedParts_sorted mu) hrow (by omega)
      have hinj2 : Set.InjOn (fun i : Fin n => rowOfPos mu.sortedParts (σ⁻¹ i).val) ↑F := by
        intro i hi j hj heq
        rw [Finset.mem_coe, Finset.mem_filter] at hi hj
        have hcol_eq : colOfPos mu.sortedParts (σ⁻¹ i).val =
            colOfPos mu.sortedParts (σ⁻¹ j).val := by rw [hi.2.2, hj.2.2]
        have hval_eq := rowOfPos_colOfPos_injective mu.sortedParts _ _
          (by rw [sortedParts_sum]; exact (σ⁻¹ i).isLt)
          (by rw [sortedParts_sum]; exact (σ⁻¹ j).isLt) heq hcol_eq
        exact σ.symm.injective (Fin.ext hval_eq)
      have h2 := Finset.card_le_card_of_injOn _ hmaps2 hinj2
      rw [Finset.card_range] at h2; exact h2

/-- For a basis element of(σ): if λ strictly dominates μ, then a_λ · of(σ) · b_μ = 0. -/
theorem basis_vanishing (n : ℕ) (la mu : Nat.Partition n)
    (hdom : ¬ mu.Dominates la)
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

/-- If μ does not dominate λ (in the dominance order on partitions of n), then
a_λ · x · b_μ = 0 for all x ∈ ℂ[S_n]. This is a generalization of Etingof Lemma 5.13.2
(which assumes λ strictly dominates μ, a stronger condition). -/
theorem Lemma5_13_2
    (n : ℕ) (la mu : Nat.Partition n)
    (hdom : ¬ mu.Dominates la)
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
