import EtingofRepresentationTheory.Chapter5.Definition5_12_1

/-!
# Lemma 5.13.1: Young Projector Linear Functional

For x ∈ ℂ[S_n], we have b_λ · x · a_λ = ℓ_λ(x) · c_λ, where ℓ_λ is a linear
functional on ℂ[S_n]. Here a_λ = Σ_{g ∈ P_λ} g and b_λ = Σ_{g ∈ Q_λ} sign(g) · g,
and c_λ = b_λ · a_λ is the Young symmetrizer.

## Mathlib correspondence

Requires Young symmetrizer infrastructure (Definition 5.12.1).
-/

namespace Etingof

private abbrev G (n : ℕ) := Equiv.Perm (Fin n)

/-- The row symmetrizer absorbs row group elements on the right:
a_λ * of(p) = a_λ for p ∈ P_λ. -/
theorem RowSymmetrizer_mul_of_row {n : ℕ} {la : Nat.Partition n}
    (p : G n) (hp : p ∈ RowSubgroup n la) :
    RowSymmetrizer n la * MonoidAlgebra.of ℂ (G n) p =
      RowSymmetrizer n la := by
  classical
  simp only [RowSymmetrizer]
  rw [Finset.sum_mul]
  simp_rw [← (MonoidAlgebra.of ℂ (G n)).map_mul]
  exact Fintype.sum_equiv (Equiv.mulRight ⟨p, hp⟩) _ _
    (fun g => by simp [Subgroup.coe_mul])

/-- Row group elements are absorbed on the left:
of(p) * a_λ = a_λ for p ∈ P_λ. -/
theorem of_row_mul_RowSymmetrizer {n : ℕ} {la : Nat.Partition n}
    (p : G n) (hp : p ∈ RowSubgroup n la) :
    MonoidAlgebra.of ℂ (G n) p * RowSymmetrizer n la =
      RowSymmetrizer n la := by
  classical
  simp only [RowSymmetrizer]
  rw [Finset.mul_sum]
  simp_rw [← (MonoidAlgebra.of ℂ (G n)).map_mul]
  exact Fintype.sum_equiv (Equiv.mulLeft ⟨p, hp⟩) _ _
    (fun g => by simp [Subgroup.coe_mul])

/-- Column group elements are absorbed on the left of b_λ with sign:
of(q) * b_λ = sign(q) • b_λ for q ∈ Q_λ. -/
theorem of_col_mul_ColumnAntisymmetrizer {n : ℕ} {la : Nat.Partition n}
    (q : G n) (hq : q ∈ ColumnSubgroup n la) :
    MonoidAlgebra.of ℂ (G n) q * ColumnAntisymmetrizer n la =
      ((↑(↑(Equiv.Perm.sign q) : ℤ) : ℂ)) • ColumnAntisymmetrizer n la := by
  classical
  simp only [ColumnAntisymmetrizer]
  rw [Finset.mul_sum, Finset.smul_sum]
  simp_rw [Algebra.mul_smul_comm, ← (MonoidAlgebra.of ℂ (G n)).map_mul, smul_smul]
  refine Fintype.sum_equiv (Equiv.mulLeft ⟨q, hq⟩) _ _ (fun g => ?_)
  simp only [Equiv.coe_mulLeft, Subgroup.coe_mul]
  congr 1
  -- Need: sign(g) = sign(q) * sign(q * g), using sign_mul and sign(q)^2 = 1
  have hsqq : ((↑(↑(Equiv.Perm.sign q) : ℤ) : ℂ)) * ((↑(↑(Equiv.Perm.sign q) : ℤ) : ℂ)) = 1 := by
    have hmul : (Equiv.Perm.sign q : ℤˣ) * (Equiv.Perm.sign q : ℤˣ) = 1 := Int.units_mul_self _
    have h : ((Equiv.Perm.sign q : ℤˣ) : ℤ) * ((Equiv.Perm.sign q : ℤˣ) : ℤ) = 1 := by
      have := congr_arg Units.val hmul
      simp only [Units.val_mul, Units.val_one] at this
      exact this
    exact_mod_cast h
  simp only [Equiv.Perm.sign_mul, Units.val_mul, Int.cast_mul]
  rw [← mul_assoc, hsqq, one_mul]

/-- Column group elements are absorbed on the right of b_λ with sign:
b_λ * of(q) = sign(q) • b_λ for q ∈ Q_λ. -/
theorem ColumnAntisymmetrizer_mul_of_col {n : ℕ} {la : Nat.Partition n}
    (q : G n) (hq : q ∈ ColumnSubgroup n la) :
    ColumnAntisymmetrizer n la * MonoidAlgebra.of ℂ (G n) q =
      ((↑(↑(Equiv.Perm.sign q) : ℤ) : ℂ)) • ColumnAntisymmetrizer n la := by
  classical
  simp only [ColumnAntisymmetrizer]
  rw [Finset.sum_mul, Finset.smul_sum]
  simp_rw [Algebra.smul_mul_assoc, ← (MonoidAlgebra.of ℂ (G n)).map_mul, smul_smul]
  refine Fintype.sum_equiv (Equiv.mulRight ⟨q, hq⟩) _ _ (fun g => ?_)
  simp only [Equiv.coe_mulRight, Subgroup.coe_mul]
  congr 1
  -- Need: sign(g) = sign(q) * sign(g * q), using sign_mul and sign(q)^2 = 1
  have hsqq : ((↑(↑(Equiv.Perm.sign q) : ℤ) : ℂ)) * ((↑(↑(Equiv.Perm.sign q) : ℤ) : ℂ)) = 1 := by
    have hmul : (Equiv.Perm.sign q : ℤˣ) * (Equiv.Perm.sign q : ℤˣ) = 1 := Int.units_mul_self _
    have h : ((Equiv.Perm.sign q : ℤˣ) : ℤ) * ((Equiv.Perm.sign q : ℤˣ) : ℤ) = 1 := by
      have := congr_arg Units.val hmul
      simp only [Units.val_mul, Units.val_one] at this
      exact this
    exact_mod_cast h
  simp only [Equiv.Perm.sign_mul, Units.val_mul, Int.cast_mul]
  -- Goal: sg = sq * (sg * sq). Proof: sq*(sg*sq) = sq*sq*sg = 1*sg = sg
  linear_combination -((↑(↑(Equiv.Perm.sign g.val) : ℤ) : ℂ)) * hsqq

open Pointwise in
/-- Key combinatorial lemma: if σ is not in the set product P_λ · Q_λ, then
there exists a transposition t ∈ P_λ whose conjugate σ⁻¹ · t · σ lies in Q_λ.
This is the pigeonhole argument: two elements in the same row must map to the
same column under σ. -/
-- A swap of two elements in the same row belongs to the row subgroup.
private theorem swap_mem_rowSubgroup {n : ℕ} {la : Nat.Partition n}
    {i j : Fin n} (h : rowOfPos la.sortedParts i.val = rowOfPos la.sortedParts j.val) :
    Equiv.swap i j ∈ RowSubgroup n la := by
  intro k
  simp only [Equiv.swap_apply_def]
  split_ifs with h1 h2
  · subst h1; exact h.symm
  · subst h2; exact h
  · rfl

-- A swap of two elements in the same column belongs to the column subgroup.
private theorem swap_mem_colSubgroup {n : ℕ} {la : Nat.Partition n}
    {i j : Fin n} (h : colOfPos la.sortedParts i.val = colOfPos la.sortedParts j.val) :
    Equiv.swap i j ∈ ColumnSubgroup n la := by
  intro k
  simp only [Equiv.swap_apply_def]
  split_ifs with h1 h2
  · subst h1; exact h.symm
  · subst h2; exact h
  · rfl

-- Conjugation of a swap: σ⁻¹ * swap(i,j) * σ = swap(σ⁻¹(i), σ⁻¹(j)).
private theorem conj_swap_eq {n : ℕ} (σ : Equiv.Perm (Fin n)) (i j : Fin n) :
    σ⁻¹ * Equiv.swap i j * σ = Equiv.swap (σ⁻¹ i) (σ⁻¹ j) :=
  Equiv.trans_swap_trans_symm i j σ

open Pointwise in
private theorem pigeonhole_transposition {n : ℕ} {la : Nat.Partition n}
    (σ : Equiv.Perm (Fin n))
    (hσ : σ ∉ (RowSubgroup n la : Set (Equiv.Perm (Fin n))) *
      (ColumnSubgroup n la : Set (Equiv.Perm (Fin n)))) :
    ∃ t : Equiv.Perm (Fin n), Equiv.Perm.IsSwap t ∧
      t ∈ RowSubgroup n la ∧ σ⁻¹ * t * σ ∈ ColumnSubgroup n la := by
  classical
  -- The map f(k) = (rowOfPos(k), colOfPos(σ⁻¹(k))) is either non-injective (giving the
  -- transposition directly) or injective (forcing σ ∈ P_λ · Q_λ, contradiction).
  -- We show it must be non-injective.
  let parts := la.sortedParts
  let row := fun k : Fin n => rowOfPos parts k.val
  let col := fun k : Fin n => colOfPos parts k.val
  -- Either ∃ distinct i, j in same row with σ⁻¹ images in same column, or not
  by_cases h_exists : ∃ i j : Fin n, i ≠ j ∧ row i = row j ∧ col (σ⁻¹ i) = col (σ⁻¹ j)
  · -- Case 1: We found the pair — construct the transposition
    obtain ⟨i, j, hij, hrow, hcol⟩ := h_exists
    exact ⟨Equiv.swap i j, ⟨i, j, hij, rfl⟩, swap_mem_rowSubgroup hrow,
      by rw [conj_swap_eq]; exact swap_mem_colSubgroup hcol⟩
  · -- Case 2: No such pair exists — derive σ ∈ P_λ · Q_λ, contradicting hσ
    push_neg at h_exists
    -- h_exists : ∀ i j, i ≠ j → row i = row j → col (σ⁻¹ i) ≠ col (σ⁻¹ j)
    -- Rephrase: same column → different rows under σ
    have h_col_inj : ∀ a b : Fin n, a ≠ b → col a = col b →
        row (σ a) ≠ row (σ b) := by
      intro a b hab hcol hrow
      have := h_exists (σ a) (σ b) (by intro h; exact hab (σ.injective h)) hrow
      simp [Equiv.Perm.inv_apply_self] at this
      exact this hcol
    exfalso
    apply hσ
    -- We show σ ∈ P_λ · Q_λ by constructing q ∈ Q_λ and p = σ * q⁻¹ ∈ P_λ
    -- Key auxiliary: parts.sum = n
    have hps : parts.sum = n := by
      show (la.parts.sort (· ≥ ·)).sum = n
      have h1 : (↑(la.parts.sort (· ≥ ·)) : Multiset ℕ) = la.parts := Multiset.sort_eq _ _
      have h2 : (↑(la.parts.sort (· ≥ ·)) : Multiset ℕ).sum =
          (la.parts.sort (· ≥ ·)).sum := Multiset.sum_coe _
      linarith [h2.symm.trans (congrArg Multiset.sum h1), la.parts_sum]
    -- Helper: getD is bounded by list sum
    have getD_le_sum : ∀ (l : List ℕ) (i : ℕ), l.getD i 0 ≤ l.sum := by
      intro l i; induction l generalizing i with
      | nil => simp [List.getD]
      | cons a as ih =>
        cases i with
        | zero => rw [List.getD_cons_zero, List.sum_cons]; omega
        | succ j => rw [List.getD_cons_succ, List.sum_cons]; linarith [ih j]
    -- Helper: rowOfPos is bounded by list length
    have row_valid_gen : ∀ (l : List ℕ) (k : ℕ), k < l.sum → rowOfPos l k < l.length := by
      intro l k hk
      by_contra h; push_neg at h
      have hcol := colOfPos_lt_getD l k hk
      have hgetD : l.getD (rowOfPos l k) 0 = 0 := by
        apply List.getD_eq_default; omega
      omega
    have row_valid : ∀ k : Fin n, rowOfPos parts k.val < parts.length := by
      intro k; exact row_valid_gen parts k.val (by omega)
    -- Cell validity: col(k) < parts.getD (row(σ(k))) 0
    -- Proof: if any k is "bad" (col ≥ parts.getD row 0), we find another with
    -- strictly larger column, giving an unbounded ascending chain. Contradiction.
    have cell_valid : ∀ k : Fin n,
        colOfPos parts k.val < parts.getD (rowOfPos parts (σ k).val) 0 := by
      -- Key sub-lemma: any bad element leads to a strictly worse one
      suffices worse : ∀ (c₀ : ℕ) (k₀ : Fin n),
          parts.getD (rowOfPos parts (σ k₀).val) 0 ≤ colOfPos parts k₀.val →
          c₀ = colOfPos parts k₀.val →
          ∃ k₁ : Fin n,
            parts.getD (rowOfPos parts (σ k₁).val) 0 ≤ colOfPos parts k₁.val ∧
            colOfPos parts k₁.val > c₀ by
        -- Derive contradiction from ascending chain
        by_contra h_bad; push_neg at h_bad; obtain ⟨k₀, hk₀⟩ := h_bad
        have chain : ∀ m : ℕ, ∃ k' : Fin n,
            parts.getD (rowOfPos parts (σ k').val) 0 ≤ colOfPos parts k'.val ∧
            colOfPos parts k'.val ≥ colOfPos parts k₀.val + m := by
          intro m; induction m with
          | zero => exact ⟨k₀, hk₀, le_refl _⟩
          | succ m ih =>
            obtain ⟨k', hk'_bad, hge⟩ := ih
            obtain ⟨k'', hk'', hgt⟩ := worse _ k' hk'_bad rfl
            exact ⟨k'', hk'', by omega⟩
        obtain ⟨k', _, hge⟩ := chain n
        have hcol_bound := (colOfPos_lt_getD parts k'.val (by omega)).trans_le
          (getD_le_sum parts _)
        omega
      -- Prove "worse": given bad k₀ with col = c₀, find k₁ with col > c₀ also bad
      intro c₀ k₀ hk₀_bad hc₀_eq
      -- S_c: positions in column c₀
      let S_c := Finset.univ.filter (fun k : Fin n => colOfPos parts k.val = c₀)
      -- R_c: rows reaching column c₀
      let R_c := (Finset.range parts.length).filter (fun r => c₀ < parts.getD r 0)
      -- σ-image: rows hit by σ on S_c
      let σ_img := S_c.image (fun k => rowOfPos parts (σ k).val)
      -- k₀ ∈ S_c
      have hk₀_S : k₀ ∈ S_c := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc₀_eq.symm⟩
      -- row(σ(k₀)) ∈ σ_img
      have hr₀_img : rowOfPos parts (σ k₀).val ∈ σ_img :=
        Finset.mem_image.mpr ⟨k₀, hk₀_S, rfl⟩
      -- row(σ(k₀)) ∉ R_c (since k₀ is bad)
      have hr₀_not_Rc : rowOfPos parts (σ k₀).val ∉ R_c := by
        intro hmem
        have := (Finset.mem_filter.mp hmem).2
        omega
      -- |S_c| ≤ |R_c| via injection k ↦ row(k)
      have hcard_S_le_R : S_c.card ≤ R_c.card := by
        apply Finset.card_le_card_of_injOn (fun k : Fin n => rowOfPos parts k.val)
        · intro k hk
          have hk_col := (Finset.mem_filter.mp (Finset.mem_coe.mp hk)).2
          refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (row_valid k), ?_⟩
          rw [← hk_col]; exact colOfPos_lt_getD parts k.val (by omega)
        · intro k₁ hk₁ k₂ hk₂ heq
          have hk₁_col := (Finset.mem_filter.mp (Finset.mem_coe.mp hk₁)).2
          have hk₂_col := (Finset.mem_filter.mp (Finset.mem_coe.mp hk₂)).2
          exact Fin.val_injective (rowOfPos_colOfPos_injective parts k₁.val k₂.val
            (by omega) (by omega) heq (by rw [hk₁_col, hk₂_col]))
      -- |σ_img| = |S_c| (σ-row is injective on S_c by h_col_inj)
      have hcard_img : σ_img.card = S_c.card := by
        apply Finset.card_image_of_injOn
        intro k₁ hk₁ k₂ hk₂ heq
        have hk₁_col := (Finset.mem_filter.mp (Finset.mem_coe.mp hk₁)).2
        have hk₂_col := (Finset.mem_filter.mp (Finset.mem_coe.mp hk₂)).2
        by_contra hne
        have hcol_eq : col k₁ = col k₂ := by
          show colOfPos parts k₁.val = colOfPos parts k₂.val
          rw [hk₁_col, hk₂_col]
        exact h_col_inj k₁ k₂ hne hcol_eq heq
      -- Some r* ∈ R_c \ σ_img
      have ⟨r_star, hr_star_Rc, hr_star_not_img⟩ : ∃ r ∈ R_c, r ∉ σ_img := by
        by_contra h_all; push_neg at h_all
        have h_union := Finset.card_le_card
          (Finset.union_subset h_all (Finset.singleton_subset_iff.mpr hr₀_img))
        rw [Finset.card_union_of_disjoint
          (Finset.disjoint_singleton_right.mpr hr₀_not_Rc),
          Finset.card_singleton] at h_union
        omega
      have hr_star_wide : c₀ < parts.getD r_star 0 :=
        (Finset.mem_filter.mp hr_star_Rc).2
      -- T_rs: positions in row r*
      let T_rs := Finset.univ.filter (fun i : Fin n => rowOfPos parts i.val = r_star)
      -- σ⁻¹ maps T_rs to positions with distinct columns
      have h_σinv_inj : Set.InjOn (fun i : Fin n => colOfPos parts (σ⁻¹ i).val) ↑T_rs := by
        intro i hi j hj heq
        have hi' := (Finset.mem_filter.mp (Finset.mem_coe.mp hi)).2
        have hj' := (Finset.mem_filter.mp (Finset.mem_coe.mp hj)).2
        by_contra hne
        have hrow_eq : row i = row j := by
          show rowOfPos parts i.val = rowOfPos parts j.val
          rw [hi', hj']
        exact h_exists i j hne hrow_eq heq
      -- None of σ⁻¹-columns is c₀
      have h_no_c : ∀ i ∈ T_rs, colOfPos parts (σ⁻¹ i).val ≠ c₀ := by
        intro i hi habs
        have hi_row := (Finset.mem_filter.mp hi).2
        apply hr_star_not_img
        refine Finset.mem_image.mpr ⟨σ⁻¹ i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, habs⟩, ?_⟩
        have happ : σ (σ⁻¹ i) = i := by show (σ * σ⁻¹) i = i; simp
        rw [show rowOfPos parts (σ (σ⁻¹ i)).val = rowOfPos parts i.val from by
          congr 1; exact congrArg Fin.val happ]
        exact hi_row
      -- ci: image of σ⁻¹-columns on T_rs
      let ci := T_rs.image (fun i => colOfPos parts (σ⁻¹ i).val)
      have hci_card : ci.card = T_rs.card := Finset.card_image_of_injOn h_σinv_inj
      -- |T_rs| ≥ parts.getD r_star 0
      have hTrs_large : parts.getD r_star 0 ≤ T_rs.card := by
        have pos_in_row : ∀ c' : ℕ, c' < parts.getD r_star 0 →
            ∃ k : Fin n, k ∈ T_rs ∧ colOfPos parts k.val = c' := by
          intro c' hc'
          obtain ⟨pos, hpos, hrow, hcol⟩ := exists_pos_of_cell parts r_star c' hc'
          exact ⟨⟨pos, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrow⟩, hcol⟩
        choose f hf_mem hf_col using pos_in_row
        rw [← Fintype.card_fin (parts.getD r_star 0)]
        rw [← Finset.card_univ (α := Fin (parts.getD r_star 0))]
        apply Finset.card_le_card_of_injOn
          (fun c' : Fin (parts.getD r_star 0) => f c'.val c'.isLt)
        · intro c' _; exact hf_mem c'.val c'.isLt
        · intro c₁ _ c₂ _ heq
          have h1 := hf_col c₁.val c₁.isLt
          have h2 := hf_col c₂.val c₂.isLt
          have hfinval : (f c₁.val c₁.isLt).val = (f c₂.val c₂.isLt).val :=
            congrArg Fin.val heq
          -- colOfPos is the same for equal positions, so c₁.val = c₂.val
          have : c₁.val = c₂.val := by rw [← h1, ← h2, hfinval]
          exact Fin.ext this
      -- ci has ≥ parts[r*] elements, all ≠ c₀; can't all fit in {0,...,parts[r*]-1}\{c₀}
      have ⟨c', hc'_mem, hc'_large⟩ : ∃ c' ∈ ci, parts.getD r_star 0 ≤ c' := by
        by_contra h_all; push_neg at h_all
        have hsub : ci ⊆ Finset.range (parts.getD r_star 0) \ {c₀} := by
          intro x hx
          refine Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr (h_all x hx), ?_⟩
          rw [Finset.mem_singleton]
          obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
          exact h_no_c i hi
        have h1 := Finset.card_le_card hsub
        have hsing_sub : {c₀} ⊆ Finset.range (parts.getD r_star 0) :=
          Finset.singleton_subset_iff.mpr (Finset.mem_range.mpr hr_star_wide)
        rw [Finset.card_sdiff_of_subset hsing_sub, Finset.card_range,
          Finset.card_singleton] at h1
        omega
      -- Extract the bad k₁
      obtain ⟨i, hi_T, hi_col⟩ := Finset.mem_image.mp hc'_mem
      have hi_row := (Finset.mem_filter.mp hi_T).2
      refine ⟨σ⁻¹ i, ?_, ?_⟩
      · -- k₁ is bad
        show parts.getD (rowOfPos parts (σ (σ⁻¹ i)).val) 0 ≤ colOfPos parts (σ⁻¹ i).val
        have happ : σ (σ⁻¹ i) = i := by
          show (σ * σ⁻¹) i = i; simp
        rw [show (σ (σ⁻¹ i)).val = i.val from congrArg Fin.val happ, hi_row]
        linarith
      · -- col(k₁) > c₀
        show c₀ < colOfPos parts (σ⁻¹ i).val
        linarith
    -- Construct q: q(k) is the unique position with row = row(σ(k)), col = col(k)
    have q_spec : ∀ k : Fin n, ∃ k' : Fin n,
        rowOfPos parts k'.val = rowOfPos parts (σ k).val ∧
        colOfPos parts k'.val = colOfPos parts k.val := by
      intro k
      obtain ⟨pos, hpos, hrow, hcol⟩ := exists_pos_of_cell parts
        (rowOfPos parts (σ k).val) (colOfPos parts k.val) (cell_valid k)
      exact ⟨⟨pos, hps ▸ hpos⟩, hrow, hcol⟩
    choose q_fun hq_row hq_col using q_spec
    -- q_fun is injective (using h_exists: same row → different columns under σ⁻¹)
    have q_inj : Function.Injective q_fun := by
      intro k₁ k₂ heq
      by_contra hne
      have hσne : σ k₁ ≠ σ k₂ := fun h => hne (σ.injective h)
      have hval : (q_fun k₁).val = (q_fun k₂).val := congrArg Fin.val heq
      have hrow_σ : row (σ k₁) = row (σ k₂) := by
        show rowOfPos parts (σ k₁).val = rowOfPos parts (σ k₂).val
        rw [← hq_row k₁, ← hq_row k₂, hval]
      have hcol_k : col k₁ = col k₂ := by
        show colOfPos parts k₁.val = colOfPos parts k₂.val
        rw [← hq_col k₁, ← hq_col k₂, hval]
      have h_absurd := h_exists (σ k₁) (σ k₂) hσne hrow_σ
      simp only [Equiv.Perm.inv_apply_self] at h_absurd
      exact h_absurd hcol_k
    -- q_fun is surjective (injective endomorphism of finite type)
    have q_surj := (Finite.injective_iff_surjective).mp q_inj
    -- Create the permutation q
    let q_perm : Equiv.Perm (Fin n) := Equiv.ofBijective q_fun ⟨q_inj, q_surj⟩
    -- q preserves columns
    have hq_col_sub : q_perm ∈ ColumnSubgroup n la := by
      intro k
      show colOfPos parts (q_fun k).val = colOfPos parts k.val
      exact hq_col k
    -- p = σ * q⁻¹ preserves rows
    have hp_row : σ * q_perm⁻¹ ∈ RowSubgroup n la := by
      intro k
      simp only [Equiv.Perm.coe_mul, Function.comp_apply]
      have h := hq_row (q_perm⁻¹ k)
      have hqq : q_fun (q_perm⁻¹ k) = k := by
        show q_perm (q_perm⁻¹ k) = k; exact q_perm.apply_symm_apply k
      rw [hqq] at h; exact h.symm
    -- σ = p * q ∈ P * Q
    refine Set.mem_mul.mpr ⟨σ * q_perm⁻¹, hp_row, q_perm, hq_col_sub, ?_⟩
    group

/-- For σ ∈ Q_λ · P_λ with σ = q · p, the sandwiched product equals sign(q) • c_λ.
(With c_λ = b_λ · a_λ.) -/
private theorem sandwich_mem {n : ℕ} {la : Nat.Partition n}
    (q : Equiv.Perm (Fin n)) (hq : q ∈ ColumnSubgroup n la)
    (p : Equiv.Perm (Fin n)) (hp : p ∈ RowSubgroup n la) :
    ColumnAntisymmetrizer n la * MonoidAlgebra.of ℂ _ (q * p) * RowSymmetrizer n la =
      ((↑(↑(Equiv.Perm.sign q) : ℤ) : ℂ)) • YoungSymmetrizer n la := by
  rw [map_mul (MonoidAlgebra.of ℂ _)]
  simp only [mul_assoc]
  rw [of_row_mul_RowSymmetrizer p hp,
    ← mul_assoc (ColumnAntisymmetrizer n la), ColumnAntisymmetrizer_mul_of_col q hq,
    Algebra.smul_mul_assoc, YoungSymmetrizer]

open Pointwise in
/-- For σ ∉ Q_λ · P_λ, a sign-reversing involution shows b_λ * of(σ) * a_λ = 0.

The proof applies the existing pigeonhole to σ⁻¹ (since σ ∉ Q·P ↔ σ⁻¹ ∉ P·Q),
obtaining t ∈ P_λ with u = σ·t·σ⁻¹ ∈ Q_λ. Then b·of(σ)·a = sign(u)·(b·of(σ)·a) = -y. -/
private theorem sandwich_not_mem {n : ℕ} {la : Nat.Partition n}
    (σ : Equiv.Perm (Fin n))
    (hσ : σ ∉ (ColumnSubgroup n la : Set (Equiv.Perm (Fin n))) *
      (RowSubgroup n la : Set (Equiv.Perm (Fin n)))) :
    ColumnAntisymmetrizer n la * MonoidAlgebra.of ℂ _ σ * RowSymmetrizer n la = 0 := by
  classical
  -- σ ∉ Q·P ↔ σ⁻¹ ∉ P·Q. Apply existing pigeonhole to σ⁻¹.
  have hσ_inv : σ⁻¹ ∉ (RowSubgroup n la : Set (Equiv.Perm (Fin n))) *
      (ColumnSubgroup n la : Set (Equiv.Perm (Fin n))) := by
    intro hmem
    apply hσ
    obtain ⟨p, hp, q, hq, hpq⟩ := Set.mem_mul.mp hmem
    exact Set.mem_mul.mpr ⟨q⁻¹, (ColumnSubgroup n la).inv_mem hq,
      p⁻¹, (RowSubgroup n la).inv_mem hp,
      show q⁻¹ * p⁻¹ = σ from by rw [← mul_inv_rev, hpq, inv_inv]⟩
  obtain ⟨t, ht_swap, ht_row, ht_col'⟩ := pigeonhole_transposition σ⁻¹ hσ_inv
  -- ht_col' : (σ⁻¹)⁻¹ * t * σ⁻¹ = σ * t * σ⁻¹ ∈ Q_λ
  set u := σ * t * σ⁻¹ with hu_def
  have hu_col : u ∈ ColumnSubgroup n la := by
    have : σ⁻¹⁻¹ = σ := inv_inv σ
    rw [hu_def, ← this]; exact ht_col'
  -- Key relation: σ * t = u * σ
  have hσt : σ * t = u * σ := by simp [hu_def]; group
  -- sign(u) = -1 (u is a conjugate of the transposition t)
  have hsign_u : (↑(↑(Equiv.Perm.sign u) : ℤ) : ℂ) = -1 := by
    have hsign_t : Equiv.Perm.sign t = -1 := by
      obtain ⟨x, z, hxz, ht_eq⟩ := ht_swap; rw [ht_eq]; exact Equiv.Perm.sign_swap hxz
    have : Equiv.Perm.sign u = -1 := by
      show Equiv.Perm.sign (σ * t * σ⁻¹) = -1
      rw [map_mul, map_mul, hsign_t, Equiv.Perm.sign_inv]
      simp [mul_comm, Int.units_mul_self]
    simp [this]
  -- y = sign(u) • y, via: insert of(t) after of(σ) (absorbed by a_λ),
  -- rewrite σ·t = u·σ, absorb of(u) into b_λ with sign.
  -- Show: b * of(σ) * a = sign(u) • (b * of(σ) * a), then use sign(u) = -1.
  suffices heq : ColumnAntisymmetrizer n la * MonoidAlgebra.of ℂ _ σ * RowSymmetrizer n la =
      ((↑(↑(Equiv.Perm.sign u) : ℤ) : ℂ)) •
        (ColumnAntisymmetrizer n la * MonoidAlgebra.of ℂ _ σ * RowSymmetrizer n la) by
    -- x = sign(u) • x = -x, so x = 0
    rw [hsign_u, neg_one_smul] at heq
    -- heq : x = -x. Pointwise: x g = -(x g), so 2*(x g) = 0, so x g = 0.
    have hg : ∀ g, (ColumnAntisymmetrizer n la * MonoidAlgebra.of ℂ _ σ *
        RowSymmetrizer n la) g = 0 := by
      intro g
      have := Finsupp.ext_iff.mp heq g
      rw [Finsupp.neg_apply] at this
      exact (mul_eq_zero.mp (show (2 : ℂ) * _ = 0 by linear_combination this)).resolve_left (by norm_num)
    exact Finsupp.ext hg
  -- Proof of x = sign(u) • x:
  -- Insert of(t) before a_λ (absorbed), combine of(σ)*of(t)=of(σ*t)=of(u*σ),
  -- split of(u)*of(σ), absorb of(u) into b_λ with sign.
  have h1 : ColumnAntisymmetrizer n la * MonoidAlgebra.of ℂ _ σ * RowSymmetrizer n la =
      ColumnAntisymmetrizer n la * MonoidAlgebra.of ℂ _ (σ * t) * RowSymmetrizer n la := by
    conv_lhs => rw [← of_row_mul_RowSymmetrizer t ht_row]
    rw [map_mul (MonoidAlgebra.of ℂ _) σ t]
    simp only [mul_assoc]
  have h2 : ColumnAntisymmetrizer n la * MonoidAlgebra.of ℂ _ (u * σ) * RowSymmetrizer n la =
      ((↑(↑(Equiv.Perm.sign u) : ℤ) : ℂ)) •
        (ColumnAntisymmetrizer n la * MonoidAlgebra.of ℂ _ σ * RowSymmetrizer n la) := by
    rw [map_mul (MonoidAlgebra.of ℂ _)]
    simp only [mul_assoc]
    rw [← mul_assoc (ColumnAntisymmetrizer n la), ColumnAntisymmetrizer_mul_of_col u hu_col,
      Algebra.smul_mul_assoc]
  exact h1.trans (hσt ▸ h2)

/-- Dual sandwich (member case): for p ∈ P_λ, q ∈ Q_λ,
a_λ * of(p*q) * b_λ = sign(q) • (a_λ * b_λ). -/
private theorem dual_sandwich_mem {n : ℕ} {la : Nat.Partition n}
    (p : Equiv.Perm (Fin n)) (hp : p ∈ RowSubgroup n la)
    (q : Equiv.Perm (Fin n)) (hq : q ∈ ColumnSubgroup n la) :
    RowSymmetrizer n la * MonoidAlgebra.of ℂ _ (p * q) * ColumnAntisymmetrizer n la =
      ((↑(↑(Equiv.Perm.sign q) : ℤ) : ℂ)) •
        (RowSymmetrizer n la * ColumnAntisymmetrizer n la) := by
  rw [map_mul (MonoidAlgebra.of ℂ _)]
  simp only [mul_assoc]
  rw [of_col_mul_ColumnAntisymmetrizer q hq, Algebra.mul_smul_comm, Algebra.mul_smul_comm]
  congr 1
  rw [← mul_assoc, RowSymmetrizer_mul_of_row p hp]

open Pointwise in
/-- Dual sandwich (non-member case): for σ ∉ P_λ · Q_λ,
a_λ * of(σ) * b_λ = 0. Uses the same pigeonhole argument as sandwich_not_mem. -/
private theorem dual_sandwich_not_mem {n : ℕ} {la : Nat.Partition n}
    (σ : Equiv.Perm (Fin n))
    (hσ : σ ∉ (RowSubgroup n la : Set (Equiv.Perm (Fin n))) *
      (ColumnSubgroup n la : Set (Equiv.Perm (Fin n)))) :
    RowSymmetrizer n la * MonoidAlgebra.of ℂ _ σ * ColumnAntisymmetrizer n la = 0 := by
  classical
  obtain ⟨t, ht_swap, ht_row, ht_col'⟩ := pigeonhole_transposition σ hσ
  set u := σ⁻¹ * t * σ with hu_def
  have hu_col : u ∈ ColumnSubgroup n la := ht_col'
  have hσt : t * σ = σ * u := by simp [hu_def]; group
  have hsign_u : (↑(↑(Equiv.Perm.sign u) : ℤ) : ℂ) = -1 := by
    have hsign_t : Equiv.Perm.sign t = -1 := by
      obtain ⟨x, z, hxz, ht_eq⟩ := ht_swap; rw [ht_eq]; exact Equiv.Perm.sign_swap hxz
    have : Equiv.Perm.sign u = -1 := by
      show Equiv.Perm.sign (σ⁻¹ * t * σ) = -1
      rw [map_mul, map_mul, hsign_t, Equiv.Perm.sign_inv]
      simp [mul_comm, Int.units_mul_self]
    simp [this]
  suffices heq : RowSymmetrizer n la * MonoidAlgebra.of ℂ _ σ * ColumnAntisymmetrizer n la =
      ((↑(↑(Equiv.Perm.sign u) : ℤ) : ℂ)) •
        (RowSymmetrizer n la * MonoidAlgebra.of ℂ _ σ * ColumnAntisymmetrizer n la) by
    rw [hsign_u, neg_one_smul] at heq
    have hg : ∀ g, (RowSymmetrizer n la * MonoidAlgebra.of ℂ _ σ *
        ColumnAntisymmetrizer n la) g = 0 := by
      intro g
      have := Finsupp.ext_iff.mp heq g
      rw [Finsupp.neg_apply] at this
      exact (mul_eq_zero.mp (show (2 : ℂ) * _ = 0 by linear_combination this)).resolve_left
        (by norm_num)
    exact Finsupp.ext hg
  have h1 : RowSymmetrizer n la * MonoidAlgebra.of ℂ _ σ * ColumnAntisymmetrizer n la =
      RowSymmetrizer n la * MonoidAlgebra.of ℂ _ (t * σ) * ColumnAntisymmetrizer n la := by
    conv_lhs => rw [← RowSymmetrizer_mul_of_row t ht_row]
    rw [map_mul (MonoidAlgebra.of ℂ _) t σ]
    simp only [mul_assoc]
  have h2 : RowSymmetrizer n la * MonoidAlgebra.of ℂ _ (σ * u) * ColumnAntisymmetrizer n la =
      ((↑(↑(Equiv.Perm.sign u) : ℤ) : ℂ)) •
        (RowSymmetrizer n la * MonoidAlgebra.of ℂ _ σ * ColumnAntisymmetrizer n la) := by
    rw [map_mul (MonoidAlgebra.of ℂ _)]
    simp only [mul_assoc]
    rw [of_col_mul_ColumnAntisymmetrizer u hu_col, Algebra.mul_smul_comm, Algebra.mul_smul_comm]
  exact h1.trans (hσt ▸ h2)

end Etingof

open Etingof Pointwise in
/-- For x ∈ ℂ[S_n], b_λ · x · a_λ is a scalar multiple of c_λ = b_λ · a_λ.
More precisely, there exists a linear functional ℓ_λ on ℂ[S_n] such that
b_λ * x * a_λ = ℓ_λ(x) • c_λ for all x.
(Etingof Lemma 5.13.1, adapted for c_λ = b_λ · a_λ convention) -/
theorem Etingof.Lemma5_13_1
    (n : ℕ) (la : Nat.Partition n) :
    ∃ ℓ : MonoidAlgebra ℂ (Equiv.Perm (Fin n)) →ₗ[ℂ] ℂ,
      ∀ x, ColumnAntisymmetrizer n la * x * RowSymmetrizer n la =
        ℓ x • YoungSymmetrizer n la := by
  classical
  -- For each basis element σ, compute the coefficient
  have basis_mul : ∀ σ : Equiv.Perm (Fin n), ∃ coeff : ℂ,
      ColumnAntisymmetrizer n la * MonoidAlgebra.of ℂ _ σ * RowSymmetrizer n la =
        coeff • YoungSymmetrizer n la := by
    intro σ
    by_cases hmem : σ ∈ (ColumnSubgroup n la : Set (Equiv.Perm (Fin n))) *
        (RowSubgroup n la : Set (Equiv.Perm (Fin n)))
    · obtain ⟨q, hq, p, hp, hqp⟩ := Set.mem_mul.mp hmem
      exact ⟨↑(↑(Equiv.Perm.sign q) : ℤ), hqp ▸ sandwich_mem q hq p hp⟩
    · exact ⟨0, by rw [zero_smul]; exact sandwich_not_mem σ hmem⟩
  -- Extract coefficient function and build linear functional
  choose f hf using basis_mul
  let ℓ : MonoidAlgebra ℂ (Equiv.Perm (Fin n)) →ₗ[ℂ] ℂ :=
    Finsupp.lsum ℂ (fun σ => f σ • (LinearMap.id : ℂ →ₗ[ℂ] ℂ))
  refine ⟨ℓ, fun x => ?_⟩
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy =>
    simp only [mul_add, add_mul, map_add, add_smul]
    exact congr_arg₂ (· + ·) hx hy
  | single σ r =>
    have hℓ : ℓ (Finsupp.single σ r) = f σ * r := by
      change (Finsupp.lsum ℂ (fun σ => f σ • (LinearMap.id : ℂ →ₗ[ℂ] ℂ)))
        (Finsupp.single σ r) = f σ * r
      rw [Finsupp.lsum_single, LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul]
    have hsingle : (Finsupp.single σ r : MonoidAlgebra ℂ _) = r • MonoidAlgebra.of ℂ _ σ := by
      simp [MonoidAlgebra.of_apply, mul_one]
    conv_lhs => rw [hsingle]
    rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, hf, smul_smul, hℓ, mul_comm]

open Etingof Pointwise in
/-- Dual sandwich: a_λ * x * b_λ is a scalar multiple of a_λ * b_λ.
There exists a linear functional ℓ' on ℂ[S_n] such that
a_λ * x * b_λ = ℓ'(x) • (a_λ * b_λ) for all x.
This is the P/Q-swapped version of Lemma 5.13.1. -/
theorem Etingof.Lemma5_13_1_dual
    (n : ℕ) (la : Nat.Partition n) :
    ∃ ℓ : MonoidAlgebra ℂ (Equiv.Perm (Fin n)) →ₗ[ℂ] ℂ,
      ∀ x, RowSymmetrizer n la * x * ColumnAntisymmetrizer n la =
        ℓ x • (RowSymmetrizer n la * ColumnAntisymmetrizer n la) := by
  classical
  have basis_mul : ∀ σ : Equiv.Perm (Fin n), ∃ coeff : ℂ,
      RowSymmetrizer n la * MonoidAlgebra.of ℂ _ σ * ColumnAntisymmetrizer n la =
        coeff • (RowSymmetrizer n la * ColumnAntisymmetrizer n la) := by
    intro σ
    by_cases hmem : σ ∈ (RowSubgroup n la : Set (Equiv.Perm (Fin n))) *
        (ColumnSubgroup n la : Set (Equiv.Perm (Fin n)))
    · obtain ⟨p, hp, q, hq, hpq⟩ := Set.mem_mul.mp hmem
      exact ⟨↑(↑(Equiv.Perm.sign q) : ℤ), hpq ▸ dual_sandwich_mem p hp q hq⟩
    · exact ⟨0, by rw [zero_smul]; exact dual_sandwich_not_mem σ hmem⟩
  choose f hf using basis_mul
  let ℓ : MonoidAlgebra ℂ (Equiv.Perm (Fin n)) →ₗ[ℂ] ℂ :=
    Finsupp.lsum ℂ (fun σ => f σ • (LinearMap.id : ℂ →ₗ[ℂ] ℂ))
  refine ⟨ℓ, fun x => ?_⟩
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy =>
    simp only [mul_add, add_mul, map_add, add_smul]
    exact congr_arg₂ (· + ·) hx hy
  | single σ r =>
    have hℓ : ℓ (Finsupp.single σ r) = f σ * r := by
      change (Finsupp.lsum ℂ (fun σ => f σ • (LinearMap.id : ℂ →ₗ[ℂ] ℂ)))
        (Finsupp.single σ r) = f σ * r
      rw [Finsupp.lsum_single, LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul]
    have hsingle : (Finsupp.single σ r : MonoidAlgebra ℂ _) = r • MonoidAlgebra.of ℂ _ σ := by
      simp [MonoidAlgebra.of_apply, mul_one]
    conv_lhs => rw [hsingle]
    rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, hf, smul_smul, hℓ, mul_comm]
