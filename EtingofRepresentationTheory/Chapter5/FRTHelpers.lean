import EtingofRepresentationTheory.Chapter5.Definition5_14_2
import EtingofRepresentationTheory.Chapter5.SYTFintype

/-!
# Frame–Robinson–Thrall Helper Infrastructure

This file provides hook length definitions, outer corner infrastructure, and the
key decomposition lemmas for the Frame–Robinson–Thrall theorem (Theorem 5.17.1).

## Strategy: Induction via the branching rule

For the empty partition (n = 0): |SYT| = 1, hook product = 1, and 0! = 1.

For n ≥ 1: The largest entry in a standard Young tableau must occupy an outer
corner. Removing that cell gives an SYT of a partition of n-1. This yields:

  |SYT(n, λ)| = Σ_{c outer corner} |SYT(n-1, λ\c)|

Combined with the hook length recurrence, induction gives the result.
-/

/-! ## Hook length definitions -/

/-- The hook length at cell (i, j) of a Young diagram.
For a cell (i,j), the hook consists of all cells directly to the right in the
same row, all cells directly below in the same column, plus the cell itself.
h(i,j) = (rowLen i - j) + (colLen j - i) - 1 -/
def YoungDiagram.hookLength (μ : YoungDiagram) (i j : ℕ) : ℕ :=
  μ.rowLen i + μ.colLen j - i - j - 1

/-- The product of all hook lengths of a Young diagram. -/
noncomputable def YoungDiagram.hookLengthProduct (μ : YoungDiagram) : ℕ :=
  μ.cells.prod (fun c => μ.hookLength c.1 c.2)

/-! ## Hook length properties -/

/-- The hook length at a cell in the diagram is positive. -/
lemma YoungDiagram.hookLength_pos (μ : YoungDiagram) (i j : ℕ) (h : (i, j) ∈ μ.cells) :
    0 < μ.hookLength i j := by
  simp [YoungDiagram.hookLength]
  rw [YoungDiagram.mem_cells] at h
  have hi := YoungDiagram.mem_iff_lt_colLen.mp h
  have hj := YoungDiagram.mem_iff_lt_rowLen.mp h
  omega

/-- The hook length product of any Young diagram is positive. -/
lemma YoungDiagram.hookLengthProduct_pos (μ : YoungDiagram) :
    0 < μ.hookLengthProduct := by
  unfold YoungDiagram.hookLengthProduct
  apply Finset.prod_pos
  intro c hc
  exact YoungDiagram.hookLength_pos μ c.1 c.2 hc

/-! ## Outer corner infrastructure -/

/-- A cell (i,j) is an outer corner of μ if it is in μ but removing it
leaves a valid Young diagram. Equivalently: (i,j) ∈ μ, (i+1,j) ∉ μ, (i,j+1) ∉ μ. -/
def YoungDiagram.IsOuterCorner (μ : YoungDiagram) (i j : ℕ) : Prop :=
  (i, j) ∈ μ.cells ∧ (i + 1, j) ∉ μ.cells ∧ (i, j + 1) ∉ μ.cells

/-- The finset of outer corners of a Young diagram. -/
noncomputable def YoungDiagram.outerCorners (μ : YoungDiagram) : Finset (ℕ × ℕ) :=
  μ.cells.filter fun c => (c.1 + 1, c.2) ∉ μ.cells ∧ (c.1, c.2 + 1) ∉ μ.cells

theorem YoungDiagram.mem_outerCorners {μ : YoungDiagram} {c : ℕ × ℕ} :
    c ∈ μ.outerCorners ↔ μ.IsOuterCorner c.1 c.2 := by
  simp [outerCorners, IsOuterCorner, Finset.mem_filter]

/-- Every nonempty Young diagram has at least one outer corner. -/
theorem YoungDiagram.outerCorners_nonempty (μ : YoungDiagram) (h : μ.cells.Nonempty) :
    μ.outerCorners.Nonempty := by
  -- The cell with maximum i+j sum is an outer corner
  obtain ⟨c, hc_mem, hc_max⟩ := Finset.exists_max_image μ.cells
    (fun c : ℕ × ℕ => c.1 + c.2) h
  refine ⟨c, mem_outerCorners.mpr ⟨hc_mem, ?_, ?_⟩⟩
  · intro h1
    have := hc_max _ h1
    simp at this
  · intro h1
    have := hc_max _ h1
    simp at this

/-! ## Corner removal -/

/-- Removing an outer corner from a Young diagram gives a valid Young diagram.
The resulting diagram has all cells of μ except (i,j), and remains a lower set
because (i,j) is maximal (no cell below or to the right). -/
noncomputable def YoungDiagram.removeCorner (μ : YoungDiagram) (i j : ℕ)
    (hc : μ.IsOuterCorner i j) : YoungDiagram where
  cells := μ.cells.erase (i, j)
  isLowerSet := by
    -- IsLowerSet (via @[to_dual]): ∀ ⦃a b⦄, b ≤ a → a ∈ s → b ∈ s
    intro a b hle hmem
    simp only [Finset.mem_coe, Finset.mem_erase] at hmem ⊢
    -- hle : b ≤ a, hmem : a ≠ (i,j) ∧ a ∈ μ.cells, goal : b ≠ (i,j) ∧ b ∈ μ.cells
    have hle' := Prod.mk_le_mk.mp hle
    have ha_μ : a ∈ μ := hmem.2
    have hb_μ : b ∈ μ := μ.up_left_mem hle'.1 hle'.2 ha_μ
    refine ⟨?_, hb_μ⟩
    intro heq
    -- b = (i,j), b ≤ a, a ∈ μ, a ≠ (i,j)
    rw [heq] at hle'
    obtain ⟨_, hbelow, hright⟩ := hc
    have hne := hmem.1
    rcases Nat.lt_or_eq_of_le hle'.1 with h | h
    · exact hbelow (μ.up_left_mem (Nat.succ_le_of_lt h) hle'.2 ha_μ)
    · rcases Nat.lt_or_eq_of_le hle'.2 with h' | h'
      · exact hright (μ.up_left_mem (le_of_eq h) (Nat.succ_le_of_lt h') ha_μ)
      · exact absurd (show a = (i, j) from Prod.ext h.symm h'.symm) hne

theorem YoungDiagram.removeCorner_card (μ : YoungDiagram) (i j : ℕ)
    (hc : μ.IsOuterCorner i j) :
    (μ.removeCorner i j hc).cells.card = μ.cells.card - 1 := by
  simp only [removeCorner]
  exact Finset.card_erase_of_mem hc.1

/-! ## Partition-level corner removal -/

/-- The number of cells in `cellsOfRowLens w` equals the sum of `w`. -/
private theorem cellsOfRowLens_card : ∀ w : List ℕ,
    (YoungDiagram.cellsOfRowLens w).card = w.sum := by
  intro w
  induction w with
  | nil => simp [YoungDiagram.cellsOfRowLens]
  | cons a as ih =>
    rw [YoungDiagram.cellsOfRowLens, List.sum_cons]
    rw [Finset.card_union_of_disjoint]
    · simp [ih]
    · rw [Finset.disjoint_left]
      intro x hx hx'
      simp only [Finset.mem_product, Finset.mem_singleton, Finset.mem_range] at hx
      rw [Finset.mem_map] at hx'
      obtain ⟨y, _, hy⟩ := hx'
      have : x.1 = 0 := hx.1
      have : x.1 = y.1 + 1 := by
        have := congr_arg Prod.fst hy
        simp [Function.Embedding.prodMap] at this
        omega
      omega

/-- The Young diagram of a partition of n has exactly n cells. -/
theorem Nat.Partition.toYoungDiagram_card {n : ℕ} (la : Nat.Partition n) :
    la.toYoungDiagram.cells.card = n := by
  unfold Nat.Partition.toYoungDiagram YoungDiagram.ofRowLens
  rw [cellsOfRowLens_card]
  have : (la.parts.sort (· ≥ ·) : Multiset ℕ).sum = la.parts.sum :=
    congrArg Multiset.sum (Multiset.sort_eq la.parts (· ≥ ·))
  rw [Multiset.sum_coe] at this
  rw [this, la.parts_sum]

/-! ## Key decomposition lemmas for FRT -/

/-- The sum of row lengths of a Young diagram equals the number of cells. -/
private lemma YoungDiagram.rowLens_sum (μ : YoungDiagram) :
    μ.rowLens.sum = μ.cells.card := by
  have h := cellsOfRowLens_card μ.rowLens
  have : YoungDiagram.cellsOfRowLens μ.rowLens =
    (YoungDiagram.ofRowLens μ.rowLens μ.rowLens_sorted).cells := rfl
  rw [this] at h
  rw [show YoungDiagram.ofRowLens μ.rowLens μ.rowLens_sorted = μ from
    YoungDiagram.ofRowLens_to_rowLens_eq_self] at h
  linarith

/-! ## Partition-level corner removal -/

/-- Remove an outer corner from a partition of n+1 to get a partition of n.
The resulting partition has the same parts, except the row containing the
corner has its length decreased by 1 (or removed if it was length 1).

Implementation: take row lengths of the Young diagram after corner removal. -/
noncomputable def Nat.Partition.removeOuterCorner {n : ℕ} (la : Nat.Partition (n + 1))
    (c : ℕ × ℕ) (hc : la.toYoungDiagram.IsOuterCorner c.1 c.2) : Nat.Partition n where
  parts := ((la.toYoungDiagram.removeCorner c.1 c.2 hc).rowLens : List ℕ)
  parts_pos := fun {i} hi => YoungDiagram.pos_of_mem_rowLens _ _ hi
  parts_sum := by
    rw [Multiset.sum_coe]
    rw [YoungDiagram.rowLens_sum]
    rw [YoungDiagram.removeCorner_card]
    rw [Nat.Partition.toYoungDiagram_card]
    omega

/-- The Young diagram of a removed-corner partition equals the
Young diagram obtained by removing the corner directly. -/
theorem Nat.Partition.toYoungDiagram_removeOuterCorner {n : ℕ} (la : Nat.Partition (n + 1))
    (c : ℕ × ℕ) (hc : la.toYoungDiagram.IsOuterCorner c.1 c.2) :
    (la.removeOuterCorner c hc).toYoungDiagram =
      la.toYoungDiagram.removeCorner c.1 c.2 hc := by
  set μ' := la.toYoungDiagram.removeCorner c.1 c.2 hc
  unfold Nat.Partition.toYoungDiagram Nat.Partition.removeOuterCorner
  convert YoungDiagram.ofRowLens_to_rowLens_eq_self (μ := μ') using 2
  -- Goal: sort of already-sorted rowLens = rowLens
  change (μ'.rowLens : Multiset ℕ).sort (· ≥ ·) = μ'.rowLens
  rw [Multiset.coe_sort]
  exact List.mergeSort_eq_self _ (List.sortedGE_iff_pairwise.mp μ'.rowLens_sorted)

namespace Etingof

noncomputable section

private lemma partition_zero_sortedParts (la : Nat.Partition 0) : la.sortedParts = [] := by
  unfold Nat.Partition.sortedParts
  rw [Nat.Partition.partition_zero_parts la]
  simp

theorem card_standardYoungTableau_mul_zero (la : Nat.Partition 0) :
    Nat.card (StandardYoungTableau 0 la) *
      la.toYoungDiagram.hookLengthProduct = Nat.factorial 0 := by
  have h_empty : la.toYoungDiagram.cells = ∅ :=
    Finset.card_eq_zero.mp la.toYoungDiagram_card
  have h_hook : la.toYoungDiagram.hookLengthProduct = 1 := by
    simp [YoungDiagram.hookLengthProduct, h_empty]
  have h_sorted := partition_zero_sortedParts la
  haveI : Unique (StandardYoungTableau 0 la) := by
    unfold StandardYoungTableau
    rw [h_sorted]
    simp only [List.length_nil, List.getD_nil]
    haveI : IsEmpty { c : ℕ × ℕ // c.1 < 0 ∧ c.2 < 0 } :=
      ⟨fun c => absurd c.2.1 (by omega)⟩
    exact {
      toInhabited := ⟨⟨isEmptyElim, ⟨fun a => isEmptyElim a, fun b => Fin.elim0 b⟩,
               fun c₁ _ _ _ => isEmptyElim c₁, fun c₁ _ _ _ => isEmptyElim c₁⟩⟩
      uniq := fun ⟨f, _⟩ => by congr 1; exact funext fun c => isEmptyElim c
    }
  simp [h_hook, Nat.factorial]

/-! ## Sub-lemmas for the inductive step -/

/-- Cell membership in the SYT sense is equivalent to Young diagram membership. -/
private lemma sytCell_iff_mem_toYoungDiagram {n : ℕ} (la : Nat.Partition n)
    (c : ℕ × ℕ) :
    (c.1 < la.sortedParts.length ∧ c.2 < la.sortedParts.getD c.1 0) ↔
    c ∈ la.toYoungDiagram.cells := by
  simp only [Nat.Partition.toYoungDiagram, Nat.Partition.sortedParts,
    YoungDiagram.mem_cells, YoungDiagram.mem_ofRowLens]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    have heq := List.getD_eq_getElem _ 0 h1
    omega
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    have heq := List.getD_eq_getElem _ 0 h1
    omega

/-- Equivalence between SYT cells and Young diagram cells for a partition. -/
private noncomputable def sytCellEquiv {n : ℕ} (la : Nat.Partition n) :
    { c : ℕ × ℕ // c.1 < la.sortedParts.length ∧ c.2 < la.sortedParts.getD c.1 0 } ≃
    { c : ℕ × ℕ // c ∈ la.toYoungDiagram.cells } where
  toFun := fun ⟨c, h⟩ => ⟨c, (sytCell_iff_mem_toYoungDiagram la c).mp h⟩
  invFun := fun ⟨c, h⟩ => ⟨c, (sytCell_iff_mem_toYoungDiagram la c).mpr h⟩
  left_inv := fun ⟨_, _⟩ => by simp
  right_inv := fun ⟨_, _⟩ => by simp

/-- In any SYT of shape λ ⊢ (n+1), the cell containing the maximum value n
is an outer corner of the Young diagram. -/
private lemma syt_maxCell_isOuterCorner {n : ℕ} {la : Nat.Partition (n + 1)}
    (f : { c : ℕ × ℕ // c.1 < la.sortedParts.length ∧
      c.2 < la.sortedParts.getD c.1 0 } → Fin (n + 1))
    (_hbij : Function.Bijective f)
    (hrow : ∀ c₁ c₂, c₁.val.1 = c₂.val.1 → c₁.val.2 < c₂.val.2 → f c₁ < f c₂)
    (hcol : ∀ c₁ c₂, c₁.val.2 = c₂.val.2 → c₁.val.1 < c₂.val.1 → f c₁ < f c₂)
    (c₀ : { c : ℕ × ℕ // c.1 < la.sortedParts.length ∧
      c.2 < la.sortedParts.getD c.1 0 })
    (hc₀ : f c₀ = Fin.last n) :
    la.toYoungDiagram.IsOuterCorner c₀.val.1 c₀.val.2 := by
  refine ⟨(sytCell_iff_mem_toYoungDiagram la c₀.val).mp c₀.property, ?_, ?_⟩
  · -- (c₀.1 + 1, c₀.2) ∉ cells: if it were, the cell below would have f > n, impossible
    intro hmem
    have hmem' := (sytCell_iff_mem_toYoungDiagram la (c₀.val.1 + 1, c₀.val.2)).mpr hmem
    have h := hcol c₀ ⟨(c₀.val.1 + 1, c₀.val.2), hmem'⟩ rfl
      (show c₀.val.1 < c₀.val.1 + 1 by omega)
    rw [hc₀] at h
    exact absurd h (not_lt.mpr (Fin.le_last _))
  · -- (c₀.1, c₀.2 + 1) ∉ cells: if it were, the cell to the right would have f > n, impossible
    intro hmem
    have hmem' := (sytCell_iff_mem_toYoungDiagram la (c₀.val.1, c₀.val.2 + 1)).mpr hmem
    have h := hrow c₀ ⟨(c₀.val.1, c₀.val.2 + 1), hmem'⟩ rfl
      (show c₀.val.2 < c₀.val.2 + 1 by omega)
    rw [hc₀] at h
    exact absurd h (not_lt.mpr (Fin.le_last _))

/-- A cell of la.removeOuterCorner is also a valid cell of la (the original partition). -/
private lemma reducedCell_mem_original {n : ℕ} {la : Nat.Partition (n + 1)}
    {corner : ℕ × ℕ} {hcorner : la.toYoungDiagram.IsOuterCorner corner.1 corner.2}
    {x : ℕ × ℕ}
    (hx : x.1 < (la.removeOuterCorner corner hcorner).sortedParts.length ∧
      x.2 < (la.removeOuterCorner corner hcorner).sortedParts.getD x.1 0) :
    x.1 < la.sortedParts.length ∧ x.2 < la.sortedParts.getD x.1 0 := by
  have hmem := (sytCell_iff_mem_toYoungDiagram _ x).mp hx
  rw [Nat.Partition.toYoungDiagram_removeOuterCorner] at hmem
  -- hmem : x ∈ (removeCorner ...).cells, which unfolds to cells.erase corner
  have hmem' : x ∈ la.toYoungDiagram.cells :=
    (Finset.mem_erase.mp hmem).2
  exact (sytCell_iff_mem_toYoungDiagram la x).mpr hmem'

/-- A cell of la.removeOuterCorner is distinct from the removed corner. -/
private lemma reducedCell_ne_corner {n : ℕ} {la : Nat.Partition (n + 1)}
    {corner : ℕ × ℕ} {hcorner : la.toYoungDiagram.IsOuterCorner corner.1 corner.2}
    {x : ℕ × ℕ}
    (hx : x.1 < (la.removeOuterCorner corner hcorner).sortedParts.length ∧
      x.2 < (la.removeOuterCorner corner hcorner).sortedParts.getD x.1 0) :
    x ≠ corner := by
  have hmem := (sytCell_iff_mem_toYoungDiagram _ x).mp hx
  rw [Nat.Partition.toYoungDiagram_removeOuterCorner] at hmem
  exact (Finset.mem_erase.mp hmem).1

/-- A cell of la that is not the corner is a valid cell of la.removeOuterCorner. -/
private lemma originalCell_mem_reduced {n : ℕ} {la : Nat.Partition (n + 1)}
    {corner : ℕ × ℕ} {hcorner : la.toYoungDiagram.IsOuterCorner corner.1 corner.2}
    {x : ℕ × ℕ}
    (hx : x.1 < la.sortedParts.length ∧ x.2 < la.sortedParts.getD x.1 0)
    (hne : x ≠ corner) :
    x.1 < (la.removeOuterCorner corner hcorner).sortedParts.length ∧
      x.2 < (la.removeOuterCorner corner hcorner).sortedParts.getD x.1 0 := by
  have hmem := (sytCell_iff_mem_toYoungDiagram la x).mp hx
  have hmem' : x ∈ (la.removeOuterCorner corner hcorner).toYoungDiagram.cells := by
    rw [Nat.Partition.toYoungDiagram_removeOuterCorner]
    exact Finset.mem_erase.mpr ⟨hne, hmem⟩
  exact (sytCell_iff_mem_toYoungDiagram _ x).mpr hmem'

/-- Forward direction of the branching bijection: given an SYT of shape λ ⊢ (n+1),
find the cell with maximum value n (an outer corner) and restrict to get an SYT of λ\c ⊢ n. -/
private noncomputable def sytBranchingToFun (n : ℕ) (la : Nat.Partition (n + 1))
    (t : StandardYoungTableau (n + 1) la) :
    (c : la.toYoungDiagram.outerCorners) ×
      StandardYoungTableau n (la.removeOuterCorner c.val
        (YoungDiagram.mem_outerCorners.mp c.property)) := by
  classical
  have hbij := t.property.1
  have hrow := t.property.2.1
  have hcol := t.property.2.2
  let c₀ := (hbij.surjective (Fin.last n)).choose
  have hc₀ : t.val c₀ = Fin.last n := (hbij.surjective (Fin.last n)).choose_spec
  have hoc := syt_maxCell_isOuterCorner t.val hbij hrow hcol c₀ hc₀
  let corner : la.toYoungDiagram.outerCorners :=
    ⟨c₀.val, YoungDiagram.mem_outerCorners.mpr hoc⟩
  let la' := la.removeOuterCorner corner.val (YoungDiagram.mem_outerCorners.mp corner.property)
  have hcorner_oc := YoungDiagram.mem_outerCorners.mp corner.property
  let g : { x : ℕ × ℕ // x.1 < la'.sortedParts.length ∧
      x.2 < la'.sortedParts.getD x.1 0 } → Fin n := fun c' =>
    let cell_la : { x : ℕ × ℕ // x.1 < la.sortedParts.length ∧
        x.2 < la.sortedParts.getD x.1 0 } :=
      ⟨c'.val, reducedCell_mem_original (hcorner := hcorner_oc) c'.property⟩
    let v := t.val cell_la
    have hne : c'.val ≠ c₀.val :=
      reducedCell_ne_corner (hcorner := hcorner_oc) c'.property
    have hv_ne : v ≠ Fin.last n := by
      intro heq
      have heq' : t.val cell_la = t.val c₀ := heq.trans hc₀.symm
      exact hne (congr_arg Subtype.val (hbij.injective heq'))
    ⟨v.val, Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp v.isLt)
      (Fin.val_ne_of_ne hv_ne)⟩
  have g_bij : Function.Bijective g := by
    constructor
    · intro c₁ c₂ heq
      have hval := congr_arg Fin.val heq
      have h_eq := hbij.injective (Fin.ext hval)
      have h_val_eq : c₁.val = c₂.val :=
        congrArg (fun (x : { x : ℕ × ℕ // x.1 < la.sortedParts.length ∧
          x.2 < la.sortedParts.getD x.1 0 }) => x.val) h_eq
      exact Subtype.ext h_val_eq
    · intro v
      obtain ⟨cell, hcell⟩ := hbij.surjective (Fin.castSucc v)
      have hne : cell.val ≠ c₀.val := by
        intro heq
        have := congr_arg t.val (Subtype.ext heq : cell = c₀)
        rw [hcell, hc₀] at this
        exact absurd this (Fin.castSucc_ne_last v)
      refine ⟨⟨cell.val, originalCell_mem_reduced (hcorner := hcorner_oc)
        cell.property hne⟩, ?_⟩
      ext
      show (t.val ⟨cell.val, _⟩).val = v.val
      have : (⟨cell.val, reducedCell_mem_original (hcorner := hcorner_oc)
        (originalCell_mem_reduced (hcorner := hcorner_oc)
          cell.property hne)⟩ :
        { x : ℕ × ℕ // x.1 < la.sortedParts.length ∧
          x.2 < la.sortedParts.getD x.1 0 }) = cell := Subtype.ext rfl
      rw [this, hcell]
      rfl
  have g_row : ∀ c₁ c₂ : { x : ℕ × ℕ // x.1 < la'.sortedParts.length ∧
      x.2 < la'.sortedParts.getD x.1 0 },
      c₁.val.1 = c₂.val.1 → c₁.val.2 < c₂.val.2 → g c₁ < g c₂ := by
    intro c₁ c₂ hr hc
    exact hrow ⟨c₁.val, reducedCell_mem_original (hcorner := hcorner_oc) c₁.property⟩
           ⟨c₂.val, reducedCell_mem_original (hcorner := hcorner_oc) c₂.property⟩ hr hc
  have g_col : ∀ c₁ c₂ : { x : ℕ × ℕ // x.1 < la'.sortedParts.length ∧
      x.2 < la'.sortedParts.getD x.1 0 },
      c₁.val.2 = c₂.val.2 → c₁.val.1 < c₂.val.1 → g c₁ < g c₂ := by
    intro c₁ c₂ hr hc
    exact hcol ⟨c₁.val, reducedCell_mem_original (hcorner := hcorner_oc) c₁.property⟩
           ⟨c₂.val, reducedCell_mem_original (hcorner := hcorner_oc) c₂.property⟩ hr hc
  exact ⟨corner, g, g_bij, g_row, g_col⟩

/-- Inverse direction of the branching bijection: given an outer corner and an SYT of λ\c ⊢ n,
place value n at the corner to reconstruct an SYT of λ ⊢ (n+1). -/
private noncomputable def sytBranchingInvFun (n : ℕ) (la : Nat.Partition (n + 1))
    (x : (c : la.toYoungDiagram.outerCorners) ×
      StandardYoungTableau n (la.removeOuterCorner c.val
        (YoungDiagram.mem_outerCorners.mp c.property))) :
    StandardYoungTableau (n + 1) la := by
  classical
  obtain ⟨corner, t'⟩ := x
  let hcorner := YoungDiagram.mem_outerCorners.mp corner.property
  let la' := la.removeOuterCorner corner.val hcorner
  let f : { x : ℕ × ℕ // x.1 < la.sortedParts.length ∧
      x.2 < la.sortedParts.getD x.1 0 } → Fin (n + 1) := fun cell =>
    if h : cell.val = corner.val then Fin.last n
    else Fin.castSucc (t'.val ⟨cell.val,
      originalCell_mem_reduced (hcorner := hcorner) cell.property h⟩)
  have corner_no_right : ∀ cell : { x : ℕ × ℕ // x.1 < la.sortedParts.length ∧
      x.2 < la.sortedParts.getD x.1 0 },
      cell.val.1 = corner.val.1 → cell.val.2 > corner.val.2 → False := by
    intro cell hr hc
    have hcell_yd := (sytCell_iff_mem_toYoungDiagram la cell.val).mp cell.property
    have hmem : (cell.val.1, cell.val.2) ∈ la.toYoungDiagram.cells := by
      convert hcell_yd using 1
    have := la.toYoungDiagram.up_left_mem (le_of_eq hr.symm) (Nat.succ_le_of_lt hc) hmem
    exact hcorner.2.2 this
  have corner_no_below : ∀ cell : { x : ℕ × ℕ // x.1 < la.sortedParts.length ∧
      x.2 < la.sortedParts.getD x.1 0 },
      cell.val.2 = corner.val.2 → cell.val.1 > corner.val.1 → False := by
    intro cell hc hr
    have hcell_yd := (sytCell_iff_mem_toYoungDiagram la cell.val).mp cell.property
    have hmem : (cell.val.1, cell.val.2) ∈ la.toYoungDiagram.cells := by
      convert hcell_yd using 1
    have := la.toYoungDiagram.up_left_mem
      (Nat.succ_le_of_lt hr) (le_of_eq hc.symm) hmem
    exact hcorner.2.1 this
  have f_bij : Function.Bijective f := by
    constructor
    · intro c₁ c₂ heq
      simp only [f] at heq
      split_ifs at heq with h₁ h₂ h₂
      · exact Subtype.ext (h₁.trans h₂.symm)
      · exact absurd heq (Fin.castSucc_ne_last _).symm
      · exact absurd heq (Fin.castSucc_ne_last _)
      · have := Fin.castSucc_injective _ heq
        have h_eq := t'.property.1.injective this
        have h_val_eq : c₁.val = c₂.val :=
          congrArg (fun (x : { x : ℕ × ℕ // x.1 < la'.sortedParts.length ∧
            x.2 < la'.sortedParts.getD x.1 0 }) => x.val) h_eq
        exact Subtype.ext h_val_eq
    · intro v
      by_cases hv : v = Fin.last n
      · have hcorner_cell := (sytCell_iff_mem_toYoungDiagram la corner.val).mpr hcorner.1
        exact ⟨⟨corner.val, hcorner_cell⟩, by simp [f, dif_pos, hv]⟩
      · have hv_lt : v.val < n := Nat.lt_of_le_of_ne
          (Nat.lt_succ_iff.mp v.isLt) (Fin.val_ne_of_ne hv)
        obtain ⟨cell', hcell'⟩ := t'.property.1.surjective ⟨v.val, hv_lt⟩
        refine ⟨⟨cell'.val, reducedCell_mem_original (hcorner := hcorner)
          cell'.property⟩, ?_⟩
        simp only [f, dif_neg (reducedCell_ne_corner (hcorner := hcorner) cell'.property)]
        ext
        have : (⟨cell'.val, originalCell_mem_reduced (hcorner := hcorner)
            (reducedCell_mem_original (hcorner := hcorner) cell'.property)
            (reducedCell_ne_corner (hcorner := hcorner) cell'.property)⟩ :
          { x : ℕ × ℕ // x.1 < la'.sortedParts.length ∧
            x.2 < la'.sortedParts.getD x.1 0 }) = cell' := Subtype.ext rfl
        simp [this, hcell']
  have f_row : ∀ c₁ c₂ : { x : ℕ × ℕ // x.1 < la.sortedParts.length ∧
      x.2 < la.sortedParts.getD x.1 0 },
      c₁.val.1 = c₂.val.1 → c₁.val.2 < c₂.val.2 → f c₁ < f c₂ := by
    intro c₁ c₂ hr hc
    simp only [f]
    split_ifs with h₁ h₂ h₂
    · exfalso; rw [h₁] at hc; rw [h₂] at hc; exact Nat.lt_irrefl _ hc
    · exfalso; exact corner_no_right c₂
        (by have := congr_arg Prod.fst h₁; simp at this; omega)
        (by have := congr_arg Prod.snd h₁; simp at this; omega)
    · rw [h₂] at hr hc
      exact Fin.castSucc_lt_last _
    · exact Fin.castSucc_lt_castSucc_iff.mpr (t'.property.2.1
        ⟨c₁.val, originalCell_mem_reduced (hcorner := hcorner) c₁.property h₁⟩
        ⟨c₂.val, originalCell_mem_reduced (hcorner := hcorner) c₂.property h₂⟩ hr hc)
  have f_col : ∀ c₁ c₂ : { x : ℕ × ℕ // x.1 < la.sortedParts.length ∧
      x.2 < la.sortedParts.getD x.1 0 },
      c₁.val.2 = c₂.val.2 → c₁.val.1 < c₂.val.1 → f c₁ < f c₂ := by
    intro c₁ c₂ hc hr
    simp only [f]
    split_ifs with h₁ h₂ h₂
    · exfalso; rw [h₁] at hr; rw [h₂] at hr; exact Nat.lt_irrefl _ hr
    · exfalso; exact corner_no_below c₂
        (by have := congr_arg Prod.snd h₁; simp at this; omega)
        (by have := congr_arg Prod.fst h₁; simp at this; omega)
    · exact Fin.castSucc_lt_last _
    · exact Fin.castSucc_lt_castSucc_iff.mpr (t'.property.2.2
        ⟨c₁.val, originalCell_mem_reduced (hcorner := hcorner) c₁.property h₁⟩
        ⟨c₂.val, originalCell_mem_reduced (hcorner := hcorner) c₂.property h₂⟩ hc hr)
  exact ⟨f, f_bij, f_row, f_col⟩

/-- Left inverse property: invFun ∘ toFun = id for the branching bijection. -/
private theorem sytBranching_leftInv (n : ℕ) (la : Nat.Partition (n + 1))
    (t : StandardYoungTableau (n + 1) la) :
    sytBranchingInvFun n la (sytBranchingToFun n la t) = t := by
  apply Subtype.ext
  funext cell
  simp only [sytBranchingInvFun, sytBranchingToFun]
  split_ifs with h
  · have hc₀_spec := (t.property.1.surjective (Fin.last n)).choose_spec
    have h_eq : cell = (t.property.1.surjective (Fin.last n)).choose := Subtype.ext h
    rw [h_eq, hc₀_spec]
  · apply Fin.ext
    rfl

/-- The inverse function of the branching bijection is injective:
if two (corner, SYT) pairs produce the same extended SYT, they must be equal. -/
private theorem sytBranching_invFun_injective (n : ℕ) (la : Nat.Partition (n + 1)) :
    Function.Injective (sytBranchingInvFun n la) := by
  intro ⟨c₁, t₁⟩ ⟨c₂, t₂⟩ heq
  -- heq : sytBranchingInvFun ⟨c₁, t₁⟩ = sytBranchingInvFun ⟨c₂, t₂⟩
  -- The invFun SYTs are subtypes with .val being functions.
  -- Equal SYTs means equal functions (by Subtype.val_injective applied to heq).
  have hfun := congrArg Subtype.val heq
  -- hfun : f₁ = f₂ where f₁ cell = dite(cell.val = c₁.val) ... and similarly f₂
  -- Step 1: show c₁ = c₂
  -- f₁(corner₁_cell) = last n (by dif_pos) and f₂(corner₁_cell) = f₁(corner₁_cell) = last n
  -- f₂(corner₁_cell) = last n means dite(corner₁_cell.val = c₂.val) ... = last n
  -- If corner₁_cell.val ≠ c₂.val, then f₂ = castSucc(...) ≠ last n. Contradiction.
  -- So corner₁_cell.val = c₂.val, i.e., c₁.val = c₂.val.
  have hcorner_eq : c₁.val = c₂.val := by
    have hc₁_cell := (sytCell_iff_mem_toYoungDiagram la c₁.val).mpr
      (YoungDiagram.mem_outerCorners.mp c₁.property).1
    -- The invFun SYT maps corner to last n. If c₁.val ≠ c₂.val,
    -- then f₂(c₁_cell) = castSucc(...) ≠ last n, but f₁(c₁_cell) = last n = f₂(c₁_cell).
    by_contra hne
    -- f₁(c₁_cell) = last n
    have hval₁ : (sytBranchingInvFun n la ⟨c₁, t₁⟩).val ⟨c₁.val, hc₁_cell⟩ = Fin.last n := by
      simp only [sytBranchingInvFun]; simp
    -- f₂(c₁_cell) ≠ last n since c₁.val ≠ c₂.val
    have hval₂ : (sytBranchingInvFun n la ⟨c₂, t₂⟩).val ⟨c₁.val, hc₁_cell⟩ ≠ Fin.last n := by
      simp only [sytBranchingInvFun]
      simp only [dif_neg hne]
      exact Fin.castSucc_ne_last _
    -- But they must be equal since heq says the SYTs are equal
    exact hval₂ (by rw [← hval₁]; exact (congrFun hfun ⟨c₁.val, hc₁_cell⟩).symm)
  have hc_eq : c₁ = c₂ := Subtype.ext hcorner_eq
  subst hc_eq
  -- Now c₁ = c₂, so we need t₁ = t₂
  congr 1
  -- t₁ and t₂ are SYTs (subtypes), so Subtype.ext + funext
  apply Subtype.ext
  funext c'
  -- f₁ and f₂ agree on all cells. For c' in removeOuterCorner (≠ corner):
  -- f₁ c'_embed = castSucc(t₁.val c') and f₂ c'_embed = castSucc(t₂.val c')
  -- So castSucc(t₁.val c') = castSucc(t₂.val c') → t₁.val c' = t₂.val c'
  have hne : c'.val ≠ c₁.val :=
    reducedCell_ne_corner (hcorner := YoungDiagram.mem_outerCorners.mp c₁.property) c'.property
  have hc'_la := reducedCell_mem_original
    (hcorner := YoungDiagram.mem_outerCorners.mp c₁.property) c'.property
  have h₁ : (sytBranchingInvFun n la ⟨c₁, t₁⟩).val ⟨c'.val, hc'_la⟩ =
    Fin.castSucc (t₁.val c') := by
    simp only [sytBranchingInvFun, dif_neg hne]
  have h₂ : (sytBranchingInvFun n la ⟨c₁, t₂⟩).val ⟨c'.val, hc'_la⟩ =
    Fin.castSucc (t₂.val c') := by
    simp only [sytBranchingInvFun, dif_neg hne]
  have := congrFun hfun ⟨c'.val, hc'_la⟩
  rw [h₁, h₂] at this
  exact Fin.castSucc_injective _ this

/-- The branching bijection: every SYT of shape λ ⊢ (n+1) corresponds to
a choice of outer corner (where the max value sits) and an SYT of the
reduced shape λ\c ⊢ n. -/
private noncomputable def sytBranchingEquiv (n : ℕ) (la : Nat.Partition (n + 1)) :
    StandardYoungTableau (n + 1) la ≃
    (c : la.toYoungDiagram.outerCorners) ×
      StandardYoungTableau n (la.removeOuterCorner c.val
        (YoungDiagram.mem_outerCorners.mp c.property)) :=
  haveI : Fintype (StandardYoungTableau (n + 1) la) := sytFintype (n + 1) la
  haveI : ∀ c : la.toYoungDiagram.outerCorners,
    Fintype (StandardYoungTableau n (la.removeOuterCorner c.val
      (YoungDiagram.mem_outerCorners.mp c.property))) :=
    fun _c => sytFintype n _
  -- invFun is bijective: surjective from leftInv, injective proved directly
  have h_surj : Function.Surjective (sytBranchingInvFun n la) :=
    Function.LeftInverse.surjective (sytBranching_leftInv n la)
  have h_inj : Function.Injective (sytBranchingInvFun n la) :=
    sytBranching_invFun_injective n la
  (Equiv.ofBijective (sytBranchingInvFun n la) ⟨h_inj, h_surj⟩).symm

/-- Branching rule: the number of SYT of shape λ (partition of n+1) equals the
sum over outer corners c of the number of SYT of shape λ\c (partition of n).

The largest entry n+1 in an SYT must occupy an outer corner. Removing it
gives an SYT of the reduced partition. This bijection gives the identity. -/
theorem syt_branching_rule (n : ℕ) (la : Nat.Partition (n + 1)) :
    Nat.card (StandardYoungTableau (n + 1) la) =
      la.toYoungDiagram.outerCorners.attach.sum (fun c =>
        Nat.card (StandardYoungTableau n
          (la.removeOuterCorner c.val
            (YoungDiagram.mem_outerCorners.mp c.property)))) := by
  rw [Nat.card_congr (sytBranchingEquiv n la), Nat.card_sigma]
  rfl

/-! ## Infrastructure for hook quotient identity -/

/-- Membership in removeCorner: in μ and not the removed corner. -/
lemma YoungDiagram.mem_removeCorner_iff {μ : YoungDiagram} {i j : ℕ}
    (hc : μ.IsOuterCorner i j) {a b : ℕ} :
    (a, b) ∈ (μ.removeCorner i j hc) ↔
      (a, b) ∈ μ ∧ (a, b) ≠ (i, j) := by
  change (a, b) ∈ μ.cells.erase (i, j) ↔ (a, b) ∈ μ.cells ∧ _
  simp [Finset.mem_erase]
  tauto

/-- An outer corner (i,j) has rowLen(i) = j + 1. -/
lemma YoungDiagram.IsOuterCorner.rowLen_eq
    {μ : YoungDiagram} {i j : ℕ}
    (hc : μ.IsOuterCorner i j) : μ.rowLen i = j + 1 := by
  have h1 : j < μ.rowLen i :=
    YoungDiagram.mem_iff_lt_rowLen.mp hc.1
  have h2 : ¬(j + 1 < μ.rowLen i) := by
    intro h
    exact hc.2.2 (YoungDiagram.mem_iff_lt_rowLen.mpr h)
  omega

/-- An outer corner (i,j) has colLen(j) = i + 1. -/
lemma YoungDiagram.IsOuterCorner.colLen_eq
    {μ : YoungDiagram} {i j : ℕ}
    (hc : μ.IsOuterCorner i j) : μ.colLen j = i + 1 := by
  have h1 : i < μ.colLen j :=
    YoungDiagram.mem_iff_lt_colLen.mp hc.1
  have h2 : ¬(i + 1 < μ.colLen j) := by
    intro h
    exact hc.2.1 (YoungDiagram.mem_iff_lt_colLen.mpr h)
  omega

/-- The hook length at an outer corner is 1. -/
lemma YoungDiagram.hookLength_outerCorner
    {μ : YoungDiagram} {i j : ℕ}
    (hc : μ.IsOuterCorner i j) :
    μ.hookLength i j = 1 := by
  unfold YoungDiagram.hookLength
  rw [Etingof.YoungDiagram.IsOuterCorner.rowLen_eq hc,
      YoungDiagram.IsOuterCorner.colLen_eq hc]
  omega

/-- Row a cells in μ are the same as in removeCorner when a ≠ i. -/
private lemma YoungDiagram.removeCorner_mem_row
    {μ : YoungDiagram} {i j : ℕ}
    (hc : μ.IsOuterCorner i j) {a : ℕ} (ha : a ≠ i)
    (b : ℕ) :
    (a, b) ∈ (μ.removeCorner i j hc) ↔ (a, b) ∈ μ := by
  rw [mem_removeCorner_iff hc]
  constructor
  · exact And.left
  · exact fun h => ⟨h, by simp [Prod.ext_iff, ha]⟩

/-- rowLen after removing corner: unchanged for rows ≠ i. -/
lemma YoungDiagram.removeCorner_rowLen_ne
    {μ : YoungDiagram} {i j : ℕ}
    (hc : μ.IsOuterCorner i j) {a : ℕ} (ha : a ≠ i) :
    (μ.removeCorner i j hc).rowLen a = μ.rowLen a := by
  apply le_antisymm
  · by_contra h; push_neg at h
    have := (removeCorner_mem_row hc ha (μ.rowLen a)).mp
      (YoungDiagram.mem_iff_lt_rowLen.mpr h)
    exact absurd (YoungDiagram.mem_iff_lt_rowLen.mp this)
      (lt_irrefl _)
  · by_contra h; push_neg at h
    have := (removeCorner_mem_row hc ha _).mpr
      (YoungDiagram.mem_iff_lt_rowLen.mpr h)
    exact absurd (YoungDiagram.mem_iff_lt_rowLen.mp this)
      (lt_irrefl _)

/-- rowLen after removing corner: row i decreases by 1. -/
lemma YoungDiagram.removeCorner_rowLen_eq
    {μ : YoungDiagram} {i j : ℕ}
    (hc : μ.IsOuterCorner i j) :
    (μ.removeCorner i j hc).rowLen i = j := by
  apply le_antisymm
  · -- removeCorner.rowLen i ≤ j: cell (i, j) was removed
    by_contra h; push_neg at h
    have : (i, j) ∈ (μ.removeCorner i j hc) :=
      YoungDiagram.mem_iff_lt_rowLen.mpr h
    rw [mem_removeCorner_iff hc] at this
    exact this.2 rfl
  · -- j ≤ removeCorner.rowLen i: cells (i, b) for b < j still in
    by_contra h; push_neg at h
    have hr := Etingof.YoungDiagram.IsOuterCorner.rowLen_eq hc
    have : (i, (μ.removeCorner i j hc).rowLen i) ∈ μ :=
      YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    have hne : (i, (μ.removeCorner i j hc).rowLen i) ≠ (i, j) :=
      by simp [Prod.ext_iff]; omega
    have : (i, (μ.removeCorner i j hc).rowLen i) ∈
        (μ.removeCorner i j hc) :=
      (mem_removeCorner_iff hc).mpr ⟨this, hne⟩
    exact absurd (YoungDiagram.mem_iff_lt_rowLen.mp this)
      (lt_irrefl _)

/-- Col b cells in μ are the same as in removeCorner when b ≠ j. -/
private lemma YoungDiagram.removeCorner_mem_col
    {μ : YoungDiagram} {i j : ℕ}
    (hc : μ.IsOuterCorner i j) {b : ℕ} (hb : b ≠ j)
    (a : ℕ) :
    (a, b) ∈ (μ.removeCorner i j hc) ↔ (a, b) ∈ μ := by
  rw [mem_removeCorner_iff hc]
  constructor
  · exact And.left
  · exact fun h => ⟨h, fun heq => by cases heq; exact hb rfl⟩

/-- colLen after removing corner: unchanged for cols ≠ j. -/
lemma YoungDiagram.removeCorner_colLen_ne
    {μ : YoungDiagram} {i j : ℕ}
    (hc : μ.IsOuterCorner i j) {b : ℕ} (hb : b ≠ j) :
    (μ.removeCorner i j hc).colLen b = μ.colLen b := by
  apply le_antisymm
  · by_contra h; push_neg at h
    have := (removeCorner_mem_col hc hb (μ.colLen b)).mp
      (YoungDiagram.mem_iff_lt_colLen.mpr h)
    exact absurd (YoungDiagram.mem_iff_lt_colLen.mp this)
      (lt_irrefl _)
  · by_contra h; push_neg at h
    have := (removeCorner_mem_col hc hb _).mpr
      (YoungDiagram.mem_iff_lt_colLen.mpr h)
    exact absurd (YoungDiagram.mem_iff_lt_colLen.mp this)
      (lt_irrefl _)

/-- colLen after removing corner: col j decreases by 1. -/
lemma YoungDiagram.removeCorner_colLen_eq
    {μ : YoungDiagram} {i j : ℕ}
    (hc : μ.IsOuterCorner i j) :
    (μ.removeCorner i j hc).colLen j = i := by
  apply le_antisymm
  · by_contra h; push_neg at h
    have : (i, j) ∈ (μ.removeCorner i j hc) :=
      YoungDiagram.mem_iff_lt_colLen.mpr h
    rw [mem_removeCorner_iff hc] at this
    exact this.2 rfl
  · by_contra h; push_neg at h
    have hc_col := YoungDiagram.IsOuterCorner.colLen_eq hc
    have : ((μ.removeCorner i j hc).colLen j, j) ∈ μ :=
      YoungDiagram.mem_iff_lt_colLen.mpr (by omega)
    have hne :
        ((μ.removeCorner i j hc).colLen j, j) ≠ (i, j) :=
      by simp [Prod.ext_iff]; omega
    have : ((μ.removeCorner i j hc).colLen j, j) ∈
        (μ.removeCorner i j hc) :=
      (mem_removeCorner_iff hc).mpr ⟨this, hne⟩
    exact absurd (YoungDiagram.mem_iff_lt_colLen.mp this)
      (lt_irrefl _)

/-- Hook length at (i₀, b) for b < j₀ decreases by 1. -/
lemma YoungDiagram.removeCorner_hookLength_row
    {μ : YoungDiagram} {i j : ℕ}
    (hc : μ.IsOuterCorner i j) {b : ℕ} (hb : b < j) :
    (μ.removeCorner i j hc).hookLength i b =
      μ.hookLength i b - 1 := by
  unfold YoungDiagram.hookLength
  rw [removeCorner_rowLen_eq hc, removeCorner_colLen_ne hc
    (by omega : b ≠ j)]
  have := Etingof.YoungDiagram.IsOuterCorner.rowLen_eq hc
  omega

/-- Hook length at (a, j₀) for a < i₀ decreases by 1. -/
lemma YoungDiagram.removeCorner_hookLength_col
    {μ : YoungDiagram} {i j : ℕ}
    (hc : μ.IsOuterCorner i j) {a : ℕ} (ha : a < i) :
    (μ.removeCorner i j hc).hookLength a j =
      μ.hookLength a j - 1 := by
  unfold YoungDiagram.hookLength
  rw [removeCorner_rowLen_ne hc (by omega : a ≠ i),
      removeCorner_colLen_eq hc]
  have := YoungDiagram.IsOuterCorner.colLen_eq hc
  omega

/-- Hook length at (a, b) unchanged when a ≠ i₀ and b ≠ j₀. -/
lemma YoungDiagram.removeCorner_hookLength_other
    {μ : YoungDiagram} {i j : ℕ}
    (hc : μ.IsOuterCorner i j) {a b : ℕ}
    (ha : a ≠ i) (hb : b ≠ j) :
    (μ.removeCorner i j hc).hookLength a b =
      μ.hookLength a b := by
  unfold YoungDiagram.hookLength
  rw [removeCorner_rowLen_ne hc ha,
      removeCorner_colLen_ne hc hb]

/-- Hook quotient identity for Young diagrams: for any Young diagram μ,
∑_{c ∈ outerCorners} hookProd(μ)/hookProd(μ\c) = |μ|.

This is a deep combinatorial identity. Known proofs:
- Greene–Nijenhuis–Wilf (1979): probabilistic hook walk argument
- Novelli–Pak–Stoyanovskii (1997): bijective proof
- Pak (2002): direct algebraic via Frobenius character formula
All are substantial and require significant formalization effort.

Infrastructure provided: `IsOuterCorner.rowLen_eq`, `colLen_eq`,
`hookLength_outerCorner`, `removeCorner_rowLen_ne/eq`,
`removeCorner_colLen_ne/eq`, `removeCorner_hookLength_row/col/other`.
-/
private lemma YoungDiagram.hookLengthProduct_erase_corner
    {μ : YoungDiagram} {i j : ℕ}
    (hc : μ.IsOuterCorner i j) :
    μ.hookLengthProduct =
      (μ.cells.erase (i, j)).prod
        (fun c => μ.hookLength c.1 c.2) := by
  unfold YoungDiagram.hookLengthProduct
  rw [← Finset.mul_prod_erase _ _ hc.1,
      YoungDiagram.hookLength_outerCorner hc, one_mul]

private lemma YoungDiagram.hookLengthProduct_removeCorner
    {μ : YoungDiagram} {i j : ℕ}
    (hc : μ.IsOuterCorner i j) :
    (μ.removeCorner i j hc).hookLengthProduct =
      (μ.cells.erase (i, j)).prod
        (fun c => (μ.removeCorner i j hc).hookLength
          c.1 c.2) := by
  unfold YoungDiagram.hookLengthProduct
  rfl

-- The ratio H(μ)/H(μ\c) expressed via product over erase'd cells
lemma YoungDiagram.hookRatio_eq_prod_div
    {μ : YoungDiagram} {i j : ℕ} (hc : μ.IsOuterCorner i j) :
    (μ.hookLengthProduct : ℚ) /
      ((μ.removeCorner i j hc).hookLengthProduct : ℚ) =
    (μ.cells.erase (i, j)).prod (fun c =>
      (μ.hookLength c.1 c.2 : ℚ) /
        ((μ.removeCorner i j hc).hookLength c.1 c.2 : ℚ)) := by
  rw [hookLengthProduct_erase_corner hc, hookLengthProduct_removeCorner hc]
  push_cast
  rw [Finset.prod_div_distrib]

/-- Empty diagram has no outer corners. -/
private lemma YoungDiagram.outerCorners_eq_empty_of_cells_eq_empty
    {μ : YoungDiagram} (h : μ.cells = ∅) : μ.outerCorners = ∅ := by
  simp only [_root_.YoungDiagram.outerCorners, h]
  simp

/-- If c₀ and c are distinct outer corners of μ, then c remains
an outer corner of μ after removing c₀. -/
private lemma YoungDiagram.IsOuterCorner.persist_removeCorner
    {μ : YoungDiagram} {i₀ j₀ i j : ℕ}
    (hc₀ : μ.IsOuterCorner i₀ j₀) (hc : μ.IsOuterCorner i j)
    (hne : (i, j) ≠ (i₀, j₀)) :
    (μ.removeCorner i₀ j₀ hc₀).IsOuterCorner i j := by
  refine ⟨(mem_removeCorner_iff hc₀).mpr ⟨hc.1, hne⟩, ?_, ?_⟩
  · -- (i+1, j) ∉ removeCorner: it's not in μ (since (i,j) is outer corner)
    intro hmem
    have : (i + 1, j) ∈ μ.cells := by
      rw [_root_.YoungDiagram.removeCorner] at hmem
      exact (Finset.mem_erase.mp hmem).2
    exact hc.2.1 this
  · -- (i, j+1) ∉ removeCorner: it's not in μ (since (i,j) is outer corner)
    intro hmem
    have : (i, j + 1) ∈ μ.cells := by
      rw [_root_.YoungDiagram.removeCorner] at hmem
      exact (Finset.mem_erase.mp hmem).2
    exact hc.2.2 this

/-- Corners of μ other than c₀ remain corners in μ \ c₀. -/
private lemma YoungDiagram.outerCorner_of_removeCorner
    {μ : YoungDiagram} {i₀ j₀ : ℕ}
    (hc₀ : μ.IsOuterCorner i₀ j₀)
    {c : ℕ × ℕ} (hc_oc : c ∈ μ.outerCorners) (hne : c ≠ (i₀, j₀)) :
    c ∈ (μ.removeCorner i₀ j₀ hc₀).outerCorners := by
  have hc := YoungDiagram.mem_outerCorners.mp hc_oc
  exact YoungDiagram.mem_outerCorners.mpr
    (YoungDiagram.IsOuterCorner.persist_removeCorner hc₀ hc hne)

/-- Hook length strictly decreases when moving right within a row. -/
private lemma YoungDiagram.hookLength_lt_of_right
    {μ : YoungDiagram} {a b b' : ℕ}
    (hb : (a, b) ∈ μ.cells) (hb' : (a, b') ∈ μ.cells)
    (hlt : b < b') :
    μ.hookLength a b' < μ.hookLength a b := by
  have h1 := YoungDiagram.hookLength_pos μ a b hb
  have h2 := YoungDiagram.hookLength_pos μ a b' hb'
  unfold YoungDiagram.hookLength at h1 h2 ⊢
  have hanti := μ.colLen_anti b b' (Nat.le_of_lt hlt)
  omega

/-- Hook length strictly decreases when moving down within a column. -/
private lemma YoungDiagram.hookLength_lt_of_down
    {μ : YoungDiagram} {a a' b : ℕ}
    (ha : (a, b) ∈ μ.cells) (ha' : (a', b) ∈ μ.cells)
    (hlt : a < a') :
    μ.hookLength a' b < μ.hookLength a b := by
  have h1 := YoungDiagram.hookLength_pos μ a b ha
  have h2 := YoungDiagram.hookLength_pos μ a' b ha'
  unfold YoungDiagram.hookLength at h1 h2 ⊢
  have hanti := μ.rowLen_anti a a' (Nat.le_of_lt hlt)
  omega

/-- Hook length at an outer corner is exactly 1.
(This strengthens hookLength_outerCorner: h = 1 iff it's an outer corner.) -/
private lemma YoungDiagram.hookLength_eq_one_iff_outerCorner
    {μ : YoungDiagram} {i j : ℕ} (h : (i, j) ∈ μ.cells) :
    μ.hookLength i j = 1 ↔ μ.IsOuterCorner i j := by
  constructor
  · intro heq
    refine ⟨h, ?_, ?_⟩
    · intro hmem
      have h1 := YoungDiagram.hookLength_lt_of_down h hmem (Nat.lt_succ_of_le le_rfl)
      have h2 := YoungDiagram.hookLength_pos μ (i + 1) j hmem
      omega
    · intro hmem
      have h1 := YoungDiagram.hookLength_lt_of_right h hmem (Nat.lt_succ_of_le le_rfl)
      have h2 := YoungDiagram.hookLength_pos μ i (j + 1) hmem
      omega
  · exact fun hc => YoungDiagram.hookLength_outerCorner hc

end -- noncomputable section

end Etingof

/-! ## Hook walk weight function (GNW) -/

/-- The hook cells of (i,j) in μ, excluding (i,j) itself: all cells in the same row
to the right and in the same column below. -/
def YoungDiagram.hookCellsExcl (μ : YoungDiagram) (i j : ℕ) :
    Finset (ℕ × ℕ) :=
  ((Finset.Ico (j + 1) (μ.rowLen i)).image (fun b' => (i, b'))) ∪
  ((Finset.Ico (i + 1) (μ.colLen j)).image (fun a' => (a', j)))

/-- Every cell in the hook (excluding the cell itself) has strictly smaller hook length. -/
private lemma YoungDiagram.hookLength_lt_of_hookCellsExcl
    {μ : YoungDiagram} {i j : ℕ} (hmem : (i, j) ∈ μ.cells)
    {v : ℕ × ℕ} (hv : v ∈ μ.hookCellsExcl i j) :
    μ.hookLength v.1 v.2 < μ.hookLength i j := by
  simp only [YoungDiagram.hookCellsExcl, Finset.mem_union, Finset.mem_image,
    Finset.mem_Ico] at hv
  rcases hv with ⟨b', ⟨hlo, hhi⟩, rfl⟩ | ⟨a', ⟨hlo, hhi⟩, rfl⟩
  · exact Etingof.YoungDiagram.hookLength_lt_of_right hmem
      (YoungDiagram.mem_iff_lt_rowLen.mpr hhi) (by omega)
  · exact Etingof.YoungDiagram.hookLength_lt_of_down hmem
      (YoungDiagram.mem_iff_lt_colLen.mpr hhi) (by omega)

/-- The hook walk weight function w(μ, (i,j), c) for the Greene–Nijenhuis–Wilf proof.

For a cell (i,j) ∈ μ.cells and a corner c:
- If hookLength(i,j) = 1 (i.e., (i,j) is a corner): w = δ((i,j), c)
- Otherwise: w = (1/(h-1)) × ∑_{v ∈ hook(i,j)\{(i,j)}} w(v, c)

Termination: hookLength strictly decreases along hook walk steps. -/
noncomputable def YoungDiagram.hookWalkWeight
    (μ : YoungDiagram) (i j : ℕ) (c : ℕ × ℕ) : ℚ :=
  if hmem : (i, j) ∈ μ.cells then
    if μ.hookLength i j = 1 then
      if (i, j) = c then 1 else 0
    else
      ((μ.hookCellsExcl i j).attach.sum fun ⟨v, hv⟩ =>
        have : μ.hookLength v.1 v.2 < μ.hookLength i j :=
          YoungDiagram.hookLength_lt_of_hookCellsExcl hmem hv
        YoungDiagram.hookWalkWeight μ v.1 v.2 c) /
        (μ.hookLength i j - 1 : ℚ)
  else 0
termination_by μ.hookLength i j

/-- At a corner cell, the hook walk weight is 1 if it's the target corner, 0 otherwise. -/
lemma YoungDiagram.hookWalkWeight_corner
    {μ : YoungDiagram} {i j : ℕ}
    (hc : μ.IsOuterCorner i j) :
    μ.hookWalkWeight i j (i, j) = 1 := by
  unfold YoungDiagram.hookWalkWeight
  rw [dif_pos hc.1, if_pos (Etingof.YoungDiagram.hookLength_outerCorner hc), if_pos rfl]

/-- At a corner cell different from the target, the hook walk weight is 0. -/
lemma YoungDiagram.hookWalkWeight_ne_corner
    {μ : YoungDiagram} {i j i' j' : ℕ}
    (hc : μ.IsOuterCorner i j) (hne : (i, j) ≠ (i', j')) :
    μ.hookWalkWeight i j (i', j') = 0 := by
  unfold YoungDiagram.hookWalkWeight
  rw [dif_pos hc.1, if_pos (Etingof.YoungDiagram.hookLength_outerCorner hc), if_neg hne]

/-- The hook walk weight is 0 for cells not in the diagram. -/
lemma YoungDiagram.hookWalkWeight_not_mem
    {μ : YoungDiagram} {i j : ℕ} (h : (i, j) ∉ μ.cells)
    (c : ℕ × ℕ) : μ.hookWalkWeight i j c = 0 := by
  rw [YoungDiagram.hookWalkWeight, dif_neg h]

/-! ## hookCellsExcl infrastructure -/

/-- Cells in hookCellsExcl are cells of μ. -/
lemma YoungDiagram.hookCellsExcl_subset_cells
    {μ : YoungDiagram} {i j : ℕ} (_ : (i, j) ∈ μ.cells)
    {v : ℕ × ℕ} (hv : v ∈ μ.hookCellsExcl i j) :
    v ∈ μ.cells := by
  simp only [YoungDiagram.hookCellsExcl, Finset.mem_union, Finset.mem_image,
    Finset.mem_Ico] at hv
  rcases hv with ⟨b', ⟨_, hhi⟩, rfl⟩ | ⟨a', ⟨_, hhi⟩, rfl⟩
  · exact YoungDiagram.mem_iff_lt_rowLen.mpr hhi
  · exact YoungDiagram.mem_iff_lt_colLen.mpr hhi

/-- The row and column parts of hookCellsExcl are disjoint. -/
private lemma YoungDiagram.hookCellsExcl_disjoint
    (μ : YoungDiagram) (i j : ℕ) :
    Disjoint
      ((Finset.Ico (j + 1) (μ.rowLen i)).image (fun b' => (i, b')))
      ((Finset.Ico (i + 1) (μ.colLen j)).image (fun a' => (a', j))) := by
  rw [Finset.disjoint_left]
  intro x hx1 hx2
  simp only [Finset.mem_image, Finset.mem_Ico] at hx1 hx2
  obtain ⟨b', _, rfl⟩ := hx1
  obtain ⟨a', ⟨ha', _⟩, h⟩ := hx2
  simp [Prod.ext_iff] at h
  omega

/-- The cardinality of hookCellsExcl equals hookLength - 1. -/
lemma YoungDiagram.card_hookCellsExcl
    {μ : YoungDiagram} {i j : ℕ} (hmem : (i, j) ∈ μ.cells) :
    (μ.hookCellsExcl i j).card = μ.hookLength i j - 1 := by
  unfold YoungDiagram.hookCellsExcl
  rw [Finset.card_union_of_disjoint (hookCellsExcl_disjoint μ i j)]
  have hrl := YoungDiagram.mem_iff_lt_rowLen.mp hmem
  have hcl := YoungDiagram.mem_iff_lt_colLen.mp hmem
  rw [Finset.card_image_of_injective _ (fun a b h => by simpa [Prod.ext_iff] using h),
      Finset.card_image_of_injective _ (fun a b h => by simpa [Prod.ext_iff] using h),
      Nat.card_Ico, Nat.card_Ico]
  unfold YoungDiagram.hookLength
  omega

/-! ## GNW Property 1: Row sums equal 1 -/

/-- Property 1 of the GNW hook walk: for each cell (i,j) ∈ μ, the sum of
hook walk weights over all outer corners equals 1.

Proof: by well-founded induction on hookLength.
- Base (hookLength = 1): (i,j) is a corner, w = δ, sum = 1.
- Step (hookLength > 1): swap sums, apply IH, use |hookCellsExcl| = h-1. -/
theorem YoungDiagram.hookWalkWeight_row_sum
    (μ : YoungDiagram) (i j : ℕ) (hmem : (i, j) ∈ μ.cells) :
    μ.outerCorners.sum (fun c => μ.hookWalkWeight i j c) = 1 := by
  -- Generalize to induct on hookLength
  suffices h : ∀ (n : ℕ) (i j : ℕ), (i, j) ∈ μ.cells → μ.hookLength i j = n →
      μ.outerCorners.sum (fun c => μ.hookWalkWeight i j c) = 1 from
    h _ i j hmem rfl
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro i j hmem h_wf
  by_cases hone : μ.hookLength i j = 1
  · -- Base case: hookLength = 1, (i,j) is a corner
    have hoc := (Etingof.YoungDiagram.hookLength_eq_one_iff_outerCorner hmem).mp hone
    have hcorner : (i, j) ∈ μ.outerCorners := by
      rw [YoungDiagram.mem_outerCorners]; exact hoc
    -- Each w(i,j,c) = δ((i,j),c)
    have hsummand : ∀ c ∈ μ.outerCorners,
        μ.hookWalkWeight i j c = if (i, j) = c then 1 else 0 := by
      intro c _
      rw [YoungDiagram.hookWalkWeight, dif_pos hmem, if_pos hone]
    rw [Finset.sum_congr rfl hsummand]
    rw [Finset.sum_eq_single (i, j)
      (fun b _ hne => if_neg (Ne.symm hne))
      (fun h => absurd hcorner h),
      if_pos rfl]
  · -- Inductive case: hookLength > 1
    -- Each w(i,j,c) = (∑_v w(v,c)) / (h-1)
    have hsummand : ∀ c ∈ μ.outerCorners,
        μ.hookWalkWeight i j c =
          ((μ.hookCellsExcl i j).attach.sum fun ⟨v, hv⟩ =>
            YoungDiagram.hookWalkWeight μ v.1 v.2 c) /
            (μ.hookLength i j - 1 : ℚ) := by
      intro c _
      rw [YoungDiagram.hookWalkWeight, dif_pos hmem, if_neg hone]
    rw [Finset.sum_congr rfl hsummand]
    -- Factor out the denominator: ∑_c (∑_v w(v,c))/(h-1) = (∑_c ∑_v w(v,c))/(h-1)
    rw [← Finset.sum_div]
    -- Swap the double sum: ∑_c ∑_v = ∑_v ∑_c
    rw [Finset.sum_comm]
    -- Each ∑_c w(v,c) = 1 by IH
    have hinner : ∀ (w : { v // v ∈ μ.hookCellsExcl i j }),
        w ∈ (μ.hookCellsExcl i j).attach →
        (μ.outerCorners.sum fun c =>
          YoungDiagram.hookWalkWeight μ w.val.1 w.val.2 c) = 1 := by
      intro ⟨v, hv⟩ _
      exact ih (μ.hookLength v.1 v.2)
        (h_wf ▸ YoungDiagram.hookLength_lt_of_hookCellsExcl hmem hv)
        _ _ (hookCellsExcl_subset_cells hmem hv) rfl
    rw [Finset.sum_congr rfl hinner]
    -- Now sum of 1's divided by (h-1)
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [Finset.card_attach, card_hookCellsExcl hmem]
    have hh_ge2 : 2 ≤ μ.hookLength i j := by
      have := YoungDiagram.hookLength_pos μ i j hmem; omega
    rw [Nat.cast_sub (by omega : 1 ≤ μ.hookLength i j)]
    have hne : (↑(μ.hookLength i j) : ℚ) - ↑1 ≠ 0 := by
      have : (2 : ℚ) ≤ μ.hookLength i j := by exact_mod_cast hh_ge2
      linarith
    exact div_self hne

/-! ## GNW Property 2: Column identity -/

/-- The hook walk weight at cell u for corner c, when u is not a corner itself
(hookLength > 1), unfolds to the recursive formula. -/
private lemma YoungDiagram.hookWalkWeight_unfold_noncorner
    {μ : YoungDiagram} {a b : ℕ} (hmem : (a, b) ∈ μ.cells)
    (hne : μ.hookLength a b ≠ 1) (c : ℕ × ℕ) :
    μ.hookWalkWeight a b c =
      ((μ.hookCellsExcl a b).attach.sum fun ⟨v, hv⟩ =>
        μ.hookWalkWeight v.1 v.2 c) /
        (μ.hookLength a b - 1 : ℚ) := by
  rw [YoungDiagram.hookWalkWeight, dif_pos hmem, if_neg hne]

/-- Cells of μ that are outer corners different from (i,j) contribute 0
to hookWalkWeight _ _ (i,j). -/
private lemma YoungDiagram.hookWalkWeight_other_corner
    {μ : YoungDiagram} {a b i j : ℕ}
    (hoc : μ.IsOuterCorner a b) (hne : (a, b) ≠ (i, j)) :
    μ.hookWalkWeight a b (i, j) = 0 := by
  rw [YoungDiagram.hookWalkWeight, dif_pos hoc.1,
      if_pos (Etingof.YoungDiagram.hookLength_outerCorner hoc), if_neg hne]

/-- The hookWalkWeight for a cell not in μ is 0 (variant for Finset.sum). -/
private lemma YoungDiagram.hookWalkWeight_zero_of_not_mem
    {μ : YoungDiagram} {u : ℕ × ℕ} (h : u ∉ μ.cells) (c : ℕ × ℕ) :
    μ.hookWalkWeight u.1 u.2 c = 0 :=
  YoungDiagram.hookWalkWeight_not_mem h c

/-- The cells of μ.erase (i,j) can be partitioned into three groups:
arm cells (same row i, col < j), leg cells (same col j, row < i),
and other cells (different row and column).
For the hook ratio, arm/leg cells contribute h/(h-1), others contribute 1. -/
private lemma YoungDiagram.hookRatio_arm_leg_decomp
    {μ : YoungDiagram} {i j : ℕ} (hc : μ.IsOuterCorner i j) :
    (μ.cells.erase (i, j)).prod (fun c =>
      (μ.hookLength c.1 c.2 : ℚ) /
        ((μ.removeCorner i j hc).hookLength c.1 c.2 : ℚ)) =
    (μ.cells.erase (i, j)).prod (fun c =>
      if c.1 = i ∧ c.2 < j then
        (μ.hookLength c.1 c.2 : ℚ) / (μ.hookLength c.1 c.2 - 1 : ℚ)
      else if c.2 = j ∧ c.1 < i then
        (μ.hookLength c.1 c.2 : ℚ) / (μ.hookLength c.1 c.2 - 1 : ℚ)
      else 1) := by
  apply Finset.prod_congr rfl
  intro ⟨a, b⟩ hmem
  simp only
  have hmem' : (a, b) ∈ μ.cells := Finset.mem_of_mem_erase hmem
  have hne : (a, b) ≠ (i, j) := Finset.ne_of_mem_erase hmem
  by_cases hai : a = i
  · -- Same row: a = i, so need b < j (since rowLen i = j+1 and (a,b) ≠ (i,j))
    have hbj : b ≠ j := fun h => hne (by rw [hai, h])
    have hblt : b < j := by
      rcases Nat.lt_or_gt_of_ne hbj with h | h
      · exact h
      · exfalso
        have := Etingof.YoungDiagram.IsOuterCorner.rowLen_eq hc
        have := YoungDiagram.mem_iff_lt_rowLen.mp (hai ▸ hmem')
        omega
    -- The first `if` is true: a = i ∧ b < j
    rw [if_pos ⟨hai, hblt⟩]
    congr 1
    rw [hai, Etingof.YoungDiagram.removeCorner_hookLength_row hc hblt]
    have hpos := YoungDiagram.hookLength_pos μ i b (hai ▸ hmem')
    simp [Nat.cast_sub (by omega : 1 ≤ μ.hookLength i b)]
  · by_cases hbj : b = j
    · -- Same column: b = j, need a < i
      have halt : a < i := by
        rcases Nat.lt_or_gt_of_ne hai with h | h
        · exact h
        · exfalso
          have := Etingof.YoungDiagram.IsOuterCorner.colLen_eq hc
          have := YoungDiagram.mem_iff_lt_colLen.mp (hbj ▸ hmem')
          omega
      -- The first `if` is false (a ≠ i), second is true (b = j ∧ a < i)
      rw [if_neg (fun h => hai h.1), if_pos ⟨hbj, halt⟩]
      congr 1
      rw [hbj, Etingof.YoungDiagram.removeCorner_hookLength_col hc halt]
      have hpos := YoungDiagram.hookLength_pos μ a j (hbj ▸ hmem')
      simp [Nat.cast_sub (by omega : 1 ≤ μ.hookLength a j)]
    · -- Neither row nor column: hook length unchanged, ratio = 1
      rw [if_neg (fun h => hai h.1), if_neg (fun h => hbj h.1)]
      rw [Etingof.YoungDiagram.removeCorner_hookLength_other hc hai hbj]
      have hpos := YoungDiagram.hookLength_pos μ a b hmem'
      exact div_self (by positivity)

/-- For a cell u in the hook of v (excluding v), v is in μ. -/
private lemma YoungDiagram.hookCellsExcl_mem_cells
    {μ : YoungDiagram} {a b : ℕ} (hmem : (a, b) ∈ μ.cells)
    {v : ℕ × ℕ} (hv : v ∈ μ.hookCellsExcl a b) : v ∈ μ.cells :=
  YoungDiagram.hookCellsExcl_subset_cells hmem hv

/-- Hook walk weight is zero when the target corner c = (i, j) has
smaller row index than u. The hook walk from (a, b) only visits cells
(a', b') with a' ≥ a, so it can never reach (i, j) when a > i. -/
private lemma YoungDiagram.hookWalkWeight_zero_of_row_gt
    {μ : YoungDiagram} {a b i j : ℕ} (ha : i < a)
    (hmem : (a, b) ∈ μ.cells) :
    μ.hookWalkWeight a b (i, j) = 0 := by
  -- By well-founded induction on hookLength
  suffices h : ∀ (n : ℕ) (a b : ℕ), i < a → (a, b) ∈ μ.cells →
      μ.hookLength a b = n → μ.hookWalkWeight a b (i, j) = 0 from
    h _ a b ha hmem rfl
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro a b ha hmem hlen
    by_cases hone : μ.hookLength a b = 1
    · rw [YoungDiagram.hookWalkWeight, dif_pos hmem, if_pos hone,
          if_neg (by intro h; exact absurd (congr_arg Prod.fst h).symm (by omega))]
    · rw [YoungDiagram.hookWalkWeight_unfold_noncorner hmem hone]
      rw [Finset.sum_eq_zero, zero_div]
      intro ⟨v, hv⟩ _
      have hv_mem := YoungDiagram.hookCellsExcl_subset_cells hmem hv
      have hv_lt := YoungDiagram.hookLength_lt_of_hookCellsExcl hmem hv
      simp only [YoungDiagram.hookCellsExcl, Finset.mem_union, Finset.mem_image,
        Finset.mem_Ico] at hv
      rcases hv with ⟨b', _, rfl⟩ | ⟨a', ⟨ha', _⟩, rfl⟩
      · exact ih _ (hlen ▸ hv_lt) a b' (by omega) hv_mem rfl
      · exact ih _ (hlen ▸ hv_lt) a' b (by omega) hv_mem rfl

/-- Hook walk weight is zero when the target corner c = (i, j) has
smaller column index than u. Symmetric to `hookWalkWeight_zero_of_row_gt`. -/
private lemma YoungDiagram.hookWalkWeight_zero_of_col_gt
    {μ : YoungDiagram} {a b i j : ℕ} (hb : j < b)
    (hmem : (a, b) ∈ μ.cells) :
    μ.hookWalkWeight a b (i, j) = 0 := by
  suffices h : ∀ (n : ℕ) (a b : ℕ), j < b → (a, b) ∈ μ.cells →
      μ.hookLength a b = n → μ.hookWalkWeight a b (i, j) = 0 from
    h _ a b hb hmem rfl
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro a b hb hmem hlen
    by_cases hone : μ.hookLength a b = 1
    · rw [YoungDiagram.hookWalkWeight, dif_pos hmem, if_pos hone,
          if_neg (by intro h; exact absurd (congr_arg Prod.snd h).symm (by omega))]
    · rw [YoungDiagram.hookWalkWeight_unfold_noncorner hmem hone]
      rw [Finset.sum_eq_zero, zero_div]
      intro ⟨v, hv⟩ _
      have hv_mem := YoungDiagram.hookCellsExcl_subset_cells hmem hv
      have hv_lt := YoungDiagram.hookLength_lt_of_hookCellsExcl hmem hv
      simp only [YoungDiagram.hookCellsExcl, Finset.mem_union, Finset.mem_image,
        Finset.mem_Ico] at hv
      rcases hv with ⟨b', ⟨hb', _⟩, rfl⟩ | ⟨a', _, rfl⟩
      · exact ih _ (hlen ▸ hv_lt) a b' (by omega) hv_mem rfl
      · exact ih _ (hlen ▸ hv_lt) a' b (by omega) hv_mem rfl

/-! ## Hook length decomposition and weight factorization -/

/-- Key arithmetic identity: hookLength(a,b) - 1 decomposes as
(hookLength(a,j) - 1) + (hookLength(i,b) - 1) for cells (a,b) in the rectangle
below-left of an outer corner (i,j). This is the arithmetic heart of the
column identity proof. -/
private lemma YoungDiagram.hookLength_sub_one_decomp
    {μ : YoungDiagram} {i j : ℕ} (hc : μ.IsOuterCorner i j)
    {a b : ℕ} (ha : a ≤ i) (hb : b ≤ j) (hmem : (a, b) ∈ μ.cells) :
    μ.hookLength a b - 1 = (μ.hookLength a j - 1) + (μ.hookLength i b - 1) := by
  have hrl := Etingof.YoungDiagram.IsOuterCorner.rowLen_eq hc
  have hcl := Etingof.YoungDiagram.IsOuterCorner.colLen_eq hc
  have hmem_aj : (a, j) ∈ μ.cells := by
    rw [YoungDiagram.mem_cells, YoungDiagram.mem_iff_lt_colLen]; omega
  have hmem_ib : (i, b) ∈ μ.cells := by
    rw [YoungDiagram.mem_cells, YoungDiagram.mem_iff_lt_rowLen]; omega
  simp only [YoungDiagram.hookLength]
  have h1 : i + 1 ≤ μ.colLen b := YoungDiagram.mem_iff_lt_colLen.mp hmem_ib
  have h2 : j + 1 ≤ μ.rowLen a := YoungDiagram.mem_iff_lt_rowLen.mp hmem_aj
  omega

/-- The hook walk weight factorizes: w(a,b,c) = w(a,j,c) * w(i,b,c)
for corner c = (i,j) and cells (a,b) with a ≤ i, b ≤ j in μ.
Proof by well-founded induction on hookLength(a,b). -/
private lemma YoungDiagram.hookWalkWeight_factorization
    {μ : YoungDiagram} {i j : ℕ} (hc : μ.IsOuterCorner i j)
    {a b : ℕ} (ha : a ≤ i) (hb : b ≤ j) (hmem : (a, b) ∈ μ.cells) :
    μ.hookWalkWeight a b (i, j) =
      μ.hookWalkWeight a j (i, j) * μ.hookWalkWeight i b (i, j) := by
  have hrl := Etingof.YoungDiagram.IsOuterCorner.rowLen_eq hc
  have hcl := Etingof.YoungDiagram.IsOuterCorner.colLen_eq hc
  -- Induction on hookLength
  suffices hsuff : ∀ (n : ℕ) (a b : ℕ), a ≤ i → b ≤ j → (a, b) ∈ μ.cells →
      μ.hookLength a b = n →
      μ.hookWalkWeight a b (i, j) =
        μ.hookWalkWeight a j (i, j) * μ.hookWalkWeight i b (i, j) from
    hsuff _ a b ha hb hmem rfl
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro a b ha hb hmem hlen
    have hmem_aj : (a, j) ∈ μ.cells := by
      rw [YoungDiagram.mem_cells, YoungDiagram.mem_iff_lt_colLen]; omega
    have hmem_ib : (i, b) ∈ μ.cells := by
      rw [YoungDiagram.mem_cells, YoungDiagram.mem_iff_lt_rowLen]; omega
    by_cases hone : μ.hookLength a b = 1
    · -- Base: hookLength = 1 means (a,b) is outer corner with a ≤ i, b ≤ j
      -- So (a,b) = (i,j) since colLen(b) = a+1 forces a ≥ i and rowLen(a) = b+1 forces b ≥ j
      have hoc := (Etingof.YoungDiagram.hookLength_eq_one_iff_outerCorner
        (by rw [YoungDiagram.mem_cells] at hmem; exact hmem)).mp hone
      have hab_eq : a = i ∧ b = j := by
        constructor
        · -- colLen(b) = a + 1 (outer corner at (a,b)), but i < colLen(b) since (i,b) ∈ μ
          have := Etingof.YoungDiagram.IsOuterCorner.colLen_eq hoc
          have := YoungDiagram.mem_iff_lt_colLen.mp hmem_ib
          omega
        · -- rowLen(a) = b + 1 (outer corner at (a,b)), but j < rowLen(a) since (a,j) ∈ μ
          have := Etingof.YoungDiagram.IsOuterCorner.rowLen_eq hoc
          have := YoungDiagram.mem_iff_lt_rowLen.mp hmem_aj
          omega
      rw [hab_eq.1, hab_eq.2, YoungDiagram.hookWalkWeight_corner hc]; ring
    · -- Recursive case: hookLength > 1
      -- Handle trivial subcases first
      by_cases hbj : b = j
      · -- w(a,j,(i,j)) = w(a,j,(i,j)) * w(i,j,(i,j)) = w(a,j,(i,j)) * 1
        rw [hbj, YoungDiagram.hookWalkWeight_corner hc, mul_one]
      · by_cases hai : a = i
        · -- w(i,b,(i,j)) = w(i,j,(i,j)) * w(i,b,(i,j)) = 1 * w(i,b,(i,j))
          rw [hai, YoungDiagram.hookWalkWeight_corner hc, one_mul]
        · -- Main case: a < i, b < j
          have halt : a < i := lt_of_le_of_ne ha hai
          have hblt : b < j := lt_of_le_of_ne hb hbj
          -- hookLength for (i,b) and (a,j) are > 1
          have hone_ib : μ.hookLength i b ≠ 1 := by
            intro h
            have hoc := (Etingof.YoungDiagram.hookLength_eq_one_iff_outerCorner
              (by rw [YoungDiagram.mem_cells] at hmem_ib; exact hmem_ib)).mp h
            have hrl_ib := Etingof.YoungDiagram.IsOuterCorner.rowLen_eq hoc
            -- hrl_ib : rowLen i = b + 1, but hrl : rowLen i = j + 1 and b ≠ j
            omega
          have hone_aj : μ.hookLength a j ≠ 1 := by
            intro h
            have hoc := (Etingof.YoungDiagram.hookLength_eq_one_iff_outerCorner
              (by rw [YoungDiagram.mem_cells] at hmem_aj; exact hmem_aj)).mp h
            have hcl_aj := Etingof.YoungDiagram.IsOuterCorner.colLen_eq hoc
            -- hcl_aj : colLen j = a + 1, but hcl : colLen j = i + 1 and a ≠ i
            omega
          -- Key: show hookCellsExcl sum = w(a,j)*w(i,b)*(h(a,b)-1)
          -- then division by (h(a,b)-1) gives the factorization
          have hh_pos : (0 : ℚ) < μ.hookLength a b - 1 := by
            have h1 := YoungDiagram.hookLength_pos μ a b hmem
            have h2 : 1 < μ.hookLength a b := by omega
            exact_mod_cast (show (0 : ℤ) < (μ.hookLength a b : ℤ) - 1 by omega)
          -- Suffices: the regular sum = w(a,j)*w(i,b)*(h-1)
          suffices hsum : (μ.hookCellsExcl a b).sum
              (fun v => μ.hookWalkWeight v.1 v.2 (i, j)) =
              μ.hookWalkWeight a j (i, j) * μ.hookWalkWeight i b (i, j) *
                (↑(μ.hookLength a b) - 1) by
            rw [YoungDiagram.hookWalkWeight_unfold_noncorner hmem hone]
            show (∑ x ∈ (μ.hookCellsExcl a b).attach,
                μ.hookWalkWeight x.val.1 x.val.2 (i, j)) /
                (↑(μ.hookLength a b) - 1) =
              μ.hookWalkWeight a j (i, j) * μ.hookWalkWeight i b (i, j)
            rw [@Finset.sum_attach _ _ _ (μ.hookCellsExcl a b)
                (fun v => μ.hookWalkWeight v.1 v.2 (i, j)),
              hsum, mul_div_cancel_right₀ _ (ne_of_gt hh_pos)]
          -- Now prove hsum: the sum = w(a,j)*w(i,b)*(h(a,b)-1)
          have hdisj := YoungDiagram.hookCellsExcl_disjoint μ a b
          rw [YoungDiagram.hookCellsExcl, Finset.sum_union hdisj]
          -- Convert image sums to index sums
          rw [Finset.sum_image (by intro x _ y _ h; simpa [Prod.ext_iff] using h),
              Finset.sum_image (by intro x _ y _ h; simpa [Prod.ext_iff] using h)]
          simp only [Prod.fst, Prod.snd]
          -- Now: w(a,j)*w(i,b)*(h-1) =
          --   ∑_{b' in Ico(b+1, rowLen a)} w(a,b',(i,j)) +
          --   ∑_{a' in Ico(a+1, colLen b)} w(a',b,(i,j))
          -- Split each Ico: effective part (≤ i/j) + vanishing part (> i/j)
          have hrla : j + 1 ≤ μ.rowLen a :=
            YoungDiagram.mem_iff_lt_rowLen.mp hmem_aj
          have hclb : i + 1 ≤ μ.colLen b :=
            YoungDiagram.mem_iff_lt_colLen.mp hmem_ib
          rw [show Finset.Ico (b + 1) (μ.rowLen a) =
                Finset.Ico (b + 1) (j + 1) ∪ Finset.Ico (j + 1) (μ.rowLen a) from
                (Finset.Ico_union_Ico_eq_Ico (by omega) hrla).symm,
              show Finset.Ico (a + 1) (μ.colLen b) =
                Finset.Ico (a + 1) (i + 1) ∪ Finset.Ico (i + 1) (μ.colLen b) from
                (Finset.Ico_union_Ico_eq_Ico (by omega) hclb).symm]
          rw [Finset.sum_union (by
                rw [Finset.disjoint_left]; intro x hx1 hx2
                simp [Finset.mem_Ico] at hx1 hx2; omega),
              Finset.sum_union (by
                rw [Finset.disjoint_left]; intro x hx1 hx2
                simp [Finset.mem_Ico] at hx1 hx2; omega)]
          -- Vanishing sums are 0
          have hvan_arm : (Finset.Ico (j + 1) (μ.rowLen a)).sum
              (fun b' => μ.hookWalkWeight a b' (i, j)) = 0 := by
            apply Finset.sum_eq_zero; intro b' hb'
            simp [Finset.mem_Ico] at hb'
            exact YoungDiagram.hookWalkWeight_zero_of_col_gt
              (by omega) (YoungDiagram.mem_iff_lt_rowLen.mpr hb'.2)
          have hvan_leg : (Finset.Ico (i + 1) (μ.colLen b)).sum
              (fun a' => μ.hookWalkWeight a' b (i, j)) = 0 := by
            apply Finset.sum_eq_zero; intro a' ha'
            simp [Finset.mem_Ico] at ha'
            exact YoungDiagram.hookWalkWeight_zero_of_row_gt
              (by omega) (YoungDiagram.mem_iff_lt_colLen.mpr ha'.2)
          rw [hvan_arm, hvan_leg, add_zero, add_zero]
          -- Now: w(a,j)*w(i,b)*(h(a,b)-1) =
          --   ∑_{b'∈Ico(b+1,j+1)} w(a,b',(i,j)) +
          --   ∑_{a'∈Ico(a+1,i+1)} w(a',b,(i,j))
          -- Apply IH to each summand
          have hih_arm : ∀ b' ∈ Finset.Ico (b + 1) (j + 1),
              μ.hookWalkWeight a b' (i, j) =
                μ.hookWalkWeight a j (i, j) * μ.hookWalkWeight i b' (i, j) := by
            intro b' hb'
            simp [Finset.mem_Ico] at hb'
            have hb'mem : (a, b') ∈ μ.cells :=
              YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
            have hlt : μ.hookLength a b' < μ.hookLength a b :=
              Etingof.YoungDiagram.hookLength_lt_of_right hmem hb'mem (by omega)
            exact ih _ (hlen ▸ hlt) a b' ha (by omega) hb'mem rfl
          have hih_leg : ∀ a' ∈ Finset.Ico (a + 1) (i + 1),
              μ.hookWalkWeight a' b (i, j) =
                μ.hookWalkWeight a' j (i, j) * μ.hookWalkWeight i b (i, j) := by
            intro a' ha'
            simp [Finset.mem_Ico] at ha'
            have ha'mem : (a', b) ∈ μ.cells :=
              YoungDiagram.mem_iff_lt_colLen.mpr (by omega)
            have hlt : μ.hookLength a' b < μ.hookLength a b :=
              Etingof.YoungDiagram.hookLength_lt_of_down hmem ha'mem (by omega)
            exact ih _ (hlen ▸ hlt) a' b (by omega) hb ha'mem rfl
          rw [Finset.sum_congr rfl hih_arm, Finset.sum_congr rfl hih_leg]
          -- Factor out common terms
          rw [← Finset.mul_sum, ← Finset.sum_mul]
          -- Now: w(a,j)*w(i,b)*(h(a,b)-1) =
          --   w(a,j) * ∑_{b'} w(i,b',(i,j)) + (∑_{a'} w(a',j,(i,j))) * w(i,b)
          -- Use recursion identities:
          --   ∑_{b'∈Ico(b+1,j+1)} w(i,b',(i,j)) = (h(i,b)-1)*w(i,b,(i,j))
          --   ∑_{a'∈Ico(a+1,i+1)} w(a',j,(i,j)) = (h(a,j)-1)*w(a,j,(i,j))
          -- These follow from unfold of w(i,b) and w(a,j) + vanishing
          have hrec_ib : (Finset.Ico (b + 1) (j + 1)).sum
              (fun b' => μ.hookWalkWeight i b' (i, j)) =
              (↑(μ.hookLength i b) - 1) * μ.hookWalkWeight i b (i, j) := by
            have hunf : μ.hookWalkWeight i b (i, j) =
                (μ.hookCellsExcl i b).sum (fun v => μ.hookWalkWeight v.1 v.2 (i, j)) /
                  (↑(μ.hookLength i b) - 1) := by
              have h := YoungDiagram.hookWalkWeight_unfold_noncorner hmem_ib hone_ib (i, j)
              show μ.hookWalkWeight i b (i, j) = _
              rw [h]; congr 1
              rw [@Finset.sum_attach _ _ _ (μ.hookCellsExcl i b)
                (fun v => μ.hookWalkWeight v.1 v.2 (i, j))]
            rw [YoungDiagram.hookCellsExcl,
                Finset.sum_union (YoungDiagram.hookCellsExcl_disjoint μ i b),
                Finset.sum_image (by intro x _ y _ h; simpa [Prod.ext_iff] using h),
                Finset.sum_image (by intro x _ y _ h; simpa [Prod.ext_iff] using h)] at hunf
            simp only [Prod.fst, Prod.snd] at hunf
            rw [hrl] at hunf
            have hleg_van : (Finset.Ico (i + 1) (μ.colLen b)).sum
                (fun a' => μ.hookWalkWeight a' b (i, j)) = 0 :=
              Finset.sum_eq_zero (fun a' ha' => by
                simp [Finset.mem_Ico] at ha'
                exact YoungDiagram.hookWalkWeight_zero_of_row_gt
                  (by omega) (YoungDiagram.mem_iff_lt_colLen.mpr ha'.2))
            rw [hleg_van, add_zero] at hunf
            have hh_ib : (↑(μ.hookLength i b) - 1 : ℚ) ≠ 0 := ne_of_gt (by
              have h1 := YoungDiagram.hookLength_pos μ i b hmem_ib
              have h2 : 1 < μ.hookLength i b := by omega
              exact_mod_cast (show (0 : ℤ) < (μ.hookLength i b : ℤ) - 1 by omega))
            rw [hunf, mul_div_cancel₀ _ hh_ib]
          have hrec_aj : (Finset.Ico (a + 1) (i + 1)).sum
              (fun a' => μ.hookWalkWeight a' j (i, j)) =
              (↑(μ.hookLength a j) - 1) * μ.hookWalkWeight a j (i, j) := by
            have hunf : μ.hookWalkWeight a j (i, j) =
                (μ.hookCellsExcl a j).sum (fun v => μ.hookWalkWeight v.1 v.2 (i, j)) /
                  (↑(μ.hookLength a j) - 1) := by
              have h := YoungDiagram.hookWalkWeight_unfold_noncorner hmem_aj hone_aj (i, j)
              show μ.hookWalkWeight a j (i, j) = _
              rw [h]; congr 1
              rw [@Finset.sum_attach _ _ _ (μ.hookCellsExcl a j)
                (fun v => μ.hookWalkWeight v.1 v.2 (i, j))]
            rw [YoungDiagram.hookCellsExcl,
                Finset.sum_union (YoungDiagram.hookCellsExcl_disjoint μ a j),
                Finset.sum_image (by intro x _ y _ h; simpa [Prod.ext_iff] using h),
                Finset.sum_image (by intro x _ y _ h; simpa [Prod.ext_iff] using h)] at hunf
            simp only [Prod.fst, Prod.snd] at hunf
            rw [hcl] at hunf
            have harm_van : (Finset.Ico (j + 1) (μ.rowLen a)).sum
                (fun b' => μ.hookWalkWeight a b' (i, j)) = 0 :=
              Finset.sum_eq_zero (fun b' hb' => by
                simp [Finset.mem_Ico] at hb'
                exact YoungDiagram.hookWalkWeight_zero_of_col_gt
                  (by omega) (YoungDiagram.mem_iff_lt_rowLen.mpr hb'.2))
            rw [harm_van, zero_add] at hunf
            have hh_aj : (↑(μ.hookLength a j) - 1 : ℚ) ≠ 0 := ne_of_gt (by
              have h1 := YoungDiagram.hookLength_pos μ a j hmem_aj
              have h2 : 1 < μ.hookLength a j := by omega
              exact_mod_cast (show (0 : ℤ) < (μ.hookLength a j : ℤ) - 1 by omega))
            rw [hunf, mul_div_cancel₀ _ hh_aj]
          rw [hrec_ib, hrec_aj]
          -- Now: w(a,j)*w(i,b)*(h(a,b)-1) =
          --   w(a,j) * ((h(i,b)-1)*w(i,b)) + ((h(a,j)-1)*w(a,j)) * w(i,b)
          -- = w(a,j)*w(i,b)*[(h(i,b)-1)+(h(a,j)-1)]
          -- = w(a,j)*w(i,b)*(h(a,b)-1) by hookLength_sub_one_decomp
          -- The ℕ decomposition: h(a,b) - 1 = (h(a,j) - 1) + (h(i,b) - 1)
          have hdecomp := YoungDiagram.hookLength_sub_one_decomp hc ha hb hmem
          -- Cast to ℚ: h(a,b) = h(a,j) + h(i,b) - 1
          have hd : (μ.hookLength a b : ℚ) =
              (μ.hookLength a j : ℚ) + (μ.hookLength i b : ℚ) - 1 := by
            have h1 := YoungDiagram.hookLength_pos μ a b hmem
            have h2 := YoungDiagram.hookLength_pos μ a j hmem_aj
            have h3 := YoungDiagram.hookLength_pos μ i b hmem_ib
            have : (μ.hookLength a b : ℤ) =
                (μ.hookLength a j : ℤ) + (μ.hookLength i b : ℤ) - 1 := by
              zify [h1, h2, h3] at hdecomp; linarith
            exact_mod_cast this
          rw [hd]; ring

/-- Row partial sum telescoping: for an outer corner (i,j), the sum of w(i,b',(i,j))
over b' from b to j equals the product of h(i,b')/(h(i,b')-1) over b' from b to j-1. -/
private lemma YoungDiagram.hookWalkWeight_row_telescope
    {μ : YoungDiagram} {i j : ℕ} (hc : μ.IsOuterCorner i j)
    {b : ℕ} (hb : b ≤ j) :
    (Finset.Ico b (j + 1)).sum (fun b' => μ.hookWalkWeight i b' (i, j)) =
      (Finset.Ico b j).prod (fun b' =>
        (μ.hookLength i b' : ℚ) / (μ.hookLength i b' - 1 : ℚ)) := by
  have hrl := Etingof.YoungDiagram.IsOuterCorner.rowLen_eq hc
  suffices ∀ n (b : ℕ), b ≤ j → j + 1 - b = n →
      (Finset.Ico b (j + 1)).sum (fun b' => μ.hookWalkWeight i b' (i, j)) =
        (Finset.Ico b j).prod (fun b' =>
          (μ.hookLength i b' : ℚ) / (μ.hookLength i b' - 1 : ℚ)) from
    this _ b hb rfl
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro b hb hn
    by_cases hbj : b = j
    · -- Base: b = j
      rw [show Finset.Ico b (j + 1) = {b} from by ext; simp [Finset.mem_Ico]; omega]
      rw [Finset.sum_singleton]
      rw [show Finset.Ico b j = ∅ from by ext; simp [Finset.mem_Ico]; omega]
      rw [Finset.prod_empty, hbj, YoungDiagram.hookWalkWeight_corner hc]
    · have hblt : b < j := lt_of_le_of_ne hb hbj
      rw [show Finset.Ico b (j + 1) = {b} ∪ Finset.Ico (b + 1) (j + 1) from by
            ext x; simp [Finset.mem_Ico]; omega]
      rw [Finset.sum_union (Finset.disjoint_singleton_left.mpr (by simp [Finset.mem_Ico]))]
      simp only [Finset.sum_singleton]
      have ih_val := ih (j - b) (by omega) (b + 1) (by omega) (by omega)
      rw [show Finset.Ico b j = {b} ∪ Finset.Ico (b + 1) j from by
            ext x; simp [Finset.mem_Ico]; omega]
      rw [Finset.prod_union (Finset.disjoint_singleton_left.mpr (by simp [Finset.mem_Ico]))]
      simp only [Finset.prod_singleton]
      have hmem_ib : (i, b) ∈ μ.cells := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      have hone_ib : μ.hookLength i b ≠ 1 := by
        intro h
        have hoc := (Etingof.YoungDiagram.hookLength_eq_one_iff_outerCorner
          (by rw [YoungDiagram.mem_cells] at hmem_ib; exact hmem_ib)).mp h
        have := Etingof.YoungDiagram.IsOuterCorner.rowLen_eq hoc; omega
      have hh_pos : (0 : ℚ) < μ.hookLength i b - 1 := by
        have := YoungDiagram.hookLength_pos μ i b hmem_ib
        have : 1 < μ.hookLength i b := by omega
        exact_mod_cast (show (0 : ℤ) < (μ.hookLength i b : ℤ) - 1 by omega)
      have hw_eq : μ.hookWalkWeight i b (i, j) =
          (Finset.Ico (b + 1) (j + 1)).sum (fun b' => μ.hookWalkWeight i b' (i, j)) /
            (μ.hookLength i b - 1 : ℚ) := by
        rw [YoungDiagram.hookWalkWeight_unfold_noncorner hmem_ib hone_ib]
        congr 1
        show (∑ x ∈ (μ.hookCellsExcl i b).attach,
            μ.hookWalkWeight x.val.1 x.val.2 (i, j)) = _
        rw [@Finset.sum_attach _ _ _ (μ.hookCellsExcl i b)
            (fun v => μ.hookWalkWeight v.1 v.2 (i, j))]
        rw [YoungDiagram.hookCellsExcl,
            Finset.sum_union (YoungDiagram.hookCellsExcl_disjoint μ i b),
            Finset.sum_image (by intro x _ y _ h; simpa [Prod.ext_iff] using h),
            Finset.sum_image (by intro x _ y _ h; simpa [Prod.ext_iff] using h)]
        simp only [Prod.fst, Prod.snd]
        rw [hrl]
        have hleg_van : (Finset.Ico (i + 1) (μ.colLen b)).sum
            (fun a' => μ.hookWalkWeight a' b (i, j)) = 0 :=
          Finset.sum_eq_zero (fun a' ha' => by
            simp [Finset.mem_Ico] at ha'
            exact YoungDiagram.hookWalkWeight_zero_of_row_gt
              (by omega) (YoungDiagram.mem_iff_lt_colLen.mpr ha'.2))
        rw [hleg_van, add_zero]
      rw [hw_eq, ih_val]
      have hne : (↑(μ.hookLength i b) - 1 : ℚ) ≠ 0 := ne_of_gt hh_pos
      field_simp
      ring

/-- Column partial sum telescoping: symmetric to row_telescope. -/
private lemma YoungDiagram.hookWalkWeight_col_telescope
    {μ : YoungDiagram} {i j : ℕ} (hc : μ.IsOuterCorner i j)
    {a : ℕ} (ha : a ≤ i) :
    (Finset.Ico a (i + 1)).sum (fun a' => μ.hookWalkWeight a' j (i, j)) =
      (Finset.Ico a i).prod (fun a' =>
        (μ.hookLength a' j : ℚ) / (μ.hookLength a' j - 1 : ℚ)) := by
  have hcl := Etingof.YoungDiagram.IsOuterCorner.colLen_eq hc
  suffices ∀ n (a : ℕ), a ≤ i → i + 1 - a = n →
      (Finset.Ico a (i + 1)).sum (fun a' => μ.hookWalkWeight a' j (i, j)) =
        (Finset.Ico a i).prod (fun a' =>
          (μ.hookLength a' j : ℚ) / (μ.hookLength a' j - 1 : ℚ)) from
    this _ a ha rfl
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro a ha hn
    by_cases haj : a = i
    · rw [show Finset.Ico a (i + 1) = {a} from by ext; simp [Finset.mem_Ico]; omega]
      rw [Finset.sum_singleton]
      rw [show Finset.Ico a i = ∅ from by ext; simp [Finset.mem_Ico]; omega]
      rw [Finset.prod_empty, haj, YoungDiagram.hookWalkWeight_corner hc]
    · have halt : a < i := lt_of_le_of_ne ha haj
      rw [show Finset.Ico a (i + 1) = {a} ∪ Finset.Ico (a + 1) (i + 1) from by
            ext x; simp [Finset.mem_Ico]; omega]
      rw [Finset.sum_union (Finset.disjoint_singleton_left.mpr (by simp [Finset.mem_Ico]))]
      simp only [Finset.sum_singleton]
      have ih_val := ih (i - a) (by omega) (a + 1) (by omega) (by omega)
      rw [show Finset.Ico a i = {a} ∪ Finset.Ico (a + 1) i from by
            ext x; simp [Finset.mem_Ico]; omega]
      rw [Finset.prod_union (Finset.disjoint_singleton_left.mpr (by simp [Finset.mem_Ico]))]
      simp only [Finset.prod_singleton]
      have hmem_aj : (a, j) ∈ μ.cells := YoungDiagram.mem_iff_lt_colLen.mpr (by omega)
      have hone_aj : μ.hookLength a j ≠ 1 := by
        intro h
        have hoc := (Etingof.YoungDiagram.hookLength_eq_one_iff_outerCorner
          (by rw [YoungDiagram.mem_cells] at hmem_aj; exact hmem_aj)).mp h
        have := Etingof.YoungDiagram.IsOuterCorner.colLen_eq hoc; omega
      have hh_pos : (0 : ℚ) < μ.hookLength a j - 1 := by
        have := YoungDiagram.hookLength_pos μ a j hmem_aj
        have : 1 < μ.hookLength a j := by omega
        exact_mod_cast (show (0 : ℤ) < (μ.hookLength a j : ℤ) - 1 by omega)
      have hw_eq : μ.hookWalkWeight a j (i, j) =
          (Finset.Ico (a + 1) (i + 1)).sum (fun a' => μ.hookWalkWeight a' j (i, j)) /
            (μ.hookLength a j - 1 : ℚ) := by
        rw [YoungDiagram.hookWalkWeight_unfold_noncorner hmem_aj hone_aj]
        congr 1
        show (∑ x ∈ (μ.hookCellsExcl a j).attach,
            μ.hookWalkWeight x.val.1 x.val.2 (i, j)) = _
        rw [@Finset.sum_attach _ _ _ (μ.hookCellsExcl a j)
            (fun v => μ.hookWalkWeight v.1 v.2 (i, j))]
        rw [YoungDiagram.hookCellsExcl,
            Finset.sum_union (YoungDiagram.hookCellsExcl_disjoint μ a j),
            Finset.sum_image (by intro x _ y _ h; simpa [Prod.ext_iff] using h),
            Finset.sum_image (by intro x _ y _ h; simpa [Prod.ext_iff] using h)]
        simp only [Prod.fst, Prod.snd]
        rw [hcl]
        have harm_van : (Finset.Ico (j + 1) (μ.rowLen a)).sum
            (fun b' => μ.hookWalkWeight a b' (i, j)) = 0 :=
          Finset.sum_eq_zero (fun b' hb' => by
            simp [Finset.mem_Ico] at hb'
            exact YoungDiagram.hookWalkWeight_zero_of_col_gt
              (by omega) (YoungDiagram.mem_iff_lt_rowLen.mpr hb'.2))
        rw [harm_van, zero_add]
      rw [hw_eq, ih_val]
      have hne : (↑(μ.hookLength a j) - 1 : ℚ) ≠ 0 := ne_of_gt hh_pos
      field_simp
      ring

/-- HP(μ)/HP(μ\c) decomposes as a product over arm cells times a product over leg cells,
indexed by Finset.range rather than μ.cells. -/
private lemma YoungDiagram.hookRatio_eq_range_prods
    {μ : YoungDiagram} {i j : ℕ} (hc : μ.IsOuterCorner i j) :
    (μ.hookLengthProduct : ℚ) / ((μ.removeCorner i j hc).hookLengthProduct : ℚ) =
      (Finset.range j).prod (fun b =>
        (μ.hookLength i b : ℚ) / (μ.hookLength i b - 1 : ℚ)) *
      (Finset.range i).prod (fun a =>
        (μ.hookLength a j : ℚ) / (μ.hookLength a j - 1 : ℚ)) := by
  have hrl := Etingof.YoungDiagram.IsOuterCorner.rowLen_eq hc
  have hcl := Etingof.YoungDiagram.IsOuterCorner.colLen_eq hc
  rw [Etingof.YoungDiagram.hookRatio_eq_prod_div hc]
  -- Replace each h/h' with conditional on arm∨leg
  have hcond : (μ.cells.erase (i, j)).prod (fun c =>
      (μ.hookLength c.1 c.2 : ℚ) /
        ((μ.removeCorner i j hc).hookLength c.1 c.2 : ℚ)) =
    (μ.cells.erase (i, j)).prod (fun c =>
      if c.1 = i ∨ c.2 = j then
        (μ.hookLength c.1 c.2 : ℚ) / (μ.hookLength c.1 c.2 - 1 : ℚ)
      else 1) := by
    apply Finset.prod_congr rfl
    intro ⟨a, b⟩ hmem
    have hmem' := Finset.mem_of_mem_erase hmem
    have hne := Finset.ne_of_mem_erase hmem
    by_cases hai : a = i
    · have hblt : b < j := by
        have := YoungDiagram.mem_iff_lt_rowLen.mp (hai ▸ hmem')
        have : b ≠ j := fun h => hne (Prod.ext hai h); omega
      rw [if_pos (Or.inl hai)]
      have hmem_ib := hai ▸ hmem'
      have h_pos := YoungDiagram.hookLength_pos μ i b hmem_ib
      congr 1; simp only [Prod.fst, Prod.snd]
      rw [hai, Etingof.YoungDiagram.removeCorner_hookLength_row hc hblt]
      exact Nat.cast_sub (by omega)
    · by_cases hbj : b = j
      · have halt : a < i := by
          have := YoungDiagram.mem_iff_lt_colLen.mp (hbj ▸ hmem')
          omega
        rw [if_pos (Or.inr hbj)]
        have hmem_aj := hbj ▸ hmem'
        have h_pos := YoungDiagram.hookLength_pos μ a j hmem_aj
        congr 1; simp only [Prod.fst, Prod.snd]
        rw [hbj, Etingof.YoungDiagram.removeCorner_hookLength_col hc halt]
        exact Nat.cast_sub (by omega)
      · rw [if_neg (by push_neg; exact ⟨hai, hbj⟩)]
        simp only [Prod.fst, Prod.snd]
        rw [Etingof.YoungDiagram.removeCorner_hookLength_other hc hai hbj]
        have h_pos := YoungDiagram.hookLength_pos μ a b hmem'
        exact div_self (Nat.cast_ne_zero.mpr (by omega))
  rw [hcond, ← Finset.prod_filter]
  -- Show filter = arm_image ∪ leg_image
  have hfilter_eq : (μ.cells.erase (i, j)).filter (fun c => c.1 = i ∨ c.2 = j) =
      (Finset.range j).image (fun b => (i, b)) ∪
      (Finset.range i).image (fun a => (a, j)) := by
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_union,
      Finset.mem_image, Finset.mem_range, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨hne, hmem⟩, hai | hbj⟩
      · left; refine ⟨b, ?_, ?_, ?_⟩
        · have := YoungDiagram.mem_iff_lt_rowLen.mp (hai ▸ hmem)
          have : b ≠ j := fun h => hne (Prod.ext hai h); omega
        · exact hai.symm
        · rfl
      · right; refine ⟨a, ?_, ?_, ?_⟩
        · have := YoungDiagram.mem_iff_lt_colLen.mp (hbj ▸ hmem)
          have : a ≠ i := fun h => hne (Prod.ext h hbj); omega
        · rfl
        · exact hbj.symm
    · rintro (⟨b', hb', rfl, rfl⟩ | ⟨a', ha', rfl, rfl⟩)
      · exact ⟨⟨by intro h; simp [Prod.ext_iff] at h; omega,
                 YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)⟩, Or.inl rfl⟩
      · exact ⟨⟨by intro h; simp [Prod.ext_iff] at h; omega,
                 YoungDiagram.mem_iff_lt_colLen.mpr (by omega)⟩, Or.inr rfl⟩
  rw [hfilter_eq]
  -- Split by disjoint union
  rw [Finset.prod_union (by
        rw [Finset.disjoint_left]; intro ⟨a, b⟩ h1 h2
        simp [Finset.mem_image, Finset.mem_range, Prod.ext_iff] at h1 h2
        obtain ⟨_, _, rfl, rfl⟩ := h1; obtain ⟨_, ha', rfl, _⟩ := h2; omega)]
  conv_lhs =>
    arg 1; rw [Finset.prod_image (by intro x _ y _ h; simpa [Prod.ext_iff] using h)]
  conv_lhs =>
    arg 2; rw [Finset.prod_image (by intro x _ y _ h; simpa [Prod.ext_iff] using h)]

/- Column identity (Property 2 of GNW hook walk).

For each outer corner c, the sum of hook walk weights over all cells
equals HP(μ)/HP(μ\c). This is the hard direction of the GNW proof. -/

/-- When μ has exactly one cell (which must be a corner), the column sum is 1
and the hook ratio is 1, so the identity holds. -/
private lemma YoungDiagram.hookWalkWeight_col_sum_singleton
    (μ : YoungDiagram) {i j : ℕ} (hc : μ.IsOuterCorner i j)
    (hcard : μ.cells.card = 1) :
    μ.cells.sum (fun u => μ.hookWalkWeight u.1 u.2 (i, j)) =
      (μ.hookLengthProduct : ℚ) /
        ((μ.removeCorner i j hc).hookLengthProduct : ℚ) := by
  -- μ has exactly one cell, which must be (i, j)
  have honly : μ.cells = {(i, j)} := by
    have := Finset.card_eq_one.mp hcard
    obtain ⟨a, ha⟩ := this
    rw [ha]
    have : (i, j) ∈ μ.cells := hc.1
    rw [ha] at this
    exact congrArg _ (Finset.mem_singleton.mp this).symm
  -- LHS: only one cell (i,j), w(c,c) = 1
  rw [honly, Finset.sum_singleton]
  rw [YoungDiagram.hookWalkWeight_corner hc]
  -- RHS: HP(μ) = 1 (single cell with hook length 1), HP(μ\c) = 1 (empty)
  have hHP : μ.hookLengthProduct = 1 := by
    unfold YoungDiagram.hookLengthProduct
    rw [honly, Finset.prod_singleton]
    exact Etingof.YoungDiagram.hookLength_outerCorner hc
  have hHP' : (μ.removeCorner i j hc).hookLengthProduct = 1 := by
    unfold YoungDiagram.hookLengthProduct
    have : (μ.removeCorner i j hc).cells = ∅ := by
      simp [YoungDiagram.removeCorner, honly]
    rw [this, Finset.prod_empty]
  rw [hHP, hHP']
  simp

theorem YoungDiagram.hookWalkWeight_col_sum
    (μ : YoungDiagram) {i j : ℕ} (hc : μ.IsOuterCorner i j) :
    μ.cells.sum (fun u => μ.hookWalkWeight u.1 u.2 (i, j)) =
      (μ.hookLengthProduct : ℚ) /
        ((μ.removeCorner i j hc).hookLengthProduct : ℚ) := by
  -- Strong induction on |μ.cells|
  suffices h : ∀ (n : ℕ) (μ : YoungDiagram) (i j : ℕ) (hc : μ.IsOuterCorner i j),
      μ.cells.card = n →
      μ.cells.sum (fun u => μ.hookWalkWeight u.1 u.2 (i, j)) =
        (μ.hookLengthProduct : ℚ) /
          ((μ.removeCorner i j hc).hookLengthProduct : ℚ) from
    h _ μ i j hc rfl
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro μ i j hc hcard
    -- Base case: single cell
    by_cases hn : n ≤ 1
    · have hcard1 : μ.cells.card = 1 := by
        have hpos : 0 < μ.cells.card := Finset.card_pos.mpr ⟨(i, j), hc.1⟩
        omega
      exact hookWalkWeight_col_sum_singleton μ hc hcard1
    · -- Inductive step: n > 1
      push_neg at hn
      -- Step 1: Restrict to rectangle {(a,b) : a ≤ i, b ≤ j} via vanishing
      have hrl := Etingof.YoungDiagram.IsOuterCorner.rowLen_eq hc
      have hcl := Etingof.YoungDiagram.IsOuterCorner.colLen_eq hc
      -- Partition cells into those in the rectangle and those outside
      have hsum_rect : μ.cells.sum (fun u => μ.hookWalkWeight u.1 u.2 (i, j)) =
          (μ.cells.filter (fun u => u.1 ≤ i ∧ u.2 ≤ j)).sum
            (fun u => μ.hookWalkWeight u.1 u.2 (i, j)) := by
        rw [Finset.sum_filter_of_ne]
        intro ⟨a, b⟩ hmem hne
        by_contra hab
        simp only [Prod.fst, Prod.snd, not_and_or, not_le] at hab
        rcases hab with ha | hb
        · exact absurd (YoungDiagram.hookWalkWeight_zero_of_row_gt ha hmem) hne
        · exact absurd (YoungDiagram.hookWalkWeight_zero_of_col_gt hb hmem) hne
      rw [hsum_rect]
      -- Step 2: Apply factorization w(a,b,c) = w(a,j,c) * w(i,b,c)
      have hfact : (μ.cells.filter (fun u => u.1 ≤ i ∧ u.2 ≤ j)).sum
            (fun u => μ.hookWalkWeight u.1 u.2 (i, j)) =
          (μ.cells.filter (fun u => u.1 ≤ i ∧ u.2 ≤ j)).sum
            (fun u => μ.hookWalkWeight u.1 j (i, j) * μ.hookWalkWeight i u.2 (i, j)) := by
        apply Finset.sum_congr rfl
        intro ⟨a, b⟩ hmem
        simp only [Finset.mem_filter, decide_eq_true_eq] at hmem
        exact YoungDiagram.hookWalkWeight_factorization hc hmem.2.1 hmem.2.2 hmem.1
      rw [hfact]
      -- Step 3: The filter set = Ico 0 (i+1) ×ˢ Ico 0 (j+1) ∩ μ.cells
      -- Actually, every cell (a,b) with a ≤ i, b ≤ j is in μ because μ is upward-closed
      -- and (i,j) ∈ μ. So the filter = Finset.Ico 0 (i+1) ×ˢ Finset.Ico 0 (j+1)
      have hfilter_eq : μ.cells.filter (fun u => u.1 ≤ i ∧ u.2 ≤ j) =
          Finset.Ico 0 (i + 1) ×ˢ Finset.Ico 0 (j + 1) := by
        ext ⟨a, b⟩
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Ico, decide_eq_true_eq]
        constructor
        · rintro ⟨_, ha, hb⟩; exact ⟨⟨Nat.zero_le _, Nat.lt_succ_of_le ha⟩,
            ⟨Nat.zero_le _, Nat.lt_succ_of_le hb⟩⟩
        · rintro ⟨⟨_, ha⟩, ⟨_, hb⟩⟩
          have ha' : a ≤ i := Nat.lt_succ_iff.mp ha
          have hb' : b ≤ j := Nat.lt_succ_iff.mp hb
          exact ⟨μ.up_left_mem ha' hb' hc.1, ha', hb'⟩
      rw [hfilter_eq]
      -- Step 4: Fubini — ∑_{(a,b) ∈ rows × cols} f(a) * g(b) = (∑_a f(a)) * (∑_b g(b))
      rw [Finset.sum_product]
      -- Now: ∑_{a ∈ Ico 0 (i+1)} ∑_{b ∈ Ico 0 (j+1)} w(a,j,c) * w(i,b,c)
      -- Factor out w(a,j,c) from inner sum
      simp_rw [← Finset.mul_sum]
      -- Now: ∑_{a ∈ Ico 0 (i+1)} w(a,j,c) * (∑_{b ∈ Ico 0 (j+1)} w(i,b,c))
      -- The inner sum is independent of a, factor it out
      rw [← Finset.sum_mul]
      -- Now: (∑_{a ∈ Ico 0 (i+1)} w(a,j,c)) * (∑_{b ∈ Ico 0 (j+1)} w(i,b,c))
      -- Step 5: Apply telescoping
      rw [show Finset.Ico 0 (i + 1) = Finset.Ico 0 (i + 1) from rfl]
      rw [show Finset.Ico 0 (j + 1) = Finset.Ico 0 (j + 1) from rfl]
      rw [YoungDiagram.hookWalkWeight_col_telescope hc (Nat.zero_le _)]
      rw [YoungDiagram.hookWalkWeight_row_telescope hc (Nat.zero_le _)]
      -- Now: (∏_{a<i} h(a,j)/(h(a,j)-1)) * (∏_{b<j} h(i,b)/(h(i,b)-1))
      -- Step 6: Match with HP/HP' decomposition
      rw [YoungDiagram.hookRatio_eq_range_prods hc]
      simp only [Finset.range_eq_Ico]
      ring

namespace Etingof

noncomputable section

/-- The hook quotient identity: ∑_{c ∈ outerCorners} HP(μ)/HP(μ\c) = |μ|.

This is a deep combinatorial identity. The proof uses the Greene–Nijenhuis–Wilf
hook walk argument: define a weight function w(u,c) for each cell u and corner c
such that ∑_c w(u,c) = 1 (rows sum to 1) and ∑_u w(u,c) = HP(μ)/HP(μ\c)
(columns give the hook ratio). Then swap sums: n = ∑_u 1 = ∑_c HP/HP(μ\c).

The weight function is defined by the hook walk: from cell u, at each step
pick uniformly from the h(u)-1 other cells in hook(u), recurse.
w(u,c) = (1/(h(u)-1)) × ∑_{v ∈ hook(u)\{u}} w(v,c) for non-corners.
w(u,c) = δ(u,c) for corners (where h(u) = 1).

Infrastructure needed:
- hookLength_lt_of_right/down: hook lengths strictly decrease along walks
- hookWalkWeight definition by WF recursion on hookLength
- Property 1: ∑_c w(u,c) = 1 (by induction on hookLength)
- Property 2: ∑_u w(u,c) = HP(μ)/HP(μ\c) (the hard GNW lemma)
- Fubini: swap the finite double sum
-/
private lemma YoungDiagram.hook_quotient_identity_yd
    (μ : YoungDiagram) :
    μ.outerCorners.attach.sum (fun c =>
      (μ.hookLengthProduct : ℚ) /
        ((μ.removeCorner c.val.1 c.val.2
          (YoungDiagram.mem_outerCorners.mp
            c.property)).hookLengthProduct : ℚ)) =
      (μ.cells.card : ℚ) := by
  -- Step 1: Replace each HP/HP(μ\c) by ∑_u w(u,c) using the column identity
  have hstep1 : μ.outerCorners.attach.sum (fun c =>
      (μ.hookLengthProduct : ℚ) /
        ((μ.removeCorner c.val.1 c.val.2
          (YoungDiagram.mem_outerCorners.mp c.property)).hookLengthProduct : ℚ)) =
      μ.outerCorners.attach.sum (fun c =>
        μ.cells.sum (fun u => μ.hookWalkWeight u.1 u.2 c.val)) := by
    apply Finset.sum_congr rfl
    intro c _
    exact (YoungDiagram.hookWalkWeight_col_sum μ
      (YoungDiagram.mem_outerCorners.mp c.property)).symm
  rw [hstep1]
  -- Step 2: Swap the sums (Fubini): ∑_c ∑_u = ∑_u ∑_c
  rw [Finset.sum_comm]
  -- Step 3: Each ∑_c w(u,c) = 1 by Property 1, after converting attach sum
  have hstep3 : μ.cells.sum (fun u =>
      μ.outerCorners.attach.sum (fun c =>
        μ.hookWalkWeight u.1 u.2 c.val)) =
      μ.cells.sum (fun _ => (1 : ℚ)) := by
    apply Finset.sum_congr rfl
    intro u hu
    rw [Finset.sum_attach]
    exact YoungDiagram.hookWalkWeight_row_sum μ u.1 u.2 hu
  rw [hstep3]
  -- Step 4: ∑_u 1 = |μ|
  simp

/-- The hook quotient identity: for a partition λ of n+1, the sum over
outer corners c of hookProd(λ)/hookProd(λ\c) equals n+1. Individual
terms may be non-integer, so this is stated over ℚ. -/
private lemma hook_quotient_identity
    (n : ℕ) (la : Nat.Partition (n + 1)) :
    la.toYoungDiagram.outerCorners.attach.sum (fun c =>
      (la.toYoungDiagram.hookLengthProduct : ℚ) /
        (((la.removeOuterCorner c.val
          (YoungDiagram.mem_outerCorners.mp
            c.property)).toYoungDiagram
              ).hookLengthProduct)) =
      (n + 1 : ℚ) := by
  have h := YoungDiagram.hook_quotient_identity_yd
    la.toYoungDiagram
  rw [Nat.Partition.toYoungDiagram_card] at h
  simp_rw [Nat.Partition.toYoungDiagram_removeOuterCorner]
    at h ⊢
  push_cast at h ⊢
  exact h

/-- Hook length product identity: for the inductive step, we need that
multiplying the branching count by the hook product and using the IH gives (n+1)!.

Specifically: ∑_c |SYT(n, λ\c)| × hookProd(λ) = (n+1) × n!
This follows from the IH (|SYT(n, λ\c)| × hookProd(λ\c) = n!) and the
hook quotient identity: ∑_c hookProd(λ)/hookProd(λ\c) = n+1. -/
theorem hook_corner_sum (n : ℕ) (la : Nat.Partition (n + 1))
    (ih : ∀ la' : Nat.Partition n,
      Nat.card (StandardYoungTableau n la') *
        la'.toYoungDiagram.hookLengthProduct = n.factorial) :
    la.toYoungDiagram.outerCorners.attach.sum (fun c =>
      Nat.card (StandardYoungTableau n
        (la.removeOuterCorner c.val
          (YoungDiagram.mem_outerCorners.mp c.property)))) *
      la.toYoungDiagram.hookLengthProduct = (n + 1).factorial := by
  -- Cast to ℚ where division is exact (Nat.cast is injective since CharZero)
  suffices hq : ((la.toYoungDiagram.outerCorners.attach.sum (fun c =>
      Nat.card (StandardYoungTableau n
        (la.removeOuterCorner c.val
          (YoungDiagram.mem_outerCorners.mp c.property)))) *
      la.toYoungDiagram.hookLengthProduct : ℕ) : ℚ) =
      (((n + 1).factorial : ℕ) : ℚ) by exact_mod_cast hq
  push_cast [Finset.sum_mul]
  -- Goal: ∑_c ↑|SYT(n,λ\c)| * ↑H = ↑(n+1)!
  -- Rewrite each summand using IH: ↑|SYT| * ↑H = ↑n! * (↑H / ↑hp(c))
  have hsummand : ∀ (x : { c // c ∈ la.toYoungDiagram.outerCorners }),
      (Nat.card (StandardYoungTableau n (la.removeOuterCorner ↑x
        (YoungDiagram.mem_outerCorners.mp x.property))) : ℚ) *
      (la.toYoungDiagram.hookLengthProduct : ℚ) =
      (n.factorial : ℚ) * ((la.toYoungDiagram.hookLengthProduct : ℚ) /
        ((la.removeOuterCorner ↑x
          (YoungDiagram.mem_outerCorners.mp x.property)
            ).toYoungDiagram.hookLengthProduct : ℚ)) := by
    intro x
    set la' := la.removeOuterCorner ↑x (YoungDiagram.mem_outerCorners.mp x.property)
    have ih_c := ih la'
    have hne : (la'.toYoungDiagram.hookLengthProduct : ℚ) ≠ 0 := by
      exact_mod_cast (YoungDiagram.hookLengthProduct_pos la'.toYoungDiagram).ne'
    have hsyt : (Nat.card (StandardYoungTableau n la') : ℚ) =
        (n.factorial : ℚ) / (la'.toYoungDiagram.hookLengthProduct : ℚ) := by
      rw [eq_div_iff hne]
      exact_mod_cast ih_c
    rw [hsyt]
    ring
  simp_rw [hsummand]
  -- Goal: ∑_c ↑n! * (↑H / ↑hp(c)) = ↑(n+1)!
  -- Factor out ↑n!
  rw [← Finset.mul_sum]
  -- Goal: ↑n! * ∑_c (↑H / ↑hp(c)) = ↑(n+1)!
  rw [hook_quotient_identity]
  -- Goal: ↑n! * ↑(n+1) = ↑(n+1)!
  push_cast [Nat.factorial_succ]
  ring

/-- Inductive step: if the FRT formula holds for all partitions of n,
then it holds for all partitions of n+1.

Proved by combining the branching rule and the hook-corner-sum identity. -/
theorem card_standardYoungTableau_mul_succ (n : ℕ)
    (ih : ∀ la' : Nat.Partition n,
      Nat.card (StandardYoungTableau n la') *
        la'.toYoungDiagram.hookLengthProduct = n.factorial)
    (la : Nat.Partition (n + 1)) :
    Nat.card (StandardYoungTableau (n + 1) la) *
      la.toYoungDiagram.hookLengthProduct = (n + 1).factorial := by
  rw [syt_branching_rule n la]
  exact hook_corner_sum n la ih

/-- Frame–Robinson–Thrall theorem, multiplicative form.
Proved by induction on n using the base case and inductive step. -/
theorem card_standardYoungTableau_mul (n : ℕ) (la : Nat.Partition n) :
    Nat.card (StandardYoungTableau n la) * la.toYoungDiagram.hookLengthProduct =
      n.factorial := by
  induction n with
  | zero => exact card_standardYoungTableau_mul_zero la
  | succ n ih => exact card_standardYoungTableau_mul_succ n ih la

end

end Etingof
