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
  rw [YoungDiagram.IsOuterCorner.rowLen_eq hc,
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
    have hr := YoungDiagram.IsOuterCorner.rowLen_eq hc
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
  have := YoungDiagram.IsOuterCorner.rowLen_eq hc
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

private lemma YoungDiagram.hook_quotient_identity_yd
    (μ : YoungDiagram) :
    μ.outerCorners.attach.sum (fun c =>
      (μ.hookLengthProduct : ℚ) /
        ((μ.removeCorner c.val.1 c.val.2
          (YoungDiagram.mem_outerCorners.mp
            c.property)).hookLengthProduct : ℚ)) =
      (μ.cells.card : ℚ) := by
  sorry

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
