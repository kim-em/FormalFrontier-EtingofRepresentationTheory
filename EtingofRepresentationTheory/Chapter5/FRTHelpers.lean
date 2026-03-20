import Mathlib
import EtingofRepresentationTheory.Chapter5.Definition5_12_1
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
  -- Requires constructing the branching bijection:
  -- SYT(n+1, λ) ≃ Σ_{c ∈ outerCorners} SYT(n, λ\c)
  -- via "remove the cell containing the largest entry n+1"
  sorry

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
