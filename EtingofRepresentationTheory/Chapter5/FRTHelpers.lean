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
  show (μ'.rowLens : Multiset ℕ).sort (· ≥ ·) = μ'.rowLens
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
  -- Key steps:
  -- 1. Distribute hookProd(λ) into the sum
  -- 2. For each c: |SYT(n, λ\c)| × hookProd(λ)
  --    = |SYT(n, λ\c)| × hookProd(λ\c) × (hookProd(λ) / hookProd(λ\c))
  --    = n! × (hookProd(λ) / hookProd(λ\c))
  -- 3. The hook quotient identity: ∑_c hookProd(λ)/hookProd(λ\c) = n+1
  --    gives the final result (n+1) × n! = (n+1)!
  sorry

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
