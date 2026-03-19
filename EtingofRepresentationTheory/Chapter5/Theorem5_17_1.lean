import Mathlib
import EtingofRepresentationTheory.Chapter5.Definition5_14_2
import EtingofRepresentationTheory.Chapter5.Theorem5_12_2

/-!
# Theorem 5.17.1: Hook Length Formula

The dimension of the Specht module V_λ is given by the hook length formula:

  dim V_λ = n! / ∏_{(i,j) ∈ λ} h(i,j)

where h(i,j) = λᵢ - j + λ'ⱼ - i - 1 is the hook length at cell (i,j)
(using 0-indexed cells), and λ' is the conjugate partition.

## Mathlib correspondence

Mathlib has `YoungDiagram` but hook lengths are not defined. The hook length
formula is a major combinatorial result connecting Young diagrams to
representation dimensions.

## Proof structure

The hook length formula decomposes into two independent results:

1. **Representation → combinatorics**: dim V_λ = |SYT(λ)|, the number of standard
   Young tableaux of shape λ. This follows from exhibiting an explicit basis of
   the Specht module indexed by standard Young tableaux (via the polytabloid
   construction or the seminormal basis).

2. **Frame–Robinson–Thrall (1954)**: |SYT(λ)| = n! / ∏ h(i,j). This is a purely
   combinatorial identity. Standard proofs use either a direct inductive/bijective
   argument, or the RSK correspondence combined with the hook-walk algorithm.

Both results are deep and require substantial infrastructure not currently
available in Mathlib.
-/

/-- The hook length at cell (i, j) of a Young diagram.
For a cell (i,j), the hook consists of all cells directly to the right in the
same row, all cells directly below in the same column, plus the cell itself.
h(i,j) = (rowLen i - j) + (colLen j - i) - 1 -/
def YoungDiagram.hookLength (μ : YoungDiagram) (i j : ℕ) : ℕ :=
  μ.rowLen i + μ.colLen j - i - j - 1

/-- The product of all hook lengths of a Young diagram. -/
noncomputable def YoungDiagram.hookLengthProduct (μ : YoungDiagram) : ℕ :=
  μ.cells.prod (fun c => μ.hookLength c.1 c.2)

/-! ## Finiteness infrastructure for StandardYoungTableau -/

namespace Etingof

/-- Each row entry of a partition's sorted parts is bounded by the total sum. -/
private lemma getD_le_sum (l : List ℕ) (i : ℕ) : l.getD i 0 ≤ l.sum := by
  induction l generalizing i with
  | nil => simp [List.getD]
  | cons a as ih =>
    cases i with
    | zero =>
      show (a :: as).getD 0 0 ≤ (a :: as).sum
      rw [List.getD_cons_zero, List.sum_cons]
      omega
    | succ i =>
      simp only [List.getD_cons_succ, List.sum_cons]
      exact le_trans (ih i) (Nat.le_add_left _ _)

/-- The sorted parts of a partition of n sum to n. -/
private lemma sortedParts_sum' (n : ℕ) (la : Nat.Partition n) :
    la.sortedParts.sum = n := by
  have h := Multiset.sort_eq la.parts (· ≥ ·)
  have : (la.sortedParts : Multiset ℕ).sum = la.parts.sum := congrArg Multiset.sum h
  rw [Multiset.sum_coe] at this; rw [this, la.parts_sum]

/-- The cell type of a Young diagram (pairs (i,j) with i < #rows, j < row_length(i))
is finite, since all indices are bounded by n. -/
noncomputable instance cellFintype (n : ℕ) (la : Nat.Partition n) :
    Fintype { c : ℕ × ℕ // c.1 < la.sortedParts.length ∧ c.2 < la.sortedParts.getD c.1 0 } := by
  haveI : Fintype { c : ℕ × ℕ // c ∈ (Finset.range la.sortedParts.length ×ˢ Finset.range (n+1)) } :=
    (Finset.range la.sortedParts.length ×ˢ Finset.range (n+1)).fintypeCoeSort
  apply Fintype.ofInjective
    (fun ⟨c, hc⟩ => (⟨c, by
      simp only [Finset.mem_product, Finset.mem_range]
      exact ⟨hc.1, by have := getD_le_sum la.sortedParts c.1; have := sortedParts_sum' n la; omega⟩
    ⟩ : { c : ℕ × ℕ // c ∈ (Finset.range la.sortedParts.length ×ˢ Finset.range (n+1)) }))
  intro ⟨a, _⟩ ⟨b, _⟩ h
  exact Subtype.ext (Subtype.mk.inj h)

/-- The type of standard Young tableaux of a given shape is finite.
This follows from finiteness of the cell type and `Fin n`. -/
noncomputable instance sytFintype (n : ℕ) (la : Nat.Partition n) :
    Fintype (StandardYoungTableau n la) := by
  unfold StandardYoungTableau
  haveI := cellFintype n la
  exact Subtype.fintype _

noncomputable section

/-- The hook length product divides n!. This is a consequence of the
Frame–Robinson–Thrall theorem: n!/∏h(i,j) = |SYT(λ)| is a positive integer. -/
theorem hookLengthProduct_dvd_factorial (n : ℕ) (la : Nat.Partition n) :
    la.toYoungDiagram.hookLengthProduct ∣ n.factorial := by
  sorry

/-- The dimension of V_λ equals the number of standard Young tableaux of shape λ.
This is the core representation-theoretic content: the polytabloid basis of the
Specht module is naturally indexed by SYT(λ).

Proof sketch: For each standard Young tableau T, the polytabloid e_T = b_T · {T}
(column antisymmetrizer applied to the tabloid) lies in V_λ. The set {e_T} forms
a basis. This requires:
- The polytabloid construction and its properties
- Linear independence of polytabloids (via the straightening algorithm)
- Spanning (via the Young symmetrizer generating the module) -/
theorem finrank_spechtModule_eq_card_standardYoungTableau (n : ℕ) (la : Nat.Partition n) :
    Module.finrank ℂ (SpechtModule n la) =
      Nat.card (StandardYoungTableau n la) := by
  sorry

/-- Frame–Robinson–Thrall theorem (1954): the number of standard Young tableaux
of shape λ equals n! / ∏ h(i,j), where the product is over all cells of the
Young diagram and h(i,j) is the hook length.

Standard proof approaches:
1. Bijective proof via the hook walk algorithm (Greene–Nijenhuis–Wilf, 1979)
2. Inductive proof using the branching rule for SYT
3. Via the RSK correspondence and properties of the Plancherel measure -/
theorem card_standardYoungTableau_eq (n : ℕ) (la : Nat.Partition n) :
    Nat.card (StandardYoungTableau n la) =
      n.factorial / la.toYoungDiagram.hookLengthProduct := by
  sorry

/-- Hook length formula: dim V_λ = n! / ∏ h(i,j).
(Etingof Theorem 5.17.1)

The dimension of the Specht module V_λ equals n! divided by the product
of all hook lengths of the Young diagram of λ. -/
theorem Theorem5_17_1
    (n : ℕ) (la : Nat.Partition n) :
    Module.finrank ℂ (SpechtModule n la) =
      n.factorial / la.toYoungDiagram.hookLengthProduct := by
  rw [finrank_spechtModule_eq_card_standardYoungTableau,
      card_standardYoungTableau_eq]

end

end Etingof
