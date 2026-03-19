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

namespace Etingof

noncomputable section

/-- The cell type of a partition is finite: cells (i,j) with i < length, j < row width.
Both coordinates are bounded (i < length, j < part i ≤ n), giving a finite set. -/
noncomputable instance partitionCell_fintype (n : ℕ) (la : Nat.Partition n) :
    Fintype { c : ℕ × ℕ // c.1 < la.sortedParts.length ∧
      c.2 < la.sortedParts.getD c.1 0 } := by
  classical
  haveI : Finite { c : ℕ × ℕ // c.1 < la.sortedParts.length ∧
      c.2 < la.sortedParts.getD c.1 0 } := by
    refine Finite.of_injective
      (fun (c : { c : ℕ × ℕ // c.1 < la.sortedParts.length ∧
          c.2 < la.sortedParts.getD c.1 0 }) =>
        show Fin la.sortedParts.length × Fin (n + 1) from
        ⟨⟨c.1.1, c.2.1⟩, ⟨c.1.2, by
          have hj := c.2.2
          have hi := c.2.1
          simp only [List.getD, List.getElem?_eq_getElem hi, Option.getD_some] at hj
          have : la.sortedParts[c.1.1] ≤ n := by
            calc la.sortedParts[c.1.1] ≤ la.sortedParts.sum :=
                  List.single_le_sum (fun x _ => Nat.zero_le x) _ (List.getElem_mem hi)
              _ = n := by
                  unfold Nat.Partition.sortedParts
                  rw [← Multiset.sum_coe, Multiset.sort_eq]; exact la.parts_sum
          omega⟩⟩) ?_
    intro ⟨⟨a1, a2⟩, ha⟩ ⟨⟨b1, b2⟩, hb⟩ h
    simp only [Prod.mk.injEq, Fin.mk.injEq] at h
    exact Subtype.ext (Prod.ext h.1 h.2)
  exact Fintype.ofFinite _

/-- StandardYoungTableau is a finite type: it is a subtype of functions
from a finite cell set to Fin n. -/
instance standardYoungTableau_finite (n : ℕ) (la : Nat.Partition n) :
    Finite (StandardYoungTableau n la) := by
  classical
  unfold StandardYoungTableau
  change Finite { f : { c : ℕ × ℕ // c.1 < la.sortedParts.length ∧
    c.2 < la.sortedParts.getD c.1 0 } → Fin n // _ }
  exact Subtype.finite

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
