import Mathlib
import EtingofRepresentationTheory.Chapter5.Definition5_14_2
import EtingofRepresentationTheory.Chapter5.PolytabloidBasis

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

/-- A cell (i,j) is an outer corner of μ if it is in μ but removing it
leaves a valid Young diagram. Equivalently: (i,j) ∈ μ, (i+1,j) ∉ μ, (i,j+1) ∉ μ. -/
def YoungDiagram.IsOuterCorner (μ : YoungDiagram) (i j : ℕ) : Prop :=
  (i, j) ∈ μ.cells ∧ (i + 1, j) ∉ μ.cells ∧ (i, j + 1) ∉ μ.cells

namespace Etingof

noncomputable section

/-! ## Frame–Robinson–Thrall theorem

The core combinatorial identity is stated in multiplicative form to avoid
natural number division issues:

  |SYT(λ)| * ∏ h(i,j) = n!

This implies both the division form and the divisibility result.

**Required infrastructure (not in Mathlib)**:
The standard proof via the branching rule requires:
- Young diagram with a corner removed
- Branching bijection: SYT(λ) ≅ Σ_c SYT(λ \ c) (by mapping where n goes)
- Hook length recurrence: how ∏ h changes when removing a corner cell
- Connection between `StandardYoungTableau` (uses `sortedParts`)
  and `YoungDiagram.cells` (used by hook length definitions)

Alternative proofs (hook walk algorithm, Frobenius character formula + Vandermonde
determinant) require equally substantial infrastructure. -/

/-- Frame–Robinson–Thrall theorem, multiplicative form: the number of standard
Young tableaux of shape λ times the hook length product equals n!.

This is the core sorry: proving either this or the division form suffices
for the full hook length formula. The multiplicative form is preferred
because it avoids natural number division. -/
theorem card_standardYoungTableau_mul (n : ℕ) (la : Nat.Partition n) :
    Nat.card (StandardYoungTableau n la) * la.toYoungDiagram.hookLengthProduct =
      n.factorial := by
  sorry

/-- The hook length product divides n!. Follows from the multiplicative form
of the Frame–Robinson–Thrall theorem. -/
theorem hookLengthProduct_dvd_factorial (n : ℕ) (la : Nat.Partition n) :
    la.toYoungDiagram.hookLengthProduct ∣ n.factorial :=
  ⟨Nat.card (StandardYoungTableau n la), by linarith [card_standardYoungTableau_mul n la]⟩

/-- The dimension of V_λ equals the number of standard Young tableaux of shape λ.
This is the core representation-theoretic content: the polytabloid basis of the
Specht module is naturally indexed by SYT(λ).

The proof delegates to `finrank_spechtModule_eq_card_syt` (which uses
`Fintype.card`) and converts to `Nat.card`. The underlying proof constructs
the polytabloid basis: linear independence + spanning of polytabloids. -/
theorem finrank_spechtModule_eq_card_standardYoungTableau (n : ℕ) (la : Nat.Partition n) :
    Module.finrank ℂ (SpechtModule n la) =
      Nat.card (StandardYoungTableau n la) := by
  rw [Nat.card_eq_fintype_card]
  exact finrank_spechtModule_eq_card_syt n la

/-- Frame–Robinson–Thrall theorem (1954): the number of standard Young tableaux
of shape λ equals n! / ∏ h(i,j). Derived from the multiplicative form. -/
theorem card_standardYoungTableau_eq (n : ℕ) (la : Nat.Partition n) :
    Nat.card (StandardYoungTableau n la) =
      n.factorial / la.toYoungDiagram.hookLengthProduct := by
  have h := card_standardYoungTableau_mul n la
  have hpos := YoungDiagram.hookLengthProduct_pos la.toYoungDiagram
  rw [← h, Nat.mul_div_cancel _ hpos]

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
