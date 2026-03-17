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

/-- Hook length formula: dim V_λ = n! / ∏ h(i,j).
(Etingof Theorem 5.17.1)

The dimension of the Specht module V_λ equals n! divided by the product
of all hook lengths of the Young diagram of λ. -/
theorem Theorem5_17_1
    (n : ℕ) (la : Nat.Partition n) :
    Module.finrank ℂ (SpechtModule n la) =
      n.factorial / la.toYoungDiagram.hookLengthProduct := by
  sorry

end Etingof
