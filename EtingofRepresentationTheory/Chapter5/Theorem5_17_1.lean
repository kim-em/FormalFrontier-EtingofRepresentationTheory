import Mathlib

/-!
# Theorem 5.17.1: Hook Length Formula

The dimension of the Specht module V_λ is given by the hook length formula:

  dim V_λ = n! / ∏_{(i,j) ∈ λ} h(i,j)

where h(i,j) = λᵢ - j + λ'ⱼ - i + 1 is the hook length at cell (i,j),
and λ' is the conjugate partition.

## Mathlib correspondence

Mathlib has `YoungDiagram` but hook lengths are not defined. The hook length
formula is a major combinatorial result connecting Young diagrams to
representation dimensions.
-/

/-- Hook length formula: dim V_λ = n! / ∏ h(i,j).
(Etingof Theorem 5.17.1) -/
theorem Etingof.Theorem5_17_1
    (n : ℕ) (la : Nat.Partition n) :
    -- dim V_λ = n! / ∏_{(i,j) ∈ λ} h(i,j)
    (sorry : Prop) := by
  sorry
