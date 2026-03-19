import Mathlib
import EtingofRepresentationTheory.Chapter5.Definition5_14_2
import EtingofRepresentationTheory.Chapter5.PolytabloidBasis
import EtingofRepresentationTheory.Chapter5.FRTHelpers

/-!
# Theorem 5.17.1: Hook Length Formula

The dimension of the Specht module V_λ is given by the hook length formula:

  dim V_λ = n! / ∏_{(i,j) ∈ λ} h(i,j)

where h(i,j) = λᵢ - j + λ'ⱼ - i - 1 is the hook length at cell (i,j)
(using 0-indexed cells), and λ' is the conjugate partition.

## Proof structure

The hook length formula decomposes into two independent results:

1. **Representation → combinatorics**: dim V_λ = |SYT(λ)|, proved via the
   polytabloid basis (see `PolytabloidBasis.lean`).

2. **Frame–Robinson–Thrall (1954)**: |SYT(λ)| = n! / ∏ h(i,j). Proved by
   induction on n via the branching rule (see `FRTHelpers.lean`).
-/

namespace Etingof

noncomputable section

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
