import Mathlib
import EtingofRepresentationTheory.Chapter5.Definition5_12_1

/-!
# Finiteness of Standard Young Tableaux

This file provides `Fintype` and `Finite` instances for `StandardYoungTableau n la`,
extracted from Theorem5_17_1.lean to break a circular import dependency with
PolytabloidBasis.lean.
-/

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
lemma sortedParts_sum_eq (n : ℕ) (la : Nat.Partition n) :
    la.sortedParts.sum = n := by
  have h := Multiset.sort_eq la.parts (· ≥ ·)
  have : (la.sortedParts : Multiset ℕ).sum = la.parts.sum := congrArg Multiset.sum h
  rw [Multiset.sum_coe] at this; rw [this, la.parts_sum]

/-- The cell type of a Young diagram (pairs (i,j) with i < #rows, j < row_length(i))
is finite, since all indices are bounded by n. -/
noncomputable instance cellFintype (n : ℕ) (la : Nat.Partition n) :
    Fintype { c : ℕ × ℕ // c.1 < la.sortedParts.length ∧ c.2 < la.sortedParts.getD c.1 0 } := by
  haveI : Fintype { c : ℕ × ℕ //
      c ∈ (Finset.range la.sortedParts.length ×ˢ Finset.range (n+1)) } :=
    (Finset.range la.sortedParts.length ×ˢ Finset.range (n+1)).fintypeCoeSort
  apply Fintype.ofInjective
    (fun ⟨c, hc⟩ => (⟨c, by
      simp only [Finset.mem_product, Finset.mem_range]
      exact ⟨hc.1, by
        have := getD_le_sum la.sortedParts c.1
        have := sortedParts_sum_eq n la; omega⟩
    ⟩ : { c : ℕ × ℕ //
        c ∈ (Finset.range la.sortedParts.length ×ˢ Finset.range (n+1)) }))
  intro ⟨a, _⟩ ⟨b, _⟩ h
  exact Subtype.ext (Subtype.mk.inj h)

/-- The type of standard Young tableaux of a given shape is finite.
This follows from finiteness of the cell type and `Fin n`. -/
noncomputable instance sytFintype (n : ℕ) (la : Nat.Partition n) :
    Fintype (StandardYoungTableau n la) := by
  unfold StandardYoungTableau
  haveI := cellFintype n la
  exact Subtype.fintype _

/-- StandardYoungTableau is a finite type: it is a subtype of functions
from a finite cell set to Fin n. -/
instance standardYoungTableau_finite (n : ℕ) (la : Nat.Partition n) :
    Finite (StandardYoungTableau n la) := by
  classical
  unfold StandardYoungTableau
  change Finite { f : { c : ℕ × ℕ // c.1 < la.sortedParts.length ∧
    c.2 < la.sortedParts.getD c.1 0 } → Fin n // _ }
  exact Subtype.finite

end Etingof
