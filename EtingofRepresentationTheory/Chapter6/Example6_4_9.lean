import Mathlib
import EtingofRepresentationTheory.Chapter6.Theorem_Dynkin_classification
import EtingofRepresentationTheory.Chapter6.Definition6_4_3

/-!
# Example 6.4.9: Root Counts for Dynkin Diagrams

(1) For type Aₙ₋₁, the lattice L = ℤⁿ⁻¹ can be realized as the sublattice
of ℤⁿ consisting of vectors with coordinate sum 0. The simple roots are
αᵢ = eᵢ - eᵢ₊₁. The roots are vectors eᵢ - eⱼ (i ≠ j), giving N(N-1)/2
positive roots. Thus Aₙ has n(n+1)/2 positive roots.

(2) Root counts for other Dynkin diagrams:
- Dₙ: n(n-1) positive roots
- E₆: 36 positive roots
- E₇: 63 positive roots
- E₈: 120 positive roots

## Mathlib correspondence

Root system structure exists in Mathlib via `RootPairing` but the specific
root counts for each Dynkin type are not stated. We use the project's
`IsRoot` definition (Definition 6.4.3) and the `DynkinType` adjacency matrices
from the classification theorem.
-/

/-- The set of positive roots of a graph given by its adjacency matrix.
A positive root is a root (nonzero vector x with B(x,x) = 2) whose coordinates
are all nonneg ative. By Lemma 6.4.6, every root is either positive or negative. -/
def Etingof.positiveRoots (n : ℕ) (adj : Matrix (Fin n) (Fin n) ℤ) : Set (Fin n → ℤ) :=
  {x | Etingof.IsRoot n adj x ∧ ∀ i, 0 ≤ x i}

/-- The number of positive roots for Aₙ is n(n+1)/2.
(Etingof Example 6.4.9(1)) -/
theorem Etingof.Example_6_4_9_An (n : ℕ) (hn : 1 ≤ n) :
    (Etingof.positiveRoots n (Etingof.DynkinType.A n hn).adj).Finite ∧
    Set.ncard (Etingof.positiveRoots n (Etingof.DynkinType.A n hn).adj) =
      n * (n + 1) / 2 := sorry

/-- The number of positive roots for Dₙ is n(n-1).
(Etingof Example 6.4.9(2)) -/
theorem Etingof.Example_6_4_9_Dn (n : ℕ) (hn : 4 ≤ n) :
    (Etingof.positiveRoots n (Etingof.DynkinType.D n hn).adj).Finite ∧
    Set.ncard (Etingof.positiveRoots n (Etingof.DynkinType.D n hn).adj) =
      n * (n - 1) := sorry

/-- E₆ has 36 positive roots.
(Etingof Example 6.4.9(2)) -/
theorem Etingof.Example_6_4_9_E6 :
    (Etingof.positiveRoots 6 Etingof.DynkinType.E6.adj).Finite ∧
    Set.ncard (Etingof.positiveRoots 6 Etingof.DynkinType.E6.adj) = 36 := sorry

/-- E₇ has 63 positive roots.
(Etingof Example 6.4.9(2)) -/
theorem Etingof.Example_6_4_9_E7 :
    (Etingof.positiveRoots 7 Etingof.DynkinType.E7.adj).Finite ∧
    Set.ncard (Etingof.positiveRoots 7 Etingof.DynkinType.E7.adj) = 63 := sorry

/-- E₈ has 120 positive roots.
(Etingof Example 6.4.9(2)) -/
theorem Etingof.Example_6_4_9_E8 :
    (Etingof.positiveRoots 8 Etingof.DynkinType.E8.adj).Finite ∧
    Set.ncard (Etingof.positiveRoots 8 Etingof.DynkinType.E8.adj) = 120 := sorry
