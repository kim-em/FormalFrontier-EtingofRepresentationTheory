import EtingofRepresentationTheory.Chapter6.Definition6_4_3

/-!
# Definition 6.4.7: Positive and Negative Roots

A root α = Σᵢ kᵢ αᵢ is called a **positive root** if all kᵢ ≥ 0.
A root for which kᵢ ≤ 0 for all i is called a **negative root**.

By Lemma 6.4.6, every root is either positive or negative.

## Mathlib correspondence

Mathlib has positive root concepts via `RootPairing`. The book's definition is
more elementary, defined in terms of coordinates in the simple root basis.
-/

/-- A root is positive if all its coordinates are nonnegative.
(Etingof Definition 6.4.7) -/
def Etingof.IsPositiveRoot (n : ℕ) (adj : Matrix (Fin n) (Fin n) ℤ)
    (x : Fin n → ℤ) : Prop :=
  Etingof.IsRoot n adj x ∧ ∀ i, 0 ≤ x i

/-- A root is negative if all its coordinates are nonpositive.
(Etingof Definition 6.4.7) -/
def Etingof.IsNegativeRoot (n : ℕ) (adj : Matrix (Fin n) (Fin n) ℤ)
    (x : Fin n → ℤ) : Prop :=
  Etingof.IsRoot n adj x ∧ ∀ i, x i ≤ 0
