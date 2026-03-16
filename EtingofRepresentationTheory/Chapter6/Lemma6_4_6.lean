import EtingofRepresentationTheory.Chapter6.Definition6_4_3

/-!
# Lemma 6.4.6: Roots are Positive or Negative

Let α be a root, α = Σᵢ kᵢ αᵢ. Then either kᵢ ≥ 0 for all i or kᵢ ≤ 0 for all i.

**Proof sketch:** Assume for contradiction that kᵢ > 0 and kⱼ < 0. Split the root
into two parts β (supported on the component containing i) and γ (containing j)
obtained by removing an edge between positive and negative regions. Then
B(β,β) ≥ 2, B(γ,γ) ≥ 2, and B(β,γ) ≥ 0, giving B(α,α) ≥ 4, contradicting
α being a root.

## Mathlib correspondence

This is a specific combinatorial/algebraic lemma about Dynkin diagrams not in Mathlib.
The proof uses positive definiteness and the tree structure of Dynkin diagrams.
-/

/-- Every root of a Dynkin diagram has all nonnegative or all nonpositive coordinates
with respect to the simple root basis. (Etingof Lemma 6.4.6) -/
theorem Etingof.Lemma_6_4_6 (n : ℕ) (adj : Matrix (Fin n) (Fin n) ℤ)
    (x : Fin n → ℤ)
    (hroot : Etingof.IsRoot n adj x) :
    (∀ i, 0 ≤ x i) ∨ (∀ i, x i ≤ 0) := by
  sorry
