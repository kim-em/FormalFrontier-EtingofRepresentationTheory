import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Example 7.8.3: Split Exact Sequences

The sequence 0 → X → X ⊕ Z → Z → 0 with the obvious morphisms is a short exact
sequence. Such a sequence is called **split**. It corresponds to the trivial
extension of Z by X.

## Mathlib correspondence

Split exact sequences are available in Mathlib. `CategoryTheory.ShortComplex.Splitting`
captures the notion of a splitting of a short complex.
-/

open CategoryTheory

/-- A split short exact sequence: 0 → X → X ⊕ Z → Z → 0.
(Etingof Example 7.8.3)

In Mathlib, a split short exact sequence is witnessed by a `ShortComplex.Splitting`. -/
theorem Etingof.split_exact_sequence : (sorry : Prop) := by sorry
