import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# Example 7.9.6: Exactness Properties of Standard Functors

(i) The functors Ind_K^G, Res_K^G are exact.
(ii) The functor Hom(X, ?) is left exact, but not necessarily right exact.
     Counterexample: 0 → ℤ → ℤ → ℤ/2ℤ → 0 with Hom(ℤ/2ℤ, ?).
(iii) The functor X ⊗_A - for a right A-module X is right exact but not
      necessarily left exact. Counterexample: tensor the above sequence by ℤ/2ℤ.

## Mathlib correspondence

Left exactness of Hom is available in Mathlib. The counterexamples for failure
of right/left exactness are standard.
-/

open CategoryTheory

/-- The Hom functor is left exact but not necessarily right exact.
(Etingof Example 7.9.6(ii)) -/
theorem Etingof.hom_left_exact : (sorry : Prop) := by sorry

/-- The tensor product functor is right exact but not necessarily left exact.
(Etingof Example 7.9.6(iii)) -/
theorem Etingof.tensor_right_exact : (sorry : Prop) := by sorry
