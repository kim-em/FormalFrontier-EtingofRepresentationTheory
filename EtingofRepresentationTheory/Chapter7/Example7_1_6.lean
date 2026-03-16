import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
# Example 7.1.6: Rep(A) is Enriched over k-vector spaces

The category Rep(A) of representations of a k-algebra A is enriched over the
category of k-vector spaces. That is, the Hom spaces carry a k-module structure.

## Mathlib correspondence

`ModuleCat k` is a `k`-linear category via `CategoryTheory.Linear`.
-/

open CategoryTheory

/-- The category of modules over a k-algebra is k-linear (enriched over k-Vect).
(Etingof Example 7.1.6) -/
example (k : Type*) [Field k] : Linear k (ModuleCat k) := inferInstance
