import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# Example 7.7.2: Module Categories are Abelian

The category of modules over an algebra A and the category of finite dimensional
modules over A are abelian categories.

## Mathlib correspondence

Exact match. `ModuleCat A` is an abelian category in Mathlib via
`ModuleCat.instAbelian`.
-/

open CategoryTheory

/-- The category of modules over a ring A is an abelian category.
(Etingof Example 7.7.2) -/
example (A : Type*) [Ring A] : Abelian (ModuleCat A) := inferInstance
