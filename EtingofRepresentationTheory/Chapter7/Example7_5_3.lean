import Mathlib.CategoryTheory.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
# Example 7.5.3: Representable Forgetful Functor

Let A be an algebra. Then the forgetful functor from the category of left A-modules
to the category of vector spaces is representable, and the representing object is
the free rank 1 module (= the regular representation) M = A.

But if A is infinite dimensional and we restrict to finite dimensional modules,
the forgetful functor is in general not representable.

## Mathlib correspondence

The forgetful functor `ModuleCat A → Type*` being representable by A (the regular
representation) is a standard fact. Mathlib has `ModuleCat.representable` infrastructure.
-/

open CategoryTheory

/-- The forgetful functor from A-mod to Type is representable by the free module A.
(Etingof Example 7.5.3)

The representing object is A itself (the regular representation). -/
theorem Etingof.forgetful_representable : (sorry : Prop) := by sorry
