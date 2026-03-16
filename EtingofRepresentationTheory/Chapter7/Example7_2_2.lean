import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.Types.Basic

/-!
# Example 7.2.2: Examples of Functors

1. A category with one object is a monoid; a functor between such categories is
   a monoid homomorphism.
2. Forgetful functors: Groups → Sets, Rings → AbelianGroups.
3. The opposite category C^op; V ↦ V* is a functor Vect_k → Vect_k^op.
4. Hom functors: Y ↦ Hom(X, Y) and Y ↦ Hom(Y, X).
5. X ↦ Fun(X, ℤ) is a functor Sets → Rings^op.
6. Functors from the path category of a quiver to Vect_k are quiver representations.
7. Induction and restriction functors Ind_K^G, Res_K^G.
8. Direct sum, tensor product, symmetric/exterior power as functors.
9. Reflection functors on quiver representation categories.

## Mathlib correspondence

Several of these functors exist in Mathlib. We demonstrate the forgetful functors
and Hom functors which have direct Mathlib instances.
-/

open CategoryTheory

/-- The forgetful functor from Groups to Types (Sets). (Etingof Example 7.2.2(2)) -/
example : Functor GrpCat (Type*) := forget GrpCat

/-- The forgetful functor from Rings to Types (Sets). (Etingof Example 7.2.2(2)) -/
example : Functor RingCat (Type*) := forget RingCat

/-- For any object X in a category, Y ↦ Hom(X, Y) is a functor to Type.
(Etingof Example 7.2.2(4)) -/
example {C : Type*} [Category C] (X : C) : Functor C (Type*) :=
  coyoneda.obj (Opposite.op X)
