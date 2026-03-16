import Mathlib.CategoryTheory.NatTrans
import Mathlib.CategoryTheory.Functor.Basic

/-!
# Example 7.3.2: Examples of Natural Transformations

1. On the category of finite dimensional vector spaces FVect_k, the functors id and **
   are isomorphic via the standard maps a_V : V → V**. But on Vect_k they are not
   isomorphic (infinite dimensional V is not isomorphic to V**).
2. On FVect_k' (morphisms = isomorphisms), V ↦ V* is a functor where V ≅ F(V) for
   all V, but it is not isomorphic to the identity functor.
3. If F : A-mod → Vect_k is the forgetful functor, then End(F) = A.
4. The endomorphisms of the identity functor on A-mod is the center of A.

## Mathlib correspondence

These examples involve specific categorical constructions. The double dual natural
transformation and functor endomorphism results require more infrastructure to
state formally. We provide sorry'd placeholders.
-/

open CategoryTheory

/-- The double dual natural transformation on finite-dimensional vector spaces is
a natural isomorphism from the identity functor to the double dual functor.
(Etingof Example 7.3.2(1))

This requires the canonical map V → V** to be packaged as a natural transformation,
which needs infrastructure for the dual functor on finite-dimensional spaces. -/
theorem Etingof.double_dual_nat_iso : (sorry : Prop) := by sorry
