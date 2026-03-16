import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic

/-!
# Example 7.6.3: Examples of Adjoint Functors

1. For a finite dimensional representation V of a group G or Lie algebra g,
   V ⊗ - and V* ⊗ - are adjoint functors on the category of representations.
2. Res_K^G is left adjoint to Ind_K^G (Frobenius reciprocity).
3. The Lie algebra functor L : Assoc_k → Lie_k has a left adjoint: the universal
   enveloping algebra functor U.
4. GL₁ : Assoc_k → Groups (A ↦ A×) has left adjoint G ↦ k[G].
5. The tensor algebra functor V ↦ TV is left adjoint to the forgetful functor
   Assoc_k → Vect_k. Similarly, symmetric algebra for commutative algebras.

## Mathlib correspondence

Frobenius reciprocity and the UEA adjunction are partially available in Mathlib.
-/

open CategoryTheory

/-- Frobenius reciprocity: Res_K^G is left adjoint to Ind_K^G.
(Etingof Example 7.6.3(2))

This is a fundamental adjunction in representation theory of finite groups. -/
theorem Etingof.frobenius_reciprocity : (sorry : Prop) := by sorry

/-- The universal enveloping algebra functor U is left adjoint to the Lie algebra
functor L. (Etingof Example 7.6.3(3)) -/
theorem Etingof.uea_adjunction : (sorry : Prop) := by sorry
