import Mathlib.RepresentationTheory.Induced
import Mathlib.Algebra.Lie.UniversalEnveloping

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

Frobenius reciprocity is `Rep.indResAdjunction` in Mathlib. The UEA universal
property is captured by `UniversalEnvelopingAlgebra.lift`.
-/

open CategoryTheory

/-- Frobenius reciprocity: induction is left adjoint to restriction for
representations of finite groups. (Etingof Example 7.6.3(2))

Given a group homomorphism φ : G →* H over a commutative ring k,
the induction functor `Rep.indFunctor k φ` is left adjoint to the
restriction functor `Action.res _ φ`. -/
noncomputable def Etingof.frobenius_reciprocity
    (k : Type u) {G H : Type u} [CommRing k] [Group G] [Group H] (φ : G →* H) :
    Rep.indFunctor k φ ⊣ Action.res _ φ :=
  Rep.indResAdjunction k φ

/-- The universal enveloping algebra functor is left adjoint to the "underlying
Lie algebra" functor, in the sense that Lie algebra homomorphisms L → A correspond
bijectively to algebra homomorphisms U(L) → A. (Etingof Example 7.6.3(3))

This captures the adjunction at the level of hom-sets via an equivalence. -/
def Etingof.uea_adjunction
    (R : Type*) [CommRing R] (L : Type*) [LieRing L] [LieAlgebra R L]
    (A : Type*) [Ring A] [Algebra R A] :
    (L →ₗ⁅R⁆ A) ≃ (UniversalEnvelopingAlgebra R L →ₐ[R] A) :=
  UniversalEnvelopingAlgebra.lift R
