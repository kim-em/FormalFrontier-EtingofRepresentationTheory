import Mathlib.CategoryTheory.NatTrans

/-!
# Definition 7.3.1: Natural Transformation

A morphism (natural transformation) a : F → G between functors F, G : C → D is a
collection of morphisms a_X : F(X) → G(X) labeled by objects X of C, which is
functorial in X; i.e., for any morphism f : X → Y, we have a_Y ∘ F(f) = G(f) ∘ a_X.

A morphism a : F → G is an isomorphism if there exists a⁻¹ : G → F such that
a ∘ a⁻¹ and a⁻¹ ∘ a are identities.

## Mathlib correspondence

This is exactly `CategoryTheory.NatTrans`. Natural isomorphisms are `CategoryTheory.NatIso`.
-/

/-- A natural transformation between functors, in the sense of Etingof Definition 7.3.1.
This is `CategoryTheory.NatTrans` in Mathlib. -/
abbrev Etingof.NatTrans {C : Type*} {D : Type*} [CategoryTheory.Category C]
    [CategoryTheory.Category D] (F G : CategoryTheory.Functor C D) :=
  CategoryTheory.NatTrans F G
