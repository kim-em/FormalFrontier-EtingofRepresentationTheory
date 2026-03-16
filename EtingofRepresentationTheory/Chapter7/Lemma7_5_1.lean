import Mathlib.CategoryTheory.Yoneda

/-!
# Lemma 7.5.1: The Yoneda Lemma

If a functor F is represented by an object X, then X is unique up to a unique
isomorphism. I.e., if X, Y are two objects in C, then for any isomorphism of functors
φ : Hom(X, ?) → Hom(Y, ?) there is a unique isomorphism a_φ : X → Y inducing φ.

## Mathlib correspondence

This is exactly `CategoryTheory.yoneda`. The Yoneda lemma and its consequences
are fully formalized in Mathlib.
-/

open CategoryTheory

/-- The Yoneda lemma: if two representable functors are isomorphic, then
the representing objects are uniquely isomorphic. (Etingof Lemma 7.5.1)

More precisely, the Yoneda embedding is fully faithful, so an isomorphism
Hom(X, ?) ≅ Hom(Y, ?) corresponds to a unique isomorphism X ≅ Y.

This is `CategoryTheory.yoneda.obj` and `CategoryTheory.Yoneda.isIso` in Mathlib. -/
theorem Etingof.yoneda_lemma {C : Type*} [Category C]
    (X Y : C) (φ : yoneda.obj X ≅ yoneda.obj Y) :
    ∃! (a : X ≅ Y), yoneda.map a.hom = φ.hom := by
  sorry
