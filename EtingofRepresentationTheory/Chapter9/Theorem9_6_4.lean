import EtingofRepresentationTheory.Chapter9.Definition9_6_1
import EtingofRepresentationTheory.Chapter9.Definition9_6_2
import EtingofRepresentationTheory.Chapter9.Definition9_7_1
import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import Mathlib.CategoryTheory.Equivalence

universe u v

/-!
# Theorem 9.6.4: Morita equivalence theorem

Let 𝒞 be a finite abelian category over a field k. Let P = ⊕ Pᵢ be a projective
generator, and let B = End(P)ᵒᵖ. Define functor F : 𝒞 → B-fmod by F(X) = Hom(P, X).

Then F is an equivalence of categories.

Corollary: Any finite abelian category over a field k is equivalent to the category
of finite dimensional modules over some finite dimensional k-algebra.

## Mathlib correspondence

The functor F = Hom(P, −) sending X to the `(End P)ᵐᵒᵖ`-module `Hom(P, X)` is
`CategoryTheory.preadditiveCoyonedaObj P` in Mathlib. The theorem asserts that this
functor is an equivalence of categories when P is a projective generator in a
finite abelian category. We state this as `Functor.IsEquivalence`.
-/

open CategoryTheory

/-- **Theorem 9.6.4 (Morita equivalence)**: Let 𝒞 be a finite abelian category
and P a projective generator. Then the functor F(X) = Hom(P, X) gives an
equivalence 𝒞 ≌ (End P)ᵒᵖ-Mod.

In Mathlib, this functor is `preadditiveCoyonedaObj P : C ⥤ ModuleCat (End P)ᵐᵒᵖ`.
(Etingof Theorem 9.6.4) -/
theorem Etingof.Theorem_9_6_4
    (C : Type u) [Category.{v} C] [Preadditive C]
    [Etingof.IsFiniteAbelianCategory C]
    (P : C) [Etingof.IsProgenerator P] :
    (preadditiveCoyonedaObj P).IsEquivalence := by
  sorry

/-- **Corollary of Theorem 9.6.4**: Any finite abelian category is equivalent to
modules over some ring. Specifically, if P is a projective generator (which exists
by the enough-projectives and finiteness conditions), then C ≌ (End P)ᵒᵖ-Mod.
(Etingof Theorem 9.6.4, corollary) -/
theorem Etingof.Theorem_9_6_4_corollary
    (C : Type u) [Category.{v} C] [Preadditive C]
    [Etingof.IsFiniteAbelianCategory C]
    (P : C) [Etingof.IsProgenerator P] :
    Nonempty (C ≌ ModuleCat.{v} (End P)ᵐᵒᵖ) := by
  have := Etingof.Theorem_9_6_4 C P
  exact ⟨(preadditiveCoyonedaObj P).asEquivalence⟩
