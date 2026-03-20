import EtingofRepresentationTheory.Chapter9.Definition9_7_1
import EtingofRepresentationTheory.Infrastructure.CornerRing
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.Simple
import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.CategoryTheory.Equivalence
import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Morita structural theorem

This file provides:

1. **Simple module preservation**: An equivalence of module categories
   sends simple modules to simple modules.

2. **Morita structural theorem** (statement): If `MoritaEquivalent A B`,
   then `B ≅ eAe` for some full idempotent `e ∈ A`.

## Main results

* `Etingof.equivalence_preserves_simple`: An equivalence of categories
  with zero morphisms sends simple objects to simple objects.

* `Etingof.moritaEquivalent_preserves_simple`: Specialization to module
  categories.

* `Etingof.MoritaStructural`: If `MoritaEquivalent A B` then there
  exists an idempotent `e : A` with `B ≃ₐ[k] CornerRing e`.

## References

* Etingof, §9.7 on Morita equivalence
* The categorical Morita equivalence is Theorem 9.6.4 in this project
-/

universe u v

open CategoryTheory CategoryTheory.Limits

namespace Etingof

/-! ## Simple module preservation under equivalence -/

/-- An equivalence of categories preserves simple objects: if `X` is
simple in `C` and `F : C ≌ D`, then `F.functor.obj X` is simple.

Proof: Any mono `g : Y ⟶ F.obj X` in `D` transports via `F⁻¹` to a
mono into `X` in `C`. Since `X` is simple, it's iso iff nonzero, and
the equivalence preserves both properties. -/
theorem equivalence_preserves_simple
    {C : Type*} [Category C] [Preadditive C]
    {D : Type*} [Category D] [Preadditive D]
    (F : C ≌ D) (X : C) [Simple X] :
    Simple (F.functor.obj X) := by
  constructor
  intro Y g hg
  -- Build a mono into X from g via the inverse equivalence
  let g' : F.inverse.obj Y ⟶ X :=
    F.inverse.map g ≫ (F.unitIso.app X).inv
  have hg' : Mono g' := mono_comp _ _
  -- Key connections between g and g'
  have g_zero_iff : g = 0 ↔ g' = 0 := by
    constructor
    · intro h; simp [g', h, Functor.map_zero]
    · intro h
      -- g' = F⁻¹.map g ≫ unitIso.inv X = 0
      -- ⟹ F⁻¹.map g = 0 (comp with iso on right)
      have h1 : F.inverse.map g = 0 := by
        have : g' = 0 := h
        rw [show g' = F.inverse.map g ≫ (F.unitIso.app X).inv
          from rfl] at this
        rwa [Preadditive.IsIso.comp_right_eq_zero] at this
      -- F⁻¹ faithful: F⁻¹.map g = 0 ⟹ g = 0
      have : F.inverse.map g = F.inverse.map (0 : Y ⟶ _) := by
        rw [h1, Functor.map_zero]
      exact F.inverse.map_injective this
  have g_iso_iff : IsIso g ↔ IsIso g' := by
    constructor
    · intro _; exact IsIso.comp_isIso
    · intro _
      have : IsIso (F.inverse.map g) :=
        IsIso.of_isIso_comp_right _ (F.unitIso.app X).inv
      exact isIso_of_reflects_iso g F.inverse
  -- Use simplicity of X on g'
  have key := Simple.mono_isIso_iff_nonzero g'
  constructor
  · -- IsIso g → g ≠ 0
    intro hiso hg0
    have hg'0 : g' = 0 := g_zero_iff.mp hg0
    have hg'iso : IsIso g' := g_iso_iff.mp hiso
    exact (Simple.mono_isIso_iff_nonzero g').mp hg'iso hg'0
  · -- g ≠ 0 → IsIso g
    intro hne
    have hg'ne : g' ≠ 0 := fun h => hne (g_zero_iff.mpr h)
    exact g_iso_iff.mpr (key.mpr hg'ne)

/-- Morita equivalence preserves simple modules: if
`ModuleCat A ≌ ModuleCat B` and `M` is simple, then its image under
the equivalence is simple. -/
theorem moritaEquivalent_preserves_simple
    (A : Type u) [Ring A] (B : Type v) [Ring B]
    (F : ModuleCat.{max u v} A ≌ ModuleCat.{max u v} B)
    (M : ModuleCat.{max u v} A) [Simple M] :
    Simple (F.functor.obj M) :=
  equivalence_preserves_simple F M

/-! ## Morita structural theorem -/

/-- **Morita structural theorem**: If finite-dimensional `k`-algebras
`A` and `B` are Morita equivalent, then there exists an idempotent
`e ∈ A` such that `B ≅ eAe` as `k`-algebras.

The proof strategy:
1. From `ModuleCat A ≌ ModuleCat B`, the equivalence sends the free
   module `A` to a finitely generated projective `B`-module `P`.
2. `P` is a progenerator for `ModuleCat B`, so `B ≅ End_B(P)^op`.
3. As a f.g. projective `A`-module, `P ≅ Ae` for some idempotent `e`.
4. `End_A(Ae)^op ≅ eAe`, giving the result. -/
theorem MoritaStructural
    (k : Type u) [Field k]
    (A : Type u) [Ring A] [Algebra k A] [Module.Finite k A]
    (B : Type u) [Ring B] [Algebra k B] [Module.Finite k B]
    (hMor : MoritaEquivalent A B) :
    ∃ (e : A) (he : IsIdempotentElem e),
      Nonempty
        (@AlgEquiv k (CornerRing (k := k) e) B _
          (CornerRing.instRing he).toSemiring _
          (CornerRing.instAlgebra he) _) := by
  -- The full proof requires substantial infrastructure not yet
  -- formalized:
  -- (1) Equivalence F : ModuleCat A ≌ ModuleCat B sends the free
  --     A-module to a progenerator P in ModuleCat B
  -- (2) F.g. projective modules over fin-dim algebras correspond
  --     to direct summands of A^n, i.e. to idempotents in Mₙ(A)
  -- (3) End_A(Ae)^op ≅ eAe as k-algebras
  -- (4) Assembly: B ≅ End_B(B)^op ≅ End_B(F(A))^op
  --     ≅ End_A(A)^op via equivalence ≅ eAe
  sorry

end Etingof
