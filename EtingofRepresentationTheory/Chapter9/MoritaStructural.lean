import EtingofRepresentationTheory.Chapter9.Definition9_7_1
import EtingofRepresentationTheory.Infrastructure.CornerRing
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Simple

universe u v

/-!
# Morita structural theorem

The **Morita structural theorem** asserts that if two algebras `A` and `B` are
Morita equivalent (i.e., `ModuleCat A ≌ ModuleCat B`), then `B` is isomorphic
to a corner ring `eAe` for some idempotent `e ∈ A`.

This file also states that categorical equivalences preserve simple objects,
which is needed for the uniqueness of basic algebras (Corollary 9.7.3).

## Main results

* `Etingof.simple_of_equivalence`: An equivalence of categories preserves
  simple objects.
* `Etingof.MoritaStructural`: If `MoritaEquivalent A B`, then `B ≅ eAe`
  for some idempotent `e : A`.

## Implementation notes

The full proofs require substantial infrastructure connecting categorical Morita
equivalence (Theorem 9.6.4) with the concrete algebra-level isomorphism `B ≅ eAe`.
The key steps are:
1. An equivalence `F : ModuleCat A ≌ ModuleCat B` sends the free module `A` to a
   progenerator `P` of `ModuleCat B`.
2. `B ≅ End_B(P)ᵒᵖ` (Morita I).
3. `End_B(P)ᵒᵖ ≅ eAe` where `e` is the idempotent corresponding to the
   projection onto the image of `A` under `F`.

These steps are sorry'd pending formalization of the progenerator-to-algebra
correspondence.
-/

open CategoryTheory CategoryTheory.Limits

namespace Etingof

/-! ## Simple module preservation under equivalence -/

/-- An equivalence of categories preserves simple objects: if `F : C ≌ D` is
an equivalence and `X : C` is simple, then `F.functor.obj X` is simple.

Proof: `Simple` is characterized by `IsSimpleOrder (Subobject X)`. The
equivalence induces an order isomorphism on subobjects (via `MonoOver.mapIso`
composed with the essential surjectivity), preserving the simple order property.
Alternatively, use that the equivalence is fully faithful: it preserves and
reflects monomorphisms and zero morphisms, so the condition
`IsIso f ↔ f ≠ 0` for monos transfers. -/
theorem simple_of_equivalence {C : Type u} [Category.{v} C]
    {D : Type u} [Category.{v} D]
    [HasZeroMorphisms C] [HasZeroMorphisms D]
    (F : C ≌ D) (X : C) [Simple X] :
    Simple (F.functor.obj X) := by
  constructor
  intro Y g hMono
  -- Build a mono into X by applying F.inverse and composing with the unit
  let g' : F.inverse.obj Y ⟶ X := F.inverse.map g ≫ (F.unitIso.app X).inv
  -- g' is mono: F.inverse.map g is mono (right adjoint preserves mono),
  -- and (F.unitIso.app X).inv is iso hence mono
  haveI : Mono (F.inverse.map g) := by
    haveI : F.inverse.PreservesMonomorphisms :=
      CategoryTheory.Functor.preservesMonomorphisms_of_adjunction F.toAdjunction
    exact F.inverse.map_mono g
  haveI : Mono g' := mono_comp (F.inverse.map g) (F.unitIso.app X).inv
  -- By simplicity of X: IsIso g' ↔ g' ≠ 0
  have hSimp := Simple.mono_isIso_iff_nonzero g'
  constructor
  · -- IsIso g → g ≠ 0
    intro hIso h0
    -- g' = F.inverse.map 0 ≫ _ = 0 ≫ _ = 0
    have hg'_zero : g' = 0 := by
      simp only [g', h0, Functor.map_zero, zero_comp]
    -- g' = 0 implies ¬ IsIso g'
    have := hSimp.mp
    -- But g' is also iso (F.inverse preserves iso, and unit is iso)
    haveI : IsIso (F.inverse.map g) := by
      haveI := hIso
      exact Functor.map_isIso F.inverse g
    haveI : IsIso g' := IsIso.comp_isIso
    exact absurd hg'_zero (hSimp.mp ‹IsIso g'›)
  · -- g ≠ 0 → IsIso g
    intro hne
    -- g' ≠ 0 (because F.inverse is faithful, g ≠ 0 implies F.inverse.map g ≠ 0)
    have hg'_ne : g' ≠ 0 := by
      intro h0
      apply hne
      -- g' = F.inverse.map g ≫ unit.inv = 0
      -- So F.inverse.map g = 0 (compose with unit.hom on right)
      have h_inv_zero := congr_arg (· ≫ (F.unitIso.app X).hom) h0
      simp [g', Category.assoc] at h_inv_zero
      -- F.inverse.map g = 0 implies g = 0 by faithfulness
      exact F.inverse.map_injective (by rw [h_inv_zero, Functor.map_zero])
    -- By simplicity, g' is iso
    haveI : IsIso g' := hSimp.mpr hg'_ne
    -- F.inverse.map g = g' ≫ unit.hom, which is iso
    have : F.inverse.map g = g' ≫ (F.unitIso.app X).hom := by
      simp [g', Category.assoc]
    haveI : IsIso (F.inverse.map g) := by rw [this]; exact IsIso.comp_isIso
    -- F reflects isos (it's an equivalence), so g is iso
    exact isIso_of_reflects_iso g F.inverse

/-! ## Morita structural theorem -/

variable {k : Type u} [Field k]

/-- **Morita structural theorem**: If `A` and `B` are Morita equivalent algebras
over a field `k`, then there exists an idempotent `e : A` such that `B` is
isomorphic (as a `k`-algebra) to the corner ring `eAe`.

This is the concrete algebraic content of Morita's theorem beyond the categorical
equivalence proved in Theorem 9.6.4.
(Etingof, discussion after Definition 9.7.1) -/
theorem MoritaStructural
    (A : Type u) [Ring A] [Algebra k A]
    (B : Type u) [Ring B] [Algebra k B]
    (h : MoritaEquivalent A B) :
    ∃ (e : A) (he : IsIdempotentElem e),
      Nonempty (@AlgEquiv k B (CornerRing (k := k) e) _ _
        (CornerRing.instRing he).toSemiring
        _ (@CornerRing.instAlgebra k _ A _ _ e he)) := by
  sorry

/-- **Dimension bound from Morita equivalence**: If `A` and `B` are Morita
equivalent, then `dim B ≤ dim A` (when `B` is the basic algebra).
This follows from `B ≅ eAe` and `dim(eAe) ≤ dim(A)`. -/
theorem MoritaEquivalent.finrank_cornerRing_le
    (A : Type u) [Ring A] [Algebra k A] [Module.Finite k A]
    (e : A) :
    Module.finrank k (cornerSubmodule (k := k) e) ≤ Module.finrank k A :=
  finrank_cornerSubmodule_le e

end Etingof
