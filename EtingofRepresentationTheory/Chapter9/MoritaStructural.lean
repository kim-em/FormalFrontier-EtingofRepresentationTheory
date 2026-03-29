import EtingofRepresentationTheory.Chapter9.Definition9_7_1
import EtingofRepresentationTheory.Chapter9.Definition9_7_2
import EtingofRepresentationTheory.Infrastructure.CornerRing
import EtingofRepresentationTheory.Infrastructure.BasicAlgebraExistence
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Simple
import Mathlib.FieldTheory.IsAlgClosed.Basic

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

/-! ## Morita equivalence symmetry and transitivity -/

/-- Morita equivalence is symmetric. -/
lemma MoritaEquivalent.symm' {A : Type u} [Ring A] {B : Type u} [Ring B]
    (h : MoritaEquivalent A B) : MoritaEquivalent B A :=
  h.map CategoryTheory.Equivalence.symm

/-- Morita equivalence is transitive. -/
lemma MoritaEquivalent.trans' {A : Type u} [Ring A] {B : Type u} [Ring B]
    {C : Type u} [Ring C]
    (h₁ : MoritaEquivalent A B) (h₂ : MoritaEquivalent B C) :
    MoritaEquivalent A C := by
  obtain ⟨e₁⟩ := h₁; obtain ⟨e₂⟩ := h₂; exact ⟨e₁.trans e₂⟩

/-! ## Idempotent lemmas -/

/-- An idempotent element that differs from 1 by a nilpotent element must equal 1.

If `e² = e` and `1 - e` is nilpotent, then `e = 1`. This is a key step in
showing that full idempotents in basic algebras equal the identity. -/
theorem IsIdempotentElem.eq_one_of_isNilpotent_one_sub
    {R : Type*} [Ring R] {e : R}
    (he : IsIdempotentElem e) (hnil : IsNilpotent (1 - e)) : e = 1 := by
  -- If 1 - e is nilpotent, then e = 1 - (1 - e) is a unit
  have h_unit : IsUnit e := by
    have h := hnil.isUnit_one_sub
    rwa [sub_sub_cancel] at h
  -- An idempotent unit must be 1: e² = e implies e(e - 1) = 0,
  -- and since e is a unit, e - 1 = 0.
  obtain ⟨u, rfl⟩ := h_unit
  have h_mul : (↑u : R) * (↑u - 1) = 0 := by
    rw [mul_sub, mul_one, he.eq, sub_self]
  -- Left-multiply by u⁻¹: u⁻¹ * (u * (u - 1)) = u⁻¹ * 0 = 0
  -- Simplifies to: (u⁻¹ * u) * (u - 1) = 0, i.e., 1 * (u - 1) = 0
  have key : (↑u : R) - 1 = 0 := by
    have h1 : (↑u⁻¹ : R) * ↑u = 1 := u.inv_mul
    calc (↑u : R) - 1
        = 1 * (↑u - 1) := (one_mul _).symm
      _ = ↑u⁻¹ * ↑u * (↑u - 1) := by rw [h1]
      _ = ↑u⁻¹ * (↑u * (↑u - 1)) := by rw [mul_assoc]
      _ = ↑u⁻¹ * 0 := by rw [h_mul]
      _ = 0 := mul_zero _
  exact sub_eq_zero.mp key

/-! ## Morita structural theorem -/

variable {k : Type u} [Field k]

/-- Two basic algebras that are Morita equivalent are isomorphic as `k`-algebras.

This is the uniqueness component of the Morita structural theorem.

### Proof strategy (endomorphism ring approach)

Given an equivalence `F : ModuleCat B₁ ≌ ModuleCat B₂`:

1. **End preserving**: `F` induces `End_{B₁}(B₁) ≃* End_{B₂}(F(B₁))` (fully faithful).
2. **Regular module preserved**: For basic algebras, `F(B₁) ≅ B₂` as `B₂`-modules.
   This is because both regular modules decompose (Krull-Schmidt) into one copy of
   each indecomposable projective, and `F` bijects indecomposable projectives.
3. **Endomorphism = opposite**: `End_B(B) ≅ Bᵒᵖ` (right multiplication).
4. **Assembly**: `B₁ᵒᵖ ≅ End_{B₁}(B₁) ≅ End_{B₂}(F(B₁)) ≅ End_{B₂}(B₂) ≅ B₂ᵒᵖ`,
   hence `B₁ ≅ B₂`.

### Blocked by

Step 2 requires showing `F(B₁) ≅ B₂` as `B₂`-modules. A proof without
Krull-Schmidt proceeds as follows:

1. `F(B₁)` is a projective generator of `ModuleCat B₂` (categorical argument).
2. `F(B₁)/J·F(B₁) ≅ B₂/J·B₂` as `B₂/J`-modules, where `J = Ring.jacobson B₂`.
   This uses: for basic `B`, the head of `B` is `⊕ᵢ Sᵢ` (one copy of each simple).
   `F` bijects simples (`simple_of_equivalence`), so the head of `F(B₁)` has the
   same simple constituents with the same multiplicities.
3. By projective lifting (`Module.projective_lifting_property`), construct maps
   `f̃ : B₂ →ₗ F(B₁)` and `g̃ : F(B₁) →ₗ B₂` that are isomorphisms modulo `J`.
4. Nakayama's lemma (`Submodule.FG.eq_bot_of_le_jacobson_smul`) shows `g̃ ∘ f̃` and
   `f̃ ∘ g̃` are surjective, hence isomorphisms (finite-dimensional).

The main missing infrastructure is the primitive idempotent decomposition of
basic algebras and the characterization of the semisimple head `B/JB`.
See also `exists_full_idempotent_basic_corner` in BasicAlgebraExistence.lean
which constructs this decomposition for the Artin-Wedderburn quotient. -/
private lemma basic_morita_algEquiv [IsAlgClosed k]
    (B₁ : Type u) [Ring B₁] [Algebra k B₁] [Module.Finite k B₁]
    (B₂ : Type u) [Ring B₂] [Algebra k B₂] [Module.Finite k B₂]
    (_hB₁ : IsBasicAlgebra k B₁) (_hB₂ : IsBasicAlgebra k B₂)
    (h : MoritaEquivalent B₁ B₂) :
    Nonempty (B₁ ≃ₐ[k] B₂) := by
  sorry

/-- **Morita structural theorem**: If `A` is a finite-dimensional `k`-algebra
over an algebraically closed field and `B` is a basic finite-dimensional
`k`-algebra that is Morita equivalent to `A`, then there exists an idempotent
`e : A` such that `B` is isomorphic (as a `k`-algebra) to the corner ring `eAe`.

The `IsBasicAlgebra k B` hypothesis is essential: without it the statement is
false. For example, `k` and `Mₙ(k)` are Morita equivalent, but `Mₙ(k)` cannot
be realized as `eke` for any `e ∈ k`. The basic algebra is always the smallest
representative in a Morita equivalence class, so it embeds as a corner ring of
any other representative.

The `IsAlgClosed k` hypothesis is needed to ensure existence of a basic corner
ring via Wedderburn–Artin decomposition. Over non-algebraically-closed fields,
division algebras can have dimension > 1, and the basic algebra construction
requires each simple quotient to be isomorphic to `k`.

This is the concrete algebraic content of Morita's theorem beyond the categorical
equivalence proved in Theorem 9.6.4.
(Etingof, discussion after Definition 9.7.1)

## Proof

1. `exists_full_idempotent_basic_corner`: Wedderburn–Artin + idempotent lifting
   gives a full idempotent `e ∈ A` with `eAe` basic.
2. `morita_equiv_of_full_idempotent`: The corner functor `M ↦ eM` gives
   `MoritaEquivalent A (CornerRing e)`.
3. `basic_morita_algEquiv`: `B` and `CornerRing e` are both basic and Morita
   equivalent (by transitivity), hence `B ≃ₐ[k] CornerRing e`. -/
theorem MoritaStructural [IsAlgClosed k]
    (A : Type u) [Ring A] [Algebra k A] [Module.Finite k A]
    (B : Type u) [Ring B] [Algebra k B] [Module.Finite k B]
    (_hB : IsBasicAlgebra k B)
    (h : MoritaEquivalent A B) :
    ∃ (e : A) (he : IsIdempotentElem e),
      Nonempty (@AlgEquiv k B (CornerRing (k := k) e) _ _
        (CornerRing.instRing he).toSemiring
        _ (@CornerRing.instAlgebra k _ A _ _ e he)) := by
  -- Step 1: Get a full idempotent e whose corner ring eAe is basic
  obtain ⟨e, he_full, hbasic_corner⟩ := exists_full_idempotent_basic_corner k A
  refine ⟨e, he_full.1, ?_⟩
  -- Step 2: Corner ring eAe is Morita equivalent to A
  have hMoritaCorner := morita_equiv_of_full_idempotent (k := k) he_full
  -- Step 3: B and CornerRing e are both basic and Morita equivalent
  letI : Ring (CornerRing (k := k) e) := CornerRing.instRing he_full.1
  letI : Algebra k (CornerRing (k := k) e) := CornerRing.instAlgebra he_full.1
  letI : Module.Finite k (CornerRing (k := k) e) := CornerRing.instModuleFinite
  have hMoritaBC : MoritaEquivalent B (CornerRing (k := k) e) :=
    h.symm'.trans' hMoritaCorner
  -- Step 4: Two basic Morita equivalent algebras are isomorphic
  have hbasic_corner' : IsBasicAlgebra.{_, _, u} k (CornerRing (k := k) e) :=
    fun M _ _ _ _ _ => hbasic_corner M
  exact basic_morita_algEquiv B (CornerRing (k := k) e) _hB hbasic_corner' hMoritaBC

/-- **Dimension bound from Morita equivalence**: If `A` and `B` are Morita
equivalent, then `dim B ≤ dim A` (when `B` is the basic algebra).
This follows from `B ≅ eAe` and `dim(eAe) ≤ dim(A)`. -/
theorem MoritaEquivalent.finrank_cornerRing_le
    (A : Type u) [Ring A] [Algebra k A] [Module.Finite k A]
    (e : A) :
    Module.finrank k (cornerSubmodule (k := k) e) ≤ Module.finrank k A :=
  finrank_cornerSubmodule_le e

end Etingof
