import EtingofRepresentationTheory.Chapter2.Definition2_3_8
import EtingofRepresentationTheory.Chapter9.Definition9_7_1
import EtingofRepresentationTheory.Chapter9.Definition9_7_2
import EtingofRepresentationTheory.Infrastructure.CornerRing
import EtingofRepresentationTheory.Infrastructure.BasicAlgebraExistence
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Algebra.Opposite
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.CategoryTheory.Conj
import Mathlib.CategoryTheory.Simple
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.LinearAlgebra.Projection
import Mathlib.Algebra.Category.ModuleCat.Limits
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

/-! ## Internal direct sum ↔ categorical biproduct bridge -/

/-- Given an internal direct sum `A = ⊕ᵢ N(i)` as `A`-submodules, construct a categorical
biproduct isomorphism in `ModuleCat A`:  `ModuleCat.of A A ≅ ⨁ᵢ ModuleCat.of A (N i)`.

This bridges the module-theoretic `DirectSum.IsInternal` with the categorical biproduct
in `ModuleCat`, which is needed to apply equivalence functors to decomposed modules. -/
noncomputable def internalDirectSum_biproductIso
    {A : Type u} [Ring A] {ι : Type} [Fintype ι] [DecidableEq ι]
    (N : ι → Submodule A A)
    (h : DirectSum.IsInternal N) :
    ModuleCat.of A A ≅ ⨁ (fun i => ModuleCat.of A (↥(N i))) := by
  -- Step 1: IsInternal gives a linear equivalence (⨁ᵢ N(i)) ≃ₗ[A] A
  let e₁ := (LinearEquiv.ofBijective (DirectSum.coeLinearMap N) h)
  -- Step 2: linearEquivFunOnFintype gives (⨁ᵢ ↥(N i)) ≃ₗ[A] (∀ i, ↥(N i))
  let e₂ := DirectSum.linearEquivFunOnFintype A ι (fun i => ↥(N i))
  -- Step 3: biproductIsoPi gives ⨁ f ≅ ModuleCat.of A (∀ j, f j) in ModuleCat
  let e₃ := ModuleCat.biproductIsoPi (fun i => ModuleCat.of A (↥(N i)))
  -- Compose: A ←≃ ⨁ᵢ N(i) ≃ ∀ i, N(i) ≃← ⨁ (ModuleCat.of A (N i))
  exact e₁.symm.toModuleIso ≪≫ e₂.toModuleIso ≪≫ e₃.symm

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

/- Two basic algebras that are Morita equivalent are isomorphic as `k`-algebras.

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

/-
## Implementation of basic_morita_algEquiv

The proof decomposes into three pieces:
1. `basic_morita_regular_module_iso`: F(B₁) ≅ B₂ as B₂-modules (the hard step)
2. `equivEndAlgEquiv`: End_{B₁}(B₁) ≃ₐ[k] End_{B₂}(B₂) via the equivalence
3. Assembly: B₁ᵐᵒᵖ ≅ End(B₁) ≅ End(B₂) ≅ B₂ᵐᵒᵖ → B₁ ≅ B₂
-/

/-- For basic Morita-equivalent algebras, the regular modules correspond under the
equivalence. More precisely, if `F : ModuleCat B₁ ≌ ModuleCat B₂` and both `B₁`
and `B₂` are basic, then `F(B₁) ≅ B₂` as `B₂`-modules.

This uses: `F` bijects simple modules (`simple_of_equivalence`), preserves
projective covers, and for basic algebras the regular module is the unique
projective module with head `≅ k^n` (one copy of each simple). -/
private noncomputable def basic_morita_regular_module_iso [IsAlgClosed k]
    (B₁ : Type u) [Ring B₁] [Algebra k B₁] [Module.Finite k B₁]
    (B₂ : Type u) [Ring B₂] [Algebra k B₂] [Module.Finite k B₂]
    (_hB₁ : IsBasicAlgebra k B₁) (_hB₂ : IsBasicAlgebra k B₂)
    (F : ModuleCat.{u} B₁ ≌ ModuleCat.{u} B₂) :
    F.functor.obj (ModuleCat.of B₁ B₁) ≅ ModuleCat.of B₂ B₂ := by
  sorry

/-- The functor of an equivalence between module categories is additive.
An equivalence functor is full and preserves binary products, hence is additive. -/
private noncomputable instance equivFunctorAdditive
    {R : Type u} [Ring R] {S : Type u} [Ring S]
    (E : ModuleCat.{u} R ≌ ModuleCat.{u} S) : E.functor.Additive := by
  haveI : E.functor.IsEquivalence := E.isEquivalence_functor
  exact Functor.additive_of_preserves_binary_products E.functor

private noncomputable def equivEndAlgEquiv [IsAlgClosed k]
    (B₁ : Type u) [Ring B₁] [Algebra k B₁]
    (B₂ : Type u) [Ring B₂] [Algebra k B₂]
    (F : ModuleCat.{u} B₁ ≌ ModuleCat.{u} B₂)
    (α : F.functor.obj (ModuleCat.of B₁ B₁) ≅ ModuleCat.of B₂ B₂) :
    Module.End B₁ B₁ ≃ₐ[k] Module.End B₂ B₂ := by
  -- The proof combines three pieces:
  -- (a) endRingEquiv converts between categorical End and Module.End
  -- (b) The equivalence F gives End(X) ≃* End(F(X)) (fully faithful)
  -- (c) The iso α gives End(F(B₁)) ≃ End(B₂) (conjugation)
  -- We construct the composite as an AlgEquiv.
  haveI := equivFunctorAdditive F
  let X := ModuleCat.of B₁ B₁
  let Y := ModuleCat.of B₂ B₂
  -- The fully faithful mulEquivEnd is a ring equiv when the functor is additive
  let fRing : End X ≃+* End (F.functor.obj X) := {
    F.fullyFaithfulFunctor.mulEquivEnd X with
    map_add' := fun _ _ => F.functor.map_add
  }
  -- α.conj is a ring equiv in the preadditive category ModuleCat B₂
  let αRing : End (F.functor.obj X) ≃+* End Y := {
    α.conj with
    map_add' := fun f g => by
      change α.inv ≫ (f + g) ≫ α.hom = (α.inv ≫ f ≫ α.hom) + (α.inv ≫ g ≫ α.hom)
      rw [CategoryTheory.Preadditive.add_comp, CategoryTheory.Preadditive.comp_add]
  }
  -- endRingEquiv converts categorical End ≃+* Module.End
  let eB₁ := ModuleCat.endRingEquiv X
  let eB₂ := ModuleCat.endRingEquiv Y
  -- Compose to get the full RingEquiv
  let re : Module.End B₁ B₁ ≃+* Module.End B₂ B₂ :=
    eB₁.symm.trans (fRing.trans (αRing.trans eB₂))
  -- Upgrade to AlgEquiv: the composite preserves algebraMap k
  -- algebraMap k (Module.End R M) c = c • LinearMap.id, and the functor+conjugation
  -- preserves this because the equivalence is k-linear on endomorphism rings.
  -- This requires the Eilenberg-Watts theorem in full generality; we sorry this step.
  exact AlgEquiv.ofRingEquiv (f := re) (fun c => by
    -- Need: re (algebraMap k (Module.End B₁ B₁) c) = algebraMap k (Module.End B₂ B₂) c
    -- i.e., the ring equiv preserves k-scalar endomorphisms.
    -- This holds because equivalences of module categories over k-algebras are k-linear
    -- (Eilenberg-Watts theorem), but proving this requires substantial infrastructure.
    sorry)

private lemma basic_morita_algEquiv [IsAlgClosed k]
    (B₁ : Type u) [Ring B₁] [Algebra k B₁] [Module.Finite k B₁]
    (B₂ : Type u) [Ring B₂] [Algebra k B₂] [Module.Finite k B₂]
    (_hB₁ : IsBasicAlgebra k B₁) (_hB₂ : IsBasicAlgebra k B₂)
    (h : MoritaEquivalent B₁ B₂) :
    Nonempty (B₁ ≃ₐ[k] B₂) := by
  obtain ⟨F⟩ := h
  -- Step 1: F sends regular B₁-module to regular B₂-module (for basic algebras)
  have hα := basic_morita_regular_module_iso B₁ B₂ _hB₁ _hB₂ F
  -- Step 2: Endomorphism ring isomorphism: End_{B₁}(B₁) ≃ₐ[k] End_{B₂}(B₂)
  have hEnd := equivEndAlgEquiv (k := k) B₁ B₂ F hα
  -- Step 3: B₁ᵐᵒᵖ ≃ₐ[k] End_{B₁}(B₁) and End_{B₂}(B₂) ≃ₐ[k] B₂ᵐᵒᵖ
  have hB1op : B₁ᵐᵒᵖ ≃ₐ[k] Module.End B₁ B₁ :=
    AlgEquiv.moduleEndSelf (A := B₁) k
  have hB2op : B₂ᵐᵒᵖ ≃ₐ[k] Module.End B₂ B₂ :=
    AlgEquiv.moduleEndSelf (A := B₂) k
  -- Step 4: Compose to get B₁ᵐᵒᵖ ≃ₐ[k] B₂ᵐᵒᵖ
  have hOp : B₁ᵐᵒᵖ ≃ₐ[k] B₂ᵐᵒᵖ := hB1op.trans (hEnd.trans hB2op.symm)
  -- Step 5: Transfer from opposite to original
  exact ⟨AlgEquiv.unop hOp⟩

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

/-! ## Indecomposable preservation under equivalence -/

/-- An equivalence of module categories preserves indecomposability.

**Proof**: Given `IsCompl W₁ W₂` for submodules of `F(M)`, the linear projection
is an idempotent endomorphism of `F(M)`. Since `F` is fully faithful, there exists
a unique endomorphism `q` of `M` with `F(q) = p`. Since `F` preserves composition,
`q` is idempotent. By indecomposability of `M`, `range q = ⊥` or `ker q = ⊥`,
which implies `W₁ = ⊥` or `W₂ = ⊥`. -/
lemma equiv_preserves_indecomposable
    {B₁ : Type u} [Ring B₁] {B₂ : Type u} [Ring B₂]
    (F : ModuleCat.{u} B₁ ≌ ModuleCat.{u} B₂)
    {M : ModuleCat.{u} B₁}
    (hM : Etingof.IsIndecomposable B₁ M) :
    Etingof.IsIndecomposable B₂ (F.functor.obj M) := by
  obtain ⟨hnt, hind⟩ := hM
  refine ⟨?_, ?_⟩
  · -- Nontriviality: F(M) is nontrivial because M is
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    -- F(M) subsingleton → F(M) is zero → M is zero (via faithful functor)
    have hzFM : IsZero (F.functor.obj M) := ModuleCat.isZero_of_subsingleton _
    have hzM : IsZero M := by
      rw [IsZero.iff_id_eq_zero]
      apply F.functor.map_injective
      rw [F.functor.map_id, F.functor.map_zero]
      exact (IsZero.iff_id_eq_zero _).mp hzFM
    exact (not_subsingleton_iff_nontrivial.mpr hnt) (ModuleCat.subsingleton_of_isZero hzM)
  · -- No nontrivial complemented submodules
    intro W₁ W₂ hc
    -- Construct the idempotent projection p : F(M) →ₗ F(M) onto W₁ along W₂
    let proj := Submodule.linearProjOfIsCompl W₁ W₂ hc
    let p : (F.functor.obj M) →ₗ[B₂] (F.functor.obj M) :=
      W₁.subtype.comp proj
    have hp_idem : p.comp p = p := by
      ext x
      simp only [p, LinearMap.comp_apply, Submodule.subtype_apply]
      congr 1
      exact Submodule.linearProjOfIsCompl_apply_left hc (proj x)
    -- Lift p to a categorical endomorphism of F(M)
    let p_cat : F.functor.obj M ⟶ F.functor.obj M := ModuleCat.ofHom p
    -- Use full faithfulness to get the preimage q : M ⟶ M
    let q_cat : M ⟶ M := F.functor.preimage p_cat
    -- q is idempotent because F preserves composition and is faithful
    have hq_map : F.functor.map q_cat = p_cat := F.functor.map_preimage p_cat
    have hp_idem_cat : p_cat ≫ p_cat = p_cat := by
      ext x; exact LinearMap.congr_fun hp_idem x
    have hq_idem_cat : q_cat ≫ q_cat = q_cat := by
      apply F.functor.map_injective
      simp only [F.functor.map_comp, hq_map, hp_idem_cat]
    -- Extract the linear map and its idempotency
    let q : M →ₗ[B₁] M := q_cat.hom
    have hq_idem : IsIdempotentElem q := by
      ext x; exact LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp hq_idem_cat) x
    -- By indecomposability of M, range q = ⊥ or ker q = ⊥
    have hcompl_q : IsCompl (LinearMap.range q) (LinearMap.ker q) :=
      open LinearMap in IsIdempotentElem.isCompl hq_idem
    rcases hind (LinearMap.range q) (LinearMap.ker q) hcompl_q with hrange | hker
    · -- range q = ⊥ → q = 0 → p = 0 → W₁ = ⊥
      left
      have hq_zero : q = 0 := LinearMap.range_eq_bot.mp hrange
      have hp_zero : p = 0 := by
        have hp_cat_zero : p_cat = 0 := by
          rw [← hq_map]
          have : q_cat = 0 := ModuleCat.hom_ext_iff.mpr hq_zero
          rw [this, F.functor.map_zero]
        exact ModuleCat.hom_ext_iff.mp hp_cat_zero
      -- p = 0 means W₁.subtype ∘ proj = 0
      -- For x ∈ W₁: p x = x (projection is identity on W₁), so x = 0
      rw [eq_bot_iff]
      intro x hx
      have hp_x : p x = 0 := LinearMap.congr_fun hp_zero x
      -- proj is identity on W₁: proj ⟨x, hx⟩ = ⟨x, hx⟩
      have hproj := Submodule.linearProjOfIsCompl_apply_left hc ⟨x, hx⟩
      -- p x = ↑(proj x) = ↑⟨x, hx⟩ = x
      have : p x = x := by
        change (W₁.subtype (proj x)) = x
        rw [hproj]; rfl
      rw [this] at hp_x
      exact hp_x
    · -- ker q = ⊥ → q = id (idempotent + injective) → p = id → W₂ = ⊥
      right
      have hq_id : q = LinearMap.id := by
        ext x
        have hqx_mem : q x - x ∈ LinearMap.ker q := by
          rw [LinearMap.mem_ker, map_sub]
          have : q (q x) = q x := LinearMap.congr_fun (show q.comp q = q from hq_idem) x
          rw [this, sub_self]
        rw [hker, Submodule.mem_bot, sub_eq_zero] at hqx_mem
        rw [hqx_mem, LinearMap.id_apply]
      have hp_id : p = LinearMap.id := by
        have hp_cat_id : p_cat = 𝟙 _ := by
          rw [← hq_map, ← F.functor.map_id]
          congr 1
          exact ModuleCat.hom_ext_iff.mpr hq_id
        exact ModuleCat.hom_ext_iff.mp hp_cat_id
      -- p = id means the projection onto W₁ is the identity, so W₁ = ⊤
      have hW1_top : W₁ = ⊤ := by
        rw [eq_top_iff]
        intro x _
        have hpx : p x = x := LinearMap.congr_fun hp_id x
        have : W₁.subtype (proj x) = x := hpx
        rw [Submodule.subtype_apply] at this
        have hmem := (proj x).2
        rwa [this] at hmem
      exact eq_bot_of_isCompl_top (hW1_top ▸ hc.symm)

end Etingof
