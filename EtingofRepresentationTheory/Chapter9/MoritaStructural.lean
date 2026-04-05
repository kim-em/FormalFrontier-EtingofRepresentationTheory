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
import Mathlib.Algebra.Category.ModuleCat.Algebra
import Mathlib.CategoryTheory.Linear.LinearFunctor
import Mathlib.CategoryTheory.Preadditive.Projective.Preserves
import Mathlib.RingTheory.Jacobson.Radical
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.Algebra.Category.ModuleCat.Projective

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
open scoped ModuleCat

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

/-! ## Helper lemmas for basic_morita_regular_module_iso

The proof that F(B₁) ≅ B₂ for basic Morita-equivalent algebras proceeds by:

1. F(B₁) is projective as a B₂-module (equivalences preserve projectives).
2. Both F(B₁)/J·F(B₁) and B₂/J·B₂ are isomorphic to ⊕ᵢ Sᵢ (one copy of each
   simple), because both algebras are basic and the equivalence bijects simples.
3. Using projectivity of F(B₁), lift the head isomorphism to a map f : F(B₁) → B₂.
4. By Nakayama's lemma (non-commutative version), f is surjective.
5. Since B₂ is projective (free module of rank 1), f splits: F(B₁) ≅ B₂ ⊕ K.
6. Nakayama kills K: from step 2, K/J·K = 0, so K = 0 by finite generation.
-/

/-- A B₂-linear surjection from a module P to B₂ whose kernel
    is killed by the Jacobson radical gives P ≅ B₂.

    More precisely: if `f : P →ₗ B₂` is surjective, `B₂` is Artinian, and the
    kernel `K` satisfies `K ≤ J(B₂) • K`, then `K = 0` by nilpotency of the
    Jacobson radical (which is nilpotent for Artinian rings), and `f` is an
    isomorphism. This avoids needing `Module.Finite B₂ P` (which would require
    showing that equivalences preserve finite generation). -/
private noncomputable def iso_of_surjection_with_trivial_kernel_head
    {B₂ : Type u} [Ring B₂] [IsArtinianRing B₂]
    (P : ModuleCat.{u} B₂)
    (f : P →ₗ[B₂] B₂) (hf_surj : Function.Surjective f)
    (hker : LinearMap.ker f ≤ Ring.jacobson B₂ • (LinearMap.ker f)) :
    P ≅ ModuleCat.of B₂ B₂ := by
  -- ker f = J • ker f (since hker gives ≤ and smul_le_right gives ≥)
  have heq : LinearMap.ker f = Ring.jacobson B₂ • LinearMap.ker f :=
    le_antisymm hker Submodule.smul_le_right
  -- ker f = ⊥ by nilpotency of the Jacobson radical
  have hker_bot : LinearMap.ker f = ⊥ := by
    obtain ⟨n, hn⟩ := (IsSemiprimaryRing.isNilpotent : IsNilpotent (Ring.jacobson B₂))
    -- Key: ker f = J^k • ker f for all k
    -- Because ker f = J • ker f, so J^k • ker f = J^k • (J • ker f) = (J^k * J) • ker f
    --   = J^(k+1) • ker f (by pow_succ)
    -- Key: J^k • ker f = J^(k+1) • ker f for all k
    -- Because ker f = J • ker f (heq), so
    --   J^k • ker f = J^k • (J • ker f) = (J^k * J) • ker f = J^(k+1) • ker f
    have hstep : ∀ k, Ring.jacobson B₂ ^ k • LinearMap.ker f =
        Ring.jacobson B₂ ^ (k + 1) • LinearMap.ker f := fun k => by
      conv_lhs => rw [heq]
      rw [← Submodule.mul_smul, ← Submodule.pow_succ]
    -- Therefore ker f = J^k • ker f for all k
    suffices h : ∀ k, LinearMap.ker f = Ring.jacobson B₂ ^ k • LinearMap.ker f by
      have h1 := h n
      rw [eq_bot_iff, h1]
      have : (Ring.jacobson B₂ ^ n : Ideal B₂) = ⊥ := by rwa [Ideal.zero_eq_bot] at hn
      rw [this, Submodule.bot_smul]
    intro k; induction k with
    | zero => rw [Submodule.pow_zero, Ideal.one_eq_top, Submodule.top_smul]
    | succ k ih => rw [← hstep, ← ih]
  -- f is injective
  have hf_inj : Function.Injective f :=
    LinearMap.ker_eq_bot.mp hker_bot
  -- Construct the isomorphism from the bijective linear map
  exact (LinearEquiv.ofBijective f ⟨hf_inj, hf_surj⟩).toModuleIso

/-- For basic Morita-equivalent algebras over an algebraically closed field,
    there exists a B₂-linear surjection F(B₁) → B₂ whose kernel K satisfies
    K ≤ J(B₂) • K.

    The surjection is constructed by:
    1. Showing F(B₁)/J·F(B₁) ≅ B₂/J·B₂ (both are ⊕ᵢ Sᵢ with each simple once,
       since both algebras are basic and F bijects simples).
    2. Using projectivity of F(B₁) to lift the surjection F(B₁) → F(B₁)/J·F(B₁)
       → B₂/J·B₂ through the quotient B₂ → B₂/J·B₂.
    3. By Nakayama, the lifted map is surjective (image covers B₂ mod J).
    4. Splitting (B₂ projective) gives F(B₁) ≅ B₂ ⊕ K where K/J·K = 0. -/
-- Helper 1: An equivalence of module categories preserves projectivity.
-- F(B₁) is projective as a B₂-module because B₁ is projective (free rank 1)
-- and equivalences preserve projective objects.
private noncomputable instance equiv_image_projective
    {R : Type u} [Ring R] {S : Type u} [Ring S]
    (F : ModuleCat.{u} R ≌ ModuleCat.{u} S) :
    Module.Projective S (F.functor.obj (ModuleCat.of R R)) := by
  -- R is projective as a module over itself (it's free of rank 1)
  haveI : Module.Projective R R := Module.Projective.of_free
  haveI : CategoryTheory.Projective (ModuleCat.of R R) :=
    (ModuleCat.of R R).projective_of_categoryTheory_projective
  haveI : CategoryTheory.Projective (F.functor.obj (ModuleCat.of R R)) :=
    (F.map_projective_iff _).mpr ‹CategoryTheory.Projective (ModuleCat.of R R)›
  exact (F.functor.obj (ModuleCat.of R R)).projective_of_module_projective

-- Helper 2: A projective lift of a surjection through a nilpotent quotient is surjective.
-- If P is projective, g : P → B₂/J is surjective, and J is nilpotent, then the
-- lift f : P → B₂ (with π ∘ f = g) is also surjective.
private theorem projective_lift_surjective
    {B₂ : Type u} [Ring B₂] [IsSemiprimaryRing B₂]
    {P : Type u} [AddCommGroup P] [Module B₂ P]
    {f : P →ₗ[B₂] B₂}
    {g : P →ₗ[B₂] B₂ ⧸ (Ring.jacobson B₂ • ⊤ : Submodule B₂ B₂)}
    (hg_surj : Function.Surjective g)
    (hf : (Ring.jacobson B₂ • ⊤ : Submodule B₂ B₂).mkQ ∘ₗ f = g) :
    Function.Surjective f := by
  rw [← LinearMap.range_eq_top]
  let π := (Ring.jacobson B₂ • ⊤ : Submodule B₂ B₂).mkQ
  -- First show range f + J•⊤ = ⊤
  have h_range_sup : LinearMap.range f ⊔ (Ring.jacobson B₂ • ⊤ : Submodule B₂ B₂) = ⊤ := by
    rw [eq_top_iff]
    intro b _
    obtain ⟨p, hp⟩ := hg_surj (π b)
    have hπfp : π (f p) = π b := by rw [← LinearMap.comp_apply, hf, hp]
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at hπfp
    exact Submodule.mem_sup.mpr ⟨f p, LinearMap.mem_range.mpr ⟨p, rfl⟩, b - f p,
      neg_sub (f p) b ▸ Submodule.neg_mem _ hπfp, add_sub_cancel (f p) b⟩
  -- Use nilpotency of J to conclude range f = ⊤
  obtain ⟨n, hn⟩ := (IsSemiprimaryRing.isNilpotent : IsNilpotent (Ring.jacobson B₂))
  suffices h : ∀ k, LinearMap.range f ⊔ Ring.jacobson B₂ ^ k • ⊤ = ⊤ by
    have h1 := h n
    have : (Ring.jacobson B₂ ^ n : Ideal B₂) = ⊥ := by rwa [Ideal.zero_eq_bot] at hn
    rw [this, Submodule.bot_smul, sup_bot_eq] at h1
    exact h1
  intro k; induction k with
  | zero =>
    simp only [Submodule.pow_zero, Ideal.one_eq_top, Submodule.top_smul, sup_top_eq]
  | succ k ih =>
    -- J^k • ⊤ ≤ range f ⊔ J^(k+1) • ⊤ since J^k • ⊤ = J^k • (range f ⊔ J•⊤)
    have hstep : Ring.jacobson B₂ ^ k • (⊤ : Submodule B₂ B₂) ≤
        LinearMap.range f ⊔ Ring.jacobson B₂ ^ (k + 1) • ⊤ := by
      calc Ring.jacobson B₂ ^ k • ⊤
          = Ring.jacobson B₂ ^ k • (LinearMap.range f ⊔ Ring.jacobson B₂ • ⊤) := by
            rw [h_range_sup]
        _ = Ring.jacobson B₂ ^ k • LinearMap.range f ⊔
            Ring.jacobson B₂ ^ k • (Ring.jacobson B₂ • ⊤) := Submodule.smul_sup _ _ _
        _ ≤ LinearMap.range f ⊔ Ring.jacobson B₂ ^ (k + 1) • ⊤ := by
            apply sup_le_sup
            · exact Submodule.smul_le_right
            · rw [← Submodule.mul_smul, ← Submodule.pow_succ]
    exact le_antisymm le_top (ih.symm.le.trans
      ((sup_le_sup_left hstep _).trans (by rw [← sup_assoc, sup_idem])))

-- Helper 3: The Jacobson radical annihilates semisimple modules.
-- For a semisimple B₂-module M, J₂ • M = 0.
private theorem jacobson_smul_eq_bot_of_semisimple
    {B₂ : Type u} [Ring B₂]
    {M : Type u} [AddCommGroup M] [Module B₂ M] [IsSemisimpleModule B₂ M] :
    Ring.jacobson B₂ • (⊤ : Submodule B₂ M) = ⊥ :=
  le_bot_iff.mp ((Ring.jacobson_smul_top_le B₂ M).trans
    (le_of_eq (IsSemisimpleModule.jacobson_eq_bot B₂ M)))

-- Helper 4: Module.jacobson equals J·M for modules over Artinian (hence semiprimary) rings.
private theorem module_jacobson_eq_smul_of_artinian
    {B₂ : Type u} [Ring B₂] [IsArtinianRing B₂]
    {M : Type u} [AddCommGroup M] [Module B₂ M] :
    Module.jacobson B₂ M = Ring.jacobson B₂ • (⊤ : Submodule B₂ M) := by
  apply le_antisymm
  · -- M/(J·M) is J-torsion, so it's a B₂/J-module. B₂/J is semisimple (semiprimary),
    -- so M/(J·M) is semisimple as B₂/J-module, hence as B₂-module.
    -- Then Module.jacobson(M/(J·M)) = ⊥, and le_comap_jacobson gives the result.
    set N := Ring.jacobson B₂ • (⊤ : Submodule B₂ M) with hN
    have h_tors := Module.isTorsionBySet_quotient_ideal_smul M (Ring.jacobson B₂)
    -- M/(J·M) is semisimple as B₂-module (transfer from B₂/J-semisimplicity)
    haveI : IsSemisimpleModule B₂ (M ⧸ N) := h_tors.isSemisimpleModule_iff.mp inferInstance
    have h_le := Module.le_comap_jacobson (f := N.mkQ)
    rw [IsSemisimpleModule.jacobson_eq_bot B₂ (M ⧸ N), Submodule.comap_bot,
      Submodule.ker_mkQ] at h_le
    exact h_le
  · exact Ring.jacobson_smul_top_le B₂ M

-- Helper 5: For an equivalence F, there exists a nonzero morphism F(B₁) → S
-- for every simple S. Uses the adjunction: Hom(F(B₁), S) ≅ Hom(B₁, G(S)) ≅ G(S) ≠ 0.
private theorem equiv_hom_to_simple_nonzero
    {B₁ : Type u} [Ring B₁]
    {B₂ : Type u} [Ring B₂]
    (F : ModuleCat.{u} B₁ ≌ ModuleCat.{u} B₂)
    (S : ModuleCat.{u} B₂) [hS : Simple S] :
    ∃ (f : F.functor.obj (ModuleCat.of B₁ B₁) ⟶ S), f ≠ 0 := by
  -- G(S) is simple (by simple_of_equivalence for the inverse)
  haveI : Simple (F.inverse.obj S) := simple_of_equivalence F.symm S
  -- G(S) is nontrivial: Simple objects are not the zero object
  have hGS_nt : Nontrivial (F.inverse.obj S) := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact Simple.not_isZero (F.inverse.obj S) (ModuleCat.isZero_of_subsingleton _)
  -- Pick a nonzero element m ∈ G(S)
  obtain ⟨m, hm⟩ := exists_ne (0 : F.inverse.obj S)
  -- The B₁-linear map φ_m : B₁ → G(S) sending b ↦ b • m
  let φ_m : ModuleCat.of B₁ B₁ ⟶ F.inverse.obj S :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton B₁ (F.inverse.obj S) m)
  -- φ_m is nonzero (φ_m(1) = m ≠ 0)
  have hφ_ne : φ_m ≠ 0 := by
    intro h
    apply hm
    have h1 : φ_m.hom = (0 : ModuleCat.of B₁ B₁ ⟶ F.inverse.obj S).hom :=
      congrArg ModuleCat.Hom.hom h
    have h2 : φ_m.hom (1 : B₁) = 0 := by rw [h1]; rfl
    simpa [φ_m, LinearMap.toSpanSingleton_apply] using h2
  -- Under the adjunction F ⊣ G: nonzero φ_m maps to a nonzero morphism F(B₁) → S
  let f : F.functor.obj (ModuleCat.of B₁ B₁) ⟶ S :=
    (F.toAdjunction.homEquiv _ _).symm φ_m
  refine ⟨f, ?_⟩
  intro hf
  apply hφ_ne
  have h2 : φ_m = (F.toAdjunction.homEquiv _ _) f := by
    rw [Equiv.apply_symm_apply]
  rw [h2, hf, Adjunction.homEquiv_apply, F.inverse.map_zero, comp_zero]

-- Helper 5b: For a surjective B₂-linear map π : F(B₁) → S where S is semisimple,
-- the image of F(J₁·B₁) under π is zero. This means F(J₁·B₁) is contained in
-- the kernel of every map to a semisimple quotient of F(B₁).
-- Proof: J₂ annihilates S, and the image of J₁·B₁ under the adjunction
-- correspondence lands in J₁, which annihilates all simple B₁-modules.
-- (This helper captures the key "radical preservation" property of equivalences.)
-- The full proof requires: for each maximal submodule N of F(B₁), the composition
-- F(J₁·B₁) → F(B₁) → F(B₁)/N is zero. This follows from the adjunction:
-- the preimage of this map in Hom_{B₁}(J₁·B₁, G(F(B₁)/N)) is zero because
-- J₁ annihilates the simple module G(F(B₁)/N).

private noncomputable def exists_surjection_with_trivial_kernel_head [IsAlgClosed k]
    (B₁ : Type u) [Ring B₁] [Algebra k B₁] [Module.Finite k B₁]
    (B₂ : Type u) [Ring B₂] [Algebra k B₂] [Module.Finite k B₂]
    (_hB₁ : IsBasicAlgebra k B₁) (_hB₂ : IsBasicAlgebra k B₂)
    (F : ModuleCat.{u} B₁ ≌ ModuleCat.{u} B₂) :
    Σ' (f : (F.functor.obj (ModuleCat.of B₁ B₁)) →ₗ[B₂] B₂),
      Function.Surjective f ∧
      LinearMap.ker f ≤ Ring.jacobson B₂ • (LinearMap.ker f) := by
  haveI := equiv_image_projective F
  haveI : IsArtinianRing B₂ := IsArtinianRing.of_finite k B₂
  -- Use Pt for the carrier type to work around HasQuotient synthesis issues
  set Pt : Type u := ↑(F.functor.obj (ModuleCat.of B₁ B₁))
  set P := F.functor.obj (ModuleCat.of B₁ B₁) with hP_def
  set J₂ := Ring.jacobson B₂
  set JP := (J₂ • ⊤ : Submodule B₂ Pt) with hJP_def
  set JB := (J₂ • ⊤ : Submodule B₂ B₂) with hJB_def
  -- STEP 1: Construct a surjection g : Pt → B₂/JB whose kernel is JP.
  -- This encodes the head isomorphism: F(B₁)/(J₂·F(B₁)) ≅ B₂/J₂ as B₂-modules.
  --
  -- Both quotients are semisimple B₂-modules (by module_jacobson_eq_smul_of_artinian).
  -- For basic algebras, B₂/J₂ ≅ kⁿ as k-algebras (Wedderburn-Artin), so each simple
  -- B₂-module Sᵢ has dim_k = 1, and B₂/J₂ = S₁ ⊕ ... ⊕ Sₙ (each simple once).
  --
  -- The key multiplicity computation uses the adjunction F ⊣ G = F⁻¹:
  --   Hom_{B₂}(F(B₁), Sᵢ) ≅ Hom_{B₁}(B₁, G(Sᵢ)) ≅ G(Sᵢ)
  -- Since G preserves simples (simple_of_equivalence) and B₁ is basic, dim_k G(Sᵢ) = 1.
  -- So each simple Sᵢ appears with multiplicity 1 in the head F(B₁)/J₂·F(B₁).
  --
  -- Both heads have each simple with multiplicity 1, hence are isomorphic as B₂-modules.
  -- This requires the classification of semisimple modules by simple multiplicities,
  -- which is not yet available as a single Mathlib lemma.
  -- Proof paths: (a) Krull-Schmidt for semisimple modules, or
  --              (b) Wedderburn-Artin B₂/J ≅ kⁿ + classify kⁿ-modules by component dims.
  have head_iso : (Pt ⧸ JP) ≃ₗ[B₂] (B₂ ⧸ JB) := sorry
  let g : Pt →ₗ[B₂] B₂ ⧸ JB := head_iso.toLinearMap.comp JP.mkQ
  have hg_surj : Function.Surjective g :=
    head_iso.surjective.comp (Submodule.mkQ_surjective JP)
  have hg_ker : LinearMap.ker g = JP := by
    ext x
    simp only [g, LinearMap.mem_ker, LinearMap.comp_apply]
    exact (head_iso.map_eq_zero_iff).trans (Submodule.Quotient.mk_eq_zero JP)
  -- STEP 2: Lift g to f : P → B₂ by projectivity of P
  have hex_f := Module.projective_lifting_property JB.mkQ g (Submodule.mkQ_surjective _)
  let f : ↑P →ₗ[B₂] B₂ := hex_f.choose
  have hf : JB.mkQ ∘ₗ f = g := hex_f.choose_spec
  -- STEP 3: f is surjective (Nakayama via projective_lift_surjective)
  have hf_surj : Function.Surjective f := projective_lift_surjective hg_surj hf
  -- STEP 4: ker f ≤ J₂ • ker f using splitting argument
  -- Split f: since B₂ is projective (free rank 1), ∃ section s with f ∘ s = id
  have hex_s := LinearMap.exists_rightInverse_of_surjective f
    (LinearMap.range_eq_top.mpr hf_surj)
  let s : B₂ →ₗ[B₂] ↑P := hex_s.choose
  have hs : f ∘ₗ s = LinearMap.id := hex_s.choose_spec
  -- Step 4a: ker f ⊆ J₂ • P (g kills ker f and head_iso is injective)
  have hker_le_JP : LinearMap.ker f ≤ JP := by
    intro x hx
    rw [LinearMap.mem_ker] at hx
    have hgx : g x = 0 := by rw [← hf, LinearMap.comp_apply, hx, map_zero]
    rw [← hg_ker]
    exact LinearMap.mem_ker.mpr hgx
  -- Step 4b: Upgrade ker f ⊆ J₂ • ⊤ to ker f ⊆ J₂ • ker f using the section
  -- Define the kernel projection: proj = id - s ∘ f (projects onto ker f)
  let proj : ↑P →ₗ[B₂] ↑P := LinearMap.id - s.comp f
  have hproj_ker : ∀ p : ↑P, proj p ∈ LinearMap.ker f := fun p => by
    rw [LinearMap.mem_ker]
    change f (proj p) = 0
    simp only [proj, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, map_sub]
    -- Goal: f p - f (s (f p)) = 0
    have : (f ∘ₗ s) (f p) = f p := by rw [hs, LinearMap.id_apply]
    simp only [LinearMap.comp_apply] at this
    rw [this, sub_self]
  have hproj_id : ∀ x ∈ LinearMap.ker f, proj x = x := fun x hx => by
    simp only [proj, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply,
      LinearMap.mem_ker.mp hx, map_zero, sub_zero]
  have hker : LinearMap.ker f ≤ J₂ • LinearMap.ker f := by
    intro x hx
    -- proj(x) = x and x ∈ J₂ • ⊤, so suffices to show proj maps J₂ • ⊤ into J₂ • ker f
    rw [← hproj_id x hx]
    exact Submodule.smul_induction_on (hker_le_JP hx)
      (fun j hj p _ => by
        change proj (j • p) ∈ J₂ • LinearMap.ker f
        rw [proj.map_smul]
        exact Submodule.smul_mem_smul hj (hproj_ker p))
      (fun a b ha hb => by
        change proj (a + b) ∈ J₂ • LinearMap.ker f
        rw [map_add]
        exact Submodule.add_mem _ ha hb)
  exact ⟨f, hf_surj, hker⟩

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
  -- B₂ is Artinian (finite-dim over field)
  haveI : IsArtinianRing B₂ := IsArtinianRing.of_finite k B₂
  -- Obtain the surjection with trivial kernel head
  let ⟨f, hf_surj, hker⟩ :=
    exists_surjection_with_trivial_kernel_head B₁ B₂ _hB₁ _hB₂ F
  exact iso_of_surjection_with_trivial_kernel_head _ f hf_surj hker

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
    [F.functor.Additive] [F.functor.Linear k]
    (α : F.functor.obj (ModuleCat.of B₁ B₁) ≅ ModuleCat.of B₂ B₂) :
    Module.End B₁ B₁ ≃ₐ[k] Module.End B₂ B₂ := by
  let X := ModuleCat.of B₁ B₁
  let Y := ModuleCat.of B₂ B₂
  -- fRing: End(X) ≃+* End(F(X)) via fully faithful functor
  let fRing : End X ≃+* End (F.functor.obj X) := {
    F.fullyFaithfulFunctor.mulEquivEnd X with
    map_add' := fun _ _ => F.functor.map_add
  }
  -- αRing: End(F(X)) ≃+* End(Y) via conjugation by α
  let αRing : End (F.functor.obj X) ≃+* End Y := {
    α.conj with
    map_add' := fun f g => by
      change α.inv ≫ (f + g) ≫ α.hom =
        (α.inv ≫ f ≫ α.hom) + (α.inv ≫ g ≫ α.hom)
      rw [Preadditive.add_comp, Preadditive.comp_add]
  }
  -- Compose: Module.End B₁ B₁ ≃+* Module.End B₂ B₂
  let eB₁ := ModuleCat.endRingEquiv X
  let eB₂ := ModuleCat.endRingEquiv Y
  let re : Module.End B₁ B₁ ≃+* Module.End B₂ B₂ :=
    eB₁.symm.trans (fRing.trans (αRing.trans eB₂))
  -- Upgrade to AlgEquiv: re preserves algebraMap k.
  -- Chain: algebraMap c = c • 1 ↦ c • 𝟙 X ↦ c • 𝟙 (F.obj X) ↦ c • 𝟙 Y ↦ c • 1
  exact AlgEquiv.ofRingEquiv (f := re) (fun c => by
    -- re c = eB₂ (αRing (fRing (eB₁.symm c)))
    -- eB₁.symm (algebraMap k _ c) = algebraMap k _ c (as categorical endo)
    -- which is c • 𝟙 X in the k-linear category
    -- fRing (c • 𝟙 X) = F.map (c • 𝟙 X) = c • F.map (𝟙 X) = c • 𝟙 (F.obj X)
    -- αRing (c • 𝟙 FX) = α.inv ≫ (c • 𝟙 FX) ≫ α.hom = c • (α.inv ≫ 𝟙 ≫ α.hom)
    --                    = c • 𝟙 Y
    -- eB₂ (c • 𝟙 Y) = algebraMap k _ c
    change re (algebraMap k (Module.End B₁ B₁) c) =
      algebraMap k (Module.End B₂ B₂) c
    simp only [Algebra.algebraMap_eq_smul_one]
    change eB₂ (αRing (fRing (eB₁.symm (c • 1)))) = c • 1
    -- Step 1: eB₁.symm (c • 1) = c • 𝟙 X (bridging End↔Hom SMul via hom_ext)
    have h1 : eB₁.symm (c • (1 : Module.End B₁ B₁)) =
        (c • (𝟙 X : X ⟶ X) : X ⟶ X) :=
      ModuleCat.hom_ext rfl
    -- fRing is definitionally F.functor.map
    change eB₂ (αRing (F.functor.map (eB₁.symm (c • (1 : Module.End B₁ B₁))))) = c • 1
    rw [h1]
    -- Work at element level to bypass SMul instance diamond
    -- between Algebra.toModule and RestrictScalars.module
    apply LinearMap.ext; intro x
    -- RHS: (c • 1 : Module.End B₂ B₂) x = c • x
    simp only [LinearMap.smul_apply]
    -- LHS: (re (c • 1)) x = eB₂(αRing(fRing(eB₁.symm(c • 1)))) x
    -- eB₂ f = f.hom (endRingEquiv), so LHS = (αRing(fRing(eB₁.symm(c•1)))).hom x
    -- αRing f = α.inv ≫ f ≫ α.hom, so .hom x = α.hom.hom(f.hom(α.inv.hom x))
    -- fRing = F.map, eB₁.symm f = ⟨f⟩ (ofHom)
    -- So LHS = α.hom.hom((F.map ⟨c•1⟩).hom(α.inv.hom x))
    -- By F's k-linearity: F.map(c•𝟙 X) = c•𝟙(F.obj X) (at .hom level)
    -- So (F.map ⟨c•1⟩).hom y = c • y for all y
    -- Then α.hom.hom(c • α.inv.hom x) = c • α.hom.hom(α.inv.hom x) = c • x
    change (re (c • (1 : Module.End B₁ B₁))).toFun x = c • x
    -- Unfold re = eB₁.symm.trans (fRing.trans (αRing.trans eB₂))
    -- eB₂ f = f.hom (endRingEquiv), so (re f) x = (αRing(fRing(eB₁.symm f))).hom x
    change (αRing (fRing (eB₁.symm (c • (1 : Module.End B₁ B₁))))).hom x = c • x
    -- Unfold αRing: conjugation by α
    change (α.inv ≫ (fRing (eB₁.symm (c • (1 : Module.End B₁ B₁)))) ≫ α.hom).hom x = c • x
    simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply]
    -- Unfold fRing and eB₁.symm
    change α.hom.hom ((F.functor.map (eB₁.symm (c • (1 : Module.End B₁ B₁)))).hom
      (α.inv.hom x)) = c • x
    -- eB₁.symm f = ⟨f⟩ = ModuleCat.ofHom f, so .hom is identity on the LinearMap
    rw [h1]
    -- F.map(c • 𝟙 X) at .hom level: use Functor.Linear.map_smul via congrArg
    have hF := congrArg ModuleCat.Hom.hom
      (Functor.Linear.map_smul (F := F.functor) (R := k) (𝟙 X) c)
    -- hF : (F.map (c •[Linear] 𝟙 X)).hom = (c •[Linear] F.map (𝟙 X)).hom
    simp only [F.functor.map_id, ModuleCat.hom_smul] at hF
    -- hF should be: (F.map (c • 𝟙 X)).hom = c • (𝟙 FX).hom
    -- Bridge the SMul diamond via element-level Algebra.smul_def normalization.
    -- F.map (c • 𝟙 X) at element level: use map_smul then normalize
    have key := Functor.Linear.map_smul (F := F.functor) (R := k) (𝟙 X) c
    simp only [F.functor.map_id] at key
    -- key : F.map (c •[Linear] 𝟙 X) = c •[?] 𝟙 FX  (with Linear-SMul)
    -- Bridge: c •[instSMulHom] 𝟙 X = c •[Linear] 𝟙 X at element level
    have smul_eq : (c • 𝟙 X : X ⟶ X) = @HSMul.hSMul k (X ⟶ X) (X ⟶ X)
        (@instHSMul k (X ⟶ X) (Linear.homModule X X).toSMul) c (𝟙 X) := by
      apply ModuleCat.hom_ext; apply LinearMap.ext; intro z
      simp only [ModuleCat.hom_smul, LinearMap.smul_apply, ModuleCat.id_apply]
      -- Goal: c •[Algebra.toModule] z = c •[moduleOfAlgebraModule] z
      -- RHS is definitionally algebraMap k B₁ c * z (via Module.compHom)
      -- LHS requires Algebra.smul_def to normalize
      conv_lhs => rw [Algebra.smul_def]
      rfl
    -- Use smul_eq + key to get F.map at element level
    have h_Fmap : ∀ y, (F.functor.map (c • 𝟙 X)).hom y = c • y := by
      intro y
      have h := congrArg F.functor.map smul_eq
      -- h : F.map (c •[instSMulHom] 𝟙 X) = F.map (c •[Linear] 𝟙 X)
      have := congrArg ModuleCat.Hom.hom (h.trans key)
      -- this : (F.map (c •[instSMulHom] 𝟙 X)).hom = (c •[?] 𝟙 FX).hom
      simp only [ModuleCat.hom_smul] at this
      exact LinearMap.congr_fun this y
    rw [h_Fmap]
    -- Goal: α.hom.hom (c • α.inv.hom x) = c • x
    -- α.hom is B₂-linear, c acts via algebraMap
    -- α.hom.hom (c • α.inv.hom x) = c • x
    -- Rewrite c • as algebraMap action, use B₂-linearity of α.hom
    conv_lhs => rw [show c • α.inv.hom x = algebraMap k B₂ c • α.inv.hom x from by
      simp only [algebraMap_smul]]
    rw [map_smul]
    -- Goal: algebraMap k B₂ c • α.hom.hom (α.inv.hom x) = c • x
    conv_rhs => rw [show c • x = algebraMap k B₂ c • x from by
      simp only [Algebra.smul_def, algebraMap_smul]]
    congr 1
    exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom α.inv_hom_id) x)

private lemma basic_morita_algEquiv [IsAlgClosed k]
    (B₁ : Type u) [Ring B₁] [Algebra k B₁] [Module.Finite k B₁]
    (B₂ : Type u) [Ring B₂] [Algebra k B₂] [Module.Finite k B₂]
    (_hB₁ : IsBasicAlgebra k B₁) (_hB₂ : IsBasicAlgebra k B₂)
    (h : KLinearMoritaEquivalent k B₁ B₂) :
    Nonempty (B₁ ≃ₐ[k] B₂) := by
  obtain ⟨F, hlin⟩ := h
  haveI : F.functor.Additive :=
    letI : F.functor.IsEquivalence := F.isEquivalence_functor
    Functor.additive_of_preserves_binary_products F.functor
  haveI := hlin
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
    (h : KLinearMoritaEquivalent k A B) :
    ∃ (e : A) (he : IsIdempotentElem e),
      Nonempty (@AlgEquiv k B (CornerRing (k := k) e) _ _
        (CornerRing.instRing he).toSemiring
        _ (@CornerRing.instAlgebra k _ A _ _ e he)) := by
  -- Step 1: Get a full idempotent e whose corner ring eAe is basic
  obtain ⟨e, he_full, hbasic_corner⟩ := exists_full_idempotent_basic_corner k A
  refine ⟨e, he_full.1, ?_⟩
  -- Step 2: Corner ring eAe is k-linearly Morita equivalent to A
  have hKLinCorner := klinear_morita_equiv_of_full_idempotent (k := k) he_full
  -- Step 3: B and CornerRing e are both basic and k-linearly Morita equivalent
  letI : Ring (CornerRing (k := k) e) := CornerRing.instRing he_full.1
  letI : Algebra k (CornerRing (k := k) e) := CornerRing.instAlgebra he_full.1
  letI : Module.Finite k (CornerRing (k := k) e) := CornerRing.instModuleFinite
  have hKLinBC : KLinearMoritaEquivalent k B (CornerRing (k := k) e) :=
    h.symm'.trans' hKLinCorner
  -- Step 4: Two basic k-linearly Morita equivalent algebras are isomorphic
  have hbasic_corner' : IsBasicAlgebra.{_, _, u} k (CornerRing (k := k) e) :=
    fun M _ _ _ _ _ => hbasic_corner M
  exact basic_morita_algEquiv B (CornerRing (k := k) e) _hB hbasic_corner' hKLinBC

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
