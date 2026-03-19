import EtingofRepresentationTheory.Chapter9.Definition9_6_1
import EtingofRepresentationTheory.Chapter9.Definition9_6_2
import EtingofRepresentationTheory.Chapter9.Definition9_7_1
import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Generator.Preadditive
import Mathlib.CategoryTheory.Abelian.Yoneda
import Mathlib.Algebra.Category.FGModuleCat.Basic

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
`CategoryTheory.preadditiveCoyonedaObj P` in Mathlib. We define a restricted version
`preadditiveCoyonedaObjFG` landing in `FGModuleCat (End P)ᵐᵒᵖ` (finitely generated
modules), since the unrestricted functor into all modules cannot be essentially
surjective. The theorem asserts that this restricted functor is an equivalence when
P is a projective generator in a finite abelian category.
-/

open CategoryTheory CategoryTheory.Limits

/-- **Theorem 9.6.4 (Morita equivalence)**: Let 𝒞 be a finite abelian category
and P a projective generator. Then the functor F(X) = Hom(P, X) gives an
equivalence 𝒞 ≌ (End P)ᵒᵖ-Mod.

In Mathlib, this functor is `preadditiveCoyonedaObj P : C ⥤ ModuleCat (End P)ᵐᵒᵖ`.
(Etingof Theorem 9.6.4) -/
-- A progenerator is a separator: if all maps from P compose to zero,
-- then the map itself is zero (using the epi from a biproduct of copies of P).
theorem Etingof.IsProgenerator.isSeparator {C : Type u} [Category.{v} C]
    [Preadditive C] {P : C} [hp : Etingof.IsProgenerator P] : IsSeparator P := by
  rw [Preadditive.isSeparator_iff]
  intro X Y f hf
  obtain ⟨n, hbp, π, hπ⟩ := hp.epiFromBiproduct X
  have : π ≫ f = 0 := by
    apply @biproduct.hom_ext' _ _ _ _ (fun _ : Fin n => P) hbp
    intro i
    simp only [comp_zero]
    rw [← Category.assoc]
    exact hf _
  exact (cancel_epi π).mp (by rw [this, comp_zero])

-- Faithfulness of Hom(P, -) when P is a progenerator
instance Etingof.IsProgenerator.faithful_preadditiveCoyonedaObj
    {C : Type u} [Category.{v} C] [Preadditive C]
    {P : C} [Etingof.IsProgenerator P] :
    (preadditiveCoyonedaObj P).Faithful :=
  (isSeparator_iff_faithful_preadditiveCoyonedaObj P).mp
    Etingof.IsProgenerator.isSeparator

-- Fullness of Hom(P, -) when P is a projective separator in an abelian category
set_option synthInstance.maxHeartbeats 40000 in
-- IsFiniteAbelianCategory provides Preadditive indirectly; extra heartbeats for Projective resolution
instance Etingof.IsProgenerator.full_preadditiveCoyonedaObj
    {C : Type u} [Category.{v} C]
    [Etingof.IsFiniteAbelianCategory C]
    {P : C} [hp : Etingof.IsProgenerator P] :
    (preadditiveCoyonedaObj P).Full := by
  haveI : Projective P := hp.toProjective
  constructor
  intro X Y f
  obtain ⟨n, hbp, π, hπ⟩ := hp.epiFromBiproduct X
  haveI : HasBiproduct (fun _ : Fin n => P) := hbp
  let F := fun _ : Fin n => P
  -- Linearity lemma: f is End(P)^op-linear, so f(s ≫ g) = s ≫ f(g)
  have hlin : ∀ (s : P ⟶ P) (g : P ⟶ X),
      (f : (P ⟶ X) → (P ⟶ Y)) (s ≫ g) = s ≫ (f : (P ⟶ X) → (P ⟶ Y)) g := by
    intro s g
    have := f.hom.map_smul (MulOpposite.op s) g
    -- this : f.hom (op s • g) = op s • f.hom g
    -- op s • g = s ≫ g (module action of End(P)^op on Hom(P,X))
    exact this
  -- Build h : ⨁ P → Y by applying f to each ι_i ≫ π
  let h : ⨁ F ⟶ Y :=
    biproduct.desc (fun i => (f : (P ⟶ X) → (P ⟶ Y)) (biproduct.ι F i ≫ π))
  -- kernel.ι π ≫ h = 0 using separator + linearity of f
  have h_kernel : kernel.ι π ≫ h = 0 := by
    have hSep := Etingof.IsProgenerator.isSeparator (P := P)
    rw [Preadditive.isSeparator_iff] at hSep
    apply hSep
    intro φ
    rw [← Category.assoc]
    show (φ ≫ kernel.ι π) ≫ h = 0
    change (φ ≫ kernel.ι π) ≫
      biproduct.desc (fun i => (f : (P ⟶ X) → (P ⟶ Y)) (biproduct.ι F i ≫ π)) = 0
    rw [biproduct.desc_eq, Preadditive.comp_sum]
    simp_rw [← Category.assoc _ (biproduct.π _ _), ← hlin]
    -- Now goal is: ∑ j, f((φ ≫ kernel.ι π ≫ π_j) ≫ (ι_j ≫ π)) = 0
    rw [← map_sum f.hom]
    -- Goal: f(∑ j, (φ ≫ kernel.ι π ≫ π_j) ≫ (ι_j ≫ π)) = 0
    -- Factor out common terms from the sum
    simp_rw [Category.assoc]
    -- f(φ ≫ ∑ j, (kernel.ι π ≫ π_j ≫ ι_j ≫ π)) = 0
    -- Goal: f(∑ j, (φ ≫ kernel.ι π ≫ π_j) ≫ (ι_j ≫ π)) = 0
    -- after simp_rw [Category.assoc]:
    -- f(φ ≫ ∑ j, kernel.ι π ≫ π_j ≫ ι_j ≫ π) = 0
    -- But ← Preadditive.comp_sum only pulled out φ.
    -- The sum under f is ∑ x, φ ≫ kernel.ι π ≫ π_x ≫ ι_x ≫ π
    -- Use a direct have for the whole argument
    have key : (∑ x, φ ≫ kernel.ι π ≫ biproduct.π (fun _ : Fin n => P) x ≫
        biproduct.ι F x ≫ π : P ⟶ X) = 0 := by
      rw [← Preadditive.comp_sum, ← Preadditive.comp_sum]
      have : ∑ j : Fin n, biproduct.π F j ≫ biproduct.ι F j ≫ π = π := by
        simp_rw [← Category.assoc]
        rw [← Preadditive.sum_comp, biproduct.total, Category.id_comp]
      rw [this, kernel.condition, comp_zero]
    rw [key, map_zero]
  -- Factor h through π to get g : X → Y with π ≫ g = h
  refine ⟨Abelian.epiDesc π h h_kernel, ?_⟩
  -- Show (preadditiveCoyonedaObj P).map g = f, i.e., ∀ α : P → X, α ≫ g = f(α)
  have hcomp : π ≫ Abelian.epiDesc π h h_kernel = h := Abelian.comp_epiDesc π h h_kernel
  -- Use ModuleCat extensionality
  ext α
  -- α : P → X. Since P is projective, lift α through π
  have hβ : Projective.factorThru α π ≫ π = α := Projective.factorThru_comp α π
  -- (preadditiveCoyonedaObj P).map g sends α to α ≫ g
  -- We show α ≫ g = f(α) by lifting α = β ≫ π
  change α ≫ Abelian.epiDesc π h h_kernel =
    (f : (P ⟶ X) → (P ⟶ Y)) α
  rw [← hβ, Category.assoc, hcomp]
  -- Now: (Projective.factorThru α π) ≫ h = f(Projective.factorThru α π ≫ π)
  change Projective.factorThru α π ≫
    biproduct.desc (fun i => (f : (P ⟶ X) → (P ⟶ Y)) (biproduct.ι F i ≫ π)) = _
  rw [biproduct.desc_eq, Preadditive.comp_sum]
  simp_rw [← Category.assoc _ (biproduct.π _ _), ← hlin]
  rw [← map_sum f.hom]
  simp_rw [Category.assoc]
  rw [← Preadditive.comp_sum]
  have : ∑ j : Fin n, biproduct.π F j ≫ biproduct.ι F j ≫ π = π := by
    simp_rw [← Category.assoc]
    rw [← Preadditive.sum_comp, biproduct.total, Category.id_comp]
  rw [this]

-- Hom(P, X) is finitely generated as an (End P)ᵒᵖ-module when P is a progenerator.
-- Proof: P^n ↠ X gives Hom(P, P^n) ↠ Hom(P, X) (since P is projective), and
-- Hom(P, P^n) ≅ (End P)^n is finitely generated.
instance Etingof.IsProgenerator.finite_hom_module
    {C : Type u} [Category.{v} C]
    [Etingof.IsFiniteAbelianCategory C]
    {P : C} [hp : Etingof.IsProgenerator P] (X : C) :
    Module.Finite (End P)ᵐᵒᵖ (P ⟶ X) := by
  -- From progenerator: get epi π : P^n ↠ X
  obtain ⟨n, hbp, π, hπ⟩ := hp.epiFromBiproduct X
  haveI : HasBiproduct (fun _ : Fin n => P) := hbp
  haveI : Projective P := hp.toProjective
  -- Post-composition with π gives (End P)ᵒᵖ-linear surjection Hom(P, P^n) → Hom(P, X)
  -- This is exactly (preadditiveCoyonedaObj P).map π
  let φ : (P ⟶ biproduct (fun _ : Fin n => P)) →ₗ[(End P)ᵐᵒᵖ] (P ⟶ X) :=
    ((preadditiveCoyonedaObj P).map π).hom
  have hφ_surj : Function.Surjective φ := by
    intro f
    exact ⟨Projective.factorThru f π, Projective.factorThru_comp f π⟩
  -- Source: Hom(P, P^n) ≅ (End P)^n as (End P)ᵒᵖ-module, hence f.g.
  -- We show Module.Finite for the source via the biproduct components
  haveI : Module.Finite (End P)ᵐᵒᵖ (P ⟶ biproduct (fun _ : Fin n => P)) := by
    let F := fun _ : Fin n => P
    -- Construct linear surjection: (Fin n → End P) → (P ⟶ ⨁P) via biproduct.lift
    -- First show End P is f.g. as (End P)ᵒᵖ-module (generated by 𝟙 P)
    haveI : Module.Finite (End P)ᵐᵒᵖ (End P) := by
      constructor
      refine ⟨{𝟙 P}, ?_⟩
      rw [Submodule.eq_top_iff']
      intro f
      have hmem : 𝟙 P ∈ Submodule.span (End P)ᵐᵒᵖ
          (↑({𝟙 P} : Finset _) : Set _) :=
        Submodule.subset_span (by simp)
      have hsmul : MulOpposite.op f • (𝟙 P : End P) = f := by
        show f ≫ 𝟙 P = f; simp
      rw [← hsmul]
      exact Submodule.smul_mem _ _ hmem
    -- Fin n → End P is f.g. by Module.Finite.pi
    haveI : Module.Finite (End P)ᵐᵒᵖ (Fin n → End P) := Module.Finite.pi
    -- Construct the surjection via biproduct.lift
    exact Module.Finite.of_surjective
      ({ toFun := fun f => biproduct.lift (fun i => f i)
         map_add' := fun f g => by
           apply biproduct.hom_ext; intro i
           simp [Preadditive.add_comp, biproduct.lift_π]
         map_smul' := fun s f => by
           apply biproduct.hom_ext; intro i
           simp only [RingHom.id_apply, biproduct.lift_π]
           -- Goal: (s • f) i = (s • biproduct.lift f) ≫ π_i
           -- LHS: s • f i = s.unop ≫ f i
           -- RHS: (s.unop ≫ biproduct.lift f) ≫ π_i
           change s.unop ≫ f i =
             (s.unop ≫ biproduct.lift fun j => f j) ≫ biproduct.π F i
           rw [Category.assoc, biproduct.lift_π] } :
        (Fin n → End P) →ₗ[(End P)ᵐᵒᵖ] (P ⟶ biproduct F))
      (fun g => ⟨fun i => g ≫ biproduct.π F i, by
        apply @biproduct.hom_ext _ _ _ _ F hbp; intro i
        show (biproduct.lift fun j => g ≫ biproduct.π F j) ≫ biproduct.π F i =
             g ≫ biproduct.π F i
        exact biproduct.lift_π _ _⟩)
  exact Module.Finite.of_surjective φ hφ_surj

/-- The restricted Coyoneda functor landing in finitely generated modules.
When P is a progenerator, Hom(P, X) is finitely generated for all X, so the
coyoneda functor factors through `FGModuleCat`. -/
noncomputable def Etingof.IsProgenerator.preadditiveCoyonedaObjFG
    {C : Type u} [Category.{v} C]
    [Etingof.IsFiniteAbelianCategory C]
    {P : C} [hp : Etingof.IsProgenerator P] :
    C ⥤ FGModuleCat.{v} (End P)ᵐᵒᵖ where
  obj X := ⟨(preadditiveCoyonedaObj P).obj X, hp.finite_hom_module X⟩
  map f := InducedCategory.homMk ((preadditiveCoyonedaObj P).map f)
  map_id X := by
    apply InducedCategory.hom_ext
    change (preadditiveCoyonedaObj P).map (𝟙 X) = 𝟙 _
    exact (preadditiveCoyonedaObj P).map_id X
  map_comp f g := by
    apply InducedCategory.hom_ext
    change (preadditiveCoyonedaObj P).map (f ≫ g) =
      (preadditiveCoyonedaObj P).map f ≫ (preadditiveCoyonedaObj P).map g
    exact (preadditiveCoyonedaObj P).map_comp f g

-- Essential surjectivity of Hom(P, -) restricted to finitely generated modules.
-- Given M : FGModuleCat (End P)ᵒᵖ, construct X ∈ C with Hom(P, X) ≅ M.
-- Strategy: M is f.g., so choose a presentation (End P)^m → (End P)^n → M → 0.
-- By fullness, this lifts to P^m → P^n in C; let X = coker. Then Hom(P, X) ≅ M.
instance Etingof.IsProgenerator.essSurj_preadditiveCoyonedaObjFG
    {C : Type u} [Category.{v} C]
    [Etingof.IsFiniteAbelianCategory C]
    {P : C} [hp : Etingof.IsProgenerator P] :
    hp.preadditiveCoyonedaObjFG.EssSurj := by
  constructor
  intro M
  -- M is a finitely generated (End P)ᵒᵖ-module.
  -- Strategy: choose a finite presentation of M:
  --   (End P)^m → (End P)^n → M → 0
  -- Use fullness of Hom(P,-) to lift to maps in C:
  --   P^m → P^n
  -- Set X = coker of P^m → P^n. Then Hom(P, X) ≅ M.
  -- This requires substantial infrastructure that is beyond
  -- what can be done in a single session.
  sorry

/-- **Theorem 9.6.4 (Morita equivalence)**: Let 𝒞 be a finite
abelian category and P a progenerator. Then Hom(P, -) is an equivalence from 𝒞 to
the category of finitely generated (End P)ᵒᵖ-modules. -/
theorem Etingof.Theorem_9_6_4
    {C : Type u} [Category.{v} C]
    [Etingof.IsFiniteAbelianCategory C]
    {P : C} [hp : Etingof.IsProgenerator P] :
    hp.preadditiveCoyonedaObjFG.IsEquivalence where
  essSurj := hp.essSurj_preadditiveCoyonedaObjFG
  faithful :=
    { map_injective := fun {X Y f g} h => by
        have hF := Etingof.IsProgenerator.faithful_preadditiveCoyonedaObj (P := P)
        apply hF.map_injective
        have : (hp.preadditiveCoyonedaObjFG.map f).hom =
               (hp.preadditiveCoyonedaObjFG.map g).hom := congrArg InducedCategory.Hom.hom h
        exact this }
  full :=
    { map_surjective := fun {X Y} f => by
        have hF := Etingof.IsProgenerator.full_preadditiveCoyonedaObj (P := P)
        obtain ⟨g, hg⟩ := hF.map_surjective f.hom
        exact ⟨g, InducedCategory.hom_ext hg⟩ }

/-- **Corollary of Theorem 9.6.4**: Any finite abelian category is equivalent to
finitely generated modules over some ring. If P is a projective generator, then
C ≌ (End P)ᵒᵖ-fgmod. (Etingof Theorem 9.6.4, corollary) -/
theorem Etingof.Theorem_9_6_4_corollary
    (C : Type u) [Category.{v} C]
    [Etingof.IsFiniteAbelianCategory C]
    (P : C) [hp : Etingof.IsProgenerator P] :
    Nonempty (C ≌ FGModuleCat.{v} (End P)ᵐᵒᵖ) := by
  have := @Etingof.Theorem_9_6_4 C _ _ P hp
  exact ⟨hp.preadditiveCoyonedaObjFG.asEquivalence⟩
