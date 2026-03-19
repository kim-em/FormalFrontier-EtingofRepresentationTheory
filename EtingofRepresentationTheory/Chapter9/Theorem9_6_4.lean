import EtingofRepresentationTheory.Chapter9.Definition9_6_1
import EtingofRepresentationTheory.Chapter9.Definition9_6_2
import EtingofRepresentationTheory.Chapter9.Definition9_7_1
import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Generator.Preadditive
import Mathlib.CategoryTheory.Abelian.Yoneda
import Mathlib.Algebra.Category.FGModuleCat.Basic
import Mathlib.RingTheory.Noetherian.Basic

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

noncomputable instance Etingof.IsFiniteAbelianCategory.hasFiniteBiproducts
    {C : Type u} [Category.{v} C] [h : Etingof.IsFiniteAbelianCategory C] :
    HasFiniteBiproducts C := Abelian.hasFiniteBiproducts

private lemma Etingof.unop_mul_eq_comp {C : Type u} [Category.{v} C] {P : C}
    (s r : (End P)ᵐᵒᵖ) : (s * r).unop = s.unop ≫ r.unop := by
  rw [MulOpposite.unop_mul]; rfl

/-- Linear equivalence between the free (End P)ᵒᵖ-module (Fin n → (End P)ᵒᵖ)
and Hom(P, P^n). The forward map sends a tuple v to biproduct.lift (unop ∘ v). -/
private noncomputable def Etingof.freeModuleIsoHom
    {C : Type u} [Category.{v} C] [Preadditive C]
    (P : C) (n : ℕ) [HasBiproduct (fun _ : Fin n => P)] :
    (Fin n → (End P)ᵐᵒᵖ) ≃ₗ[(End P)ᵐᵒᵖ] (P ⟶ ⨁ (fun _ : Fin n => P)) where
  toFun v := biproduct.lift (fun i => (v i).unop)
  invFun g := fun i => MulOpposite.op (g ≫ biproduct.π _ i)
  left_inv v := by ext i; simp [biproduct.lift_π]
  right_inv g := by apply biproduct.hom_ext; intro i; simp [biproduct.lift_π]
  map_add' a b := by
    apply biproduct.hom_ext; intro i
    simp [biproduct.lift_π, MulOpposite.unop_add, Preadditive.add_comp]
  map_smul' s v := by
    apply biproduct.hom_ext; intro i
    simp only [biproduct.lift_π, RingHom.id_apply]
    show (s * v i).unop = (s.unop ≫ biproduct.lift fun j => (v j).unop) ≫ biproduct.π _ i
    rw [Category.assoc, biproduct.lift_π, Etingof.unop_mul_eq_comp]

-- Essential surjectivity of Hom(P, -) restricted to finitely generated modules.
-- Given M : FGModuleCat (End P)ᵒᵖ, construct X ∈ C with Hom(P, X) ≅ M.
-- Strategy: M is f.g., so choose a surjection (End P)^n → M → 0. The kernel is
-- f.g. (End P is Noetherian), giving (End P)^m → (End P)^n → M → 0.
-- By fullness, lift to P^m → P^n in C; let X = coker. Then Hom(P, X) ≅ M.
set_option maxHeartbeats 400000 in
instance Etingof.IsProgenerator.essSurj_preadditiveCoyonedaObjFG
    {C : Type u} [Category.{v} C]
    [Etingof.IsFiniteAbelianCategory C]
    {P : C} [hp : Etingof.IsProgenerator P]
    [IsNoetherianRing (End P)ᵐᵒᵖ] :
    hp.preadditiveCoyonedaObjFG.EssSurj := by
  constructor
  intro M
  -- Abbreviations
  let R := (End P)ᵐᵒᵖ
  haveI : Projective P := hp.toProjective
  -- Step 1: Surjection R^n ↠ M
  haveI : Module.Finite R ↑M.obj := M.property
  obtain ⟨n, φ, hφ⟩ := Module.Finite.exists_fin' R ↑M.obj
  -- Step 2: Kernel is f.g. (End P is Noetherian)
  haveI : Module.Finite R (LinearMap.ker φ) :=
    IsNoetherian.noetherian (LinearMap.ker φ) |>.choose_spec ▸ inferInstance
  obtain ⟨m, ψ, hψ⟩ := Module.Finite.exists_fin' R (LinearMap.ker φ)
  -- Step 3: Compose to get α : R^m → R^n with image = ker φ
  let α : (Fin m → R) →ₗ[R] (Fin n → R) := (LinearMap.ker φ).subtype.comp ψ
  -- Step 4: Transport α through freeModuleIsoHom to get α' on Hom(P, P^k)
  let Fm := fun _ : Fin m => P
  let Fn := fun _ : Fin n => P
  let βm := Etingof.freeModuleIsoHom P m
  let βn := Etingof.freeModuleIsoHom P n
  let α' : (P ⟶ ⨁ Fm) →ₗ[R] (P ⟶ ⨁ Fn) :=
    βn.toLinearMap.comp (α.comp βm.symm.toLinearMap)
  -- Step 5: Lift α' to a morphism f : ⨁ Fm ⟶ ⨁ Fn using fullness
  have hFull := Etingof.IsProgenerator.full_preadditiveCoyonedaObj (P := P)
  -- α' is a module map (P ⟶ ⨁Fm) → (P ⟶ ⨁Fn), i.e. an element of
  -- Hom in ModuleCat. Fullness gives a lift.
  obtain ⟨f, hf⟩ := hFull.map_surjective
    (ModuleCat.ofHom α' : (preadditiveCoyonedaObj P).obj (⨁ Fm) ⟶
      (preadditiveCoyonedaObj P).obj (⨁ Fn))
  -- Step 6: X = cokernel f
  let X := cokernel f
  -- Step 7: Build the isomorphism Hom(P, X) ≅ M
  -- We have:
  --   ε : Hom(P, ⨁Fn) → ↑M.obj  defined as  φ ∘ βn⁻¹  (surjective)
  --   π★ : Hom(P, ⨁Fn) → Hom(P, X) defined as post-composition with cokernel.π
  -- Both have the same kernel, giving Hom(P, X) ≅ ↑M.obj
  let ε : (P ⟶ ⨁ Fn) →ₗ[R] ↑M.obj := φ.comp βn.symm.toLinearMap
  have hε_surj : Function.Surjective ε := by
    intro x; obtain ⟨y, hy⟩ := hφ x
    exact ⟨βn y, by change φ (βn.symm (βn y)) = x; rw [LinearEquiv.symm_apply_apply]; exact hy⟩
  let π_star : (P ⟶ ⨁ Fn) →ₗ[R] (P ⟶ X) :=
    ((preadditiveCoyonedaObj P).map (cokernel.π f)).hom
  have hπ_surj : Function.Surjective π_star := by
    intro g; exact ⟨Projective.factorThru g (cokernel.π f),
      Projective.factorThru_comp g (cokernel.π f)⟩
  -- Key: ker ε = ker π_star
  have hker_eq : LinearMap.ker ε = LinearMap.ker π_star := by
    ext g
    constructor
    · -- ker ε ⊆ ker π_star: if ε(g) = 0 then g ∈ Im(α') so g ≫ cokernel.π = 0
      intro hg
      simp only [LinearMap.mem_ker] at hg ⊢
      -- g ∈ ker ε means φ(βn⁻¹(g)) = 0, i.e. βn⁻¹(g) ∈ ker φ = Im ψ
      have hg_ker : βn.symm g ∈ LinearMap.ker φ := by
        rw [LinearMap.mem_ker]; simp only [FGModuleCat.obj_carrier] at hg; exact hg
      obtain ⟨w, hw⟩ := hψ ⟨βn.symm g, hg_ker⟩
      -- So g = βn(α(w)) = α'(βm(w)) = (F.map f)(βm(w))
      -- α' = F.map f on elements (post-composition with f)
      have hα'_eq : ∀ k, α' k = k ≫ f := by
        intro k
        change α' k = ((preadditiveCoyonedaObj P).map f).hom k
        conv_rhs => rw [hf]; simp [ModuleCat.hom_ofHom]
      have hg_eq : g = α' (βm w) := by
        change g = βn (α (βm.symm (βm w)))
        simp only [LinearEquiv.symm_apply_apply]
        change g = βn ((LinearMap.ker φ).subtype (ψ w))
        rw [hw]; simp [Submodule.coe_subtype, LinearEquiv.apply_symm_apply]
      rw [hg_eq, hα'_eq]
      -- goal: π_star (βm w ≫ f) = 0, i.e., (βm w ≫ f) ≫ cokernel.π f = 0
      change (βm w ≫ f) ≫ cokernel.π f = 0
      rw [Category.assoc, cokernel.condition, comp_zero]
    · -- ker π_star ⊆ ker ε: if g ≫ cokernel.π = 0 then g factors through f
      intro hg
      simp only [LinearMap.mem_ker] at hg ⊢
      -- g ≫ cokernel.π = 0, so g factors through kernel of cokernel.π
      -- In an abelian category, image f = kernel (cokernel.π f)
      -- g ∈ ker(cokernel.π) = image(f), so g = h ≫ f for some h
      -- Actually: g factors through Abelian.image f via the factorization
      have hg_zero : g ≫ cokernel.π f = 0 := hg
      -- g factors through the kernel of cokernel.π
      let g_lift := kernel.lift (cokernel.π f) g hg_zero
      -- kernel of cokernel.π = image of f (abelian category)
      -- Abelian.image.ι f : Abelian.image f ⟶ ⨁Fn
      -- Abelian.factorThruImage f : ⨁Fm ⟶ Abelian.image f  (epi)
      -- kernel.ι (cokernel.π f) = Abelian.image.ι f (up to iso)
      -- Use that imageSubobject = kernel of cokernel.π
      -- Since P is projective: lift g_lift through factorThruImage
      let img_iso := Abelian.imageIsoImage f
      -- img_iso : Abelian.image f ≅ image f (the categorical image)
      -- image.ι f : image f ⟶ ⨁Fn
      -- We need to connect kernel.ι (cokernel.π f) with image
      -- In an abelian category: image f ≅ kernel (cokernel.π f)
      -- Use imageIsoKernelCokernelπ
      -- Actually, let's use a more direct approach:
      -- Abelian.factorThruImage f ≫ Abelian.image.ι f = f
      -- and factorThruImage is epi
      -- P is projective, so lift g_lift through factorThruImage
      -- Actually, kernel.ι (cokernel.π f) factors through Abelian.image.ι f
      -- Let's use: g = g_lift ≫ kernel.ι (cokernel.π f)
      --          = g_lift ≫ ... ≫ image.ι f
      -- Simpler: just note that in abelian categories, f = factorThruImage f ≫ image.ι f
      -- and image.ι f = imageSubobject.arrow = ...
      -- This is getting complex. Let me use the direct characterization:
      -- g ≫ cokernel.π f = 0  implies  g ∈ range of (· ≫ f) as End(P)^op-module maps
      -- i.e., there exists h : P ⟶ ⨁Fm with h ≫ f = g
      -- This follows from: P projective + abelian image factorization
      -- In an abelian category: f = factorThruImage f ≫ image.ι f
      --   factorThruImage f is epi, image.ι f is mono
      --   kernel (cokernel.π f) = image f  (this IS the abelian category axiom)
      -- So kernel.ι (cokernel.π f) factors through image.ι f and vice versa
      -- Using Abelian.image approach:
      -- Abelian.image.ι f = kernel.ι (cokernel.π f) (definitionally in Mathlib!)
      -- So g_lift ≫ kernel.ι (cokernel.π f) = g
      -- means g_lift ≫ Abelian.image.ι f = g  (wrong: different types)
      -- Actually in Mathlib: Abelian.image f is defined as kernel (cokernel.π f)
      -- So Abelian.image.ι f = kernel.ι (cokernel.π f) definitionally
      -- and Abelian.factorThruImage f : ⨁Fm ⟶ Abelian.image f
      -- with Abelian.factorThruImage f ≫ Abelian.image.ι f = f
      -- Since P is projective, lift g_lift : P ⟶ Abelian.image f
      -- through Abelian.factorThruImage f (which is epi)
      let h := Projective.factorThru g_lift (Abelian.factorThruImage f)
      -- h : P ⟶ ⨁Fm with h ≫ Abelian.factorThruImage f = g_lift
      -- So h ≫ f = h ≫ (factorThruImage f ≫ image.ι f)
      --          = g_lift ≫ image.ι f = g_lift ≫ kernel.ι (cokernel.π f) = g
      have hh : h ≫ f = g := by
        have h1 := Projective.factorThru_comp g_lift (Abelian.factorThruImage f)
        have h2 := Abelian.image.fac f
        -- h2 : Abelian.factorThruImage f ≫ Abelian.image.ι f = f
        calc h ≫ f = h ≫ (Abelian.factorThruImage f ≫ Abelian.image.ι f) := by rw [h2]
          _ = (h ≫ Abelian.factorThruImage f) ≫ Abelian.image.ι f := by rw [Category.assoc]
          _ = g_lift ≫ Abelian.image.ι f := by rw [h1]
          _ = g_lift ≫ kernel.ι (cokernel.π f) := rfl
          _ = g := kernel.lift_ι (cokernel.π f) g hg_zero
      -- Now: ε(g) = ε(h ≫ f) = φ(βn⁻¹(α'(βm.symm⁻¹(h))))
      -- Since α = subtype ∘ ψ and ε = φ ∘ βn⁻¹:
      -- ε(h ≫ f) = φ(βn⁻¹(h ≫ f))
      -- h ≫ f = α'(h) (since F.map f = α' by hf)
      -- So βn⁻¹(α'(h)) = α(βm⁻¹(h)) = subtype(ψ(βm⁻¹(h))) ∈ ker φ
      -- Hence φ(βn⁻¹(h ≫ f)) = 0
      rw [← hh]
      -- goal: ε (h ≫ f) = 0, i.e., φ (βn.symm (h ≫ f)) = 0
      change φ (βn.symm (h ≫ f)) = 0
      -- h ≫ f = α' h (since F.map f = ofHom α')
      have hα'_eq : ∀ k, α' k = k ≫ f := by
        intro k
        change α' k = ((preadditiveCoyonedaObj P).map f).hom k
        conv_rhs => rw [hf]; simp [ModuleCat.hom_ofHom]
      rw [← hα'_eq]
      change φ (βn.symm (βn (α (βm.symm h)))) = 0
      rw [LinearEquiv.symm_apply_apply]
      -- α (βm.symm h) = subtype (ψ (βm.symm h)) ∈ ker φ
      exact LinearMap.mem_ker.mp (ψ (βm.symm h)).property
  -- Build the LinearEquiv via quotient kernels
  let iso1 := ε.quotKerEquivOfSurjective hε_surj
  -- iso1 : (P ⟶ ⨁Fn) ⧸ ker ε ≃ₗ[R] ↑M.obj
  let iso2 := Submodule.quotEquivOfEq _ _ hker_eq
  -- iso2 : (P ⟶ ⨁Fn) ⧸ ker ε ≃ₗ[R] (P ⟶ ⨁Fn) ⧸ ker π_star
  let iso3 := π_star.quotKerEquivOfSurjective hπ_surj
  -- iso3 : (P ⟶ ⨁Fn) ⧸ ker π_star ≃ₗ[R] (P ⟶ X)
  -- Full chain: (P ⟶ X) ←(iso3)← quot/ker π_star ←(iso2)← quot/ker ε →(iso1)→ ↑M.obj
  let full_iso : (P ⟶ X) ≃ₗ[R] ↑M.obj := iso3.symm.trans (iso2.symm.trans iso1)
  -- Package as FGModuleCat iso
  -- full_iso : (P ⟶ X) ≃ₗ[R] ↑M.obj
  exact ⟨cokernel f, ⟨{
    hom := InducedCategory.homMk (ModuleCat.ofHom full_iso.toLinearMap)
    inv := InducedCategory.homMk (ModuleCat.ofHom full_iso.symm.toLinearMap)
    hom_inv_id := by apply InducedCategory.hom_ext; ext x; exact full_iso.left_inv x
    inv_hom_id := by apply InducedCategory.hom_ext; ext x; exact full_iso.right_inv x
  }⟩⟩

/-- **Theorem 9.6.4 (Morita equivalence)**: Let 𝒞 be a finite
abelian category and P a progenerator. Then Hom(P, -) is an equivalence from 𝒞 to
the category of finitely generated (End P)ᵒᵖ-modules. -/
theorem Etingof.Theorem_9_6_4
    {C : Type u} [Category.{v} C]
    [Etingof.IsFiniteAbelianCategory C]
    {P : C} [hp : Etingof.IsProgenerator P]
    [IsNoetherianRing (End P)ᵐᵒᵖ] :
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
    (P : C) [hp : Etingof.IsProgenerator P]
    [IsNoetherianRing (End P)ᵐᵒᵖ] :
    Nonempty (C ≌ FGModuleCat.{v} (End P)ᵐᵒᵖ) := by
  have := @Etingof.Theorem_9_6_4 C _ _ P hp _
  exact ⟨hp.preadditiveCoyonedaObjFG.asEquivalence⟩
