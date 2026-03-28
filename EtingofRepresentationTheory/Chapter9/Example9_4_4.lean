import EtingofRepresentationTheory.Chapter9.Definition9_4_3
import EtingofRepresentationTheory.Chapter9.ShapiroLemma
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Descent
import Mathlib.Data.ENat.Lattice
import Mathlib.RingTheory.SimpleModule.InjectiveProjective
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Preadditive.Projective.Preserves
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Module.AEval
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import EtingofRepresentationTheory.Chapter9.KoszulHelpers

/-!
# Example 9.4.4: Homological dimension of polynomial algebra (Hilbert syzygies)

By the Hilbert syzygies theorem, the homological dimension of k[x₁, …, xₙ] is n
(where k is a field).

## Mathlib correspondence

The Hilbert syzygy theorem is not yet in Mathlib.
-/

universe u

open Etingof CategoryTheory Limits

/-- Over a semisimple ring, every module is projective and hence has projective dimension ≤ 0. -/
theorem hasHomologicalDimensionLE_zero_of_isSemisimpleRing
    (R : Type u) [Ring R] [IsSemisimpleRing R] [Small.{u} R] :
    HasHomologicalDimensionLE R 0 := by
  intro M
  have : Module.Projective R M := Module.projective_of_isSemisimpleRing R M
  have : Projective M := M.projective_of_categoryTheory_projective
  infer_instance

section EquivalencePreservesProjectiveDimension

variable {C : Type*} [Category C] [Abelian C] [EnoughProjectives C]
variable {D : Type*} [Category D] [Abelian D]

/-- An equivalence of abelian categories with enough projectives preserves
projective dimension (upper bound). The proof is by induction on n, using
the kernel short exact sequence from a projective presentation. -/
theorem hasProjectiveDimensionLT_of_equivalence (E : C ≌ D) {X : C} :
    ∀ {n : ℕ}, HasProjectiveDimensionLT X n →
      HasProjectiveDimensionLT (E.functor.obj X) n := by
  intro n
  induction n generalizing X with
  | zero =>
    intro h
    exact (E.functor.map_isZero
      (isZero_of_hasProjectiveDimensionLT_zero X)).hasProjectiveDimensionLT_zero
  | succ n ih =>
    intro h
    cases n with
    | zero =>
      have hproj : Projective X := (projective_iff_hasProjectiveDimensionLT_one X).mpr h
      have : Projective (E.functor.obj X) := (E.map_projective_iff X).mpr hproj
      exact (projective_iff_hasProjectiveDimensionLT_one _).mp this
    | succ m =>
      obtain ⟨pp⟩ := EnoughProjectives.presentation X
      let S : ShortComplex C := ShortComplex.mk (kernel.ι pp.f) pp.f (by simp)
      have hSE : S.ShortExact := { exact := ShortComplex.exact_kernel pp.f }
      have hK : HasProjectiveDimensionLT (kernel pp.f) (m + 1) :=
        hSE.hasProjectiveDimensionLT_X₁ (m + 1)
          (hasProjectiveDimensionLT_of_ge pp.p 1 (m + 1) (by omega)) h
      have hEK := ih hK
      have hEP : Projective (E.functor.obj pp.p) := (E.map_projective_iff pp.p).mpr pp.projective
      have hEP_pd : HasProjectiveDimensionLT (E.functor.obj pp.p) (m + 2) :=
        hasProjectiveDimensionLT_of_ge (E.functor.obj pp.p) 1 (m + 2) (by omega)
      exact (hSE.map_of_exact E.functor).hasProjectiveDimensionLT_X₃ (m + 1) hEK hEP_pd

end EquivalencePreservesProjectiveDimension

/-- Ring isomorphisms preserve homological dimension. -/
theorem hasHomologicalDimensionLE_of_ringEquiv {R S : Type u} [Ring R] [Ring S]
    (e : R ≃+* S) (d : ℕ) (h : Etingof.HasHomologicalDimensionLE S d) :
    Etingof.HasHomologicalDimensionLE R d := by
  intro M
  -- restrictScalarsEquivalenceOfRingEquiv e : ModuleCat S ≌ ModuleCat R
  -- functor: ModuleCat S ⥤ ModuleCat R, inverse: ModuleCat R ⥤ ModuleCat S
  let E := ModuleCat.restrictScalarsEquivalenceOfRingEquiv e
  -- E.inverse.obj M : ModuleCat S, has pd ≤ d by hypothesis
  have hN : HasProjectiveDimensionLE (E.inverse.obj M) d := h (E.inverse.obj M)
  -- The equivalence preserves projective dimension: E.functor sends it back to ModuleCat R
  have hFN := hasProjectiveDimensionLT_of_equivalence E hN
  -- E.counitIso.app M : (E.inverse ⋙ E.functor).obj M ≅ (𝟭 _).obj M
  -- which is E.functor.obj (E.inverse.obj M) ≅ M
  exact @hasProjectiveDimensionLT_of_iso _ _ _ _ _ (E.counitIso.app M) (d + 1) hFN

/-- The extension-of-scalars functor `R[X] ⊗_R -` preserves projective dimension.
Since R[X] is free (hence flat) over R, `extendScalars C` is exact and preserves
projective objects, so it preserves `HasProjectiveDimensionLT`. -/
private theorem extendScalars_preservesProjectiveDimensionLT
    {R : Type u} [CommRing R] [Small.{u} R]
    (M : ModuleCat.{u} R) :
    ∀ (n : ℕ), HasProjectiveDimensionLT M n →
    HasProjectiveDimensionLT
      ((ModuleCat.extendScalars.{u, u, u} (Polynomial.C (R := R))).obj M) n := by
  set C := Polynomial.C (R := R)
  set F := ModuleCat.extendScalars.{u, u, u} C
  letI : Small.{u} (Polynomial R) := ⟨⟨Polynomial R, ⟨Equiv.refl _⟩⟩⟩
  have hFlat : C.Flat := by
    change (algebraMap R (Polynomial R)).Flat; rw [RingHom.flat_algebraMap_iff]; infer_instance
  haveI := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hFlat
  haveI := (ModuleCat.extendRestrictScalarsAdj.{u} C).leftAdjoint_preservesColimits
  haveI : F.PreservesHomology := inferInstance
  haveI : F.Additive :=
    Adjunction.left_adjoint_additive (ModuleCat.extendRestrictScalarsAdj.{u} C)
  intro n
  induction n generalizing M with
  | zero =>
    intro h
    exact (F.map_isZero (isZero_of_hasProjectiveDimensionLT_zero M)).hasProjectiveDimensionLT_zero
  | succ n ih =>
    intro h
    cases n with
    | zero =>
      have hproj : Projective M := (projective_iff_hasProjectiveDimensionLT_one M).mpr h
      have : Projective (F.obj M) :=
        Functor.PreservesProjectiveObjects.projective_obj hproj
      exact (projective_iff_hasProjectiveDimensionLT_one _).mp this
    | succ k =>
      obtain ⟨pp⟩ := EnoughProjectives.presentation M
      let SC := ShortComplex.mk (kernel.ι pp.f) pp.f (by simp)
      have hSE : SC.ShortExact := { exact := ShortComplex.exact_kernel pp.f }
      have hK : HasProjectiveDimensionLT (kernel pp.f) (k + 1) :=
        hSE.hasProjectiveDimensionLT_X₁ (k + 1)
          (hasProjectiveDimensionLT_of_ge pp.p 1 (k + 1) (by omega)) h
      have hFK := ih (kernel pp.f) hK
      have hFSE : (SC.map F).ShortExact := hSE.map_of_exact F
      exact hFSE.hasProjectiveDimensionLT_X₃ (k + 1) hFK
        (hasProjectiveDimensionLT_of_ge (F.obj pp.p) 1 (k + 2) (by omega))

/-- The X-action on an R[X]-module M, viewed as an R-linear endomorphism of M|_R.
This sends m ↦ X • m, which is R-linear since C(r) and X commute in R[X]. -/
private noncomputable def xActionAsRLinear {R : Type u} [CommRing R]
    (M : ModuleCat.{u} (Polynomial R)) :
    (ModuleCat.restrictScalars (Polynomial.C (R := R))).obj M ⟶
    (ModuleCat.restrictScalars (Polynomial.C (R := R))).obj M :=
  -- G.obj M has the same carrier as M but with R-module structure via C
  -- We need the R-linear map m ↦ X • m
  -- Use G.map applied to the R[X]-linear map X • 𝟙_M
  (ModuleCat.restrictScalars (Polynomial.C (R := R))).map
    ((Polynomial.X : Polynomial R) • (𝟙 M))

set_option maxHeartbeats 800000 in
/-- The Koszul short exact sequence for an R[X]-module M:
  0 → R[X] ⊗_R M|_R →^d R[X] ⊗_R M|_R →^ε M → 0
where d(p ⊗ m) = Xp ⊗ m - p ⊗ (X·m) and ε(p ⊗ m) = p·m. -/
private theorem koszulSES_shortExact {R : Type u} [CommRing R]
    (M : ModuleCat.{u} (Polynomial R)) :
    let C := Polynomial.C (R := R)
    let F := ModuleCat.extendScalars.{u, u, u} C
    let G := ModuleCat.restrictScalars.{u} C
    let FGM := F.obj (G.obj M)
    let ε := (ModuleCat.extendRestrictScalarsAdj.{u} C).counit.app M
    let d := (Polynomial.X : Polynomial R) • (𝟙 FGM) - F.map (xActionAsRLinear M)
    (ShortComplex.mk d ε (by
      -- d ≫ ε = 0 by counit naturality
      set adj := ModuleCat.extendRestrictScalarsAdj.{u} C
      have nat := adj.counit.naturality ((Polynomial.X : Polynomial R) • 𝟙 M)
      simp only [Functor.comp_map, Functor.id_map] at nat
      -- d ≫ ε = 0 by counit naturality:
      -- d = X•𝟙 - F(G(X•𝟙_M)), and by naturality of counit,
      -- F(G(X•𝟙_M)) ≫ ε = ε ≫ X•𝟙_M = X•ε, so d ≫ ε = X•ε - X•ε = 0
      show d ≫ adj.counit.app M = 0
      show (Polynomial.X • 𝟙 FGM - F.map (xActionAsRLinear M)) ≫ adj.counit.app M = 0
      rw [Preadditive.sub_comp, Linear.smul_comp, Category.id_comp,
        show F.map (xActionAsRLinear M) = F.map (G.map (Polynomial.X • 𝟙 M)) from rfl,
        nat, Linear.comp_smul]
      erw [Category.comp_id]; exact sub_self _
      )).ShortExact := by
  set C := Polynomial.C (R := R) with C_def
  set F := ModuleCat.extendScalars.{u, u, u} C with F_def
  set G := ModuleCat.restrictScalars.{u} C with G_def
  set FGM := F.obj (G.obj M) with FGM_def
  set adj := ModuleCat.extendRestrictScalarsAdj.{u} C
  set ε := adj.counit.app M
  set d := (Polynomial.X : Polynomial R) • (𝟙 FGM) - F.map (xActionAsRLinear M)
  set N := (G.obj M : Type u)
  intro C' F' G' FGM' ε' d'
  -- Prove mono (injectivity of d')
  haveI : Mono d' := by
    rw [ModuleCat.mono_iff_injective, ← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro t ht
    have hdt : d'.hom t = 0 := LinearMap.mem_ker.mp ht
    -- Use coordinate map injectivity: suffices to show coordMapCH t = 0
    suffices h : coordMapCH N t = 0 from coordMapCH_injective N h
    -- Show coordinates satisfy the shift relation f(k) = xAct(f(k+1))
    set f := coordMapCH N t with f_def
    apply finsupp_shift_eq_zero (xActionAsRLinear M).hom (map_zero (xActionAsRLinear M).hom) f
    intro k
    -- From d'(t) = 0, extract the shift relation at each coordinate
    -- coordMapCH(d'(t))(k+1) = f(k) - xAct(f(k+1)) for ALL t, not just kernel elements
    -- So d'(t) = 0 implies f(k) = xAct(f(k+1))
    have hshift_gen : ∀ (s : ↑FGM'),
        (coordMapCH N (d'.hom s)) (k + 1) =
        (coordMapCH N s) k - (xActionAsRLinear M).hom ((coordMapCH N s) (k + 1)) := by
      intro s
      refine TensorProduct.induction_on s ?_ ?_ ?_
      · simp [map_zero]
      · intro p m
        -- d'.hom decomposes: (X • 𝟙 - F.map xAct).hom = X • id - F.map(xAct).hom
        have hd_sub : d'.hom (p ⊗ₜ[R] m) =
            ((Polynomial.X : Polynomial R) • 𝟙 FGM').hom (p ⊗ₜ[R] m) -
            (F'.map (xActionAsRLinear M)).hom (p ⊗ₜ[R] m) := by
          show (((Polynomial.X : Polynomial R) • 𝟙 FGM' -
            F'.map (xActionAsRLinear M)).hom) (p ⊗ₜ[R] m) = _
          exact LinearMap.sub_apply _ _ _
        -- Reduce each morphism application to a pure tensor (definitional)
        have h_smul : (ModuleCat.Hom.hom ((Polynomial.X : Polynomial R) • 𝟙 FGM'))
            (p ⊗ₜ[R] m) = ((Polynomial.X : Polynomial R) • p) ⊗ₜ[R] m := rfl
        have h_map : (ModuleCat.Hom.hom (F'.map (xActionAsRLinear M)))
            (p ⊗ₜ[R] m) = p ⊗ₜ[R] ((xActionAsRLinear M).hom m) := rfl
        rw [hd_sub, map_sub, h_smul, h_map]
        simp only [coordMapCH, TensorProduct.lift.tmul, LinearMap.coe_mk,
          AddHom.coe_mk, Finsupp.mapRange_apply, Finsupp.sub_apply]
        -- Goal: (X • p).toFinsupp(k+1) • m - p.toFinsupp(k+1) • xAct(m)
        --     = p.toFinsupp(k) • m - xAct(p.toFinsupp(k+1) • m)
        congr 1
        · -- (X • p).toFinsupp(k+1) = p.toFinsupp(k) by coeff_X_mul
          congr 1
          exact Polynomial.coeff_X_mul (show Polynomial R from p) k
        · -- xAct(r • m) = r • xAct(m) by map_smul
          exact (map_smul (xActionAsRLinear M).hom _ _).symm
      · intro s₁ s₂ ih₁ ih₂
        simp only [map_add, Finsupp.add_apply] at ih₁ ih₂ ⊢
        simp only [ih₁, ih₂]; abel
    have h1 := hshift_gen t
    simp only [hdt, map_zero, Finsupp.zero_apply] at h1
    -- h1 : 0 = f k - xAct(f(k+1))
    exact sub_eq_zero.mp h1.symm
  -- Prove epi (surjectivity of ε')
  haveI : Epi ε' := by
    rw [ModuleCat.epi_iff_surjective]
    intro m
    refine ⟨(1 : Polynomial R) ⊗ₜ[R] (m : (G'.obj M : Type u)), ?_⟩
    erw [ModuleCat.ExtendRestrictScalarsAdj.Counit.map_hom_apply]
    simp [TensorProduct.lift.tmul, one_smul]
  -- Prove exactness: ker(ε') ⊆ im(d')
  -- Use coordinate bijection: coordMapCH is a bijection FGM' ≃ (ℕ →₀ N)
  -- coordMapCH(d'(s))(k+1) = coordMapCH(s)(k) - xAct(coordMapCH(s)(k+1))  [shift]
  -- Given f = coordMapCH(x₂), construct g with g(k) - xAct(g(k+1)) = f(k+1)
  -- and -xAct(g(0)) = f(0) (from ε(x₂)=0)
  -- Then s = coordMapCHInv(g) is the preimage
  constructor
  rw [ShortComplex.moduleCat_exact_iff]
  intro x₂ hx₂
  set xAct := (xActionAsRLinear M).hom with xAct_def
  set f := coordMapCH N x₂ with f_def
  -- The shift relation (already proved for mono, reuse the same structure)
  have hshift_gen : ∀ (s : ↑FGM') (k : ℕ),
      (coordMapCH N (d'.hom s)) (k + 1) =
      (coordMapCH N s) k - xAct ((coordMapCH N s) (k + 1)) := by
    intro s k
    refine TensorProduct.induction_on s ?_ ?_ ?_
    · simp [map_zero]
    · intro p m
      have hd_sub : d'.hom (p ⊗ₜ[R] m) =
          ((Polynomial.X : Polynomial R) • 𝟙 FGM').hom (p ⊗ₜ[R] m) -
          (F'.map (xActionAsRLinear M)).hom (p ⊗ₜ[R] m) := by
        show (((Polynomial.X : Polynomial R) • 𝟙 FGM' -
          F'.map (xActionAsRLinear M)).hom) (p ⊗ₜ[R] m) = _
        exact LinearMap.sub_apply _ _ _
      have h_smul : (ModuleCat.Hom.hom ((Polynomial.X : Polynomial R) • 𝟙 FGM'))
          (p ⊗ₜ[R] m) = ((Polynomial.X : Polynomial R) • p) ⊗ₜ[R] m := rfl
      have h_map : (ModuleCat.Hom.hom (F'.map (xActionAsRLinear M)))
          (p ⊗ₜ[R] m) = p ⊗ₜ[R] (xAct m) := rfl
      rw [hd_sub, map_sub, h_smul, h_map]
      simp only [coordMapCH, TensorProduct.lift.tmul, LinearMap.coe_mk,
        AddHom.coe_mk, Finsupp.mapRange_apply, Finsupp.sub_apply]
      congr 1
      · congr 1
        exact Polynomial.coeff_X_mul (show Polynomial R from p) k
      · exact (map_smul xAct _ _).symm
    · intro s₁ s₂ ih₁ ih₂
      simp only [map_add, Finsupp.add_apply] at ih₁ ih₂ ⊢
      simp only [ih₁, ih₂]; abel
  -- Index-0 relation: coordMapCH(d'(s))(0) = -xAct(coordMapCH(s)(0))
  have hshift_zero : ∀ (s : ↑FGM'),
      (coordMapCH N (d'.hom s)) 0 = -xAct ((coordMapCH N s) 0) := by
    intro s
    refine TensorProduct.induction_on s ?_ ?_ ?_
    · simp [map_zero]
    · intro p m
      have hd_sub : d'.hom (p ⊗ₜ[R] m) =
          ((Polynomial.X : Polynomial R) • 𝟙 FGM').hom (p ⊗ₜ[R] m) -
          (F'.map (xActionAsRLinear M)).hom (p ⊗ₜ[R] m) := by
        show (((Polynomial.X : Polynomial R) • 𝟙 FGM' -
          F'.map (xActionAsRLinear M)).hom) (p ⊗ₜ[R] m) = _
        exact LinearMap.sub_apply _ _ _
      have h_smul : (ModuleCat.Hom.hom ((Polynomial.X : Polynomial R) • 𝟙 FGM'))
          (p ⊗ₜ[R] m) = ((Polynomial.X : Polynomial R) • p) ⊗ₜ[R] m := rfl
      have h_map : (ModuleCat.Hom.hom (F'.map (xActionAsRLinear M)))
          (p ⊗ₜ[R] m) = p ⊗ₜ[R] (xAct m) := rfl
      rw [hd_sub, map_sub, h_smul, h_map]
      simp only [coordMapCH, TensorProduct.lift.tmul, LinearMap.coe_mk,
        AddHom.coe_mk, Finsupp.mapRange_apply, Finsupp.sub_apply]
      -- LHS: (X • p).toFinsupp 0 • m - p.toFinsupp 0 • xAct(m)
      -- (X • p).toFinsupp 0 = coeff(X * p, 0) = 0
      have h_zero : ((Polynomial.X : Polynomial R) • (p : _)).toFinsupp 0 = 0 := by
        show Polynomial.coeff ((Polynomial.X : Polynomial R) * (show Polynomial R from p)) 0 = _
        exact Polynomial.coeff_X_mul_zero _
      rw [h_zero, zero_smul, zero_sub, neg_inj]
      exact (map_smul xAct _ _).symm
    · intro s₁ s₂ ih₁ ih₂
      simp only [map_add, Finsupp.add_apply, map_add, neg_add] at ih₁ ih₂ ⊢
      rw [ih₁, ih₂]
  -- Construct g: g(k) = Σ_{j≥0} xAct^j(f(k+1+j)), a finite sum since f has finite support
  -- This satisfies g(k) = f(k+1) + xAct(g(k+1))
  -- Define the underlying function
  set B := if h : f.support.Nonempty then f.support.max' h + 1 else 0 with B_def
  -- g_fun k = Σ_{j=0}^{B} xAct^j (f(k+1+j))
  set g_fun : ℕ → N := fun k =>
    (Finset.range (B + 1)).sum (fun j => (xAct ^ j) (f (k + 1 + j))) with g_fun_def
  -- g_fun is zero for k ≥ B (since f(k+1+j) = 0 for all j when k+1 > max support)
  have g_fun_zero : ∀ k, B ≤ k → g_fun k = 0 := by
    intro k hk
    simp only [g_fun_def]
    apply Finset.sum_eq_zero
    intro j _
    have : f (k + 1 + j) = 0 := by
      by_contra hmem_ne
      have hmem := Finsupp.mem_support_iff.mpr hmem_ne
      simp only [B_def] at hk
      split_ifs at hk with h
      · exact Nat.not_succ_le_self (f.support.max' h)
          (le_trans (Nat.succ_le_of_lt (by omega))
            (Finset.le_max' _ _ hmem))
      · exact h ⟨_, hmem⟩
    rw [this, map_zero]
  -- Build g as a Finsupp
  set g := Finsupp.onFinset (Finset.range B) g_fun (fun k hk => by
    simp only [Finset.mem_range]
    by_contra h
    push_neg at h
    exact hk (g_fun_zero k h)) with g_def
  -- g satisfies the recurrence: g(k) = f(k+1) + xAct(g(k+1))
  have g_rec : ∀ k, g k = f (k + 1) + xAct (g (k + 1)) := by
    intro k
    show g_fun k = f (k + 1) + xAct (g_fun (k + 1))
    simp only [g_fun_def]
    -- Split off j=0 from the sum, then shift index
    -- g(k) = Σ_{j ∈ range(B+1)} xAct^j(f(k+1+j))
    -- We show this equals f(k+1) + xAct(g(k+1))
    -- = f(k+1) + xAct(Σ_{j ∈ range(B+1)} xAct^j(f(k+2+j)))
    -- = f(k+1) + Σ_{j ∈ range(B+1)} xAct^{j+1}(f(k+2+j))
    -- = f(k+1) + Σ_{j ∈ range(B+1)} xAct^{j+1}(f(k+1+(j+1)))
    -- Strategy: show g(k) = f(k+1) + Σ_{j ∈ range B} xAct^{j+1}(f(k+1+(j+1)))
    --           and xAct(g(k+1)) = Σ_{j ∈ range B} xAct^{j+1}(f(k+1+(j+1)))
    -- because the j=B term in the xAct sum is xAct^{B+1}(f(k+2+B)) = xAct^{B+1}(0) = 0
    rw [Finset.sum_range_succ' (fun j => (xAct ^ j) (f (k + 1 + j)))]
    have h0 : (xAct ^ 0) (f (k + 1 + 0)) = f (k + 1) := by simp [pow_zero]
    rw [h0, add_comm]
    congr 1
    -- LHS: Σ_{j ∈ range B} xAct^{j+1}(f(k+1+(j+1)))
    -- RHS: xAct(Σ_{j ∈ range(B+1)} xAct^j(f(k+2+j)))
    -- First peel off the last term of the RHS sum
    rw [map_sum, Finset.sum_range_succ]
    -- Now RHS = Σ_{j ∈ range B} xAct(xAct^j(f(k+2+j))) + xAct(xAct^B(f(k+2+B)))
    -- The last term is 0
    have hB_zero : xAct ((xAct ^ B) (f (k + 2 + B))) = 0 := by
      have : f (k + 2 + B) = 0 := by
        by_contra hmem_ne
        have hmem := Finsupp.mem_support_iff.mpr hmem_ne
        have hB_bound : ∀ n ∈ f.support, n < B := by
          intro n hn
          simp only [B_def]
          split_ifs with h
          · exact Nat.lt_succ_of_le (Finset.le_max' _ _ hn)
          · exact absurd ⟨n, hn⟩ h
        exact absurd (hB_bound _ hmem) (by omega)
      rw [this, map_zero, map_zero]
    rw [hB_zero, add_zero]
    apply Finset.sum_congr rfl
    intro j _
    have h1 : k + 1 + (j + 1) = k + 2 + j := by omega
    have h2 : k + 1 + 1 + j = k + 2 + j := by omega
    rw [h1, h2, pow_succ' xAct j]; rfl
  -- Now show d'(coordMapCHInv(g)) = x₂
  -- It suffices to show coordMapCH(d'(coordMapCHInv(g))) = coordMapCH(x₂) = f
  refine ⟨coordMapCHInv N g, ?_⟩
  apply coordMapCH_injective N
  -- Show coordMapCH(d'(coordMapCHInv(g))) = f pointwise
  ext k
  -- Use right inverse: coordMapCH(coordMapCHInv(g)) = g
  have hg_coord : coordMapCH N (coordMapCHInv N (R := R) g) = g :=
    coordMapCH_rightInverse (R := R) N g
  cases k with
  | zero =>
    -- At index 0: coordMapCH(d'(s))(0) = -xAct(coordMapCH(s)(0))
    rw [hshift_zero]
    rw [show coordMapCH N (coordMapCHInv N g) = g from hg_coord]
    -- Need: -xAct(g 0) = f 0
    -- Use finsupp_eval_sum + counit identity + hx₂
    -- Step 1: x₂ = coordMapCHInv(f) by left inverse
    have hx₂_eq : x₂ = coordMapCHInv N (R := R) f :=
      (coordMapCH_leftInverse (R := R) N x₂).symm
    rw [hx₂_eq] at hx₂
    -- Step 2: X^k • m = xAct^k(m)
    have hXpow : ∀ (k : ℕ) (m : (G'.obj M : Type u)),
        ((Polynomial.X : Polynomial R) ^ k) • m = (xAct ^ k) m := by
      intro k; induction k with
      | zero => intro m; simp [pow_zero, one_smul]
      | succ k ih =>
        intro m; rw [pow_succ, mul_smul, ih, pow_succ xAct k]
        -- Goal: (xAct^k)(X • m) = (xAct^k * xAct)(m) = (xAct^k)(xAct(m))
        -- Since xAct(m) = X • m definitionally, both sides are (xAct^k)(xAct(m))
        rfl
    -- Step 3: ε'(coordMapCHInv(f)) = f.sum(xAct^k)
    have hcounit_inv : ε'.hom (coordMapCHInv N (R := R) f) =
        f.sum (fun k m => (xAct ^ k) m) := by
      simp only [coordMapCHInv, LinearMap.coe_mk, AddHom.coe_mk, Finsupp.sum]
      rw [map_sum]
      apply Finset.sum_congr rfl; intro k _
      erw [ModuleCat.ExtendRestrictScalarsAdj.Counit.map_hom_apply]
      simp only [TensorProduct.lift.tmul, LinearMap.coe_mk, AddHom.coe_mk]
      exact hXpow k (f k)
    -- Step 4: f.sum(xAct^k) = 0
    have hsum_zero : f.sum (fun k m => (xAct ^ k) m) = 0 := by
      rw [← hcounit_inv]; exact hx₂
    -- Step 5: f 0 + xAct(g 0) = f.sum(xAct^k) via finsupp_eval_sum
    have hB_bound : ∀ n ∈ f.support, n < B := by
      intro n hn; simp only [B_def]
      split_ifs with h
      · exact Nat.lt_succ_of_le (Finset.le_max' _ _ hn)
      · exact absurd ⟨n, hn⟩ h
    rw [neg_eq_iff_eq_neg, eq_neg_iff_add_eq_zero, add_comm, ← f_def]
    show f 0 + xAct (g_fun 0) = 0
    rw [show xAct (g_fun 0) = xAct ((Finset.range (B + 1)).sum
        (fun j => (xAct ^ j) (f (0 + 1 + j)))) from rfl]
    rw [finsupp_eval_sum xAct f B hB_bound]
    exact hsum_zero
  | succ k =>
    -- At index k+1: coordMapCH(d'(s))(k+1) = coordMapCH(s)(k) - xAct(coordMapCH(s)(k+1))
    rw [hshift_gen]
    rw [show coordMapCH N (coordMapCHInv N g) = g from hg_coord]
    -- Need: g(k) - xAct(g(k+1)) = f(k+1)
    rw [g_rec k]
    abel

theorem hasHomologicalDimensionLE_polynomial {R : Type u} [CommRing R] [Small.{u} R] (d : ℕ)
    (h : Etingof.HasHomologicalDimensionLE R d) :
    Etingof.HasHomologicalDimensionLE (Polynomial R) (d + 1) := by
  letI : Small.{u} (Polynomial R) := ⟨⟨Polynomial R, ⟨Equiv.refl _⟩⟩⟩
  set C := Polynomial.C (R := R)
  set F := ModuleCat.extendScalars.{u, u, u} C
  set G := ModuleCat.restrictScalars.{u} C
  intro M
  -- The Koszul SES: 0 → F(G(M)) →^d F(G(M)) →^ε M → 0
  have hSES := koszulSES_shortExact M
  -- pd_{R[X]}(F(G(M))) ≤ d
  have hFGM_pd : HasProjectiveDimensionLE (F.obj (G.obj M)) d := by
    exact extendScalars_preservesProjectiveDimensionLT (G.obj M) (d + 1) (h (G.obj M))
  -- Apply dimension shifting: pd(M) ≤ d+1
  -- hasProjectiveDimensionLT_X₃ n : pd(X₁) < n → pd(X₂) < n+1 → pd(X₃) < n+1
  -- Here n = d+1, X₁ = X₂ = F(G(M)) with pd ≤ d, i.e., pd < d+1
  exact hSES.hasProjectiveDimensionLT_X₃ (d + 1) hFGM_pd
    (hasProjectiveDimensionLT_of_ge _ (d + 1) (d + 2) (by omega))

/-- The Hilbert syzygy theorem (upper bound): every module over k[x₁, …, xₙ] has
projective dimension ≤ n.

This is the hard direction of the Hilbert syzygy theorem. The proof uses the Koszul
resolution or induction on n via the change-of-rings spectral sequence. Neither
the Koszul complex nor the polynomial ring global dimension theorem is currently
in Mathlib. -/
private instance isSemisimpleRing_mvPolynomial_fin_zero (k : Type u) [Field k] :
    IsSemisimpleRing (MvPolynomial (Fin 0) k) :=
  (MvPolynomial.isEmptyAlgEquiv k (Fin 0)).symm.toRingEquiv.isSemisimpleRing

theorem mvPolynomial_hasHomologicalDimensionLE (k : Type u) [Field k] :
    ∀ n, HasHomologicalDimensionLE (MvPolynomial (Fin n) k) n
  | 0 => hasHomologicalDimensionLE_zero_of_isSemisimpleRing _
  | n + 1 => by
    -- By induction, MvPolynomial (Fin n) k has homological dimension ≤ n
    have ih := mvPolynomial_hasHomologicalDimensionLE k n
    -- MvPolynomial (Fin (n+1)) k ≃ₐ Polynomial (MvPolynomial (Fin n) k)
    have e := (MvPolynomial.finSuccEquiv k n).toRingEquiv
    -- By the polynomial extension theorem, Polynomial (MvPolynomial (Fin n) k)
    -- has homological dimension ≤ n + 1
    have h_poly := hasHomologicalDimensionLE_polynomial n ih
    -- Transfer across the ring isomorphism
    exact hasHomologicalDimensionLE_of_ringEquiv e (n + 1) h_poly

section PolynomialLowerBound

open Polynomial

/-! ### Polynomial ring has positive global dimension

For a nontrivial commutative ring R, the polynomial ring R[x] is not semisimple.
The key argument: the augmentation module R (where x acts as 0) is not projective
over R[x], because any R[x]-linear section of the evaluation-at-0 map would be
killed by x (since x acts as 0 on R), hence zero, contradicting surjectivity. -/

/-- In Polynomial R, multiplication by X is injective (for any ring R). -/
private theorem Polynomial.X_mul_eq_zero {R : Type u} [CommRing R] {p : R[X]} (h : X * p = 0) :
    p = 0 := by
  ext n
  have h1 := congr_arg (Polynomial.coeff · (n + 1)) h
  simp only [coeff_X_mul, coeff_zero] at h1
  exact h1

/-- The polynomial ring over a nontrivial commutative ring has global dimension ≥ 1.
Equivalently, it is not semisimple: the augmentation module is not projective. -/
private theorem not_hasHomologicalDimensionLE_zero_polynomial
    (R : Type u) [CommRing R] [Nontrivial R] :
    ¬ Etingof.HasHomologicalDimensionLE (Polynomial R) 0 := by
  intro hall
  -- The augmentation module: R with R[X]-action where X acts as 0
  let φ : R →ₗ[R] R := 0
  let A := Module.AEval' φ
  let MA := ModuleCat.of (Polynomial R) A
  -- Every R[X]-module has pd ≤ 0, so MA is projective
  have hpd : HasProjectiveDimensionLE MA 0 := hall MA
  have hproj : Projective MA :=
    (projective_iff_hasProjectiveDimensionLT_one MA).mpr hpd
  have hmod : Module.Projective (Polynomial R) A :=
    MA.projective_of_module_projective
  -- The surjection: R[X] → A sending p ↦ p • 1_A
  let one_A : A := Module.AEval'.of φ (1 : R)
  let surj := LinearMap.toSpanSingleton (Polynomial R) A one_A
  have hsurj : Function.Surjective surj := by
    intro a
    refine ⟨Polynomial.C ((Module.AEval'.of φ).symm a), ?_⟩
    simp only [surj, LinearMap.toSpanSingleton_apply]
    rw [Module.AEval.C_smul,
      ← (Module.AEval'.of φ).map_smul, smul_eq_mul, mul_one,
      LinearEquiv.apply_symm_apply]
  -- Get section from projectivity
  obtain ⟨sect, hsect⟩ :=
    Module.projective_lifting_property surj LinearMap.id hsurj
  -- Show sect = 0: X • a = 0 in A (since X acts as 0),
  -- so X * sect(a) = sect(X • a) = 0
  have X_smul_zero : ∀ a : A, (X : R[X]) • a = 0 := by
    intro a
    rw [show a = Module.AEval'.of φ ((Module.AEval'.of φ).symm a) from
      ((Module.AEval'.of φ).apply_symm_apply a).symm,
      Module.AEval'.X_smul_of, LinearMap.zero_apply, map_zero]
  have hzero : ∀ a : A, sect a = 0 := by
    intro a
    apply Polynomial.X_mul_eq_zero
    calc X * sect a
        = sect ((X : R[X]) • a) := (sect.map_smul (X : R[X]) a).symm
      _ = sect 0 := by rw [X_smul_zero]
      _ = 0 := map_zero sect
  -- surj ∘ sect = id, but sect = 0 means every a = 0
  have hall_zero : ∀ a : A, a = 0 := by
    intro a
    have h := LinearMap.ext_iff.mp hsect a
    simp only [LinearMap.comp_apply, LinearMap.id_apply, hzero a,
      map_zero] at h
    exact h.symm
  -- But A ≅ R as additive groups, and R is nontrivial
  have : one_A ≠ 0 := by
    intro h
    exact one_ne_zero ((Module.AEval'.of φ).injective
      (h.trans (map_zero (Module.AEval'.of φ)).symm))
  exact this (hall_zero one_A)

/-- `Polynomial.divX` is a left inverse of X-multiplication on R[X]. -/
private theorem Polynomial.divX_X_mul (R : Type u) [CommRing R] (p : R[X]) :
    Polynomial.divX (X * p) = p := by
  ext n
  simp [coeff_divX, coeff_X_mul]

/-- X-multiplication on R[X] ⊗_R M is injective: X· has a left inverse (divX ⊗ id),
since divX is a left inverse of X· on R[X] as an R-linear map. -/
private theorem polynomial_X_mul_mono_extendScalars (R : Type u) [CommRing R]
    (M : ModuleCat.{u} R) :
    Mono ((Polynomial.X : Polynomial R) •
      (𝟙 ((ModuleCat.extendScalars.{u, u, u} (Polynomial.C (R := R))).obj M))) := by
  rw [ModuleCat.mono_iff_injective]
  set FM := (ModuleCat.extendScalars.{u, u, u} (Polynomial.C (R := R))).obj M
  -- X • 𝟙_FM sends p ⊗ m ↦ (X*p) ⊗ m on FM = R[X] ⊗[R] M.
  -- divX ⊗ id is a left inverse since divX(X*p) = p.
  -- We construct the left inverse via TensorProduct.lift.
  set C := Polynomial.C (R := R)
  let S' := (ModuleCat.restrictScalars C).obj (ModuleCat.of (Polynomial R) (Polynomial R))
  -- divX ⊗ id as a bilinear map
  -- divX(C(r) * q) = C(r) * divX(q) for q : R[X], cast to S'
  have divX_C_mul : ∀ (r : R) (q : Polynomial R),
      Polynomial.divX (Polynomial.C r * q) = Polynomial.C r * Polynomial.divX q := by
    intro r q; apply Polynomial.ext; intro n
    simp [Polynomial.coeff_divX, Polynomial.coeff_C_mul]
  let g : TensorProduct R (S' : Type u) (M : Type u) →ₗ[R]
      TensorProduct R (S' : Type u) (M : Type u) :=
    TensorProduct.lift
      { toFun := fun (p : (S' : Type u)) =>
          { toFun := fun (m : (M : Type u)) =>
              (Polynomial.divX (p : Polynomial R) : (S' : Type u)) ⊗ₜ[R] m
            map_add' := fun _ _ => TensorProduct.tmul_add _ _ _
            map_smul' := fun r m => by
              simp only [RingHom.id_apply]; exact TensorProduct.tmul_smul r _ m }
        map_add' := fun p q => by
          ext m; simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply]
          rw [Polynomial.divX_add]; exact (TensorProduct.add_tmul _ _ m)
        map_smul' := fun r p => by
          ext m
          simp only [RingHom.id_apply, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply]
          rw [TensorProduct.smul_tmul']
          congr 1
          exact divX_C_mul r p }
  have hli : Function.LeftInverse g
      (ConcreteCategory.hom ((Polynomial.X : Polynomial R) • 𝟙 FM)) := by
    intro t
    refine TensorProduct.induction_on t ?_ ?_ ?_
    · simp
    · intro p m
      change g ((Polynomial.X : Polynomial R) • (p ⊗ₜ[R] m)) = p ⊗ₜ m
      rw [ModuleCat.ExtendScalars.smul_tmul]
      simp only [g, TensorProduct.lift.tmul, LinearMap.coe_mk, AddHom.coe_mk]
      congr 1
      exact Polynomial.divX_X_mul R p
    · intro x y hx hy
      simp only [map_add, hx, hy]
  exact hli.injective

/-- The short exact sequence 0 → F(M) →^{X·} F(M) → coker(X·) → 0 in ModuleCat R[X].
This is the key SES for the polynomial extension dimension theory. -/
private noncomputable def polynomialExtensionSES (R : Type u) [CommRing R]
    (M : ModuleCat.{u} R) :
    let FM := (ModuleCat.extendScalars.{u, u, u} (Polynomial.C (R := R))).obj M
    let f : FM ⟶ FM := (Polynomial.X : Polynomial R) • (𝟙 FM)
    (ShortComplex.mk f (cokernel.π f) (cokernel.condition f)).ShortExact where
  exact := ShortComplex.exact_cokernel _
  mono_f := polynomial_X_mul_mono_extendScalars R M
  epi_g := inferInstance

/-- Core vanishing lemma: In ModuleCat R[X], given a short exact sequence
0 → A →^{X·𝟙} A → Q → 0 and an R[X]-module Y with X · 𝟙_Y = 0,
if Ext^{n+1}(Q, Y) vanishes then Ext^n(A, Y) vanishes.

The proof uses the contravariant LES of Ext:
1. The connecting map δ sends Ext^n(A,Y) to Ext^{n+1}(Q,Y) = 0
2. By exactness, every element lifts through precomposition with X·𝟙
3. Precomp with X·𝟙 equals X-scalar multiplication on Ext (by mk₀_smul + smul_comp + mk₀_id_comp)
4. X-scalar multiplication is zero by smul_eq_comp_mk₀ + hY -/
private theorem ext_eq_zero_of_X_action_vanishing
    {R : Type u} [CommRing R]
    {A : ModuleCat.{u} (Polynomial R)} {Y : ModuleCat.{u} (Polynomial R)}
    (hY : (Polynomial.X : Polynomial R) • (𝟙 Y) = (0 : Y ⟶ Y))
    {Q : ModuleCat.{u} (Polynomial R)} {g : A ⟶ Q}
    {w : ((Polynomial.X : Polynomial R) • (𝟙 A)) ≫ g = 0}
    (hSES : (ShortComplex.mk ((Polynomial.X : Polynomial R) • (𝟙 A)) g w).ShortExact)
    {n : ℕ}
    [Small.{u} (Polynomial R)]
    (hQ : HasProjectiveDimensionLE Q (n + 1))
    (e : Abelian.Ext A Y (n + 1)) : e = 0 := by
  -- Step 1: The connecting map δ(e) lands in Ext^{n+2}(Q, Y) = 0
  have hδ : hSES.extClass.comp e (show 1 + (n + 1) = n + 2 by omega) = 0 :=
    Abelian.Ext.eq_zero_of_hasProjectiveDimensionLT _ (n + 2) (by omega)
  -- Step 2: By exactness, e lifts: ∃ e₂ : Ext(A, Y, n+1), (mk₀ f).comp e₂ = e
  obtain ⟨e₂, he₂⟩ := Abelian.Ext.contravariant_sequence_exact₁ hSES Y e
    (show 1 + (n + 1) = n + 2 by omega) hδ
  -- Step 3: Show (mk₀ (X • 𝟙_A)).comp e₂ = X • e₂
  -- By mk₀_smul: mk₀ (X • 𝟙) = X • mk₀ 𝟙
  -- By smul_comp: (X • mk₀ 𝟙).comp e₂ = X • (mk₀ 𝟙).comp e₂
  -- By mk₀_id_comp: (mk₀ 𝟙).comp e₂ = e₂
  have h_precomp : (Abelian.Ext.mk₀ ((Polynomial.X : Polynomial R) • (𝟙 A))).comp
      e₂ (zero_add (n + 1)) = (Polynomial.X : Polynomial R) • e₂ := by
    rw [Abelian.Ext.mk₀_smul, Abelian.Ext.smul_comp, Abelian.Ext.mk₀_id_comp]
  -- Step 4: Show X • e₂ = 0 using smul_eq_comp_mk₀ and hY
  have h_smul_zero : (Polynomial.X : Polynomial R) • e₂ = 0 := by
    rw [Abelian.Ext.smul_eq_comp_mk₀ e₂ (Polynomial.X : Polynomial R)]
    rw [hY, Abelian.Ext.mk₀_zero, Abelian.Ext.comp_zero]
  -- Combine: e = f*(e₂) = X • e₂ = 0
  rw [← he₂, h_precomp, h_smul_zero]

/-- The Shapiro transfer: for any R-module N, Ext vanishing for R[X]-modules with
trivial X-action transfers to Ext vanishing over R via the extension-restriction
adjunction. This combines ext_subsingleton_of_extendScalars with the observation
that every R-module is the restriction of an R[X]-module with trivial X-action. -/
private theorem ext_subsingleton_of_polynomial_trivial_action
    (R : Type u) [CommRing R] [Small.{u} R]
    (M : ModuleCat.{u} R) (N : ModuleCat.{u} R) (i : ℕ)
    (h : ∀ (Y : ModuleCat.{u} (Polynomial R)),
      (Polynomial.X : Polynomial R) • (𝟙 Y) = (0 : Y ⟶ Y) →
      Subsingleton (Abelian.Ext ((ModuleCat.extendScalars.{u, u, u}
        (Polynomial.C (R := R))).obj M) Y i)) :
    Subsingleton (Abelian.Ext M N i) := by
  letI : Small.{u} (Polynomial R) := ⟨⟨Polynomial R, ⟨Equiv.refl _⟩⟩⟩
  set C := Polynomial.C (R := R)
  set F := ModuleCat.extendScalars.{u, u, u} C
  set G := ModuleCat.restrictScalars.{u} C
  -- Construct the R[X]-module N₀ from N with trivial X-action (φ = 0)
  let φ : N →ₗ[R] N := 0
  let N₀ := ModuleCat.of (Polynomial R) (Module.AEval' φ)
  -- X acts as zero on N₀
  have hX : (Polynomial.X : Polynomial R) • (𝟙 N₀) = (0 : N₀ ⟶ N₀) := by
    ext x
    change (Polynomial.X : Polynomial R) • x = (0 : N₀ ⟶ N₀) x
    change (Polynomial.X : Polynomial R) • x = 0
    obtain ⟨m, rfl⟩ := (Module.AEval'.of φ).surjective x
    rw [Module.AEval'.X_smul_of, LinearMap.zero_apply, map_zero]
  -- By hypothesis, Ext^i(F(M), N₀) is subsingleton
  have hN₀ := h N₀ hX
  -- Apply Shapiro's lemma: need (extendScalars C).PreservesHomology
  -- R[X] is free over R, hence flat, so extendScalars C preserves homology
  have hFlat : C.Flat := by
    change (algebraMap R R[X]).Flat
    rw [RingHom.flat_algebraMap_iff]
    infer_instance
  haveI : F.PreservesHomology := by
    haveI := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hFlat
    haveI := (ModuleCat.extendRestrictScalarsAdj.{u} C).leftAdjoint_preservesColimits
    infer_instance
  -- By Shapiro, Ext^i(M, G(N₀)) is subsingleton
  have hGN₀ := ModuleCat.ext_subsingleton_of_extendScalars C M N₀ i hN₀
  -- G(N₀) and N have the same carrier (AEval' 0 is a type alias for N)
  -- and same R-action (C(r) •_{R[X]} m = r • m via aeval_C).
  -- Transfer: G(N₀) and N have the same carrier (AEval' 0 is a type alias for ↑N)
  -- with the same R-module structure (C(r) acts as r by Module.AEval.C_smul).
  -- We construct a LinearEquiv between G(N₀) and N, lift to a ModuleCat iso,
  -- then use Ext functoriality to transfer Subsingleton.
  -- Step 1: Build a linear equivalence G.obj N₀ ≃ₗ[R] N
  have smul_compat : ∀ (r : R) (m : G.obj N₀), (r • m : G.obj N₀) = r • (show N from m) := by
    intro r m
    change Polynomial.C r • (show N₀ from m) = r • (show N from m)
    rw [Module.AEval.C_smul]
  let e : (G.obj N₀) ≃ₗ[R] N :=
    { toFun := fun m => (show N from m)
      invFun := fun m => (show G.obj N₀ from m)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun r m => smul_compat r m }
  -- Step 2: Build the iso in ModuleCat R
  let iso : G.obj N₀ ≅ N := e.toModuleIso
  -- Step 3: Transfer Subsingleton via Ext postcomposition
  -- Postcompose a : Ext M N i with mk₀ iso.inv to land in Ext M (G.obj N₀) i,
  -- use hGN₀ to equate, then compose back with mk₀ iso.hom.
  constructor
  intro a b
  -- Map a, b into Ext M (G.obj N₀) i via postcomposition with iso.inv
  have ha := hGN₀.elim (a.comp (Abelian.Ext.mk₀ iso.inv) (add_zero i))
    (b.comp (Abelian.Ext.mk₀ iso.inv) (add_zero i))
  -- Roundtrip: composing with iso.hom after iso.inv gives identity
  have hrt : ∀ (x : Abelian.Ext M N i),
      (x.comp (Abelian.Ext.mk₀ iso.inv) (add_zero i)).comp
        (Abelian.Ext.mk₀ iso.hom) (add_zero i) = x := by
    intro x
    rw [Abelian.Ext.comp_assoc _ _ _ (add_zero i) (zero_add 0) (by omega)]
    rw [Abelian.Ext.mk₀_comp_mk₀, iso.inv_hom_id, Abelian.Ext.comp_mk₀_id]
  calc a = (a.comp (Abelian.Ext.mk₀ iso.inv) (add_zero i)).comp
        (Abelian.Ext.mk₀ iso.hom) (add_zero i) := (hrt a).symm
    _ = (b.comp (Abelian.Ext.mk₀ iso.inv) (add_zero i)).comp
        (Abelian.Ext.mk₀ iso.hom) (add_zero i) := by rw [ha]
    _ = b := hrt b

/-- For any R-module M, if gldim(R[X]) ≤ d + 1, then pd_R(M) ≤ d.

The proof combines three ingredients:

1. **SES construction**: For any R-module M, there is a short exact sequence
   0 → R[X] ⊗_R M →^{X·} R[X] ⊗_R M → Q → 0 in ModuleCat R[X].

2. **X-action vanishing**: From the contravariant LES of Ext applied to this SES,
   precomposition with X-multiplication is surjective on Ext^{d+1}(F(M), Y₀)
   (since Ext^{d+2}(Q, Y₀) = 0 by gldim). By `smul_eq_comp_mk₀`, this equals
   scalar multiplication by X, which is zero when Y₀ has trivial X-action.
   Hence Ext^{d+1}_{R[X]}(F(M), Y₀) = 0.

3. **Shapiro's lemma**: `ext_subsingleton_of_polynomial_trivial_action` transfers
   the vanishing from R[X]-modules to R-modules via the extension-restriction
   adjunction. -/
private theorem pd_le_of_polynomial_gldim (R : Type u) [CommRing R] (d : ℕ)
    (M : ModuleCat.{u} R)
    (h : Etingof.HasHomologicalDimensionLE (Polynomial R) (d + 1)) :
    HasProjectiveDimensionLE M d := by
  letI : Small.{u} R := ⟨⟨R, ⟨Equiv.refl R⟩⟩⟩
  letI : Small.{u} (Polynomial R) := ⟨⟨Polynomial R, ⟨Equiv.refl _⟩⟩⟩
  -- Abbreviations
  set F := ModuleCat.extendScalars.{u, u, u} (Polynomial.C (R := R))
  set FM := F.obj M
  set f : FM ⟶ FM := (Polynomial.X : Polynomial R) • (𝟙 FM)
  set Q := cokernel f
  -- The SES: 0 → FM →^{X·} FM → Q → 0
  have hSES := polynomialExtensionSES R M
  -- Q has pd ≤ d+1 (from gldim assumption)
  have hQ : HasProjectiveDimensionLE Q (d + 1) := h Q
  -- We show HasProjectiveDimensionLT M (d + 1), i.e., ∀ i ≥ d+1, Ext^i(M, N) = 0
  change HasProjectiveDimensionLT M (d + 1)
  rw [hasProjectiveDimensionLT_iff]
  intro i hi N e
  -- Use the Shapiro transfer: it suffices to show Ext^i(FM, Y) = 0
  -- for all Y with trivial X-action
  have hss : Subsingleton (Abelian.Ext M N i) :=
    ext_subsingleton_of_polynomial_trivial_action R M N i (fun Y hY => by
      constructor; intro a b
      -- For i ≥ d+2: direct from pd(FM) ≤ d+1
      -- For i = d+1: use the LES + X-action vanishing lemma
      have hFM_pd : HasProjectiveDimensionLE FM (d + 1) := h FM
      -- Both a and b are elements of Ext FM Y i
      -- For i ≥ d+1, we need to show a = b, i.e., a - b = 0
      suffices ∀ (x : Abelian.Ext FM Y i), x = 0 from
        (this a).trans (this b).symm
      intro x
      -- Case split: i = d+1 vs i ≥ d+2
      obtain rfl | hi' := Nat.eq_or_lt_of_le hi
      · -- i = d+1: use the LES + X-action vanishing
        exact ext_eq_zero_of_X_action_vanishing hY hSES hQ x
      · -- i ≥ d+2: Ext vanishes by pd(FM) ≤ d+1
        exact Abelian.Ext.eq_zero_of_hasProjectiveDimensionLT x (d + 2) (by omega))
  exact hss.elim e 0

/-- If R is a nontrivial commutative ring and HasHomologicalDimensionLE (Polynomial R) (d+1),
then HasHomologicalDimensionLE R d. This is the key inductive step for the lower bound:
gldim(R[x]) ≥ gldim(R) + 1.

See `pd_le_of_polynomial_gldim` for the proof strategy. -/
private theorem hasHomologicalDimensionLE_of_polynomial_succ
    (R : Type u) [CommRing R] [Nontrivial R] (d : ℕ)
    (h : Etingof.HasHomologicalDimensionLE (Polynomial R) (d + 1)) :
    Etingof.HasHomologicalDimensionLE R d := by
  intro M
  exact pd_le_of_polynomial_gldim R d M h

end PolynomialLowerBound

/-- The Hilbert syzygy theorem (lower bound): if every module over k[x₁, …, xₙ] has
projective dimension ≤ d, then n ≤ d. Equivalently, the residue field
k = k[x₁,…,xₙ]/(x₁,…,xₙ) has projective dimension exactly n.

The proof is by induction on n, using the ring equivalence
k[x₁,…,x_{n+1}] ≃ k[x₁,…,xₙ][x_{n+1}] and the fact that polynomial extension
increases global dimension by at least 1. -/
theorem mvPolynomial_homologicalDimension_le_iff (k : Type u) [Field k] :
    ∀ n d, HasHomologicalDimensionLE (MvPolynomial (Fin n) k) d → n ≤ d
  | 0, d, _ => Nat.zero_le d
  | n + 1, d, hd => by
    -- Transfer via ring iso: MvPolynomial (Fin (n+1)) k ≃+* Polynomial (MvPolynomial (Fin n) k)
    have e := (MvPolynomial.finSuccEquiv k n).symm.toRingEquiv
    have hpoly : HasHomologicalDimensionLE (Polynomial (MvPolynomial (Fin n) k)) d :=
      hasHomologicalDimensionLE_of_ringEquiv e d hd
    -- Case split on d
    match d with
    | 0 => exact absurd hpoly (not_hasHomologicalDimensionLE_zero_polynomial _)
    | d' + 1 =>
      have hR := hasHomologicalDimensionLE_of_polynomial_succ _ d' hpoly
      have ih := mvPolynomial_homologicalDimension_le_iff k n d' hR
      omega

/-- The Hilbert syzygy theorem: the homological dimension of k[x₁, …, xₙ] is n.
(Etingof Example 9.4.4) -/
theorem Etingof.Example_9_4_4 (k : Type u) [Field k] (n : ℕ) :
    Etingof.homologicalDimension (MvPolynomial (Fin n) k) = n := by
  unfold homologicalDimension
  apply le_antisymm
  · exact iInf₂_le n (mvPolynomial_hasHomologicalDimensionLE k n)
  · apply le_iInf₂
    intro d hd
    exact_mod_cast mvPolynomial_homologicalDimension_le_iff k n d hd
