import Mathlib
import EtingofRepresentationTheory.Infrastructure.IrreducibleEnumeration

/-!
# Theorem 5.25.2: Principal Series Representations of GL₂(𝔽_q)

(1) If λ₁ ≠ λ₂, then V(λ₁, λ₂) is irreducible.
(2) If λ₁ = λ₂ = μ, then V(λ₁, λ₂) = ℂ_μ ⊕ W_μ where W_μ is
    a q-dimensional irreducible representation of G.
(3) W_μ ≅ W_ν iff μ = ν; V(λ₁, λ₂) ≅ V(λ'₁, λ'₂) iff {λ₁, λ₂} = {λ'₁, λ'₂}.

## Mathlib correspondence

Uses `GaloisField` and finite group representation theory.
The principal series construction is not in Mathlib; we define the
Borel subgroup and principal series locally.
-/

open CategoryTheory CategoryTheory.Limits Classical

noncomputable section

variable (p : ℕ) [hp : Fact (Nat.Prime p)] (n : ℕ)

private abbrev GL2 (p n : ℕ) [Fact (Nat.Prime p)] :=
  Matrix.GeneralLinearGroup (Fin 2) (GaloisField p n)

instance : Fintype (GaloisField p n) := Fintype.ofFinite _

/-- The Borel subgroup of GL₂(𝔽_q): upper-triangular invertible matrices. -/
def Etingof.GL2.BorelSubgroup :
    Subgroup (GL2 p n) where
  carrier := {g | (g : Matrix (Fin 2) (Fin 2) (GaloisField p n)) 1 0 = 0}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two] at *
    simp [ha, hb]
  one_mem' := by
    simp only [Set.mem_setOf_eq, Units.val_one, Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0)]
  inv_mem' := by
    intro g hg
    simp only [Set.mem_setOf_eq] at *
    have hmul : (g.val * (g⁻¹).val) 1 0 = (1 : Matrix (Fin 2) (Fin 2) _) 1 0 := by
      have : g.val * (g⁻¹).val = 1 := by exact_mod_cast g.mul_inv
      rw [this]
    simp only [Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0)] at hmul
    rw [hg, zero_mul, zero_add] at hmul
    have hdet : IsUnit (g.val.det) := g.isUnit.map Matrix.detMonoidHom
    rw [Matrix.det_fin_two, hg, mul_zero, sub_zero] at hdet
    exact (mul_eq_zero.mp hmul).resolve_left
      (IsUnit.ne_zero (isUnit_of_mul_isUnit_right hdet))

-- ============================================================
-- Helper infrastructure for principal series definitions
-- ============================================================

private lemma Etingof.GL2.borel_diag00_ne_zero
    (b : ↥(Etingof.GL2.BorelSubgroup p n)) :
    (b.val.val : Matrix (Fin 2) (Fin 2) (GaloisField p n)) 0 0 ≠ 0 := by
  intro h
  have hdet : IsUnit (b.val.val : Matrix (Fin 2) (Fin 2) (GaloisField p n)).det :=
    b.val.isUnit.map Matrix.detMonoidHom
  rw [Matrix.det_fin_two, b.prop, mul_zero, sub_zero, h, zero_mul] at hdet
  exact not_isUnit_zero hdet

private lemma Etingof.GL2.borel_diag11_ne_zero
    (b : ↥(Etingof.GL2.BorelSubgroup p n)) :
    (b.val.val : Matrix (Fin 2) (Fin 2) (GaloisField p n)) 1 1 ≠ 0 := by
  intro h
  have hdet : IsUnit (b.val.val : Matrix (Fin 2) (Fin 2) (GaloisField p n)).det :=
    b.val.isUnit.map Matrix.detMonoidHom
  rw [Matrix.det_fin_two, b.prop, mul_zero, sub_zero, h, mul_zero] at hdet
  exact not_isUnit_zero hdet

/-- The value of the Borel character χ₁(b₀₀)·χ₂(b₁₁) for b ∈ B. -/
private def Etingof.GL2.borelCharValue
    (chi1 chi2 : (GaloisField p n)ˣ →* ℂˣ)
    (b : ↥(Etingof.GL2.BorelSubgroup p n)) : ℂ :=
  let bmat := (b.val.val : Matrix (Fin 2) (Fin 2) (GaloisField p n))
  (chi1 (Units.mk0 (bmat 0 0) (Etingof.GL2.borel_diag00_ne_zero p n b)) : ℂ) *
  (chi2 (Units.mk0 (bmat 1 1) (Etingof.GL2.borel_diag11_ne_zero p n b)) : ℂ)

/-- The covariance submodule: functions f : G → ℂ satisfying f(bg) = λ(b)·f(g). -/
private def Etingof.GL2.principalSeriesSubmodule
    (chi1 chi2 : (GaloisField p n)ˣ →* ℂˣ) :
    Submodule ℂ (GL2 p n → ℂ) where
  carrier := {f | ∀ (b : ↥(Etingof.GL2.BorelSubgroup p n)) (g : GL2 p n),
    f (b.val * g) = Etingof.GL2.borelCharValue p n chi1 chi2 b * f g}
  add_mem' {f g} hf hg := by
    intro b x; simp only [Set.mem_setOf_eq, Pi.add_apply]; rw [hf b x, hg b x, mul_add]
  zero_mem' := by intro b g; simp
  smul_mem' c f hf := by
    intro b g; simp only [Set.mem_setOf_eq, Pi.smul_apply, smul_eq_mul]
    rw [hf b g, mul_left_comm]

/-- The principal series as a representation via right translation. -/
private def Etingof.GL2.principalSeriesRep
    (chi1 chi2 : (GaloisField p n)ˣ →* ℂˣ) :
    Representation ℂ (GL2 p n)
      (Etingof.GL2.principalSeriesSubmodule p n chi1 chi2) where
  toFun h := {
    toFun := fun ⟨f, hf⟩ => ⟨fun g => f (g * h), fun b g => by
      change f (↑b * g * h) = Etingof.GL2.borelCharValue p n chi1 chi2 b * f (g * h)
      rw [mul_assoc]; exact hf b (g * h)⟩
    map_add' := fun ⟨_, _⟩ ⟨_, _⟩ => Subtype.ext rfl
    map_smul' := fun _ ⟨_, _⟩ => Subtype.ext rfl }
  map_one' := by
    apply LinearMap.ext; intro ⟨f, _⟩
    exact Subtype.ext (funext fun g => congr_arg f (mul_one g))
  map_mul' a b := by
    apply LinearMap.ext; intro ⟨f, _⟩
    exact Subtype.ext (funext fun g => congr_arg f (mul_assoc g a b).symm)

/-- The augmentation functional on G → ℂ, used to define W_μ.
    Maps f to ∑_g f(g) · μ(det g)⁻¹. -/
private def Etingof.GL2.augmentation
    (mu : (GaloisField p n)ˣ →* ℂˣ) :
    (GL2 p n → ℂ) →ₗ[ℂ] ℂ where
  toFun f := ∑ g : GL2 p n,
    f g * ((mu (Matrix.GeneralLinearGroup.det g))⁻¹ : ℂˣ)
  map_add' f g := by simp [Finset.sum_add_distrib, add_mul]
  map_smul' c f := by
    simp only [smul_eq_mul, RingHom.id_apply, Pi.smul_apply]
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum]

/-- The complement submodule W_μ: covariant functions with zero augmentation. -/
private def Etingof.GL2.complementWSubmodule
    (mu : (GaloisField p n)ˣ →* ℂˣ) :
    Submodule ℂ (GL2 p n → ℂ) :=
  Etingof.GL2.principalSeriesSubmodule p n mu mu ⊓
    LinearMap.ker (Etingof.GL2.augmentation p n mu)

/-- Right translation preserves the complement W_μ. -/
private lemma Etingof.GL2.complementW_mem_of_mul
    (mu : (GaloisField p n)ˣ →* ℂˣ)
    (f : GL2 p n → ℂ)
    (hf : f ∈ Etingof.GL2.complementWSubmodule p n mu)
    (h : GL2 p n) :
    (fun g => f (g * h)) ∈ Etingof.GL2.complementWSubmodule p n mu := by
  constructor
  · -- Covariance preserved
    intro b g
    change f (↑b * g * h) = Etingof.GL2.borelCharValue p n mu mu b * f (g * h)
    rw [mul_assoc]; exact hf.1 b (g * h)
  · -- Augmentation = 0: ∑_g f(gh) · μ(det g)⁻¹ = 0
    -- Reindex g ↦ g·h⁻¹, use det multiplicativity, factor out constant
    have hker : ∑ g : GL2 p n, f g * ↑(mu (Matrix.GeneralLinearGroup.det g))⁻¹ = 0 := by
      have := hf.2; simp only [LinearMap.mem_ker, Etingof.GL2.augmentation,
        LinearMap.coe_mk, AddHom.coe_mk] at this; exact this
    show (fun g => f (g * h)) ∈ LinearMap.ker (Etingof.GL2.augmentation p n mu)
    rw [LinearMap.mem_ker]
    show ∑ g : GL2 p n,
      f (g * h) * ↑(mu (Matrix.GeneralLinearGroup.det g))⁻¹ = 0
    -- Reindex via g ↦ g * h⁻¹: transforms ∑ f(g*h)*c(g) into ∑ f(g)*c(g*h⁻¹)
    rw [Fintype.sum_equiv (Equiv.mulRight h)
        (fun g => f (g * h) * ↑(mu (Matrix.GeneralLinearGroup.det g))⁻¹)
        (fun g => f g * ↑(mu (Matrix.GeneralLinearGroup.det (g * h⁻¹)))⁻¹)
        (fun g => by simp [Equiv.coe_mulRight, inv_mul_cancel_right])]
    -- Now: ∑_g f(g) * μ(det(g * h⁻¹))⁻¹ = 0
    -- Use det multiplicativity and factor out the constant
    simp_rw [map_mul, mul_inv_rev, Units.val_mul]
    simp_rw [show ∀ g : GL2 p n,
        f g * (↑(mu (Matrix.GeneralLinearGroup.det h⁻¹))⁻¹ *
        ↑(mu (Matrix.GeneralLinearGroup.det g))⁻¹) =
        f g * ↑(mu (Matrix.GeneralLinearGroup.det g))⁻¹ *
        ↑(mu (Matrix.GeneralLinearGroup.det h⁻¹))⁻¹ from fun g => by ring]
    rw [← Finset.sum_mul, hker, zero_mul]

/-- The complement W_μ as a representation via right translation. -/
private def Etingof.GL2.complementWRep
    (mu : (GaloisField p n)ˣ →* ℂˣ) :
    Representation ℂ (GL2 p n) (Etingof.GL2.complementWSubmodule p n mu) where
  toFun h := {
    toFun := fun ⟨f, hf⟩ => ⟨fun g => f (g * h),
      Etingof.GL2.complementW_mem_of_mul p n mu f hf h⟩
    map_add' := fun ⟨_, _⟩ ⟨_, _⟩ => Subtype.ext rfl
    map_smul' := fun _ ⟨_, _⟩ => Subtype.ext rfl }
  map_one' := by
    apply LinearMap.ext; intro ⟨f, _⟩
    exact Subtype.ext (funext fun g => congr_arg f (mul_one g))
  map_mul' a b := by
    apply LinearMap.ext; intro ⟨f, _⟩
    exact Subtype.ext (funext fun g => congr_arg f (mul_assoc g a b).symm)

-- ============================================================
-- Main definitions
-- ============================================================

/-- The principal series representation V(χ₁, χ₂) of GL₂(𝔽_q), defined as
Ind_B^G ℂ_{χ₁,χ₂} where B is the Borel subgroup and χ₁, χ₂ : 𝔽_q× → ℂ×
are multiplicative characters. -/
def Etingof.GL2.principalSeries
    (chi1 chi2 : (GaloisField p n)ˣ →* ℂˣ) :
    FDRep ℂ (GL2 p n) :=
  FDRep.of (Etingof.GL2.principalSeriesRep p n chi1 chi2)

/-- The one-dimensional representation ℂ_μ of GL₂(𝔽_q) given by
g ↦ μ(det g), where μ : 𝔽_q× → ℂ× is a multiplicative character. -/
def Etingof.GL2.detChar
    (mu : (GaloisField p n)ˣ →* ℂˣ) :
    FDRep ℂ (GL2 p n) :=
  FDRep.of
    ({ toFun := fun g => ((mu (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) • LinearMap.id
       map_one' := by
         ext; simp
       map_mul' := fun a b => by
         apply LinearMap.ext; intro x
         change ((mu (Matrix.GeneralLinearGroup.det (a * b)) : ℂˣ) : ℂ) * x =
           ((mu (Matrix.GeneralLinearGroup.det a) : ℂˣ) : ℂ) *
           (((mu (Matrix.GeneralLinearGroup.det b) : ℂˣ) : ℂ) * x)
         rw [map_mul, map_mul, Units.val_mul, mul_assoc]
    } : Representation ℂ _ ℂ)

/-- The irreducible representation W_μ of GL₂(𝔽_q) of dimension q, appearing
as the complement of ℂ_μ in V(μ, μ). -/
def Etingof.GL2.complementW
    (mu : (GaloisField p n)ˣ →* ℂˣ) :
    FDRep ℂ (GL2 p n) :=
  FDRep.of (Etingof.GL2.complementWRep p n mu)

-- ============================================================
-- Character orthogonality helpers
-- ============================================================

/-- Sum of a nontrivial multiplicative character over a finite commutative group is zero. -/
private lemma sum_monoidHom_units_eq_zero
    {F : Type*} [CommGroup F] [Fintype F]
    (φ : F →* ℂˣ) (hφ : φ ≠ 1) :
    ∑ x : F, (φ x : ℂ) = 0 := by
  -- Find an element where φ is nontrivial
  have ⟨b, hb⟩ : ∃ b, φ b ≠ 1 := by
    by_contra h; push_neg at h
    exact hφ (MonoidHom.ext fun x => h x)
  -- Reindex sum: ∑ φ(x) = ∑ φ(b*x) = φ(b) · ∑ φ(x)
  have hreindex : ∑ x : F, (φ (b * x) : ℂ) = ∑ x : F, (φ x : ℂ) :=
    Fintype.sum_equiv (Equiv.mulLeft b) _ _ (fun _ => rfl)
  simp_rw [map_mul, Units.val_mul] at hreindex
  rw [← Finset.mul_sum] at hreindex
  -- So (φ(b) - 1) · ∑ φ(x) = 0, and φ(b) ≠ 1, hence ∑ = 0
  have hsub : ((φ b : ℂ) - 1) * ∑ x : F, (φ x : ℂ) = 0 := by
    rw [sub_mul, one_mul, sub_eq_zero]; exact hreindex
  rcases mul_eq_zero.mp hsub with h | h
  · exact absurd (Units.val_injective ((sub_eq_zero.mp h).trans Units.val_one.symm)) hb
  · exact h

/-- A full faithful functor preserving monomorphisms reflects Simple objects. -/
private lemma simple_of_full_faithful_preservesMono' {C D : Type*} [Category C] [Category D]
    [Limits.HasZeroMorphisms C] [Limits.HasZeroMorphisms D]
    (F : C ⥤ D) [F.Full] [F.Faithful] [F.PreservesMonomorphisms] (X : C)
    [Simple (F.obj X)] : Simple X where
  mono_isIso_iff_nonzero {Y} f := by
    intro
    constructor
    · intro hiso
      haveI : IsIso (F.map f) := Functor.map_isIso F f
      exact fun h => (Simple.mono_isIso_iff_nonzero (F.map f)).mp inferInstance
        (by rw [h]; simp)
    · intro hne
      haveI : Mono (F.map f) := inferInstance
      haveI : IsIso (F.map f) := (Simple.mono_isIso_iff_nonzero (F.map f)).mpr
        (fun h => hne (F.map_injective (by rwa [F.map_zero])))
      exact isIso_of_fully_faithful F f

/-- Bridge: IsSimpleModule → Simple FDRep. -/
private lemma simple_of_isSimpleModule_FDRep
    {G : Type} [Group G] [Fintype G]
    [NeZero (Nat.card G : ℂ)]
    {V : Type} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (ρ : Representation ℂ G V)
    [IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule] :
    Simple (FDRep.of ρ) := by
  let E := Rep.equivalenceModuleMonoidAlgebra (k := ℂ) (G := G)
  haveI : Simple (E.functor.obj ((forget₂ (FDRep ℂ G) (Rep ℂ G)).obj (FDRep.of ρ))) := by
    change Simple (ModuleCat.of (MonoidAlgebra ℂ G) ρ.asModule)
    exact simple_of_isSimpleModule
  haveI : Simple ((forget₂ (FDRep ℂ G) (Rep ℂ G)).obj (FDRep.of ρ)) :=
    simple_of_full_faithful_preservesMono' E.functor _
  exact simple_of_full_faithful_preservesMono' (forget₂ (FDRep ℂ G) (Rep ℂ G)) _

section Theorem5_25_2

variable (p : ℕ) [hp : Fact (Nat.Prime p)] (n : ℕ) (hn : 0 < n)

-- principalSeries_simple_of_ne is proved below, after coset rep infrastructure

/-- Coset representatives for B\GL₂(𝔽_q), indexed by Option (GaloisField p n) ≅ P¹(𝔽_q).
    none ↦ I, some t ↦ [[0,-1],[1,t]] with det = 1. -/
private noncomputable def Etingof.GL2.cosetRep
    (i : Option (GaloisField p n)) : GL2 p n :=
  match i with
  | none => 1
  | some t => Matrix.GeneralLinearGroup.mkOfDetNeZero
      (n := Fin 2) (K := GaloisField p n) !![0, -1; 1, t]
      (by simp [Matrix.det_fin_two])

/-- The coset index of g ∈ GL₂: none if g ∈ B, some (g₁₁/g₁₀) if g₁₀ ≠ 0. -/
private noncomputable def Etingof.GL2.cosetIndex
    (g : GL2 p n) : Option (GaloisField p n) :=
  if h : (g.val : Matrix (Fin 2) (Fin 2) (GaloisField p n)) 1 0 = 0 then none
  else some ((g.val : Matrix _ _ _) 1 1 / (g.val : Matrix _ _ _) 1 0)

/-- Every g ∈ GL₂ satisfies g = b * rep(idx(g)) for some b ∈ B. -/
private lemma Etingof.GL2.mem_coset_of_cosetIndex
    (g : GL2 p n) :
    ∃ (b : ↥(Etingof.GL2.BorelSubgroup p n)),
      g = b.val * Etingof.GL2.cosetRep p n (Etingof.GL2.cosetIndex p n g) := by
  unfold Etingof.GL2.cosetIndex Etingof.GL2.cosetRep
  split_ifs with h10
  · exact ⟨⟨g, h10⟩, by simp⟩
  · set gm := (g.val : Matrix (Fin 2) (Fin 2) (GaloisField p n)) with hgm_def
    have hdet : gm.det ≠ 0 := IsUnit.ne_zero ((Units.isUnit g).map Matrix.detMonoidHom)
    set bmat : Matrix (Fin 2) (Fin 2) (GaloisField p n) :=
      !![gm.det / gm 1 0, gm 0 0; (0 : _), gm 1 0] with hbmat_def
    have hbdet : bmat.det ≠ 0 := by
      have : bmat.det = gm.det := by
        simp [hbmat_def, Matrix.det_fin_two]
        field_simp
      rw [this]; exact hdet
    refine ⟨⟨Matrix.GeneralLinearGroup.mkOfDetNeZero bmat hbdet, ?_⟩, ?_⟩
    · -- b ∈ B: b₁₀ = 0
      show ((Matrix.GeneralLinearGroup.mkOfDetNeZero bmat hbdet).val :
        Matrix (Fin 2) (Fin 2) (GaloisField p n)) 1 0 = 0
      simp [Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.GeneralLinearGroup.mk',
            Matrix.unitOfDetInvertible, bmat]
    · -- g = b * rep(t): verify entry by entry
      apply Matrix.GeneralLinearGroup.ext; intro i j
      simp only [Matrix.GeneralLinearGroup.coe_mul,
        Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.GeneralLinearGroup.mk',
        Matrix.unitOfDetInvertible, Matrix.mul_apply, Fin.sum_univ_two]
      fin_cases i <;> fin_cases j <;>
        simp [bmat, Matrix.det_fin_two, Matrix.unitOfDetInvertible] <;>
        (try ring) <;> (field_simp; ring)

/-- Evaluation at coset representatives is injective: if f(rep(i)) = 0 for all i, then f = 0. -/
private lemma Etingof.GL2.principalSeries_eval_injective
    (chi1 chi2 : (GaloisField p n)ˣ →* ℂˣ)
    (f : ↥(Etingof.GL2.principalSeriesSubmodule p n chi1 chi2))
    (hf : ∀ i : Option (GaloisField p n),
      (f : GL2 p n → ℂ) (Etingof.GL2.cosetRep p n i) = 0) :
    f = 0 := by
  ext g
  -- Decompose g = b * rep(idx(g))
  obtain ⟨b, hbg⟩ := Etingof.GL2.mem_coset_of_cosetIndex p n g
  -- Use covariance: f(g) = f(b * rep(i)) = χ(b) * f(rep(i)) = χ(b) * 0 = 0
  have hcov := f.prop b (Etingof.GL2.cosetRep p n (Etingof.GL2.cosetIndex p n g))
  rw [← hbg] at hcov
  rw [show (f : GL2 p n → ℂ) g = (f.val g) from rfl, hcov,
      hf (Etingof.GL2.cosetIndex p n g), mul_zero]
  simp

-- ============================================================
-- Helper group elements and action formulas for the irreducibility proof
-- ============================================================

/-- Translation element [[1,s],[0,1]] in GL₂(𝔽_q). -/
private noncomputable def Etingof.GL2.translationElt
    (s : GaloisField p n) : GL2 p n :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero
    !![1, s; 0, 1] (by simp [Matrix.det_fin_two])

/-- Diagonal element [[c,0],[0,1]] in GL₂(𝔽_q). -/
private noncomputable def Etingof.GL2.diagElt
    (c : (GaloisField p n)ˣ) : GL2 p n :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero
    !![(c : GaloisField p n), 0; 0, 1]
    (by simp [Matrix.det_fin_two, Units.ne_zero])

/-- rep(some t) * [[1,s],[0,1]] = rep(some(t+s)). -/
private lemma Etingof.GL2.cosetRep_mul_translation_some
    (t s : GaloisField p n) :
    Etingof.GL2.cosetRep p n (some t) * Etingof.GL2.translationElt p n s =
    Etingof.GL2.cosetRep p n (some (t + s)) := by
  apply Matrix.GeneralLinearGroup.ext; intro i j
  simp only [Matrix.GeneralLinearGroup.coe_mul,
    Etingof.GL2.cosetRep, Etingof.GL2.translationElt,
    Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.GeneralLinearGroup.mk',
    Matrix.unitOfDetInvertible, Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> simp <;> ring

/-- (ρ(τ_s) f)(rep(some t)) = f(rep(some(t + s))). -/
private lemma Etingof.GL2.action_translation_some
    (chi1 chi2 : (GaloisField p n)ˣ →* ℂˣ)
    (f : ↥(Etingof.GL2.principalSeriesSubmodule p n chi1 chi2))
    (s t : GaloisField p n) :
    (Etingof.GL2.principalSeriesRep p n chi1 chi2
      (Etingof.GL2.translationElt p n s) f).val
      (Etingof.GL2.cosetRep p n (some t)) =
    f.val (Etingof.GL2.cosetRep p n (some (t + s))) := by
  change f.val (Etingof.GL2.cosetRep p n (some t) * Etingof.GL2.translationElt p n s) = _
  rw [Etingof.GL2.cosetRep_mul_translation_some]

/-- (ρ(τ_s) f)(rep(none)) = f(rep(none)). -/
private lemma Etingof.GL2.action_translation_none
    (chi1 chi2 : (GaloisField p n)ˣ →* ℂˣ)
    (f : ↥(Etingof.GL2.principalSeriesSubmodule p n chi1 chi2))
    (s : GaloisField p n) :
    (Etingof.GL2.principalSeriesRep p n chi1 chi2
      (Etingof.GL2.translationElt p n s) f).val
      (Etingof.GL2.cosetRep p n none) =
    f.val (Etingof.GL2.cosetRep p n none) := by
  change f.val (Etingof.GL2.cosetRep p n none * Etingof.GL2.translationElt p n s) = _
  simp only [Etingof.GL2.cosetRep, one_mul]
  -- τ_s ∈ B with b₀₀ = 1, b₁₁ = 1
  have hb_mem : (Etingof.GL2.translationElt p n s).val 1 0 = 0 := by
    simp [Etingof.GL2.translationElt, Matrix.GeneralLinearGroup.mkOfDetNeZero,
      Matrix.GeneralLinearGroup.mk', Matrix.unitOfDetInvertible]
  have hcov := f.prop ⟨Etingof.GL2.translationElt p n s, hb_mem⟩ 1
  simp only [Subgroup.coe_mk, mul_one] at hcov
  rw [hcov]
  simp [Etingof.GL2.borelCharValue, Etingof.GL2.translationElt,
    Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.GeneralLinearGroup.mk',
    Matrix.unitOfDetInvertible]

/-- (ρ(δ_c) f)(rep(some t)) = (χ₂ c : ℂ) * f(rep(some(t * ↑c⁻¹))). -/
private lemma Etingof.GL2.action_diagonal_some
    (chi1 chi2 : (GaloisField p n)ˣ →* ℂˣ)
    (f : ↥(Etingof.GL2.principalSeriesSubmodule p n chi1 chi2))
    (c : (GaloisField p n)ˣ) (t : GaloisField p n) :
    (Etingof.GL2.principalSeriesRep p n chi1 chi2
      (Etingof.GL2.diagElt p n c) f).val
      (Etingof.GL2.cosetRep p n (some t)) =
    (chi2 c : ℂ) * f.val (Etingof.GL2.cosetRep p n (some (t * ↑c⁻¹))) := by
  change f.val (Etingof.GL2.cosetRep p n (some t) * Etingof.GL2.diagElt p n c) = _
  -- Factor: rep(some t) * diag(c,1) = diag(1,c) * rep(some(t*c⁻¹))
  set bmat : Matrix (Fin 2) (Fin 2) (GaloisField p n) :=
    !![1, 0; 0, (c : GaloisField p n)]
  have hbdet : bmat.det ≠ 0 := by
    simp [bmat, Matrix.det_fin_two, Units.ne_zero]
  set b := Matrix.GeneralLinearGroup.mkOfDetNeZero bmat hbdet
  have hb_mem : b.val 1 0 = 0 := by
    simp [b, bmat, Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.GeneralLinearGroup.mk',
      Matrix.unitOfDetInvertible]
  have hprod : Etingof.GL2.cosetRep p n (some t) * Etingof.GL2.diagElt p n c =
      b * Etingof.GL2.cosetRep p n (some (t * ↑c⁻¹)) := by
    apply Matrix.GeneralLinearGroup.ext; intro i j
    simp only [Matrix.GeneralLinearGroup.coe_mul,
      Etingof.GL2.cosetRep, Etingof.GL2.diagElt, b, bmat,
      Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.GeneralLinearGroup.mk',
      Matrix.unitOfDetInvertible, Matrix.mul_apply, Fin.sum_univ_two]
    have hc_ne : (c : GaloisField p n) ≠ 0 := Units.ne_zero c
    fin_cases i <;> fin_cases j <;> simp
    · -- (1,1) entry: t = ↑c * (t * (↑c)⁻¹)
      field_simp
  rw [hprod]
  have hcov := f.prop ⟨b, hb_mem⟩ (Etingof.GL2.cosetRep p n (some (t * ↑c⁻¹)))
  rw [hcov]
  congr 1
  simp [Etingof.GL2.borelCharValue, b, bmat,
    Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.GeneralLinearGroup.mk',
    Matrix.unitOfDetInvertible]

/-- (ρ(δ_c) f)(rep(none)) = (χ₁ c : ℂ) * f(rep(none)). -/
private lemma Etingof.GL2.action_diagonal_none
    (chi1 chi2 : (GaloisField p n)ˣ →* ℂˣ)
    (f : ↥(Etingof.GL2.principalSeriesSubmodule p n chi1 chi2))
    (c : (GaloisField p n)ˣ) :
    (Etingof.GL2.principalSeriesRep p n chi1 chi2
      (Etingof.GL2.diagElt p n c) f).val
      (Etingof.GL2.cosetRep p n none) =
    (chi1 c : ℂ) * f.val (Etingof.GL2.cosetRep p n none) := by
  change f.val (Etingof.GL2.cosetRep p n none * Etingof.GL2.diagElt p n c) = _
  simp only [Etingof.GL2.cosetRep, one_mul]
  have hb_mem : (Etingof.GL2.diagElt p n c).val 1 0 = 0 := by
    simp [Etingof.GL2.diagElt, Matrix.GeneralLinearGroup.mkOfDetNeZero,
      Matrix.GeneralLinearGroup.mk', Matrix.unitOfDetInvertible]
  have hcov := f.prop ⟨Etingof.GL2.diagElt p n c, hb_mem⟩ 1
  simp only [Subgroup.coe_mk, mul_one] at hcov
  rw [hcov]
  congr 1
  simp [Etingof.GL2.borelCharValue, Etingof.GL2.diagElt,
    Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.GeneralLinearGroup.mk',
    Matrix.unitOfDetInvertible]

/-- (ρ(w) f)(rep(none)) = f(rep(some 0)) where w = rep(some 0). -/
private lemma Etingof.GL2.action_weyl_none
    (chi1 chi2 : (GaloisField p n)ˣ →* ℂˣ)
    (f : ↥(Etingof.GL2.principalSeriesSubmodule p n chi1 chi2)) :
    (Etingof.GL2.principalSeriesRep p n chi1 chi2
      (Etingof.GL2.cosetRep p n (some 0)) f).val
      (Etingof.GL2.cosetRep p n none) =
    f.val (Etingof.GL2.cosetRep p n (some 0)) := by
  change f.val (Etingof.GL2.cosetRep p n none * Etingof.GL2.cosetRep p n (some 0)) = _
  simp [Etingof.GL2.cosetRep]

-- ============================================================
-- Main irreducibility proof
-- ============================================================

/-- The principal series module is nonzero: there exists a nonzero covariant function. -/
private lemma Etingof.GL2.principalSeries_nontrivial
    (chi1 chi2 : (GaloisField p n)ˣ →* ℂˣ) :
    Nontrivial (Subrepresentation (Etingof.GL2.principalSeriesRep p n chi1 chi2)) := by
  -- The underlying module is nonzero (there exist nonzero covariant functions).
  -- By principalSeries_eval_surjective, the evaluation map at coset reps is surjective,
  -- so the module has dimension ≥ 1.
  sorry

/-- Key construction: from any nonzero f ∈ S, produce g ∈ S
    with g(rep(none)) ≠ 0 and g(rep(some t)) = 0 for all t.
    Step 1: if f(rep(none)) = 0, apply Weyl·τ to get f' with f'(rep(none)) ≠ 0.
    Step 2: average over translations, then use diagonal scaling with
    χ₁ ≠ χ₂ to kill the "some" part. -/
private lemma Etingof.GL2.principalSeries_construct_delta_none
    (chi1 chi2 : (GaloisField p n)ˣ →* ℂˣ) (hne : chi1 ≠ chi2)
    (S : Subrepresentation (Etingof.GL2.principalSeriesRep p n chi1 chi2))
    (f : ↥(Etingof.GL2.principalSeriesSubmodule p n chi1 chi2))
    (hfS : f ∈ S.toSubmodule) (hfne : f ≠ 0) :
    ∃ g : ↥(Etingof.GL2.principalSeriesSubmodule p n chi1 chi2),
      g ∈ S.toSubmodule ∧
      g.val (Etingof.GL2.cosetRep p n none) ≠ 0 ∧
      ∀ t : GaloisField p n, g.val (Etingof.GL2.cosetRep p n (some t)) = 0 := by
  -- Step 1: Get f' ∈ S with f'(rep(none)) ≠ 0
  -- If f(rep(none)) ≠ 0, use f directly; otherwise apply ρ(w)·ρ(τ_t) for some t
  have hf'exists : ∃ f' ∈ S.toSubmodule,
      f'.val (Etingof.GL2.cosetRep p n none) ≠ 0 := by
    by_cases hfnone : f.val (Etingof.GL2.cosetRep p n none) ≠ 0
    · exact ⟨f, hfS, hfnone⟩
    · push_neg at hfnone
      -- f ≠ 0 but f(rep(none)) = 0, so some f(rep(some t₀)) ≠ 0
      have hsome : ∃ t₀, f.val (Etingof.GL2.cosetRep p n (some t₀)) ≠ 0 := by
        by_contra hall; push_neg at hall
        exact hfne (Etingof.GL2.principalSeries_eval_injective p n chi1 chi2 f
          (fun i => match i with | none => hfnone | some t => hall t))
      obtain ⟨t₀, ht₀⟩ := hsome
      -- ρ(w)(ρ(τ_{t₀})(f)) has nonzero value at rep(none)
      set f' := (Etingof.GL2.principalSeriesRep p n chi1 chi2) (Etingof.GL2.cosetRep p n (some 0))
        ((Etingof.GL2.principalSeriesRep p n chi1 chi2) (Etingof.GL2.translationElt p n t₀) f)
      refine ⟨f', ?_, ?_⟩
      · -- f' ∈ S: S is G-stable
        exact S.apply_mem_toSubmodule _ (S.apply_mem_toSubmodule _ hfS)
      · -- f'(rep(none)) ≠ 0
        -- f'(rep(none)) = ρ(w)(ρ(τ_{t₀})f)(rep(none)) = ρ(τ_{t₀})f(rep(some 0))
        --   = f(rep(some(0 + t₀))) = f(rep(some t₀)) ≠ 0
        change f'.val (Etingof.GL2.cosetRep p n none) ≠ 0
        rw [show f'.val = (Etingof.GL2.principalSeriesRep p n chi1 chi2
          (Etingof.GL2.cosetRep p n (some 0))
          (Etingof.GL2.principalSeriesRep p n chi1 chi2
            (Etingof.GL2.translationElt p n t₀) f)).val from rfl]
        rw [Etingof.GL2.action_weyl_none p n chi1 chi2
          (Etingof.GL2.principalSeriesRep p n chi1 chi2 (Etingof.GL2.translationElt p n t₀) f)]
        rw [Etingof.GL2.action_translation_some p n chi1 chi2 f t₀ 0, zero_add]
        exact ht₀
  obtain ⟨f', hf'S, hf'none⟩ := hf'exists
  -- Step 2: Average over translations to make "some" values constant
  -- Use abbreviation for readability
  let ρ := Etingof.GL2.principalSeriesRep p n chi1 chi2
  set avg := ∑ s : GaloisField p n, ρ (Etingof.GL2.translationElt p n s) f' with avg_def
  have havgS : avg ∈ S.toSubmodule :=
    S.toSubmodule.sum_mem (fun s _ => S.apply_mem_toSubmodule _ hf'S)
  -- Key: avg.val evaluated pointwise
  have hval : ∀ x, avg.val x =
      ∑ s : GaloisField p n, (ρ (Etingof.GL2.translationElt p n s) f').val x := by
    intro x
    have : (Submodule.subtype _ avg) x =
        ∑ s, (Submodule.subtype _ (ρ (Etingof.GL2.translationElt p n s) f')) x := by
      rw [show Submodule.subtype _ avg = Submodule.subtype _
        (∑ s, ρ (Etingof.GL2.translationElt p n s) f') from rfl, map_sum]
      simp [Finset.sum_apply]
    exact this
  -- avg(rep(none)) = q · f'(rep(none))
  have havg_none : avg.val (Etingof.GL2.cosetRep p n none) =
      (Fintype.card (GaloisField p n) : ℂ) * f'.val (Etingof.GL2.cosetRep p n none) := by
    rw [hval]
    conv_lhs => arg 2; ext s
                rw [Etingof.GL2.action_translation_none p n chi1 chi2 f' s]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  -- avg(rep(some t)) = ∑_u f'(rep(some u)) (independent of t)
  have havg_some_const : ∀ t : GaloisField p n,
      avg.val (Etingof.GL2.cosetRep p n (some t)) =
      ∑ u : GaloisField p n, f'.val (Etingof.GL2.cosetRep p n (some u)) := by
    intro t; rw [hval]
    conv_lhs => arg 2; ext s
                rw [Etingof.GL2.action_translation_some p n chi1 chi2 f' s t]
    exact Fintype.sum_equiv (Equiv.addLeft t) _ _ (fun s => rfl)
  -- Step 3: ρ(δ_c)(avg) - χ₂(c) · avg kills the "some" part
  have ⟨c, hc⟩ : ∃ c : (GaloisField p n)ˣ, chi1 c ≠ chi2 c := by
    by_contra h; push_neg at h; exact hne (MonoidHom.ext h)
  set g := ρ (Etingof.GL2.diagElt p n c) avg - (chi2 c : ℂ) • avg
  refine ⟨g, ?_, ?_, ?_⟩
  · -- g ∈ S
    exact S.toSubmodule.sub_mem (S.apply_mem_toSubmodule _ havgS)
      (S.toSubmodule.smul_mem _ havgS)
  · -- g(rep(none)) ≠ 0: g(rep(none)) = (χ₁(c) - χ₂(c)) · q · f'(rep(none))
    intro heq
    -- Compute g(rep(none))
    have hgval : g.val (Etingof.GL2.cosetRep p n none) =
        ((chi1 c : ℂ) - (chi2 c : ℂ)) * ((Fintype.card (GaloisField p n) : ℂ) *
          f'.val (Etingof.GL2.cosetRep p n none)) := by
      show (ρ (Etingof.GL2.diagElt p n c) avg - (chi2 c : ℂ) • avg).val
        (Etingof.GL2.cosetRep p n none) = _
      simp only [Submodule.coe_sub, Submodule.coe_smul, Pi.sub_apply, Pi.smul_apply,
        smul_eq_mul]
      rw [Etingof.GL2.action_diagonal_none p n chi1 chi2 avg c, havg_none]
      ring
    rw [hgval] at heq
    -- (χ₁(c) - χ₂(c)) · q · f'(none) = 0, but all three factors are nonzero
    rcases mul_eq_zero.mp heq with hsub | hprod
    · exact hc (Units.val_injective (sub_eq_zero.mp hsub))
    · rcases mul_eq_zero.mp hprod with hq | hf
      · exact (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) hq
      · exact hf'none hf
  · -- g(rep(some t)) = 0: diagonal and averaging cancel
    intro t
    show (ρ (Etingof.GL2.diagElt p n c) avg - (chi2 c : ℂ) • avg).val
      (Etingof.GL2.cosetRep p n (some t)) = 0
    simp only [Submodule.coe_sub, Submodule.coe_smul, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul]
    rw [Etingof.GL2.action_diagonal_some p n chi1 chi2 avg c t,
      havg_some_const (t * ↑c⁻¹), havg_some_const t]
    ring

/-- From a delta function at rep(none), the Weyl element produces a delta at rep(some 0),
    and translations produce deltas at any rep(some s). Together these span V,
    so S = ⊤. -/
private lemma Etingof.GL2.principalSeries_delta_spans_top
    (chi1 chi2 : (GaloisField p n)ˣ →* ℂˣ)
    (S : Subrepresentation (Etingof.GL2.principalSeriesRep p n chi1 chi2))
    (g : ↥(Etingof.GL2.principalSeriesSubmodule p n chi1 chi2))
    (hgS : g ∈ S.toSubmodule)
    (hgnone : g.val (Etingof.GL2.cosetRep p n none) ≠ 0)
    (hgsome : ∀ t, g.val (Etingof.GL2.cosetRep p n (some t)) = 0) :
    S = ⊤ := by
  sorry

/-- V(χ₁, χ₂) is irreducible when χ₁ ≠ χ₂.

Direct proof: any nonzero G-stable subspace S contains a function
supported only at rep(∞) (using translations, diagonal scaling,
and character orthogonality ∑(χ₁/χ₂)(c) = 0). Then the Weyl element
and translations generate all basis functions. -/
private lemma Etingof.GL2.principalSeries_simple_of_ne
    (chi1 chi2 : (GaloisField p n)ˣ →* ℂˣ) (hne : chi1 ≠ chi2) :
    Simple (Etingof.GL2.principalSeries p n chi1 chi2) := by
  haveI : NeZero (Nat.card (GL2 p n) : ℂ) := ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  set ρ := Etingof.GL2.principalSeriesRep p n chi1 chi2
  -- Bridge: IsSimpleModule → Simple FDRep
  suffices IsSimpleModule (MonoidAlgebra ℂ (GL2 p n)) ρ.asModule by
    haveI := this; exact simple_of_isSimpleModule_FDRep ρ
  rw [← Representation.irreducible_iff_isSimpleModule_asModule]
  -- Now need: IsSimpleOrder (Subrepresentation ρ)
  -- The representation space is nonzero and every nonzero G-stable subspace is the whole space.
  -- Proof strategy:
  -- 1. Take nonzero f ∈ S. If f(rep(none)) = 0, apply Weyl·τ to get f' with f'(rep(none)) ≠ 0.
  -- 2. Average ∑_s ρ(τ_s)(f') makes the "some" values constant. Then
  --    ρ(δ_c)(avg) - χ₂(c)·avg kills the "some" part, leaving a delta at rep(none).
  -- 3. Apply w to get delta at rep(some 0), then τ_s for deltas at all rep(some s).
  -- 4. These span V by principalSeries_eval_injective, so S = ⊤.
  haveI : Nontrivial (Subrepresentation ρ) :=
    Etingof.GL2.principalSeries_nontrivial p n chi1 chi2
  exact IsSimpleOrder.mk fun S => by
    by_cases hS : S = ⊥
    · exact Or.inl hS
    · right
      -- S ≠ ⊥ → ∃ nonzero f ∈ S
      have hSne : S.toSubmodule ≠ ⊥ := by
        intro heq; apply hS
        exact Subrepresentation.toSubmodule_injective heq
      rw [ne_eq, Submodule.eq_bot_iff] at hSne; push_neg at hSne
      obtain ⟨f, hfS, hfne⟩ := hSne
      -- Construct delta at none, deltas at all some, show they span
      obtain ⟨g, hgS, hgnone, hgsome⟩ :=
        Etingof.GL2.principalSeries_construct_delta_none p n chi1 chi2 hne S f hfS hfne
      exact Etingof.GL2.principalSeries_delta_spans_top p n chi1 chi2 S g hgS hgnone hgsome

/-- **Theorem 5.25.2 (1)**: If χ₁ ≠ χ₂, the principal series representation
V(χ₁, χ₂) is irreducible. (Etingof Theorem 5.25.2) -/
theorem Etingof.Theorem5_25_2_part1
    (chi1 chi2 : (GaloisField p n)ˣ →* ℂˣ) (hne : chi1 ≠ chi2) :
    Simple (Etingof.GL2.principalSeries p n chi1 chi2) :=
  Etingof.GL2.principalSeries_simple_of_ne p n chi1 chi2 hne

/-- For any values on coset representatives, there exists a covariant function realizing them. -/
private lemma Etingof.GL2.principalSeries_eval_surjective
    (chi1 chi2 : (GaloisField p n)ˣ →* ℂˣ)
    (c : Option (GaloisField p n) → ℂ) :
    ∃ f : ↥(Etingof.GL2.principalSeriesSubmodule p n chi1 chi2),
      ∀ i, (f : GL2 p n → ℂ) (Etingof.GL2.cosetRep p n i) = c i := by
  sorry

/-- Evaluation at coset reps restricted to complementW is injective into GaloisField → ℂ.
    Key: if f(rep(some t)) = 0 for all t AND aug(f) = 0, then f(rep(none)) = 0 too. -/
private lemma Etingof.GL2.complementW_eval_injective
    (mu : (GaloisField p n)ˣ →* ℂˣ)
    (f : ↥(Etingof.GL2.complementWSubmodule p n mu))
    (hf : ∀ t : GaloisField p n,
      (f : GL2 p n → ℂ) (Etingof.GL2.cosetRep p n (some t)) = 0) :
    f = 0 := by
  sorry

/-- Evaluation at "some" coset reps from complementW is surjective onto GaloisField → ℂ. -/
private lemma Etingof.GL2.complementW_eval_surjective
    (mu : (GaloisField p n)ˣ →* ℂˣ)
    (c : GaloisField p n → ℂ) :
    ∃ f : ↥(Etingof.GL2.complementWSubmodule p n mu),
      ∀ t, (f : GL2 p n → ℂ) (Etingof.GL2.cosetRep p n (some t)) = c t := by
  sorry

/-- dim V(χ₁,χ₂) = [G:B] = p^n + 1. -/
private lemma Etingof.GL2.principalSeriesSubmodule_finrank
    (chi1 chi2 : (GaloisField p n)ˣ →* ℂˣ) :
    Module.finrank ℂ ↥(Etingof.GL2.principalSeriesSubmodule p n chi1 chi2) = p ^ n + 1 := by
  sorry

/-- The determinant character g ↦ μ(det g) is in the principal series submodule for (μ,μ). -/
private lemma Etingof.GL2.detFun_mem_principalSeries
    (mu : (GaloisField p n)ˣ →* ℂˣ) :
    (fun g : GL2 p n => (mu (Matrix.GeneralLinearGroup.det g) : ℂ)) ∈
      Etingof.GL2.principalSeriesSubmodule p n mu mu := by
  intro b g
  simp only [Etingof.GL2.borelCharValue]
  -- LHS: μ(det(b·g)) = μ(det(b)) · μ(det(g))
  rw [show Matrix.GeneralLinearGroup.det (b.val * g) =
    Matrix.GeneralLinearGroup.det b.val * Matrix.GeneralLinearGroup.det g from map_mul _ _ _,
    map_mul, Units.val_mul]
  -- Need: μ(det(b)) = μ(b₀₀) · μ(b₁₁) since det(b) = b₀₀·b₁₁ for upper triangular b
  congr 1
  have hb10 : (b.val.val : Matrix (Fin 2) (Fin 2) (GaloisField p n)) 1 0 = 0 := b.prop
  have hdet_eq : (Matrix.GeneralLinearGroup.det b.val : GaloisField p n) =
      (b.val.val : Matrix _ _ _) 0 0 * (b.val.val : Matrix _ _ _) 1 1 := by
    show (b.val.val : Matrix _ _ _).det = _
    rw [Matrix.det_fin_two, hb10, mul_zero, sub_zero]
  have : Matrix.GeneralLinearGroup.det b.val =
      Units.mk0 ((b.val.val : Matrix _ _ _) 0 0) (Etingof.GL2.borel_diag00_ne_zero p n b) *
      Units.mk0 ((b.val.val : Matrix _ _ _) 1 1) (Etingof.GL2.borel_diag11_ne_zero p n b) := by
    ext; simp [hdet_eq]
  rw [this, map_mul, Units.val_mul]

/-- Augmentation of μ∘det equals |G|, hence is nonzero. -/
private lemma Etingof.GL2.augmentation_detFun_ne_zero
    (mu : (GaloisField p n)ˣ →* ℂˣ) :
    Etingof.GL2.augmentation p n mu
      (fun g : GL2 p n => (mu (Matrix.GeneralLinearGroup.det g) : ℂ)) ≠ 0 := by
  -- aug(μ∘det) = ∑_g μ(det g) · μ(det g)⁻¹ = ∑_g 1 = |G|
  simp only [Etingof.GL2.augmentation, LinearMap.coe_mk, AddHom.coe_mk]
  have hone : ∀ g : GL2 p n,
      (mu (Matrix.GeneralLinearGroup.det g) : ℂ) *
      ↑(mu (Matrix.GeneralLinearGroup.det g))⁻¹ = 1 := fun g => by
    rw [Units.val_inv_eq_inv_val, mul_inv_cancel₀ (Units.ne_zero _)]
  simp_rw [hone, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero

/-- The augmentation restricted to the principal series submodule, as a linear map. -/
private noncomputable def Etingof.GL2.augOnPrincipalSeries
    (mu : (GaloisField p n)ˣ →* ℂˣ) :
    ↥(Etingof.GL2.principalSeriesSubmodule p n mu mu) →ₗ[ℂ] ℂ :=
  (Etingof.GL2.augmentation p n mu).comp (Submodule.subtype _)

/-- The kernel of augmentation restricted to principal series equals
    the complement W_μ submodule. -/
private lemma Etingof.GL2.ker_augOnPrincipalSeries_eq
    (mu : (GaloisField p n)ˣ →* ℂˣ) :
    LinearMap.ker (Etingof.GL2.augOnPrincipalSeries p n mu) =
      (Etingof.GL2.complementWSubmodule p n mu).comap
        (Submodule.subtype (Etingof.GL2.principalSeriesSubmodule p n mu mu)) := by
  ext ⟨f, hf⟩
  simp only [LinearMap.mem_ker, Submodule.mem_comap,
    Etingof.GL2.augOnPrincipalSeries, LinearMap.comp_apply,
    Etingof.GL2.complementWSubmodule, Submodule.mem_inf, LinearMap.mem_ker]
  exact ⟨fun h => ⟨hf, h⟩, fun ⟨_, h⟩ => h⟩

/-- The augmentation restricted to principal series is surjective (onto ℂ). -/
private lemma Etingof.GL2.augOnPrincipalSeries_surjective
    (mu : (GaloisField p n)ˣ →* ℂˣ) :
    Function.Surjective (Etingof.GL2.augOnPrincipalSeries p n mu) := by
  -- The det function μ∘det has nonzero augmentation, so the map is surjective onto ℂ
  intro c
  have hdetMem := Etingof.GL2.detFun_mem_principalSeries p n mu
  set detFn : ↥(Etingof.GL2.principalSeriesSubmodule p n mu mu) :=
    ⟨fun g => (mu (Matrix.GeneralLinearGroup.det g) : ℂ), hdetMem⟩
  have haugNe := Etingof.GL2.augmentation_detFun_ne_zero p n mu
  set a := Etingof.GL2.augOnPrincipalSeries p n mu detFn with ha_def
  refine ⟨(c / a) • detFn, ?_⟩
  simp only [map_smul, smul_eq_mul]
  have ha_ne : a ≠ 0 := haugNe
  exact div_mul_cancel₀ c ha_ne

/-- The augmentation is equivariant: aug(ρ(g)f) = μ(det g) · aug(f). -/
private lemma Etingof.GL2.augOnPrincipalSeries_equivariant
    (mu : (GaloisField p n)ˣ →* ℂˣ)
    (g : GL2 p n)
    (f : ↥(Etingof.GL2.principalSeriesSubmodule p n mu mu)) :
    Etingof.GL2.augOnPrincipalSeries p n mu
      (Etingof.GL2.principalSeriesRep p n mu mu g f) =
    ((mu (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
      Etingof.GL2.augOnPrincipalSeries p n mu f := by
  simp only [Etingof.GL2.augOnPrincipalSeries, LinearMap.comp_apply,
    Etingof.GL2.augmentation, LinearMap.coe_mk, AddHom.coe_mk,
    Submodule.coe_subtype]
  -- LHS: ∑_x f(xg) · μ(det x)⁻¹. Reindex x ↦ xg⁻¹.
  change ∑ x : GL2 p n, f.val (x * g) * ↑(mu (Matrix.GeneralLinearGroup.det x))⁻¹ =
    ↑(mu (Matrix.GeneralLinearGroup.det g)) *
    (∑ x : GL2 p n, f.val x * ↑(mu (Matrix.GeneralLinearGroup.det x))⁻¹)
  conv_lhs =>
    rw [Fintype.sum_equiv (Equiv.mulRight g)
        (fun x => f.val (x * g) * ↑(mu (Matrix.GeneralLinearGroup.det x))⁻¹)
        (fun x => f.val x * ↑(mu (Matrix.GeneralLinearGroup.det (x * g⁻¹)))⁻¹)
        (fun x => by simp [Equiv.mulRight])]
  simp_rw [map_mul, mul_inv_rev, Units.val_mul]
  simp_rw [show ∀ x : GL2 p n,
      f.val x * (↑(mu (Matrix.GeneralLinearGroup.det g⁻¹))⁻¹ *
      ↑(mu (Matrix.GeneralLinearGroup.det x))⁻¹) =
      f.val x * ↑(mu (Matrix.GeneralLinearGroup.det x))⁻¹ *
      ↑(mu (Matrix.GeneralLinearGroup.det g⁻¹))⁻¹ from fun x => by ring]
  rw [← Finset.sum_mul, mul_comm]
  congr 1
  -- μ(det g⁻¹)⁻¹ = μ(det g)
  rw [map_inv, map_inv, inv_inv]

/-- The augmentation as a G-equivariant map V(μ,μ) ⟶ ℂ_μ in FDRep. -/
private noncomputable def Etingof.GL2.augMorphism
    (mu : (GaloisField p n)ˣ →* ℂˣ) :
    Etingof.GL2.principalSeries p n mu mu ⟶ Etingof.GL2.detChar p n mu where
  hom := FGModuleCat.ofHom (Etingof.GL2.augOnPrincipalSeries p n mu)
  comm g := by
    apply FGModuleCat.hom_ext
    ext ⟨f, hf⟩
    show Etingof.GL2.augOnPrincipalSeries p n mu
      (Etingof.GL2.principalSeriesRep p n mu mu g ⟨f, hf⟩) =
      ((mu (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
        Etingof.GL2.augOnPrincipalSeries p n mu ⟨f, hf⟩
    exact Etingof.GL2.augOnPrincipalSeries_equivariant p n mu g ⟨f, hf⟩

/-- The inclusion W_μ ↪ V(μ,μ) in FDRep. -/
private noncomputable def Etingof.GL2.complementWInclusion
    (mu : (GaloisField p n)ˣ →* ℂˣ) :
    Etingof.GL2.complementW p n mu ⟶ Etingof.GL2.principalSeries p n mu mu where
  hom := FGModuleCat.ofHom
    { toFun := fun ⟨f, hf⟩ => ⟨f, hf.1⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  comm g := by
    ext ⟨f, hf⟩; rfl

/-- The embedding ℂ_μ ↪ V(μ,μ) sending c to c · (g ↦ μ(det g)) in FDRep. -/
private noncomputable def Etingof.GL2.detCharEmbedding
    (mu : (GaloisField p n)ˣ →* ℂˣ) :
    Etingof.GL2.detChar p n mu ⟶ Etingof.GL2.principalSeries p n mu mu where
  hom := FGModuleCat.ofHom
    { toFun := fun c =>
        ⟨fun g => c * (mu (Matrix.GeneralLinearGroup.det g) : ℂ),
         fun b g => by
           have := Etingof.GL2.detFun_mem_principalSeries p n mu b g
           simp only [Etingof.GL2.borelCharValue] at this ⊢; rw [this]; ring⟩
      map_add' := fun _ _ => Subtype.ext (funext fun _ => by simp [add_mul])
      map_smul' := fun _ _ => Subtype.ext (funext fun _ => by simp [mul_assoc]) }
  comm g := by
    apply FGModuleCat.hom_ext; ext1
    apply Subtype.ext; funext x
    -- Both sides reduce to μ(det g) * μ(det x) vs μ(det(x*g))
    show ((mu (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) • (1 : ℂ) *
      ↑(mu (Matrix.GeneralLinearGroup.det x)) =
      1 * ↑(mu (Matrix.GeneralLinearGroup.det (x * g)))
    simp only [smul_eq_mul, mul_one, one_mul, map_mul, Units.val_mul]; ring

/-- ℂ_μ is a simple (1-dimensional) representation. -/
private def Etingof.GL2.detCharRep
    (mu : (GaloisField p n)ˣ →* ℂˣ) :
    Representation ℂ (GL2 p n) ℂ where
  toFun g := ((mu (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) • LinearMap.id
  map_one' := by ext; simp
  map_mul' a b := by
    apply LinearMap.ext; intro x
    change ((mu (Matrix.GeneralLinearGroup.det (a * b)) : ℂˣ) : ℂ) * x =
      ((mu (Matrix.GeneralLinearGroup.det a) : ℂˣ) : ℂ) *
      (((mu (Matrix.GeneralLinearGroup.det b) : ℂˣ) : ℂ) * x)
    rw [map_mul, map_mul, Units.val_mul, mul_assoc]

private lemma Etingof.GL2.detChar_eq_of
    (mu : (GaloisField p n)ˣ →* ℂˣ) :
    Etingof.GL2.detChar p n mu = FDRep.of (Etingof.GL2.detCharRep p n mu) := rfl

private lemma Etingof.GL2.detChar_simple
    (mu : (GaloisField p n)ˣ →* ℂˣ) :
    Simple (Etingof.GL2.detChar p n mu) := by
  haveI : NeZero (Nat.card (GL2 p n) : ℂ) :=
    ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  rw [Etingof.GL2.detChar_eq_of]
  let ρ := Etingof.GL2.detCharRep p n mu
  haveI : IsSimpleModule (MonoidAlgebra ℂ (GL2 p n)) ρ.asModule := by
    rw [isSimpleModule_iff]
    exact is_simple_module_of_finrank_eq_one (Module.finrank_self ℂ)
  haveI : Simple (ModuleCat.of (MonoidAlgebra ℂ (GL2 p n)) ρ.asModule) :=
    simple_of_isSimpleModule
  let E := Rep.equivalenceModuleMonoidAlgebra (k := ℂ) (G := GL2 p n)
  haveI : Simple
      (E.functor.obj ((forget₂ (FDRep ℂ (GL2 p n)) (Rep ℂ (GL2 p n))).obj
        (FDRep.of ρ))) := by
    change Simple (ModuleCat.of (MonoidAlgebra ℂ (GL2 p n)) ρ.asModule)
    infer_instance
  haveI : Simple ((forget₂ (FDRep ℂ (GL2 p n)) (Rep ℂ (GL2 p n))).obj (FDRep.of ρ)) :=
    simple_of_full_faithful_preservesMono' E.functor _
  exact simple_of_full_faithful_preservesMono' (forget₂ (FDRep ℂ (GL2 p n)) (Rep ℂ (GL2 p n))) _

/-- The linear map underlying the embedding sends c to ⟨g ↦ c·μ(det g), _⟩. -/
private def Etingof.GL2.detCharEmbedding_linearMap
    (mu : (GaloisField p n)ˣ →* ℂˣ) :
    ℂ →ₗ[ℂ] ↥(Etingof.GL2.principalSeriesSubmodule p n mu mu) where
  toFun c := ⟨fun g => c * (mu (Matrix.GeneralLinearGroup.det g) : ℂ),
    fun b g => by
      have := Etingof.GL2.detFun_mem_principalSeries p n mu b g
      simp only [Etingof.GL2.borelCharValue] at this ⊢; rw [this]; ring⟩
  map_add' a b := Subtype.ext (funext fun _ => by simp [add_mul])
  map_smul' r c := Subtype.ext (funext fun _ => by simp [mul_assoc])

/-- aug ∘ emb(c) = c · |G| (at the linear map level). -/
private lemma Etingof.GL2.aug_comp_emb_eq
    (mu : (GaloisField p n)ˣ →* ℂˣ) (c : ℂ) :
    Etingof.GL2.augOnPrincipalSeries p n mu
      (Etingof.GL2.detCharEmbedding_linearMap p n mu c) =
    c * (Fintype.card (GL2 p n) : ℂ) := by
  simp only [Etingof.GL2.augOnPrincipalSeries, LinearMap.comp_apply,
    Etingof.GL2.augmentation, Etingof.GL2.detCharEmbedding_linearMap,
    LinearMap.coe_mk, AddHom.coe_mk, Submodule.coe_subtype]
  simp_rw [show ∀ g : GL2 p n,
      c * ↑(mu (Matrix.GeneralLinearGroup.det g)) *
      ↑(mu (Matrix.GeneralLinearGroup.det g))⁻¹ = c from fun g => by
    rw [mul_assoc, Units.val_inv_eq_inv_val, mul_inv_cancel₀ (Units.ne_zero _), mul_one]]
  simp [Finset.sum_const, Finset.card_univ, mul_comm]

/-- The embedding ℂ_μ ↪ V(μ,μ) is nonzero. -/
private lemma Etingof.GL2.detCharEmbedding_ne_zero
    (mu : (GaloisField p n)ˣ →* ℂˣ) :
    Etingof.GL2.detCharEmbedding p n mu ≠ 0 := by
  -- It suffices to show the underlying linear map is nonzero
  -- emb(1) = (g ↦ μ(det g)) which evaluated at g=1 gives μ(1) = 1 ≠ 0
  intro h
  -- Extract: if emb = 0 in FDRep, the linear map sends 1 to 0
  have h1 : (Etingof.GL2.detCharEmbedding_linearMap p n mu 1).val (1 : GL2 p n) = 0 := by
    -- The detCharEmbedding is built from detCharEmbedding_linearMap
    -- If emb = 0, then emb.hom.hom = 0, so detCharEmbedding_linearMap = 0
    have hlin : Etingof.GL2.detCharEmbedding_linearMap p n mu = 0 := by
      have hh : (Etingof.GL2.detCharEmbedding p n mu).hom = 0 := by
        rw [h]; exact Action.zero_hom
      ext x
      -- Goal: ↑(detCharEmbedding_linearMap ... 1) x = 0
      -- This equals μ(det x) = 0, derivable from hh
      -- detCharEmbedding.hom = FGModuleCat.ofHom {toFun := detCharEmbedding_linearMap ...}
      -- So hh tells us FGModuleCat.ofHom(detCharEmbedding_linearMap) = 0
      -- Extract: (FGModuleCat.ofHom f).hom.hom = f as a function
      have key : ∀ (c : ℂ) (g : GL2 p n),
          (Etingof.GL2.detCharEmbedding_linearMap p n mu c).val g =
          (ConcreteCategory.hom
            (Etingof.GL2.detCharEmbedding p n mu).hom.hom c :
            ↥(Etingof.GL2.principalSeriesSubmodule p n mu mu)).val g := by
        intro c g; rfl
      rw [key 1 x, hh]
      -- Goal: ↑((ConcreteCategory.hom (InducedCategory.Hom.hom 0)) 1) x = 0
      rfl
    simp [hlin]
  -- But emb(1) at g=1 is 1·μ(det 1) = μ(1) = 1
  simp [Etingof.GL2.detCharEmbedding_linearMap] at h1

/-- The embedding ℂ_μ ↪ V(μ,μ) is mono (injective). -/
private lemma Etingof.GL2.detCharEmbedding_mono
    (mu : (GaloisField p n)ˣ →* ℂˣ) :
    Mono (Etingof.GL2.detCharEmbedding p n mu) := by
  haveI := Etingof.GL2.detChar_simple p n mu
  exact mono_of_nonzero_from_simple (Etingof.GL2.detCharEmbedding_ne_zero p n mu)

set_option maxHeartbeats 4000000 in
/-- The projection V(μ,μ) → W_μ: f ↦ f − (aug(f)/|G|)·(μ∘det), as a morphism in FDRep. -/
private noncomputable def Etingof.GL2.complementWProjection
    (mu : (GaloisField p n)ˣ →* ℂˣ) :
    Etingof.GL2.principalSeries p n mu mu ⟶ Etingof.GL2.complementW p n mu where
  hom := FGModuleCat.ofHom
    { toFun := fun ⟨f, hf⟩ =>
        let c := (Fintype.card (GL2 p n) : ℂ)⁻¹ *
          Etingof.GL2.augOnPrincipalSeries p n mu ⟨f, hf⟩
        ⟨fun g => f g - c * (mu (Matrix.GeneralLinearGroup.det g) : ℂ),
         ⟨fun b g' => by
            have hcov := hf b g'
            have hdet := Etingof.GL2.detFun_mem_principalSeries p n mu b g'
            simp only [Etingof.GL2.borelCharValue] at hcov hdet ⊢
            rw [hcov, hdet]; ring,
          by
            show (fun g => f g - (Fintype.card (GL2 p n) : ℂ)⁻¹ *
              Etingof.GL2.augOnPrincipalSeries p n mu ⟨f, hf⟩ *
              ↑(mu (Matrix.GeneralLinearGroup.det g))) ∈
              LinearMap.ker (Etingof.GL2.augmentation p n mu)
            rw [LinearMap.mem_ker]
            simp only [Etingof.GL2.augmentation, LinearMap.coe_mk, AddHom.coe_mk]
            simp_rw [sub_mul, Finset.sum_sub_distrib]
            simp_rw [show ∀ g : GL2 p n,
              (Fintype.card (GL2 p n) : ℂ)⁻¹ *
                Etingof.GL2.augOnPrincipalSeries p n mu ⟨f, hf⟩ *
                ↑(mu (Matrix.GeneralLinearGroup.det g)) *
                ↑(mu (Matrix.GeneralLinearGroup.det g))⁻¹ =
              (Fintype.card (GL2 p n) : ℂ)⁻¹ *
                Etingof.GL2.augOnPrincipalSeries p n mu ⟨f, hf⟩ from fun g => by
              rw [mul_assoc, mul_assoc, Units.val_inv_eq_inv_val,
                mul_inv_cancel₀ (Units.ne_zero _), mul_one]]
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
              ← mul_assoc, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero),
              one_mul]
            simp only [Etingof.GL2.augOnPrincipalSeries, Etingof.GL2.augmentation,
              LinearMap.comp_apply, Submodule.coe_subtype,
              LinearMap.coe_mk, AddHom.coe_mk, sub_self]⟩⟩
      map_add' := fun ⟨a, ha⟩ ⟨b, hb⟩ => by
        apply Subtype.ext; funext g
        simp only [Etingof.GL2.augOnPrincipalSeries, LinearMap.comp_apply,
          Submodule.coe_subtype, Submodule.coe_add, Pi.add_apply, LinearMap.map_add]
        ring
      map_smul' := fun r ⟨a, ha⟩ => by
        apply Subtype.ext; funext g
        simp only [smul_eq_mul, Etingof.GL2.augOnPrincipalSeries, LinearMap.comp_apply,
          Submodule.coe_subtype, Submodule.coe_smul, Pi.smul_apply, RingHom.id_apply,
          LinearMap.map_smul]
        ring }
  comm g := by
    apply FGModuleCat.hom_ext; ext ⟨f, hf⟩
    apply Subtype.ext; funext x
    -- Both sides reduce to f(xg) - (1/|G|)·aug(f)·μ(det g)·μ(det x)
    sorry

/-- The scaled augmentation (1/|G|)·aug as a morphism V(μ,μ) → ℂ_μ in FDRep. -/
private noncomputable def Etingof.GL2.scaledAugMorphism
    (mu : (GaloisField p n)ˣ →* ℂˣ) :
    Etingof.GL2.principalSeries p n mu mu ⟶ Etingof.GL2.detChar p n mu where
  hom := FGModuleCat.ofHom
    ((Fintype.card (GL2 p n) : ℂ)⁻¹ • Etingof.GL2.augOnPrincipalSeries p n mu)
  comm g := by
    apply FGModuleCat.hom_ext; ext ⟨f, hf⟩
    change (Fintype.card (GL2 p n) : ℂ)⁻¹ *
      Etingof.GL2.augOnPrincipalSeries p n mu
        (Etingof.GL2.principalSeriesRep p n mu mu g ⟨f, hf⟩) =
      ((mu (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
        ((Fintype.card (GL2 p n) : ℂ)⁻¹ *
          Etingof.GL2.augOnPrincipalSeries p n mu ⟨f, hf⟩)
    rw [Etingof.GL2.augOnPrincipalSeries_equivariant]; ring

/-- emb ≫ scaledAug = 𝟙: the scaled augmentation retracts the embedding. -/
private lemma Etingof.GL2.emb_comp_scaledAug_eq_id
    (mu : (GaloisField p n)ˣ →* ℂˣ) :
    Etingof.GL2.detCharEmbedding p n mu ≫
      Etingof.GL2.scaledAugMorphism p n mu = 𝟙 _ := by
  refine Action.Hom.ext (FGModuleCat.hom_ext (LinearMap.ext (fun c => ?_)))
  -- (emb ≫ scaledAug)(c) = (1/|G|) · aug(emb(c)) = (1/|G|) · c · |G| = c
  show (Fintype.card (GL2 p n) : ℂ)⁻¹ *
    Etingof.GL2.augOnPrincipalSeries p n mu
      (Etingof.GL2.detCharEmbedding_linearMap p n mu c) = c
  rw [Etingof.GL2.aug_comp_emb_eq]
  field_simp

/-- The total condition: scaledAug ≫ emb + proj ≫ incl = 𝟙 V. -/
private lemma Etingof.GL2.total_condition
    (mu : (GaloisField p n)ˣ →* ℂˣ) :
    Etingof.GL2.scaledAugMorphism p n mu ≫ Etingof.GL2.detCharEmbedding p n mu +
      Etingof.GL2.complementWProjection p n mu ≫ Etingof.GL2.complementWInclusion p n mu =
      𝟙 _ := by
  refine Action.Hom.ext (FGModuleCat.hom_ext (LinearMap.ext (fun ⟨f, hf⟩ => ?_)))
  apply Subtype.ext; funext g
  show ((Fintype.card (GL2 p n) : ℂ)⁻¹ *
    Etingof.GL2.augOnPrincipalSeries p n mu ⟨f, hf⟩) *
    ↑(mu (Matrix.GeneralLinearGroup.det g)) +
    (f g - (Fintype.card (GL2 p n) : ℂ)⁻¹ *
      Etingof.GL2.augOnPrincipalSeries p n mu ⟨f, hf⟩ *
      ↑(mu (Matrix.GeneralLinearGroup.det g))) = f g
  ring

/-- emb ≫ proj = 0: the projection kills the image of the embedding. -/
private lemma Etingof.GL2.emb_comp_proj_eq_zero
    (mu : (GaloisField p n)ˣ →* ℂˣ) :
    Etingof.GL2.detCharEmbedding p n mu ≫ Etingof.GL2.complementWProjection p n mu = 0 := by
  apply Action.Hom.ext
  simp only [Action.comp_hom, Action.zero_hom]
  apply FGModuleCat.hom_ext
  ext c
  -- c = 1 since detChar is ℂ as a 1-dim module
  -- Need: (emb ≫ proj)(1) = 0 in complementW
  apply Subtype.ext; funext g
  -- LHS: emb(1)(g) = μ(det g), then proj subtracts (1/|G|)*aug(emb(1))*μ(det g)
  -- aug(emb(1)) = |G|, so proj(emb(1))(g) = μ(det g) - μ(det g) = 0
  show (1 : ℂ) * ↑(mu (Matrix.GeneralLinearGroup.det g)) -
    (Fintype.card (GL2 p n) : ℂ)⁻¹ *
      Etingof.GL2.augOnPrincipalSeries p n mu
        (Etingof.GL2.detCharEmbedding_linearMap p n mu (1 : ℂ)) *
      ↑(mu (Matrix.GeneralLinearGroup.det g)) = 0
  rw [Etingof.GL2.aug_comp_emb_eq, one_mul, one_mul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero), one_mul, sub_self]

/-- incl ≫ proj = 𝟙: the projection is a retraction of the inclusion. -/
private lemma Etingof.GL2.incl_comp_proj_eq_id
    (mu : (GaloisField p n)ˣ →* ℂˣ) :
    Etingof.GL2.complementWInclusion p n mu ≫
      Etingof.GL2.complementWProjection p n mu = 𝟙 _ := by
  refine Action.Hom.ext (FGModuleCat.hom_ext (LinearMap.ext (fun ⟨f, hf⟩ => ?_)))
  apply Subtype.ext; funext g
  show f g - (Fintype.card (GL2 p n) : ℂ)⁻¹ *
    Etingof.GL2.augOnPrincipalSeries p n mu ⟨f, hf.1⟩ *
    ↑(mu (Matrix.GeneralLinearGroup.det g)) = f g
  have hker : Etingof.GL2.augOnPrincipalSeries p n mu ⟨f, hf.1⟩ = 0 := by
    simp only [Etingof.GL2.augOnPrincipalSeries, LinearMap.comp_apply, Submodule.coe_subtype]
    exact hf.2
  rw [hker, mul_zero, zero_mul, sub_zero]

/-- V(μ,μ) decomposes as ℂ_μ ⊕ W_μ in FDRep. -/
private lemma Etingof.GL2.principalSeries_decomp
    (mu : (GaloisField p n)ˣ →* ℂˣ) :
    Nonempty (Etingof.GL2.principalSeries p n mu mu ≅
      Etingof.GL2.detChar p n mu ⊞ Etingof.GL2.complementW p n mu) := by
  -- Step 1: ℂ_μ is simple and the embedding is nonzero → mono → split mono (Maschke)
  haveI : Simple (Etingof.GL2.detChar p n mu) := Etingof.GL2.detChar_simple p n mu
  have hne := Etingof.GL2.detCharEmbedding_ne_zero p n mu
  set emb := Etingof.GL2.detCharEmbedding p n mu
  set incl := Etingof.GL2.complementWInclusion p n mu
  set proj := Etingof.GL2.complementWProjection p n mu
  haveI : Mono emb := Etingof.GL2.detCharEmbedding_mono p n mu
  haveI : NeZero (Nat.card (GL2 p n) : ℂ) := ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  haveI : CategoryTheory.Injective (Etingof.GL2.detChar p n mu) := inferInstance
  haveI : IsSplitMono emb := IsSplitMono.mk'
    ⟨CategoryTheory.Injective.factorThru (𝟙 _) emb,
     CategoryTheory.Injective.comp_factorThru (𝟙 _) emb⟩
  -- Step 2: V(μ,μ) ≅ ℂ_μ ⊞ cokernel(emb)
  have hcok := cokernelIsCokernel emb
  let bc := binaryBiconeOfIsSplitMonoOfCokernel hcok
  have hbl := isBilimitBinaryBiconeOfIsSplitMonoOfCokernel hcok
  haveI : HasBinaryBiproduct (Etingof.GL2.detChar p n mu) (cokernel emb) :=
    HasBinaryBiproduct.mk ⟨bc, hbl⟩
  have iso1 : Etingof.GL2.principalSeries p n mu mu ≅
    Etingof.GL2.detChar p n mu ⊞ cokernel emb :=
    biprod.uniqueUpToIso _ _ hbl
  -- Step 3: Show cokernel(emb) ≅ W_μ using the projection
  -- The projection factors through the cokernel since emb ≫ proj = 0
  let ψ : cokernel emb ⟶ Etingof.GL2.complementW p n mu :=
    cokernel.desc emb proj (Etingof.GL2.emb_comp_proj_eq_zero p n mu)
  -- The composition incl ≫ cokernel.π gives the map W_μ → cokernel(emb)
  let φ : Etingof.GL2.complementW p n mu ⟶ cokernel emb := incl ≫ cokernel.π emb
  -- Show φ ≫ ψ = 𝟙 (using incl ≫ proj = 𝟙)
  have hφψ : φ ≫ ψ = 𝟙 _ := by
    simp only [φ, ψ, Category.assoc, cokernel.π_desc]
    exact Etingof.GL2.incl_comp_proj_eq_id p n mu
  -- Show ψ ≫ φ = 𝟙 (using epi-ness of cokernel.π and total condition)
  have hψφ : ψ ≫ φ = 𝟙 _ := by
    -- proj ≫ incl = 𝟙 - scaledAug ≫ emb (from total condition)
    set sAug := Etingof.GL2.scaledAugMorphism p n mu
    have htotal := Etingof.GL2.total_condition p n mu
    have hpi : proj ≫ incl = 𝟙 _ - sAug ≫ emb := by
      rw [eq_sub_iff_add_eq, add_comm]; exact htotal
    -- Key: proj ≫ incl ≫ cokernel.π = cokernel.π
    have hkey : proj ≫ (incl ≫ cokernel.π emb) = cokernel.π emb := by
      rw [← Category.assoc, hpi, Preadditive.sub_comp, Category.id_comp,
        Category.assoc, cokernel.condition, comp_zero, sub_zero]
    -- cokernel.π is epi, so cancel it
    haveI : Epi (cokernel.π emb) := inferInstance
    apply (cancel_epi (cokernel.π emb)).mp
    rw [Category.comp_id]
    -- LHS: cokernel.π ≫ ψ ≫ φ = (cokernel.π ≫ ψ) ≫ φ = proj ≫ φ = proj ≫ incl ≫ cokernel.π
    conv_lhs => rw [← Category.assoc (cokernel.π emb) ψ φ]
    show (cokernel.π emb ≫ ψ) ≫ φ = cokernel.π emb
    rw [cokernel.π_desc]
    exact hkey
  let cokIso : cokernel emb ≅ Etingof.GL2.complementW p n mu :=
    ⟨ψ, φ, hψφ, hφψ⟩
  exact ⟨iso1.trans (biprod.mapIso (Iso.refl _) cokIso)⟩

/-- W_μ is irreducible. -/
private lemma Etingof.GL2.complementW_simple
    (mu : (GaloisField p n)ˣ →* ℂˣ) :
    Simple (Etingof.GL2.complementW p n mu) := by
  sorry

/-- Helper: dim W_μ = q = p^n. Since dim V(μ,μ) = [G:B] = q+1 and
dim ℂ_μ = 1, we get dim W_μ = q. -/
private lemma Etingof.GL2.complementW_finrank
    (mu : (GaloisField p n)ˣ →* ℂˣ) :
    Module.finrank ℂ (Etingof.GL2.complementW p n mu).V = p ^ n := by
  sorry

/-- **Theorem 5.25.2 (2)**: If χ₁ = χ₂ = μ, then V(μ, μ) ≅ ℂ_μ ⊕ W_μ where
W_μ is an irreducible q-dimensional representation. (Etingof Theorem 5.25.2) -/
theorem Etingof.Theorem5_25_2_part2
    (mu : (GaloisField p n)ˣ →* ℂˣ) :
    (Nonempty (Etingof.GL2.principalSeries p n mu mu ≅
      Etingof.GL2.detChar p n mu ⊞ Etingof.GL2.complementW p n mu)) ∧
    Simple (Etingof.GL2.complementW p n mu) ∧
    Module.finrank ℂ (Etingof.GL2.complementW p n mu).V = p ^ n :=
  ⟨Etingof.GL2.principalSeries_decomp p n mu,
   Etingof.GL2.complementW_simple p n mu,
   Etingof.GL2.complementW_finrank p n mu⟩

/-- Helper: the character of W_μ on diagonal matrices determines μ.
If W_μ ≅ W_ν as representations, then their characters agree on all elements,
and evaluation on diagonal matrices diag(x, 1) recovers μ(x). -/
private lemma Etingof.GL2.complementW_iso_implies_eq
    (mu nu : (GaloisField p n)ˣ →* ℂˣ)
    (iso : Etingof.GL2.complementW p n mu ≅ Etingof.GL2.complementW p n nu) :
    mu = nu := by
  sorry

/-- **Theorem 5.25.2 (3a)**: W_μ ≅ W_ν if and only if μ = ν.
(Etingof Theorem 5.25.2) -/
theorem Etingof.Theorem5_25_2_part3a
    (mu nu : (GaloisField p n)ˣ →* ℂˣ) :
    Nonempty (Etingof.GL2.complementW p n mu ≅ Etingof.GL2.complementW p n nu) ↔
    mu = nu := by
  constructor
  · rintro ⟨iso⟩
    exact Etingof.GL2.complementW_iso_implies_eq p n mu nu iso
  · rintro rfl
    exact ⟨Iso.refl _⟩

/-- **Theorem 5.25.2 (3b)**: V(χ₁, χ₂) ≅ V(χ'₁, χ'₂) if and only if
{χ₁, χ₂} = {χ'₁, χ'₂} (as sets). (Etingof Theorem 5.25.2) -/
theorem Etingof.Theorem5_25_2_part3b
    (chi1 chi2 chi1' chi2' : (GaloisField p n)ˣ →* ℂˣ)
    (hne : chi1 ≠ chi2) (hne' : chi1' ≠ chi2') :
    Nonempty (Etingof.GL2.principalSeries p n chi1 chi2 ≅
      Etingof.GL2.principalSeries p n chi1' chi2') ↔
    ({chi1, chi2} : Set ((GaloisField p n)ˣ →* ℂˣ)) = {chi1', chi2'} := by
  sorry

end Theorem5_25_2

end
