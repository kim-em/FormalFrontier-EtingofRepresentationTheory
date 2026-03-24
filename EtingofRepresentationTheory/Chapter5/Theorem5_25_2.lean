import Mathlib
import EtingofRepresentationTheory.Infrastructure.IrreducibleEnumeration
import EtingofRepresentationTheory.Chapter4.Corollary4_2_4

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

end Theorem5_25_2

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

/-- The Borel component of g in the coset decomposition g = b · rep(idx(g)). -/
private noncomputable def Etingof.GL2.cosetBorel
    (g : GL2 p n) : ↥(Etingof.GL2.BorelSubgroup p n) :=
  if h : (g.val : Matrix (Fin 2) (Fin 2) (GaloisField p n)) 1 0 = 0 then
    ⟨g, h⟩
  else
    let gm := (g.val : Matrix (Fin 2) (Fin 2) (GaloisField p n))
    let bmat : Matrix (Fin 2) (Fin 2) (GaloisField p n) :=
      !![gm.det / gm 1 0, gm 0 0; (0 : _), gm 1 0]
    have hdet : gm.det ≠ 0 := IsUnit.ne_zero ((Units.isUnit g).map Matrix.detMonoidHom)
    have hbdet : bmat.det ≠ 0 := by
      have h10 : gm 1 0 ≠ 0 := h
      have : bmat.det = gm.det := by
        simp [Matrix.det_fin_two, bmat]; field_simp
      rw [this]; exact hdet
    ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero bmat hbdet, by
      change ((Matrix.GeneralLinearGroup.mkOfDetNeZero bmat hbdet).val :
        Matrix (Fin 2) (Fin 2) (GaloisField p n)) 1 0 = 0
      simp [Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.GeneralLinearGroup.mk',
            Matrix.unitOfDetInvertible, bmat]⟩

/-- The coset decomposition: g = cosetBorel(g) · rep(idx(g)). -/
private lemma Etingof.GL2.cosetBorel_mul_cosetRep
    (g : GL2 p n) :
    g = (Etingof.GL2.cosetBorel p n g).val * Etingof.GL2.cosetRep p n (Etingof.GL2.cosetIndex p n g) := by
  unfold Etingof.GL2.cosetBorel Etingof.GL2.cosetIndex Etingof.GL2.cosetRep
  split_ifs with h10
  · simp
  · apply Matrix.GeneralLinearGroup.ext; intro i j
    set gm := (g.val : Matrix (Fin 2) (Fin 2) (GaloisField p n))
    simp only [Matrix.GeneralLinearGroup.coe_mul,
      Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.GeneralLinearGroup.mk',
      Matrix.unitOfDetInvertible, Matrix.mul_apply, Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.det_fin_two] <;> field_simp <;> ring

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

/-- cosetIndex is invariant under left-multiplication by Borel elements. -/
private lemma Etingof.GL2.cosetIndex_borel_mul
    (b : ↥(Etingof.GL2.BorelSubgroup p n)) (g : GL2 p n) :
    Etingof.GL2.cosetIndex p n (b.val * g) = Etingof.GL2.cosetIndex p n g := by
  simp only [Etingof.GL2.cosetIndex]
  have hb10 : (b.val.val : Matrix (Fin 2) (Fin 2) (GaloisField p n)) 1 0 = 0 := b.prop
  -- (b * g)₁₀ = b₁₀ * g₀₀ + b₁₁ * g₁₀ = 0 * g₀₀ + b₁₁ * g₁₀ = b₁₁ * g₁₀
  have hbg10 : ((b.val * g).val : Matrix (Fin 2) (Fin 2) (GaloisField p n)) 1 0 =
    (b.val.val : Matrix _ _ _) 1 1 * (g.val : Matrix _ _ _) 1 0 := by
    simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, hb10]
  have hb11 : (b.val.val : Matrix (Fin 2) (Fin 2) (GaloisField p n)) 1 1 ≠ 0 :=
    Etingof.GL2.borel_diag11_ne_zero p n b
  -- If g₁₀ = 0, then (bg)₁₀ = 0
  -- If g₁₀ ≠ 0, then (bg)₁₀ ≠ 0 and we need (bg)₁₁/(bg)₁₀ = g₁₁/g₁₀
  by_cases hg10 : (g.val : Matrix (Fin 2) (Fin 2) (GaloisField p n)) 1 0 = 0
  · have : ((b.val * g).val : Matrix (Fin 2) (Fin 2) (GaloisField p n)) 1 0 = 0 := by
      rw [hbg10]; simp [hg10]
    simp [hg10, this]
  · have hbg10_ne : ¬ ((b.val * g).val : Matrix (Fin 2) (Fin 2) (GaloisField p n)) 1 0 = 0 := by
      rw [hbg10]; exact mul_ne_zero hb11 hg10
    have hbg11 : ((b.val * g).val : Matrix (Fin 2) (Fin 2) (GaloisField p n)) 1 1 =
      (b.val.val : Matrix _ _ _) 1 1 * (g.val : Matrix _ _ _) 1 1 := by
      simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, hb10]
    simp only [hg10, hbg10_ne, ↓reduceDIte, dite_false]
    congr 1
    rw [show ((b.val * g).val : Matrix _ _ _) 1 1 =
        (b.val.val : Matrix _ _ _) 1 1 * (g.val : Matrix _ _ _) 1 1 from hbg11,
      show ((b.val * g).val : Matrix _ _ _) 1 0 =
        (b.val.val : Matrix _ _ _) 1 1 * (g.val : Matrix _ _ _) 1 0 from hbg10]
    rw [mul_div_mul_left _ _ hb11]

/-- borelCharValue is multiplicative on the Borel subgroup. -/
private lemma Etingof.GL2.borelCharValue_mul
    (chi1 chi2 : (GaloisField p n)ˣ →* ℂˣ)
    (b1 b2 : ↥(Etingof.GL2.BorelSubgroup p n)) :
    Etingof.GL2.borelCharValue p n chi1 chi2
      ⟨b1.val * b2.val, (Etingof.GL2.BorelSubgroup p n).mul_mem b1.prop b2.prop⟩ =
    Etingof.GL2.borelCharValue p n chi1 chi2 b1 *
    Etingof.GL2.borelCharValue p n chi1 chi2 b2 := by
  unfold Etingof.GL2.borelCharValue
  have hb1_10 := b1.prop
  have hb2_10 := b2.prop
  -- (b1 * b2)₀₀ = b1₀₀ * b2₀₀ + b1₀₁ * b2₁₀ = b1₀₀ * b2₀₀ + b1₀₁ * 0 = b1₀₀ * b2₀₀
  -- (b1 * b2)₁₁ = b1₁₀ * b2₀₁ + b1₁₁ * b2₁₁ = 0 * b2₀₁ + b1₁₁ * b2₁₁ = b1₁₁ * b2₁₁
  have hb2_10' : (b2.val.val : Matrix (Fin 2) (Fin 2) (GaloisField p n)) 1 0 = 0 := b2.prop
  have hb1_10' : (b1.val.val : Matrix (Fin 2) (Fin 2) (GaloisField p n)) 1 0 = 0 := b1.prop
  have h00 : Units.mk0 _ (Etingof.GL2.borel_diag00_ne_zero p n
      ⟨b1.val * b2.val, (Etingof.GL2.BorelSubgroup p n).mul_mem b1.prop b2.prop⟩) =
    Units.mk0 _ (Etingof.GL2.borel_diag00_ne_zero p n b1) *
    Units.mk0 _ (Etingof.GL2.borel_diag00_ne_zero p n b2) := by
    ext
    show ((b1.val * b2.val).val : Matrix _ _ _) 0 0 =
      (b1.val.val : Matrix _ _ _) 0 0 * (b2.val.val : Matrix _ _ _) 0 0
    change ((b1.val.val * b2.val.val) 0 0 : _) = _
    simp [Matrix.mul_apply, Fin.sum_univ_two, hb2_10']
  have h11 : Units.mk0 _ (Etingof.GL2.borel_diag11_ne_zero p n
      ⟨b1.val * b2.val, (Etingof.GL2.BorelSubgroup p n).mul_mem b1.prop b2.prop⟩) =
    Units.mk0 _ (Etingof.GL2.borel_diag11_ne_zero p n b1) *
    Units.mk0 _ (Etingof.GL2.borel_diag11_ne_zero p n b2) := by
    ext
    show ((b1.val * b2.val).val : Matrix _ _ _) 1 1 =
      (b1.val.val : Matrix _ _ _) 1 1 * (b2.val.val : Matrix _ _ _) 1 1
    change ((b1.val.val * b2.val.val) 1 1 : _) = _
    simp [Matrix.mul_apply, Fin.sum_univ_two, hb1_10']
  -- Use h00, h11 to show multiplicativity
  simp only [Etingof.GL2.borelCharValue]
  rw [show Units.mk0 ((b1.val * b2.val).val 0 0 : _) _ = _ from h00,
      show Units.mk0 ((b1.val * b2.val).val 1 1 : _) _ = _ from h11,
      map_mul, map_mul, Units.val_mul, Units.val_mul]
  ring

/-- cosetBorel(b * g) = b * cosetBorel(g) for b ∈ B. -/
private lemma Etingof.GL2.cosetBorel_borel_mul
    (b : ↥(Etingof.GL2.BorelSubgroup p n)) (g : GL2 p n) :
    Etingof.GL2.cosetBorel p n (b.val * g) =
      ⟨b.val * (Etingof.GL2.cosetBorel p n g).val,
       (Etingof.GL2.BorelSubgroup p n).mul_mem b.prop (Etingof.GL2.cosetBorel p n g).prop⟩ := by
  -- Both sides decompose b*g = _ * rep(idx(b*g))
  -- LHS: cosetBorel(b*g) * rep(idx(b*g)) = b*g    [by cosetBorel_mul_cosetRep]
  -- RHS: b * cosetBorel(g) * rep(idx(g)) = b*g     [by cosetBorel_mul_cosetRep for g]
  -- Since idx(b*g) = idx(g), and rep is injective on right, the Borel parts are equal.
  apply Subtype.ext
  have h1 := Etingof.GL2.cosetBorel_mul_cosetRep p n (b.val * g)
  have h2 := Etingof.GL2.cosetBorel_mul_cosetRep p n g
  have hidx := Etingof.GL2.cosetIndex_borel_mul p n b g
  -- From h1: b*g = cosetBorel(b*g) * rep(idx(b*g))
  -- From h2: g = cosetBorel(g) * rep(idx(g))
  -- So b*g = b * cosetBorel(g) * rep(idx(g))
  -- And b*g = cosetBorel(b*g) * rep(idx(b*g)) = cosetBorel(b*g) * rep(idx(g))
  -- Therefore cosetBorel(b*g) * rep(idx(g)) = b * cosetBorel(g) * rep(idx(g))
  -- Cancel rep(idx(g)) on the right
  have key : (Etingof.GL2.cosetBorel p n (b.val * g)).val *
      Etingof.GL2.cosetRep p n (Etingof.GL2.cosetIndex p n (b.val * g)) =
    (b.val * (Etingof.GL2.cosetBorel p n g).val) *
      Etingof.GL2.cosetRep p n (Etingof.GL2.cosetIndex p n (b.val * g)) := by
    rw [← h1, mul_assoc, hidx, ← h2]
  exact mul_right_cancel key

/-- Construct a covariant function from values at coset reps. -/
private noncomputable def Etingof.GL2.mkCovariantFun
    (chi1 chi2 : (GaloisField p n)ˣ →* ℂˣ)
    (c : Option (GaloisField p n) → ℂ) :
    GL2 p n → ℂ :=
  fun g => Etingof.GL2.borelCharValue p n chi1 chi2
    (Etingof.GL2.cosetBorel p n g) * c (Etingof.GL2.cosetIndex p n g)

/-- The covariant function constructed from c is in the principal series submodule. -/
private lemma Etingof.GL2.mkCovariantFun_mem
    (chi1 chi2 : (GaloisField p n)ˣ →* ℂˣ)
    (c : Option (GaloisField p n) → ℂ) :
    Etingof.GL2.mkCovariantFun p n chi1 chi2 c ∈
      Etingof.GL2.principalSeriesSubmodule p n chi1 chi2 := by
  intro b g
  simp only [Etingof.GL2.mkCovariantFun]
  rw [Etingof.GL2.cosetIndex_borel_mul, Etingof.GL2.cosetBorel_borel_mul]
  rw [Etingof.GL2.borelCharValue_mul]
  ring

/-- cosetIndex(rep(i)) = i. -/
private lemma Etingof.GL2.cosetIndex_cosetRep
    (i : Option (GaloisField p n)) :
    Etingof.GL2.cosetIndex p n (Etingof.GL2.cosetRep p n i) = i := by
  cases i with
  | none =>
    simp [Etingof.GL2.cosetIndex, Etingof.GL2.cosetRep]
  | some t =>
    simp only [Etingof.GL2.cosetIndex, Etingof.GL2.cosetRep,
      Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.GeneralLinearGroup.mk',
      Matrix.unitOfDetInvertible]
    -- rep(some t) has (1,0)-entry = 1 ≠ 0
    have h10 : (Matrix.GeneralLinearGroup.mkOfDetNeZero
        (n := Fin 2) (K := GaloisField p n) !![0, -1; 1, t]
        (by simp [Matrix.det_fin_two])).val 1 0 ≠ 0 := by
      simp [Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.GeneralLinearGroup.mk',
            Matrix.unitOfDetInvertible]
    simp [Etingof.GL2.cosetIndex, h10,
          Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.GeneralLinearGroup.mk',
          Matrix.unitOfDetInvertible]

/-- borelCharValue at 1 is 1. -/
private lemma Etingof.GL2.borelCharValue_one
    (chi1 chi2 : (GaloisField p n)ˣ →* ℂˣ) :
    Etingof.GL2.borelCharValue p n chi1 chi2
      ⟨1, by simp [Etingof.GL2.BorelSubgroup]⟩ = 1 := by
  unfold Etingof.GL2.borelCharValue
  simp

/-- cosetBorel(rep(i)) = 1 for all i. -/
private lemma Etingof.GL2.cosetBorel_cosetRep
    (i : Option (GaloisField p n)) :
    Etingof.GL2.cosetBorel p n (Etingof.GL2.cosetRep p n i) =
      ⟨1, by simp [Etingof.GL2.BorelSubgroup]⟩ := by
  cases i with
  | none =>
    simp [Etingof.GL2.cosetBorel, Etingof.GL2.cosetRep, Etingof.GL2.BorelSubgroup]
  | some t =>
    simp only [Etingof.GL2.cosetBorel, Etingof.GL2.cosetRep]
    -- rep(some t) has (1,0)-entry = 1 ≠ 0
    have h10 : ¬ ((Matrix.GeneralLinearGroup.mkOfDetNeZero
        (n := Fin 2) (K := GaloisField p n) !![0, -1; 1, t]
        (by simp [Matrix.det_fin_two])).val : Matrix (Fin 2) (Fin 2) (GaloisField p n)) 1 0 = 0 := by
      simp [Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.GeneralLinearGroup.mk',
            Matrix.unitOfDetInvertible]
    rw [dif_neg h10]
    -- Now need to show the constructed Borel element = 1
    -- bmat = !![det/1, 0; 0, 1] = !![1, 0; 0, 1] = I
    apply Subtype.ext
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    simp [Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.GeneralLinearGroup.mk',
          Matrix.unitOfDetInvertible, Matrix.det_fin_two]
    fin_cases i <;> fin_cases j <;> simp [Matrix.det_fin_two]

/-- The covariant function evaluates to c at coset reps. -/
private lemma Etingof.GL2.mkCovariantFun_eval
    (chi1 chi2 : (GaloisField p n)ˣ →* ℂˣ)
    (c : Option (GaloisField p n) → ℂ)
    (i : Option (GaloisField p n)) :
    Etingof.GL2.mkCovariantFun p n chi1 chi2 c
      (Etingof.GL2.cosetRep p n i) = c i := by
  simp [Etingof.GL2.mkCovariantFun,
    Etingof.GL2.cosetIndex_cosetRep,
    Etingof.GL2.cosetBorel_cosetRep,
    Etingof.GL2.borelCharValue_one]

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
  -- Need: the module is nontrivial (has a nonzero element)
  -- Produce a nonzero element using mkCovariantFun
  set f : ↥(Etingof.GL2.principalSeriesSubmodule p n chi1 chi2) :=
    ⟨Etingof.GL2.mkCovariantFun p n chi1 chi2 (fun _ => 1),
     Etingof.GL2.mkCovariantFun_mem p n chi1 chi2 (fun _ => 1)⟩
  have hfne : f ≠ 0 := by
    intro h
    have heval := Etingof.GL2.mkCovariantFun_eval p n chi1 chi2 (fun _ => 1) none
    simp only [f] at h
    have : (0 : ↥(Etingof.GL2.principalSeriesSubmodule p n chi1 chi2)).val
        (Etingof.GL2.cosetRep p n none) = 1 := by rw [← h]; exact heval
    simp at this
  -- ⊥ ≠ ⊤ because ⊤ contains f ≠ 0 but ⊥ doesn't
  exact nontrivial_of_ne ⊥ ⊤ (by
    intro heq
    apply hfne
    have hmem : f ∈ (⊥ : Subrepresentation
      (Etingof.GL2.principalSeriesRep p n chi1 chi2)).toSubmodule := by
      rw [heq]; exact Submodule.mem_top
    simpa using hmem)

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

/-- (ρ(w) f)(rep(some 0)) = borelCharValue(-I) · f(rep(none)) for delta functions.
More precisely, rep(some 0) · rep(some 0) = -I which is in B. -/
private lemma Etingof.GL2.action_weyl_some_zero
    (chi1 chi2 : (GaloisField p n)ˣ →* ℂˣ)
    (f : ↥(Etingof.GL2.principalSeriesSubmodule p n chi1 chi2)) :
    (Etingof.GL2.principalSeriesRep p n chi1 chi2
      (Etingof.GL2.cosetRep p n (some 0)) f).val
      (Etingof.GL2.cosetRep p n (some 0)) =
    f.val (Etingof.GL2.cosetRep p n (some 0) * Etingof.GL2.cosetRep p n (some 0)) := rfl

/-- rep(some t) · rep(some 0) for t ≠ 0 has nonzero (1,0)-entry.
This means it's NOT in the Borel subgroup coset of rep(none). -/
private lemma Etingof.GL2.cosetRep_some_mul_weyl_not_borel
    (t : GaloisField p n) (ht : t ≠ 0) :
    ((Etingof.GL2.cosetRep p n (some t) *
      Etingof.GL2.cosetRep p n (some 0)).val :
      Matrix (Fin 2) (Fin 2) (GaloisField p n)) 1 0 ≠ 0 := by
  simp only [Etingof.GL2.cosetRep, Matrix.GeneralLinearGroup.coe_mul,
    Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.GeneralLinearGroup.mk',
    Matrix.unitOfDetInvertible, Matrix.mul_apply, Fin.sum_univ_two]
  simp [ht]

/-- (ρ(w) f)(rep(some t)) = 0 when t ≠ 0 and f is a "delta at none"
(i.e., f(rep(some s)) = 0 for all s). -/
private lemma Etingof.GL2.action_weyl_some_ne_zero
    (chi1 chi2 : (GaloisField p n)ˣ →* ℂˣ)
    (f : ↥(Etingof.GL2.principalSeriesSubmodule p n chi1 chi2))
    (hfsome : ∀ s, f.val (Etingof.GL2.cosetRep p n (some s)) = 0)
    (t : GaloisField p n) (ht : t ≠ 0) :
    (Etingof.GL2.principalSeriesRep p n chi1 chi2
      (Etingof.GL2.cosetRep p n (some 0)) f).val
      (Etingof.GL2.cosetRep p n (some t)) = 0 := by
  -- ρ(w)(f)(rep(some t)) = f(rep(some t) · w)
  change f.val (Etingof.GL2.cosetRep p n (some t) * Etingof.GL2.cosetRep p n (some 0)) = 0
  -- rep(some t) · w has (1,0) entry = -t ≠ 0, so it's in a "some" coset
  -- By covariance, f(M) = χ(b) · f(rep(idx(M))) where idx(M) = some(...)
  -- Since f(rep(some s)) = 0 for all s, we get f(M) = 0.
  set M := Etingof.GL2.cosetRep p n (some t) * Etingof.GL2.cosetRep p n (some 0)
  -- M = b · rep(cosetIndex M) and cosetIndex M = some(...)
  obtain ⟨b, hbM⟩ := Etingof.GL2.mem_coset_of_cosetIndex p n M
  have hcov := f.prop b (Etingof.GL2.cosetRep p n (Etingof.GL2.cosetIndex p n M))
  rw [← hbM] at hcov
  rw [hcov]
  have hidx : ∃ s, Etingof.GL2.cosetIndex p n M = some s := by
    unfold Etingof.GL2.cosetIndex
    simp only [M]
    have h10 := Etingof.GL2.cosetRep_some_mul_weyl_not_borel p n t ht
    rw [show (M : Matrix (Fin 2) (Fin 2) (GaloisField p n)) =
      (Etingof.GL2.cosetRep p n (some t)).val *
        (Etingof.GL2.cosetRep p n (some 0)).val from
      Units.val_mul _ _] at h10
    simp [Etingof.GL2.cosetIndex, h10]
  obtain ⟨s, hs⟩ := hidx
  rw [hs, hfsome, mul_zero]

private lemma Etingof.GL2.principalSeries_delta_spans_top
    (chi1 chi2 : (GaloisField p n)ˣ →* ℂˣ)
    (S : Subrepresentation (Etingof.GL2.principalSeriesRep p n chi1 chi2))
    (g : ↥(Etingof.GL2.principalSeriesSubmodule p n chi1 chi2))
    (hgS : g ∈ S.toSubmodule)
    (hgnone : g.val (Etingof.GL2.cosetRep p n none) ≠ 0)
    (hgsome : ∀ t, g.val (Etingof.GL2.cosetRep p n (some t)) = 0) :
    S = ⊤ := by
  rw [eq_top_iff]
  intro f _
  -- Normalize g to have value 1 at rep(none)
  set c₀ := g.val (Etingof.GL2.cosetRep p n none)
  set g' := c₀⁻¹ • g with g'_def
  have hg'S : g' ∈ S.toSubmodule := S.toSubmodule.smul_mem _ hgS
  have hg'_none : g'.val (Etingof.GL2.cosetRep p n none) = 1 := by
    simp only [g'_def, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
    exact inv_mul_cancel₀ hgnone
  have hg'_some : ∀ t, g'.val (Etingof.GL2.cosetRep p n (some t)) = 0 := by
    intro t
    simp [g'_def, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, hgsome]
  -- wg' = ρ(w)(g') is a delta at rep(some 0):
  -- wg'(rep(none)) = 0, wg'(rep(some t)) = 0 for t ≠ 0,
  -- wg'(rep(some 0)) ≠ 0
  set wg' := Etingof.GL2.principalSeriesRep p n chi1 chi2
    (Etingof.GL2.cosetRep p n (some 0)) g' with wg'_def
  have hwg'S : wg' ∈ S.toSubmodule := S.apply_mem_toSubmodule _ hg'S
  have hwg'_none : wg'.val (Etingof.GL2.cosetRep p n none) = 0 := by
    rw [Etingof.GL2.action_weyl_none]; exact hg'_some 0
  have hwg'_some_ne : ∀ t, t ≠ 0 →
      wg'.val (Etingof.GL2.cosetRep p n (some t)) = 0 :=
    fun t ht => Etingof.GL2.action_weyl_some_ne_zero p n chi1 chi2 g'
      hg'_some t ht
  -- α = wg'(rep(some 0)) ≠ 0
  set α := wg'.val (Etingof.GL2.cosetRep p n (some 0))
  have hα_ne : α ≠ 0 := by
    change wg'.val (Etingof.GL2.cosetRep p n (some 0)) ≠ 0
    rw [show wg'.val (Etingof.GL2.cosetRep p n (some 0)) =
      g'.val (Etingof.GL2.cosetRep p n (some 0) *
        Etingof.GL2.cosetRep p n (some 0)) from rfl]
    -- rep(some 0)² = -I ∈ B, and g'(-I) = χ₁(-1)·χ₂(-1) · g'(rep(none))
    obtain ⟨b, hbM⟩ := Etingof.GL2.mem_coset_of_cosetIndex p n
      (Etingof.GL2.cosetRep p n (some 0) *
        Etingof.GL2.cosetRep p n (some 0))
    have hcov := g'.prop b (Etingof.GL2.cosetRep p n
      (Etingof.GL2.cosetIndex p n
        (Etingof.GL2.cosetRep p n (some 0) *
          Etingof.GL2.cosetRep p n (some 0))))
    rw [← hbM] at hcov; rw [hcov]
    have hidx : Etingof.GL2.cosetIndex p n
        (Etingof.GL2.cosetRep p n (some 0) *
          Etingof.GL2.cosetRep p n (some 0)) = none := by
      simp [Etingof.GL2.cosetIndex, Etingof.GL2.cosetRep,
        Matrix.GeneralLinearGroup.mkOfDetNeZero,
        Matrix.GeneralLinearGroup.mk',
        Matrix.unitOfDetInvertible,
        Matrix.GeneralLinearGroup.coe_mul,
        Matrix.mul_apply, Fin.sum_univ_two]
    rw [hidx, hg'_none]
    simp [Etingof.GL2.borelCharValue]
  -- Decompose f = f(rep(none)) • g' + ∑_t f(rep(some t)) • (α⁻¹ • ρ(τ_{-t})(wg'))
  -- Each ρ(τ_{-t})(wg') is a "delta at rep(some t)" (up to factor α).
  set rhs := f.val (Etingof.GL2.cosetRep p n none) • g' +
    ∑ t : GaloisField p n,
      f.val (Etingof.GL2.cosetRep p n (some t)) •
        (α⁻¹ • Etingof.GL2.principalSeriesRep p n chi1 chi2
          (Etingof.GL2.translationElt p n (-t)) wg')
  have hrhs_S : rhs ∈ S.toSubmodule := by
    apply S.toSubmodule.add_mem (S.toSubmodule.smul_mem _ hg'S)
    apply S.toSubmodule.sum_mem; intro t _
    exact S.toSubmodule.smul_mem _
      (S.toSubmodule.smul_mem _ (S.apply_mem_toSubmodule _ hwg'S))
  suffices heq : f = rhs by rwa [heq]
  -- Prove f = rhs by showing they agree on all coset reps (then use injectivity)
  have := Etingof.GL2.principalSeries_eval_injective p n chi1 chi2 (f - rhs)
  rw [sub_eq_zero] at this; apply this
  intro i
  -- Unfold the subtraction and rhs definition
  change f.val (Etingof.GL2.cosetRep p n i) -
    (f.val (Etingof.GL2.cosetRep p n none) • g' +
      ∑ t : GaloisField p n,
        f.val (Etingof.GL2.cosetRep p n (some t)) •
          (α⁻¹ • Etingof.GL2.principalSeriesRep p n chi1 chi2
            (Etingof.GL2.translationElt p n (-t)) wg')).val
      (Etingof.GL2.cosetRep p n i) = 0
  simp only [Submodule.coe_add, Submodule.coe_smul, Submodule.coe_sum,
    Pi.add_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  cases i with
  | none =>
    rw [hg'_none, mul_one]
    simp_rw [Etingof.GL2.action_translation_none p n chi1 chi2 wg']
    simp [hwg'_none]
  | some s =>
    rw [hg'_some, mul_zero, zero_add]
    -- ρ(τ_{-t})(wg')(rep(some s)) = wg'(rep(some(s + (-t))))
    simp_rw [Etingof.GL2.action_translation_some p n chi1 chi2
      wg' (-_) s]
    conv_lhs =>
      arg 2; arg 2; ext t; rw [show s + -t = s - t from by ring]
    -- Only t = s contributes: wg'(rep(some 0)) = α, others = 0
    rw [show (∑ t : GaloisField p n,
        f.val (Etingof.GL2.cosetRep p n (some t)) *
          (α⁻¹ * wg'.val
            (Etingof.GL2.cosetRep p n (some (s - t))))) =
      f.val (Etingof.GL2.cosetRep p n (some s)) *
        (α⁻¹ * wg'.val (Etingof.GL2.cosetRep p n (some 0))) from by
      rw [← Finset.sum_subset (Finset.subset_univ {s})
        (fun t _ ht => by
          simp at ht
          rw [hwg'_some_ne (s - t)
            (sub_ne_zero.mpr (Ne.symm ht)), mul_zero, mul_zero])]
      simp [sub_self]]
    rw [inv_mul_cancel₀ hα_ne, mul_one, sub_self]

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
      ∀ i, (f : GL2 p n → ℂ) (Etingof.GL2.cosetRep p n i) = c i :=
  ⟨⟨Etingof.GL2.mkCovariantFun p n chi1 chi2 c,
    Etingof.GL2.mkCovariantFun_mem p n chi1 chi2 c⟩,
   Etingof.GL2.mkCovariantFun_eval p n chi1 chi2 c⟩

/-- Evaluation at coset reps restricted to complementW is injective into GaloisField → ℂ.
    Key: if f(rep(some t)) = 0 for all t AND aug(f) = 0, then f(rep(none)) = 0 too. -/
private lemma Etingof.GL2.complementW_eval_injective
    (mu : (GaloisField p n)ˣ →* ℂˣ)
    (f : ↥(Etingof.GL2.complementWSubmodule p n mu))
    (hf : ∀ t : GaloisField p n,
      (f : GL2 p n → ℂ) (Etingof.GL2.cosetRep p n (some t)) = 0) :
    f = 0 := by
  -- f is in principalSeriesSubmodule ⊓ ker(augmentation)
  have hcov := f.prop.1  -- covariance
  have hker := f.prop.2  -- ker(augmentation)
  -- It suffices to show f(rep(i)) = 0 for all i (including none)
  suffices h : ∀ i : Option (GaloisField p n),
      (f.val : GL2 p n → ℂ) (Etingof.GL2.cosetRep p n i) = 0 by
    -- Use principalSeries_eval_injective on f viewed as element of principalSeriesSubmodule
    have hinj := Etingof.GL2.principalSeries_eval_injective p n mu mu
      ⟨f.val, hcov⟩ h
    exact Subtype.ext (show f.val = 0 from congr_arg Subtype.val hinj)
  intro i
  cases i with
  | some t => exact hf t
  | none =>
    -- Need: f(1) = 0, using aug(f) = 0
    -- For each g, f(g) = χ(b_g)·f(rep(idx(g))), where g = b_g · rep(idx(g))
    -- If idx(g) = some t, then f(rep(some t)) = 0, so f(g) = 0, so the aug summand = 0.
    -- If idx(g) = none (g ∈ B), then f(g) = χ(g)·f(1) and the summand is
    --   χ(g)·f(1)·μ(det g)⁻¹ = f(1) (since χ₁=χ₂=μ means χ(b)·μ(det b)⁻¹ = 1).
    -- So aug(f) = |B|·f(1) = 0, giving f(1) = 0.
    -- Step 1: Show f(g) = 0 for all g ∉ B
    have hf_zero_outside_B : ∀ g : GL2 p n,
        (g.val : Matrix (Fin 2) (Fin 2) (GaloisField p n)) 1 0 ≠ 0 →
        f.val g = 0 := by
      intro g hg10
      obtain ⟨b, hbg⟩ := Etingof.GL2.mem_coset_of_cosetIndex p n g
      have hcov_g := hcov b (Etingof.GL2.cosetRep p n (Etingof.GL2.cosetIndex p n g))
      rw [← hbg] at hcov_g
      rw [hcov_g]
      have : Etingof.GL2.cosetIndex p n g = some ((g.val : Matrix _ _ _) 1 1 / (g.val : Matrix _ _ _) 1 0) := by
        simp [Etingof.GL2.cosetIndex, hg10]
      rw [this]
      rw [hf _, mul_zero]
    -- Step 2: Show f(g) · μ(det g)⁻¹ = f(1) for g ∈ B
    have hf_B_term : ∀ g : GL2 p n,
        (g.val : Matrix (Fin 2) (Fin 2) (GaloisField p n)) 1 0 = 0 →
        f.val g * ↑(mu (Matrix.GeneralLinearGroup.det g))⁻¹ = f.val 1 := by
      intro g hg10
      -- g ∈ B, so g = b · rep(none) = b · 1 = b
      have hcov_g := hcov ⟨g, hg10⟩ 1
      simp only [Units.val_one, mul_one] at hcov_g ⊢
      -- f(g) = borelCharValue(g) · f(1)
      rw [hcov_g]
      -- borelCharValue = μ(g₀₀) · μ(g₁₁), det(g) = g₀₀ · g₁₁ (since g₁₀ = 0)
      unfold Etingof.GL2.borelCharValue
      have hdet_g : Matrix.GeneralLinearGroup.det g =
        Units.mk0 _ (Etingof.GL2.borel_diag00_ne_zero p n ⟨g, hg10⟩) *
        Units.mk0 _ (Etingof.GL2.borel_diag11_ne_zero p n ⟨g, hg10⟩) := by
        ext; simp [Matrix.GeneralLinearGroup.det, Matrix.det_fin_two, hg10]
      rw [hdet_g, map_mul, mul_inv_rev, Units.val_mul]
      -- Goal: μ(g₀₀) * μ(g₁₁) * f(1) * μ(g₁₁)⁻¹ * μ(g₀₀)⁻¹ = f(1)
      simp only [Units.val_inv_eq_inv_val]
      have h1 : ((mu (Units.mk0 _ (Etingof.GL2.borel_diag11_ne_zero p n ⟨g, hg10⟩)) : ℂˣ) : ℂ) ≠ 0 :=
        Units.ne_zero _
      have h0 : ((mu (Units.mk0 _ (Etingof.GL2.borel_diag00_ne_zero p n ⟨g, hg10⟩)) : ℂˣ) : ℂ) ≠ 0 :=
        Units.ne_zero _
      field_simp
    -- Step 3: Compute aug(f) = |B| · f(1)
    have hker_val : ∑ g : GL2 p n,
        f.val g * ↑(mu (Matrix.GeneralLinearGroup.det g))⁻¹ = 0 := by
      have := hker
      simp only [LinearMap.mem_ker, Etingof.GL2.augmentation,
        LinearMap.coe_mk, AddHom.coe_mk] at this
      exact this
    -- Split sum into B and non-B parts
    have hterm : ∀ g : GL2 p n,
        f.val g * ↑(mu (Matrix.GeneralLinearGroup.det g))⁻¹ =
        if (g.val : Matrix (Fin 2) (Fin 2) (GaloisField p n)) 1 0 = 0
        then f.val 1
        else 0 := by
      intro g
      split_ifs with h10
      · exact hf_B_term g h10
      · rw [hf_zero_outside_B g h10, zero_mul]
    simp_rw [hterm] at hker_val
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
        nsmul_eq_mul] at hker_val
    -- |B| ≠ 0
    have hB_ne : ((Finset.univ.filter
        (fun g : GL2 p n =>
          (g.val : Matrix (Fin 2) (Fin 2) (GaloisField p n)) 1 0 = 0)).card : ℂ) ≠ 0 := by
      rw [Nat.cast_ne_zero]
      exact Finset.card_ne_zero.mpr ⟨1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp⟩⟩
    exact (mul_eq_zero.mp hker_val).resolve_left hB_ne

/-- Evaluation at "some" coset reps from complementW is surjective onto GaloisField → ℂ. -/
private lemma Etingof.GL2.complementW_eval_surjective
    (mu : (GaloisField p n)ˣ →* ℂˣ)
    (c : GaloisField p n → ℂ) :
    ∃ f : ↥(Etingof.GL2.complementWSubmodule p n mu),
      ∀ t, (f : GL2 p n → ℂ) (Etingof.GL2.cosetRep p n (some t)) = c t := by
  -- Construct covariant function with v(some t) = c(t), v(none) = -∑ c(t)
  let v : Option (GaloisField p n) → ℂ := fun i =>
    match i with
    | some t => c t
    | none => -∑ t, c t
  have hf_mem := Etingof.GL2.mkCovariantFun_mem p n mu mu v
  have hf_eval := Etingof.GL2.mkCovariantFun_eval p n mu mu v
  -- Need to show f ∈ complementWSubmodule = principalSeriesSubmodule ⊓ ker(augmentation)
  -- f ∈ principalSeriesSubmodule is hf_mem
  -- f ∈ ker(augmentation) needs: aug(f) = 0
  -- This follows because aug(f) = |B| · ∑_i v(i) = |B| · ((-∑ c(t)) + ∑ c(t)) = 0
  -- Show f ∈ ker(augmentation) via the augmentation computation
  have hf_aug : Etingof.GL2.mkCovariantFun p n mu mu v ∈
      LinearMap.ker (Etingof.GL2.augmentation p n mu) := by
    simp only [LinearMap.mem_ker, Etingof.GL2.augmentation, LinearMap.coe_mk, AddHom.coe_mk]
    -- Each term: mkCovariantFun(g) * mu(det g)⁻¹ = v(cosetIndex g)
    -- because borelCharValue(cosetBorel g) cancels with mu(det(cosetBorel g))
    -- and det(rep(i)) = 1 for all i
    -- Each term: mkCovariantFun(g) * mu(det g)⁻¹ = v(cosetIndex g)
    -- because borelCharValue(cosetBorel g) cancels with mu(det(cosetBorel g))
    -- and det(rep(i)) = 1 for all i
    -- Key helper: det(rep(i)) = 1 for all coset reps
    have hdet_rep : ∀ i : Option (GaloisField p n),
        Matrix.GeneralLinearGroup.det (Etingof.GL2.cosetRep p n i) = 1 := by
      intro i
      cases i with
      | none =>
        ext
        simp [Etingof.GL2.cosetRep, Matrix.GeneralLinearGroup.det]
      | some t =>
        ext
        simp [Etingof.GL2.cosetRep, Matrix.GeneralLinearGroup.det,
          Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.GeneralLinearGroup.mk',
          Matrix.unitOfDetInvertible, Matrix.det_fin_two]
    -- Key helper: borelCharValue(b) * mu(det b)⁻¹ = 1 when chi1=chi2=mu
    have hborel_cancel : ∀ b : ↥(Etingof.GL2.BorelSubgroup p n),
        Etingof.GL2.borelCharValue p n mu mu b *
        ((mu (Matrix.GeneralLinearGroup.det b.val))⁻¹ : ℂˣ) = 1 := by
      intro b
      have hb10 : (b.val.val : Matrix (Fin 2) (Fin 2) (GaloisField p n)) 1 0 = 0 := b.prop
      have hdet_b : Matrix.GeneralLinearGroup.det b.val =
        Units.mk0 ((b.val.val : Matrix _ _ _) 0 0)
          (Etingof.GL2.borel_diag00_ne_zero p n b) *
        Units.mk0 ((b.val.val : Matrix _ _ _) 1 1)
          (Etingof.GL2.borel_diag11_ne_zero p n b) := by
        ext; simp [Matrix.GeneralLinearGroup.det, Matrix.det_fin_two, hb10]
      rw [hdet_b, map_mul]
      -- Goal: borelCharValue b * ↑(mu a * mu b)⁻¹ = 1
      -- ↑(mu a * mu b)⁻¹ = (↑(mu a * mu b))⁻¹ = (↑(mu a) * ↑(mu b))⁻¹
      rw [Units.val_inv_eq_inv_val, Units.val_mul]
      simp only [Etingof.GL2.borelCharValue]
      rw [mul_inv_cancel₀ (mul_ne_zero (Units.ne_zero _) (Units.ne_zero _))]
    -- Rewrite each term using coset decomposition
    have hterm : ∀ g : GL2 p n,
        Etingof.GL2.mkCovariantFun p n mu mu v g *
        ((mu (Matrix.GeneralLinearGroup.det g))⁻¹ : ℂˣ) =
        v (Etingof.GL2.cosetIndex p n g) := by
      intro g
      simp only [Etingof.GL2.mkCovariantFun]
      -- g = cosetBorel(g) * rep(cosetIndex(g))
      have hdecomp := Etingof.GL2.cosetBorel_mul_cosetRep p n g
      -- det(g) = det(cosetBorel g) * det(rep(cosetIndex g)) = det(cosetBorel g) * 1
      have hdet_g : Matrix.GeneralLinearGroup.det g =
          Matrix.GeneralLinearGroup.det (Etingof.GL2.cosetBorel p n g).val *
          Matrix.GeneralLinearGroup.det
            (Etingof.GL2.cosetRep p n (Etingof.GL2.cosetIndex p n g)) := by
        conv_lhs => rw [hdecomp]
        exact map_mul _ _ _
      rw [hdet_g, hdet_rep, mul_one]
      rw [show Etingof.GL2.borelCharValue p n mu mu (Etingof.GL2.cosetBorel p n g) *
            v (Etingof.GL2.cosetIndex p n g) *
            ((mu (Matrix.GeneralLinearGroup.det
              (Etingof.GL2.cosetBorel p n g).val))⁻¹ : ℂˣ) =
          (Etingof.GL2.borelCharValue p n mu mu (Etingof.GL2.cosetBorel p n g) *
            ((mu (Matrix.GeneralLinearGroup.det
              (Etingof.GL2.cosetBorel p n g).val))⁻¹ : ℂˣ)) *
          v (Etingof.GL2.cosetIndex p n g) from by ring]
      rw [hborel_cancel, one_mul]
    simp_rw [hterm]
    -- ∑_g v(cosetIndex g) = 0 because v factors through cosetIndex
    -- and ∑_i v(i) = 0 (by construction: v(none) = -∑ c t, v(some t) = c t)
    -- Each fiber has the same size |B|, so ∑_g v(cosetIndex g) = |B| * ∑_i v(i) = |B| * 0 = 0
    -- Step 1: ∑_i v(i) = 0
    have hv_sum : ∑ i : Option (GaloisField p n), v i = 0 := by
      simp only [Fintype.sum_option, v]
      simp [add_comm]
    -- Step 2: Build Equiv GL₂ ≃ B × Option(GaloisField p n)
    let e : GL2 p n ≃ ↥(Etingof.GL2.BorelSubgroup p n) × Option (GaloisField p n) :=
      { toFun := fun g => (Etingof.GL2.cosetBorel p n g, Etingof.GL2.cosetIndex p n g)
        invFun := fun bi => bi.1.val * Etingof.GL2.cosetRep p n bi.2
        left_inv := fun g => by
          simp only
          exact (Etingof.GL2.cosetBorel_mul_cosetRep p n g).symm
        right_inv := fun ⟨b, i⟩ => by
          simp only
          ext
          · -- cosetBorel(b * rep(i)) = b
            have := Etingof.GL2.cosetBorel_borel_mul p n b
                      (Etingof.GL2.cosetRep p n i)
            rw [this, Etingof.GL2.cosetBorel_cosetRep]
            simp
          · -- cosetIndex(b * rep(i)) = i
            rw [Etingof.GL2.cosetIndex_borel_mul,
                Etingof.GL2.cosetIndex_cosetRep] }
    -- Step 3: Reindex the sum
    rw [show (∑ g : GL2 p n, v (Etingof.GL2.cosetIndex p n g)) =
        ∑ bi : ↥(Etingof.GL2.BorelSubgroup p n) × Option (GaloisField p n), v bi.2 from
      Fintype.sum_equiv e _ _ (fun g => by simp [e])]
    rw [Fintype.sum_prod_type]
    simp [hv_sum]
  exact ⟨⟨Etingof.GL2.mkCovariantFun p n mu mu v, ⟨hf_mem, hf_aug⟩⟩,
    fun t => hf_eval (some t)⟩

/-- dim V(χ₁,χ₂) = [G:B] = p^n + 1. -/
private lemma Etingof.GL2.principalSeriesSubmodule_finrank [NeZero n]
    (chi1 chi2 : (GaloisField p n)ˣ →* ℂˣ) :
    Module.finrank ℂ ↥(Etingof.GL2.principalSeriesSubmodule p n chi1 chi2) = p ^ n + 1 := by
  -- Build linear map: evaluate at coset reps
  let evalMap : ↥(Etingof.GL2.principalSeriesSubmodule p n chi1 chi2) →ₗ[ℂ]
      (Option (GaloisField p n) → ℂ) :=
    { toFun := fun f i => (f : GL2 p n → ℂ) (Etingof.GL2.cosetRep p n i)
      map_add' := fun _ _ => funext fun _ => rfl
      map_smul' := fun _ _ => funext fun _ => rfl }
  -- evalMap is injective (by principalSeries_eval_injective)
  have hinj : Function.Injective evalMap := by
    intro f g hfg
    have h : f - g = 0 := Etingof.GL2.principalSeries_eval_injective p n chi1 chi2 (f - g)
      (fun i => by
        have := congr_fun hfg i
        simp [evalMap] at this
        simp [this])
    exact sub_eq_zero.mp h
  -- evalMap is surjective (via mkCovariantFun)
  have hsurj : Function.Surjective evalMap := fun c =>
    ⟨⟨Etingof.GL2.mkCovariantFun p n chi1 chi2 c,
      Etingof.GL2.mkCovariantFun_mem p n chi1 chi2 c⟩,
     funext fun i => Etingof.GL2.mkCovariantFun_eval p n chi1 chi2 c i⟩
  -- Use the linear equiv to transfer finrank
  have heq := (LinearEquiv.ofBijective evalMap ⟨hinj, hsurj⟩).finrank_eq
  rw [Module.finrank_pi_fintype] at heq
  simp only [Module.finrank_self] at heq
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] at heq
  rw [heq, Fintype.card_option]
  congr 1
  rw [← Nat.card_eq_fintype_card, GaloisField.card p n (NeZero.ne n)]

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
    -- LHS: proj(g·f)(x) = f(xg) - (aug(g·f)/|G|)·μ(det x)
    -- RHS: (g·proj(f))(x) = proj(f)(xg) = f(xg) - (aug(f)/|G|)·μ(det(xg))
    --                      = f(xg) - (aug(f)/|G|)·μ(det x)·μ(det g)
    -- These are equal because aug(g·f) = μ(det g)·aug(f)
    simp only [Etingof.GL2.complementW, Etingof.GL2.complementWSubmodule,
      Etingof.GL2.principalSeriesRep, Representation.ofMulAction]
    show f (x * g) -
        (Fintype.card (GL2 p n) : ℂ)⁻¹ *
          Etingof.GL2.augOnPrincipalSeries p n mu
            (Etingof.GL2.principalSeriesRep p n mu mu g ⟨f, hf⟩) *
          ↑(mu (Matrix.GeneralLinearGroup.det x)) =
      f (x * g) -
        (Fintype.card (GL2 p n) : ℂ)⁻¹ *
          Etingof.GL2.augOnPrincipalSeries p n mu ⟨f, hf⟩ *
          ↑(mu (Matrix.GeneralLinearGroup.det (x * g)))
    rw [Etingof.GL2.augOnPrincipalSeries_equivariant]
    simp only [map_mul, Units.val_mul]
    ring

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

/-- For f ∈ complementW, aug(f) = 0 implies f(rep(none)) = -∑_t f(rep(some t)).
    Proof: the augmentation ∑_g f(g)·μ(det g)⁻¹ = 0 reduces to |B|·(f(1) + ∑_t f(rep(some t))) = 0
    since borelCharValue·μ(det)⁻¹ = 1 for the (μ,μ) character. -/
private lemma Etingof.GL2.complementW_none_eq_neg_sum
    (mu : (GaloisField p n)ˣ →* ℂˣ)
    (f : ↥(Etingof.GL2.complementWSubmodule p n mu)) :
    f.val (Etingof.GL2.cosetRep p n none) =
    -(∑ t : GaloisField p n, f.val (Etingof.GL2.cosetRep p n (some t))) := by
  -- f ∈ complementWSubmodule = principalSeriesSubmodule ⊓ ker(augmentation)
  have hcov := f.prop.1  -- covariance
  have hker : f.val ∈ LinearMap.ker (Etingof.GL2.augmentation p n mu) := f.prop.2
  rw [LinearMap.mem_ker] at hker
  -- hker : ∑_g f.val(g) * μ(det g)⁻¹ = 0
  simp only [Etingof.GL2.augmentation, LinearMap.coe_mk, AddHom.coe_mk] at hker
  -- Each term: f(g) * μ(det g)⁻¹ = f(rep(cosetIndex g))
  -- because borelCharValue(cosetBorel g) cancels with μ(det(cosetBorel g))⁻¹
  -- and det(rep(i)) = 1 for all i
  have hdet_rep : ∀ i : Option (GaloisField p n),
      Matrix.GeneralLinearGroup.det (Etingof.GL2.cosetRep p n i) = 1 := by
    intro i; cases i with
    | none => ext; simp [Etingof.GL2.cosetRep, Matrix.GeneralLinearGroup.det]
    | some t => ext; simp [Etingof.GL2.cosetRep, Matrix.GeneralLinearGroup.det,
        Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.GeneralLinearGroup.mk',
        Matrix.unitOfDetInvertible, Matrix.det_fin_two]
  have hborel_cancel : ∀ b : ↥(Etingof.GL2.BorelSubgroup p n),
      Etingof.GL2.borelCharValue p n mu mu b *
      ((mu (Matrix.GeneralLinearGroup.det b.val))⁻¹ : ℂˣ) = 1 := by
    intro b
    have hb10 : (b.val.val : Matrix (Fin 2) (Fin 2) (GaloisField p n)) 1 0 = 0 := b.prop
    have hdet_b : Matrix.GeneralLinearGroup.det b.val =
      Units.mk0 ((b.val.val : Matrix _ _ _) 0 0)
        (Etingof.GL2.borel_diag00_ne_zero p n b) *
      Units.mk0 ((b.val.val : Matrix _ _ _) 1 1)
        (Etingof.GL2.borel_diag11_ne_zero p n b) := by
      ext; simp [Matrix.GeneralLinearGroup.det, Matrix.det_fin_two, hb10]
    rw [hdet_b, map_mul]
    rw [Units.val_inv_eq_inv_val, Units.val_mul]
    simp only [Etingof.GL2.borelCharValue]
    rw [mul_inv_cancel₀ (mul_ne_zero (Units.ne_zero _) (Units.ne_zero _))]
  -- Each term f(g) * μ(det g)⁻¹ = f(rep(cosetIndex g))
  have hterm : ∀ g : GL2 p n,
      f.val g * ((mu (Matrix.GeneralLinearGroup.det g))⁻¹ : ℂˣ) =
      f.val (Etingof.GL2.cosetRep p n (Etingof.GL2.cosetIndex p n g)) := by
    intro g
    have hdecomp := Etingof.GL2.cosetBorel_mul_cosetRep p n g
    have hdet_g : Matrix.GeneralLinearGroup.det g =
        Matrix.GeneralLinearGroup.det (Etingof.GL2.cosetBorel p n g).val *
        Matrix.GeneralLinearGroup.det
          (Etingof.GL2.cosetRep p n (Etingof.GL2.cosetIndex p n g)) := by
      conv_lhs => rw [hdecomp]; exact map_mul _ _ _
    rw [hdet_g, hdet_rep, mul_one]
    -- f(g) = f(cosetBorel(g) * rep(idx(g))) = borelCharValue(cosetBorel g) * f(rep(idx(g)))
    have hcov_g := hcov (Etingof.GL2.cosetBorel p n g)
      (Etingof.GL2.cosetRep p n (Etingof.GL2.cosetIndex p n g))
    rw [← hdecomp] at hcov_g
    rw [hcov_g]
    rw [show Etingof.GL2.borelCharValue p n mu mu (Etingof.GL2.cosetBorel p n g) *
          f.val (Etingof.GL2.cosetRep p n (Etingof.GL2.cosetIndex p n g)) *
          ((mu (Matrix.GeneralLinearGroup.det
            (Etingof.GL2.cosetBorel p n g).val))⁻¹ : ℂˣ) =
        (Etingof.GL2.borelCharValue p n mu mu (Etingof.GL2.cosetBorel p n g) *
          ((mu (Matrix.GeneralLinearGroup.det
            (Etingof.GL2.cosetBorel p n g).val))⁻¹ : ℂˣ)) *
        f.val (Etingof.GL2.cosetRep p n (Etingof.GL2.cosetIndex p n g)) from by ring]
    rw [hborel_cancel, one_mul]
  simp_rw [hterm] at hker
  -- Now hker : ∑_g f.val(rep(cosetIndex g)) = 0
  -- Reindex via GL₂ ≃ B × Option(GaloisField)
  let e : GL2 p n ≃ ↥(Etingof.GL2.BorelSubgroup p n) × Option (GaloisField p n) :=
    { toFun := fun g => (Etingof.GL2.cosetBorel p n g, Etingof.GL2.cosetIndex p n g)
      invFun := fun bi => bi.1.val * Etingof.GL2.cosetRep p n bi.2
      left_inv := fun g => by
        simp only
        exact (Etingof.GL2.cosetBorel_mul_cosetRep p n g).symm
      right_inv := fun ⟨b, i⟩ => by
        simp only
        ext
        · have := Etingof.GL2.cosetBorel_borel_mul p n b (Etingof.GL2.cosetRep p n i)
          rw [this, Etingof.GL2.cosetBorel_cosetRep]; simp
        · rw [Etingof.GL2.cosetIndex_borel_mul, Etingof.GL2.cosetIndex_cosetRep] }
  rw [show (∑ g : GL2 p n, f.val (Etingof.GL2.cosetRep p n
      (Etingof.GL2.cosetIndex p n g))) =
    ∑ bi : ↥(Etingof.GL2.BorelSubgroup p n) × Option (GaloisField p n),
      f.val (Etingof.GL2.cosetRep p n bi.2) from
    Fintype.sum_equiv e _ _ (fun g => by simp [e])] at hker
  rw [Fintype.sum_prod_type] at hker
  -- ∑_{b ∈ B} 1 = |B|, so this is |B| * ∑_i f(rep(i)) = 0
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hker
  -- |B| * ∑_i f(rep(i)) = 0 and |B| ≠ 0
  have hB_ne : (Fintype.card ↥(Etingof.GL2.BorelSubgroup p n) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_pos.ne'
  have hsum_zero : ∑ i : Option (GaloisField p n),
      f.val (Etingof.GL2.cosetRep p n i) = 0 := by
    rcases mul_eq_zero.mp hker with h | h
    · exact absurd h hB_ne
    · exact h
  -- ∑_i f(rep(i)) = f(rep(none)) + ∑_t f(rep(some t))
  rw [Fintype.sum_option] at hsum_zero
  -- f(none) + ∑ f(some t) = 0 → f(none) = -∑ f(some t)
  linear_combination hsum_zero

/-- For f ∈ complementW with constant evaluations σ at all rep(some t),
    and t ≠ 0, the Weyl action ρ(w)(f) also evaluates to σ at rep(some t).
    This is because rep(some t)·w is in a "some" coset, f has constant value σ
    at all "some" reps, and the Borel character factor is 1 (since chi1 = chi2 = mu). -/
private lemma Etingof.GL2.complementW_weyl_const_ne
    (mu : (GaloisField p n)ˣ →* ℂˣ)
    (f : ↥(Etingof.GL2.complementWSubmodule p n mu))
    (σ : ℂ)
    (hconst : ∀ t : GaloisField p n,
      f.val (Etingof.GL2.cosetRep p n (some t)) = σ)
    (t : GaloisField p n) (ht : t ≠ 0) :
    (Etingof.GL2.complementWRep p n mu (Etingof.GL2.cosetRep p n (some 0)) f).val
      (Etingof.GL2.cosetRep p n (some t)) = σ := by
  -- LHS = f.val(rep(some t) * rep(some 0)) by definition
  change f.val (Etingof.GL2.cosetRep p n (some t) *
    Etingof.GL2.cosetRep p n (some 0)) = σ
  set M := Etingof.GL2.cosetRep p n (some t) * Etingof.GL2.cosetRep p n (some 0)
  -- M has nonzero (1,0) entry since t ≠ 0
  have h10 := Etingof.GL2.cosetRep_some_mul_weyl_not_borel p n t ht
  -- cosetIndex(M) = some s for some s
  have hM10 : (M.val : Matrix (Fin 2) (Fin 2) (GaloisField p n)) 1 0 ≠ 0 := by
    change ((Etingof.GL2.cosetRep p n (some t)).val *
      (Etingof.GL2.cosetRep p n (some 0)).val : Matrix _ _ _) 1 0 ≠ 0
    exact h10
  have hidx : ∃ s, Etingof.GL2.cosetIndex p n M = some s := by
    unfold Etingof.GL2.cosetIndex
    simp [hM10]
  obtain ⟨s, hs⟩ := hidx
  -- By covariance: f(M) = borelCharValue(cosetBorel M) * f(rep(some s))
  have hcov_f := f.prop.1
  have hcov_app := hcov_f (Etingof.GL2.cosetBorel p n M)
    (Etingof.GL2.cosetRep p n (Etingof.GL2.cosetIndex p n M))
  rw [← Etingof.GL2.cosetBorel_mul_cosetRep p n M] at hcov_app
  rw [hcov_app, hs, hconst s]
  -- Need: borelCharValue(cosetBorel M) = 1 when χ₁ = χ₂ = μ
  -- Since M = cosetBorel(M) * rep(some s), det M = det(cosetBorel M) * det(rep(some s))
  -- det M = det(rep(some t)) * det(rep(some 0)) = 1 * 1 = 1
  -- det(rep(some s)) = 1, so det(cosetBorel M) = 1
  -- borelCharValue(b) = μ(b₀₀) * μ(b₁₁) = μ(b₀₀ * b₁₁) = μ(det b) = μ(1) = 1
  suffices Etingof.GL2.borelCharValue p n mu mu (Etingof.GL2.cosetBorel p n M) = 1 by
    rw [this, one_mul]
  -- borelCharValue = μ(diag00) * μ(diag11), and for chi1=chi2=mu:
  -- this equals μ(diag00 * diag11) = μ(det(cosetBorel M))
  set b := Etingof.GL2.cosetBorel p n M
  have hb10 : (b.val.val : Matrix (Fin 2) (Fin 2) (GaloisField p n)) 1 0 = 0 := b.prop
  -- det(b) = b₀₀ * b₁₁ (since b₁₀ = 0)
  have hdet_b : Matrix.GeneralLinearGroup.det b.val =
    Units.mk0 ((b.val.val : Matrix _ _ _) 0 0) (Etingof.GL2.borel_diag00_ne_zero p n b) *
    Units.mk0 ((b.val.val : Matrix _ _ _) 1 1) (Etingof.GL2.borel_diag11_ne_zero p n b) := by
    ext; simp [Matrix.GeneralLinearGroup.det, Matrix.det_fin_two, hb10]
  -- det(M) = 1
  have hdet_M : Matrix.GeneralLinearGroup.det M = 1 := by
    simp only [M]
    rw [map_mul]
    have h1 : Matrix.GeneralLinearGroup.det (Etingof.GL2.cosetRep p n (some t)) = 1 := by
      ext; simp [Etingof.GL2.cosetRep, Matrix.GeneralLinearGroup.det,
        Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.GeneralLinearGroup.mk',
        Matrix.unitOfDetInvertible, Matrix.det_fin_two]
    have h2 : Matrix.GeneralLinearGroup.det (Etingof.GL2.cosetRep p n (some 0)) = 1 := by
      ext; simp [Etingof.GL2.cosetRep, Matrix.GeneralLinearGroup.det,
        Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.GeneralLinearGroup.mk',
        Matrix.unitOfDetInvertible, Matrix.det_fin_two]
    rw [h1, h2, mul_one]
  -- det(rep(some s)) = 1
  have hdet_rep_s : Matrix.GeneralLinearGroup.det (Etingof.GL2.cosetRep p n (some s)) = 1 := by
    ext; simp [Etingof.GL2.cosetRep, Matrix.GeneralLinearGroup.det,
      Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.GeneralLinearGroup.mk',
      Matrix.unitOfDetInvertible, Matrix.det_fin_two]
  -- det(b) = 1
  have hdet_b_one : Matrix.GeneralLinearGroup.det b.val = 1 := by
    have hdecomp := Etingof.GL2.cosetBorel_mul_cosetRep p n M
    rw [hs] at hdecomp
    have : Matrix.GeneralLinearGroup.det M =
      Matrix.GeneralLinearGroup.det b.val *
      Matrix.GeneralLinearGroup.det (Etingof.GL2.cosetRep p n (some s)) := by
      conv_lhs => rw [hdecomp]; rw [map_mul]
    rw [hdet_M, hdet_rep_s, mul_one] at this
    exact this.symm
  -- borelCharValue(b) = μ(b₀₀) * μ(b₁₁) = μ(b₀₀ * b₁₁) = μ(det b) = μ(1) = 1
  unfold Etingof.GL2.borelCharValue
  rw [hdet_b] at hdet_b_one
  -- det(b) = mk0(b₀₀) * mk0(b₁₁) = 1
  have hprod : Units.mk0 ((b.val.val : Matrix _ _ _) 0 0)
      (Etingof.GL2.borel_diag00_ne_zero p n b) *
    Units.mk0 ((b.val.val : Matrix _ _ _) 1 1)
      (Etingof.GL2.borel_diag11_ne_zero p n b) = 1 := hdet_b_one
  -- μ(b₀₀) * μ(b₁₁) = μ(b₀₀ * b₁₁) = μ(1) = 1
  have hmu : (mu (Units.mk0 ((b.val.val : Matrix _ _ _) 0 0)
      (Etingof.GL2.borel_diag00_ne_zero p n b)) : ℂˣ) *
    (mu (Units.mk0 ((b.val.val : Matrix _ _ _) 1 1)
      (Etingof.GL2.borel_diag11_ne_zero p n b)) : ℂˣ) = 1 := by
    rw [← map_mul, hprod, map_one]
  -- The goal has a `let` from borelCharValue unfolding; convert via Units.val
  have := congr_arg Units.val hmu
  simp only [Units.val_mul, Units.val_one] at this
  convert this using 1

/-- ρ(w)(f)(rep(some 0)) = f(rep(none)) for f ∈ complementW.
    Proof: rep(some 0)² = -I, and f(-I) = borelCharValue(-I)·f(1) = f(1)
    since mu(-1)² = 1. -/
private lemma Etingof.GL2.complementW_weyl_zero_eval
    (mu : (GaloisField p n)ˣ →* ℂˣ)
    (f : ↥(Etingof.GL2.complementWSubmodule p n mu)) :
    (Etingof.GL2.complementWRep p n mu (Etingof.GL2.cosetRep p n (some 0)) f).val
      (Etingof.GL2.cosetRep p n (some 0)) =
    f.val (Etingof.GL2.cosetRep p n none) := by
  -- LHS = f.val(rep(some 0) * rep(some 0)) by definition of complementWRep
  change f.val (Etingof.GL2.cosetRep p n (some 0) *
    Etingof.GL2.cosetRep p n (some 0)) = f.val (Etingof.GL2.cosetRep p n none)
  set w2 := Etingof.GL2.cosetRep p n (some 0) * Etingof.GL2.cosetRep p n (some 0)
  -- w2 ∈ B (its (1,0) entry is 0): w2 = [[0,-1],[1,0]]² = [[-1,0],[0,-1]]
  have hw2_borel : (w2.val : Matrix (Fin 2) (Fin 2) (GaloisField p n)) 1 0 = 0 := by
    simp [w2, Etingof.GL2.cosetRep, Matrix.GeneralLinearGroup.mkOfDetNeZero,
      Matrix.GeneralLinearGroup.mk', Matrix.unitOfDetInvertible,
      Matrix.mul_apply, Fin.sum_univ_two]
  -- Use covariance from f ∈ principalSeriesSubmodule (first component of complementWSubmodule)
  have hcov_f := f.prop.1  -- f.val ∈ principalSeriesSubmodule = covariant
  -- cosetIndex(w2) = none since w2 ∈ B
  have hidx : Etingof.GL2.cosetIndex p n w2 = none := by
    unfold Etingof.GL2.cosetIndex; simp [hw2_borel]
  -- cosetBorel(w2).val = w2 (since rep(none) = 1)
  have hcb : (Etingof.GL2.cosetBorel p n w2).val = w2 := by
    have := Etingof.GL2.cosetBorel_mul_cosetRep p n w2
    rw [hidx] at this; simp [Etingof.GL2.cosetRep] at this; exact this.symm
  -- By covariance: f(w2) = f(cosetBorel(w2) · rep(none)) = borelCharValue · f(rep(none))
  have hcov_app := hcov_f (Etingof.GL2.cosetBorel p n w2)
    (Etingof.GL2.cosetRep p n none)
  rw [show (Etingof.GL2.cosetBorel p n w2).val * Etingof.GL2.cosetRep p n none = w2 from by
    rw [hcb]; simp [Etingof.GL2.cosetRep]] at hcov_app
  rw [hcov_app]
  -- Need: borelCharValue(cosetBorel w2) = 1
  -- w2 diagonal entries are both -1
  have h00 : ((Etingof.GL2.cosetBorel p n w2).val.val :
      Matrix (Fin 2) (Fin 2) (GaloisField p n)) 0 0 = -1 := by
    rw [show (Etingof.GL2.cosetBorel p n w2).val = w2 from hcb]
    simp [w2, Etingof.GL2.cosetRep, Matrix.GeneralLinearGroup.mkOfDetNeZero,
      Matrix.GeneralLinearGroup.mk', Matrix.unitOfDetInvertible,
      Matrix.mul_apply, Fin.sum_univ_two]
  have h11 : ((Etingof.GL2.cosetBorel p n w2).val.val :
      Matrix (Fin 2) (Fin 2) (GaloisField p n)) 1 1 = -1 := by
    rw [show (Etingof.GL2.cosetBorel p n w2).val = w2 from hcb]
    simp [w2, Etingof.GL2.cosetRep, Matrix.GeneralLinearGroup.mkOfDetNeZero,
      Matrix.GeneralLinearGroup.mk', Matrix.unitOfDetInvertible,
      Matrix.mul_apply, Fin.sum_univ_two]
  -- borelCharValue(cosetBorel w2) = μ(diag00) * μ(diag11) = μ(-1) * μ(-1) = 1
  change Etingof.GL2.borelCharValue p n mu mu (Etingof.GL2.cosetBorel p n w2) *
    f.val (Etingof.GL2.cosetRep p n none) = f.val (Etingof.GL2.cosetRep p n none)
  have hbcv : Etingof.GL2.borelCharValue p n mu mu (Etingof.GL2.cosetBorel p n w2) = 1 := by
    unfold Etingof.GL2.borelCharValue
    -- Units.mk0 (diag00) ... where diag00 = -1
    have h00' : Units.mk0 (((Etingof.GL2.cosetBorel p n w2).val.val :
        Matrix (Fin 2) (Fin 2) (GaloisField p n)) 0 0)
        (Etingof.GL2.borel_diag00_ne_zero p n _) = -1 := by
      ext; simp [h00]
    have h11' : Units.mk0 (((Etingof.GL2.cosetBorel p n w2).val.val :
        Matrix (Fin 2) (Fin 2) (GaloisField p n)) 1 1)
        (Etingof.GL2.borel_diag11_ne_zero p n _) = -1 := by
      ext; simp [h11]
    simp only [h00', h11']
    simp [← Units.val_mul, ← map_mul]
  rw [hbcv, one_mul]

/-- W_μ is irreducible.

Proof: Direct irreducibility via evaluation map.
Take any nonzero subrepresentation S of W_μ and show S = W_μ.
1. Get nonzero f ∈ S with f(rep(some 0)) ≠ 0 (by translation)
2. If needed, apply Weyl to ensure sum of evals is nonzero
3. Average over translations to get constant-evaluation element A
4. h = ρ(w)(A) - A is a "delta at rep(some 0)" in S
5. Translate h to get deltas at all points, spanning W_μ -/
private lemma Etingof.GL2.complementW_simple
    (mu : (GaloisField p n)ˣ →* ℂˣ) :
    Simple (Etingof.GL2.complementW p n mu) := by
  haveI : NeZero (Nat.card (GL2 p n) : ℂ) := ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  set ρ := Etingof.GL2.complementWRep p n mu
  -- Bridge: Simple FDRep ← IsSimpleModule ← IsSimpleOrder Subrepresentation
  suffices IsSimpleModule (MonoidAlgebra ℂ (GL2 p n)) ρ.asModule by
    haveI := this; exact simple_of_isSimpleModule_FDRep ρ
  rw [← Representation.irreducible_iff_isSimpleModule_asModule]
  -- Nontriviality: W_μ ≠ 0
  haveI : Nontrivial (Subrepresentation ρ) := by
    obtain ⟨f, hf⟩ := Etingof.GL2.complementW_eval_surjective p n mu
      (fun t => if t = (0 : GaloisField p n) then 1 else 0)
    have hfne : f ≠ 0 := by
      intro h; rw [h] at hf; simp at hf
    exact nontrivial_of_ne ⊥ ⊤ (by
      intro heq; apply hfne
      have : f ∈ (⊥ : Subrepresentation ρ).toSubmodule := heq ▸ Submodule.mem_top
      simpa using this)
  exact IsSimpleOrder.mk fun S => by
    by_cases hS : S = ⊥
    · exact Or.inl hS
    · right
      -- S ≠ ⊥ → ∃ nonzero f ∈ S
      have hSne : S.toSubmodule ≠ ⊥ := by
        intro heq; exact hS (Subrepresentation.toSubmodule_injective heq)
      rw [ne_eq, Submodule.eq_bot_iff] at hSne; push_neg at hSne
      obtain ⟨f, hfS, hfne⟩ := hSne
      -- f ≠ 0 → ∃ t₀ with f(rep(some t₀)) ≠ 0
      have hsome : ∃ t₀, f.val (Etingof.GL2.cosetRep p n (some t₀)) ≠ 0 := by
        by_contra hall; push_neg at hall
        exact hfne (Etingof.GL2.complementW_eval_injective p n mu f hall)
      obtain ⟨t₀, ht₀⟩ := hsome
      -- Step 1: Translate to get f' with f'(rep(some 0)) ≠ 0
      set f' := ρ (Etingof.GL2.translationElt p n t₀) f
      have hf'S : f' ∈ S.toSubmodule := S.apply_mem_toSubmodule _ hfS
      have hf'_eval0 : f'.val (Etingof.GL2.cosetRep p n (some 0)) ≠ 0 := by
        change f.val (Etingof.GL2.cosetRep p n (some 0) *
          Etingof.GL2.translationElt p n t₀) ≠ 0
        rw [Etingof.GL2.cosetRep_mul_translation_some, zero_add]
        exact ht₀
      -- Step 2: Get g ∈ S with nonzero eval-sum σ and g(rep(some 0)) ≠ 0
      -- If ∑_t f'(rep(some t)) ≠ 0, use f'.
      -- If = 0, then f'(rep(none)) = 0, so ρ(w)(f') has ρ(w)(f')(rep(none)) = f'(rep(some 0)) ≠ 0.
      -- The eval-sum of ρ(w)(f') is -ρ(w)(f')(rep(none)) = -f'(rep(some 0)) ≠ 0.
      set σ₀ := ∑ t : GaloisField p n, f'.val (Etingof.GL2.cosetRep p n (some t))
      -- Get g ∈ S with nonzero eval-sum
      obtain ⟨g, hgS, hg_sum_ne⟩ : ∃ g ∈ S.toSubmodule,
          ∑ t : GaloisField p n, g.val (Etingof.GL2.cosetRep p n (some t)) ≠ 0 := by
        by_cases hσ : σ₀ ≠ 0
        · exact ⟨f', hf'S, hσ⟩
        · push_neg at hσ
          -- σ₀ = 0 → f'(rep(none)) = -σ₀ = 0
          have hf'_none : f'.val (Etingof.GL2.cosetRep p n none) = 0 := by
            rw [Etingof.GL2.complementW_none_eq_neg_sum]
            change -σ₀ = 0
            rw [hσ, neg_zero]
          -- Apply Weyl: ρ(w)(f') ∈ S with nonzero eval-sum
          set g := ρ (Etingof.GL2.cosetRep p n (some 0)) f'
          refine ⟨g, S.apply_mem_toSubmodule _ hf'S, ?_⟩
          -- eval-sum of g = -g(rep(none))
          rw [show ∑ t, g.val (Etingof.GL2.cosetRep p n (some t)) =
            -(g.val (Etingof.GL2.cosetRep p n none)) from by
            rw [Etingof.GL2.complementW_none_eq_neg_sum]; ring]
          -- g(rep(none)) = f'(rep(none) · w) = f'(1 · w) = f'(w) = f'(rep(some 0))
          change -(f'.val (Etingof.GL2.cosetRep p n none *
            Etingof.GL2.cosetRep p n (some 0))) ≠ 0
          rw [show Etingof.GL2.cosetRep p n none * Etingof.GL2.cosetRep p n (some 0) =
            Etingof.GL2.cosetRep p n (some 0) from by simp [Etingof.GL2.cosetRep]]
          exact neg_ne_zero.mpr hf'_eval0
      -- Step 3: Average g over translations to get A with constant evals
      set σ := ∑ t : GaloisField p n, g.val (Etingof.GL2.cosetRep p n (some t))
      set A := ∑ s : GaloisField p n, ρ (Etingof.GL2.translationElt p n s) g
      have hAS : A ∈ S.toSubmodule :=
        S.toSubmodule.sum_mem (fun s _ => S.apply_mem_toSubmodule _ hgS)
      -- A has constant evaluation σ at all rep(some t)
      have hA_const : ∀ t : GaloisField p n,
          A.val (Etingof.GL2.cosetRep p n (some t)) = σ := by
        intro t
        simp only [A, Submodule.coe_sum, Finset.sum_apply]
        simp_rw [show ∀ s, (ρ (Etingof.GL2.translationElt p n s) g).val
          (Etingof.GL2.cosetRep p n (some t)) =
          g.val (Etingof.GL2.cosetRep p n (some (t + s))) from
          fun s => by change g.val (Etingof.GL2.cosetRep p n (some t) *
            Etingof.GL2.translationElt p n s) = _; rw [Etingof.GL2.cosetRep_mul_translation_some]]
        exact Fintype.sum_equiv (Equiv.addLeft t) _ _ (fun s => rfl)
      -- σ ≠ 0
      have hσ_ne : σ ≠ 0 := hg_sum_ne
      -- Step 4: A(rep(none)) = -qσ (by augmentation kernel)
      have hA_none : A.val (Etingof.GL2.cosetRep p n none) =
          -(Fintype.card (GaloisField p n) : ℂ) * σ := by
        rw [Etingof.GL2.complementW_none_eq_neg_sum]
        simp_rw [hA_const]
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, neg_mul]
      -- Step 5: Form h = ρ(w)(A) - A. This has eval 0 at rep(some t) for t ≠ 0
      set w := Etingof.GL2.cosetRep p n (some 0)
      set wA := ρ w A
      have hwAS : wA ∈ S.toSubmodule := S.apply_mem_toSubmodule _ hAS
      -- wA(rep(some t)) = σ for t ≠ 0 (by complementW_weyl_const_ne)
      have hwA_ne : ∀ t : GaloisField p n, t ≠ 0 →
          wA.val (Etingof.GL2.cosetRep p n (some t)) = σ :=
        fun t ht => Etingof.GL2.complementW_weyl_const_ne p n mu A σ hA_const t ht
      -- wA(rep(some 0)) = A(rep(none)) = -qσ
      have hwA_zero : wA.val (Etingof.GL2.cosetRep p n (some 0)) =
          -(Fintype.card (GaloisField p n) : ℂ) * σ := by
        rw [Etingof.GL2.complementW_weyl_zero_eval]; exact hA_none
      set h := wA - A
      have hhS : h ∈ S.toSubmodule := S.toSubmodule.sub_mem hwAS hAS
      -- h(rep(some t)) = 0 for t ≠ 0
      have hh_ne : ∀ t : GaloisField p n, t ≠ 0 →
          h.val (Etingof.GL2.cosetRep p n (some t)) = 0 := by
        intro t ht
        change wA.val (Etingof.GL2.cosetRep p n (some t)) -
          A.val (Etingof.GL2.cosetRep p n (some t)) = 0
        rw [hwA_ne t ht, hA_const t, sub_self]
      -- h(rep(some 0)) ≠ 0
      have hh_zero_ne : h.val (Etingof.GL2.cosetRep p n (some 0)) ≠ 0 := by
        change wA.val (Etingof.GL2.cosetRep p n (some 0)) -
          A.val (Etingof.GL2.cosetRep p n (some 0)) ≠ 0
        rw [hwA_zero, hA_const]
        -- Need: -q·σ - σ ≠ 0, i.e., -(q+1)·σ ≠ 0
        intro heq
        apply hσ_ne
        have h1 : -(Fintype.card (GaloisField p n) : ℂ) * σ - σ = 0 := heq
        have h2 : -((Fintype.card (GaloisField p n) : ℂ) + 1) * σ = 0 := by
          have : -((Fintype.card (GaloisField p n) : ℂ) + 1) * σ =
              -(Fintype.card (GaloisField p n) : ℂ) * σ - σ := by ring
          rw [this]; exact h1
        have hqp1 : ((Fintype.card (GaloisField p n) : ℂ) + 1) ≠ 0 :=
          Nat.cast_add_one_ne_zero _
        rcases mul_eq_zero.mp h2 with hq | hσ
        · exact absurd (neg_eq_zero.mp hq) hqp1
        · exact hσ
      -- Step 6: For each u, T_u(h) is a "delta at u" in S
      -- T_u(h)(rep(some t)) = h(rep(some(t+u))) = 0 if t+u ≠ 0, i.e., t ≠ -u
      -- T_u(h)(rep(some(-u))) = h(rep(some 0)) ≠ 0
      -- Step 7: Show every element of W_μ is in S
      -- For any x ∈ W_μ, write x = ∑_u (x(rep(some(-u))) / h(rep(some 0))) • T_u(h)
      -- This works because the T_u(h) form a "delta basis" (via evaluation)
      apply Subrepresentation.toSubmodule_injective
      apply le_antisymm le_top
      intro x _
      -- Express x as a linear combination of T_u(h) (translates of h)
      set α := h.val (Etingof.GL2.cosetRep p n (some 0))
      have hα_ne : α ≠ 0 := hh_zero_ne
      set rhs := ∑ u : GaloisField p n,
        (α⁻¹ * x.val (Etingof.GL2.cosetRep p n (some u))) •
          ρ (Etingof.GL2.translationElt p n (-u)) h
      have hrhs_S : rhs ∈ S.toSubmodule := by
        apply S.toSubmodule.sum_mem; intro u _
        exact S.toSubmodule.smul_mem _ (S.apply_mem_toSubmodule _ hhS)
      suffices heq : x = rhs by rw [heq]; exact hrhs_S
      -- Prove x = rhs by showing they agree on all "some" evaluations
      have hxrhs := Etingof.GL2.complementW_eval_injective p n mu (x - rhs)
      rw [sub_eq_zero] at hxrhs; apply hxrhs; intro t
      change x.val (Etingof.GL2.cosetRep p n (some t)) -
        (∑ u : GaloisField p n,
          (α⁻¹ * x.val (Etingof.GL2.cosetRep p n (some u))) •
            ρ (Etingof.GL2.translationElt p n (-u)) h).val
          (Etingof.GL2.cosetRep p n (some t)) = 0
      simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply,
        Pi.smul_apply, smul_eq_mul]
      -- Each translate: (ρ(τ_{-u})(h))(rep(some t)) = h(rep(some(t + (-u)))) = h(rep(some(t-u)))
      simp_rw [show ∀ u, (ρ (Etingof.GL2.translationElt p n (-u)) h).val
        (Etingof.GL2.cosetRep p n (some t)) =
        h.val (Etingof.GL2.cosetRep p n (some (t + (-u)))) from fun u => by
        change h.val (Etingof.GL2.cosetRep p n (some t) *
          Etingof.GL2.translationElt p n (-u)) = _
        rw [Etingof.GL2.cosetRep_mul_translation_some]]
      -- Only u = t contributes (h is zero at nonzero args)
      conv_lhs => arg 2; arg 2; ext u; rw [show t + -u = t - u from by ring]
      rw [show (∑ u : GaloisField p n,
          α⁻¹ * x.val (Etingof.GL2.cosetRep p n (some u)) *
          h.val (Etingof.GL2.cosetRep p n (some (t - u)))) =
        α⁻¹ * x.val (Etingof.GL2.cosetRep p n (some t)) *
          h.val (Etingof.GL2.cosetRep p n (some 0)) from by
        rw [← Finset.sum_subset (Finset.subset_univ {t}) (fun u _ hu => by
          simp only [Finset.mem_singleton] at hu
          rw [hh_ne (t - u) (sub_ne_zero.mpr (Ne.symm hu)), mul_zero])]
        simp [sub_self]]
      rw [show h.val (Etingof.GL2.cosetRep p n (some 0)) = α from rfl]
      rw [mul_comm (α⁻¹) _, mul_assoc, inv_mul_cancel₀ hα_ne, mul_one, sub_self]

/-- The evaluation map from complementW to (GaloisField → ℂ). -/
private noncomputable def Etingof.GL2.complementW_evalMap
    (mu : (GaloisField p n)ˣ →* ℂˣ) :
    ↥(Etingof.GL2.complementWSubmodule p n mu) →ₗ[ℂ] (GaloisField p n → ℂ) where
  toFun f t := (f : GL2 p n → ℂ) (Etingof.GL2.cosetRep p n (some t))
  map_add' f g := by ext; simp
  map_smul' c f := by ext; simp [smul_eq_mul]

/-- Helper: dim W_μ = q = p^n. Since dim V(μ,μ) = [G:B] = q+1 and
dim ℂ_μ = 1, we get dim W_μ = q. -/
private lemma Etingof.GL2.complementW_finrank
    (hn : 0 < n)
    (mu : (GaloisField p n)ˣ →* ℂˣ) :
    Module.finrank ℂ (Etingof.GL2.complementW p n mu).V = p ^ n := by
  -- Show dim(complementWSubmodule) = p^n via linear bijection with (GaloisField p n → ℂ)
  -- The evaluation map eval : complementWSubmodule → (GaloisField p n → ℂ) is a bijection
  have hinj : Function.Injective (Etingof.GL2.complementW_evalMap p n mu) := by
    intro f g heq
    have : f - g = 0 := by
      apply Etingof.GL2.complementW_eval_injective
      intro t
      have := congr_fun heq t
      simp [Etingof.GL2.complementW_evalMap] at this
      simp [this]
    exact sub_eq_zero.mp this
  have hsurj : Function.Surjective (Etingof.GL2.complementW_evalMap p n mu) := by
    intro c
    obtain ⟨f, hf⟩ := Etingof.GL2.complementW_eval_surjective p n mu c
    exact ⟨f, funext hf⟩
  -- Use the linear equivalence to compute dimension
  have hequiv : ↥(Etingof.GL2.complementWSubmodule p n mu) ≃ₗ[ℂ] (GaloisField p n → ℂ) :=
    LinearEquiv.ofBijective (Etingof.GL2.complementW_evalMap p n mu) ⟨hinj, hsurj⟩
  -- complementW.V = complementWSubmodule (by definition)
  change Module.finrank ℂ ↥(Etingof.GL2.complementWSubmodule p n mu) = p ^ n
  rw [hequiv.finrank_eq, Module.finrank_pi_fintype, Module.finrank_self]
  simp only [Finset.sum_const, smul_eq_mul, mul_one]
  rw [Finset.card_univ, Fintype.card_eq_nat_card, GaloisField.card p n (Nat.pos_iff_ne_zero.mp hn)]

/-- **Theorem 5.25.2 (2)**: If χ₁ = χ₂ = μ, then V(μ, μ) ≅ ℂ_μ ⊕ W_μ where
W_μ is an irreducible q-dimensional representation. (Etingof Theorem 5.25.2) -/
theorem Etingof.Theorem5_25_2_part2
    (hn : 0 < n)
    (mu : (GaloisField p n)ˣ →* ℂˣ) :
    (Nonempty (Etingof.GL2.principalSeries p n mu mu ≅
      Etingof.GL2.detChar p n mu ⊞ Etingof.GL2.complementW p n mu)) ∧
    Simple (Etingof.GL2.complementW p n mu) ∧
    Module.finrank ℂ (Etingof.GL2.complementW p n mu).V = p ^ n :=
  ⟨Etingof.GL2.principalSeries_decomp p n mu,
   Etingof.GL2.complementW_simple p n mu,
   Etingof.GL2.complementW_finrank p n hn mu⟩

/-- The action of diagElt(c) on a complementW element at cosetRep(some t)
gives mu(c) * f(cosetRep(some(t * c⁻¹))). This is the W_μ version of
action_diagonal_some. -/
private lemma Etingof.GL2.complementW_action_diagonal_some
    (mu : (GaloisField p n)ˣ →* ℂˣ)
    (f : ↥(Etingof.GL2.complementWSubmodule p n mu))
    (c : (GaloisField p n)ˣ) (t : GaloisField p n) :
    (Etingof.GL2.complementWRep p n mu (Etingof.GL2.diagElt p n c) f).val
      (Etingof.GL2.cosetRep p n (some t)) =
    (mu c : ℂ) * f.val (Etingof.GL2.cosetRep p n (some (t * ↑c⁻¹))) := by
  -- The complementWRep action is the same as principalSeriesRep on the underlying function
  change f.val (Etingof.GL2.cosetRep p n (some t) * Etingof.GL2.diagElt p n c) = _
  -- Use the principalSeries action formula (same proof as action_diagonal_some with chi1=chi2=mu)
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
    · field_simp
  rw [hprod]
  have hcov := f.prop.1 ⟨b, hb_mem⟩ (Etingof.GL2.cosetRep p n (some (t * ↑c⁻¹)))
  rw [hcov]
  congr 1
  simp [Etingof.GL2.borelCharValue, b, bmat,
    Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.GeneralLinearGroup.mk',
    Matrix.unitOfDetInvertible]

/-- The permutation action on 𝔽_q → ℂ given by (σ_c · f)(t) = f(t * c⁻¹). -/
private noncomputable def Etingof.GL2.permAction
    (c : (GaloisField p n)ˣ) : (GaloisField p n → ℂ) →ₗ[ℂ] (GaloisField p n → ℂ) where
  toFun f t := f (t * ↑c⁻¹)
  map_add' f g := by ext t; simp [Pi.add_apply]
  map_smul' r f := by ext t; simp [Pi.smul_apply, smul_eq_mul]

set_option maxHeartbeats 800000 in
/-- The trace of the permutation t ↦ t * c⁻¹ on 𝔽_q → ℂ.
For c ≠ 1, only t = 0 is a fixed point, so the trace is 1. -/
private lemma Etingof.GL2.trace_permAction
    (c : (GaloisField p n)ˣ) (hc : c ≠ 1) :
    LinearMap.trace ℂ (GaloisField p n → ℂ) (Etingof.GL2.permAction p n c) = 1 := by
  rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (GaloisField p n))]
  simp only [Matrix.trace, Matrix.diag]
  -- Need to compute diagonal entries of the matrix representation
  -- M_{i,i} = coefficient of e_i in permAction(c)(e_i) = (permAction(c)(e_i))(i) = e_i(i * c⁻¹)
  -- = if i = i * c⁻¹ then 1 else 0
  -- For c ≠ 1: only i = 0 satisfies i = i * c⁻¹
  have hcinv_ne_one : (↑c⁻¹ : GaloisField p n) ≠ 1 := by
    intro h
    apply hc
    have : c⁻¹ = 1 := Units.val_eq_one.mp h
    rw [inv_eq_one] at this
    exact this
  have hfixed : ∀ i : GaloisField p n, i * ↑c⁻¹ = i ↔ i = 0 := by
    intro i
    constructor
    · intro h
      by_contra hi
      apply hcinv_ne_one
      have : i * ↑c⁻¹ = i * 1 := by rw [mul_one]; exact h
      exact mul_left_cancel₀ hi this
    · intro h; rw [h, zero_mul]
  -- Each diagonal entry of the matrix is: (permAction(c)(e_i))(i)
  -- = e_i(i * c⁻¹) = if i*c⁻¹ = i then 1 else 0
  -- By hfixed, only i = 0 contributes, so the sum = 1
  have hentry : ∀ i : GaloisField p n,
      (Pi.basisFun ℂ (GaloisField p n)).repr
        (Etingof.GL2.permAction p n c ((Pi.basisFun ℂ (GaloisField p n)) i)) i =
      if i = 0 then (1 : ℂ) else 0 := by
    intro i
    simp only [Pi.basisFun_apply, Pi.basisFun_repr, Etingof.GL2.permAction,
      LinearMap.coe_mk, AddHom.coe_mk, Pi.single_apply, hfixed]
  simp_rw [LinearMap.toMatrix_apply, hentry]
  simp [Finset.sum_ite_eq', Finset.mem_univ]

set_option maxHeartbeats 800000 in
private lemma Etingof.GL2.complementW_char_diagElt
    (mu : (GaloisField p n)ˣ →* ℂˣ)
    (c : (GaloisField p n)ˣ) (hc : c ≠ 1) :
    FDRep.character (Etingof.GL2.complementW p n mu)
      (Etingof.GL2.diagElt p n c) = (mu c : ℂ) := by
  -- The character is the trace of the action
  simp only [FDRep.character]
  -- Transfer trace to (GaloisField p n → ℂ) via the evaluation equivalence
  have hinj : Function.Injective (Etingof.GL2.complementW_evalMap p n mu) := by
    intro f g heq
    have : f - g = 0 := by
      apply Etingof.GL2.complementW_eval_injective
      intro t
      have := congr_fun heq t
      simp [Etingof.GL2.complementW_evalMap] at this
      simp [this]
    exact sub_eq_zero.mp this
  have hsurj : Function.Surjective (Etingof.GL2.complementW_evalMap p n mu) := by
    intro c
    obtain ⟨f, hf⟩ := Etingof.GL2.complementW_eval_surjective p n mu c
    exact ⟨f, funext hf⟩
  set e := LinearEquiv.ofBijective (Etingof.GL2.complementW_evalMap p n mu) ⟨hinj, hsurj⟩
  -- trace on complementWSubmodule = trace of conjugated map on (GaloisField → ℂ)
  rw [show (LinearMap.trace ℂ _)
      ((Etingof.GL2.complementW p n mu).ρ (Etingof.GL2.diagElt p n c)) =
    (LinearMap.trace ℂ _) (e.conj
      ((Etingof.GL2.complementW p n mu).ρ (Etingof.GL2.diagElt p n c))) from
    (LinearMap.trace_conj' _ e).symm]
  -- The conjugated map is μ(c) • permAction
  have hconj : e.conj ((Etingof.GL2.complementW p n mu).ρ (Etingof.GL2.diagElt p n c)) =
      (mu c : ℂ) • Etingof.GL2.permAction p n c := by
    apply LinearMap.ext; intro g
    apply funext; intro t
    simp only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearMap.smul_apply,
      Etingof.GL2.permAction, LinearMap.coe_mk, AddHom.coe_mk, smul_eq_mul,
      Pi.smul_apply]
    -- Use the action formula: (diagElt c · e⁻¹(g))(rep(some t)) = μ(c) * e⁻¹(g)(rep(some(t*c⁻¹)))
    have hact := Etingof.GL2.complementW_action_diagonal_some p n mu (e.symm g) c t
    -- The LHS after unfolding e = complementW_evalMap
    change (Etingof.GL2.complementWRep p n mu (Etingof.GL2.diagElt p n c) (e.symm g)).val
      (Etingof.GL2.cosetRep p n (some t)) = _
    rw [hact]
    congr 1
    -- (e⁻¹(g))(cosetRep(some(t*c⁻¹))) = g(t*c⁻¹) by definition of e
    exact congr_fun (e.apply_symm_apply g) (t * ↑c⁻¹)
  rw [hconj, map_smul, Etingof.GL2.trace_permAction p n c hc, smul_eq_mul, mul_one]

private lemma Etingof.GL2.complementW_iso_implies_eq
    (mu nu : (GaloisField p n)ˣ →* ℂˣ)
    (iso : Etingof.GL2.complementW p n mu ≅ Etingof.GL2.complementW p n nu) :
    mu = nu := by
  -- Step 1: Isomorphic reps have equal characters
  have hchar : FDRep.character (Etingof.GL2.complementW p n mu) =
    FDRep.character (Etingof.GL2.complementW p n nu) := FDRep.char_iso iso
  -- Step 2: Extract pointwise equality from character equality at diagElt(c)
  ext c
  by_cases hc : c = 1
  · subst hc; simp
  · have h1 := Etingof.GL2.complementW_char_diagElt p n mu c hc
    have h2 := Etingof.GL2.complementW_char_diagElt p n nu c hc
    have h3 := congr_fun hchar (Etingof.GL2.diagElt p n c)
    rw [h1, h2] at h3
    exact_mod_cast h3

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

/-- Character orthogonality: sum of nontrivial character values is zero. -/
private lemma Etingof.GL2.sum_nontrivial_char_eq_zero
    {G : Type*} [CommGroup G] [Fintype G]
    (χ : G →* ℂˣ) (hχ : χ ≠ 1) :
    ∑ g : G, (χ g : ℂ) = 0 := by
  have ⟨g₀, hg₀⟩ : ∃ g₀, χ g₀ ≠ 1 := by
    by_contra h; push_neg at h; exact absurd (MonoidHom.ext h) hχ
  have hne : (χ g₀ : ℂ) ≠ 1 := fun h => hg₀ (Units.val_injective h)
  have key : (χ g₀ : ℂ) * ∑ g, (χ g : ℂ) = ∑ g, (χ g : ℂ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_nbij (fun g => g₀ * g)
    · intro g _; exact Finset.mem_univ _
    · intro g₁ _ g₂ _ h; exact mul_left_cancel h
    · intro g _; exact ⟨g₀⁻¹ * g, Finset.mem_univ _, by group⟩
    · intro g _; simp only [map_mul, Units.val_mul]
  have h1 : ((χ g₀ : ℂ) - 1) * ∑ g, (χ g : ℂ) = 0 := by
    rw [sub_mul, one_mul, sub_eq_zero]; exact key
  exact (mul_eq_zero.mp h1).resolve_left (sub_ne_zero.mpr hne)

/-- Factorization: cosetRep(some u) * b = diagBorel * cosetRep(some v)
    where diagBorel has (0,0)=b₁₁, (1,1)=b₀₀ and v = (b₀₁ + u*b₁₁)/b₀₀. -/
private lemma Etingof.GL2.cosetRep_some_mul_borel_factor
    (u : GaloisField p n) (b : ↥(Etingof.GL2.BorelSubgroup p n)) :
    let bm := (b.val.val : Matrix (Fin 2) (Fin 2) (GaloisField p n))
    let a := bm 0 0
    let d := bm 1 1
    let c := bm 0 1
    let v := (c + u * d) / a
    ∃ b' : ↥(Etingof.GL2.BorelSubgroup p n),
      Etingof.GL2.cosetRep p n (some u) * b.val = b'.val *
        Etingof.GL2.cosetRep p n (some v) ∧
      (b'.val.val : Matrix (Fin 2) (Fin 2) (GaloisField p n)) 0 0 = d ∧
      (b'.val.val : Matrix (Fin 2) (Fin 2) (GaloisField p n)) 1 1 = a := by
  set bm := (b.val.val : Matrix (Fin 2) (Fin 2) (GaloisField p n))
  set a := bm 0 0
  set d := bm 1 1
  set c := bm 0 1
  set v := (c + u * d) / a
  have ha : a ≠ 0 := Etingof.GL2.borel_diag00_ne_zero p n b
  have hd : d ≠ 0 := Etingof.GL2.borel_diag11_ne_zero p n b
  set b'mat : Matrix (Fin 2) (Fin 2) (GaloisField p n) := !![d, 0; 0, a]
  have hb'det : b'mat.det ≠ 0 := by
    simp only [b'mat, Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_one, Matrix.vecHead,
      Matrix.vecTail, mul_zero, sub_zero]
    exact mul_ne_zero hd ha
  set b'gl := Matrix.GeneralLinearGroup.mkOfDetNeZero b'mat hb'det
  have hb'mem : (b'gl.val : Matrix (Fin 2) (Fin 2) (GaloisField p n)) 1 0 = 0 := by
    simp [b'gl, b'mat, Matrix.GeneralLinearGroup.mkOfDetNeZero,
      Matrix.GeneralLinearGroup.mk', Matrix.unitOfDetInvertible]
  refine ⟨⟨b'gl, hb'mem⟩, ?_, ?_, ?_⟩
  · -- Matrix identity: r_u * b = b' * r_v
    apply Matrix.GeneralLinearGroup.ext; intro i j
    simp only [Matrix.GeneralLinearGroup.coe_mul,
      Etingof.GL2.cosetRep,
      Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.GeneralLinearGroup.mk',
      Matrix.unitOfDetInvertible, Matrix.mul_apply, Fin.sum_univ_two,
      b'mat, b'gl]
    have hb10 : bm 1 0 = 0 := b.prop
    have ha' : (b.val.val : Matrix (Fin 2) (Fin 2) (GaloisField p n)) 0 0 ≠ 0 := ha
    fin_cases i <;> fin_cases j <;>
      simp [hb10, a, d, c, v, bm, b'mat, b'gl,
        Matrix.GeneralLinearGroup.coe_mul, Etingof.GL2.cosetRep,
        Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.GeneralLinearGroup.mk',
        Matrix.unitOfDetInvertible, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val',
        Matrix.cons_val_one, Matrix.vecHead, Matrix.vecTail] <;>
      (try field_simp [ha', ha, hd]) <;> ring
  · -- (0,0) entry of b' is d
    simp only [b'gl, b'mat, Matrix.GeneralLinearGroup.mkOfDetNeZero,
      Matrix.GeneralLinearGroup.mk', Matrix.unitOfDetInvertible,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val',
      Matrix.cons_val_one, Matrix.vecHead, Matrix.vecTail]; rfl
  · -- (1,1) entry of b' is a
    simp only [b'gl, b'mat, Matrix.GeneralLinearGroup.mkOfDetNeZero,
      Matrix.GeneralLinearGroup.mk', Matrix.unitOfDetInvertible,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val',
      Matrix.cons_val_one, Matrix.vecHead, Matrix.vecTail]; rfl

/-- The intertwining sum ∑_u f(r_u * b * g) = χ₂(b₀₀)·χ₁(b₁₁) · ∑_u f(r_u * g). -/
private lemma Etingof.GL2.intertwining_sum_covariant
    (chi1 chi2 : (GaloisField p n)ˣ →* ℂˣ)
    (f : ↥(Etingof.GL2.principalSeriesSubmodule p n chi1 chi2))
    (b : ↥(Etingof.GL2.BorelSubgroup p n)) (g : GL2 p n) :
    ∑ u : GaloisField p n,
      f.val (Etingof.GL2.cosetRep p n (some u) * (b.val * g)) =
    Etingof.GL2.borelCharValue p n chi2 chi1 b *
      ∑ u : GaloisField p n,
        f.val (Etingof.GL2.cosetRep p n (some u) * g) := by
  set bm := (b.val.val : Matrix (Fin 2) (Fin 2) (GaloisField p n))
  set a := bm 0 0
  set d := bm 1 1
  set c := bm 0 1
  have ha : a ≠ 0 := Etingof.GL2.borel_diag00_ne_zero p n b
  have hd : d ≠ 0 := Etingof.GL2.borel_diag11_ne_zero p n b
  -- Rewrite each term using the factorization
  have hterm : ∀ u : GaloisField p n,
      f.val (Etingof.GL2.cosetRep p n (some u) * (b.val * g)) =
      Etingof.GL2.borelCharValue p n chi2 chi1 b *
        f.val (Etingof.GL2.cosetRep p n (some ((c + u * d) / a)) * g) := by
    intro u
    obtain ⟨b', hfact, hb'00, hb'11⟩ :=
      Etingof.GL2.cosetRep_some_mul_borel_factor p n u b
    rw [← mul_assoc, hfact, mul_assoc]
    -- Apply covariance of f
    have hcov := f.prop b' (Etingof.GL2.cosetRep p n (some ((c + u * d) / a)) * g)
    rw [hcov]
    -- Show the borel char values match
    -- borelCharValue chi1 chi2 b' = chi1(b'₀₀) * chi2(b'₁₁) = chi1(d) * chi2(a)
    -- borelCharValue chi2 chi1 b = chi2(b₀₀) * chi1(b₁₁) = chi2(a) * chi1(d)
    unfold Etingof.GL2.borelCharValue
    simp only [hb'00, hb'11]
    ring
  simp_rw [hterm, ← Finset.mul_sum]
  congr 1
  -- Change of variable: u ↦ (c + u * d) / a is bijection on 𝔽_q
  apply Fintype.sum_equiv
    (show GaloisField p n ≃ GaloisField p n from
      { toFun := fun u => (c + u * d) / a
        invFun := fun v => (v * a - c) / d
        left_inv := fun u => by field_simp; ring
        right_inv := fun v => by field_simp; ring })
  intro u; rfl

/-- V(χ₁,χ₂) ≅ V(χ₂,χ₁): constructed via the intertwining operator
    T(f)(g) = ∑_u f(cosetRep(some u) · g). When χ₁ = χ₂ this is trivial;
    when χ₁ ≠ χ₂ both reps are simple so a nonzero equivariant map is an iso. -/
private lemma Etingof.GL2.principalSeries_iso_swap
    (chi1 chi2 : (GaloisField p n)ˣ →* ℂˣ) :
    Nonempty (Etingof.GL2.principalSeries p n chi1 chi2 ≅
      Etingof.GL2.principalSeries p n chi2 chi1) := by
  by_cases heq : chi1 = chi2
  · subst heq; exact ⟨Iso.refl _⟩
  · -- Both representations are simple
    have hSimple₁ := Etingof.GL2.principalSeries_simple_of_ne p n chi1 chi2 heq
    have hSimple₂ := Etingof.GL2.principalSeries_simple_of_ne p n chi2 chi1 (Ne.symm heq)
    -- Construct the intertwining operator T: V₁₂ → V₂₁
    -- T(f) has evaluation coordinates c(j) = ∑_u f(r_u * r_j)
    let evalMap₂ : ↥(Etingof.GL2.principalSeriesSubmodule p n chi2 chi1) →ₗ[ℂ]
        (Option (GaloisField p n) → ℂ) :=
      { toFun := fun f i => (f : GL2 p n → ℂ) (Etingof.GL2.cosetRep p n i)
        map_add' := fun _ _ => funext fun _ => rfl
        map_smul' := fun _ _ => funext fun _ => rfl }
    have hinj₂ : Function.Injective evalMap₂ := by
      intro f g hfg
      have h := Etingof.GL2.principalSeries_eval_injective p n chi2 chi1 (f - g)
        (fun i => by have := congr_fun hfg i; simp [evalMap₂] at this; simp [this])
      exact sub_eq_zero.mp h
    have hsurj₂ : Function.Surjective evalMap₂ := fun c =>
      ⟨⟨Etingof.GL2.mkCovariantFun p n chi2 chi1 c,
        Etingof.GL2.mkCovariantFun_mem p n chi2 chi1 c⟩,
       funext fun i => Etingof.GL2.mkCovariantFun_eval p n chi2 chi1 c i⟩
    set e₂ := LinearEquiv.ofBijective evalMap₂ ⟨hinj₂, hsurj₂⟩
    set T : ↥(Etingof.GL2.principalSeriesSubmodule p n chi1 chi2) →ₗ[ℂ]
        ↥(Etingof.GL2.principalSeriesSubmodule p n chi2 chi1) :=
      { toFun := fun f => e₂.symm (fun j => ∑ u : GaloisField p n,
          f.val (Etingof.GL2.cosetRep p n (some u) * Etingof.GL2.cosetRep p n j))
        map_add' := fun f₁ f₂ => by
          apply e₂.injective; simp [LinearEquiv.apply_symm_apply]
          ext j; simp [Finset.sum_add_distrib]
        map_smul' := fun c f => by
          apply e₂.injective; simp [LinearEquiv.apply_symm_apply]
          ext j; simp [Finset.mul_sum] }
    -- T is G-equivariant
    have hT_equiv : ∀ (h : GL2 p n)
        (f : ↥(Etingof.GL2.principalSeriesSubmodule p n chi1 chi2)),
        T (Etingof.GL2.principalSeriesRep p n chi1 chi2 h f) =
        Etingof.GL2.principalSeriesRep p n chi2 chi1 h (T f) := by
      intro h f
      apply e₂.injective
      have hLHS : e₂ (T (Etingof.GL2.principalSeriesRep p n chi1 chi2 h f)) =
          fun j => ∑ u : GaloisField p n,
            f.val (Etingof.GL2.cosetRep p n (some u) *
              Etingof.GL2.cosetRep p n j * h) := by
        change e₂ (e₂.symm (fun j => ∑ u : GaloisField p n,
          (Etingof.GL2.principalSeriesRep p n chi1 chi2 h f).val
            (Etingof.GL2.cosetRep p n (some u) * Etingof.GL2.cosetRep p n j))) = _
        rw [LinearEquiv.apply_symm_apply]; rfl
      have hRHS : e₂ (Etingof.GL2.principalSeriesRep p n chi2 chi1 h (T f)) =
          fun j => (T f).val (Etingof.GL2.cosetRep p n j * h) := by
        ext j; rfl
      rw [hLHS, hRHS]; ext j
      set b := Etingof.GL2.cosetBorel p n (Etingof.GL2.cosetRep p n j * h)
      set k := Etingof.GL2.cosetIndex p n (Etingof.GL2.cosetRep p n j * h)
      have hdecomp := Etingof.GL2.cosetBorel_mul_cosetRep p n
        (Etingof.GL2.cosetRep p n j * h)
      have hTf_cov : (T f).val (Etingof.GL2.cosetRep p n j * h) =
          Etingof.GL2.borelCharValue p n chi2 chi1 b *
            (T f).val (Etingof.GL2.cosetRep p n k) := by
        conv_lhs => rw [hdecomp]; exact (T f).prop b (Etingof.GL2.cosetRep p n k)
      have hTf_eval : (T f).val (Etingof.GL2.cosetRep p n k) =
          ∑ u, f.val (Etingof.GL2.cosetRep p n (some u) *
            Etingof.GL2.cosetRep p n k) := by
        exact congr_fun (e₂.apply_symm_apply (fun j => ∑ u : GaloisField p n,
          f.val (Etingof.GL2.cosetRep p n (some u) * Etingof.GL2.cosetRep p n j))) k
      rw [hTf_cov, hTf_eval]
      have hreassoc : ∀ u : GaloisField p n,
          f.val (Etingof.GL2.cosetRep p n (some u) *
            Etingof.GL2.cosetRep p n j * h) =
          f.val (Etingof.GL2.cosetRep p n (some u) *
            (b.val * Etingof.GL2.cosetRep p n k)) := by
        intro u; rw [mul_assoc, hdecomp]
      simp_rw [hreassoc]
      exact Etingof.GL2.intertwining_sum_covariant p n chi1 chi2 f b
        (Etingof.GL2.cosetRep p n k)
    -- T is nonzero
    have hT_ne : T ≠ 0 := by
      intro hT0
      obtain ⟨f₀, hf₀⟩ := hsurj₂ (Pi.single (some (0 : GaloisField p n)) 1)
      -- Build basis function for V₁₂ with eval coords = Pi.single (some 0) 1
      let evalMap₁ : ↥(Etingof.GL2.principalSeriesSubmodule p n chi1 chi2) →ₗ[ℂ]
          (Option (GaloisField p n) → ℂ) :=
        { toFun := fun f i => (f : GL2 p n → ℂ) (Etingof.GL2.cosetRep p n i)
          map_add' := fun _ _ => funext fun _ => rfl
          map_smul' := fun _ _ => funext fun _ => rfl }
      have hsurj₁ : Function.Surjective evalMap₁ := fun c =>
        ⟨⟨Etingof.GL2.mkCovariantFun p n chi1 chi2 c,
          Etingof.GL2.mkCovariantFun_mem p n chi1 chi2 c⟩,
         funext fun i => Etingof.GL2.mkCovariantFun_eval p n chi1 chi2 c i⟩
      obtain ⟨g₀, hg₀⟩ := hsurj₁ (Pi.single (some (0 : GaloisField p n)) 1)
      have hTg₀ : T g₀ = 0 := by rw [hT0]; simp
      have heval_none : (e₂ (T g₀)) none = ∑ u : GaloisField p n,
          g₀.val (Etingof.GL2.cosetRep p n (some u) *
            Etingof.GL2.cosetRep p n none) := by
        simp [T, LinearEquiv.apply_symm_apply]
      rw [hTg₀] at heval_none; simp at heval_none
      have : ∑ u : GaloisField p n,
          g₀.val (Etingof.GL2.cosetRep p n (some u) *
            Etingof.GL2.cosetRep p n none) =
        ∑ u : GaloisField p n,
          g₀.val (Etingof.GL2.cosetRep p n (some u)) := by
        congr 1; ext u; simp [Etingof.GL2.cosetRep]
      rw [this] at heval_none
      have hg₀_eval : ∀ u : GaloisField p n,
          g₀.val (Etingof.GL2.cosetRep p n (some u)) =
          if u = 0 then 1 else 0 := by
        intro u; have := congr_fun hg₀ (some u)
        simp [evalMap₁, Pi.single_apply] at this; exact this
      simp_rw [hg₀_eval] at heval_none; simp at heval_none
    -- Build T as a morphism in FDRep (Action category)
    let Thom : Etingof.GL2.principalSeries p n chi1 chi2 ⟶
        Etingof.GL2.principalSeries p n chi2 chi1 :=
      { hom := FGModuleCat.ofHom T
        comm := fun g => by
          ext f
          change T (Etingof.GL2.principalSeriesRep p n chi1 chi2 g f) =
            Etingof.GL2.principalSeriesRep p n chi2 chi1 g (T f)
          exact hT_equiv g f }
    -- T is nonzero as a morphism
    have hThom_ne : Thom ≠ 0 := by
      intro h
      apply hT_ne
      have : Thom.hom.hom.hom = (0 : _ →ₗ[ℂ] _) := by
        have h1 := congr_arg Action.Hom.hom h; rw [h1]; rfl
      exact this
    -- By Schur's lemma, nonzero map between simple objects is an iso
    haveI := isIso_of_hom_simple hThom_ne
    exact ⟨asIso Thom⟩

set_option maxHeartbeats 1600000 in
-- trace computation through evaluation linear equiv
/-- The character of V(χ₁,χ₂) on diagElt(c) for c ≠ 1 equals χ₁(c) + χ₂(c). -/
private lemma Etingof.GL2.principalSeries_char_diagElt
    (chi1 chi2 : (GaloisField p n)ˣ →* ℂˣ)
    (c : (GaloisField p n)ˣ) (hc : c ≠ 1) :
    FDRep.character (Etingof.GL2.principalSeries p n chi1 chi2)
      (Etingof.GL2.diagElt p n c) = (chi1 c : ℂ) + (chi2 c : ℂ) := by
  simp only [FDRep.character]
  -- Build the evaluation linear equiv
  let evalMap : ↥(Etingof.GL2.principalSeriesSubmodule p n chi1 chi2) →ₗ[ℂ]
      (Option (GaloisField p n) → ℂ) :=
    { toFun := fun f i => (f : GL2 p n → ℂ) (Etingof.GL2.cosetRep p n i)
      map_add' := fun _ _ => funext fun _ => rfl
      map_smul' := fun _ _ => funext fun _ => rfl }
  have hinj : Function.Injective evalMap := by
    intro f g hfg
    have h : f - g = 0 := Etingof.GL2.principalSeries_eval_injective p n chi1 chi2 (f - g)
      (fun i => by have := congr_fun hfg i; simp [evalMap] at this; simp [this])
    exact sub_eq_zero.mp h
  have hsurj : Function.Surjective evalMap := fun c =>
    ⟨⟨Etingof.GL2.mkCovariantFun p n chi1 chi2 c,
      Etingof.GL2.mkCovariantFun_mem p n chi1 chi2 c⟩,
     funext fun i => Etingof.GL2.mkCovariantFun_eval p n chi1 chi2 c i⟩
  set e := LinearEquiv.ofBijective evalMap ⟨hinj, hsurj⟩
  rw [show (LinearMap.trace ℂ _)
      ((Etingof.GL2.principalSeries p n chi1 chi2).ρ (Etingof.GL2.diagElt p n c)) =
    (LinearMap.trace ℂ _) (e.conj
      ((Etingof.GL2.principalSeries p n chi1 chi2).ρ (Etingof.GL2.diagElt p n c))) from
    (LinearMap.trace_conj' _ e).symm]
  have hcinv_ne_one : (↑c⁻¹ : GaloisField p n) ≠ 1 := by
    intro h; apply hc; exact inv_eq_one.mp (Units.val_eq_one.mp h)
  have hfixed : ∀ t : GaloisField p n, t * ↑c⁻¹ = t ↔ t = 0 := by
    intro t; constructor
    · intro h; by_contra ht; apply hcinv_ne_one
      exact mul_left_cancel₀ ht (by rw [mul_one]; exact h)
    · intro h; rw [h, zero_mul]
  -- The conjugated map acts as: g(none) ↦ χ₁(c)·g(none), g(some t) ↦ χ₂(c)·g(some(t*c⁻¹))
  -- Compute its trace via the matrix diagonal
  rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (Option (GaloisField p n)))]
  simp only [Matrix.trace, Matrix.diag]
  -- Compute diagonal entries
  have hentry : ∀ i : Option (GaloisField p n),
      (Pi.basisFun ℂ (Option (GaloisField p n))).repr
        (e.conj ((Etingof.GL2.principalSeries p n chi1 chi2).ρ
          (Etingof.GL2.diagElt p n c))
          ((Pi.basisFun ℂ (Option (GaloisField p n))) i)) i =
      match i with
      | none => (chi1 c : ℂ)
      | some t => if t = 0 then (chi2 c : ℂ) else 0 := by
    intro i
    simp only [Pi.basisFun_apply, Pi.basisFun_repr, LinearEquiv.conj_apply,
      LinearMap.comp_apply]
    -- e.conj(ρ(δ_c))(e_i) = e(ρ(δ_c)(e⁻¹(e_i)))
    -- e⁻¹(e_i) is the unique covariant function with value (Pi.single i 1) at coset reps
    -- ρ(δ_c) acts on it, then e evaluates at cosetRep(i)
    -- The result at index i gives the diagonal entry
    cases i with
    | none =>
      -- (e(ρ(δ_c)(e⁻¹(e_none))))(none)
      -- = (ρ(δ_c)(e⁻¹(e_none)))(cosetRep(none))
      -- = χ₁(c) · (e⁻¹(e_none))(cosetRep(none))
      -- = χ₁(c) · e_none(none) = χ₁(c) · 1 = χ₁(c)
      change (evalMap (Etingof.GL2.principalSeriesRep p n chi1 chi2
        (Etingof.GL2.diagElt p n c) (e.symm (Pi.single none 1)))) none = (chi1 c : ℂ)
      -- Unfold evalMap
      change (Etingof.GL2.principalSeriesRep p n chi1 chi2
        (Etingof.GL2.diagElt p n c) (e.symm (Pi.single none 1))).val
        (Etingof.GL2.cosetRep p n none) = (chi1 c : ℂ)
      rw [Etingof.GL2.action_diagonal_none]
      -- Goal: χ₁(c) * (e⁻¹(e_none))(cosetRep(none)) = χ₁(c)
      -- Suffices to show the eval = 1
      have h1 : (↑(e.symm (Pi.single none 1)) : GL2 p n → ℂ)
          (Etingof.GL2.cosetRep p n none) = 1 :=
        (congr_fun (e.apply_symm_apply (Pi.single none 1)) none).trans
          (Pi.single_eq_same _ _)
      rw [h1, mul_one]
    | some t =>
      change (evalMap (Etingof.GL2.principalSeriesRep p n chi1 chi2
        (Etingof.GL2.diagElt p n c) (e.symm (Pi.single (some t) 1)))) (some t) =
        if t = 0 then (chi2 c : ℂ) else 0
      change (Etingof.GL2.principalSeriesRep p n chi1 chi2
        (Etingof.GL2.diagElt p n c) (e.symm (Pi.single (some t) 1))).val
        (Etingof.GL2.cosetRep p n (some t)) = if t = 0 then (chi2 c : ℂ) else 0
      rw [Etingof.GL2.action_diagonal_some]
      -- Goal: χ₂(c) * (e⁻¹(δ_{some t}))(cosetRep(some(t*c⁻¹))) = if t = 0 then χ₂(c) else 0
      -- First isolate the eval part using congr 1 won't work since RHS isn't chi2*_
      -- Instead, prove the eval = Pi.single value, then rewrite
      have heval : (↑(e.symm (Pi.single (some t) 1)) : GL2 p n → ℂ)
          (Etingof.GL2.cosetRep p n (some (t * ↑c⁻¹))) =
          if t = 0 then 1 else 0 := by
        have h := congr_fun (e.apply_symm_apply (Pi.single (some t) 1)) (some (t * ↑c⁻¹))
        -- h : e(e.symm(δ_{some t}))(some(t*c⁻¹)) = δ_{some t}(some(t*c⁻¹))
        -- which is definitionally = (e.symm ...).val(cosetRep(some(t*c⁻¹)))
        rw [show e (e.symm (Pi.single (some t) 1)) (some (t * ↑c⁻¹)) =
            (↑(e.symm (Pi.single (some t) 1)) : GL2 p n → ℂ)
            (Etingof.GL2.cosetRep p n (some (t * ↑c⁻¹))) from rfl] at h
        rw [h]; simp only [Pi.single_apply, Option.some.injEq]
        simp only [hfixed]
      rw [heval]; split_ifs <;> simp
  simp_rw [LinearMap.toMatrix_apply, hentry]
  -- Sum over Option: none gives χ₁(c), some(0) gives χ₂(c), rest give 0
  rw [Fintype.sum_option]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- If χ₁ + χ₂ = χ₁' + χ₂' as functions on units, and χ₁ ≠ χ₂, χ₁' ≠ χ₂',
    then {χ₁, χ₂} = {χ₁', χ₂'} as sets. Uses character orthogonality. -/
private lemma Etingof.GL2.pair_eq_of_sum_eq
    (chi1 chi2 chi1' chi2' : (GaloisField p n)ˣ →* ℂˣ)
    (_hne : chi1 ≠ chi2) (hne' : chi1' ≠ chi2')
    (hsum : ∀ c : (GaloisField p n)ˣ, (chi1 c : ℂ) + (chi2 c : ℂ) =
      (chi1' c : ℂ) + (chi2' c : ℂ)) :
    ({chi1, chi2} : Set ((GaloisField p n)ˣ →* ℂˣ)) = {chi1', chi2'} := by
  -- Use orthogonality: ∑_c (χ/ψ)(c) = 0 if χ ≠ ψ, = |G| if χ = ψ
  -- Pair both sides of the sum with χ₁'⁻¹:
  -- ∑_c (χ₁(c) + χ₂(c)) · χ₁'(c)⁻¹ = ∑_c (χ₁'(c) + χ₂'(c)) · χ₁'(c)⁻¹
  -- LHS = ∑ (χ₁/χ₁')(c) + ∑ (χ₂/χ₁')(c) = δ(χ₁,χ₁')·|G| + δ(χ₂,χ₁')·|G|
  -- RHS = |G| + 0 = |G| (since χ₂' ≠ χ₁')
  -- So δ(χ₁,χ₁') + δ(χ₂,χ₁') = 1
  -- Either χ₁ = χ₁' (→ χ₂ = χ₂') or χ₂ = χ₁' (→ χ₁ = χ₂')
  by_cases h : chi1 = chi1'
  · -- χ₁ = χ₁': from sum equality, χ₂ = χ₂'
    have h2 : chi2 = chi2' := by
      ext c; have := hsum c; rw [show (chi1 c : ℂ) = (chi1' c : ℂ) from by rw [h]] at this
      exact_mod_cast add_left_cancel this
    rw [h, h2]
  · by_cases h2 : chi2 = chi1'
    · -- χ₂ = χ₁': from sum equality, χ₁ = χ₂'
      have h3 : chi1 = chi2' := by
        ext c; have hsm := hsum c
        rw [show (chi2 c : ℂ) = (chi1' c : ℂ) from by rw [h2]] at hsm
        rw [add_comm (chi1 c : ℂ) (chi1' c : ℂ)] at hsm
        exact_mod_cast (add_left_cancel hsm : (chi1 c : ℂ) = (chi2' c : ℂ))
      rw [Set.pair_eq_pair_iff]; right; exact ⟨h3, h2⟩
    · -- Neither: get contradiction from orthogonality
      exfalso
      -- ∑_c (χ₁·χ₁'⁻¹)(c) = 0 (since χ₁ ≠ χ₁')
      -- ∑_c (χ₂·χ₁'⁻¹)(c) = 0 (since χ₂ ≠ χ₁')
      -- But also: ∑_c (χ₁'·χ₁'⁻¹)(c) = |G| ≠ 0
      -- From sum: ∑_c ((χ₁+χ₂)·χ₁'⁻¹)(c) = ∑_c ((χ₁'+χ₂')·χ₁'⁻¹)(c)
      -- LHS = 0 + 0 = 0
      -- RHS = |G| + ∑_c (χ₂'·χ₁'⁻¹)(c) = |G| + 0 = |G| (since χ₂' ≠ χ₁')
      -- Contradiction: 0 = |G|
      have hcard_ne : (Fintype.card (GaloisField p n)ˣ : ℂ) ≠ 0 :=
        Nat.cast_ne_zero.mpr Fintype.card_ne_zero
      -- ∑_c χ₁(c)·χ₁'(c)⁻¹
      set μ₁ : (GaloisField p n)ˣ →* ℂˣ := chi1 * chi1'⁻¹
      set μ₂ : (GaloisField p n)ˣ →* ℂˣ := chi2 * chi1'⁻¹
      set μ₂' : (GaloisField p n)ˣ →* ℂˣ := chi2' * chi1'⁻¹
      have hμ₁_ne : μ₁ ≠ 1 := by
        intro heq; apply h
        have : ∀ c, μ₁ c = 1 := fun c => by
          have := congr_arg (· c) heq; simpa using this
        ext c; have := mul_inv_eq_one.mp (this c)
        exact congr_arg Units.val this
      have hμ₂_ne : μ₂ ≠ 1 := by
        intro heq; apply h2
        have : ∀ c, μ₂ c = 1 := fun c => by
          have := congr_arg (· c) heq; simpa using this
        ext c; have := mul_inv_eq_one.mp (this c)
        exact congr_arg Units.val this
      have hμ₂'_ne : μ₂' ≠ 1 := by
        intro heq; apply hne'
        have : ∀ c, μ₂' c = 1 := fun c => by
          have := congr_arg (· c) heq; simpa using this
        ext c; have := (mul_inv_eq_one.mp (this c)).symm
        exact congr_arg Units.val this
      -- Sum both sides of hsum times χ₁'⁻¹
      have lhs_eq : ∑ c : (GaloisField p n)ˣ,
          ((chi1 c : ℂ) + (chi2 c : ℂ)) * ((chi1' c)⁻¹ : ℂˣ) =
        ∑ c, ((chi1' c : ℂ) + (chi2' c : ℂ)) * ((chi1' c)⁻¹ : ℂˣ) := by
        congr 1; ext c; rw [hsum c]
      -- Key: ∑ (χ·ψ⁻¹)(c) relates to ∑ μ(c) for μ = χ·ψ⁻¹
      have hval_eq : ∀ (χ ψ : (GaloisField p n)ˣ →* ℂˣ) (c : (GaloisField p n)ˣ),
          (χ c : ℂ) * (↑(ψ c)⁻¹ : ℂ) = ((χ * ψ⁻¹) c : ℂ) := by
        intro χ ψ c; simp [MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul]
      -- LHS = ∑ μ₁(c) + ∑ μ₂(c) = 0 + 0 = 0
      have hlhs : ∑ c : (GaloisField p n)ˣ,
          ((chi1 c : ℂ) + (chi2 c : ℂ)) * (↑(chi1' c)⁻¹ : ℂ) = 0 := by
        simp_rw [add_mul, hval_eq]
        rw [Finset.sum_add_distrib,
            Etingof.GL2.sum_nontrivial_char_eq_zero μ₁ hμ₁_ne,
            Etingof.GL2.sum_nontrivial_char_eq_zero μ₂ hμ₂_ne, add_zero]
      -- RHS = |G| + ∑ μ₂'(c) = |G| + 0 = |G|
      have hrhs : ∑ c : (GaloisField p n)ˣ,
          ((chi1' c : ℂ) + (chi2' c : ℂ)) * (↑(chi1' c)⁻¹ : ℂ) =
          (Fintype.card (GaloisField p n)ˣ : ℂ) := by
        simp_rw [add_mul, hval_eq]
        rw [Finset.sum_add_distrib]
        have h1 : ∑ c : (GaloisField p n)ˣ, ((chi1' * chi1'⁻¹) c : ℂ) =
            Fintype.card (GaloisField p n)ˣ := by
          simp [mul_inv_cancel, Finset.card_univ]
        rw [h1, Etingof.GL2.sum_nontrivial_char_eq_zero μ₂' hμ₂'_ne, add_zero]
      -- Contradiction: 0 = |G|
      have lhs_eq : ∑ c : (GaloisField p n)ˣ,
          ((chi1 c : ℂ) + (chi2 c : ℂ)) * (↑(chi1' c)⁻¹ : ℂ) =
        ∑ c, ((chi1' c : ℂ) + (chi2' c : ℂ)) * (↑(chi1' c)⁻¹ : ℂ) :=
        Finset.sum_congr rfl (fun c _ => by rw [hsum c])
      exact hcard_ne (hrhs.symm.trans (lhs_eq.symm.trans hlhs))

/-- **Theorem 5.25.2 (3b)**: V(χ₁, χ₂) ≅ V(χ'₁, χ'₂) if and only if
{χ₁, χ₂} = {χ'₁, χ'₂} (as sets). (Etingof Theorem 5.25.2) -/
theorem Etingof.Theorem5_25_2_part3b [NeZero n]
    (chi1 chi2 chi1' chi2' : (GaloisField p n)ˣ →* ℂˣ)
    (hne : chi1 ≠ chi2) (hne' : chi1' ≠ chi2') :
    Nonempty (Etingof.GL2.principalSeries p n chi1 chi2 ≅
      Etingof.GL2.principalSeries p n chi1' chi2') ↔
    ({chi1, chi2} : Set ((GaloisField p n)ˣ →* ℂˣ)) = {chi1', chi2'} := by
  constructor
  · -- Forward: iso → equal characters → sum equality → set equality
    rintro ⟨iso⟩
    have hchar := FDRep.char_iso iso
    have hsum : ∀ c : (GaloisField p n)ˣ, c ≠ 1 →
        (chi1 c : ℂ) + (chi2 c : ℂ) = (chi1' c : ℂ) + (chi2' c : ℂ) := by
      intro c hc
      have h1 := Etingof.GL2.principalSeries_char_diagElt p n chi1 chi2 c hc
      have h2 := Etingof.GL2.principalSeries_char_diagElt p n chi1' chi2' c hc
      rw [← h1, ← h2, congr_fun hchar]
    -- Extend to c = 1: both sides equal 2
    have hsum_all : ∀ c : (GaloisField p n)ˣ,
        (chi1 c : ℂ) + (chi2 c : ℂ) = (chi1' c : ℂ) + (chi2' c : ℂ) := by
      intro c
      by_cases hc : c = 1
      · subst hc; simp
      · exact hsum c hc
    exact Etingof.GL2.pair_eq_of_sum_eq p n chi1 chi2 chi1' chi2' hne hne' hsum_all
  · -- Backward: set equality → iso
    intro heq
    rw [Set.pair_eq_pair_iff] at heq
    rcases heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
      exact ⟨Iso.refl _⟩
    · rw [h1, h2]
      exact Etingof.GL2.principalSeries_iso_swap p n chi2' chi1'

end
