import Mathlib

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

open CategoryTheory Classical

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

section Theorem5_25_2

variable (p : ℕ) [hp : Fact (Nat.Prime p)] (n : ℕ) (hn : 0 < n)

/-- Helper: inner product ⟨χ_{V(χ₁,χ₂)}, χ_{V(χ₁,χ₂)}⟩ = 1 when χ₁ ≠ χ₂.
Uses the Frobenius trace formula evaluated on each conjugacy class of GL₂(𝔽_q)
and the vanishing of ∑_{z ∈ 𝔽_q×} (χ₁/χ₂)(z) for χ₁ ≠ χ₂. -/
private lemma Etingof.GL2.principalSeries_simple_of_ne
    (chi1 chi2 : (GaloisField p n)ˣ →* ℂˣ) (hne : chi1 ≠ chi2) :
    Simple (Etingof.GL2.principalSeries p n chi1 chi2) := by
  sorry

/-- **Theorem 5.25.2 (1)**: If χ₁ ≠ χ₂, the principal series representation
V(χ₁, χ₂) is irreducible. (Etingof Theorem 5.25.2) -/
theorem Etingof.Theorem5_25_2_part1
    (chi1 chi2 : (GaloisField p n)ˣ →* ℂˣ) (hne : chi1 ≠ chi2) :
    Simple (Etingof.GL2.principalSeries p n chi1 chi2) :=
  Etingof.GL2.principalSeries_simple_of_ne p n chi1 chi2 hne

/-- Helper: V(μ,μ) decomposes as ℂ_μ ⊕ W_μ in FDRep.
The augmentation functional provides the ℂ_μ summand, and W_μ = ker(augmentation)
is the complement. -/
private lemma Etingof.GL2.principalSeries_decomp
    (mu : (GaloisField p n)ˣ →* ℂˣ) :
    Nonempty (Etingof.GL2.principalSeries p n mu mu ≅
      Etingof.GL2.detChar p n mu ⊞ Etingof.GL2.complementW p n mu) := by
  sorry

/-- Helper: W_μ is irreducible. Uses ⟨χ_{V(μ,μ)}, χ_{V(μ,μ)}⟩ = 2 and the
fact that ℂ_μ is a 1-dimensional constituent, so W_μ must be the other
irreducible summand. -/
private lemma Etingof.GL2.complementW_simple
    (mu : (GaloisField p n)ˣ →* ℂˣ) :
    Simple (Etingof.GL2.complementW p n mu) := by
  sorry

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
  sorry

/-- For any values on coset representatives, there exists a covariant function realizing them. -/
private lemma Etingof.GL2.principalSeries_eval_surjective
    (chi1 chi2 : (GaloisField p n)ˣ →* ℂˣ)
    (c : Option (GaloisField p n) → ℂ) :
    ∃ f : ↥(Etingof.GL2.principalSeriesSubmodule p n chi1 chi2),
      ∀ i, (f : GL2 p n → ℂ) (Etingof.GL2.cosetRep p n i) = c i := by
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
  sorry

/-- Augmentation of μ∘det equals |G|, hence is nonzero. -/
private lemma Etingof.GL2.augmentation_detFun_ne_zero
    (mu : (GaloisField p n)ˣ →* ℂˣ) :
    Etingof.GL2.augmentation p n mu
      (fun g : GL2 p n => (mu (Matrix.GeneralLinearGroup.det g) : ℂ)) ≠ 0 := by
  sorry

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
  sorry

/-- The augmentation restricted to principal series is surjective (onto ℂ). -/
private lemma Etingof.GL2.augOnPrincipalSeries_surjective
    (mu : (GaloisField p n)ˣ →* ℂˣ) :
    Function.Surjective (Etingof.GL2.augOnPrincipalSeries p n mu) := by
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
