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

section Theorem5_25_2

variable (p : ℕ) [hp : Fact (Nat.Prime p)] (n : ℕ) (hn : 0 < n)

/-- Helper: inner product ⟨χ_{V(χ₁,χ₂)}, χ_{V(χ₁,χ₂)}⟩ = 1 when χ₁ ≠ χ₂.
Uses the Frobenius trace formula evaluated on each conjugacy class of GL₂(𝔽_q)
and the vanishing of ∑_{z ∈ 𝔽_q×} (χ₁/χ₂)(z) for χ₁ ≠ χ₂.

Proof strategy (from Etingof Theorem 5.25.2):
1. Apply `FDRep.simple_iff_char_is_norm_one`: reduces to
   ∑_g χ_V(g) · χ_V(g⁻¹) = |G|
2. The induced character formula gives χ_V on each conjugacy class type:
   - Scalar xI: (q+1)χ₁(x)χ₂(x)
   - Parabolic: χ₁(x)χ₂(x)
   - Split semisimple diag(x,y): χ₁(x)χ₂(y) + χ₁(y)χ₂(x)
   - Elliptic: 0
3. Use `GL2.sum_split` to decompose and `sum_monoidHom_units_eq_zero`
   for ∑ (χ₁/χ₂)(z) = 0.
4. Arithmetic: (q-1)(q+1)² + (q-1)(q²-1) + q(q+1)(q-1)(q-3) = q(q+1)(q-1)² = |G|.
-/
private lemma Etingof.GL2.principalSeries_simple_of_ne
    (chi1 chi2 : (GaloisField p n)ˣ →* ℂˣ) (hne : chi1 ≠ chi2) :
    Simple (Etingof.GL2.principalSeries p n chi1 chi2) := by
  -- The proof reduces to showing ∑_g χ(g)·χ(g⁻¹) = |G| via simple_iff_char_is_norm_one.
  -- This requires:
  -- (a) The induced character formula (trace of right translation on covariant functions)
  -- (b) Conjugacy class decomposition via GL2.sum_split
  -- (c) Character orthogonality: ∑ (χ₁/χ₂)(z) = 0 (proved in sum_monoidHom_units_eq_zero)
  sorry

/-- **Theorem 5.25.2 (1)**: If χ₁ ≠ χ₂, the principal series representation
V(χ₁, χ₂) is irreducible. (Etingof Theorem 5.25.2) -/
theorem Etingof.Theorem5_25_2_part1
    (chi1 chi2 : (GaloisField p n)ˣ →* ℂˣ) (hne : chi1 ≠ chi2) :
    Simple (Etingof.GL2.principalSeries p n chi1 chi2) :=
  Etingof.GL2.principalSeries_simple_of_ne p n chi1 chi2 hne

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

/-- V(μ,μ) decomposes as ℂ_μ ⊕ W_μ in FDRep. -/
private lemma Etingof.GL2.principalSeries_decomp
    (mu : (GaloisField p n)ˣ →* ℂˣ) :
    Nonempty (Etingof.GL2.principalSeries p n mu mu ≅
      Etingof.GL2.detChar p n mu ⊞ Etingof.GL2.complementW p n mu) := by
  -- Step 1: ℂ_μ is simple and the embedding is nonzero → mono → split mono (Maschke)
  haveI : Simple (Etingof.GL2.detChar p n mu) := Etingof.GL2.detChar_simple p n mu
  have hne := Etingof.GL2.detCharEmbedding_ne_zero p n mu
  set emb := Etingof.GL2.detCharEmbedding p n mu
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
  -- Step 3: Show cokernel(emb) ≅ W_μ
  -- Both have the same character (= χ_V - χ_{ℂ_μ})
  -- For now, we use character comparison via Corollary 4.2.4
  sorry

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
