import Mathlib
import EtingofRepresentationTheory.Chapter5.GL2ConjugacyClasses

/-!
# Lemma 5.25.3: Complementary Series Character Properties

For the virtual representation χ defined in the construction of
complementary series representations of GL₂(𝔽_q):
- ⟨χ, χ⟩ = 1
- χ(1) = q - 1 > 0

These properties establish that χ is the character of an actual
irreducible representation (of dimension q - 1).

The virtual character is defined as:
  χ = char(W₁ ⊗ V_{α,1}) - char(V_{α,1}) - char(Ind_K^G ℂ_ν)
where K ⊂ GL₂(𝔽_q) is the cyclic subgroup of multiplications by
elements of 𝔽_{q²}×, ν : K → ℂ× satisfies ν^q ≠ ν, and α = ν|_{𝔽_q×}.

## Mathlib correspondence

Uses `GaloisField` and character inner product theory.
-/

variable (p : ℕ) [hp : Fact (Nat.Prime p)] (n : ℕ)

private abbrev GL2 := Matrix.GeneralLinearGroup (Fin 2) (GaloisField p n)

section FieldExtInfrastructure

open Polynomial

/-- X^(p^n) - X divides X^(p^(2n)) - X in characteristic p.
Proof: (X^(p^n) - X)^(p^n) = X^(p^(2n)) - X^(p^n) by Freshman's dream,
so X^(p^(2n)) - X = (X^(p^n) - X)^(p^n) + (X^(p^n) - X). -/
lemma Etingof.dvd_X_pow_sub_X :
    (X ^ p ^ n - X : (ZMod p)[X]) ∣ (X ^ p ^ (2 * n) - X : (ZMod p)[X]) := by
  set f := (X ^ p ^ n - X : (ZMod p)[X])
  have key : f ^ p ^ n = X ^ p ^ (2 * n) - X ^ p ^ n := by
    change (X ^ p ^ n - X) ^ p ^ n = X ^ p ^ (2 * n) - X ^ p ^ n
    rw [sub_pow_char_pow (p := p)]
    congr 1
    rw [← pow_mul, ← Nat.pow_add]
    ring_nf
  have decomp : X ^ p ^ (2 * n) - X = f ^ p ^ n + f := by
    rw [key]; ring
  rw [decomp]
  exact dvd_add (dvd_pow_self f (pow_ne_zero n hp.out.pos.ne')) dvd_rfl

/-- X^(p^n) - X splits in GaloisField p (2*n) because it divides X^(p^(2n)) - X
which splits there. -/
lemma Etingof.splits_X_pow_sub_X :
    Splits (map (algebraMap (ZMod p) (GaloisField p (2 * n))) (X ^ p ^ n - X)) := by
  by_cases hn : n = 0
  · subst hn
    simp only [Nat.mul_zero, pow_zero, pow_one, sub_self, Polynomial.map_zero]
    exact Polynomial.Splits.zero
  · haveI : Fintype (GaloisField p (2 * n)) := Fintype.ofFinite _
    have hsplits : Splits (map (algebraMap (ZMod p) (GaloisField p (2 * n)))
        (X ^ p ^ (2 * n) - X)) := by
      have hcard : Nat.card (GaloisField p (2 * n)) = p ^ (2 * n) :=
        GaloisField.card p (2 * n) (Nat.mul_ne_zero two_ne_zero hn)
      rw [show p ^ (2 * n) = Fintype.card (GaloisField p (2 * n)) from by
        rw [Nat.card_eq_fintype_card] at hcard; omega]
      exact @FiniteField.splits_X_pow_card_sub_X p hp _ _ _ _
    have hne : (X ^ p ^ (2 * n) - X : (ZMod p)[X]) ≠ 0 :=
      FiniteField.X_pow_card_pow_sub_X_ne_zero (ZMod p)
        (Nat.mul_ne_zero two_ne_zero hn) hp.out.one_lt
    exact hsplits.of_dvd (map_ne_zero hne) (map_dvd _ (Etingof.dvd_X_pow_sub_X p n))

/-- The algebra homomorphism GaloisField p n →ₐ[ZMod p] GaloisField p (2*n)
obtained from IsSplittingField.lift. -/
noncomputable def Etingof.galoisFieldAlgHom :
    GaloisField p n →ₐ[ZMod p] GaloisField p (2 * n) :=
  IsSplittingField.lift (GaloisField p n) (X ^ p ^ n - X)
    (Etingof.splits_X_pow_sub_X p n)

/-- Algebra instance for GaloisField p (2*n) over GaloisField p n. -/
noncomputable instance Etingof.algebraGaloisFieldExt :
    Algebra (GaloisField p n) (GaloisField p (2 * n)) :=
  (Etingof.galoisFieldAlgHom p n).toRingHom.toAlgebra

/-- The scalar tower ZMod p → GaloisField p n → GaloisField p (2*n). -/
noncomputable instance Etingof.scalarTowerGaloisField :
    IsScalarTower (ZMod p) (GaloisField p n) (GaloisField p (2 * n)) :=
  IsScalarTower.of_algebraMap_eq fun r => by
    change (algebraMap (ZMod p) (GaloisField p (2 * n))) r =
      (Etingof.galoisFieldAlgHom p n).toRingHom
        ((algebraMap (ZMod p) (GaloisField p n)) r)
    exact ((Etingof.galoisFieldAlgHom p n).commutes r).symm

/-- GaloisField p (2*n) is finite-dimensional over GaloisField p n. -/
noncomputable instance Etingof.finiteDimensionalGaloisFieldExt :
    FiniteDimensional (GaloisField p n) (GaloisField p (2 * n)) := by
  haveI : FiniteDimensional (ZMod p) (GaloisField p (2 * n)) := inferInstance
  exact FiniteDimensional.right (ZMod p) (GaloisField p n) (GaloisField p (2 * n))

/-- The degree of GaloisField p (2*n) over GaloisField p n is 2 (when n > 0). -/
lemma Etingof.finrank_galoisField_ext (hn : n ≠ 0) :
    Module.finrank (GaloisField p n) (GaloisField p (2 * n)) = 2 := by
  have h1 := GaloisField.finrank p (show n ≠ 0 from hn)
  have h2 := GaloisField.finrank p (show 2 * n ≠ 0 from Nat.mul_ne_zero two_ne_zero hn)
  have htower := Module.finrank_mul_finrank (ZMod p) (GaloisField p n)
    (GaloisField p (2 * n))
  rw [h1, h2] at htower
  -- htower : n * finrank = 2 * n
  have hpos : 0 < n := Nat.pos_of_ne_zero hn
  nlinarith

end FieldExtInfrastructure

/-- The embedding of 𝔽_{q²}× into GL₂(𝔽_q) via the left regular representation
on a chosen basis of the degree-2 field extension 𝔽_{q²}/𝔽_q. -/
noncomputable def Etingof.GL2.fieldExtEmbed :
    (GaloisField p (2 * n))ˣ →* GL2 p n := by
  by_cases hn : n = 0
  · -- Degenerate case: n = 0, both fields have 1 element
    exact 1
  · -- Main case: use left multiplication matrix representation
    letI := Etingof.algebraGaloisFieldExt p n
    letI := Etingof.scalarTowerGaloisField p n
    haveI := Etingof.finiteDimensionalGaloisFieldExt p n
    -- Construct Fin 2-indexed basis via finrank = 2
    let b := Module.finBasisOfFinrankEq (R := GaloisField p n)
      (M := GaloisField p (2 * n)) (Etingof.finrank_galoisField_ext p n hn)
    let matRepr := Algebra.leftMulMatrix b
    -- matRepr is an algebra hom: lift to units
    exact
      { toFun := fun u =>
          ⟨matRepr u, matRepr ↑u⁻¹, by
            rw [← map_mul, Units.mul_inv, map_one],
           by rw [← map_mul, Units.inv_mul, map_one]⟩
        map_one' := Units.ext (map_one matRepr)
        map_mul' := fun a b => Units.ext (by simp [map_mul]) }

/-- The cyclic subgroup K ⊂ GL₂(𝔽_q) corresponding to multiplication by
elements of 𝔽_{q²}× (embedded via the basis {1, √ε}). -/
noncomputable def Etingof.GL2.ellipticSubgroup : Subgroup (GL2 p n) :=
  (Etingof.GL2.fieldExtEmbed p n).range

/-- Embedding of scalar matrices 𝔽_q× ↪ K via a ↦ embed(algebraMap a). -/
noncomputable def Etingof.GL2.scalarToElliptic :
    (GaloisField p n)ˣ →* ↥(Etingof.GL2.ellipticSubgroup p n) := by
  by_cases hn : n = 0
  · exact 1
  · letI := Etingof.algebraGaloisFieldExt p n
    -- Map a : (GaloisField p n)ˣ to algebraMap a : (GaloisField p (2*n))ˣ
    -- then apply fieldExtEmbed
    refine (Etingof.GL2.fieldExtEmbed p n).codRestrict
      (Etingof.GL2.ellipticSubgroup p n) ?_ |>.comp ?_
    · intro x; exact ⟨x, rfl⟩
    · -- Units.map of algebraMap
      exact Units.map (algebraMap (GaloisField p n) (GaloisField p (2 * n))).toMonoidHom

/-- Character of W₁, the q-dimensional irreducible complement in V(1,1).
W₁ is the complement of the trivial representation in the permutation representation
on P¹(𝔽_q). Its character equals (number of fixed points on P¹) - 1.

A point [1:t] ∈ P¹ is fixed by matrix M iff M₀₁t² + (M₀₀ - M₁₁)t - M₁₀ = 0.
The point [0:1] is fixed iff M₀₁ = 0. -/
noncomputable def Etingof.GL2.charW₁
    [Fintype (GaloisField p n)] [DecidableEq (GaloisField p n)] : GL2 p n → ℂ :=
  fun g =>
    let M := (g : Matrix (Fin 2) (Fin 2) (GaloisField p n))
    -- Count fixed points on the affine chart [1:t]
    let fixedAffine := Finset.univ.filter fun (t : GaloisField p n) =>
      M 0 1 * t ^ 2 + (M 0 0 - M 1 1) * t - M 1 0 = 0
    -- Check if the point at infinity [0:1] is fixed
    let fixedInfty : ℕ := if M 0 1 = 0 then 1 else 0
    ((fixedAffine.card + fixedInfty : ℕ) : ℂ) - 1

/-- Character of the principal series representation V(α, 1) of GL₂(𝔽_q).
V(α, 1) = Ind_B^G(α ⊗ 1) where B is the Borel subgroup (upper triangular matrices).
By Frobenius reciprocity, char(V(α,1))(g) = (1/|B|) ∑_{x : x⁻¹gx ∈ B} α(upper-left of x⁻¹gx). -/
noncomputable def Etingof.GL2.charVα₁
    [Fintype (GaloisField p n)] [DecidableEq (GaloisField p n)]
    [Fintype (GL2 p n)]
    (alpha : (GaloisField p n)ˣ →* ℂˣ) : GL2 p n → ℂ :=
  fun g =>
    -- Frobenius character formula for induced representation
    -- sum over x ∈ G of (indicator that x⁻¹gx is upper triangular) * α(upper-left entry)
    let borelCard : ℂ := ((Fintype.card (GaloisField p n) - 1) ^ 2 *
      Fintype.card (GaloisField p n) : ℕ)
    borelCard⁻¹ * ∑ x : GL2 p n,
      let conj := (x⁻¹ * g * x : GL2 p n)
      let M := (conj : Matrix (Fin 2) (Fin 2) (GaloisField p n))
      if M 1 0 = 0 then
        -- x⁻¹gx is upper triangular; extract upper-left entry as a unit
        if h : M 0 0 ≠ 0 then
          (alpha (Units.mk0 (M 0 0) h) : ℂ)
        else 0
      else 0

open Classical in
/-- The complementary series virtual character of GL₂(𝔽_q), defined as
char(W₁ ⊗ V_{α,1}) - char(V_{α,1}) - char(Ind_K^G ℂ_ν)
where ν : K → ℂ× with ν^q ≠ ν and α = ν|_{scalars}. -/
noncomputable def Etingof.GL2.complementarySeriesChar
    [Fintype (GaloisField p n)] [DecidableEq (GaloisField p n)]
    [Fintype (GL2 p n)]
    (nu : (Etingof.GL2.ellipticSubgroup p n) →* ℂˣ) :
    GL2 p n → ℂ :=
  let K := Etingof.GL2.ellipticSubgroup p n
  let alpha : (GaloisField p n)ˣ →* ℂˣ := nu.comp (Etingof.GL2.scalarToElliptic p n)
  fun g =>
    -- char(W₁ ⊗ V_{α,1})(g) = char(W₁)(g) · char(V_{α,1})(g)
    Etingof.GL2.charW₁ p n g * Etingof.GL2.charVα₁ p n alpha g
    -- minus char(V_{α,1})(g)
    - Etingof.GL2.charVα₁ p n alpha g
    -- minus char(Ind_K^G ℂ_ν)(g) via Frobenius character formula
    - (Fintype.card ↥K : ℂ)⁻¹ *
        ∑ x : GL2 p n,
          if h : x⁻¹ * g * x ∈ K
          then (nu ⟨x⁻¹ * g * x, h⟩).val
          else 0

/-! ### Character value lemmas on each conjugacy class type

From Discussion 5.25.4, the complementary series virtual character
χ = char(W₁ ⊗ V_{α,1}) - char(V_{α,1}) - char(Ind_K^G ℂ_ν)
has the following values:
- Scalar xI: χ(xI) = (q-1)α(x)
- Parabolic [[x,1],[0,x]]: χ = -α(x)
- Hyperbolic diag(x,y), x≠y: χ = 0
- Elliptic ζ ∈ K\F_q×: χ = -(ν(ζ) + ν^q(ζ))
-/

section CharacterValues

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-- Scalar matrices commute with everything: x⁻¹ · (aI) · x = aI. -/
lemma Etingof.scalar_conj_eq_self
    (g : GL2 p n) (hg : GL2.IsScalar (p := p) (n := n) g) (x : GL2 p n) :
    x⁻¹ * g * x = g := by
  obtain ⟨h01, h10, h00_eq_11⟩ := hg
  have hg_scalar : g.val = (g.val 0 0) • (1 : Matrix (Fin 2) (Fin 2) (GaloisField p n)) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [*, Matrix.one_apply]
  have hcomm : g * x = x * g := by
    apply Units.ext
    simp only [Units.val_mul]
    rw [hg_scalar, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.one_mul]
  rw [mul_assoc, hcomm, ← mul_assoc, inv_mul_cancel, one_mul]

/-- For a unit character ν : G →* ℂˣ of a finite group, |ν(g)|² = 1. -/
lemma Etingof.units_char_normSq {G : Type*} [Group G] [Fintype G]
    (ν : G →* ℂˣ) (g : G) :
    (ν g : ℂ) * starRingEnd ℂ (ν g : ℂ) = 1 := by
  rw [Complex.mul_conj]
  -- ν(g) is a root of unity, so its norm is 1
  have hpow : (ν g : ℂ) ^ orderOf g = 1 := by
    have h : (ν g : ℂˣ) ^ orderOf g = 1 := by
      rw [← map_pow, pow_orderOf_eq_one, map_one]
    have : ((ν g : ℂˣ) : ℂ) ^ orderOf g = ((1 : ℂˣ) : ℂ) := congr_arg Units.val h
    simpa using this
  have hne : orderOf g ≠ 0 := Nat.pos_iff_ne_zero.mp (orderOf_pos g)
  have habs : ‖(ν g : ℂ)‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hpow hne
  rw [Complex.normSq_eq_norm_sq, habs, one_pow]; norm_cast

/-- charW₁ on a scalar matrix aI equals q (all q+1 points of P¹ are fixed, minus 1). -/
lemma Etingof.charW₁_scalar
    [Fintype (GaloisField p n)] [DecidableEq (GaloisField p n)]
    (g : GL2 p n) (hg : GL2.IsScalar (p := p) (n := n) g) :
    Etingof.GL2.charW₁ p n g = (Fintype.card (GaloisField p n) : ℂ) := by
  obtain ⟨h01, h10, h00_eq_11⟩ := hg
  simp only [GL2.charW₁]
  set M := (g : Matrix (Fin 2) (Fin 2) (GaloisField p n))
  have hM01 : M 0 1 = 0 := h01
  have hM10 : M 1 0 = 0 := h10
  have hM00_eq_11 : M 0 0 = M 1 1 := h00_eq_11
  have hfilt : (Finset.univ.filter fun t : GaloisField p n =>
      M 0 1 * t ^ 2 + (M 0 0 - M 1 1) * t - M 1 0 = 0) = Finset.univ := by
    ext t; simp [hM01, hM10, hM00_eq_11]
  rw [hfilt, Finset.card_univ, hM01, if_pos rfl]
  push_cast
  ring

/-- For scalar g = aI, the diagonal entry g.val 0 0 is nonzero (since g ∈ GL₂). -/
lemma Etingof.scalar_diag_ne_zero
    (g : GL2 p n) (hg : GL2.IsScalar (p := p) (n := n) g) :
    g.val 0 0 ≠ 0 := by
  obtain ⟨h01, h10, h00_eq_11⟩ := hg
  intro h
  have hdet : Matrix.det g.val = 0 := by
    simp [Matrix.det_fin_two, h01, h10, h]
  have hunit := g.isUnit
  rw [Matrix.isUnit_iff_isUnit_det] at hunit
  exact hunit.ne_zero hdet

/-- For scalar g, charVα₁(g) = borelCard⁻¹ * |G| * α(a) where a = g.val 0 0. -/
lemma Etingof.charVα₁_scalar
    [Fintype (GaloisField p n)] [DecidableEq (GaloisField p n)]
    [Fintype (GL2 p n)]
    (alpha : (GaloisField p n)ˣ →* ℂˣ)
    (g : GL2 p n) (hg : GL2.IsScalar (p := p) (n := n) g)
    (h_ne : g.val 0 0 ≠ 0) :
    Etingof.GL2.charVα₁ p n alpha g =
    (((Fintype.card (GaloisField p n) - 1) ^ 2 *
      Fintype.card (GaloisField p n) : ℕ) : ℂ)⁻¹ *
    (Fintype.card (GL2 p n) : ℂ) *
    (alpha (Units.mk0 (g.val 0 0) h_ne) : ℂ) := by
  unfold GL2.charVα₁
  simp only [Etingof.scalar_conj_eq_self p n g hg]
  obtain ⟨h01, h10, _⟩ := hg
  -- h10 : GL2.mat g 1 0 = 0, which is g.val 1 0 = 0
  have h10' : g.val 1 0 = 0 := h10
  set a_unit : (GaloisField p n)ˣ := Units.mk0 (g.val 0 0) h_ne with ha_unit
  -- Every term in the sum is the same
  conv in (Finset.univ.sum _) =>
    arg 2; ext x
    rw [if_pos h10', dif_pos h_ne]
    change (alpha a_unit : ℂ)
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

/-- A scalar matrix aI equals fieldExtEmbed(algebraMap a). -/
lemma Etingof.scalar_eq_fieldExtEmbed
    (hn : n ≠ 0)
    (g : GL2 p n) (hg : GL2.IsScalar (p := p) (n := n) g)
    (h_ne : g.val 0 0 ≠ 0) :
    g = Etingof.GL2.fieldExtEmbed p n
      (Units.map (algebraMap (GaloisField p n) (GaloisField p (2 * n))).toMonoidHom
        (Units.mk0 (g.val 0 0) h_ne)) := by
  letI := Etingof.algebraGaloisFieldExt p n
  obtain ⟨h01, h10, h00_eq_11⟩ := hg
  set b := Module.finBasisOfFinrankEq (R := GaloisField p n)
    (M := GaloisField p (2 * n)) (Etingof.finrank_galoisField_ext p n hn)
  set u := Units.map (algebraMap (GaloisField p n) (GaloisField p (2 * n))).toMonoidHom
      (Units.mk0 (g.val 0 0) h_ne)
  -- The .val of fieldExtEmbed u is leftMulMatrix b u
  have hval : (GL2.fieldExtEmbed p n u).val =
      Algebra.leftMulMatrix b (u : GaloisField p (2 * n)) := by
    unfold GL2.fieldExtEmbed; simp only [dif_neg hn]; rfl
  -- g.val = leftMulMatrix b (algebraMap (g.val 0 0))
  suffices h : g.val = (GL2.fieldExtEmbed p n u).val from Units.ext h
  rw [hval]
  ext i j
  rw [Algebra.leftMulMatrix_eq_repr_mul]
  show g.val i j = (b.repr ((algebraMap (GaloisField p n) (GaloisField p (2 * n)))
    (g.val 0 0) * b j)) i
  rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
    map_smul, Finsupp.smul_apply, smul_eq_mul, b.repr_self,
    Finsupp.single_apply]
  fin_cases i <;> fin_cases j <;> simp [h01, h10, h00_eq_11]

/-- Scalar matrices are in the elliptic subgroup K. -/
lemma Etingof.scalar_mem_ellipticSubgroup
    (hn : n ≠ 0)
    (g : GL2 p n) (hg : GL2.IsScalar (p := p) (n := n) g)
    (h_ne : g.val 0 0 ≠ 0) :
    g ∈ Etingof.GL2.ellipticSubgroup p n := by
  change g ∈ (Etingof.GL2.fieldExtEmbed p n).range
  exact ⟨_, (Etingof.scalar_eq_fieldExtEmbed p n hn g hg h_ne).symm⟩

/-- For scalar g, nu(⟨g, _⟩) equals alpha(Units.mk0 (g.val 0 0) _). -/
lemma Etingof.nu_scalar_eq_alpha
    [Fintype (GaloisField p n)] [DecidableEq (GaloisField p n)]
    (hn : n ≠ 0)
    (nu : (Etingof.GL2.ellipticSubgroup p n) →* ℂˣ)
    (g : GL2 p n) (hg : GL2.IsScalar (p := p) (n := n) g)
    (h_ne : g.val 0 0 ≠ 0)
    (hg_mem : g ∈ Etingof.GL2.ellipticSubgroup p n) :
    (nu ⟨g, hg_mem⟩ : ℂ) =
    ((nu.comp (Etingof.GL2.scalarToElliptic p n))
      (Units.mk0 (g.val 0 0) h_ne) : ℂ) := by
  -- alpha = nu ∘ scalarToElliptic, so alpha(a) = nu(scalarToElliptic(a))
  -- We need ⟨g, hg_mem⟩ = scalarToElliptic(Units.mk0 (g.val 0 0) h_ne) as elements of ↥K
  -- Both map to the same underlying GL2 element (the scalar matrix aI)
  -- Both sides are nu applied to the same K-element
  -- ⟨g, hg_mem⟩ and scalarToElliptic(Units.mk0 (g.val 0 0) h_ne) are the same subgroup element
  -- because g = fieldExtEmbed(Units.map algebraMap (Units.mk0 ...))
  congr 1; apply congr_arg
  apply Subtype.ext
  -- Need: g = (scalarToElliptic(Units.mk0 (g.val 0 0) h_ne)).val
  letI := Etingof.algebraGaloisFieldExt p n
  unfold GL2.scalarToElliptic
  simp only [dif_neg hn, MonoidHom.comp_apply, MonoidHom.codRestrict_apply]
  exact Etingof.scalar_eq_fieldExtEmbed p n hn g hg h_ne

/-- Arithmetic identity: the coefficient in the scalar case equals q-1.
Given |B| = (q-1)²q, |G| = (q²-1)(q²-q), |K| = q²-1:
(q-1)/|B| · |G| - |G|/|K| = (q+1)(q-1) - q(q-1) = q-1 -/
lemma Etingof.scalar_coeff_eq (q : ℂ) (hq : q ≠ 0) (hq1 : q - 1 ≠ 0)
    (hq_plus_1 : q + 1 ≠ 0) :
    (q - 1) * ((q - 1) ^ 2 * q)⁻¹ * ((q ^ 2 - 1) * (q ^ 2 - q)) -
    (q ^ 2 - 1)⁻¹ * ((q ^ 2 - 1) * (q ^ 2 - q)) = q - 1 := by
  have hq2 : q ^ 2 - 1 ≠ 0 := by
    rw [show q ^ 2 - 1 = (q - 1) * (q + 1) from by ring]
    exact mul_ne_zero hq1 hq_plus_1
  have hB : (q - 1) ^ 2 * q ≠ 0 := mul_ne_zero (pow_ne_zero _ hq1) hq
  field_simp
  ring

/-- On scalar matrices, |χ(xI)|² = (q-1)². Since χ(xI) = (q-1)α(x) and
|α(x)| = 1 (α is a character to ℂˣ, landing on roots of unity). -/
lemma Etingof.normSq_complementaryChar_scalar
    [Fintype (GaloisField p n)] [DecidableEq (GaloisField p n)]
    [Fintype (GL2 p n)]
    (nu : (Etingof.GL2.ellipticSubgroup p n) →* ℂˣ)
    (hn : n ≠ 0)
    (g : GL2 p n) (hg : GL2.IsScalar (p := p) (n := n) g) :
    Etingof.GL2.complementarySeriesChar p n nu g *
    starRingEnd ℂ (Etingof.GL2.complementarySeriesChar p n nu g) =
    ((Fintype.card (GaloisField p n) : ℂ) - 1) ^ 2 := by
  classical
  -- Setup
  set alpha := nu.comp (GL2.scalarToElliptic p n)
  have h_ne := Etingof.scalar_diag_ne_zero p n g hg
  set z := (alpha (Units.mk0 (g.val 0 0) h_ne) : ℂ)
  have hconj := Etingof.scalar_conj_eq_self p n g hg
  -- Unfold and simplify the character
  unfold GL2.complementarySeriesChar
  rw [Etingof.charW₁_scalar p n g hg, Etingof.charVα₁_scalar p n alpha g hg h_ne]
  -- Main case: n ≠ 0
  have hg_mem := Etingof.scalar_mem_ellipticSubgroup p n hn g hg h_ne
  -- Simplify induced sum: each term is z since x⁻¹gx = g ∈ K
  have hind_term : ∀ x : GL2 p n,
      (if h : x⁻¹ * g * x ∈ GL2.ellipticSubgroup p n
       then (nu ⟨x⁻¹ * g * x, h⟩).val else 0) = z := by
    intro x; rw [hconj x, dif_pos hg_mem]
    rw [Etingof.nu_scalar_eq_alpha p n hn nu g hg h_ne hg_mem]
  simp_rw [hind_term]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  -- Factor out z
  set q := (Fintype.card (GaloisField p n) : ℂ)
  set G := (Fintype.card (GL2 p n) : ℂ)
  set Kc := (Fintype.card ↥(GL2.ellipticSubgroup p n) : ℂ)
  set B := (((Fintype.card (GaloisField p n) - 1) ^ 2 *
    Fintype.card (GaloisField p n) : ℕ) : ℂ)
  -- χ = ((q-1) * B⁻¹ * G - Kc⁻¹ * G) * z
  have hchi : (q * (B⁻¹ * G * z) - B⁻¹ * G * z - Kc⁻¹ * (G * z)) =
      ((q - 1) * B⁻¹ * G - Kc⁻¹ * G) * z := by ring
  rw [hchi, map_mul (starRingEnd ℂ), mul_mul_mul_comm,
    Etingof.units_char_normSq, mul_one]
  -- The coefficient is real, so c * conj(c) = c²
  have hreal : starRingEnd ℂ ((q - 1) * B⁻¹ * G - Kc⁻¹ * G) =
      (q - 1) * B⁻¹ * G - Kc⁻¹ * G := by
    simp only [q, G, Kc, B, map_sub, map_mul, map_inv₀, Complex.conj_natCast,
      Complex.conj_ofNat, map_one, map_pow]
  rw [hreal]
  -- Show the coefficient = q-1 by substituting cardinality values
  suffices h : (q - 1) * B⁻¹ * G - Kc⁻¹ * G = q - 1 by
    rw [h]; ring
  -- Get cardinality facts
  have hq1 : 1 < Fintype.card (GaloisField p n) := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card p n hn]
    exact Nat.one_lt_pow hn hp.out.one_lt
  -- B = (q-1)²·q as ℕ cast
  have hB_val : B = (q - 1) ^ 2 * q := by
    simp only [B, q]
    have h1 : 1 ≤ Fintype.card (GaloisField p n) := by omega
    push_cast [Nat.cast_sub h1]; ring
  -- Use the main theorem to get G and Kc values
  -- G = (q²-1)(q²-q): use Matrix.card_GL_field
  have hGL := @Matrix.card_GL_field (GaloisField p n) _ _ 2
  simp only [Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one] at hGL
  -- hGL: Nat.card GL = (card F - 1) * (card F ^ 2 - card F)
  have hcard_F := Fintype.card (GaloisField p n)
  -- Convert to Fintype.card
  have hGL' : Fintype.card (GL2 p n) =
      (Fintype.card (GaloisField p n) ^ 2 - 1) *
      (Fintype.card (GaloisField p n) ^ 2 - Fintype.card (GaloisField p n)) := by
    rw [← Nat.card_eq_fintype_card]; exact hGL
  have hG_val : G = (q ^ 2 - 1) * (q ^ 2 - q) := by
    simp only [G, q]
    have h1 : 1 ≤ Fintype.card (GaloisField p n) ^ 2 := by nlinarith
    have h2 : Fintype.card (GaloisField p n) ≤ Fintype.card (GaloisField p n) ^ 2 := by nlinarith
    rw [hGL']
    push_cast [Nat.cast_sub h1, Nat.cast_sub h2]; ring
  -- Kc = q² - 1: use card of elliptic subgroup
  have hinj : Function.Injective (GL2.fieldExtEmbed p n) := by
    intro a b hab
    unfold GL2.fieldExtEmbed at hab
    simp only [dif_neg hn] at hab
    exact Units.ext (RingHom.injective
      (Algebra.leftMulMatrix (Module.finBasisOfFinrankEq (GaloisField p n)
      (GaloisField p (2 * n)) (Etingof.finrank_galoisField_ext p n hn))).toRingHom
      (congr_arg (fun g => g.val) hab))
  haveI : Fintype (GaloisField p (2 * n)) := Fintype.ofFinite _
  have hKc_nat : Fintype.card ↥(GL2.ellipticSubgroup p n) =
      Fintype.card (GaloisField p (2 * n))ˣ := by
    -- Use Nat.card to avoid Fintype instance issues
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    change Nat.card ↥(GL2.fieldExtEmbed p n).range = _
    exact Nat.card_congr ((GL2.fieldExtEmbed p n).ofInjective hinj).symm.toEquiv
  have hKc_val : Kc = q ^ 2 - 1 := by
    simp only [Kc, q]
    rw [hKc_nat, Fintype.card_units,
      ← Nat.card_eq_fintype_card,
      GaloisField.card p (2 * n) (Nat.mul_ne_zero two_ne_zero hn)]
    have h1 : 1 ≤ p ^ (2 * n) := Nat.one_le_pow _ _ hp.out.pos
    push_cast [Nat.cast_sub h1]
    rw [← Nat.card_eq_fintype_card, GaloisField.card p n hn]
    push_cast; ring
  -- Nonzero conditions
  have hq_ne : q ≠ 0 := by
    simp only [q]; exact_mod_cast show (Fintype.card (GaloisField p n) : ℕ) ≠ 0 by omega
  have hq1_ne : q - 1 ≠ 0 := by
    simp only [q]; rw [sub_ne_zero]
    exact_mod_cast show Fintype.card (GaloisField p n) ≠ 1 by omega
  have hq_plus_1 : q + 1 ≠ 0 := by
    simp only [q]
    exact_mod_cast show (Fintype.card (GaloisField p n) + 1 : ℕ) ≠ 0 by omega
  -- Substitute and apply scalar_coeff_eq
  rw [hG_val, hKc_val, hB_val]
  exact Etingof.scalar_coeff_eq q hq_ne hq1_ne hq_plus_1

/-- A quadratic ax² + bx + c with a ≠ 0 and zero discriminant b²-4ac = 0
has exactly one distinct root. -/
lemma Etingof.quadratic_one_root_zero_disc
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (a b c : F) (ha : a ≠ 0) (hdisc : b ^ 2 - 4 * a * c = 0) :
    (Finset.univ.filter fun x : F => a * x ^ 2 + b * x + c = 0).card = 1 := by
  -- Uniqueness: if r ≠ s are both roots, disc = a²(r-s)² = 0, contradiction
  have hatmost : ∀ r s : F, a * r ^ 2 + b * r + c = 0 →
      a * s ^ 2 + b * s + c = 0 → r = s := by
    intro r s hr hs
    by_contra hne
    have hne' : r - s ≠ 0 := sub_ne_zero.mpr hne
    -- a(r²-s²) + b(r-s) = 0 → (r-s)(a(r+s)+b) = 0 → a(r+s)+b = 0
    have hab : a * (r + s) + b = 0 := by
      have : (r - s) * (a * (r + s) + b) = 0 := by linear_combination hr - hs
      exact (mul_eq_zero.mp this).resolve_left hne'
    -- disc = a²(r-s)² via Vieta, so a²(r-s)² = 0
    have hars : a ^ 2 * (r - s) ^ 2 = 0 := by
      have hb_eq : b = -(a * (r + s)) := by linear_combination hab
      have hc_eq : c = a * r * s := by
        have : c = -(a * r ^ 2 + b * r) := by linear_combination hr
        rw [this, hb_eq]; ring
      calc a ^ 2 * (r - s) ^ 2 = b ^ 2 - 4 * a * c := by rw [hb_eq, hc_eq]; ring
        _ = 0 := hdisc
    rcases mul_eq_zero.mp hars with h | h
    · exact ha (pow_eq_zero_iff (by omega : 2 ≠ 0) |>.mp h)
    · exact hne' (pow_eq_zero_iff (by omega : 2 ≠ 0) |>.mp h)
  -- Existence: construct a root
  have hexist : ∃ r, a * r ^ 2 + b * r + c = 0 := by
    -- The key identity: 4a(ax²+bx+c) = (2ax+b)² - (b²-4ac) = (2ax+b)²
    -- So ax²+bx+c = 0 iff (2ax+b)² = 0 (when 2a ≠ 0) iff 2ax = -b iff x = -b/(2a)
    -- In char 2: b² = 0, b = 0, equation is ax² + c = 0, use Frobenius for square root
    by_cases h2 : (2 : F) = 0
    · -- char 2: b = 0 (from b² = 4ac = 0), use Frobenius for square root
      have h4 : (4 : F) = 0 := by linear_combination (2 : F) * h2
      have hb_sq : b ^ 2 = 0 := by linear_combination hdisc + h4 * a * c
      have hb : b = 0 := pow_eq_zero_iff (by omega : 2 ≠ 0) |>.mp hb_sq
      have hringchar : ringChar F = 2 := by
        haveI : CharP F 2 := (CharP.charP_iff_prime_eq_zero (by decide : Nat.Prime 2)).mpr h2
        exact ringChar.eq F 2
      obtain ⟨s, hs⟩ := FiniteField.isSquare_of_char_two hringchar (c * a⁻¹)
      refine ⟨s, ?_⟩
      have hsq : a * (s * s) + c = 0 := by
        rw [← hs, mul_comm c a⁻¹, ← mul_assoc, mul_inv_cancel₀ ha, one_mul]
        linear_combination c * h2
      simp only [hb, zero_mul, add_zero, sq]; exact hsq
    · -- char ≠ 2: root is -b/(2a)
      have h2a : (2 * a) ≠ (0 : F) := mul_ne_zero h2 ha
      refine ⟨-b / (2 * a), ?_⟩
      -- 4a · f(-b/(2a)) = (2a·(-b/(2a)) + b)² = (-b+b)² = 0, and 4a ≠ 0, so f = 0
      have h4a_ne : (4 * a : F) ≠ 0 := by
        refine mul_ne_zero ?_ ha
        intro h4
        apply h2
        have : (2 : F) ^ 2 = 4 := by ring
        rw [← this] at h4
        exact pow_eq_zero_iff (by omega : 2 ≠ 0) |>.mp h4
      have key : a * (-b / (2 * a)) ^ 2 + b * (-b / (2 * a)) + c = 0 := by
        suffices 4 * a * (a * (-b / (2 * a)) ^ 2 + b * (-b / (2 * a)) + c) = 0 by
          exact (mul_eq_zero.mp this).resolve_left h4a_ne
        have h_sum : 2 * a * (-b / (2 * a)) + b = 0 := by field_simp; ring
        have identity : ∀ (x : F), 4 * a * (a * x ^ 2 + b * x + c) =
            (2 * a * x + b) ^ 2 - (b ^ 2 - 4 * a * c) := by intro x; ring
        rw [identity, h_sum, hdisc]; ring
      exact key
  obtain ⟨r, hr⟩ := hexist
  rw [Finset.card_eq_one]
  exact ⟨r, by ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_singleton]; exact ⟨fun h => hatmost x r h hr, fun h => h ▸ hr⟩⟩

/-- On parabolic elements, charW₁ = 0 (exactly 1 fixed point on P¹). -/
lemma Etingof.charW₁_parabolic
    [Fintype (GaloisField p n)] [DecidableEq (GaloisField p n)]
    (g : GL2 p n) (hg : GL2.IsParabolic (p := p) (n := n) g) :
    Etingof.GL2.charW₁ p n g = 0 := by
  obtain ⟨hdisc, hnotscalar⟩ := hg
  simp only [Etingof.GL2.charW₁]
  set M := (g : Matrix (Fin 2) (Fin 2) (GaloisField p n))
  have hdisc' : (M 0 0 - M 1 1) ^ 2 + 4 * M 0 1 * M 1 0 = 0 := by rwa [← GL2.disc_eq]
  by_cases h01 : M 0 1 = 0
  · -- Case M₀₁ = 0: from disc = 0, (M₀₀-M₁₁)² = 0, so M₀₀ = M₁₁
    have h00_eq_11 : M 0 0 = M 1 1 := by
      have : (M 0 0 - M 1 1) ^ 2 = 0 := by
        have := hdisc'; rw [h01] at this; linear_combination this
      exact sub_eq_zero.mp (pow_eq_zero_iff (by omega : 2 ≠ 0) |>.mp this)
    have h10 : M 1 0 ≠ 0 := fun h10 => hnotscalar ⟨h01, h10, h00_eq_11⟩
    have hfilt : (Finset.univ.filter fun t : GaloisField p n =>
        M 0 1 * t ^ 2 + (M 0 0 - M 1 1) * t - M 1 0 = 0).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro t _
      simp only [h01, zero_mul, h00_eq_11, sub_self, zero_mul, zero_add]
      exact sub_ne_zero.mpr (Ne.symm h10)
    rw [hfilt]; simp [h01]
  · -- Case M₀₁ ≠ 0: quadratic with zero discriminant has 1 root
    have hfilt_eq : (Finset.univ.filter fun t : GaloisField p n =>
        M 0 1 * t ^ 2 + (M 0 0 - M 1 1) * t - M 1 0 = 0) =
        (Finset.univ.filter fun t : GaloisField p n =>
        M 0 1 * t ^ 2 + (M 0 0 - M 1 1) * t + (-(M 1 0)) = 0) := by
      congr 1; ext t; simp [sub_eq_add_neg]
    have hdisc_zero : (M 0 0 - M 1 1) ^ 2 - 4 * M 0 1 * (-(M 1 0)) = 0 := by
      linear_combination hdisc'
    rw [hfilt_eq, Etingof.quadratic_one_root_zero_disc _ _ _ h01 hdisc_zero]
    simp [h01]

/-- For a monoid homomorphism from a finite group to ℂˣ, the norm squared
of any value is 1 (since all values are roots of unity). -/
lemma Etingof.normSq_monoidHom_val_eq_one
    {G : Type*} [Group G] [Fintype G]
    (χ : G →* ℂˣ) (g : G) :
    (χ g : ℂ) * starRingEnd ℂ (χ g : ℂ) = 1 := by
  -- χ(g)^|G| = 1 (Lagrange's theorem)
  have hord : ((χ g : ℂˣ) : ℂ) ^ Fintype.card G = 1 := by
    have : (χ g) ^ Fintype.card G = (1 : ℂˣ) := by rw [← map_pow, pow_card_eq_one, map_one]
    calc ((χ g : ℂˣ) : ℂ) ^ Fintype.card G
        = ((χ g) ^ Fintype.card G : ℂˣ) := (Units.val_pow_eq_pow_val _ _).symm
      _ = (1 : ℂˣ) := by rw [this]
      _ = 1 := Units.val_one
  -- ‖χ(g)‖ = 1
  have hnorm : ‖(χ g : ℂ)‖ = 1 :=
    Complex.norm_eq_one_of_pow_eq_one hord (Fintype.card_pos.ne')
  -- z * conj(z) = ‖z‖² = 1
  calc (χ g : ℂ) * starRingEnd ℂ (χ g : ℂ)
      = ‖(χ g : ℂ)‖ ^ 2 := RCLike.mul_conj (χ g : ℂ)
    _ = (1 : ℝ) ^ 2 := by rw [hnorm]
    _ = 1 := one_pow 2

/-! ### Discriminant infrastructure (moved here for dependency ordering) -/

/-- disc = tr² - 4·det for 2×2 matrices. -/
lemma Etingof.disc_eq_tr_det (M : Matrix (Fin 2) (Fin 2) (GaloisField p n)) :
    (M 0 0 - M 1 1) ^ 2 + 4 * M 0 1 * M 1 0 =
    (Matrix.trace M) ^ 2 - 4 * Matrix.det M := by
  simp [Matrix.trace_fin_two, Matrix.det_fin_two]; ring

/-- The discriminant is a conjugation invariant: disc(x⁻¹gx) = disc(g). -/
lemma Etingof.disc_conj_eq (g x : GL2 p n) :
    GL2.disc (x⁻¹ * g * x : GL2 p n) = GL2.disc g := by
  simp only [GL2.disc_eq]
  set h := x⁻¹ * g * x
  set G := (g : Matrix (Fin 2) (Fin 2) (GaloisField p n))
  set H := (h : Matrix (Fin 2) (Fin 2) (GaloisField p n))
  rw [Etingof.disc_eq_tr_det (M := H), Etingof.disc_eq_tr_det (M := G)]
  have htr : Matrix.trace H = Matrix.trace G := by
    change Matrix.trace (x⁻¹ * g * x).val = Matrix.trace g.val
    rw [show (x⁻¹ * g * x).val = x⁻¹.val * g.val * x.val from by simp [Units.val_mul]]
    exact Matrix.trace_units_conj' x g.val
  have hdet : Matrix.det H = Matrix.det G := by
    change Matrix.det (x⁻¹ * g * x).val = Matrix.det g.val
    rw [show (x⁻¹ * g * x).val = x⁻¹.val * g.val * x.val from by simp [Units.val_mul]]
    exact Matrix.det_units_conj' x g.val
  rw [htr, hdet]

/-- disc(embed(α)) = trace(α)² - 4·norm(α) in the base field. -/
lemma Etingof.disc_fieldExtEmbed (hn : n ≠ 0) (α : (GaloisField p (2 * n))ˣ) :
    letI := Etingof.algebraGaloisFieldExt p n
    GL2.disc (Etingof.GL2.fieldExtEmbed p n α) =
    Algebra.trace (GaloisField p n) (GaloisField p (2 * n)) (α : GaloisField p (2 * n)) ^ 2 -
    4 * Algebra.norm (GaloisField p n) (α : GaloisField p (2 * n)) := by
  letI := Etingof.algebraGaloisFieldExt p n
  letI := Etingof.scalarTowerGaloisField p n
  haveI := Etingof.finiteDimensionalGaloisFieldExt p n
  let b := Module.finBasisOfFinrankEq (R := GaloisField p n)
    (M := GaloisField p (2 * n)) (Etingof.finrank_galoisField_ext p n hn)
  rw [GL2.disc_eq, Etingof.disc_eq_tr_det]
  have hval : (Etingof.GL2.fieldExtEmbed p n α).val =
      Algebra.leftMulMatrix b (α : GaloisField p (2 * n)) := by
    change (Etingof.GL2.fieldExtEmbed p n α).val = _
    simp only [Etingof.GL2.fieldExtEmbed, dif_neg hn]; rfl
  congr 1
  · congr 1; rw [hval]; exact (Algebra.trace_eq_matrix_trace b _).symm
  · congr 1; rw [hval]; exact (Algebra.norm_eq_matrix_det b _).symm

/-- The algebraMap of disc(embed(α)) equals (α - α^q)² in the extension field. -/
lemma Etingof.algebraMap_disc_fieldExtEmbed (hn : n ≠ 0)
    (α : (GaloisField p (2 * n))ˣ) :
    letI := Etingof.algebraGaloisFieldExt p n
    algebraMap (GaloisField p n) (GaloisField p (2 * n))
      (GL2.disc (Etingof.GL2.fieldExtEmbed p n α)) =
    ((α : GaloisField p (2 * n)) -
     (α : GaloisField p (2 * n)) ^ (p ^ n : ℕ)) ^ 2 := by
  letI := Etingof.algebraGaloisFieldExt p n
  letI := Etingof.scalarTowerGaloisField p n
  haveI := Etingof.finiteDimensionalGaloisFieldExt p n
  rw [Etingof.disc_fieldExtEmbed p n hn α, map_sub, map_mul, map_pow]
  have hfinrank : Module.finrank (GaloisField p n) (GaloisField p (2 * n)) = 2 :=
    Etingof.finrank_galoisField_ext p n hn
  have hcard : Nat.card (GaloisField p n) = p ^ n := GaloisField.card p n hn
  rw [FiniteField.algebraMap_trace_eq_sum_pow, FiniteField.algebraMap_norm_eq_prod_pow]
  rw [hfinrank]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Finset.prod_range_succ,
    Finset.prod_range_zero, one_mul, zero_add, pow_zero, pow_one, hcard]
  have h4 : algebraMap (GaloisField p n) (GaloisField p (2 * n)) 4 = 4 := map_ofNat _ 4
  rw [h4]
  ring

/-- Conjugation preserves IsScalar: if x⁻¹gx is scalar, then g is scalar. -/
lemma Etingof.conj_isScalar (g x : GL2 p n)
    (h : GL2.IsScalar (p := p) (n := n) (x⁻¹ * g * x)) :
    GL2.IsScalar (p := p) (n := n) g := by
  have heq : x⁻¹ * g * x = g := by
    have hcomm := Etingof.scalar_conj_eq_self p n (x⁻¹ * g * x) h x⁻¹
    rw [inv_inv] at hcomm
    have hsimp : x * (x⁻¹ * g * x) * x⁻¹ = g := by group
    rw [hsimp] at hcomm
    exact hcomm.symm
  rwa [← heq]

/-! ### Parabolic character values -/

/-- charVα₁ is a class function: charVα₁(y⁻¹gy) = charVα₁(g). -/
lemma Etingof.charVα₁_conj
    [Fintype (GaloisField p n)] [DecidableEq (GaloisField p n)]
    [Fintype (GL2 p n)]
    (alpha : (GaloisField p n)ˣ →* ℂˣ)
    (g y : GL2 p n) :
    Etingof.GL2.charVα₁ p n alpha (y⁻¹ * g * y) =
    Etingof.GL2.charVα₁ p n alpha g := by
  -- charVα₁(y⁻¹gy) = borelCard⁻¹ * ∑ x, f(x⁻¹(y⁻¹gy)x)
  -- = borelCard⁻¹ * ∑ x, f((yx)⁻¹g(yx))  (since x⁻¹(y⁻¹gy)x = (yx)⁻¹g(yx))
  -- = borelCard⁻¹ * ∑ z, f(z⁻¹gz)  (reindex z = yx)
  -- = charVα₁(g)
  simp only [Etingof.GL2.charVα₁]
  congr 1
  -- After congr 1, goal is about the sums only
  have hconj : ∀ x : GL2 p n,
      (x⁻¹ * (y⁻¹ * g * y) * x : GL2 p n) = (y * x)⁻¹ * g * (y * x) := by
    intro x; group
  simp_rw [hconj]
  -- Goal: ∑ x, f(y*x) = ∑ x, f(x) where f involves let-bindings
  -- Convert ∑ to Fintype.sum form and apply reindexing
  let f' : GL2 p n → ℂ := fun z =>
    if (z⁻¹ * g * z : GL2 p n).val 1 0 = 0 then
      if h : (z⁻¹ * g * z : GL2 p n).val 0 0 ≠ 0 then
        (alpha (Units.mk0 ((z⁻¹ * g * z : GL2 p n).val 0 0) h) : ℂ)
      else 0
    else 0
  show ∑ x, f' ((Equiv.mulLeft y) x) = ∑ x, f' x
  exact Equiv.sum_comp (Equiv.mulLeft y) f'

/-- For upper-triangular parabolic g (g₁₀ = 0), the diagonal entry is nonzero. -/
lemma Etingof.parabolic_diag_ne_zero
    (g : GL2 p n) (hg : GL2.IsParabolic (p := p) (n := n) g)
    (h10 : g.val 1 0 = 0) :
    g.val 0 0 ≠ 0 := by
  intro h
  obtain ⟨hdisc_zero, hnotscalar⟩ := hg
  have hdisc : (g.val 0 0 - g.val 1 1) ^ 2 + 4 * g.val 0 1 * g.val 1 0 = 0 := by
    rwa [← GL2.disc_eq]
  rw [h10] at hdisc
  have h00_eq_11 : g.val 0 0 = g.val 1 1 := by
    have : (g.val 0 0 - g.val 1 1) ^ 2 = 0 := by linear_combination hdisc
    exact sub_eq_zero.mp (pow_eq_zero_iff (by omega : 2 ≠ 0) |>.mp this)
  have hdet : Matrix.det g.val = 0 := by
    simp [Matrix.det_fin_two, h, h10, h00_eq_11.symm ▸ h]
  have hunit := g.isUnit
  rw [Matrix.isUnit_iff_isUnit_det] at hunit
  exact hunit.ne_zero hdet

/-- For upper-triangular parabolic g (g₁₀ = 0), the (0,0) entry of any
upper-triangular conjugate x⁻¹gx equals g₀₀. -/
lemma Etingof.parabolic_upperTri_entry
    [Fintype (GaloisField p n)] [DecidableEq (GaloisField p n)]
    (g : GL2 p n) (hg : GL2.IsParabolic (p := p) (n := n) g)
    (h10 : g.val 1 0 = 0)
    (x : GL2 p n)
    (hx10 : (x⁻¹ * g * x : GL2 p n).val 1 0 = 0) :
    (x⁻¹ * g * x : GL2 p n).val 0 0 = g.val 0 0 := by
  set M := (x⁻¹ * g * x : GL2 p n).val
  -- disc(x⁻¹gx) = disc(g) = 0
  have hdisc_eq : GL2.disc (x⁻¹ * g * x : GL2 p n) = GL2.disc g :=
    Etingof.disc_conj_eq p n g x
  -- From disc = 0 and M₁₀ = 0: (M₀₀ - M₁₁)² = 0, so M₀₀ = M₁₁
  have hdisc_conj : GL2.disc (x⁻¹ * g * x) = 0 := by rw [hdisc_eq]; exact hg.1
  have hdisc' : (M 0 0 - M 1 1) ^ 2 + 4 * M 0 1 * M 1 0 = 0 := by rwa [← GL2.disc_eq]
  have h00_eq_11 : M 0 0 = M 1 1 := by
    have : (M 0 0 - M 1 1) ^ 2 = 0 := by rw [hx10] at hdisc'; linear_combination hdisc'
    exact sub_eq_zero.mp (pow_eq_zero_iff (by omega : 2 ≠ 0) |>.mp this)
  -- tr(x⁻¹gx) = tr(g), and tr(x⁻¹gx) = 2·M₀₀, tr(g) = 2·g₀₀
  -- From disc(g) = 0 and g₁₀ = 0: g₀₀ = g₁₁
  have hg00_eq_11 : g.val 0 0 = g.val 1 1 := by
    have hdisc_g : (g.val 0 0 - g.val 1 1) ^ 2 + 4 * g.val 0 1 * g.val 1 0 = 0 := by
      have := hg.1; rw [GL2.disc_eq] at this; exact this
    have : (g.val 0 0 - g.val 1 1) ^ 2 = 0 := by rw [h10] at hdisc_g; linear_combination hdisc_g
    exact sub_eq_zero.mp (pow_eq_zero_iff (by omega : 2 ≠ 0) |>.mp this)
  -- tr(x⁻¹gx) = M₀₀ + M₁₁ = 2·M₀₀
  -- tr(g) = g₀₀ + g₁₁ = 2·g₀₀
  have htr_eq : Matrix.trace M = Matrix.trace g.val := by
    change Matrix.trace (x⁻¹ * g * x).val = Matrix.trace g.val
    rw [show (x⁻¹ * g * x).val = x⁻¹.val * g.val * x.val from by simp [Units.val_mul]]
    exact Matrix.trace_units_conj' x g.val
  -- M₀₀ + M₁₁ = g₀₀ + g₁₁
  have htr' : M 0 0 + M 1 1 = g.val 0 0 + g.val 1 1 := by
    have h1 : Matrix.trace M = M 0 0 + M 1 1 := Matrix.trace_fin_two M
    have h2 : Matrix.trace g.val = g.val 0 0 + g.val 1 1 := Matrix.trace_fin_two g.val
    rw [← h1, ← h2]; exact htr_eq
  -- Use det(x⁻¹gx) = det(g) to get M₀₀² = g₀₀²
  have hdet_eq : Matrix.det M = Matrix.det g.val := by
    change Matrix.det (x⁻¹ * g * x).val = Matrix.det g.val
    rw [show (x⁻¹ * g * x).val = x⁻¹.val * g.val * x.val from by simp [Units.val_mul]]
    exact Matrix.det_units_conj' x g.val
  -- det(M) = M₀₀² (since M₁₀ = 0 and M₀₀ = M₁₁)
  have hdetM : Matrix.det M = M 0 0 * M 0 0 - M 0 1 * 0 := by
    rw [Matrix.det_fin_two]; congr 1; rw [h00_eq_11]; rw [hx10]
  have hdetG : Matrix.det g.val = g.val 0 0 * g.val 0 0 - g.val 0 1 * 0 := by
    rw [Matrix.det_fin_two]; congr 1; rw [hg00_eq_11]; rw [h10]
  simp only [mul_zero, sub_zero] at hdetM hdetG
  -- M₀₀² = g₀₀²
  have hsq : M 0 0 * M 0 0 = g.val 0 0 * g.val 0 0 := by
    rw [← hdetM, ← hdetG, hdet_eq]
  -- (M₀₀ - g₀₀) * (M₀₀ + g₀₀) = 0
  have hprod : (M 0 0 - g.val 0 0) * (M 0 0 + g.val 0 0) = 0 := by
    have : M 0 0 * M 0 0 - g.val 0 0 * g.val 0 0 = 0 := sub_eq_zero.mpr hsq
    linear_combination this
  rcases mul_eq_zero.mp hprod with h | h
  · exact sub_eq_zero.mp h
  · -- M₀₀ + g₀₀ = 0 means M₀₀ = -g₀₀
    -- From trace: M₀₀ + M₁₁ = g₀₀ + g₁₁, i.e. M₀₀ + M₀₀ = g₀₀ + g₀₀
    -- Combined with M₀₀ = -g₀₀: 4·g₀₀ = 0
    have h4 : (4 : GaloisField p n) * g.val 0 0 = 0 := by
      linear_combination -htr' - h00_eq_11 + hg00_eq_11 + 2 * h
    have hg00_ne : g.val 0 0 ≠ 0 := Etingof.parabolic_diag_ne_zero p n g hg h10
    rcases mul_eq_zero.mp h4 with h4z | h4z
    · -- 4 = 0 means char = 2, so M₀₀ + g₀₀ = 0 iff M₀₀ = g₀₀
      have h2 : (2 : GaloisField p n) = 0 := by
        have : (4 : GaloisField p n) = 2 * 2 := by ring
        rw [this] at h4z
        rcases mul_eq_zero.mp h4z with h2z | h2z <;> exact h2z
      -- In char 2: M₀₀ - g₀₀ = (M₀₀ + g₀₀) - 2*g₀₀ = 0 - 0 = 0
      exact sub_eq_zero.mp (by linear_combination h - g.val 0 0 * h2)
    · exact absurd h4z hg00_ne

/-- For upper-triangular parabolic g (g₁₀ = 0), the set of x ∈ GL₂ with
(x⁻¹gx)₁₀ = 0 consists exactly of upper-triangular matrices (y = 0).
This follows from the formula (x⁻¹gx)₁₀ = d⁻¹ · (-g₀₁ · y²) where y = x.val 1 0
and g₀₁ ≠ 0 (since g is parabolic with g₁₀ = 0 and not scalar). -/
lemma Etingof.parabolic_upperTri_count
    [Fintype (GaloisField p n)] [DecidableEq (GaloisField p n)]
    [Fintype (GL2 p n)]
    (g : GL2 p n) (hg : GL2.IsParabolic (p := p) (n := n) g)
    (h10 : g.val 1 0 = 0) :
    ∀ x : GL2 p n, (x⁻¹ * g * x : GL2 p n).val 1 0 = 0 → x.val 1 0 = 0 := by
  -- g₀₁ ≠ 0 (since g is parabolic, g₁₀ = 0, not scalar → g₀₁ ≠ 0 or g₀₀ ≠ g₁₁, but disc = 0
  -- and g₁₀ = 0 forces g₀₀ = g₁₁, so must have g₀₁ ≠ 0)
  obtain ⟨hdisc, hnotscalar⟩ := hg
  have hdisc' : (g.val 0 0 - g.val 1 1) ^ 2 + 4 * g.val 0 1 * g.val 1 0 = 0 := by
    rwa [← GL2.disc_eq]
  rw [h10] at hdisc'
  have h00_eq_11 : g.val 0 0 = g.val 1 1 := by
    have : (g.val 0 0 - g.val 1 1) ^ 2 = 0 := by linear_combination hdisc'
    exact sub_eq_zero.mp (pow_eq_zero_iff (by omega : 2 ≠ 0) |>.mp this)
  have h01 : g.val 0 1 ≠ 0 := fun h01 => hnotscalar ⟨h01, h10, h00_eq_11⟩
  intro x hx
  -- Key idea: from x * (x⁻¹gx) = g * x, comparing (0,0) entries:
  -- x₀₀ * (x⁻¹gx)₀₀ + x₀₁ * (x⁻¹gx)₁₀ = g₀₀ * x₀₀ + g₀₁ * x₁₀
  -- With (x⁻¹gx)₁₀ = 0 (by hx) and (x⁻¹gx)₀₀ = g₀₀ (by parabolic_upperTri_entry):
  -- g₀₀ * x₀₀ = g₀₀ * x₀₀ + g₀₁ * x₁₀
  -- So g₀₁ * x₁₀ = 0, and since g₀₁ ≠ 0, x₁₀ = 0.
  set conj := (x⁻¹ * g * x : GL2 p n) with hconjdef
  have hconj00 : conj.val 0 0 = g.val 0 0 :=
    Etingof.parabolic_upperTri_entry p n g ⟨hdisc, hnotscalar⟩ h10 x hx
  -- x * conj = g * x (since conj = x⁻¹gx)
  have hmul : x * conj = g * x := by
    rw [hconjdef]; group
  -- Compare (0,0) entries of x.val * conj.val = (g * x).val
  have hmul_val : (x * conj).val = x.val * conj.val := by simp [Units.val_mul]
  have hgx_val : (g * x).val = g.val * x.val := by simp [Units.val_mul]
  have hmul_eq : x.val * conj.val = g.val * x.val := by
    rw [← hmul_val, ← hgx_val]; exact congrArg _ hmul
  -- Extract (0,0) entries
  have h00 : (x.val * conj.val) 0 0 = (g.val * x.val) 0 0 := by
    rw [hmul_eq]
  -- Expand using Fin.sum_univ_two
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at h00
  -- h00: x₀₀ * conj₀₀ + x₀₁ * conj₁₀ = g₀₀ * x₀₀ + g₀₁ * x₁₀
  -- After simp, h00 should be:
  -- x₀₀ * conj₀₀ + x₀₁ * conj₁₀ = g₀₀ * x₀₀ + g₀₁ * x₁₀
  -- Substitute conj₀₀ = g₀₀ and conj₁₀ = 0:
  have hconj10 : conj.val 1 0 = 0 := hx
  rw [hconj10, hconj00] at h00
  simp only [mul_zero, add_zero] at h00
  -- h00: g₀₀ * x₀₀ = g₀₀ * x₀₀ + g₀₁ * x₁₀
  have : g.val 0 1 * x.val 1 0 = 0 := by linear_combination -h00
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h h01
  · exact h

/-- For upper-triangular parabolic g, charVα₁(g) = α(g₀₀). -/
lemma Etingof.charVα₁_parabolic_upperTri
    [Fintype (GaloisField p n)] [DecidableEq (GaloisField p n)]
    [Fintype (GL2 p n)]
    (alpha : (GaloisField p n)ˣ →* ℂˣ)
    (g : GL2 p n) (hg : GL2.IsParabolic (p := p) (n := n) g)
    (h10 : g.val 1 0 = 0) :
    Etingof.GL2.charVα₁ p n alpha g =
    (alpha (Units.mk0 (g.val 0 0) (Etingof.parabolic_diag_ne_zero p n g hg h10)) : ℂ) := by
  unfold Etingof.GL2.charVα₁
  set a := g.val 0 0
  set ha := Etingof.parabolic_diag_ne_zero p n g hg h10
  set borelCard : ℂ := (((Fintype.card (GaloisField p n) - 1) ^ 2 *
    Fintype.card (GaloisField p n) : ℕ) : ℂ)
  -- Every term in the sum: if (x⁻¹gx)₁₀ = 0 then α(a) else 0
  -- Because (x⁻¹gx)₀₀ = a for all such x (by parabolic_upperTri_entry)
  -- And (x⁻¹gx)₀₀ ≠ 0 (since a ≠ 0)
  have hterm : ∀ x : GL2 p n,
      (let conj := (x⁻¹ * g * x : GL2 p n)
       let M := (conj : Matrix (Fin 2) (Fin 2) (GaloisField p n))
       if M 1 0 = 0 then
         if h : M 0 0 ≠ 0 then (alpha (Units.mk0 (M 0 0) h) : ℂ)
         else 0
       else 0) =
      if (x⁻¹ * g * x : GL2 p n).val 1 0 = 0 then
        (alpha (Units.mk0 a ha) : ℂ)
      else 0 := by
    intro x
    by_cases hx10 : (x⁻¹ * g * x : GL2 p n).val 1 0 = 0
    · -- upper-tri conjugate: entry = a
      simp only [hx10, ite_true]
      have hentry := Etingof.parabolic_upperTri_entry p n g hg h10 x hx10
      rw [dif_pos (hentry ▸ ha)]
      have : Units.mk0 ((x⁻¹ * g * x : GL2 p n).val 0 0) (hentry ▸ ha) =
             Units.mk0 a ha := by
        ext; exact hentry
      simp only [this]
    · simp only [hx10, ite_false]
  conv in (Finset.univ.sum _) =>
    arg 2; ext x; rw [hterm]
  -- Sum = α(a) * |{x : (x⁻¹gx)₁₀ = 0}|
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  -- |{x : (x⁻¹gx)₁₀ = 0}| = borelCard
  -- For x with (x⁻¹gx)₁₀ = 0: x.val 1 0 = 0 (by parabolic_upperTri_count)
  -- and conversely, any upper-tri invertible x gives upper-tri conjugate
  -- Count of upper-tri GL₂ = (q-1)²·q = borelCard
  -- Step 1: The filter set equals {x : GL₂ | x₁₀ = 0}
  have hfilt_eq : (Finset.univ.filter fun x : GL2 p n => (x⁻¹ * g * x : GL2 p n).val 1 0 = 0) =
      (Finset.univ.filter fun x : GL2 p n => x.val 1 0 = 0) := by
    ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact Etingof.parabolic_upperTri_count p n g hg h10 x
    · -- Converse: if x₁₀ = 0 and g₁₀ = 0, then (x⁻¹gx)₁₀ = 0
      intro hx10
      -- From x * x⁻¹ = 1, entry (1,0): x₁₀ * (x⁻¹)₀₀ + x₁₁ * (x⁻¹)₁₀ = 0
      have hxxinv : x.val * x⁻¹.val = 1 := by
        rw [← Units.val_mul]; simp
      have h10_eq : (x.val * x⁻¹.val) 1 0 = (1 : Matrix (Fin 2) (Fin 2) (GaloisField p n)) 1 0 := by
        rw [hxxinv]
      simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] at h10_eq
      -- h10_eq: x₁₀ * (x⁻¹)₀₀ + x₁₁ * (x⁻¹)₁₀ = 0
      have hxinv10 : x⁻¹.val 1 0 = 0 := by
        simp only [hx10, zero_mul, zero_add, Fin.isValue, Matrix.one_apply,
          one_ne_zero, ite_false] at h10_eq
        -- h10_eq : x.val 1 1 * x⁻¹.val 1 0 = 0
        -- x₁₁ ≠ 0 since det(x) ≠ 0 and x₁₀ = 0
        have hdet_ne : Matrix.det x.val ≠ 0 := by
          intro hdet0
          have hiu := x.isUnit
          rw [Matrix.isUnit_iff_isUnit_det] at hiu
          exact hiu.ne_zero hdet0
        have hdet' : x.val 0 0 * x.val 1 1 ≠ 0 := by
          rw [Matrix.det_fin_two] at hdet_ne
          rwa [hx10, mul_zero, sub_zero] at hdet_ne
        have hx11_ne : x.val 1 1 ≠ 0 := right_ne_zero_of_mul hdet'
        exact (mul_eq_zero.mp h10_eq).resolve_left hx11_ne
      -- Now compute (x⁻¹ * g * x).val 1 0
      have hmul : (x⁻¹ * g * x).val = x⁻¹.val * g.val * x.val := by simp [Units.val_mul]
      rw [show (x⁻¹ * g * x : GL2 p n).val 1 0 = (x⁻¹.val * g.val * x.val) 1 0 from by
        simp [Units.val_mul]]
      simp only [Matrix.mul_apply, Fin.sum_univ_two]
      rw [hxinv10, h10, hx10]
      ring
  rw [hfilt_eq]
  -- Step 2: Count {x : GL₂ | x₁₀ = 0} = (q-1)²·q
  -- Upper-tri invertible = x₀₀ ≠ 0, x₁₁ ≠ 0, x₀₁ arbitrary
  -- This has cardinality (q-1) · q · (q-1) = (q-1)²·q = borelCard
  -- Goal: borelCard⁻¹ * (↑(filter card) * ↑(alpha ...)) = ↑(alpha ...)
  -- Suffices: borelCard⁻¹ * borelCard = 1, i.e. filter card = borelCard as ℕ
  -- Then rearrange: borelCard⁻¹ * borelCard * α = 1 * α = α
  -- First show borelCard ≠ 0 (need q ≥ 2)
  set q := Fintype.card (GaloisField p n) with hq_def
  have hq_ge : 1 < q := Fintype.one_lt_card
  have hq_pos : 0 < q := by omega
  have hq1_pos : 0 < q - 1 := by omega
  -- borelCard as ℕ
  set bc_nat := (q - 1) ^ 2 * q with hbc_nat_def
  have hbc_nat_pos : 0 < bc_nat := by positivity
  have hbc_ne_zero : (bc_nat : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  -- Show filter card = bc_nat
  suffices hcard : (Finset.univ.filter fun x : GL2 p n => x.val 1 0 = 0).card = bc_nat by
    rw [hcard]
    -- Goal: borelCard⁻¹ * ((bc_nat : ℂ) * α(...)) = α(...)
    rw [show borelCard = (bc_nat : ℂ) from rfl]
    rw [inv_mul_cancel_left₀ hbc_ne_zero]
  -- Build bijection: {x : GL₂ | x₁₀ = 0} ≃ F_q× × F_q × F_q×
  -- Forward: x ↦ (x₀₀, x₀₁, x₁₁) where x₀₀, x₁₁ are units
  -- Backward: (w, u, z) ↦ [[w, u], [0, z]] ∈ GL₂
  -- Helper: for x ∈ GL₂ with x₁₀ = 0, det = x₀₀*x₁₁ ≠ 0
  have hdet_entries (x : GL2 p n) (hx : x.val 1 0 = 0) :
      x.val 0 0 * x.val 1 1 ≠ 0 := by
    have hiu := x.isUnit
    rw [Matrix.isUnit_iff_isUnit_det] at hiu
    have hdet_ne := hiu.ne_zero
    rw [Matrix.det_fin_two, hx, mul_zero, sub_zero] at hdet_ne
    exact hdet_ne
  set S := Finset.univ.filter (fun x : GL2 p n => x.val 1 0 = 0) with hS_def
  -- Count via surjection from F_q× × F_q × F_q×
  set T := (Finset.univ : Finset ((GaloisField p n)ˣ × GaloisField p n × (GaloisField p n)ˣ))
  have hTcard : T.card = bc_nat := by
    rw [hbc_nat_def]
    change Fintype.card ((GaloisField p n)ˣ × GaloisField p n × (GaloisField p n)ˣ) =
      (q - 1) ^ 2 * q
    rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_units, ← hq_def]
    -- Goal: (q - 1) * (q * (q - 1)) = (q - 1) ^ 2 * q
    nlinarith [sq_nonneg (q - 1), hq1_pos]
  rw [← hTcard]
  -- Define forward map
  let fwd : (x : GL2 p n) → x ∈ S → (GaloisField p n)ˣ × GaloisField p n × (GaloisField p n)ˣ :=
    fun x hxS =>
      let hx := (Finset.mem_filter.mp hxS).2
      (Units.mk0 (x.val 0 0) (left_ne_zero_of_mul (hdet_entries x hx)),
       x.val 0 1,
       Units.mk0 (x.val 1 1) (right_ne_zero_of_mul (hdet_entries x hx)))
  apply Finset.card_bij fwd
  · -- fwd maps into T
    intro x _; exact Finset.mem_univ _
  · -- fwd is injective
    intro x₁ hx₁ x₂ hx₂ heq
    have hx10_1 := (Finset.mem_filter.mp hx₁).2
    have hx10_2 := (Finset.mem_filter.mp hx₂).2
    have h00 : x₁.val 0 0 = x₂.val 0 0 := by
      have := congr_arg (fun t : (GaloisField p n)ˣ × GaloisField p n × (GaloisField p n)ˣ =>
        (t.1 : GaloisField p n)) heq
      simpa [fwd] using this
    have h01 : x₁.val 0 1 = x₂.val 0 1 := by
      have := congr_arg (fun t : (GaloisField p n)ˣ × GaloisField p n × (GaloisField p n)ˣ =>
        t.2.1) heq
      simpa [fwd] using this
    have h11 : x₁.val 1 1 = x₂.val 1 1 := by
      have := congr_arg (fun t : (GaloisField p n)ˣ × GaloisField p n × (GaloisField p n)ˣ =>
        (t.2.2 : GaloisField p n)) heq
      simpa [fwd] using this
    exact Matrix.GeneralLinearGroup.ext fun i j => by
      fin_cases i <;> fin_cases j <;> simp_all
  · -- fwd is surjective: for (w, u, z) build [[w, u], [0, z]]
    intro ⟨w, u, z⟩ _
    have hdet : Matrix.det !![↑w, u; (0 : GaloisField p n), ↑z] ≠ 0 := by
      simp [Matrix.det_fin_two, w.ne_zero, z.ne_zero]
    set mat := !![↑w, u; (0 : GaloisField p n), ↑z]
    set M := Matrix.GeneralLinearGroup.mkOfDetNeZero mat hdet
    have hMval : M.val = mat := by
      simp [M, Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.GeneralLinearGroup.mk',
            Matrix.unitOfDetInvertible]
    have hM10 : M.val 1 0 = 0 := by
      rw [hMval]; simp [mat, Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_fin_const]
    have hM00 : M.val 0 0 = ↑w := by
      rw [hMval]; simp [mat, Matrix.cons_val_zero, Matrix.vecHead]
    have hM01 : M.val 0 1 = u := by
      rw [hMval]; simp [mat, Matrix.cons_val_zero, Matrix.cons_val_one,
            Matrix.vecHead, Matrix.vecTail]
    have hM11 : M.val 1 1 = ↑z := by
      rw [hMval]; simp [mat, Matrix.cons_val_one, Matrix.vecTail, Matrix.vecHead]
    have hMS : M ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hM10⟩
    refine ⟨M, hMS, ?_⟩
    simp only [fwd]
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · exact Units.ext hM00
    · exact hM01
    · exact Units.ext hM11

/-- For parabolic g, charVα₁(g) = α(a) for some unit a (the repeated eigenvalue).

Uses the class function property (charVα₁ is conjugation-invariant) to reduce to the
upper-triangular case, then direct computation shows every upper-tri conjugate has
the same (0,0) entry and the count of such conjugates equals borelCard. -/
lemma Etingof.charVα₁_parabolic
    [Fintype (GaloisField p n)] [DecidableEq (GaloisField p n)]
    [Fintype (GL2 p n)]
    (alpha : (GaloisField p n)ˣ →* ℂˣ)
    (g : GL2 p n) (hg : GL2.IsParabolic (p := p) (n := n) g) :
    ∃ a : (GaloisField p n)ˣ, Etingof.GL2.charVα₁ p n alpha g = (alpha a : ℂ) := by
  -- Case split: either g₁₀ = 0 (already upper-triangular) or g₁₀ ≠ 0
  by_cases h10 : g.val 1 0 = 0
  · -- Already upper-triangular, apply charVα₁_parabolic_upperTri
    exact ⟨Units.mk0 (g.val 0 0) (Etingof.parabolic_diag_ne_zero p n g hg h10),
           Etingof.charVα₁_parabolic_upperTri p n alpha g hg h10⟩
  · -- g₁₀ ≠ 0: conjugate to make it upper-triangular, then apply the upper-tri case.
    -- Use charVα₁_conj to transfer: charVα₁(g) = charVα₁(y⁻¹gy) for any y.
    -- Construct y such that (y⁻¹gy)₁₀ = 0.
    obtain ⟨hdisc, hnotscalar⟩ := hg
    have hdisc' : (g.val 0 0 - g.val 1 1) ^ 2 + 4 * g.val 0 1 * g.val 1 0 = 0 := by
      rwa [← GL2.disc_eq]
    -- Case split on g₀₁
    by_cases h01 : g.val 0 1 = 0
    · -- g₀₁ = 0: disc = (g₀₀-g₁₁)² = 0, so g₀₀ = g₁₁. Use swap matrix [[0,1],[1,0]].
      have h00_eq_11 : g.val 0 0 = g.val 1 1 := by
        have : (g.val 0 0 - g.val 1 1) ^ 2 = 0 := by rw [h01] at hdisc'; linear_combination hdisc'
        exact sub_eq_zero.mp (pow_eq_zero_iff (by omega : 2 ≠ 0) |>.mp this)
      -- Construct the swap matrix y = [[0,1],[1,0]]
      have hdet_swap : Matrix.det !![(0 : GaloisField p n), 1; 1, 0] ≠ 0 := by
        simp [Matrix.det_fin_two]
      set y := Matrix.GeneralLinearGroup.mkOfDetNeZero
        !![(0 : GaloisField p n), 1; 1, 0] hdet_swap
      have hyval : y.val = !![(0 : GaloisField p n), 1; 1, 0] := by
        simp [y, Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.GeneralLinearGroup.mk',
              Matrix.unitOfDetInvertible]
      -- Compute (y⁻¹gy)₁₀: For swap, y⁻¹gy swaps rows/cols, giving [[g₁₁,g₁₀],[g₀₁,g₀₀]]
      -- So (y⁻¹gy)₁₀ = g₀₁ = 0
      set g' := y⁻¹ * g * y with hg'_def
      have hg'10 : g'.val 1 0 = 0 := by
        -- Use y * g' = g * y (since g' = y⁻¹gy)
        have hconj : y * g' = g * y := by rw [hg'_def]; group
        -- Extract entries of y
        have hy00 : y.val 0 0 = 0 := by rw [hyval]; simp [Matrix.cons_val_zero, Matrix.vecHead]
        have hy01 : y.val 0 1 = 1 := by
          rw [hyval]; simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.vecHead, Matrix.vecTail]
        have hy10 : y.val 1 0 = 1 := by
          rw [hyval]; simp [Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_fin_const]
        have hy11 : y.val 1 1 = 0 := by
          rw [hyval]; simp [Matrix.cons_val_one, Matrix.vecTail, Matrix.vecHead]
        -- Compare (0,0) entries: y₀₀*g'₀₀ + y₀₁*g'₁₀ = g₀₀*y₀₀ + g₀₁*y₁₀
        have hmul_eq : y.val * g'.val = g.val * y.val := by
          rw [← Units.val_mul, ← Units.val_mul]; exact congrArg _ hconj
        have h_eq00 : (y.val * g'.val) 0 0 = (g.val * y.val) 0 0 := by rw [hmul_eq]
        simp only [Matrix.mul_apply, Fin.sum_univ_two, hy00, hy01, hy10, hy11] at h_eq00
        simp only [zero_mul, zero_add, one_mul, mul_zero, mul_one] at h_eq00
        -- h_eq00: g'₁₀ = g₀₁ = 0
        rw [h01] at h_eq00; exact h_eq00
      -- g' is parabolic
      have hg'_parabolic : GL2.IsParabolic (p := p) (n := n) g' := by
        refine ⟨?_, fun hscalar => hnotscalar (Etingof.conj_isScalar p n g y hscalar)⟩
        rw [show GL2.disc g' = GL2.disc g from Etingof.disc_conj_eq p n g y]
        exact hdisc
      -- Apply upper-tri result to g'
      have ha' := Etingof.charVα₁_parabolic_upperTri p n alpha g' hg'_parabolic hg'10
      -- charVα₁(g) = charVα₁(y⁻¹gy) = charVα₁(g')
      have hconj_inv := (Etingof.charVα₁_conj p n alpha g y).symm
      rw [show y⁻¹ * g * y = g' from rfl] at hconj_inv
      exact ⟨_, hconj_inv.trans ha'⟩
    · -- g₀₁ ≠ 0: use y = [[1,0],[c,1]] where c is the root of the quadratic
      -- g₁₀ + c*(g₁₁ - g₀₀) - c²*g₀₁ = 0
      -- Rewrite as: (-g₀₁)*c² + (g₁₁ - g₀₀)*c + g₁₀ = 0
      -- Discriminant: (g₁₁ - g₀₀)² - 4*(-g₀₁)*g₁₀ = (g₁₁-g₀₀)² + 4*g₀₁*g₁₀
      --            = (g₀₀-g₁₁)² + 4*g₀₁*g₁₀ = disc(g) = 0
      -- So by quadratic_one_root_zero_disc, there's exactly one root c₀
      have hneg01 : -g.val 0 1 ≠ 0 := neg_ne_zero.mpr h01
      have hqdisc : (g.val 1 1 - g.val 0 0) ^ 2 - 4 * (-g.val 0 1) * g.val 1 0 = 0 := by
        linear_combination hdisc'
      have hone_root := Etingof.quadratic_one_root_zero_disc
        (-g.val 0 1) (g.val 1 1 - g.val 0 0) (g.val 1 0) hneg01 hqdisc
      -- Extract a root c₀
      have hroot_exists : ∃ c₀ : GaloisField p n,
          -g.val 0 1 * c₀ ^ 2 + (g.val 1 1 - g.val 0 0) * c₀ + g.val 1 0 = 0 := by
        by_contra hall
        push_neg at hall
        have : (Finset.univ.filter fun x => -g.val 0 1 * x ^ 2 +
          (g.val 1 1 - g.val 0 0) * x + g.val 1 0 = 0).card = 0 := by
          rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          intro t _; exact hall t
        omega
      obtain ⟨c₀, hc₀⟩ := hroot_exists
      -- Construct y = [[1,0],[c₀,1]] with det = 1
      have hdet_y : Matrix.det !![(1 : GaloisField p n), 0; c₀, 1] ≠ 0 := by
        simp [Matrix.det_fin_two]
      set y := Matrix.GeneralLinearGroup.mkOfDetNeZero
        !![(1 : GaloisField p n), 0; c₀, 1] hdet_y
      have hyval : y.val = !![(1 : GaloisField p n), 0; c₀, 1] := by
        simp [y, Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.GeneralLinearGroup.mk',
              Matrix.unitOfDetInvertible]
      -- Extract entries of y
      have hy00 : y.val 0 0 = 1 := by rw [hyval]; simp [Matrix.cons_val_zero, Matrix.vecHead]
      have hy01 : y.val 0 1 = 0 := by
        rw [hyval]; simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.vecHead, Matrix.vecTail]
      have hy10 : y.val 1 0 = c₀ := by
        rw [hyval]; simp [Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_fin_const]
      have hy11 : y.val 1 1 = 1 := by
        rw [hyval]; simp [Matrix.cons_val_one, Matrix.vecTail, Matrix.vecHead]
      set g' := y⁻¹ * g * y with hg'_def
      -- Show (g')₁₀ = 0 using y * g' = g * y, entry (1,0)
      have hg'10 : g'.val 1 0 = 0 := by
        -- y * g' = g * y
        have hconj : y * g' = g * y := by rw [hg'_def]; group
        have hmul_eq : y.val * g'.val = g.val * y.val := by
          rw [← Units.val_mul, ← Units.val_mul]; exact congrArg _ hconj
        -- Entry (1,0)
        have h_eq10 : (y.val * g'.val) 1 0 = (g.val * y.val) 1 0 := by rw [hmul_eq]
        simp only [Matrix.mul_apply, Fin.sum_univ_two, hy00, hy01, hy10, hy11] at h_eq10
        simp only [one_mul, zero_mul, add_zero, mul_zero, mul_one] at h_eq10
        -- Entry (0,0)
        have h_eq00 : (y.val * g'.val) 0 0 = (g.val * y.val) 0 0 := by rw [hmul_eq]
        simp only [Matrix.mul_apply, Fin.sum_univ_two, hy00, hy01, hy10, hy11] at h_eq00
        simp only [one_mul, zero_mul, add_zero, mul_zero, mul_one] at h_eq00
        -- From h_eq10 and h_eq00 and hc₀, derive g'₁₀ = 0
        linear_combination h_eq10 - c₀ * h_eq00 + hc₀
      -- g' is parabolic
      have hg'_parabolic : GL2.IsParabolic (p := p) (n := n) g' := by
        refine ⟨?_, fun hscalar => hnotscalar (Etingof.conj_isScalar p n g y hscalar)⟩
        rw [show GL2.disc g' = GL2.disc g from Etingof.disc_conj_eq p n g y]
        exact hdisc
      -- Apply upper-tri result
      have ha' := Etingof.charVα₁_parabolic_upperTri p n alpha g' hg'_parabolic hg'10
      have hconj_inv := (Etingof.charVα₁_conj p n alpha g y).symm
      rw [show y⁻¹ * g * y = g' from rfl] at hconj_inv
      exact ⟨_, hconj_inv.trans ha'⟩

open Classical in
/-- On parabolic g, the complementary series character equals -α(eigenvalue).
This follows from charW₁ = 0 and Ind = 0, giving χ = -charVα₁.
For parabolic g, charVα₁(g) = α(a) where a is the repeated eigenvalue. -/
lemma Etingof.complementaryChar_parabolic_val
    [Fintype (GaloisField p n)] [DecidableEq (GaloisField p n)]
    [Fintype (GL2 p n)]
    (nu : (Etingof.GL2.ellipticSubgroup p n) →* ℂˣ)
    (g : GL2 p n) (hg : GL2.IsParabolic (p := p) (n := n) g) :
    ∃ a : (GaloisField p n)ˣ,
      Etingof.GL2.complementarySeriesChar p n nu g =
      -((nu.comp (Etingof.GL2.scalarToElliptic p n) : (GaloisField p n)ˣ →* ℂˣ) a : ℂ) := by
  -- Step 1: charW₁(g) = 0 for parabolic g
  have hW : Etingof.GL2.charW₁ p n g = 0 := Etingof.charW₁_parabolic p n g hg
  -- Step 2: No conjugate of parabolic g lies in elliptic subgroup K.
  -- Inline proof: disc is a conjugation invariant (uses tr²-4det form),
  -- K elements with disc=0 must be scalar, and conjugation preserves IsScalar.
  have hnoK : ∀ x : GL2 p n, ¬(x⁻¹ * g * x ∈ Etingof.GL2.ellipticSubgroup p n) := by
    intro x hcontra
    obtain ⟨hdisc_zero, hnotscalar⟩ := hg
    have hdisc_conj : GL2.disc (x⁻¹ * g * x : GL2 p n) = GL2.disc g :=
      Etingof.disc_conj_eq p n g x
    obtain ⟨α, hα⟩ := hcontra
    by_cases hn : n = 0
    · -- n = 0: K is trivial
      have h1 : GL2.fieldExtEmbed p n α = 1 := by unfold GL2.fieldExtEmbed; simp [hn]
      have hone : x⁻¹ * g * x = 1 := hα ▸ h1
      have hg1 : g = 1 := by
        have key : x * (x⁻¹ * g * x) * x⁻¹ = g := by group
        rw [hone] at key; simpa using key.symm
      exact hnotscalar (hg1 ▸ ⟨by simp [Units.val_one], by simp [Units.val_one],
        by simp [Units.val_one]⟩)
    · letI := Etingof.algebraGaloisFieldExt p n
      have hconj_disc : GL2.disc (GL2.fieldExtEmbed p n α) = 0 := by
        rw [hα, hdisc_conj]; exact hdisc_zero
      -- α^q = α (from disc = 0), so α ∈ base field
      set s := (α : GaloisField p (2 * n)) - (α : GaloisField p (2 * n)) ^ (p ^ n : ℕ)
      have hd := Etingof.algebraMap_disc_fieldExtEmbed p n hn α
      have hinj := (algebraMap (GaloisField p n) (GaloisField p (2 * n))).injective
      have hs : s = 0 := by
        have : s ^ 2 = 0 := by rw [← hd, hconj_disc, map_zero]
        exact pow_eq_zero_iff (by omega : 2 ≠ 0) |>.mp this
      have hα_frob : (α : GaloisField p (2 * n)) ^ (p ^ n : ℕ) =
          (α : GaloisField p (2 * n)) := (sub_eq_zero.mp hs).symm
      -- α is in the image of algebraMap
      have hα_in_range : (α : GaloisField p (2 * n)) ∈ Set.range
          (algebraMap (GaloisField p n) (GaloisField p (2 * n))) := by
        haveI : Fintype (GaloisField p (2 * n)) := Fintype.ofFinite _
        set fixed := Finset.univ.filter
          (fun x : GaloisField p (2 * n) => x ^ (p ^ n : ℕ) = x)
        set img := Finset.univ.image
          (algebraMap (GaloisField p n) (GaloisField p (2 * n)))
        have hcard_n : Fintype.card (GaloisField p n) = p ^ n := by
          rw [← Nat.card_eq_fintype_card, GaloisField.card p n hn]
        have hα_mem : (α : GaloisField p (2 * n)) ∈ fixed := by
          simp only [fixed, Finset.mem_filter, Finset.mem_univ, true_and]; exact hα_frob
        have himg_sub : img ⊆ fixed := by
          intro y hy
          simp only [img, Finset.mem_image, Finset.mem_univ, true_and] at hy
          obtain ⟨r, hr⟩ := hy
          simp only [fixed, Finset.mem_filter, Finset.mem_univ, true_and]
          rw [← hr, ← map_pow]; congr 1; rw [← hcard_n]; exact FiniteField.pow_card r
        have himg_card : img.card = p ^ n := by
          simp only [img, Finset.card_image_of_injective _ hinj, Finset.card_univ, hcard_n]
        have hfixed_le : fixed.card ≤ p ^ n := by
          open Polynomial in
          set f := (X ^ (p ^ n) - X : Polynomial (GaloisField p (2 * n)))
          have hf_ne : f ≠ 0 :=
            FiniteField.X_pow_card_pow_sub_X_ne_zero (GaloisField p (2 * n)) hn hp.out.one_lt
          calc fixed.card
            ≤ f.roots.toFinset.card := Finset.card_le_card (by
                intro y hy
                simp only [fixed, Finset.mem_filter, Finset.mem_univ, true_and] at hy
                rw [Multiset.mem_toFinset, Polynomial.mem_roots hf_ne, Polynomial.IsRoot.def,
                  Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X]
                exact sub_eq_zero.mpr hy)
            _ ≤ Multiset.card f.roots := Multiset.toFinset_card_le _
            _ ≤ f.natDegree := Polynomial.card_roots' _
            _ = p ^ n := FiniteField.X_pow_card_pow_sub_X_natDegree_eq
                  (GaloisField p (2 * n)) hn hp.out.one_lt
        have : fixed = img :=
          (Finset.eq_of_subset_of_card_le himg_sub (himg_card ▸ hfixed_le)).symm
        rw [this] at hα_mem
        simp only [img, Finset.mem_image, Finset.mem_univ, true_and] at hα_mem
        exact hα_mem
      obtain ⟨a, ha⟩ := hα_in_range
      -- embed(α) is scalar since α is in the base field
      have hconj_scalar : GL2.IsScalar (p := p) (n := n) (GL2.fieldExtEmbed p n α) := by
        set b := Module.finBasisOfFinrankEq (R := GaloisField p n)
          (M := GaloisField p (2 * n)) (Etingof.finrank_galoisField_ext p n hn)
        have hval : (GL2.fieldExtEmbed p n α).val =
            Algebra.leftMulMatrix b (α : GaloisField p (2 * n)) := by
          unfold GL2.fieldExtEmbed; simp only [dif_neg hn]; rfl
        have hentry : ∀ i j : Fin 2,
            (GL2.fieldExtEmbed p n α).val i j = a * if j = i then 1 else 0 := by
          intro i j
          rw [show (GL2.fieldExtEmbed p n α).val i j =
              (Algebra.leftMulMatrix b (α : GaloisField p (2 * n))) i j from
            congr_fun (congr_fun hval i) j]
          rw [Algebra.leftMulMatrix_eq_repr_mul, ← ha,
            Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
            map_smul, Finsupp.smul_apply, smul_eq_mul, b.repr_self,
            Finsupp.single_apply]
        refine ⟨?_, ?_, ?_⟩
        · change (GL2.fieldExtEmbed p n α).val 0 1 = 0; rw [hentry]; simp
        · change (GL2.fieldExtEmbed p n α).val 1 0 = 0; rw [hentry]; simp
        · change (GL2.fieldExtEmbed p n α).val 0 0 = (GL2.fieldExtEmbed p n α).val 1 1
          rw [hentry 0 0, hentry 1 1]; simp
      -- x⁻¹gx is scalar, hence g is scalar (contradicts parabolic)
      have hconj_scalar' : GL2.IsScalar (p := p) (n := n) (x⁻¹ * g * x) := hα ▸ hconj_scalar
      exact hnotscalar (Etingof.conj_isScalar p n g x hconj_scalar')
  have hInd : ∑ x : GL2 p n,
      (if h : x⁻¹ * g * x ∈ Etingof.GL2.ellipticSubgroup p n
       then (nu ⟨x⁻¹ * g * x, h⟩).val
       else 0) = 0 := by
    apply Finset.sum_eq_zero; intro x _
    rw [dif_neg (hnoK x)]
  -- Step 3: charVα₁(g) = α(a) for some unit a
  set alpha := nu.comp (Etingof.GL2.scalarToElliptic p n)
  obtain ⟨a, ha⟩ := Etingof.charVα₁_parabolic p n alpha g hg
  -- Step 4: Combine
  refine ⟨a, ?_⟩
  change Etingof.GL2.charW₁ p n g * Etingof.GL2.charVα₁ p n alpha g -
    Etingof.GL2.charVα₁ p n alpha g -
    (Fintype.card ↥(Etingof.GL2.ellipticSubgroup p n) : ℂ)⁻¹ *
    ∑ x : GL2 p n,
      (if h : x⁻¹ * g * x ∈ Etingof.GL2.ellipticSubgroup p n
       then (nu ⟨x⁻¹ * g * x, h⟩).val else 0) =
    -↑(alpha a)
  rw [hW, hInd, ha]
  ring

/-- For an upper-triangular conjugate of a disc=0 element, the diagonal entries are equal. -/
lemma Etingof.upper_tri_conj_diag_eq
    (g x : GL2 p n)
    (hdisc : GL2.disc g = 0) (hut : (x⁻¹ * g * x).val 1 0 = 0) :
    (x⁻¹ * g * x).val 0 0 = (x⁻¹ * g * x).val 1 1 := by
  have hdisc_conj : GL2.disc (x⁻¹ * g * x : GL2 p n) = 0 := by
    rw [Etingof.disc_conj_eq p n g x]; exact hdisc
  simp only [GL2.disc_eq] at hdisc_conj
  rw [hut, mul_zero, add_zero] at hdisc_conj
  exact sub_eq_zero.mp (pow_eq_zero_iff (by omega : 2 ≠ 0) |>.mp hdisc_conj)

/-- For an upper-triangular conjugate of a disc=0 invertible element, the (0,0) entry is nonzero. -/
lemma Etingof.upper_tri_conj_diag_ne_zero
    (g x : GL2 p n)
    (hdisc : GL2.disc g = 0) (hut : (x⁻¹ * g * x).val 1 0 = 0) :
    (x⁻¹ * g * x).val 0 0 ≠ 0 := by
  intro h
  have heq := Etingof.upper_tri_conj_diag_eq p n g x hdisc hut
  -- det(x⁻¹gx) = det(g) by conjugation invariance
  have hval : (x⁻¹ * g * x).val = x.val⁻¹ * g.val * x.val := by simp [Units.val_mul]
  have hdet_eq : Matrix.det g.val = Matrix.det (x⁻¹ * g * x).val := by
    rw [show (x⁻¹ * g * x).val = x⁻¹.val * g.val * x.val from by simp [Units.val_mul]]
    exact (Matrix.det_units_conj' x g.val).symm
  -- det(x⁻¹gx) = M₀₀·M₁₁ - M₀₁·0 = 0·0 = 0
  have hdet_zero : Matrix.det (x⁻¹ * g * x).val = 0 := by
    rw [Matrix.det_fin_two]
    rw [hut, mul_zero, sub_zero, h, zero_mul]
  -- But g is a unit ⇒ det(g) ≠ 0
  have hg_unit : IsUnit g.val := g.isUnit
  rw [Matrix.isUnit_iff_isUnit_det] at hg_unit
  exact hg_unit.ne_zero (hdet_eq.trans hdet_zero)

/-- For an upper-triangular conjugate of a disc=0 element, M₀₀² = det(g). -/
lemma Etingof.upper_tri_conj_00_sq_eq_det
    (g x : GL2 p n)
    (hdisc : GL2.disc g = 0) (hut : (x⁻¹ * g * x).val 1 0 = 0) :
    (x⁻¹ * g * x).val 0 0 ^ 2 = Matrix.det g.val := by
  have heq := Etingof.upper_tri_conj_diag_eq p n g x hdisc hut
  -- det(x⁻¹gx) = M₀₀ · M₁₁ - M₀₁ · 0 = M₀₀ · M₀₀ = M₀₀²
  have hdet_conj : Matrix.det (x⁻¹ * g * x).val = (x⁻¹ * g * x).val 0 0 ^ 2 := by
    rw [Matrix.det_fin_two, hut, mul_zero, sub_zero, heq, sq]
  -- det(x⁻¹gx) = det(g) by conjugation invariance
  have hdet_eq : Matrix.det (x⁻¹ * g * x).val = Matrix.det g.val := by
    rw [show (x⁻¹ * g * x).val = x⁻¹.val * g.val * x.val from by simp [Units.val_mul]]
    exact Matrix.det_units_conj' x g.val
  rw [← hdet_conj, hdet_eq]

/-- For an upper-triangular conjugate of a disc=0 element, 2 · M₀₀ = tr(g).
In characteristic ≠ 2, this uniquely determines M₀₀ = tr(g)/2. -/
lemma Etingof.upper_tri_conj_00_trace
    (g x : GL2 p n)
    (hdisc : GL2.disc g = 0) (hut : (x⁻¹ * g * x).val 1 0 = 0) :
    2 * (x⁻¹ * g * x).val 0 0 = Matrix.trace g.val := by
  have heq := Etingof.upper_tri_conj_diag_eq p n g x hdisc hut
  have hval : (x⁻¹ * g * x).val = x⁻¹.val * g.val * x.val := by simp [Units.val_mul]
  -- trace(x⁻¹gx) = trace(g)
  have htr : (x⁻¹ * g * x).val 0 0 + (x⁻¹ * g * x).val 1 1 =
      g.val 0 0 + g.val 1 1 := by
    have := Matrix.trace_units_conj' x g.val
    simp only [Matrix.trace_fin_two] at this
    rw [hval]; exact this
  -- htr: M₀₀ + M₁₁ = g₀₀ + g₁₁, heq: M₀₀ = M₁₁
  -- Want: 2 * M₀₀ = g₀₀ + g₁₁
  simp only [Matrix.trace_fin_two]
  linear_combination htr + heq

/-- In characteristic ≠ 2, all upper-triangular conjugates of a disc=0 element
have the same (0,0) entry: tr(g)/2. -/
lemma Etingof.upper_tri_conj_00_unique
    (hp2 : p ≠ 2)
    (g x y : GL2 p n)
    (hdisc : GL2.disc g = 0)
    (hut_x : (x⁻¹ * g * x).val 1 0 = 0)
    (hut_y : (y⁻¹ * g * y).val 1 0 = 0) :
    (x⁻¹ * g * x).val 0 0 = (y⁻¹ * g * y).val 0 0 := by
  have h2 : (2 : GaloisField p n) ≠ 0 := by
    intro h
    -- GaloisField p n has characteristic p (inherited from ZMod p via algebra)
    have hchar2 : CharP (GaloisField p n) 2 :=
      (CharP.charP_iff_prime_eq_zero (by decide)).mpr h
    have hp_char : CharP (GaloisField p n) p := by
      haveI : Algebra (ZMod p) (GaloisField p n) := inferInstance
      exact charP_of_injective_algebraMap (algebraMap (ZMod p) (GaloisField p n)).injective p
    have := CharP.eq (GaloisField p n) hp_char hchar2
    exact hp2 this
  have hx := Etingof.upper_tri_conj_00_trace p n g x hdisc hut_x
  have hy := Etingof.upper_tri_conj_00_trace p n g y hdisc hut_y
  have : 2 * (x⁻¹ * g * x).val 0 0 = 2 * (y⁻¹ * g * y).val 0 0 := by
    rw [hx, hy]
  exact mul_left_cancel₀ h2 this

/-- A quadratic polynomial a*x² + b*x + c over a field of char ≠ 2 with a ≠ 0 and
discriminant b² - 4ac ≠ 0 being a square has exactly 2 roots. -/
lemma Etingof.quadratic_two_roots
    {F : Type*} [Field F] [Fintype F] [DecidableEq F] [NeZero (2 : F)]
    (a b c : F) (ha : a ≠ 0) (hdisc_ne : b ^ 2 - 4 * a * c ≠ 0)
    (hdisc_sq : IsSquare (b ^ 2 - 4 * a * c)) :
    (Finset.univ.filter fun x : F => a * x ^ 2 + b * x + c = 0).card = 2 := by
  -- Get the square root of the discriminant
  obtain ⟨s, hs⟩ := hdisc_sq
  -- hs : b ^ 2 - 4 * a * c = s * s (IsSquare gives s * s form)
  have hs' : discrim a b c = s * s := by
    simp only [discrim]; exact hs
  have hs_ne : s ≠ 0 := by
    intro h; rw [h, mul_zero] at hs; exact hdisc_ne hs
  -- The two roots
  set r₁ := (-b + s) / (2 * a)
  set r₂ := (-b - s) / (2 * a)
  -- They are distinct
  have h2a : (2 * a) ≠ (0 : F) := mul_ne_zero (NeZero.ne 2) ha
  have hr_ne : r₁ ≠ r₂ := by
    intro h
    have h1 : (-b + s) / (2 * a) = (-b - s) / (2 * a) := h
    rw [div_eq_div_iff h2a h2a] at h1
    -- h1 : (-b + s) * (2 * a) = (-b - s) * (2 * a)
    have h2 := mul_right_cancel₀ h2a h1
    -- h2 : -b + s = -b - s
    have : 2 * s = 0 := by linear_combination h2
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h (NeZero.ne 2)
    · exact hs_ne h
  -- The filter equals {r₁, r₂}
  have hfilter : Finset.univ.filter (fun x : F => a * x ^ 2 + b * x + c = 0) = {r₁, r₂} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    rw [show a * x ^ 2 + b * x + c = a * (x * x) + b * x + c by ring]
    rw [quadratic_eq_zero_iff ha hs']
  rw [hfilter, Finset.card_pair hr_ne]

/-- A linear equation a*x + b = 0 with a ≠ 0 has exactly 1 root. -/
lemma Etingof.linear_one_root
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (a b : F) (ha : a ≠ 0) :
    (Finset.univ.filter fun x : F => a * x + b = 0).card = 1 := by
  rw [Finset.card_eq_one]
  refine ⟨-(a⁻¹ * b), ?_⟩
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro h
    -- a*x + b = 0 → a*x = -b → x = -(a⁻¹ * b)
    have hax : a * x = -b := by linear_combination h
    have : x = -(a⁻¹ * b) := by
      have := mul_left_cancel₀ ha (show a * x = a * (-(a⁻¹ * b)) by
        rw [hax]; field_simp)
      exact this
    exact this
  · intro h
    subst h
    field_simp
    ring

lemma Etingof.charW₁_splitSemisimple
    [Fintype (GaloisField p n)] [DecidableEq (GaloisField p n)]
    (hp2 : p ≠ 2)
    (g : GL2 p n) (hg : GL2.IsSplitSemisimple (p := p) (n := n) g) :
    Etingof.GL2.charW₁ p n g = 1 := by
  haveI : NeZero (2 : GaloisField p n) := by
    constructor; intro h2; apply hp2
    have h2' : (Nat.cast 2 : GaloisField p n) = 0 := h2
    rw [CharP.cast_eq_zero_iff (GaloisField p n) p 2] at h2'
    exact Nat.le_antisymm (Nat.le_of_dvd (by omega) h2') hp.out.two_le
  simp only [Etingof.GL2.charW₁]
  set M := (g : Matrix (Fin 2) (Fin 2) (GaloisField p n))
  obtain ⟨hdisc_ne, hdisc_sq⟩ := hg
  simp only [GL2.disc_eq] at hdisc_ne hdisc_sq
  by_cases h01 : M 0 1 = 0
  · -- Case M₀₁ = 0: infinity is fixed, affine equation is linear
    have h00_ne_11 : M 0 0 - M 1 1 ≠ 0 := by
      intro h; apply hdisc_ne
      show (M 0 0 - M 1 1) ^ 2 + 4 * M 0 1 * M 1 0 = 0
      rw [h01, h]; ring
    have hfilt : (Finset.univ.filter fun t : GaloisField p n =>
        M 0 1 * t ^ 2 + (M 0 0 - M 1 1) * t - M 1 0 = 0) =
        (Finset.univ.filter fun t : GaloisField p n =>
        (M 0 0 - M 1 1) * t + (-(M 1 0)) = 0) := by
      congr 1; ext t; simp only [h01, zero_mul, zero_add, sub_eq_add_neg]
    rw [hfilt, Etingof.linear_one_root _ _ h00_ne_11]
    simp only [h01, ite_true]
    push_cast; ring
  · -- Case M₀₁ ≠ 0: infinity is not fixed, quadratic has 2 roots
    have hfilt : (Finset.univ.filter fun t : GaloisField p n =>
        M 0 1 * t ^ 2 + (M 0 0 - M 1 1) * t - M 1 0 = 0) =
        (Finset.univ.filter fun t : GaloisField p n =>
        M 0 1 * t ^ 2 + (M 0 0 - M 1 1) * t + (-(M 1 0)) = 0) := by
      congr 1; ext t; show _ - _ = 0 ↔ _ + (-_) = 0; rw [sub_eq_add_neg]
    have hconv : (M 0 0 - M 1 1) ^ 2 - 4 * M 0 1 * (-(M 1 0)) =
        (M 0 0 - M 1 1) ^ 2 + 4 * (M 0 1) * (M 1 0) := by ring
    have hdisc_ne' : (M 0 0 - M 1 1) ^ 2 - 4 * M 0 1 * (-(M 1 0)) ≠ 0 := by
      rw [hconv]; exact hdisc_ne
    have hdisc_sq' : IsSquare ((M 0 0 - M 1 1) ^ 2 - 4 * M 0 1 * (-(M 1 0))) := by
      rw [hconv]; exact hdisc_sq
    rw [hfilt, Etingof.quadratic_two_roots _ _ _ h01 hdisc_ne' hdisc_sq']
    simp only [h01, ite_false, Nat.add_zero]
    push_cast; ring

/-- A quadratic polynomial a*x² + b*x + c with a ≠ 0 and non-square discriminant
has no roots. If it had a root r, then a*x² + b*x + c = a*(x-r)*(x-s) for some s,
so disc = a²*(r-s)², which is a square — contradiction. -/
lemma Etingof.quadratic_no_roots
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (a b c : F) (_ha : a ≠ 0) (hdisc : ¬IsSquare (b ^ 2 - 4 * a * c)) :
    (Finset.univ.filter fun x : F => a * x ^ 2 + b * x + c = 0).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro x _ hroot
  exact hdisc ⟨2 * a * x + b, by linear_combination -4 * a * hroot⟩

/-- On elliptic elements, charW₁ = -1 (no fixed points on P¹).
An elliptic element has non-square discriminant, so:
- M₀₁ ≠ 0 (otherwise disc = (M₀₀-M₁₁)², always a square)
- The fixed-point quadratic M₀₁t² + (M₀₀-M₁₁)t - M₁₀ = 0 has discriminant = disc(g),
  which is non-square, so it has no roots (by `quadratic_no_roots`)
- The point at infinity [0:1] is not fixed (since M₀₁ ≠ 0)
- Total fixed points = 0, so charW₁ = 0 - 1 = -1. -/
lemma Etingof.charW₁_elliptic
    [Fintype (GaloisField p n)] [DecidableEq (GaloisField p n)]
    (g : GL2 p n) (hg : GL2.IsElliptic (p := p) (n := n) g) :
    Etingof.GL2.charW₁ p n g = -1 := by
  simp only [Etingof.GL2.charW₁]
  set M := (g : Matrix (Fin 2) (Fin 2) (GaloisField p n))
  -- M₀₁ ≠ 0 for elliptic elements (otherwise disc = (M₀₀-M₁₁)², a square)
  have h01 : M 0 1 ≠ 0 := by
    intro h
    apply hg  -- hg : ¬IsSquare (GL2.disc g)
    have hdisc : GL2.disc g = (M 0 0 - M 1 1) ^ 2 := by
      simp only [GL2.disc_eq, show g.val 0 1 = M 0 1 from rfl, h]; ring
    rw [hdisc]; exact IsSquare.sq _
  -- The fixed-point quadratic has disc = GL2.disc(g), which is non-square
  have hfilt : (Finset.univ.filter fun t : GaloisField p n =>
      M 0 1 * t ^ 2 + (M 0 0 - M 1 1) * t - M 1 0 = 0) =
      (Finset.univ.filter fun t : GaloisField p n =>
      M 0 1 * t ^ 2 + (M 0 0 - M 1 1) * t + (-(M 1 0)) = 0) := by
    congr 1; ext t; show _ - _ = 0 ↔ _ + (-_) = 0; rw [sub_eq_add_neg]
  have hconv : (M 0 0 - M 1 1) ^ 2 - 4 * M 0 1 * (-(M 1 0)) =
      (M 0 0 - M 1 1) ^ 2 + 4 * (M 0 1) * (M 1 0) := by ring
  have hdisc : ¬IsSquare ((M 0 0 - M 1 1) ^ 2 - 4 * M 0 1 * (-(M 1 0))) := by
    rw [hconv]; exact hg
  rw [hfilt, Etingof.quadratic_no_roots _ _ _ h01 hdisc]
  simp only [h01, ite_false, Nat.add_zero, Nat.cast_zero, zero_sub]

/-- If d ∈ 𝔽_q has a square root s in 𝔽_{q²} with s^q = -s and s ≠ 0 (char ≠ 2),
then d is not a square in 𝔽_q. -/
lemma Etingof.not_isSquare_of_antisymmetric_root (hp2 : p ≠ 2) (hn : n ≠ 0)
    (d : GaloisField p n) (s : GaloisField p (2 * n))
    (hd : algebraMap (GaloisField p n) (GaloisField p (2 * n)) d = s ^ 2)
    (hs_ne : s ≠ 0)
    (hs_frob : s ^ (p ^ n : ℕ) = -s) :
    ¬IsSquare d := by
  letI := Etingof.algebraGaloisFieldExt p n
  intro ⟨r, hr⟩
  -- If d = r * r in 𝔽_q, then algebraMap(r * r) = s² in 𝔽_{q²}
  have hrs : (algebraMap (GaloisField p n) (GaloisField p (2 * n)) r) ^ 2 = s ^ 2 := by
    rw [sq, ← map_mul, ← hr]; exact hd
  -- So (alg_map(r))² = s², meaning (alg_map(r) - s)(alg_map(r) + s) = 0
  set r' := algebraMap (GaloisField p n) (GaloisField p (2 * n)) r
  have h_prod : (r' - s) * (r' + s) = 0 := by
    have h1 : r' ^ 2 = s ^ 2 := hrs
    have : (r' - s) * (r' + s) = r' ^ 2 - s ^ 2 := by ring
    rw [this, h1, sub_self]
  -- Key fact: algebraMap(r)^{p^n} = algebraMap(r) since r ∈ 𝔽_{p^n}
  haveI : Fintype (GaloisField p n) := Fintype.ofFinite _
  have hr_frob : r' ^ (p ^ n : ℕ) = r' := by
    show (algebraMap (GaloisField p n) (GaloisField p (2 * n)) r) ^ (p ^ n : ℕ) = _
    rw [← map_pow]
    congr 1
    have hcard : Fintype.card (GaloisField p n) = p ^ n := by
      rw [← Nat.card_eq_fintype_card, GaloisField.card p n hn]
    rw [← hcard]
    exact FiniteField.pow_card r
  -- NeZero (2 : GaloisField p (2*n)) since char = p ≠ 2
  have h2ne : (2 : GaloisField p (2 * n)) ≠ 0 := by
    intro h2; apply hp2
    have h2' : (Nat.cast 2 : GaloisField p (2 * n)) = 0 := h2
    rw [CharP.cast_eq_zero_iff (GaloisField p (2 * n)) p 2] at h2'
    exact Nat.le_antisymm (Nat.le_of_dvd (by omega) h2') hp.out.two_le
  -- p^n is odd since p is an odd prime
  have hodd : Odd (p ^ n) := by
    exact Odd.pow (Nat.Prime.odd_of_ne_two hp.out hp2)
  rcases mul_eq_zero.mp h_prod with h | h
  · -- r' = s (from r' - s = 0)
    have hs_eq : s = r' := (sub_eq_zero.mp h).symm
    -- s^{p^n} = r'^{p^n} = r' = s, but also s^{p^n} = -s
    have hcontra : s = -s := by
      calc s = r' := hs_eq
        _ = r' ^ (p ^ n : ℕ) := hr_frob.symm
        _ = s ^ (p ^ n : ℕ) := by rw [hs_eq]
        _ = -s := hs_frob
    -- So s + s = 0, i.e., 2 * s = 0
    have h2s : (2 : GaloisField p (2 * n)) * s = 0 := by
      have : s - (-s) = 0 := sub_eq_zero.mpr hcontra
      have : 2 * s = 0 := by linear_combination this
      exact this
    exact absurd ((mul_eq_zero.mp h2s).resolve_left h2ne) hs_ne
  · -- r' + s = 0, so s = -r'
    have hs_eq : s = -r' := by
      have : r' = -s := add_eq_zero_iff_eq_neg.mp h
      rw [this]; ring
    have hr'_ne : r' ≠ 0 := by
      intro h0; rw [hs_eq, h0, neg_zero] at hs_ne; exact hs_ne rfl
    -- s^{p^n} = (-r')^{p^n} = -(r'^{p^n}) = -r' (since p^n is odd)
    have h1 : s ^ (p ^ n : ℕ) = -(r' ^ (p ^ n : ℕ)) := by
      rw [hs_eq]; exact hodd.neg_pow r'
    -- But s^{p^n} = -s = -(-r') = r'
    have h2 : s ^ (p ^ n : ℕ) = r' := by rw [hs_frob, hs_eq, neg_neg]
    -- So -r' = r'
    have h3 : -r' = r' := by
      have : -(r' ^ (p ^ n : ℕ)) = r' := by rw [← h1, h2]
      rwa [hr_frob] at this
    -- So 2r' = 0
    have h4 : (2 : GaloisField p (2 * n)) * r' = 0 := by
      have : r' - (-r') = 0 := sub_eq_zero.mpr h3.symm
      linear_combination this
    exact absurd ((mul_eq_zero.mp h4).resolve_left h2ne) hr'_ne

/-- Frobenius s^q = -s for s = α - α^q. -/
lemma Etingof.frob_diff_neg (hn : n ≠ 0) (α : GaloisField p (2 * n)) :
    (α - α ^ (p ^ n : ℕ)) ^ (p ^ n : ℕ) =
    -(α - α ^ (p ^ n : ℕ)) := by
  rw [sub_pow_char_pow (p := p)]
  -- Need α^(q²) = α, i.e. α^(p^(2n)) = α
  haveI : Fintype (GaloisField p (2 * n)) := Fintype.ofFinite _
  have hcard2 : Fintype.card (GaloisField p (2 * n)) = p ^ (2 * n) := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card p (2 * n) (Nat.mul_ne_zero two_ne_zero hn)]
  have hfrob2 : α ^ (p ^ (2 * n) : ℕ) = α := by
    rw [← hcard2]; exact FiniteField.pow_card α
  -- (α^q)^q = α^(q²) = α^(p^(2n)) = α
  have : (α ^ (p ^ n : ℕ)) ^ (p ^ n : ℕ) = α := by
    rw [← pow_mul, ← Nat.pow_add, show n + n = 2 * n from by omega]
    exact hfrob2
  rw [this]; ring

lemma Etingof.ellipticSubgroup_disc (hp2 : p ≠ 2) (k : GL2 p n)
    (hk : k ∈ Etingof.GL2.ellipticSubgroup p n) :
    GL2.disc k = 0 ∨ ¬IsSquare (GL2.disc k) := by
  obtain ⟨α, rfl⟩ := hk
  by_cases hn : n = 0
  · left; simp [GL2.disc_eq, GL2.fieldExtEmbed, hn]
  · letI := Etingof.algebraGaloisFieldExt p n
    set d := GL2.disc (Etingof.GL2.fieldExtEmbed p n α)
    set s := (α : GaloisField p (2 * n)) - (α : GaloisField p (2 * n)) ^ (p ^ n : ℕ)
    have hd : algebraMap (GaloisField p n) (GaloisField p (2 * n)) d = s ^ 2 :=
      Etingof.algebraMap_disc_fieldExtEmbed p n hn α
    by_cases hs : s = 0
    · -- α^q = α, disc = 0
      left
      have hinj : Function.Injective
          (algebraMap (GaloisField p n) (GaloisField p (2 * n))) :=
        (algebraMap (GaloisField p n) (GaloisField p (2 * n))).injective
      exact hinj (by rw [hd, hs, sq, mul_zero, map_zero])
    · -- α^q ≠ α, disc is not a square
      right
      have hs_frob : s ^ (p ^ n : ℕ) = -s := Etingof.frob_diff_neg p n hn ↑α
      exact Etingof.not_isSquare_of_antisymmetric_root p n hp2 hn d s hd hs hs_frob

/-- For parabolic g, no conjugate lies in the elliptic subgroup K. -/
lemma Etingof.parabolic_conj_not_in_ellipticSubgroup
    (g : GL2 p n)
    (hg : GL2.IsParabolic (p := p) (n := n) g) :
    ∀ x : GL2 p n, ¬(x⁻¹ * g * x ∈ Etingof.GL2.ellipticSubgroup p n) := by
  intro x hcontra
  obtain ⟨hdisc_zero, hnotscalar⟩ := hg
  have hdisc_eq : GL2.disc (x⁻¹ * g * x : GL2 p n) = GL2.disc g :=
    Etingof.disc_conj_eq p n g x
  by_cases hn : n = 0
  · -- n = 0: K is trivial, range = {1}
    obtain ⟨α, hα⟩ := hcontra
    have h1 : GL2.fieldExtEmbed p n α = 1 := by
      unfold GL2.fieldExtEmbed; simp [hn]
    have hone : x⁻¹ * g * x = 1 := hα ▸ h1
    have hg1 : g = 1 := by
      have key : x * (x⁻¹ * g * x) * x⁻¹ = g := by group
      rw [hone] at key
      simpa using key.symm
    exact hnotscalar (hg1 ▸ ⟨by simp [Units.val_one],
      by simp [Units.val_one],
      by simp [Units.val_one]⟩)
  · -- n ≥ 1: disc(x⁻¹gx) = disc(g) = 0, and K ∩ {disc=0} ⊂ {scalar}
    obtain ⟨α, hα⟩ := hcontra
    letI := Etingof.algebraGaloisFieldExt p n
    have hconj_disc : GL2.disc (GL2.fieldExtEmbed p n α) = 0 := by
      rw [hα, hdisc_eq]; exact hdisc_zero
    -- algebraMap(disc(embed(α))) = (α - α^q)²
    set s := (α : GaloisField p (2 * n)) - (α : GaloisField p (2 * n)) ^ (p ^ n : ℕ)
    have hd := Etingof.algebraMap_disc_fieldExtEmbed p n hn α
    have hinj : Function.Injective
        (algebraMap (GaloisField p n) (GaloisField p (2 * n))) :=
      (algebraMap (GaloisField p n) (GaloisField p (2 * n))).injective
    have hs : s = 0 := by
      have : s ^ 2 = 0 := by rw [← hd, hconj_disc, map_zero]
      exact pow_eq_zero_iff (by omega : 2 ≠ 0) |>.mp this
    -- From hs: α^(p^n) = α, so α is in the base field GaloisField p n
    have hα_frob : (α : GaloisField p (2 * n)) ^ (p ^ n : ℕ) = (α : GaloisField p (2 * n)) := by
      exact (sub_eq_zero.mp hs).symm
    -- Extract a base field element mapping to α
    -- The elements x with x^(p^n) = x are exactly the roots of X^(p^n) - X,
    -- and algebraMap maps GaloisField p n bijectively onto these roots.
    -- We use: algebraMap is injective + both sides have p^n elements + image ⊆ fixed set
    have hα_in_range : (α : GaloisField p (2 * n)) ∈ Set.range
        (algebraMap (GaloisField p n) (GaloisField p (2 * n))) := by
      haveI : Fintype (GaloisField p n) := Fintype.ofFinite _
      haveI : Fintype (GaloisField p (2 * n)) := Fintype.ofFinite _
      haveI : DecidableEq (GaloisField p n) := Classical.typeDecidableEq _
      haveI : DecidableEq (GaloisField p (2 * n)) := Classical.typeDecidableEq _
      -- Define the set of elements fixed by Frobenius
      set fixed := Finset.univ.filter
        (fun x : GaloisField p (2 * n) => x ^ (p ^ n : ℕ) = x)
      set img := Finset.univ.image
        (algebraMap (GaloisField p n) (GaloisField p (2 * n)))
      have hcard_n : Fintype.card (GaloisField p n) = p ^ n := by
        rw [← Nat.card_eq_fintype_card, GaloisField.card p n hn]
      -- α ∈ fixed
      have hα_mem : (α : GaloisField p (2 * n)) ∈ fixed := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, fixed]
        exact hα_frob
      -- img ⊆ fixed
      have himg_sub : img ⊆ fixed := by
        intro x hx
        simp only [Finset.mem_image, Finset.mem_univ, true_and, img] at hx
        obtain ⟨r, hr⟩ := hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, fixed]
        rw [← hr, ← map_pow]; congr 1; rw [← hcard_n]; exact FiniteField.pow_card r
      -- |img| = p^n
      have himg_card : img.card = p ^ n := by
        simp only [img, Finset.card_image_of_injective _ hinj, Finset.card_univ, hcard_n]
      -- |fixed| ≤ p^n: elements of fixed are roots of X^(p^n) - X
      have hfixed_le : fixed.card ≤ p ^ n := by
        -- fixed ⊆ (X^(p^n) - X).roots.toFinset, and roots.card ≤ natDegree = p^n
        open Polynomial in
        set f := (X ^ (p ^ n) - X : Polynomial (GaloisField p (2 * n)))
        have hf_ne : f ≠ 0 :=
          FiniteField.X_pow_card_pow_sub_X_ne_zero (GaloisField p (2 * n)) hn hp.out.one_lt
        have hfixed_sub_roots : fixed ⊆ f.roots.toFinset := by
          intro x hx
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, fixed] at hx
          rw [Multiset.mem_toFinset, Polynomial.mem_roots hf_ne, Polynomial.IsRoot.def,
            Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X]
          exact sub_eq_zero.mpr hx
        calc fixed.card ≤ f.roots.toFinset.card := Finset.card_le_card hfixed_sub_roots
          _ ≤ Multiset.card f.roots := Multiset.toFinset_card_le _
          _ ≤ f.natDegree := Polynomial.card_roots' _
          _ = p ^ n := by
              simp only [f]
              exact FiniteField.X_pow_card_pow_sub_X_natDegree_eq
                (GaloisField p (2 * n)) hn hp.out.one_lt
      -- By sandwich: img ⊆ fixed and |img| = |fixed| = p^n, so img = fixed
      have : fixed = img :=
        (Finset.eq_of_subset_of_card_le himg_sub (himg_card ▸ hfixed_le)).symm
      -- α ∈ fixed = img, so α is in the image
      rw [this] at hα_mem
      simp only [Finset.mem_image, Finset.mem_univ, true_and, img] at hα_mem
      exact hα_mem
    obtain ⟨a, ha⟩ := hα_in_range
    -- Now fieldExtEmbed(α) = fieldExtEmbed(Units.map algebraMap (Units.mk0 a _))
    -- which is a scalar matrix by the same argument as scalar_eq_fieldExtEmbed
    have hconj_scalar : GL2.IsScalar (p := p) (n := n) (GL2.fieldExtEmbed p n α) := by
      set b := Module.finBasisOfFinrankEq (R := GaloisField p n)
        (M := GaloisField p (2 * n)) (Etingof.finrank_galoisField_ext p n hn)
      have hval : (GL2.fieldExtEmbed p n α).val =
          Algebra.leftMulMatrix b (α : GaloisField p (2 * n)) := by
        unfold GL2.fieldExtEmbed; simp only [dif_neg hn]; rfl
      have hentry : ∀ i j : Fin 2,
          (GL2.fieldExtEmbed p n α).val i j =
            a * if j = i then 1 else 0 := by
        intro i j
        change (GL2.fieldExtEmbed p n α).val i j = _
        rw [show (GL2.fieldExtEmbed p n α).val i j =
            (Algebra.leftMulMatrix b (α : GaloisField p (2 * n))) i j from
          congr_fun (congr_fun hval i) j]
        rw [Algebra.leftMulMatrix_eq_repr_mul, ← ha,
          Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
          map_smul, Finsupp.smul_apply, smul_eq_mul, b.repr_self,
          Finsupp.single_apply]
      refine ⟨?_, ?_, ?_⟩
      · change (GL2.fieldExtEmbed p n α).val 0 1 = 0
        rw [hentry]; simp
      · change (GL2.fieldExtEmbed p n α).val 1 0 = 0
        rw [hentry]; simp
      · change (GL2.fieldExtEmbed p n α).val 0 0 = (GL2.fieldExtEmbed p n α).val 1 1
        rw [hentry 0 0, hentry 1 1]; simp
    have hconj_scalar' : GL2.IsScalar (p := p) (n := n) (x⁻¹ * g * x) := hα ▸ hconj_scalar
    exact hnotscalar (Etingof.conj_isScalar p n g x hconj_scalar')

lemma Etingof.normSq_complementaryChar_parabolic
    [Fintype (GaloisField p n)] [DecidableEq (GaloisField p n)]
    [Fintype (GL2 p n)]
    (hp2 : p ≠ 2)
    (nu : (Etingof.GL2.ellipticSubgroup p n) →* ℂˣ)
    (g : GL2 p n) (hg : GL2.IsParabolic (p := p) (n := n) g) :
    Etingof.GL2.complementarySeriesChar p n nu g *
    starRingEnd ℂ (Etingof.GL2.complementarySeriesChar p n nu g) = 1 := by
  obtain ⟨a, ha⟩ := Etingof.complementaryChar_parabolic_val p n nu g hg
  set alpha := nu.comp (Etingof.GL2.scalarToElliptic p n)
  rw [ha]
  simp only [map_neg, neg_mul, mul_neg, neg_neg]
  exact Etingof.normSq_monoidHom_val_eq_one alpha a

/-- On elliptic elements, charVα₁ = 0 (no conjugate is upper triangular).
If x⁻¹gx were upper triangular, its (1,0) entry would be 0, making
disc(x⁻¹gx) = (M₀₀-M₁₁)², a perfect square. But disc(x⁻¹gx) = disc(g)
(conjugation invariant) and disc(g) is non-square (g is elliptic). -/
lemma Etingof.charVα₁_elliptic
    [Fintype (GaloisField p n)] [DecidableEq (GaloisField p n)]
    [Fintype (GL2 p n)]
    (alpha : (GaloisField p n)ˣ →* ℂˣ)
    (g : GL2 p n) (hg : GL2.IsElliptic (p := p) (n := n) g) :
    Etingof.GL2.charVα₁ p n alpha g = 0 := by
  unfold Etingof.GL2.charVα₁
  simp only [mul_eq_zero]
  right
  apply Finset.sum_eq_zero
  intro x _
  -- No conjugate of an elliptic element is upper triangular
  set conj := (x⁻¹ * g * x : GL2 p n)
  set Mc := (conj : Matrix (Fin 2) (Fin 2) (GaloisField p n))
  have hM10 : ¬(Mc 1 0 = 0) := by
    intro h10
    apply hg
    -- disc(x⁻¹gx) = (M₀₀-M₁₁)² when M₁₀ = 0
    rw [← Etingof.disc_conj_eq p n g x]
    have hdisc_sq : GL2.disc conj = (Mc 0 0 - Mc 1 1) ^ 2 := by
      simp only [GL2.disc_eq]
      change (Mc 0 0 - Mc 1 1) ^ 2 + 4 * Mc 0 1 * Mc 1 0 = _
      rw [h10]; ring
    rw [hdisc_sq]; exact IsSquare.sq _
  simp only [hM10, ite_false]

lemma Etingof.induced_char_splitSemisimple_eq_zero
    [Fintype (GaloisField p n)] [DecidableEq (GaloisField p n)]
    [Fintype (GL2 p n)]
    (hp2 : p ≠ 2)
    (nu : (Etingof.GL2.ellipticSubgroup p n) →* ℂˣ)
    (g : GL2 p n) (hg : GL2.IsSplitSemisimple (p := p) (n := n) g) :
    ∀ x : GL2 p n, ¬(x⁻¹ * g * x ∈ Etingof.GL2.ellipticSubgroup p n) := by
  intro x hcontra
  have hdisc_eq : GL2.disc (x⁻¹ * g * x : GL2 p n) = GL2.disc g :=
    Etingof.disc_conj_eq p n g x
  have hK := Etingof.ellipticSubgroup_disc p n hp2 (x⁻¹ * g * x) hcontra
  -- g is split semisimple: disc ≠ 0 and IsSquare
  obtain ⟨hdisc_ne, hdisc_sq⟩ := hg
  rw [hdisc_eq] at hK
  rcases hK with hzero | hnsq
  · exact hdisc_ne hzero
  · exact hnsq hdisc_sq

open Classical in
/-- On split semisimple (hyperbolic) matrices, χ = 0.
Proof: χ = (charW₁ - 1) · charVα₁ - induced_term.
For split semisimple g, charW₁ = 1 (2 fixed points on P¹) and the
induced character sum is 0 (no conjugate lies in K). -/
lemma Etingof.complementaryChar_splitSemisimple_eq_zero
    [Fintype (GaloisField p n)] [DecidableEq (GaloisField p n)]
    [Fintype (GL2 p n)]
    (hp2 : p ≠ 2)
    (nu : (Etingof.GL2.ellipticSubgroup p n) →* ℂˣ)
    (g : GL2 p n) (hg : GL2.IsSplitSemisimple (p := p) (n := n) g) :
    Etingof.GL2.complementarySeriesChar p n nu g = 0 := by
  unfold Etingof.GL2.complementarySeriesChar
  have h1 : Etingof.GL2.charW₁ p n g = 1 := Etingof.charW₁_splitSemisimple p n hp2 g hg
  have h2 : ∀ x : GL2 p n, ¬(x⁻¹ * g * x ∈ Etingof.GL2.ellipticSubgroup p n) :=
    Etingof.induced_char_splitSemisimple_eq_zero p n hp2 nu g hg
  -- The induced character sum is zero because each term is zero
  have h3 : ∑ x : GL2 p n,
      (if h : x⁻¹ * g * x ∈ Etingof.GL2.ellipticSubgroup p n
       then (nu ⟨x⁻¹ * g * x, h⟩).val
       else 0) = 0 := by
    apply Finset.sum_eq_zero; intro x _
    rw [dif_neg (h2 x)]
  rw [h1, h3, mul_zero, one_mul, sub_self, zero_sub, neg_eq_zero]

end CharacterValues
