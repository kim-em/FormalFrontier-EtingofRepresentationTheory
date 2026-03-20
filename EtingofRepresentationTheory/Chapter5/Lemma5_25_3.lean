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
private lemma Etingof.dvd_X_pow_sub_X :
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
private lemma Etingof.splits_X_pow_sub_X :
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
private noncomputable def Etingof.galoisFieldAlgHom :
    GaloisField p n →ₐ[ZMod p] GaloisField p (2 * n) :=
  IsSplittingField.lift (GaloisField p n) (X ^ p ^ n - X)
    (Etingof.splits_X_pow_sub_X p n)

/-- Algebra instance for GaloisField p (2*n) over GaloisField p n. -/
private noncomputable instance Etingof.algebraGaloisFieldExt :
    Algebra (GaloisField p n) (GaloisField p (2 * n)) :=
  (Etingof.galoisFieldAlgHom p n).toRingHom.toAlgebra

/-- The scalar tower ZMod p → GaloisField p n → GaloisField p (2*n). -/
private noncomputable instance Etingof.scalarTowerGaloisField :
    IsScalarTower (ZMod p) (GaloisField p n) (GaloisField p (2 * n)) :=
  IsScalarTower.of_algebraMap_eq fun r => by
    change (algebraMap (ZMod p) (GaloisField p (2 * n))) r =
      (Etingof.galoisFieldAlgHom p n).toRingHom
        ((algebraMap (ZMod p) (GaloisField p n)) r)
    exact ((Etingof.galoisFieldAlgHom p n).commutes r).symm

/-- GaloisField p (2*n) is finite-dimensional over GaloisField p n. -/
private noncomputable instance Etingof.finiteDimensionalGaloisFieldExt :
    FiniteDimensional (GaloisField p n) (GaloisField p (2 * n)) := by
  haveI : FiniteDimensional (ZMod p) (GaloisField p (2 * n)) := inferInstance
  exact FiniteDimensional.right (ZMod p) (GaloisField p n) (GaloisField p (2 * n))

/-- The degree of GaloisField p (2*n) over GaloisField p n is 2 (when n > 0). -/
private lemma Etingof.finrank_galoisField_ext (hn : n ≠ 0) :
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
private noncomputable def Etingof.GL2.fieldExtEmbed :
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
private noncomputable def Etingof.GL2.scalarToElliptic :
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
private noncomputable def Etingof.GL2.charW₁
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
private noncomputable def Etingof.GL2.charVα₁
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
private lemma Etingof.scalar_conj_eq_self
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
private lemma Etingof.units_char_normSq {G : Type*} [Group G] [Fintype G]
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
private lemma Etingof.charW₁_scalar
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
private lemma Etingof.scalar_diag_ne_zero
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
private lemma Etingof.charVα₁_scalar
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
private lemma Etingof.scalar_eq_fieldExtEmbed
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
private lemma Etingof.scalar_mem_ellipticSubgroup
    (hn : n ≠ 0)
    (g : GL2 p n) (hg : GL2.IsScalar (p := p) (n := n) g)
    (h_ne : g.val 0 0 ≠ 0) :
    g ∈ Etingof.GL2.ellipticSubgroup p n := by
  change g ∈ (Etingof.GL2.fieldExtEmbed p n).range
  exact ⟨_, (Etingof.scalar_eq_fieldExtEmbed p n hn g hg h_ne).symm⟩

/-- For scalar g, nu(⟨g, _⟩) equals alpha(Units.mk0 (g.val 0 0) _). -/
private lemma Etingof.nu_scalar_eq_alpha
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
private lemma Etingof.scalar_coeff_eq (q : ℂ) (hq : q ≠ 0) (hq1 : q - 1 ≠ 0)
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
private lemma Etingof.normSq_complementaryChar_scalar
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
private lemma Etingof.quadratic_one_root_zero_disc
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
      sorry
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
private lemma Etingof.charW₁_parabolic
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
private lemma Etingof.normSq_monoidHom_val_eq_one
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

/-- On parabolic g, the complementary series character equals -α(eigenvalue).
This follows from charW₁ = 0 and Ind = 0, giving χ = -charVα₁.
For parabolic g, charVα₁(g) = α(a) where a is the repeated eigenvalue. -/
private lemma Etingof.complementaryChar_parabolic_val
    [Fintype (GaloisField p n)] [DecidableEq (GaloisField p n)]
    [Fintype (GL2 p n)]
    (nu : (Etingof.GL2.ellipticSubgroup p n) →* ℂˣ)
    (g : GL2 p n) (hg : GL2.IsParabolic (p := p) (n := n) g) :
    ∃ a : (GaloisField p n)ˣ,
      Etingof.GL2.complementarySeriesChar p n nu g =
      -((nu.comp (Etingof.GL2.scalarToElliptic p n) : (GaloisField p n)ˣ →* ℂˣ) a : ℂ) := by
  sorry

private lemma Etingof.normSq_complementaryChar_parabolic
    [Fintype (GaloisField p n)] [DecidableEq (GaloisField p n)]
    [Fintype (GL2 p n)]
    (nu : (Etingof.GL2.ellipticSubgroup p n) →* ℂˣ)
    (g : GL2 p n) (hg : GL2.IsParabolic (p := p) (n := n) g) :
    Etingof.GL2.complementarySeriesChar p n nu g *
    starRingEnd ℂ (Etingof.GL2.complementarySeriesChar p n nu g) = 1 := by
  obtain ⟨a, ha⟩ := Etingof.complementaryChar_parabolic_val p n nu g hg
  set alpha := nu.comp (Etingof.GL2.scalarToElliptic p n)
  rw [ha]
  simp only [map_neg, neg_mul, mul_neg, neg_neg]
  exact Etingof.normSq_monoidHom_val_eq_one alpha a

/-- A quadratic polynomial a*x² + b*x + c over a field of char ≠ 2 with a ≠ 0 and
discriminant b² - 4ac ≠ 0 being a square has exactly 2 roots. -/
private lemma Etingof.quadratic_two_roots
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
private lemma Etingof.linear_one_root
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

private lemma Etingof.charW₁_splitSemisimple
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
private lemma Etingof.quadratic_no_roots
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
private lemma Etingof.charW₁_elliptic
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

/-- The discriminant is a conjugation invariant: disc(x⁻¹gx) = disc(g).
This follows from disc = tr² - 4·det and both tr and det being similarity invariants. -/
private lemma Etingof.disc_eq_tr_det (M : Matrix (Fin 2) (Fin 2) (GaloisField p n)) :
    (M 0 0 - M 1 1) ^ 2 + 4 * M 0 1 * M 1 0 =
    (Matrix.trace M) ^ 2 - 4 * Matrix.det M := by
  simp [Matrix.trace_fin_two, Matrix.det_fin_two]; ring

private lemma Etingof.disc_conj_eq (g x : GL2 p n) :
    GL2.disc (x⁻¹ * g * x : GL2 p n) = GL2.disc g := by
  -- disc = tr² - 4·det for 2×2 matrices
  simp only [GL2.disc_eq]
  set h := x⁻¹ * g * x
  set G := (g : Matrix (Fin 2) (Fin 2) (GaloisField p n))
  set H := (h : Matrix (Fin 2) (Fin 2) (GaloisField p n))
  -- Express disc in terms of trace and det
  rw [Etingof.disc_eq_tr_det (M := H), Etingof.disc_eq_tr_det (M := G)]
  -- trace(h) = trace(g)  and  det(h) = det(g)
  have htr : Matrix.trace H = Matrix.trace G := by
    change Matrix.trace (x⁻¹ * g * x).val = Matrix.trace g.val
    rw [show (x⁻¹ * g * x).val = x⁻¹.val * g.val * x.val from by
      simp [Units.val_mul]]
    exact Matrix.trace_units_conj' x g.val
  have hdet : Matrix.det H = Matrix.det G := by
    change Matrix.det (x⁻¹ * g * x).val = Matrix.det g.val
    rw [show (x⁻¹ * g * x).val = x⁻¹.val * g.val * x.val from by
      simp [Units.val_mul]]
    exact Matrix.det_units_conj' x g.val
  rw [htr, hdet]

/-- If d ∈ 𝔽_q has a square root s in 𝔽_{q²} with s^q = -s and s ≠ 0 (char ≠ 2),
then d is not a square in 𝔽_q. -/
private lemma Etingof.not_isSquare_of_antisymmetric_root (hp2 : p ≠ 2) (hn : n ≠ 0)
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

/-- disc(embed(α)) = trace(α)² - 4·norm(α) in the base field.
This connects the matrix discriminant to algebraic trace and norm. -/
private lemma Etingof.disc_fieldExtEmbed (hn : n ≠ 0) (α : (GaloisField p (2 * n))ˣ) :
    letI := Etingof.algebraGaloisFieldExt p n
    GL2.disc (Etingof.GL2.fieldExtEmbed p n α) =
    Algebra.trace (GaloisField p n) (GaloisField p (2 * n)) (α : GaloisField p (2 * n)) ^ 2 -
    4 * Algebra.norm (GaloisField p n) (α : GaloisField p (2 * n)) := by
  letI := Etingof.algebraGaloisFieldExt p n
  letI := Etingof.scalarTowerGaloisField p n
  haveI := Etingof.finiteDimensionalGaloisFieldExt p n
  let b := Module.finBasisOfFinrankEq (R := GaloisField p n)
    (M := GaloisField p (2 * n)) (Etingof.finrank_galoisField_ext p n hn)
  -- disc = tr² - 4·det via disc_eq_tr_det
  rw [GL2.disc_eq, Etingof.disc_eq_tr_det]
  -- The key: fieldExtEmbed α has matrix = leftMulMatrix b α
  have hval : (Etingof.GL2.fieldExtEmbed p n α).val =
      Algebra.leftMulMatrix b (α : GaloisField p (2 * n)) := by
    show (Etingof.GL2.fieldExtEmbed p n α).val = _
    simp only [Etingof.GL2.fieldExtEmbed, dif_neg hn]; rfl
  -- Relate matrix trace/det to algebra trace/norm
  congr 1
  · congr 1; rw [hval]; exact (Algebra.trace_eq_matrix_trace b _).symm
  · congr 1; rw [hval]; exact (Algebra.norm_eq_matrix_det b _).symm

/-- The algebraMap of disc(embed(α)) equals (α - α^q)² in the extension field. -/
private lemma Etingof.algebraMap_disc_fieldExtEmbed (hn : n ≠ 0)
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
  -- Use trace/norm formulas for finite fields
  have hfinrank : Module.finrank (GaloisField p n) (GaloisField p (2 * n)) = 2 :=
    Etingof.finrank_galoisField_ext p n hn
  have hcard : Nat.card (GaloisField p n) = p ^ n := GaloisField.card p n hn
  rw [FiniteField.algebraMap_trace_eq_sum_pow, FiniteField.algebraMap_norm_eq_prod_pow]
  rw [hfinrank]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Finset.prod_range_succ,
    Finset.prod_range_zero, one_mul, zero_add, pow_zero, pow_one, hcard]
  -- Handle algebraMap 4 = 4 and close by ring
  have h4 : algebraMap (GaloisField p n) (GaloisField p (2 * n)) 4 = 4 := map_ofNat _ 4
  rw [h4]
  ring

/-- Frobenius s^q = -s for s = α - α^q. -/
private lemma Etingof.frob_diff_neg (hn : n ≠ 0) (α : GaloisField p (2 * n)) :
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

private lemma Etingof.ellipticSubgroup_disc (hp2 : p ≠ 2) (k : GL2 p n)
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

/-- On elliptic elements, charVα₁ = 0 (no conjugate is upper triangular).
If x⁻¹gx were upper triangular, its (1,0) entry would be 0, making
disc(x⁻¹gx) = (M₀₀-M₁₁)², a perfect square. But disc(x⁻¹gx) = disc(g)
(conjugation invariant) and disc(g) is non-square (g is elliptic). -/
private lemma Etingof.charVα₁_elliptic
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

private lemma Etingof.induced_char_splitSemisimple_eq_zero
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
private lemma Etingof.complementaryChar_splitSemisimple_eq_zero
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

/-- Character orthogonality for finite groups: the sum of a nontrivial
character over all group elements is zero. Applied to ν^{q-1} on F_{q²}×. -/
private lemma Etingof.sum_nontrivial_char_eq_zero
    {G : Type*} [CommGroup G] [Fintype G]
    (χ : G →* ℂˣ) (hχ : χ ≠ 1) :
    ∑ g : G, (χ g : ℂ) = 0 := by
  -- Standard character orthogonality: ∑_g χ(g) = 0 for nontrivial χ
  -- Choose g₀ with χ(g₀) ≠ 1
  have ⟨g₀, hg₀⟩ : ∃ g₀, χ g₀ ≠ 1 := by
    by_contra h; push_neg at h; exact absurd (MonoidHom.ext h) hχ
  -- χ(g₀) * ∑ g, χ(g) = ∑ g, χ(g₀ * g) = ∑ g, χ(g) (by reindexing)
  have hne : (χ g₀ : ℂ) ≠ 1 := by
    intro h; apply hg₀; exact Units.val_injective h
  have key : (χ g₀ : ℂ) * ∑ g, (χ g : ℂ) = ∑ g, (χ g : ℂ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_nbij (fun g => g₀ * g)
    · intro g _; exact Finset.mem_univ _
    · intro g₁ _ g₂ _ h; exact mul_left_cancel h
    · intro g _; exact ⟨g₀⁻¹ * g, Finset.mem_univ _, by group⟩
    · intro g _; simp only [map_mul, Units.val_mul]
  -- (χ(g₀) - 1) * ∑ χ = 0, with χ(g₀) ≠ 1
  have h1 : ((χ g₀ : ℂ) - 1) * ∑ g, (χ g : ℂ) = 0 := by
    rw [sub_mul, one_mul, sub_eq_zero]; exact key
  rcases mul_eq_zero.mp h1 with h | h
  · exact absurd (sub_eq_zero.mp h) hne
  · exact h

open Classical in
/-- On elliptic elements, the complementary series character simplifies to
just the negated induced character: χ(g) = -(|K|⁻¹ ∑ x, ν(x⁻¹gx)).
This is because charW₁(g) = -1 and charVα₁(g) = 0 for elliptic g,
so χ(g) = (-1)·0 - 0 - Ind = -Ind. -/
private lemma Etingof.complementarySeriesChar_elliptic_eq
    [Fintype (GaloisField p n)] [DecidableEq (GaloisField p n)]
    [Fintype (GL2 p n)]
    (nu : (Etingof.GL2.ellipticSubgroup p n) →* ℂˣ)
    (g : GL2 p n) (hg : GL2.IsElliptic (p := p) (n := n) g) :
    Etingof.GL2.complementarySeriesChar p n nu g =
    -((Fintype.card ↥(Etingof.GL2.ellipticSubgroup p n) : ℂ)⁻¹ *
        ∑ x : GL2 p n,
          if h : x⁻¹ * g * x ∈ Etingof.GL2.ellipticSubgroup p n
          then (nu ⟨x⁻¹ * g * x, h⟩).val
          else 0) := by
  unfold Etingof.GL2.complementarySeriesChar
  set alpha := nu.comp (Etingof.GL2.scalarToElliptic p n)
  have hW : Etingof.GL2.charW₁ p n g = -1 := Etingof.charW₁_elliptic p n g hg
  have hV : Etingof.GL2.charVα₁ p n alpha g = 0 := Etingof.charVα₁_elliptic p n alpha g hg
  rw [hW, hV]
  ring

open Classical in
/-- The sum of |Ind_K^G ν|² over elliptic elements equals q(q-1)³.

This encapsulates the three hardest steps of the elliptic contribution proof:

1. **Conjugacy class decomposition**: The sum over elliptic GL₂ elements rewrites as
   (q(q-1)/2) times the sum over non-scalar elements of K = 𝔽_{q²}×.
   Uses orbit-stabilizer: each elliptic conjugacy class has q(q-1) elements,
   and Frobenius pairing (ζ ~ ζ^q) halves the representative count.

2. **Induced character on K**: For non-scalar ζ ∈ K, the Frobenius character formula
   gives Ind_K^G ν(ζ) = ν(ζ) + ν^q(ζ), since N_G(K)/K ≅ Gal(𝔽_{q²}/𝔽_q).
   Hence |Ind(ζ)|² = 2 + ν^{q-1}(ζ) + ν^{1-q}(ζ) (using |ν(ζ)| = 1).

3. **Character orthogonality**: ∑_K ν^{q-1} = 0 (by `sum_nontrivial_char_eq_zero`
   since ν^q ≠ ν). On 𝔽_q× ⊂ K, ν^{q-1} = 1, so ∑_{K\𝔽_q×} ν^{q-1} = -(q-1).
   Total: q(q-1)/2 · [2·q(q-1) - 2(q-1)] = q(q-1)/2 · 2(q-1)² = q(q-1)³. -/
private lemma Etingof.induced_normSq_sum_elliptic
    [Fintype (GL2 p n)] [Fintype (GaloisField p n)]
    [DecidableEq (GaloisField p n)]
    (nu : (Etingof.GL2.ellipticSubgroup p n) →* ℂˣ) (hn : n ≠ 0) :
    ∑ g ∈ Finset.univ.filter (fun g : GL2 p n => GL2.IsElliptic (p := p) (n := n) g),
      ((Fintype.card ↥(Etingof.GL2.ellipticSubgroup p n) : ℂ)⁻¹ *
        ∑ x : GL2 p n,
          if h : x⁻¹ * g * x ∈ Etingof.GL2.ellipticSubgroup p n
          then (nu ⟨x⁻¹ * g * x, h⟩).val
          else 0) *
      starRingEnd ℂ ((Fintype.card ↥(Etingof.GL2.ellipticSubgroup p n) : ℂ)⁻¹ *
        ∑ x : GL2 p n,
          if h : x⁻¹ * g * x ∈ Etingof.GL2.ellipticSubgroup p n
          then (nu ⟨x⁻¹ * g * x, h⟩).val
          else 0) =
    (Fintype.card (GaloisField p n) : ℂ) *
    ((Fintype.card (GaloisField p n) : ℂ) - 1) ^ 3 := by
  sorry

open Classical in
/-- The elliptic contribution to ∑ |χ|² equals q(q-1)³.

For elliptic g, χ(g) = -Ind_K^G ν(g) (by `complementarySeriesChar_elliptic_eq`),
so |χ(g)|² = |Ind(g)|². The sum of |Ind|² over elliptic elements equals q(q-1)³
by conjugacy class decomposition and character orthogonality
(see `induced_normSq_sum_elliptic`). -/
private lemma Etingof.elliptic_contribution
    [Fintype (GL2 p n)] [Fintype (GaloisField p n)]
    [DecidableEq (GaloisField p n)]
    (nu : (Etingof.GL2.ellipticSubgroup p n) →* ℂˣ) (hn : n ≠ 0) :
    ∑ g ∈ Finset.univ.filter (fun g : GL2 p n => GL2.IsElliptic (p := p) (n := n) g),
      Etingof.GL2.complementarySeriesChar p n nu g *
      starRingEnd ℂ (Etingof.GL2.complementarySeriesChar p n nu g) =
    (Fintype.card (GaloisField p n) : ℂ) *
    ((Fintype.card (GaloisField p n) : ℂ) - 1) ^ 3 := by
  -- Step 1: Rewrite each |χ(g)|² = |Ind(g)|² using complementarySeriesChar_elliptic_eq
  have hconv : ∀ g ∈ Finset.univ.filter
      (fun g : GL2 p n => GL2.IsElliptic (p := p) (n := n) g),
      Etingof.GL2.complementarySeriesChar p n nu g *
      starRingEnd ℂ (Etingof.GL2.complementarySeriesChar p n nu g) =
      ((Fintype.card ↥(Etingof.GL2.ellipticSubgroup p n) : ℂ)⁻¹ *
        ∑ x : GL2 p n,
          if h : x⁻¹ * g * x ∈ Etingof.GL2.ellipticSubgroup p n
          then (nu ⟨x⁻¹ * g * x, h⟩).val else 0) *
      starRingEnd ℂ ((Fintype.card ↥(Etingof.GL2.ellipticSubgroup p n) : ℂ)⁻¹ *
        ∑ x : GL2 p n,
          if h : x⁻¹ * g * x ∈ Etingof.GL2.ellipticSubgroup p n
          then (nu ⟨x⁻¹ * g * x, h⟩).val else 0) := by
    intro g hg
    rw [Finset.mem_filter] at hg
    rw [Etingof.complementarySeriesChar_elliptic_eq p n nu g hg.2]
    simp only [map_neg, neg_mul, mul_neg, neg_neg]
  rw [Finset.sum_congr rfl hconv]
  -- Step 2: Apply the helper for the induced character norm-squared sum
  exact Etingof.induced_normSq_sum_elliptic p n nu hn

/-- Arithmetic identity: contributions from scalar, parabolic, and elliptic conjugacy classes
sum to |GL₂(𝔽_q)|. Specifically:
  (q-1)³ + (q-1)(q²-1) + q(q-1)³ = q(q-1)²(q+1) = (q²-1)(q²-q) -/
private lemma Etingof.innerProduct_arith_identity (q : ℂ) :
    (q - 1) ^ 3 + (q - 1) * (q ^ 2 - 1) + q * (q - 1) ^ 3 =
    (q ^ 2 - 1) * (q ^ 2 - q) := by
  ring

/-- The inner product sum ∑_{g∈G} |χ(g)|² equals |G| = q(q-1)²(q+1).

The proof splits the sum over GL₂(𝔽_q) by conjugacy class type:
- **Scalar matrices** xI (q-1 elements): |χ(xI)|² = (q-1)², total (q-1)³
- **Parabolic matrices** (q-1)(q²-1) elements: |χ|² = 1, total (q-1)(q²-1)
- **Non-scalar semisimple** (split): χ = 0, total 0
- **Elliptic elements**: uses character orthogonality ∑_{F_{q²}×} ν^{q-1}(ζ) = 0
  to get total q(q-1)³

Combined: (q-1)³ + (q-1)(q²-1) + q(q-1)³ = (q-1)²[q-1+q+1+q(q-1)] = (q-1)²q(q+1) = |G|.
-/
private lemma Etingof.innerProduct_sum_eq_card
    [Fintype (GaloisField p n)] [DecidableEq (GaloisField p n)]
    [Fintype (GL2 p n)]
    (hp2 : p ≠ 2)
    (nu : (Etingof.GL2.ellipticSubgroup p n) →* ℂˣ) (hn : 0 < n) :
    (∑ x : GL2 p n,
      Etingof.GL2.complementarySeriesChar p n nu x *
      starRingEnd ℂ (Etingof.GL2.complementarySeriesChar p n nu x) : ℂ) =
    (Fintype.card (GL2 p n) : ℂ) := by
  have hn_ne : n ≠ 0 := by omega
  set q := Fintype.card (GaloisField p n) with hq_def
  have hq1 : 1 < q := by
    rw [hq_def, ← Nat.card_eq_fintype_card, GaloisField.card p n hn_ne]
    exact Nat.one_lt_pow hn_ne hp.out.one_lt
  -- |GL₂(𝔽_q)| = (q²-1)(q²-q)
  have hG : Fintype.card (GL2 p n) = (q ^ 2 - 1) * (q ^ 2 - q) := by
    have := @Matrix.card_GL_field (GaloisField p n) _ _ 2
    simp only [Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
               ← Nat.card_eq_fintype_card] at this
    rw [← Nat.card_eq_fintype_card, this, Nat.card_eq_fintype_card]
  -- Step 1: Split sum by conjugacy class type
  set χ := Etingof.GL2.complementarySeriesChar p n nu
  set f : GL2 p n → ℂ := fun g => χ g * starRingEnd ℂ (χ g)
  -- Use GL2.sum_split (GL2 and GL2' are definitionally equal)
  have hsplit := GL2.sum_split (p := p) (n := n) f
  rw [hsplit]
  -- Step 2: Compute contribution from each class type
  -- Scalar: each element contributes (q-1)², total = (q-1) * (q-1)² = (q-1)³
  have h_scalar : ∑ g ∈ Finset.univ.filter (fun g => GL2.IsScalar g), f g =
      ((q : ℂ) - 1) ^ 3 := by
    have hval : ∀ g ∈ Finset.univ.filter (fun g => GL2.IsScalar (p := p) (n := n) g),
        f g = ((q : ℂ) - 1) ^ 2 := fun g hg => by
      rw [Finset.mem_filter] at hg
      exact Etingof.normSq_complementaryChar_scalar p n nu hn_ne g hg.2
    rw [Finset.sum_congr rfl hval, Finset.sum_const, GL2.card_isScalar hn_ne, nsmul_eq_mul]
    have h1 : 1 ≤ q := by omega
    rw [show Fintype.card (GaloisField p n) = q from hq_def.symm]
    push_cast [Nat.cast_sub h1]; ring
  -- Parabolic: each element contributes 1, total = (q-1)(q²-1)
  have h_parabolic : ∑ g ∈ Finset.univ.filter (fun g => GL2.IsParabolic g), f g =
      ((q : ℂ) - 1) * ((q : ℂ) ^ 2 - 1) := by
    have hval : ∀ g ∈ Finset.univ.filter (fun g => GL2.IsParabolic (p := p) (n := n) g),
        f g = 1 := fun g hg => by
      rw [Finset.mem_filter] at hg
      exact Etingof.normSq_complementaryChar_parabolic p n nu g hg.2
    rw [Finset.sum_congr rfl hval, Finset.sum_const, GL2.card_isParabolic hp2 hn_ne, nsmul_eq_mul,
      mul_one]
    have h1 : 1 ≤ q := by omega
    have h2 : 1 ≤ q ^ 2 := by nlinarith
    rw [show Fintype.card (GaloisField p n) = q from hq_def.symm]
    push_cast [Nat.cast_sub h1, Nat.cast_sub h2]; ring
  -- Split semisimple: each element contributes 0
  have h_split : ∑ g ∈ Finset.univ.filter (fun g => GL2.IsSplitSemisimple g), f g = 0 := by
    apply Finset.sum_eq_zero; intro g hg
    rw [Finset.mem_filter] at hg
    have h0 : χ g = 0 := Etingof.complementaryChar_splitSemisimple_eq_zero p n hp2 nu g hg.2
    change χ g * starRingEnd ℂ (χ g) = 0
    rw [h0, map_zero, mul_zero]
  -- Elliptic: total = q(q-1)³
  have h_elliptic : ∑ g ∈ Finset.univ.filter (fun g => GL2.IsElliptic g), f g =
      (q : ℂ) * ((q : ℂ) - 1) ^ 3 :=
    Etingof.elliptic_contribution p n nu hn_ne
  -- Combine
  rw [h_scalar, h_parabolic, h_split, h_elliptic, hG]
  have h1 : 1 ≤ q := by omega
  have h2 : 1 ≤ q ^ 2 := by nlinarith
  have h3 : q ≤ q ^ 2 := by nlinarith
  push_cast [Nat.cast_sub h1, Nat.cast_sub h2, Nat.cast_sub h3]; ring

/-- **Lemma 5.25.3 (part 1)**: The complementary series virtual character
satisfies ⟨χ, χ⟩ = 1, establishing (via Lemma 5.7.2) that it is the character
of an actual irreducible representation. (Etingof Lemma 5.25.3) -/
theorem Etingof.Lemma5_25_3_innerProduct
    [Fintype (GaloisField p n)] [DecidableEq (GaloisField p n)]
    [Fintype (GL2 p n)]
    (hp2 : p ≠ 2)
    (nu : (Etingof.GL2.ellipticSubgroup p n) →* ℂˣ) (hn : 0 < n) :
    (Fintype.card (GL2 p n) : ℂ)⁻¹ •
      ∑ x : GL2 p n,
        Etingof.GL2.complementarySeriesChar p n nu x *
        starRingEnd ℂ (Etingof.GL2.complementarySeriesChar p n nu x) = 1 := by
  rw [Etingof.innerProduct_sum_eq_card p n hp2 nu hn]
  simp only [smul_eq_mul]
  have hcard : (Fintype.card (GL2 p n) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_pos.ne'
  exact inv_mul_cancel₀ hcard

/-- **Lemma 5.25.3 (part 2)**: The complementary series virtual character
satisfies χ(1) = q - 1 > 0, confirming it has positive dimension.
(Etingof Lemma 5.25.3) -/
private lemma Etingof.charW₁_one
    [Fintype (GaloisField p n)] [DecidableEq (GaloisField p n)] :
    Etingof.GL2.charW₁ p n 1 =
      (Fintype.card (GaloisField p n) : ℂ) := by
  unfold GL2.charW₁
  simp only [Matrix.GeneralLinearGroup.coe_one, Matrix.one_apply]
  norm_num

private lemma Etingof.dimension_arith_identity
    (q : ℂ) (hq : q ≠ 0) (hq1 : q - 1 ≠ 0) (hqp1 : q + 1 ≠ 0) :
    q * (q⁻¹ * ((q - 1) ^ 2)⁻¹ * ((q ^ 2 - 1) * (q ^ 2 - q))) -
    q⁻¹ * ((q - 1) ^ 2)⁻¹ * ((q ^ 2 - 1) * (q ^ 2 - q)) -
    (q ^ 2 - 1)⁻¹ * ((q ^ 2 - 1) * (q ^ 2 - q)) = q - 1 := by
  have hq2m1 : q ^ 2 - 1 ≠ 0 := by
    have : q ^ 2 - 1 = (q - 1) * (q + 1) := by ring
    rw [this]; exact mul_ne_zero hq1 hqp1
  have hqm1sq : (q - 1) ^ 2 ≠ 0 := pow_ne_zero 2 hq1
  field_simp [hq, hq1, hqp1, hq2m1, hqm1sq]
  ring

theorem Etingof.Lemma5_25_3_dimension
    [Fintype (GaloisField p n)] [DecidableEq (GaloisField p n)]
    [Fintype (GL2 p n)]
    (nu : (Etingof.GL2.ellipticSubgroup p n) →* ℂˣ) (hn : 0 < n) :
    Etingof.GL2.complementarySeriesChar p n nu 1 = (p ^ n : ℂ) - 1 ∧
    (0 : ℝ) < (p ^ n : ℝ) - 1 := by
  constructor
  · -- Part 1: χ(1) = q - 1
    -- At g = 1, x⁻¹·1·x = 1 for all x
    have h1x : ∀ x : GL2 p n, x⁻¹ * 1 * x = 1 := by intro x; simp
    -- Unfold and simplify the character at identity
    change GL2.complementarySeriesChar p n nu 1 = (p ^ n : ℂ) - 1
    unfold GL2.complementarySeriesChar GL2.charW₁ GL2.charVα₁
    simp only [Matrix.GeneralLinearGroup.coe_one, Matrix.one_apply, h1x]
    -- Simplify nu at identity: nu(⟨1, _⟩) = nu(1) = 1, scalarToElliptic(1) = 1
    have hnu_sub : ∀ h, nu (⟨1, h⟩ : ↥(GL2.ellipticSubgroup p n)) = 1 :=
      fun h => (congrArg nu (Subtype.ext rfl)).trans (map_one nu)
    simp only [hnu_sub, Units.val_one]
    -- Resolve Fin 2 if-conditions and simplify 0*t²+0*t-0=0
    norm_num
    -- Goal: q * (q⁻¹ * (q-1)²⁻¹ * |G|) - q⁻¹ * (q-1)²⁻¹ * |G| - |K|⁻¹ * |G| = p^n - 1
    -- where q = p^n, |G| = |GL₂(𝔽_q)|, |K| = |𝔽_{q²}×|
    -- Factor out |G|: ((q-1) * q⁻¹ * (q-1)²⁻¹ - q⁻¹ * (q-1)²⁻¹ - |K|⁻¹) * |G|
    -- = ((q-1)/((q-1)²q) - 1/((q-1)²q) - 1/|K|) * |G|
    -- = (1/((q-1)q) - 1/|K|) * |G|  -- since (q-1-1)/((q-1)²q) = ... wait
    -- Actually: (q-1)/(q(q-1)²) = 1/(q(q-1))
    -- And 1/(q(q-1)²) = 1/(q(q-1)²) stays.
    -- So: q/(q(q-1)²) - 1/(q(q-1)²) - 1/(q²-1) = (q-1)/(q(q-1)²) - 1/(q²-1)
    --   = 1/(q(q-1)) - 1/((q-1)(q+1))  = ((q+1) - q) / (q(q-1)(q+1)) = 1/(q(q-1)(q+1))
    -- Then 1/(q(q-1)(q+1)) * q(q-1)²(q+1) = q-1. ✓
    -- This needs |GL₂| = q(q²-1)(q-1) and |K| = q²-1
    -- Convert all Fintype.card to Nat.card to avoid Fintype instance mismatches
    simp only [← Nat.card_eq_fintype_card]
    have hn_ne : n ≠ 0 := by omega
    have hq_val : Nat.card (GaloisField p n) = p ^ n := GaloisField.card p n hn_ne
    have hq1 : 1 < Nat.card (GaloisField p n) := by
      rw [hq_val]; exact Nat.one_lt_pow hn_ne hp.out.one_lt
    -- GL₂ cardinality (card_GL_field uses Fintype.card for q, convert to Nat.card)
    have hG : Nat.card (GL2 p n) =
        (Nat.card (GaloisField p n) ^ 2 - 1) *
        (Nat.card (GaloisField p n) ^ 2 - Nat.card (GaloisField p n)) := by
      haveI : Fintype (GaloisField p n) := Fintype.ofFinite _
      have := @Matrix.card_GL_field (GaloisField p n) _ _ 2
      simp only [Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
                  ← Nat.card_eq_fintype_card] at this
      exact this
    -- Elliptic subgroup cardinality: |K| = |𝔽_{q²}×| = q² - 1
    have hK : Nat.card ↥(GL2.ellipticSubgroup p n) =
        Nat.card (GaloisField p n) ^ 2 - 1 := by
      -- K = fieldExtEmbed.range
      change Nat.card ↥(GL2.fieldExtEmbed p n).range = _
      -- fieldExtEmbed is injective (leftMulMatrix is injective as AlgHom from a field)
      have hinj : Function.Injective (GL2.fieldExtEmbed p n) := by
        intro a b hab
        unfold GL2.fieldExtEmbed at hab
        simp only [dif_neg hn_ne] at hab
        have hval := congr_arg (fun g => g.val) hab
        have := RingHom.injective
          (Algebra.leftMulMatrix (Module.finBasisOfFinrankEq (GaloisField p n)
          (GaloisField p (2 * n)) (finrank_galoisField_ext p n hn_ne))).toRingHom
        exact Units.ext (this hval)
      -- |range| = |domain| since injective
      have : (GL2.fieldExtEmbed p n).range.carrier = Set.range (GL2.fieldExtEmbed p n) :=
        MonoidHom.coe_range _
      rw [show Nat.card ↥(GL2.fieldExtEmbed p n).range =
        Nat.card ↥(Set.range (GL2.fieldExtEmbed p n)) from by
        congr 1]
      rw [Nat.card_range_of_injective hinj]
      -- |𝔽_{q²}ˣ| = |𝔽_{q²}| - 1 = p^(2n) - 1 = (p^n)² - 1 = q² - 1
      rw [Nat.card_units]
      rw [GaloisField.card p (2 * n) (Nat.mul_ne_zero two_ne_zero hn_ne)]
      rw [hq_val]; ring_nf
    -- Substitute q = p^n throughout (now the goal uses Nat.card)
    rw [hq_val] at hG hK ⊢
    -- Substitute G and K cardinalities
    rw [hG, hK]
    -- Now the goal is purely in terms of p, n as ℕ with casts to ℂ
    -- Convert ℕ subtractions and prove with field_simp + ring
    have h1 : 1 ≤ p ^ n := by omega
    have h2 : 1 ≤ (p ^ n) ^ 2 := by nlinarith
    have h3 : p ^ n ≤ (p ^ n) ^ 2 := by nlinarith
    simp only [Nat.cast_sub h1, Nat.cast_mul, Nat.cast_sub h2, Nat.cast_sub h3, Nat.cast_pow,
               Nat.cast_one]
    -- Now all ℕ casts are gone, everything is in (↑p : ℂ)^n
    -- Nonzero conditions for field_simp
    have hpn_ne : (↑p : ℂ) ^ n ≠ 0 := by
      exact_mod_cast show (p ^ n : ℕ) ≠ 0 by omega
    have hpn1_ne : (↑p : ℂ) ^ n - 1 ≠ 0 := by
      intro h
      have : (p ^ n : ℕ) = 1 := by exact_mod_cast sub_eq_zero.mp h
      omega
    have hpnp1_ne : (↑p : ℂ) ^ n + 1 ≠ 0 := by
      have : (↑(p ^ n + 1) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      push_cast [Nat.cast_pow] at this; exact this
    -- Apply the standalone arithmetic identity
    exact dimension_arith_identity _ hpn_ne hpn1_ne hpnp1_ne
  · -- Part 2: q - 1 > 0
    have hp_pos := hp.out.pos
    have h1 : 1 < p ^ n := by
      calc p ^ n ≥ p ^ 1 := Nat.pow_le_pow_right hp_pos hn
        _ = p := pow_one p
        _ ≥ 2 := hp.out.two_le
    have h2 : (1 : ℝ) < (p ^ n : ℝ) := by exact_mod_cast h1
    linarith
