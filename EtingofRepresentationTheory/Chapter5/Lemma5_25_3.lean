import Mathlib

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
private noncomputable def Etingof.GL2.charW₁ : GL2 p n → ℂ :=
  haveI : Fintype (GaloisField p n) := Fintype.ofFinite _
  haveI : DecidableEq (GaloisField p n) := Classical.decEq _
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
    (alpha : (GaloisField p n)ˣ →* ℂˣ) : GL2 p n → ℂ :=
  haveI : Fintype (GaloisField p n) := Fintype.ofFinite _
  haveI : DecidableEq (GaloisField p n) := Classical.decEq _
  haveI : Fintype (GL2 p n) := Fintype.ofFinite _
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

/-- **Lemma 5.25.3 (part 1)**: The complementary series virtual character
satisfies ⟨χ, χ⟩ = 1, establishing (via Lemma 5.7.2) that it is the character
of an actual irreducible representation. (Etingof Lemma 5.25.3) -/
theorem Etingof.Lemma5_25_3_innerProduct
    [Fintype (GL2 p n)]
    (nu : (Etingof.GL2.ellipticSubgroup p n) →* ℂˣ) (hn : 0 < n) :
    (Fintype.card (GL2 p n) : ℂ)⁻¹ •
      ∑ x : GL2 p n,
        Etingof.GL2.complementarySeriesChar p n nu x *
        starRingEnd ℂ (Etingof.GL2.complementarySeriesChar p n nu x) = 1 := by
  sorry

/-- **Lemma 5.25.3 (part 2)**: The complementary series virtual character
satisfies χ(1) = q - 1 > 0, confirming it has positive dimension.
(Etingof Lemma 5.25.3) -/
private lemma Etingof.charW₁_one :
    Etingof.GL2.charW₁ p n 1 =
      (@Fintype.card (GaloisField p n) (Fintype.ofFinite _) : ℂ) := by
  unfold GL2.charW₁
  simp only [Matrix.GeneralLinearGroup.coe_one, Matrix.one_apply]
  norm_num

theorem Etingof.Lemma5_25_3_dimension
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
    -- Now the goal is arithmetic with cardinalities.
    haveI : Fintype (GaloisField p n) := Fintype.ofFinite _
    haveI : Fintype (GL2 p n) := Fintype.ofFinite _
    haveI : Fintype ↥(GL2.ellipticSubgroup p n) := Fintype.ofFinite _
    -- Set variables for readability
    set q := (Fintype.card (GaloisField p n) : ℂ) with hq_def
    set G := (Fintype.card (GL2 p n) : ℂ) with hG_def
    set Kc := (Fintype.card ↥(GL2.ellipticSubgroup p n) : ℂ) with hKc_def
    -- Need: q * (q⁻¹ * (q-1)²⁻¹ * G) - q⁻¹ * (q-1)²⁻¹ * G - Kc⁻¹ * G = p^n - 1
    -- Establish q = p^n
    have hn_ne : n ≠ 0 := by omega
    have hq_val : (Fintype.card (GaloisField p n) : ℕ) = p ^ n := by
      rw [← Nat.card_eq_fintype_card]
      exact GaloisField.card p n hn_ne
    -- q > 0 and q - 1 > 0 (as naturals)
    have hq_pos : 0 < Fintype.card (GaloisField p n) := Fintype.card_pos
    have hq1 : 1 < Fintype.card (GaloisField p n) := by
      rw [hq_val]; exact Nat.one_lt_pow hn_ne hp.out.one_lt
    -- q ≠ 0 and (q-1) ≠ 0 in ℂ
    have hqC : q ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hq1C : q - 1 ≠ 0 := by
      simp only [hq_def, Ne, sub_eq_zero]
      exact_mod_cast Nat.ne_of_gt hq1
    -- |GL₂(𝔽_q)| = ∏ i : Fin 2, (q² - q^i) = (q²-1)(q²-q)
    -- |K| relates to 𝔽_{q²}× (need injectivity of fieldExtEmbed)
    -- Kc ≠ 0
    have hKc_pos : 0 < Fintype.card ↥(GL2.ellipticSubgroup p n) := Fintype.card_pos
    have hKcC : Kc ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    -- The key equation after field_simp:
    -- q * G / (q * (q-1)²) - G / (q * (q-1)²) - G / Kc = q - 1
    -- i.e. (q-1) * G / (q * (q-1)²) - G / Kc = q - 1
    -- i.e. G / (q * (q-1)) - G / Kc = q - 1
    -- With G = q(q-1)²(q+1) and Kc = q²-1 = (q-1)(q+1):
    -- q(q-1)²(q+1) / (q(q-1)) - q(q-1)²(q+1) / ((q-1)(q+1)) = q - 1
    -- (q-1)(q+1) - q(q-1) = (q-1)(q+1-q) = q-1 ✓
    -- Establish G = q(q-1)²(q+1) via card_GL_field
    -- Establish Kc = q²-1 (|K| = |𝔽_{q²}×| since fieldExtEmbed is injective)
    -- Then field_simp and ring
    -- These cardinality computations are non-trivial infrastructure;
    -- Aristotle has been submitted for this proof.
    sorry
  · -- Part 2: q - 1 > 0
    have hp_pos := hp.out.pos
    have h1 : 1 < p ^ n := by
      calc p ^ n ≥ p ^ 1 := Nat.pow_le_pow_right hp_pos hn
        _ = p := pow_one p
        _ ≥ 2 := hp.out.two_le
    have h2 : (1 : ℝ) < (p ^ n : ℝ) := by exact_mod_cast h1
    linarith
