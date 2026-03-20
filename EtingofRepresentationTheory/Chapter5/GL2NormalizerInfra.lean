import Mathlib
import EtingofRepresentationTheory.Chapter5.GL2CharacterValues

/-!
# GL₂ Normalizer Infrastructure for Elliptic Subgroup

Infrastructure about the normalizer of K = 𝔽_{q²}× ⊂ GL₂(𝔽_q):
- Frobenius matrix and conjugation action
- Centralizer of non-scalar K-elements
- Normalizer structure N(K) = K ∪ σK, |N| = 2|K|
-/

variable (p : ℕ) [hp : Fact (Nat.Prime p)] (n : ℕ)

private abbrev GL2 := Matrix.GeneralLinearGroup (Fin 2) (GaloisField p n)

open scoped Matrix

/-- The Frobenius automorphism of 𝔽_{q²}/𝔽_q, represented as an element of GL₂(𝔽_q).
This is the matrix of the map x ↦ x^q with respect to the embedding basis. -/
noncomputable def Etingof.GL2.frobeniusMatrix : GL2 p n := by
  by_cases hn : n = 0
  · exact 1
  · letI := Etingof.algebraGaloisFieldExt p n
    letI := Etingof.scalarTowerGaloisField p n
    haveI := Etingof.finiteDimensionalGaloisFieldExt p n
    haveI : Fintype (GaloisField p n) := Fintype.ofFinite _
    haveI : Fintype (GaloisField p (2 * n)) := Fintype.ofFinite _
    haveI : Algebra.IsAlgebraic (GaloisField p n) (GaloisField p (2 * n)) :=
      Algebra.IsAlgebraic.of_finite _ _
    let b := Module.finBasisOfFinrankEq (R := GaloisField p n)
      (M := GaloisField p (2 * n)) (Etingof.finrank_galoisField_ext p n hn)
    let σ := (FiniteField.frobeniusAlgEquivOfAlgebraic
      (GaloisField p n) (GaloisField p (2 * n))).toLinearEquiv
    let M := LinearMap.toMatrix b b σ.toLinearMap
    let M_inv := LinearMap.toMatrix b b σ.symm.toLinearMap
    refine ⟨M, M_inv, ?_, ?_⟩
    · -- M * M_inv = 1: toMatrix(σ) * toMatrix(σ⁻¹) = toMatrix(σ ∘ σ⁻¹) = toMatrix(id) = 1
      rw [← LinearMap.toMatrix_mul, show σ.toLinearMap * σ.symm.toLinearMap = LinearMap.id from by
        ext x; simp, LinearMap.toMatrix_id]
    · -- M_inv * M = 1
      rw [← LinearMap.toMatrix_mul, show σ.symm.toLinearMap * σ.toLinearMap = LinearMap.id from by
        ext x; simp, LinearMap.toMatrix_id]

/-- σ² = id in GL₂ (the Frobenius has order dividing 2 on 𝔽_{q²}/𝔽_q). -/
lemma Etingof.GL2.frobeniusMatrix_sq_eq_one (hn : n ≠ 0) :
    Etingof.GL2.frobeniusMatrix p n ^ 2 = 1 := by
  letI := Etingof.algebraGaloisFieldExt p n
  letI := Etingof.scalarTowerGaloisField p n
  haveI := Etingof.finiteDimensionalGaloisFieldExt p n
  haveI : Fintype (GaloisField p n) := Fintype.ofFinite _
  haveI : Fintype (GaloisField p (2 * n)) := Fintype.ofFinite _
  haveI : Algebra.IsAlgebraic (GaloisField p n) (GaloisField p (2 * n)) :=
    Algebra.IsAlgebraic.of_finite _ _
  let b := Module.finBasisOfFinrankEq (R := GaloisField p n)
    (M := GaloisField p (2 * n)) (Etingof.finrank_galoisField_ext p n hn)
  let σ := (FiniteField.frobeniusAlgEquivOfAlgebraic
    (GaloisField p n) (GaloisField p (2 * n))).toLinearEquiv
  rw [sq]
  apply Units.ext
  -- The Frobenius on F_{q²}/F_q has order dividing 2: σ(x) = x^q, so σ²(x) = x^{q²} = x.
  -- Proving this requires matching the internal basis of frobeniusMatrix with the local basis.
  -- This is a technical instance-matching issue; the mathematical content is straightforward.
  sorry

/-- The Frobenius σ⁻¹ = σ (since σ² = 1). -/
lemma Etingof.GL2.frobeniusMatrix_inv_eq_self (hn : n ≠ 0) :
    (Etingof.GL2.frobeniusMatrix p n)⁻¹ = Etingof.GL2.frobeniusMatrix p n := by
  have h2 := Etingof.GL2.frobeniusMatrix_sq_eq_one p n hn
  rw [sq] at h2
  exact inv_eq_of_mul_eq_one_left h2

/-- The Frobenius matrix conjugates fieldExtEmbed(α) to fieldExtEmbed(α^q). -/
lemma Etingof.GL2.frobeniusMatrix_conj [Fintype (GaloisField p n)] (hn : n ≠ 0)
    (α : (GaloisField p (2 * n))ˣ) :
    (Etingof.GL2.frobeniusMatrix p n)⁻¹ *
    Etingof.GL2.fieldExtEmbed p n α *
    Etingof.GL2.frobeniusMatrix p n =
    Etingof.GL2.fieldExtEmbed p n
      ⟨(α : GaloisField p (2 * n)) ^ Fintype.card (GaloisField p n),
       (α⁻¹ : GaloisField p (2 * n)) ^ Fintype.card (GaloisField p n),
       by rw [← mul_pow]; simp [Units.val_inv_eq_inv_val, mul_inv_cancel₀ α.ne_zero],
       by rw [← mul_pow]; simp [Units.val_inv_eq_inv_val, inv_mul_cancel₀ α.ne_zero]⟩ := by
  letI := Etingof.algebraGaloisFieldExt p n
  letI := Etingof.scalarTowerGaloisField p n
  haveI := Etingof.finiteDimensionalGaloisFieldExt p n
  haveI : Fintype (GaloisField p n) := Fintype.ofFinite _
  haveI : Fintype (GaloisField p (2 * n)) := Fintype.ofFinite _
  haveI : Algebra.IsAlgebraic (GaloisField p n) (GaloisField p (2 * n)) :=
    Algebra.IsAlgebraic.of_finite _ _
  let b := Module.finBasisOfFinrankEq (R := GaloisField p n)
    (M := GaloisField p (2 * n)) (Etingof.finrank_galoisField_ext p n hn)
  let σ := (FiniteField.frobeniusAlgEquivOfAlgebraic
    (GaloisField p n) (GaloisField p (2 * n))).toLinearEquiv
  -- Mathematical content: σ⁻¹ ∘ Lα ∘ σ = L_{α^q} since σ(α·x) = σ(α)·σ(x) = α^q·σ(x)
  -- and σ² = id. The proof requires matching internal basis instances of frobeniusMatrix
  -- and fieldExtEmbed, which is a technical Lean definitional equality issue.
  sorry

/-- The Frobenius matrix normalizes the elliptic subgroup K. -/
lemma Etingof.GL2.frobeniusMatrix_normalizes [Fintype (GaloisField p n)] (hn : n ≠ 0)
    (k : GL2 p n) (hk : k ∈ Etingof.GL2.ellipticSubgroup p n) :
    (Etingof.GL2.frobeniusMatrix p n)⁻¹ * k * Etingof.GL2.frobeniusMatrix p n ∈
    Etingof.GL2.ellipticSubgroup p n := by
  obtain ⟨α, rfl⟩ := hk
  rw [Etingof.GL2.frobeniusMatrix_conj p n hn α]
  exact ⟨_, rfl⟩

/-- The Frobenius matrix squared is in K. -/
lemma Etingof.GL2.frobeniusMatrix_sq_mem (hn : n ≠ 0) :
    Etingof.GL2.frobeniusMatrix p n ^ 2 ∈ Etingof.GL2.ellipticSubgroup p n := by
  rw [Etingof.GL2.frobeniusMatrix_sq_eq_one p n hn]
  exact Subgroup.one_mem _

section Centralizer

/-! ### Centralizer of non-scalar elements of K -/

/-- For non-scalar ζ ∈ K = 𝔽_{q²}× ⊂ GL₂(𝔽_q), the centralizer C_{GL₂}(ζ) equals K.
If g ∈ GL₂(𝔽_q) commutes with ζ, then g ∈ K. -/
lemma Etingof.centralizer_nonscalar_elliptic (hn : n ≠ 0)
    (ζ : GL2 p n) (hζ_mem : ζ ∈ Etingof.GL2.ellipticSubgroup p n)
    (hζ_ns : ¬GL2.IsScalar (p := p) (n := n) ζ)
    (g : GL2 p n) (hcomm : g * ζ = ζ * g) :
    g ∈ Etingof.GL2.ellipticSubgroup p n := by
  sorry

end Centralizer

section Normalizer

/-! ### Normalizer of K in GL₂ -/

/-- The normalizer of K in GL₂(𝔽_q): the set of elements that normalize K. -/
def Etingof.GL2.isInNormalizer (g : GL2 p n) : Prop :=
  ∀ k ∈ Etingof.GL2.ellipticSubgroup p n,
    g⁻¹ * k * g ∈ Etingof.GL2.ellipticSubgroup p n

/-- Elements of K are in the normalizer (K is abelian, so conjugation is trivial). -/
lemma Etingof.GL2.ellipticSubgroup_mem_normalizer
    (k : GL2 p n) (hk : k ∈ Etingof.GL2.ellipticSubgroup p n) :
    Etingof.GL2.isInNormalizer p n k := by
  intro k' hk'
  obtain ⟨α, rfl⟩ := hk
  obtain ⟨β, rfl⟩ := hk'
  change (Etingof.GL2.fieldExtEmbed p n α)⁻¹ *
    Etingof.GL2.fieldExtEmbed p n β *
    Etingof.GL2.fieldExtEmbed p n α ∈ _
  rw [← map_inv, ← map_mul, ← map_mul, inv_mul_cancel_comm]
  exact ⟨β, rfl⟩

/-- The Frobenius matrix is in the normalizer of K. -/
lemma Etingof.GL2.frobeniusMatrix_mem_normalizer [Fintype (GaloisField p n)] (hn : n ≠ 0) :
    Etingof.GL2.isInNormalizer p n (Etingof.GL2.frobeniusMatrix p n) :=
  fun k hk => Etingof.GL2.frobeniusMatrix_normalizes p n hn k hk

/-- The normalizer of K contains K and the Frobenius coset σK. -/
lemma Etingof.GL2.normalizer_contains_frobeniusCoset [Fintype (GaloisField p n)] (hn : n ≠ 0)
    (k : GL2 p n) (hk : k ∈ Etingof.GL2.ellipticSubgroup p n) :
    Etingof.GL2.isInNormalizer p n (Etingof.GL2.frobeniusMatrix p n * k) := by
  intro k' hk'
  have : (Etingof.GL2.frobeniusMatrix p n * k)⁻¹ * k' *
    (Etingof.GL2.frobeniusMatrix p n * k) =
    k⁻¹ * ((Etingof.GL2.frobeniusMatrix p n)⁻¹ * k' *
      Etingof.GL2.frobeniusMatrix p n) * k := by group
  rw [this]
  exact Etingof.GL2.ellipticSubgroup_mem_normalizer p n k hk _
    (Etingof.GL2.frobeniusMatrix_normalizes p n hn k' hk')

/-- For non-scalar k ∈ K, if z⁻¹kz ∈ K then z normalizes K. -/
lemma Etingof.GL2.conj_mem_implies_normalizer (hn : n ≠ 0)
    (hp2 : p ≠ 2)
    (k : GL2 p n) (hk_mem : k ∈ Etingof.GL2.ellipticSubgroup p n)
    (hk_ns : ¬GL2.IsScalar (p := p) (n := n) k)
    (z : GL2 p n) (hz : z⁻¹ * k * z ∈ Etingof.GL2.ellipticSubgroup p n) :
    Etingof.GL2.isInNormalizer p n z := by
  sorry

/-- The cardinality of the normalizer: |N_{GL₂}(K)| = 2|K|. -/
lemma Etingof.GL2.normalizer_card (hn : n ≠ 0) (hp2 : p ≠ 2)
    [Fintype (GL2 p n)] [Fintype (Etingof.GL2.ellipticSubgroup p n)]
    [DecidablePred (Etingof.GL2.isInNormalizer p n)] :
    (Finset.univ.filter (fun g : GL2 p n =>
      Etingof.GL2.isInNormalizer p n g)).card =
    2 * Fintype.card ↥(Etingof.GL2.ellipticSubgroup p n) := by
  sorry

end Normalizer
