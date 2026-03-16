import Mathlib

/-!
# Definition 5.2.2: Algebraic Numbers (Eigenvalue Characterization)

An equivalent characterization: z ∈ ℂ is an algebraic number (resp. integer) if and only
if z is an eigenvalue of a matrix with entries in ℚ (resp. ℤ).

## Mathlib correspondence

This is a theorem proving equivalence with Definition 5.2.1. Uses `Matrix.IsHermitian`,
eigenvalue theory, and companion matrices.
-/

open IntermediateField in
/-- A complex number is algebraic if and only if it is an eigenvalue of a matrix
with rational entries. (Etingof Definition 5.2.2) -/
theorem Etingof.Definition5_2_2_algebraic
    (z : ℂ) :
    IsAlgebraic ℚ z ↔
    ∃ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℚ),
      (Matrix.charpoly (M.map (algebraMap ℚ ℂ))).IsRoot z := by
  constructor
  · -- Forward: algebraic → eigenvalue of left multiplication matrix
    intro halg
    have hint : IsIntegral ℚ z := isAlgebraic_iff_isIntegral.mp halg
    -- Use the power basis for ℚ(z)/ℚ
    set F := ℚ⟮z⟯ with hF
    let pb := adjoin.powerBasis hint
    -- The left multiplication matrix of the generator
    let M := Algebra.leftMulMatrix pb.basis pb.gen
    refine ⟨_, M, ?_⟩
    rw [Matrix.charpoly_map, Polynomial.IsRoot, Polynomial.eval_map_algebraMap,
        charpoly_leftMulMatrix]
    -- Need: aeval z (minpoly ℚ pb.gen) = 0
    -- pb.gen is z inside ℚ(z), and minpoly maps through the algebra
    have hgen : (algebraMap F ℂ) pb.gen = z := by
      simp [pb, adjoin.powerBasis_gen]
    let ι := IsScalarTower.toAlgHom ℚ F ℂ
    have : ι pb.gen = z := hgen
    calc Polynomial.aeval z (minpoly ℚ pb.gen)
        = Polynomial.aeval (ι pb.gen) (minpoly ℚ pb.gen) := by rw [this]
      _ = ι (Polynomial.aeval pb.gen (minpoly ℚ pb.gen)) :=
          Polynomial.aeval_algHom_apply ι pb.gen (minpoly ℚ pb.gen)
      _ = ι 0 := by rw [minpoly.aeval]
      _ = 0 := map_zero ι
  · -- Backward: eigenvalue of matrix → algebraic
    rintro ⟨n, M, hroot⟩
    rw [Matrix.charpoly_map] at hroot
    rw [Polynomial.IsRoot, Polynomial.eval_map_algebraMap] at hroot
    exact ⟨M.charpoly, M.charpoly_monic.ne_zero, hroot⟩

/-- A complex number is an algebraic integer if and only if it is an eigenvalue of a matrix
with integer entries. (Etingof Definition 5.2.2) -/
theorem Etingof.Definition5_2_2_integer
    (z : ℂ) :
    IsIntegral ℤ z ↔
    ∃ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℤ),
      (Matrix.charpoly (M.map (algebraMap ℤ ℂ))).IsRoot z := by
  constructor
  · -- Forward: integral → eigenvalue of left multiplication matrix
    intro hint
    -- Use the power basis for ℤ[z]
    let S := Algebra.adjoin ℤ ({z} : Set ℂ)
    let pb := Algebra.adjoin.powerBasis' hint
    let M := Algebra.leftMulMatrix pb.basis pb.gen
    refine ⟨_, M, ?_⟩
    rw [Matrix.charpoly_map, Polynomial.IsRoot, Polynomial.eval_map_algebraMap,
        charpoly_leftMulMatrix]
    let ι := IsScalarTower.toAlgHom ℤ S ℂ
    have hgen : ι pb.gen = z := by
      simp [ι, pb, Algebra.adjoin.powerBasis'_gen]
    calc Polynomial.aeval z (minpoly ℤ pb.gen)
        = Polynomial.aeval (ι pb.gen) (minpoly ℤ pb.gen) := by rw [hgen]
      _ = ι (Polynomial.aeval pb.gen (minpoly ℤ pb.gen)) :=
          Polynomial.aeval_algHom_apply ι pb.gen (minpoly ℤ pb.gen)
      _ = ι 0 := by rw [minpoly.aeval]
      _ = 0 := map_zero ι
  · -- Backward: eigenvalue of matrix → integral
    rintro ⟨n, M, hroot⟩
    rw [Matrix.charpoly_map] at hroot
    rw [Polynomial.IsRoot, Polynomial.eval_map_algebraMap] at hroot
    exact ⟨M.charpoly, M.charpoly_monic, hroot⟩
