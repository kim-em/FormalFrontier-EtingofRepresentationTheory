import Mathlib

/-!
# Proposition 5.2.3: Equivalence of Algebraic Number Definitions

Definitions 5.2.1 and 5.2.2 give equivalent characterizations of algebraic numbers
and algebraic integers. The proof uses:
- (5.2.1 → 5.2.2): The companion matrix of a polynomial has the roots as eigenvalues.
- (5.2.2 → 5.2.1): An eigenvalue of a matrix is a root of its characteristic polynomial.

## Mathlib correspondence

The equivalence follows from `Matrix.charpoly` and companion matrix theory.
-/

/-- Definitions 5.2.1 and 5.2.2 give equivalent characterizations of algebraic numbers:
z is a root of a rational polynomial iff z is an eigenvalue of a rational matrix.
(Etingof Proposition 5.2.3) -/
theorem Etingof.Proposition5_2_3_algebraic (z : ℂ) :
    (∃ p : Polynomial ℚ, p ≠ 0 ∧ Polynomial.aeval z p = 0) ↔
    (∃ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℚ),
      (Matrix.charpoly (M.map (algebraMap ℚ ℂ))).IsRoot z) := by
  constructor
  · -- Forward: algebraic → eigenvalue of a rational matrix
    -- Uses the left multiplication matrix on the power basis of ℚ⟮z⟯
    intro ⟨p, hp, hpz⟩
    have hint : IsIntegral ℚ z := isAlgebraic_iff_isIntegral.mp ⟨p, hp, hpz⟩
    let pb := IntermediateField.adjoin.powerBasis hint
    refine ⟨pb.dim, Algebra.leftMulMatrix pb.basis pb.gen, ?_⟩
    rw [Matrix.charpoly_map, charpoly_leftMulMatrix]
    rw [Polynomial.IsRoot, Polynomial.eval_map, ← Polynomial.aeval_def]
    rw [IntermediateField.adjoin.powerBasis_gen, IntermediateField.minpoly_gen]
    exact minpoly.aeval ℚ z
  · -- Backward: eigenvalue of rational matrix → algebraic
    -- The characteristic polynomial is nonzero and annihilates z
    rintro ⟨n, M, hM⟩
    rw [Matrix.charpoly_map] at hM
    exact ⟨M.charpoly, M.charpoly_monic.ne_zero, by
      rwa [Polynomial.IsRoot, Polynomial.eval_map, ← Polynomial.aeval_def] at hM⟩

/-- Definitions 5.2.1 and 5.2.2 give equivalent characterizations of algebraic integers:
z is a root of a monic integer polynomial iff z is an eigenvalue of an integer matrix.
(Etingof Proposition 5.2.3) -/
theorem Etingof.Proposition5_2_3_integer (z : ℂ) :
    (∃ p : Polynomial ℤ, p.Monic ∧ Polynomial.aeval z p = 0) ↔
    (∃ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℤ),
      (Matrix.charpoly (M.map (algebraMap ℤ ℂ))).IsRoot z) := by
  constructor
  · -- Forward: root of monic integer polynomial → eigenvalue of integer matrix
    -- Uses the left multiplication matrix on AdjoinRoot p, and the algebra hom to ℂ
    intro ⟨p, hp, hpz⟩
    let pb := AdjoinRoot.powerBasis' hp
    let M := Algebra.leftMulMatrix pb.basis pb.gen
    refine ⟨pb.dim, M, ?_⟩
    rw [Matrix.charpoly_map, charpoly_leftMulMatrix]
    rw [Polynomial.IsRoot, Polynomial.eval_map, ← Polynomial.aeval_def]
    -- Use the algebra hom φ : AdjoinRoot p →ₐ[ℤ] ℂ sending root p ↦ z
    have heval : p.eval₂ (↑(Algebra.ofId ℤ ℂ)) z = 0 := hpz
    let φ : AdjoinRoot p →ₐ[ℤ] ℂ :=
      AdjoinRoot.liftAlgHom p (Algebra.ofId ℤ ℂ) z heval
    -- pb.gen = root p, and φ(root p) = z
    have hgen : φ pb.gen = z :=
      AdjoinRoot.liftAlgHom_root (p := p) (Algebra.ofId ℤ ℂ) z heval
    rw [← hgen]
    have := Polynomial.aeval_algHom_apply φ pb.gen (minpoly ℤ pb.gen)
    rw [this, minpoly.aeval, map_zero]
  · -- Backward: eigenvalue of integer matrix → root of monic integer polynomial
    rintro ⟨n, M, hM⟩
    rw [Matrix.charpoly_map] at hM
    exact ⟨M.charpoly, M.charpoly_monic, by
      rwa [Polynomial.IsRoot, Polynomial.eval_map, ← Polynomial.aeval_def] at hM⟩
