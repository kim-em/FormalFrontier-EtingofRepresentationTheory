import Mathlib

/-!
# Lemma 4.10.3: Irreducibility of the Generic Determinant

For an n × n matrix Y with entries y_{ij} treated as independent variables,
det(Y) is an irreducible polynomial in the n² variables {y_{ij}}.

Proof sketch: Consider the specialization X = t · Id + Σᵢ xᵢ · E_{i,i+1 mod n}.
Then det(X) = tⁿ - (-1)ⁿ x₁ ··· xₙ, which is irreducible (e.g., by Eisenstein's
criterion with p = x₁). Since the specialization of det(Y) is irreducible,
det(Y) itself must be irreducible.

## Mathlib correspondence

Mathlib has `Matrix.det` and `MvPolynomial.Irreducible`. The irreducibility of
the generic determinant is not proved in Mathlib.
-/

/-- The determinant of a generic n × n matrix is an irreducible polynomial.
(Etingof Lemma 4.10.3) -/
theorem Etingof.Lemma4_10_3 (n : ℕ) (hn : 0 < n) :
    Irreducible (Matrix.det
      (fun (i j : Fin n) =>
        (MvPolynomial.X (i, j) : MvPolynomial (Fin n × Fin n) ℂ))) := by
  sorry
