import Mathlib

/-!
# Definition 5.2.1: Algebraic Numbers and Algebraic Integers (Polynomial Characterization)

A complex number z is an **algebraic number** if it is a root of a nonzero polynomial
with rational coefficients (equivalently, a root of a monic polynomial with rational coefficients).

A complex number z is an **algebraic integer** if it is a root of a monic polynomial
with integer coefficients.

## Mathlib correspondence

Exact match: `IsAlgebraic ℚ z` for algebraic numbers, `IsIntegral ℤ z` for algebraic integers.
-/

/-- Algebraic numbers: z ∈ ℂ is algebraic if it is a root of a nonzero polynomial
with rational coefficients. In Mathlib this is `IsAlgebraic ℚ z`.
(Etingof Definition 5.2.1) -/
theorem Etingof.Definition5_2_1_algebraic_number (z : ℂ) :
    IsAlgebraic ℚ z ↔ ∃ p : Polynomial ℚ, p ≠ 0 ∧ (Polynomial.aeval (R := ℚ) z) p = 0 :=
  Iff.rfl

/-- Algebraic integers: z ∈ ℂ is an algebraic integer if it is a root of a monic polynomial
with integer coefficients. In Mathlib this is `IsIntegral ℤ z`.
(Etingof Definition 5.2.1) -/
theorem Etingof.Definition5_2_1_algebraic_integer (z : ℂ) :
    IsIntegral ℤ z ↔ ∃ p : Polynomial ℤ, p.Monic ∧ (Polynomial.aeval (R := ℤ) z) p = 0 := by
  simp [IsIntegral, RingHom.IsIntegralElem, Polynomial.aeval_def]
