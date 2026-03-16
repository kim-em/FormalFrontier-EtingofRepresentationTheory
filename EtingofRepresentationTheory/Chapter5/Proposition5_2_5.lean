import Mathlib

/-!
# Proposition 5.2.5: Algebraic Integers in ℚ are Exactly ℤ

The intersection of the algebraic integers with ℚ is ℤ:
  Ā ∩ ℚ = ℤ

That is, a rational number is an algebraic integer if and only if it is an integer.

## Mathlib correspondence

This is `isIntegral_iff` or related results in `Mathlib.RingTheory.Algebraic`.
-/

/-- A rational number is an algebraic integer if and only if it is an integer.
Equivalently, Ā ∩ ℚ = ℤ. (Etingof Proposition 5.2.5) -/
theorem Etingof.Proposition5_2_5 (q : ℚ) :
    IsIntegral ℤ (algebraMap ℚ ℂ q) ↔ ∃ n : ℤ, q = n := by
  rw [isIntegral_algebraMap_iff (algebraMap ℚ ℂ).injective]
  constructor
  · intro hq
    have := IsIntegrallyClosed.isIntegral_iff.mp hq
    obtain ⟨r, hr⟩ := this
    exact ⟨r, by exact_mod_cast hr.symm⟩
  · rintro ⟨n, rfl⟩
    exact isIntegral_algebraMap
