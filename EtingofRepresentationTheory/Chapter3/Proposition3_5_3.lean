import Mathlib.RingTheory.Jacobson.Ideal
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Nilpotent.Defs

/-!
# Proposition 3.5.3: Rad(A) is the Largest Nilpotent Two-Sided Ideal

Let A be a finite dimensional algebra.

(i) Let I be a nilpotent two-sided ideal in A; i.e., I^n = 0 for some n.
    Then I ⊆ Rad(A).

(ii) Rad(A) is a nilpotent ideal. Thus, Rad(A) is the largest nilpotent
     two-sided ideal in A.
-/

/-- Any nilpotent two-sided ideal is contained in the radical.
Etingof Proposition 3.5.3(i). -/
theorem Etingof.nilpotent_ideal_le_radical (A : Type*) [Ring A]
    (I : Ideal A) (hI : IsNilpotent I) :
    I ≤ Ideal.jacobson ⊥ := by
  sorry

/-- The radical of a finite dimensional algebra is nilpotent.
Etingof Proposition 3.5.3(ii). -/
theorem Etingof.radical_is_nilpotent (k : Type*) (A : Type*)
    [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A] :
    IsNilpotent (Ideal.jacobson (⊥ : Ideal A)) := by
  sorry
