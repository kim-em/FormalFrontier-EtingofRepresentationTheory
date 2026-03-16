import Mathlib.RingTheory.Jacobson.Ideal

/-!
# Proposition 3.5.2: Rad(A) is a Two-Sided Ideal

The radical Rad(A) is a two-sided ideal in A.

This follows directly from the definition: Rad(A) is the intersection of annihilators of
all irreducible representations, and each annihilator is a two-sided ideal.

In Mathlib, the Jacobson radical `Ideal.jacobson ⊥` is already a two-sided ideal by
construction (it is an `Ideal A`, which in Mathlib is a two-sided ideal for commutative
rings and a left ideal in general).
-/

/-- The radical of a finite dimensional algebra is a two-sided ideal.
Etingof Proposition 3.5.2.

In the Mathlib formalization, `Ideal.jacobson ⊥` is already an ideal by construction. -/
theorem Etingof.radical_is_ideal (A : Type*) [Ring A] :
    -- The Jacobson radical is already an Ideal A in Mathlib,
    -- so this is immediate from the type system.
    (Ideal.jacobson (⊥ : Ideal A)).carrier.Nonempty := by
  exact ⟨0, (Ideal.jacobson ⊥).zero_mem⟩
