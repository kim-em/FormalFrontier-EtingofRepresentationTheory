import Mathlib

/-!
# Proposition 5.19.1: Image of GL(V) spans the centralizer algebra

The image of GL(V) in End(V⊗ⁿ) spans B (the centralizer algebra of the
Sₙ-action). This follows from the fact that the span of g⊗ⁿ for g ∈ GL(V)
equals the span of b⊗ⁿ for all b ∈ End(V), using a polynomial argument.

## Mathlib correspondence

Requires tensor power and Schur-Weyl duality infrastructure not yet in Mathlib.
-/

/-- The image of GL(V) in End(V⊗ⁿ) spans the centralizer algebra B of the
Sₙ-action on V⊗ⁿ. (Etingof Proposition 5.19.1) -/
theorem Etingof.Proposition5_19_1
    {k : Type*} [Field k] [IsAlgClosed k]
    {V : Type*} [AddCommGroup V] [Module k V] [Module.Finite k V]
    (n : ℕ) :
    -- The span of {g⊗ⁿ | g ∈ GL(V)} equals the centralizer of Sₙ in End(V⊗ⁿ)
    (sorry : Prop) := by
  sorry
