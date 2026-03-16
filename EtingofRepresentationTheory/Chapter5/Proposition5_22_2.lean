import Mathlib

/-!
# Proposition 5.22.2: Twisting by Determinant

L_{λ + 1^N} ≅ Lλ ⊗ ∧^N V, where 1^N = (1, 1, …, 1) ∈ ℤ^N.

This follows from the inclusion Lλ ⊗ ∧^N V ⊂ V^{⊗(n+N)} and the
uniqueness of the component with the given character.

## Mathlib correspondence

Requires exterior power and Schur functor infrastructure.
-/

/-- Twisting by determinant: L_{λ+1^N} ≅ Lλ ⊗ ∧^N V.
(Etingof Proposition 5.22.2) -/
theorem Etingof.Proposition5_22_2
    {k : Type*} [Field k] [IsAlgClosed k]
    {V : Type*} [AddCommGroup V] [Module k V] [Module.Finite k V]
    (N : ℕ) (lam : Fin N → ℕ) :
    -- L_{λ + (1,1,...,1)} ≅ Lλ ⊗ ∧^N V as GL(V)-representations
    (sorry : Prop) := by
  sorry
