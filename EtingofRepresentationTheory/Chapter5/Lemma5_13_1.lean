import Mathlib

/-!
# Lemma 5.13.1: Young Projector Linear Functional

For x ∈ ℂ[S_n], we have a_λ · x · b_λ = ℓ_λ(x) · c_λ, where ℓ_λ is a linear
functional on ℂ[S_n]. Here a_λ = Σ_{g ∈ P_λ} g and b_λ = Σ_{g ∈ Q_λ} sign(g) · g.

The proof proceeds by showing that when a row element g and column element h
place two elements from the same row into the same column, the contributions
cancel by sign.

## Mathlib correspondence

Requires Young symmetrizer infrastructure (Definition 5.12.1).
-/

/-- For x ∈ ℂ[S_n], a_λ · x · b_λ is a scalar multiple of c_λ = a_λ · b_λ.
(Etingof Lemma 5.13.1) -/
theorem Etingof.Lemma5_13_1
    (n : ℕ) (la : Nat.Partition n)
    (x : MonoidAlgebra ℂ (Equiv.Perm (Fin n))) :
    -- a_λ * x * b_λ = ℓ_λ(x) * c_λ for some linear functional ℓ_λ
    (sorry : Prop) := by
  sorry
