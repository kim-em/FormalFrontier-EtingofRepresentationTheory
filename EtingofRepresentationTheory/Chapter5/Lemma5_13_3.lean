import Mathlib

/-!
# Lemma 5.13.3: Young Symmetrizer as Idempotent

The Young symmetrizer c_λ is proportional to an idempotent:

  c_λ² = (n! / (|P_λ| · |Q_λ| · dim V_λ)) · c_λ

In particular, e_λ = (|P_λ| · |Q_λ| · dim V_λ / n!) · c_λ is an idempotent
in ℂ[S_n].

## Mathlib correspondence

Requires Young symmetrizer infrastructure (Definition 5.12.1) and
the Specht module dimension theory.
-/

/-- c_λ² is a scalar multiple of c_λ, so c_λ is proportional to an idempotent.
(Etingof Lemma 5.13.3) -/
theorem Etingof.Lemma5_13_3
    (n : ℕ) (la : Nat.Partition n) :
    -- c_λ² = (n! / (|P_λ| · |Q_λ| · dim V_λ)) · c_λ
    (sorry : Prop) := by
  sorry
