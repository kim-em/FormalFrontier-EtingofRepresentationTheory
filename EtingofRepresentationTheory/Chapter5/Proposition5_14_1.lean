import Mathlib

/-!
# Proposition 5.14.1: Kostka Decomposition

For partitions λ, μ of n:
- Hom_{S_n}(U_λ, V_μ) = 0 if μ < λ (dominance order)
- dim Hom_{S_n}(U_λ, V_λ) = 1

Thus U_λ = ⊕_{μ ≥ λ} K_{μλ} · V_μ where K_{μλ} are the Kostka numbers.

Here U_λ = Ind_{S_{λ₁} × ... × S_{λ_p}}^{S_n} (trivial) is the permutation
module associated to partition λ.

## Mathlib correspondence

Requires Specht modules (Theorem 5.12.2), Young tableaux, and Kostka numbers.
-/

/-- Hom_{S_n}(U_λ, V_μ) = 0 when μ < λ in dominance order.
(Etingof Proposition 5.14.1, vanishing part) -/
theorem Etingof.Proposition5_14_1_vanishing
    (n : ℕ) (la mu : Nat.Partition n)
    (hlt : sorry)  -- mu < la in dominance order
    :
    -- Hom_{S_n}(U_la, V_mu) = 0
    (sorry : Prop) := by
  sorry

/-- dim Hom_{S_n}(U_λ, V_λ) = 1.
(Etingof Proposition 5.14.1, diagonal part) -/
theorem Etingof.Proposition5_14_1_diagonal
    (n : ℕ) (la : Nat.Partition n) :
    -- dim Hom_{S_n}(U_λ, V_λ) = 1
    (sorry : Prop) := by
  sorry
