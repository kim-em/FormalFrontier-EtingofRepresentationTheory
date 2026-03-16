import Mathlib

/-!
# Theorem 5.12.2: Classification of Irreducible Representations of S_n (Specht Modules)

For each partition λ of n, the subspace V_λ = ℂ[S_n] · c_λ is an irreducible
representation of S_n (where c_λ is the Young symmetrizer). Moreover, every
irreducible representation of S_n over ℂ is isomorphic to V_λ for a unique
partition λ. These representations are called **Specht modules**.

## Mathlib correspondence

This is a fundamental classification theorem. Mathlib has `Nat.Partition` and
basic representation theory, but the Specht module construction and its
irreducibility are not yet formalized.
-/

/-- The Specht module V_λ = ℂ[S_n] · c_λ is an irreducible representation of S_n.
(Etingof Theorem 5.12.2, part 1) -/
theorem Etingof.Theorem5_12_2_irreducible
    (n : ℕ) (la : Nat.Partition n) :
    -- V_λ is an irreducible representation of S_n
    (sorry : Prop) := by
  sorry

/-- Every irreducible representation of S_n over ℂ is isomorphic to some Specht module V_λ.
(Etingof Theorem 5.12.2, part 2) -/
theorem Etingof.Theorem5_12_2_classification
    (n : ℕ) :
    -- Every irreducible ℂ-representation of S_n is isomorphic to V_λ for some partition λ
    (sorry : Prop) := by
  sorry
