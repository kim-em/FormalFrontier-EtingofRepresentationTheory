import Mathlib

/-!
# Definition 5.14.2: Kostka Numbers

The **Kostka number** K_{μλ} is defined as the number of semistandard Young tableaux
of shape μ with content λ. Equivalently, it is the multiplicity of the Specht
module V_μ in the permutation module U_λ:

  U_λ = ⊕_{μ ≥ λ} K_{μλ} · V_μ

Kostka numbers satisfy K_{λλ} = 1 and K_{μλ} = 0 when μ < λ in dominance order.

## Mathlib correspondence

Mathlib has `SemistandardYoungTableau` which can be used to define Kostka numbers
as the cardinality of semistandard tableaux of given shape and content.
-/

/-- The Kostka number K_{μ,λ}: number of semistandard Young tableaux of shape μ
with content λ. (Etingof Definition 5.14.2) -/
noncomputable def Etingof.KostkaNumber (n : ℕ) (mu la : Nat.Partition n) : ℕ :=
  sorry
