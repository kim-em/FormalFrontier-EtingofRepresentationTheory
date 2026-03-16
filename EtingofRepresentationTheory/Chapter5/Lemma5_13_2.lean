import Mathlib

/-!
# Lemma 5.13.2: Young Projector Vanishing for Distinct Partitions

If λ > μ in the lexicographic (dominance) order on partitions of n, then
a_λ · ℂ[S_n] · b_μ = 0. The proof uses the pigeonhole principle: if λ > μ,
then for any Young tableaux of shapes λ and μ, some row of the λ-tableau
must contain two elements that belong to the same column of the μ-tableau.

## Mathlib correspondence

Requires Young symmetrizer infrastructure and the dominance order on partitions.
-/

/-- If λ > μ (dominance order), then a_λ · x · b_μ = 0 for all x ∈ ℂ[S_n].
(Etingof Lemma 5.13.2) -/
theorem Etingof.Lemma5_13_2
    (n : ℕ) (la mu : Nat.Partition n)
    (hlt : sorry) -- la > mu in dominance order
    (x : MonoidAlgebra ℂ (Equiv.Perm (Fin n))) :
    -- a_λ * x * b_μ = 0
    (sorry : Prop) := by
  sorry
