import Mathlib
import EtingofRepresentationTheory.Chapter5.Definition5_12_1
import EtingofRepresentationTheory.Chapter5.Theorem5_12_2
import EtingofRepresentationTheory.Chapter5.Definition5_14_2

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
The dominance order on partitions is defined locally as Mathlib does not have it.
The permutation module is defined as the free ℂ-module on left cosets S_n/S_λ.
-/

namespace Etingof

/-! ## Dominance order on partitions -/

/-- The dominance order on partitions of n: μ dominates λ (μ ≥ λ) if for all k,
the sum of the first k parts of μ (in non-increasing order) is at least the sum
of the first k parts of λ. -/
def Nat.Partition.Dominates {n : ℕ} (mu la : Nat.Partition n) : Prop :=
  ∀ k : ℕ, (la.sortedParts.take k).sum ≤ (mu.sortedParts.take k).sum

/-- Strict dominance: μ strictly dominates λ when μ dominates λ and μ ≠ λ. -/
def Nat.Partition.StrictDominates {n : ℕ} (mu la : Nat.Partition n) : Prop :=
  Nat.Partition.Dominates mu la ∧ mu ≠ la

/-! ## Permutation module -/

/-- The permutation module U_λ = ℂ[S_n/S_λ], the free ℂ-module on left cosets of the
Young subgroup (row subgroup) S_λ = S_{λ₁} × ... × S_{λ_p}.
S_n acts by left multiplication on cosets.
(Etingof, Section 5.14) -/
noncomputable abbrev PermutationModule (n : ℕ) (la : Nat.Partition n) :=
  (Equiv.Perm (Fin n) ⧸ RowSubgroup n la) →₀ ℂ

/-- The ℂ[S_n]-module structure on the permutation module U_λ, where σ ∈ S_n acts
by left multiplication on cosets: σ · (gS_λ) = (σg)S_λ, extended linearly. -/
noncomputable instance PermutationModule.instModule (n : ℕ) (la : Nat.Partition n) :
    Module (SymGroupAlgebra n) (PermutationModule n la) :=
  Module.compHom _ (Representation.ofMulAction ℂ (Equiv.Perm (Fin n))
    (Equiv.Perm (Fin n) ⧸ RowSubgroup n la)).asAlgebraHom.toRingHom

/-! ## Proposition 5.14.1 -/

/-- Hom_{S_n}(U_λ, V_μ) = 0 when λ strictly dominates μ (i.e., μ < λ).
Equivalently, there are no nonzero S_n-equivariant maps from U_λ to V_μ.
(Etingof Proposition 5.14.1, vanishing part) -/
theorem Proposition5_14_1_vanishing
    (n : ℕ) (la mu : Nat.Partition n)
    (hdom : Nat.Partition.StrictDominates la mu) :
    ∀ f : PermutationModule n la →ₗ[SymGroupAlgebra n] ↥(SpechtModule n mu), f = 0 := by
  sorry

/-- dim Hom_{S_n}(U_λ, V_λ) = 1. The space of S_n-equivariant maps from the
permutation module U_λ to the Specht module V_λ is one-dimensional.
(Etingof Proposition 5.14.1, diagonal part) -/
theorem Proposition5_14_1_diagonal
    (n : ℕ) (la : Nat.Partition n) :
    Module.finrank ℂ (PermutationModule n la →ₗ[SymGroupAlgebra n] ↥(SpechtModule n la)) = 1 := by
  sorry

end Etingof
