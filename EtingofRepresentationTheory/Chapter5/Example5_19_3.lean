import EtingofRepresentationTheory.Chapter5.Theorem5_18_4

/-!
# Example 5.19.3: Schur Functors for Special Partitions

If λ = (n), then Lλ = SⁿV (symmetric power).
If λ = (1ⁿ), then Lλ = ∧ⁿV (exterior power).
These are irreducible GL(V)-representations (except ∧ⁿV = 0 when n > dim V).

## Mathlib correspondence

Uses `Mathlib.LinearAlgebra.ExteriorAlgebra` and symmetric powers.
-/

open scoped TensorProduct
open Etingof

variable (k : Type*) [Field k]
  (V : Type*) [AddCommGroup V] [Module k V] [Module.Finite k V]
  (n : ℕ)

/-- The Sₙ-invariant submodule of V⊗ⁿ: tensors fixed by all permutations.
These are the symmetric tensors, i.e., the subspace where σ · x = x for all σ ∈ Sₙ. -/
noncomputable def Etingof.symInvariants :
    Submodule k (TensorPower k V n) :=
  ⨅ σ : Equiv.Perm (Fin n),
    LinearMap.ker ((symGroupAction k V n σ).toLinearMap - LinearMap.id)

/-- The Sₙ-antisymmetric submodule of V⊗ⁿ: tensors where σ · x = sign(σ) · x
for all σ ∈ Sₙ. These are the alternating tensors. -/
noncomputable def Etingof.symAntisymmetric :
    Submodule k (TensorPower k V n) :=
  ⨅ σ : Equiv.Perm (Fin n),
    LinearMap.ker ((symGroupAction k V n σ).toLinearMap -
      ((Equiv.Perm.sign σ : ℤ) : k) • LinearMap.id)

/-- For the partition λ = (n), the Schur functor L_{(n)} equals SⁿV
(the n-th symmetric power). Specifically, the Sₙ-invariant subspace of
V⊗ⁿ (symmetric tensors, where σ · x = x for all σ) is isomorphic to
the n-th symmetric power Sym[k]^n V.

The GL(V)-action on SⁿV is given by g · (v₁ ⊙ ... ⊙ vₙ) = (gv₁) ⊙ ... ⊙ (gvₙ).
(Etingof Example 5.19.3) -/
theorem Etingof.Example5_19_3_symmetric
    {k : Type} [Field k] [IsAlgClosed k]
    {V : Type} [AddCommGroup V] [Module k V] [Module.Finite k V]
    (n : ℕ) :
    Nonempty (symInvariants k V n ≃ₗ[k] SymmetricPower k (Fin n) V) := by
  sorry

/-- For the partition λ = (1ⁿ), the Schur functor L_{(1ⁿ)} equals ∧ⁿV
(the n-th exterior power), which is zero when n > dim V.

The Sₙ-antisymmetric subspace of V⊗ⁿ (alternating tensors, where
σ · x = sign(σ) · x for all σ) is isomorphic to the n-th exterior
power ⋀[k]^n V.

The GL(V)-action on ∧ⁿV is given by g · (v₁ ∧ ... ∧ vₙ) = (gv₁) ∧ ... ∧ (gvₙ).
(Etingof Example 5.19.3) -/
theorem Etingof.Example5_19_3_exterior
    {k : Type*} [Field k] [IsAlgClosed k]
    {V : Type*} [AddCommGroup V] [Module k V] [Module.Finite k V]
    (n : ℕ) :
    Nonempty (symAntisymmetric k V n ≃ₗ[k] ⋀[k]^n V) := by
  sorry
