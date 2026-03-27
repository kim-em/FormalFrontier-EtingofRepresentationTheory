import EtingofRepresentationTheory.Chapter5.Theorem5_18_4

/-!
# Corollary 5.19.2: Schur-Weyl Decomposition

As a representation of Sₙ × GL(V), V⊗ⁿ decomposes as
  V⊗ⁿ ≅ ⊕_λ Vλ ⊗ Lλ
where Vλ are irreducible Sₙ-representations (Specht modules) and
Lλ = Hom_{Sₙ}(Vλ, V⊗ⁿ) are distinct irreducible GL(V)-representations (or zero).

## Mathlib correspondence

Requires Schur-Weyl duality, which is not yet in Mathlib.
-/

open scoped TensorProduct
open Etingof

universe u v

/-- Schur-Weyl decomposition: as an Sₙ × GL(V) representation,
V⊗ⁿ ≅ ⊕_λ Vλ ⊗ Lλ where the sum ranges over partitions of n.
Here Vλ are irreducible Sₙ-representations (Specht modules) and
Lλ = Hom_{Sₙ}(Vλ, V⊗ⁿ) are distinct irreducible GL(V)-representations
(or zero when the partition has more parts than dim V).

This refines Theorem 5.18.4(iii) by identifying the indexing set
as partitions of n.
(Etingof Corollary 5.19.2) -/
theorem Etingof.Corollary5_19_2
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {V : Type v} [AddCommGroup V] [Module k V] [Module.Finite k V]
    (n : ℕ) (hN : n ≤ Module.finrank k V) :
    ∃ (S : Nat.Partition n → Type (max u v))
      (L : Nat.Partition n → Type u)
      (_ : ∀ p, AddCommGroup (S p)) (_ : ∀ p, Module k (S p))
      (_ : ∀ p, AddCommGroup (L p)) (_ : ∀ p, Module k (L p)),
      Nonempty (TensorPower k V n ≃ₗ[k]
        DirectSum (Nat.Partition n) (fun p => S p ⊗[k] L p)) :=
  Theorem5_18_4_partition_decomposition k V n hN
