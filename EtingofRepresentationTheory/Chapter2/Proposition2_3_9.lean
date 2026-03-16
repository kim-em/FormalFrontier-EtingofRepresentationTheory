import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.LinearAlgebra.Span.Basic

/-!
# Proposition 2.3.9: Schur's Lemma

Let V₁, V₂ be representations of an algebra A over any field F. Let φ : V₁ → V₂ be a
nonzero homomorphism of representations. Then:

(i) If V₁ is irreducible, φ is injective.
(ii) If V₂ is irreducible, φ is surjective.

Thus, if both V₁ and V₂ are irreducible, φ is an isomorphism.

## Mathlib correspondence

Exact match. Schur's lemma is available in Mathlib via `IsSimpleModule` and properties
of module homomorphisms between simple modules.
-/

/-- Schur's lemma, part (i): A nonzero homomorphism from an irreducible representation
is injective. (Etingof Proposition 2.3.9(i)) -/
theorem Etingof.Proposition_2_3_9_injective
    {R : Type*} [Ring R]
    {V₁ : Type*} [AddCommGroup V₁] [Module R V₁] [IsSimpleModule R V₁]
    {V₂ : Type*} [AddCommGroup V₂] [Module R V₂]
    (φ : V₁ →ₗ[R] V₂) (hφ : φ ≠ 0) : Function.Injective φ := by
  sorry

/-- Schur's lemma, part (ii): A nonzero homomorphism to an irreducible representation
is surjective. (Etingof Proposition 2.3.9(ii)) -/
theorem Etingof.Proposition_2_3_9_surjective
    {R : Type*} [Ring R]
    {V₁ : Type*} [AddCommGroup V₁] [Module R V₁]
    {V₂ : Type*} [AddCommGroup V₂] [Module R V₂] [IsSimpleModule R V₂]
    (φ : V₁ →ₗ[R] V₂) (hφ : φ ≠ 0) : Function.Surjective φ := by
  sorry
