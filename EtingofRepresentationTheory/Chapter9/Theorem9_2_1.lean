import EtingofRepresentationTheory.Chapter9.Definition9_2_2
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.Artinian.Ring

/-!
# Theorem 9.2.1: Classification of indecomposable projective modules

Let A be a finite dimensional algebra over a field k. Let M₁, …, Mₘ be the irreducible
representations of A. Then:

(i) For each i there exists a unique (up to isomorphism) indecomposable finitely generated
projective module Pᵢ, called the **projective cover** of Mᵢ, such that
dim Hom_A(Pᵢ, Mⱼ) = δᵢⱼ.

(ii) A ≅ ⊕ᵢ (dim Mᵢ) · Pᵢ (as A-modules).

(iii) Any indecomposable finitely generated projective A-module is isomorphic to some Pᵢ.

## Mathlib correspondence

Uses Krull–Schmidt theorem (partially in Mathlib), Nakayama's lemma
(`Ideal.eq_top_of_isUnit_of_forall_mem`), and lifting of idempotents.

## Formalization approach

The three parts are stated as separate theorems sharing common hypotheses:
a finite-dimensional algebra A over a field k, with a finite indexing type ι for the
isomorphism classes of simple modules, and a family of simple modules indexed by ι.

Part (i) is an existence statement producing the projective covers.
Part (ii) states that A (as a module over itself) decomposes as the direct sum.
Part (iii) states that any indecomposable f.g. projective is isomorphic to some Pᵢ.
-/

open scoped DirectSum

variable {k : Type*} [Field k]
variable {A : Type*} [Ring A] [Algebra k A] [Module.Finite k A]

/-- **Theorem 9.2.1(i)**: Existence of projective covers with the Kronecker delta Hom property.

For each simple module Mᵢ over a finite-dimensional algebra A, there exists an indecomposable
finitely generated projective module Pᵢ such that dim Hom_A(Pᵢ, Mⱼ) = δᵢⱼ.

More precisely: given a finite family of pairwise non-isomorphic simple A-modules `M`,
for each index `i` there exists a type `P i` carrying the structure of an indecomposable
projective A-module, together with a proof that dim_k Hom_A(P i, M j) = if i = j then 1 else 0.
(Etingof Theorem 9.2.1(i)) -/
theorem Etingof.Theorem_9_2_1_i
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ι → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module A (M i)]
    [∀ i, Module k (M i)] [∀ i, IsScalarTower k A (M i)]
    [∀ i, SMulCommClass A k (M i)]
    [∀ i, IsSimpleModule A (M i)]
    (hM : ∀ i j, Nonempty (M i ≃ₗ[A] M j) → i = j) :
    ∃ (P : ι → Type*)
      (_ : ∀ i, AddCommGroup (P i))
      (_ : ∀ i, Module A (P i))
      (_ : ∀ i, Module k (P i))
      (_ : ∀ i, IsScalarTower k A (P i))
      (_ : ∀ i, SMulCommClass A k (P i))
      (_ : ∀ i, Module.Projective A (P i))
      (_ : ∀ i, Module.Finite A (P i))
      (_ : ∀ i, Etingof.IsIndecomposableModule A (P i)),
      ∀ i j, Module.finrank k (P i →ₗ[A] M j) = if i = j then 1 else 0 := by
  sorry

/-- **Theorem 9.2.1(ii)**: Decomposition of the algebra as a module.

The algebra A, viewed as a left module over itself, decomposes as A ≅ ⊕ᵢ (dim Mᵢ) · Pᵢ.
That is, if `P` is the family of projective covers from part (i), then A is isomorphic
as an A-module to the direct sum over `i` of `(finrank k (M i))` copies of `P i`.
(Etingof Theorem 9.2.1(ii)) -/
theorem Etingof.Theorem_9_2_1_ii
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ι → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module A (M i)]
    [∀ i, Module k (M i)] [∀ i, IsScalarTower k A (M i)]
    [∀ i, SMulCommClass A k (M i)]
    [∀ i, IsSimpleModule A (M i)]
    (P : ι → Type*) [∀ i, AddCommGroup (P i)] [∀ i, Module A (P i)]
    [∀ i, Module k (P i)] [∀ i, IsScalarTower k A (P i)]
    [∀ i, SMulCommClass A k (P i)]
    [∀ i, Module.Projective A (P i)] [∀ i, Module.Finite A (P i)]
    [∀ i, Etingof.IsIndecomposableModule A (P i)]
    (hP : ∀ i j, Module.finrank k (P i →ₗ[A] M j) = if i = j then 1 else 0) :
    Nonempty (A ≃ₗ[A] ⨁ (i : ι), Fin (Module.finrank k (M i)) → P i) := by
  sorry

/-- **Theorem 9.2.1(iii)**: Completeness of the projective cover classification.

Any indecomposable finitely generated projective A-module is isomorphic to some Pᵢ.
This follows from the decomposition of A: any indecomposable projective must appear as
a direct summand of A (since A is projective and decomposes into the Pᵢ by part (ii)),
so by Krull–Schmidt it must be isomorphic to one of them.
(Etingof Theorem 9.2.1(iii)) -/
theorem Etingof.Theorem_9_2_1_iii
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ι → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module A (M i)]
    [∀ i, Module k (M i)] [∀ i, IsScalarTower k A (M i)]
    [∀ i, SMulCommClass A k (M i)]
    [∀ i, IsSimpleModule A (M i)]
    (P : ι → Type*) [∀ i, AddCommGroup (P i)] [∀ i, Module A (P i)]
    [∀ i, Module k (P i)] [∀ i, IsScalarTower k A (P i)]
    [∀ i, SMulCommClass A k (P i)]
    [∀ i, Module.Projective A (P i)] [∀ i, Module.Finite A (P i)]
    [∀ i, Etingof.IsIndecomposableModule A (P i)]
    (hP : ∀ i j, Module.finrank k (P i →ₗ[A] M j) = if i = j then 1 else 0)
    (Q : Type*) [AddCommGroup Q] [Module A Q]
    [Module.Projective A Q] [Module.Finite A Q] [Etingof.IsIndecomposableModule A Q] :
    ∃ i, Nonempty (Q ≃ₗ[A] P i) := by
  sorry
