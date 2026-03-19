import EtingofRepresentationTheory.Chapter9.Definition9_7_1
import EtingofRepresentationTheory.Chapter9.Definition9_7_2
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.Equivalence
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.SimpleModule.Rank

universe u v

/-!
# Corollary 9.7.3: Unique basic algebra

(i) Any finite abelian category 𝒞 over k is equivalent to the category of finite
dimensional modules over a unique (up to isomorphism) basic algebra B(𝒞).

(ii) Any finite dimensional algebra A over k is Morita equivalent to a unique
basic algebra B_A, and dim B_A ≤ dim A.

## Mathlib correspondence

Part (i) combines Theorem 9.6.4 (Morita equivalence via progenerator) with the
theory of basic algebras from §9.7.

Part (ii) uses the `Etingof.MoritaEquivalent` and `Etingof.IsBasicAlgebra`
definitions from this project.

## Proof status

All three parts require Wedderburn-Artin decomposition and Morita structure theory
(idempotent extraction, corner ring construction) which are not yet available in Mathlib.
Helper lemmas for `MoritaEquivalent` (reflexivity, symmetry, transitivity) and
`IsBasicAlgebra` (field is basic) are proved below.
-/

variable (k : Type*) [Field k]

/-! ## Helper lemmas for MoritaEquivalent -/

/-- Morita equivalence is reflexive. -/
lemma Etingof.MoritaEquivalent.refl (A : Type u) [Ring A] : Etingof.MoritaEquivalent A A :=
  ⟨CategoryTheory.Equivalence.refl⟩

/-- Morita equivalence is symmetric. -/
lemma Etingof.MoritaEquivalent.symm {A : Type u} [Ring A] {B : Type u} [Ring B]
    (h : Etingof.MoritaEquivalent A B) : Etingof.MoritaEquivalent B A :=
  h.map CategoryTheory.Equivalence.symm

/-- Morita equivalence is transitive. -/
lemma Etingof.MoritaEquivalent.trans {A : Type u} [Ring A] {B : Type u} [Ring B]
    {C : Type u} [Ring C]
    (h₁ : Etingof.MoritaEquivalent A B) (h₂ : Etingof.MoritaEquivalent B C) :
    Etingof.MoritaEquivalent A C := by
  obtain ⟨e₁⟩ := h₁
  obtain ⟨e₂⟩ := h₂
  exact ⟨e₁.trans e₂⟩

/-! ## Helper lemmas for IsBasicAlgebra -/

/-- A field k is a basic algebra over itself: every simple k-module is 1-dimensional. -/
lemma Etingof.isBasicAlgebra_field : Etingof.IsBasicAlgebra k k := by
  intro M _ hModA hSimp hModK hST
  -- The two Module k M instances (from A = k and from the explicit k-module) must agree
  -- via the IsScalarTower k k M condition
  have : hModA = hModK := by
    ext c m
    have h := hST.1 c (1 : k) m
    simp only [smul_eq_mul, mul_one, one_smul] at h
    exact h
  subst this
  exact isSimpleModule_iff_finrank_eq_one.mp hSimp

/-- **Corollary 9.7.3(i)**: Any finite-dimensional algebra A over k is Morita equivalent
to some basic algebra B. That is, there exists a basic k-algebra B such that the module
categories of A and B are equivalent.
(Etingof Corollary 9.7.3(i), algebra version) -/
theorem Etingof.Corollary_9_7_3_i
    (A : Type u) [Ring A] [Algebra k A] [Module.Finite k A] :
    ∃ (B : Type u) (_ : Ring B) (_ : Algebra k B) (_ : Module.Finite k B),
      Etingof.IsBasicAlgebra k B ∧ Etingof.MoritaEquivalent A B := by
  -- Proof requires: Wedderburn-Artin decomposition of A/rad(A) ≅ ∏ Matₙᵢ(k),
  -- extraction of primitive idempotents e₁,...,eₘ, construction of B = eAe
  -- where e = e₁ + ⋯ + eₘ, and showing B is basic and Morita equivalent to A
  -- via Theorem 9.6.4 (progenerator Ae).
  sorry

/-- **Corollary 9.7.3(i), uniqueness**: The basic algebra B from part (i) is unique
up to isomorphism. If B₁ and B₂ are both basic algebras that are Morita equivalent
to A, then B₁ ≅ B₂ as k-algebras.
(Etingof Corollary 9.7.3(i), uniqueness) -/
theorem Etingof.Corollary_9_7_3_i_unique
    (A : Type u) [Ring A] [Algebra k A] [Module.Finite k A]
    (B₁ : Type u) [Ring B₁] [Algebra k B₁] [Module.Finite k B₁]
    (B₂ : Type u) [Ring B₂] [Algebra k B₂] [Module.Finite k B₂]
    (hB₁ : Etingof.IsBasicAlgebra k B₁) (hB₂ : Etingof.IsBasicAlgebra k B₂)
    (h₁ : Etingof.MoritaEquivalent A B₁) (h₂ : Etingof.MoritaEquivalent A B₂) :
    Nonempty (B₁ ≃ₐ[k] B₂) := by
  -- Proof requires: Morita equivalence preserves the set of simple modules (up to iso).
  -- For basic algebras, simple modules are 1-dimensional, so B₁ and B₂ have isomorphic
  -- simple module categories. A basic algebra is determined up to isomorphism by its
  -- module category (it equals End(⊕ simples)^op), giving B₁ ≅ B₂.
  sorry

/-- **Corollary 9.7.3(ii)**: For any finite-dimensional algebra A over k, its basic
algebra B_A satisfies dim_k B_A ≤ dim_k A.
(Etingof Corollary 9.7.3(ii)) -/
theorem Etingof.Corollary_9_7_3_ii
    (A : Type u) [Ring A] [Algebra k A] [Module.Finite k A]
    (B : Type u) [Ring B] [Algebra k B] [Module.Finite k B]
    (hB : Etingof.IsBasicAlgebra k B) (hMor : Etingof.MoritaEquivalent A B) :
    Module.finrank k B ≤ Module.finrank k A := by
  -- Proof requires: Morita's theorem implies B ≅ eAe for some full idempotent e ∈ A.
  -- As a corner ring, eAe embeds into A as a k-subspace, giving dim(eAe) ≤ dim(A).
  sorry
