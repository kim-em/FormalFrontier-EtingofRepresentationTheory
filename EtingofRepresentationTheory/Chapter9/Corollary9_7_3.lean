import EtingofRepresentationTheory.Chapter9.Definition9_7_1
import EtingofRepresentationTheory.Chapter9.Definition9_7_2
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.Equivalence
import Mathlib.LinearAlgebra.Dimension.Finrank

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
-/

variable (k : Type*) [Field k]

/-- **Corollary 9.7.3(i)**: Any finite-dimensional algebra A over k is Morita equivalent
to some basic algebra B. That is, there exists a basic k-algebra B such that the module
categories of A and B are equivalent.
(Etingof Corollary 9.7.3(i), algebra version) -/
theorem Etingof.Corollary_9_7_3_i
    (A : Type u) [Ring A] [Algebra k A] [Module.Finite k A] :
    ∃ (B : Type u) (_ : Ring B) (_ : Algebra k B) (_ : Module.Finite k B),
      Etingof.IsBasicAlgebra k B ∧ Etingof.MoritaEquivalent A B := by
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
  sorry

/-- **Corollary 9.7.3(ii)**: For any finite-dimensional algebra A over k, its basic
algebra B_A satisfies dim_k B_A ≤ dim_k A.
(Etingof Corollary 9.7.3(ii)) -/
theorem Etingof.Corollary_9_7_3_ii
    (A : Type u) [Ring A] [Algebra k A] [Module.Finite k A]
    (B : Type u) [Ring B] [Algebra k B] [Module.Finite k B]
    (hB : Etingof.IsBasicAlgebra k B) (hMor : Etingof.MoritaEquivalent A B) :
    Module.finrank k B ≤ Module.finrank k A := by
  sorry
