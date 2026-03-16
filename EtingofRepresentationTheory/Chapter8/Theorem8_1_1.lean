import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.FreeModule.Basic

/-!
# Theorem 8.1.1: Equivalent characterizations of projective modules

The following properties of P are equivalent:

(i) If α : M → N is a surjective morphism and ν : P → N is any morphism, then there exists
a morphism μ : P → M such that α ∘ μ = ν.

(ii) Any surjective morphism α : M → P splits; i.e., there exists μ : P → M such that
α ∘ μ = id.

(iii) There exists another A-module Q such that P ⊕ Q is a free A-module.

(iv) The functor Hom_A(P, ?) on the category of A-modules is exact.

## Mathlib correspondence

`Module.Projective` captures condition (i) (the lifting property). The equivalences with
splitting, direct summand of free, and exactness of Hom are available in various forms
across Mathlib's module theory.

- `Module.projective_lifting_property` : (i) follows from `Module.Projective`
- `Module.Projective.of_lifting_property` : `Module.Projective` follows from (i)
- `LinearMap.exists_rightInverse_of_surjective` : (ii) follows from `Module.Projective`
- `Module.Projective.iff_split` : equivalence with (iii)
-/

universe u v

/-- **Part (i) ↔ (ii)**: P is projective (lifting property) if and only if every surjection
onto P splits.
(Etingof Theorem 8.1.1, equivalence of conditions (i) and (ii)) -/
theorem Etingof.Theorem_8_1_1_i_iff_ii
    (R : Type u) [Ring R]
    (P : Type v) [AddCommGroup P] [Module R P] [Small.{v} R] :
    Module.Projective R P ↔
      (∀ {M : Type v} [AddCommGroup M] [Module R M]
        (f : M →ₗ[R] P), Function.Surjective f →
          ∃ g : P →ₗ[R] M, f.comp g = LinearMap.id) := by
  sorry

/-- **Part (i) ↔ (iii)**: P is projective if and only if P is a direct summand of a
free module.
(Etingof Theorem 8.1.1, equivalence of conditions (i) and (iii)) -/
theorem Etingof.Theorem_8_1_1_i_iff_iii
    (R : Type u) [Ring R]
    (P : Type v) [AddCommGroup P] [Module R P] :
    Module.Projective R P ↔
      (∃ (Q : Type (max u v)) (_ : AddCommGroup Q) (_ : Module R Q)
        (_ : Module.Free R Q) (i : P →ₗ[R] Q) (s : Q →ₗ[R] P),
          s.comp i = LinearMap.id) := by
  sorry
