import Mathlib.Algebra.Module.Injective

/-!
# Theorem 8.1.5: Equivalent characterizations of injective modules

The following properties of I are equivalent:

(i) If α : N → M is an injective morphism and ν : N → I is any morphism, then there exists
a morphism μ : M → I such that μ ∘ α = ν.

(ii) Any injective morphism α : I → M splits; i.e., there exists μ : M → I such that
μ ∘ α = id.

(iii) The functor Hom_A(?, I) on the category of A-modules is exact.

## Mathlib correspondence

`Module.Injective` captures condition (i) (the extension property). Baer's criterion
(`Module.Baer`) provides an equivalent characterization via extension from ideals.

- `Module.Injective` : the extension property (condition (i))
- `Module.Baer.iff_injective` : equivalence with Baer's criterion
-/

universe u v

/-- **Part (i) ↔ (ii)**: I is injective (extension property) if and only if every injection
from I splits.
(Etingof Theorem 8.1.5, equivalence of conditions (i) and (ii)) -/
theorem Etingof.Theorem_8_1_5_i_iff_ii
    (R : Type u) [Ring R]
    (I : Type v) [AddCommGroup I] [Module R I] [Small.{v} R] :
    Module.Injective R I ↔
      (∀ {M : Type v} [AddCommGroup M] [Module R M]
        (f : I →ₗ[R] M), Function.Injective f →
          ∃ g : M →ₗ[R] I, g.comp f = LinearMap.id) := by
  sorry

/-- **Baer's criterion**: I is injective if and only if every linear map from an ideal of R
to I extends to a linear map from R to I.
(Etingof Theorem 8.1.5, relates to the extension property) -/
theorem Etingof.Theorem_8_1_5_Baer
    (R : Type u) [Ring R]
    (I : Type v) [AddCommGroup I] [Module R I] [Small.{v} R] :
    Module.Injective R I ↔ Module.Baer R I := by
  sorry
