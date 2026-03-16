import Mathlib.CategoryTheory.Limits.Yoneda
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed

/-!
# Example 7.9.6: Exactness Properties of Standard Functors

(i) The functors Ind_K^G, Res_K^G are exact.
(ii) The functor Hom(X, ?) is left exact, but not necessarily right exact.
     Counterexample: 0 → ℤ → ℤ → ℤ/2ℤ → 0 with Hom(ℤ/2ℤ, ?).
(iii) The functor X ⊗_A - for a right A-module X is right exact but not
      necessarily left exact. Counterexample: tensor the above sequence by ℤ/2ℤ.

## Mathlib correspondence

Left exactness of Hom is available in Mathlib via `coyoneda_preservesLimits`.
The counterexamples for failure of right/left exactness are standard.
-/

open CategoryTheory CategoryTheory.Limits

/-- The Hom functor Hom(X, -) is left exact: it preserves finite limits.
This is the covariant Yoneda functor applied to X. (Etingof Example 7.9.6(ii))

In Mathlib, `coyoneda.obj (op X)` is the functor `Hom(X, -)`, and it preserves
all limits (hence in particular finite limits, making it left exact). -/
instance Etingof.hom_left_exact {C : Type*} [Category C] (X : C) :
    PreservesFiniteLimits (coyoneda.obj (Opposite.op X)) :=
  inferInstance

/-- The tensor product functor `X ⊗ -` is right exact: it preserves finite colimits.
(Etingof Example 7.9.6(iii))

In Mathlib, `ModuleCat R` is a monoidal closed category, so `tensorLeft X` (the functor
`X ⊗ -`) is a left adjoint of the internal hom functor. Left adjoints preserve all
colimits, hence in particular finite colimits, making the tensor functor right exact. -/
instance Etingof.tensor_right_exact {R : Type*} [CommRing R] (X : ModuleCat R) :
    PreservesFiniteColimits (MonoidalCategory.tensorLeft X) :=
  inferInstance
