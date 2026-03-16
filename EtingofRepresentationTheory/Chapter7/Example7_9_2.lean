import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.CategoryTheory.Linear.LinearFunctor

/-!
# Example 7.9.2: Additive and k-linear Functors in Representation Theory

The functors Ind_K^G, Res_K^G, Hom_G(V, ?) in the theory of group representations
over a field k are additive and k-linear.

## Mathlib correspondence

The restriction of scalars functor `ModuleCat.restrictScalars` is shown to be
additive and linear in Mathlib's `ChangeOfRings.lean`. These instances apply to
the representation-theoretic restriction functor since `Rep k G` is built on
`ModuleCat k`.
-/

open CategoryTheory
open scoped ModuleCat.Algebra

/-- The restriction of scalars functor along a ring homomorphism is additive.
This underlies the fact that Res_K^G is additive (Etingof Example 7.9.2). -/
instance Etingof.restrictScalars_additive
    {R S : Type*} [Ring R] [Ring S] (f : R →+* S) :
    Functor.Additive (ModuleCat.restrictScalars f) :=
  inferInstance

/-- The restriction of scalars functor along an algebra homomorphism is linear.
This underlies the fact that Res_K^G is k-linear (Etingof Example 7.9.2). -/
instance Etingof.restrictScalars_linear
    {R₀ R S : Type*} [CommSemiring R₀] [Ring R] [Ring S]
    [Algebra R₀ R] [Algebra R₀ S] (f : R →ₐ[R₀] S) :
    Functor.Linear R₀ (ModuleCat.restrictScalars f.toRingHom) :=
  inferInstance
