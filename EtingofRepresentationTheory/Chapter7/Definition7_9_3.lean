import Mathlib.CategoryTheory.Limits.Preserves.Finite

/-!
# Definition 7.9.3: Left Exact, Right Exact, and Exact Functor

An additive functor F : C → D between abelian categories is:
- **Left exact** if 0 → X → Y → Z exact implies 0 → F(X) → F(Y) → F(Z) exact
- **Right exact** if X → Y → Z → 0 exact implies F(X) → F(Y) → F(Z) → 0 exact
- **Exact** if both left and right exact

## Mathlib correspondence

- Left exact: `CategoryTheory.Functor.PreservesFiniteLimits`
- Right exact: `CategoryTheory.Functor.PreservesFiniteColimits`
- Exact: both simultaneously
-/

/-- A left exact functor (preserves finite limits), in the sense of
Etingof Definition 7.9.3. This is `CategoryTheory.Limits.PreservesFiniteLimits`
in Mathlib. -/
abbrev Etingof.LeftExactFunctor {C : Type*} {D : Type*} [CategoryTheory.Category C]
    [CategoryTheory.Category D] (F : CategoryTheory.Functor C D) :=
  CategoryTheory.Limits.PreservesFiniteLimits F

/-- A right exact functor (preserves finite colimits), in the sense of
Etingof Definition 7.9.3. This is `CategoryTheory.Limits.PreservesFiniteColimits`
in Mathlib. -/
abbrev Etingof.RightExactFunctor {C : Type*} {D : Type*} [CategoryTheory.Category C]
    [CategoryTheory.Category D] (F : CategoryTheory.Functor C D) :=
  CategoryTheory.Limits.PreservesFiniteColimits F
