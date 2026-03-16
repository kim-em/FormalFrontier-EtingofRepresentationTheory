import Mathlib.Order.RelSeries
import Mathlib.LinearAlgebra.Span.Basic

/-!
# Definition 3.4.1: Filtration of a Representation

A (finite) **filtration** of V is a sequence of subrepresentations
0 = V₀ ⊂ V₁ ⊂ ⋯ ⊂ Vₙ = V.

## Mathlib correspondence

Mathlib has `CompositionSeries` for Jordan-Hölder filtrations. General filtrations
(ascending chain of submodules) can be modeled as a `RelSeries` on `Submodule A V`
with the strict less-than relation.
-/

/-- A filtration of a module V over A is a finite strictly ascending chain of submodules.
Etingof Definition 3.4.1. -/
abbrev Etingof.Filtration (A : Type*) (V : Type*)
    [Ring A] [AddCommGroup V] [Module A V] :=
  RelSeries {p : Submodule A V × Submodule A V | p.1 < p.2}
