import Mathlib.LinearAlgebra.Span.Basic

/-!
# Definition 2.3.4: Subrepresentation

A **subrepresentation** of a representation V of an algebra A is a subspace W ⊂ V
which is invariant under all the operators ρ(a) : V → V, a ∈ A.

For instance, 0 and V are always subrepresentations.

## Mathlib correspondence

This is `Submodule A V` — the type of A-submodules of V.
-/

/-- A subrepresentation of a representation V, in the sense of Etingof Definition 2.3.4.
This is `Submodule A V` in Mathlib. -/
abbrev Etingof.Subrepresentation (A : Type*) (V : Type*) [Ring A] [AddCommGroup V]
    [Module A V] :=
  Submodule A V
