import Mathlib.GroupTheory.GroupAction.Basic

/-!
# Definition 2.7.3: Faithful Representation

A representation ρ : A → End V of an algebra A is **faithful** if ρ is injective.

## Mathlib correspondence

This is `FaithfulSMul A V` — asserts that the scalar action is faithful.
-/

/-- A faithful representation, in the sense of Etingof Definition 2.7.3.
This is `FaithfulSMul A V` in Mathlib. -/
abbrev Etingof.FaithfulRepresentation (A : Type*) (V : Type*) [Ring A] [AddCommGroup V]
    [Module A V] :=
  FaithfulSMul A V
