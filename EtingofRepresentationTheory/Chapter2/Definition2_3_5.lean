import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Definition 2.3.5: Irreducible (Simple) Representation

A representation V ≠ 0 of A is **irreducible** (or **simple**) if the only
subrepresentations of V are 0 and V.

## Mathlib correspondence

This is `IsSimpleModule R M` — asserts that the module M has exactly two submodules
(⊥ and ⊤).
-/

/-- An irreducible (simple) representation, in the sense of Etingof Definition 2.3.5.
This is `IsSimpleModule A V` in Mathlib. -/
abbrev Etingof.IrreducibleRepresentation (A : Type*) (V : Type*) [Ring A] [AddCommGroup V]
    [Module A V] :=
  IsSimpleModule A V
