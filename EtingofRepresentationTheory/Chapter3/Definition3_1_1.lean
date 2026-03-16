import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Definition 3.1.1: Semisimple (Completely Reducible) Representation

A **semisimple** (or **completely reducible**) representation of A is a direct sum of
irreducible representations.

## Mathlib correspondence

This is exactly `IsSemisimpleModule R M` in Mathlib, which asserts that every submodule
has a complement.
-/

/-- A semisimple representation in the sense of Etingof Definition 3.1.1.
This is `IsSemisimpleModule` in Mathlib. -/
abbrev Etingof.IsSemisimpleRepresentation (k : Type*) (V : Type*)
    [Field k] [AddCommGroup V] [Module k V] :=
  IsSemisimpleModule k V
