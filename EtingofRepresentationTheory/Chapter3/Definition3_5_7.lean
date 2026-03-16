import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Definition 3.5.7: Semisimple Algebra

A finite dimensional algebra A is said to be **semisimple** if Rad(A) = 0.

## Mathlib correspondence

This is exactly `IsSemisimpleRing A` in Mathlib, which asserts that every module is
semisimple (equivalently, A is semisimple as a module over itself).
-/

/-- A semisimple algebra in the sense of Etingof Definition 3.5.7.
This is `IsSemisimpleRing` in Mathlib. -/
abbrev Etingof.IsSemisimpleAlgebra (A : Type*) [Ring A] :=
  IsSemisimpleRing A
