import Mathlib.Algebra.Module.Basic

/-!
# Definition 2.3.1: Representation of an Algebra (Left A-module)

A **representation** of an algebra A (also called a **left A-module**) is a vector space V
together with a homomorphism of algebras ρ : A → End V.

Similarly, a **right A-module** is a space V equipped with an antihomomorphism
ρ : A → End V.

## Mathlib correspondence

A left A-module is `Module A V`. Mathlib uses left modules by convention.
-/

/-- A representation of an algebra A, in the sense of Etingof Definition 2.3.1.
This is `Module A V` in Mathlib. -/
abbrev Etingof.Representation (A : Type*) (V : Type*) [Ring A] [AddCommGroup V] :=
  Module A V
