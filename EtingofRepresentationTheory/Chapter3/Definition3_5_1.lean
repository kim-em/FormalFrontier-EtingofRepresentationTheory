import Mathlib.RingTheory.Jacobson.Ideal

/-!
# Definition 3.5.1: Radical of a Finite Dimensional Algebra

The **radical** of a finite dimensional algebra A is the set of all elements of A which act
by 0 in all irreducible representations of A. It is denoted Rad(A).

## Mathlib correspondence

The Jacobson radical is `Ideal.jacobson ⊥` (intersection of all maximal left ideals).
For finite dimensional algebras this equals the radical as defined by Etingof.
-/

/-- The radical of a finite dimensional algebra, in the sense of Etingof Definition 3.5.1.
This is the Jacobson radical `Ideal.jacobson ⊥` in Mathlib. -/
abbrev Etingof.Radical (A : Type*) [Ring A] : Ideal A :=
  Ideal.jacobson ⊥
