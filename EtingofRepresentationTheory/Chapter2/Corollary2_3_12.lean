import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Corollary 2.3.12: Irreducible Representations of Commutative Algebras

Let A be a commutative algebra. Then every irreducible finite dimensional representation V
of A is 1-dimensional.

## Mathlib correspondence

Exact match. This follows from Corollary 2.3.10 (Schur's lemma for algebraically closed fields):
every element of A acts as a scalar on an irreducible representation, so V must be 1-dimensional.
-/

/-- Every irreducible finite-dimensional representation of a commutative algebra over an
algebraically closed field is 1-dimensional. (Etingof Corollary 2.3.12) -/
theorem Etingof.Corollary_2_3_12
    {k : Type*} [Field k] [IsAlgClosed k]
    {A : Type*} [CommRing A] [Algebra k A]
    {V : Type*} [AddCommGroup V] [Module k V] [Module A V]
    [IsSimpleModule A V] [FiniteDimensional k V] :
    Module.finrank k V = 1 := by
  sorry
