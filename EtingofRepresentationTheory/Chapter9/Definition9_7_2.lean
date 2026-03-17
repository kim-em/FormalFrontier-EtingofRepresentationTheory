import Mathlib.RingTheory.Jacobson.Radical
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Definition 9.7.2: Basic algebra

A finite dimensional algebra B is called **basic** if B/Rad(B) is a commutative algebra
(i.e., a direct sum of copies of the ground field k).

Equivalently, B is basic if and only if all simple B-modules are one-dimensional.

## Mathlib correspondence

We use the "all simple modules are one-dimensional" characterization, expressed via
`Module.finrank`. This is more directly usable in downstream results than the
Jacobson radical quotient characterization.
-/

/-- A basic algebra in the sense of Etingof Definition 9.7.2.
A finite dimensional k-algebra A is basic if every simple A-module is one-dimensional
over k. -/
def Etingof.IsBasicAlgebra (k : Type*) [Field k]
    (A : Type*) [Ring A] [Algebra k A] : Prop :=
  ∀ (M : Type*) [AddCommGroup M] [Module A M] [IsSimpleModule A M] [Module k M]
    [IsScalarTower k A M], Module.finrank k M = 1
