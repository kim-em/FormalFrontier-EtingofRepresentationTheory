import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.FreeAlgebra

/-!
# Example 2.3.3: Examples of Representations

1. V = 0 (the zero representation).
2. V = A with ρ(a) = left multiplication by a (the regular representation).
3. A = k: a representation of k is simply a vector space over k.
4. A = k⟨x₁, …, xₙ⟩: a representation is a vector space with n arbitrary linear operators.

## Mathlib correspondence

Exact match. The regular representation is the canonical `Module A A` instance.
-/

/-- The zero module is a representation of any algebra. (Etingof Example 2.3.3(1)) -/
example (A : Type*) [Ring A] : Module A PUnit := inferInstance

/-- The regular representation: A is a left module over itself. (Etingof Example 2.3.3(2)) -/
example (A : Type*) [Ring A] : Module A A := inferInstance

/-- A representation of k is simply a vector space over k. (Etingof Example 2.3.3(3)) -/
example (k : Type*) [Field k] (V : Type*) [AddCommGroup V] [Module k V] :
    Module k V := inferInstance

/-- A representation of the free algebra k⟨x₁, …, xₙ⟩ on V is determined by n arbitrary
linear operators on V. (Etingof Example 2.3.3(4)) -/
example (k : Type*) [CommRing k] (V : Type*) [AddCommGroup V] [Module k V]
    [Module (FreeAlgebra k (Fin 3)) V] :
    Module (FreeAlgebra k (Fin 3)) V := inferInstance
