import Mathlib.LinearAlgebra.DirectSum.Finite

/-!
# Definition 2.3.7: Direct Sum of Representations

Let V₁, V₂ be representations of an algebra A. Then the space V₁ ⊕ V₂ has an
obvious structure of a representation of A, given by a(v₁ ⊕ v₂) = av₁ ⊕ av₂.
This representation is called the **direct sum** of V₁ and V₂.

## Mathlib correspondence

Binary direct sum is modeled via the product `V₁ × V₂` with the product module structure.
General direct sums use `DirectSum ι M`.
-/

/-- The direct sum of two representations, in the sense of Etingof Definition 2.3.7.
In Mathlib, the binary direct sum is `V₁ × V₂` with the product module structure. -/
abbrev Etingof.DirectSumRepresentation (A : Type*) (V₁ V₂ : Type*) [Ring A]
    [AddCommGroup V₁] [AddCommGroup V₂] [Module A V₁] [Module A V₂] :=
  V₁ × V₂
