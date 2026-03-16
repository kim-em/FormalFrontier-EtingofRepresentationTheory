import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# Definition 2.11.1: Tensor Product of Vector Spaces

The **tensor product** V ⊗ W of vector spaces V and W over a field k is the quotient
of the space with basis given by formal symbols v ⊗ w by the subspace enforcing
bilinearity.

## Mathlib correspondence

This is `TensorProduct R M N` (notation `M ⊗[R] N`).
-/

open scoped TensorProduct

/-- The tensor product of two vector spaces, in the sense of Etingof Definition 2.11.1.
This is `TensorProduct k V W` (notation `V ⊗[k] W`) in Mathlib. -/
abbrev Etingof.TensorProductDef (k : Type*) (V W : Type*) [CommRing k]
    [AddCommGroup V] [AddCommGroup W] [Module k V] [Module k W] :=
  V ⊗[k] W
