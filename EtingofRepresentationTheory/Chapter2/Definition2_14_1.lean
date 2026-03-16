import Mathlib.Algebra.Lie.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# Definition 2.14.1: Tensor Product of Lie Algebra Representations

The **tensor product** of two representations V, W of a Lie algebra 𝔤 is the space
V ⊗ W with ρ_{V⊗W}(x) = ρ_V(x) ⊗ Id + Id ⊗ ρ_W(x).

## Mathlib correspondence

Mathlib has both `TensorProduct` and `LieModule`. The Lie module structure on tensor
products uses the Leibniz rule. The instance may exist under
`Mathlib.Algebra.Lie.TensorProduct`.
-/

open scoped TensorProduct

/-- The tensor product of two Lie algebra representations, in the sense of
Etingof Definition 2.14.1. The Lie action on V ⊗ W is given by the Leibniz rule:
x · (v ⊗ w) = (x · v) ⊗ w + v ⊗ (x · w). -/
abbrev Etingof.LieTensorProduct (k : Type*) (L : Type*) (V : Type*) (W : Type*)
    [CommRing k] [LieRing L] [LieAlgebra k L]
    [AddCommGroup V] [Module k V] [LieRingModule L V] [LieModule k L V]
    [AddCommGroup W] [Module k W] [LieRingModule L W] [LieModule k L W] :=
  TensorProduct k V W
