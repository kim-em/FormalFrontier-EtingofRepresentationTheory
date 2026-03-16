import Mathlib.Algebra.Module.Submodule.Lattice

/-!
# Definition 2.3.8: Indecomposable Representation

A nonzero representation V of an algebra A is said to be **indecomposable** if it is
not isomorphic to a direct sum of two nonzero representations.

## Mathlib correspondence (partial)

Mathlib has `Indecomposable` for order theory but not directly for modules.
We define indecomposability for modules as: V is nontrivial and for any submodules
W₁, W₂ with V = W₁ ⊕ W₂, either W₁ = 0 or W₂ = 0.

This is equivalent to saying that V has no nontrivial complemented submodules.
-/

-- not in Mathlib as of v4.28
/-- A module is **indecomposable** if it is nontrivial and cannot be decomposed as a
direct sum of two nonzero submodules. Etingof Definition 2.3.8. -/
def Etingof.IsIndecomposable (A : Type*) (V : Type*) [Ring A] [AddCommGroup V]
    [Module A V] : Prop :=
  Nontrivial V ∧ ∀ (W₁ W₂ : Submodule A V),
    IsCompl W₁ W₂ → W₁ = ⊥ ∨ W₂ = ⊥
