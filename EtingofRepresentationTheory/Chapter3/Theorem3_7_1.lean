import Mathlib.Order.JordanHolder
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.LinearAlgebra.Span.Basic

/-!
# Theorem 3.7.1: Jordan-Hölder Theorem

Let V be a finite dimensional representation of A, and let
0 = V₀ ⊂ V₁ ⊂ ⋯ ⊂ Vₙ = V, 0 = V'₀ ⊂ ⋯ ⊂ V'ₘ = V
be filtrations of V such that the representations Wᵢ := Vᵢ/Vᵢ₋₁ and W'ᵢ := V'ᵢ/V'ᵢ₋₁
are irreducible for all i. Then n = m, and there exists a permutation σ of 1, …, n such
that W_{σ(i)} is isomorphic to W'ᵢ.

Two proofs are given:
- First proof (char 0): uses linear independence of characters (Theorem 3.6.2).
- Second proof (general): induction on dim V, analyzing the cases W₁ = W'₁ and W₁ ≠ W'₁.

## Mathlib correspondence

`JordanHolderLattice` and `CompositionSeries` provide the framework. The connection to
module composition series requires showing modules form a `JordanHolderLattice`.
-/

/-- The Jordan-Hölder theorem for finite dimensional representations: any two composition
series have the same length and the same composition factors up to permutation.
Etingof Theorem 3.7.1.

Note: The full statement requires a `JordanHolderLattice` instance for `Submodule A V`.
Here we state the core content: equal lengths of composition series. -/
theorem Etingof.jordan_holder (A : Type*) (V : Type*)
    [Ring A] [AddCommGroup V] [Module A V]
    (s₁ s₂ : RelSeries {p : Submodule A V × Submodule A V | p.1 < p.2})
    (hs₁_bot : s₁.head = ⊥) (hs₁_top : s₁.last = ⊤)
    (hs₂_bot : s₂.head = ⊥) (hs₂_top : s₂.last = ⊤) :
    -- Under the additional assumption that successive quotients are irreducible,
    -- s₁.length = s₂.length and the composition factors are the same up to permutation.
    s₁.length = s₂.length := by
  sorry
