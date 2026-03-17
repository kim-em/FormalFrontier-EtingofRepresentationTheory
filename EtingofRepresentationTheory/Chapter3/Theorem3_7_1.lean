import Mathlib.Order.JordanHolder
import Mathlib.RingTheory.SimpleModule.Basic

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

`JordanHolderLattice` and `CompositionSeries` provide the framework. Mathlib's
`JordanHolderModule.instJordanHolderLattice` gives a `JordanHolderLattice` instance for
`Submodule R M`, where `IsMaximal` is the covering relation `⋖` (equivalent to successive
quotients being simple modules). The theorem `CompositionSeries.jordan_holder` then gives
both equal lengths and a permutation of composition factors.
-/

/-- The Jordan-Hölder theorem for modules: any two composition series of the same module
(from ⊥ to ⊤) have the same length and isomorphic composition factors up to permutation.
Etingof Theorem 3.7.1.

A `CompositionSeries (Submodule A V)` is a `RelSeries` where consecutive submodules are
related by `⋖` (the covering relation), which is equivalent to requiring successive
quotients to be simple (irreducible) modules. -/
theorem Etingof.jordan_holder (A : Type*) (V : Type*)
    [Ring A] [AddCommGroup V] [Module A V]
    (s₁ s₂ : CompositionSeries (Submodule A V))
    (hs₁_bot : s₁.head = ⊥) (hs₁_top : s₁.last = ⊤)
    (hs₂_bot : s₂.head = ⊥) (hs₂_top : s₂.last = ⊤) :
    s₁.length = s₂.length :=
  (CompositionSeries.jordan_holder s₁ s₂
    (by rw [hs₁_bot, hs₂_bot]) (by rw [hs₁_top, hs₂_top])).length_eq
