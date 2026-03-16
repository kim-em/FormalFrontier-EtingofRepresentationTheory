import Mathlib

/-!
# Example 4.1.3: Representations of ℤ/pℤ in Characteristic p

If G = ℤ/pℤ and k has characteristic p, then every irreducible representation of G
over k is trivial (1-dimensional with trivial action).

The argument: any irreducible representation is 1-dimensional, and the generator g must
act by a p-th root of unity. But over a field of characteristic p, xᵖ - 1 = (x - 1)ᵖ,
so the only p-th root of unity is 1.

This shows that the hypothesis in Maschke's theorem (char k ∤ |G|) is essential.

## Mathlib correspondence

Uses `ZMod p` for the cyclic group and `CharP k p` for characteristic p.
-/

/-- In characteristic p, every irreducible representation of ℤ/pℤ is trivial.
(Etingof Example 4.1.3) -/
theorem Etingof.Example4_1_3
    (k : Type*) (p : ℕ) [Field k] [hp : Fact (Nat.Prime p)] [CharP k p]
    (V : Type*) [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρ : Representation k (Multiplicative (ZMod p)) V)
    (hirr : IsSimpleModule k V) :
    -- Every irreducible rep is trivial: ρ(g) = id for all g
    ∀ g : Multiplicative (ZMod p), ρ g = LinearMap.id := by
  sorry
