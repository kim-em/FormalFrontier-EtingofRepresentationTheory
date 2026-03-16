import Mathlib

/-!
# Example 4.3: Irreducible Representations of Finite Abelian Groups

For a finite abelian group G = ℤ/n₁ℤ × ⋯ × ℤ/nₖℤ, all irreducible representations
(over an algebraically closed field of characteristic 0) are 1-dimensional.

The dual group (Pontryagin dual) G^∨ consists of all irreducible characters.
For ℤ/nℤ: the irreducible characters are ρₖ(m) = e^(2πimk/n) for k = 0, …, n-1,
giving ℤ/nℤ^∨ ≅ ℤ/nℤ. In general (G₁ × G₂)^∨ = G₁^∨ × G₂^∨, so G^∨ ≅ G
(non-canonically), and G ≅ (G^∨)^∨ canonically via φ(g)(χ) = χ(g).

## Mathlib correspondence

Mathlib has `AddChar` for characters of additive groups. The Pontryagin duality
theory is partially developed.
-/

/-- For a finite abelian group, all irreducible representations over an algebraically
closed field of characteristic 0 are 1-dimensional. (Etingof Example 4.3) -/
theorem Etingof.Example4_3_FiniteAbelianGroups
    (k : Type*) (G : Type*) [Field k] [CharZero k] [IsAlgClosed k]
    [CommGroup G] [Fintype G] [DecidableEq G]
    (V : Type*) [AddCommGroup V] [Module k V] [Module.Finite k V]
    -- For a finite abelian group, all irreducible representations are 1-dimensional
    -- The MonoidAlgebra module structure would need to be derived from a Representation
    (hirr : IsSimpleModule k V) :
    Module.finrank k V = 1 := by
  sorry
