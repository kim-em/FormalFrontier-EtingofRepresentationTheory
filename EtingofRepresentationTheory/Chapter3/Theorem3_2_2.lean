import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Theorem 3.2.2: The Density Theorem

(i) Let V be an irreducible finite dimensional representation of A. Then the map
ρ : A → End V is surjective.

(ii) Let V = V₁ ⊕ ⋯ ⊕ Vᵣ, where Vᵢ are irreducible pairwise nonisomorphic finite
dimensional representations of A. Then the map ⊕ᵢ ρᵢ : A → ⊕ᵢ End(Vᵢ) is surjective.
-/

/-- The density theorem, part (i): For an irreducible finite dimensional representation,
the representation map A → End(V) is surjective. Etingof Theorem 3.2.2(i). -/
theorem Etingof.density_theorem_part1 (k : Type*) (A : Type*) (V : Type*)
    [Field k] [Ring A] [Algebra k A]
    [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
    [FiniteDimensional k V] [IsSimpleModule A V]
    (ρ : A →ₗ[k] Module.End k V) :
    Function.Surjective ρ := by
  sorry

/-- The density theorem, part (ii): For a direct sum of pairwise nonisomorphic irreducible
representations, the combined representation map is surjective.
Etingof Theorem 3.2.2(ii). -/
theorem Etingof.density_theorem_part2 (k : Type*) (A : Type*) (V : Type*)
    [Field k] [Ring A] [Algebra k A]
    [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
    [FiniteDimensional k V] [IsSemisimpleModule A V] :
    -- The combined map A → ⊕ᵢ End(Vᵢ) is surjective when the Vᵢ are the
    -- irreducible components, pairwise nonisomorphic.
    True := by
  sorry
