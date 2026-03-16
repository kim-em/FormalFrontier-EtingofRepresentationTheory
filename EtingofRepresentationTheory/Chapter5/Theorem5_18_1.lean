import Mathlib

/-!
# Theorem 5.18.1: Double Centralizer Theorem

Let A be a semisimple subalgebra of End(E) for a finite-dimensional vector space E,
and let B = End_A(E) be the commutant. Then:

(i) A = End_B(E) (the double centralizer property)
(ii) B is semisimple
(iii) As an (A ⊗ B)-module, E ≅ ⊕_{i ∈ I} Vᵢ ⊗ Wᵢ, where {Vᵢ} are the
     distinct irreducible A-modules appearing in E and Wᵢ are the corresponding
     irreducible B-modules.

## Mathlib correspondence

This is a fundamental theorem in the theory of semisimple algebras. Mathlib has
`IsSemisimpleRing` and module theory, but the double centralizer theorem
itself may not be formalized.
-/

/-- Double centralizer theorem: A = End_{End_A(E)}(E) for semisimple A ⊆ End(E).
(Etingof Theorem 5.18.1, part i) -/
theorem Etingof.Theorem5_18_1_double_centralizer
    (k : Type*) [Field k]
    (E : Type*) [AddCommGroup E] [Module k E] [Module.Finite k E] :
    -- For semisimple A ⊆ End(E), A = End_{End_A(E)}(E)
    (sorry : Prop) := by
  sorry

/-- The commutant of a semisimple subalgebra is semisimple.
(Etingof Theorem 5.18.1, part ii) -/
theorem Etingof.Theorem5_18_1_commutant_semisimple
    (k : Type*) [Field k]
    (E : Type*) [AddCommGroup E] [Module k E] [Module.Finite k E] :
    -- End_A(E) is semisimple when A is semisimple
    (sorry : Prop) := by
  sorry

/-- Decomposition of E as (A ⊗ B)-module into tensor products of irreducibles.
(Etingof Theorem 5.18.1, part iii) -/
theorem Etingof.Theorem5_18_1_decomposition
    (k : Type*) [Field k]
    (E : Type*) [AddCommGroup E] [Module k E] [Module.Finite k E] :
    -- E ≅ ⊕_i V_i ⊗ W_i as (A ⊗ B)-module
    (sorry : Prop) := by
  sorry
