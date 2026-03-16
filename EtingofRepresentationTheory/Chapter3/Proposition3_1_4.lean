import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Proposition 3.1.4: Classification of Subrepresentations in Semisimple Representations

Let Vᵢ, 1 ≤ i ≤ m, be irreducible finite dimensional pairwise nonisomorphic representations
of A, and let W be a subrepresentation of V = ⊕ᵢ nᵢVᵢ. Then W is isomorphic to ⊕ᵢ rᵢVᵢ,
rᵢ ≤ nᵢ, and the inclusion φ : W → V is a direct sum of inclusions φᵢ : rᵢVᵢ → nᵢVᵢ
given by multiplication of a row vector of elements of Vᵢ (of length rᵢ) by a certain
rᵢ × nᵢ matrix Xᵢ with linearly independent rows.
-/

/-- Any subrepresentation of a semisimple representation is semisimple with
multiplicities bounded by those of the ambient representation.
Etingof Proposition 3.1.4. -/
theorem Etingof.subrepresentation_of_semisimple (A : Type*) (V : Type*)
    [Ring A] [AddCommGroup V] [Module A V]
    [IsSemisimpleModule A V] (W : Submodule A V) :
    IsSemisimpleModule A W :=
  inferInstance
