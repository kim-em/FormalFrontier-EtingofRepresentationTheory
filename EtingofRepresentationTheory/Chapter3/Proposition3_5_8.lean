import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Proposition 3.5.8: Equivalent Characterizations of Semisimple Algebras

For a finite dimensional algebra A, the following are equivalent:

(1) A is semisimple (Rad(A) = 0).
(2) ∑ᵢ (dim Vᵢ)² = dim A, where the Vᵢ are the irreducible representations.
(3) A ≅ ⊕ᵢ Mat_{dᵢ}(k) for some dᵢ.
(4) Any finite dimensional representation of A is completely reducible.
(5) A is a completely reducible representation of A.
-/

/-- Equivalent characterizations of semisimple algebras.
Etingof Proposition 3.5.8. -/
theorem Etingof.semisimple_algebra_equiv (k : Type*) (A : Type*)
    [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A] :
    -- (1) ↔ (5): Rad(A) = 0 iff A is completely reducible as a representation of itself
    IsSemisimpleRing A ↔ IsSemisimpleModule A A := by
  sorry
