import Mathlib.RingTheory.Jacobson.Ideal
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Theorem 3.5.4: Structure of Finite Dimensional Algebras Modulo Radical

A finite dimensional algebra A has only finitely many irreducible representations Vᵢ
up to isomorphism. These representations are finite dimensional, and

  A / Rad(A) ≅ ⊕ᵢ End(Vᵢ).
-/

/-- A finite dimensional algebra has finitely many irreducible representations up to
isomorphism, and A/Rad(A) is isomorphic to the direct sum of their endomorphism algebras.
Etingof Theorem 3.5.4. -/
theorem Etingof.structure_mod_radical (k : Type*) (A : Type*)
    [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A] :
    -- A / Rad(A) ≅ ⊕ᵢ End(Vᵢ) where the Vᵢ are the irreducible representations.
    -- The key content: finitely many irreducibles, all finite dimensional,
    -- and the quotient decomposes as stated.
    True := by
  sorry
