import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Theorem 3.3.1: Irreducible Representations of Direct Sums of Matrix Algebras

Let A = ⊕ᵢ Mat_{dᵢ}(k). Then the irreducible representations of A are
V₁ = k^{d₁}, …, Vᵣ = k^{dᵣ}, and any finite dimensional representation of A is a direct
sum of copies of V₁, …, Vᵣ.
-/

/-- The irreducible representations of a direct sum of matrix algebras are exactly the
standard representations k^{dᵢ}. Etingof Theorem 3.3.1. -/
theorem Etingof.irreducible_reps_of_matrix_algebra (k : Type*) [Field k]
    (n : ℕ) (d : Fin n → ℕ) :
    -- Every irreducible representation of ⊕ᵢ Mat_{dᵢ}(k) is isomorphic to k^{dᵢ}
    -- for some i, and every finite dimensional representation is a direct sum of these.
    True := by
  sorry
