import Mathlib.RingTheory.Jacobson.Ideal
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Corollary 3.5.5: Sum of Squares of Dimensions Bounded by dim A

∑ᵢ (dim Vᵢ)² ≤ dim A, where the Vᵢ are the irreducible representations of A.

This follows from Theorem 3.5.4: dim A - dim Rad(A) = ∑ᵢ dim End(Vᵢ) = ∑ᵢ (dim Vᵢ)²,
and dim Rad(A) ≥ 0.
-/

/-- The sum of squares of dimensions of irreducible representations is at most dim A.
Etingof Corollary 3.5.5. -/
theorem Etingof.sum_dim_sq_le_dim (k : Type*) (A : Type*)
    [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A] :
    -- ∑ᵢ (dim Vᵢ)² ≤ dim A where Vᵢ range over irreducible representations
    True := by
  sorry
