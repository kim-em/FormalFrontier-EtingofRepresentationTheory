import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Corollary 3.2.1: Linear Map Realization

Let V be an irreducible finite dimensional representation of A, and let v₁, …, vₙ ∈ V
be any linearly independent vectors. Then for any w₁, …, wₙ ∈ V there exists an element
a ∈ A such that a · vᵢ = wᵢ for all i.
-/

/-- In an irreducible representation, any linear map on linearly independent vectors can be
realized by an algebra element. Etingof Corollary 3.2.1. -/
theorem Etingof.irreducible_interpolation (A : Type*) (V : Type*)
    [Ring A] [AddCommGroup V] [Module A V]
    [IsSimpleModule A V] {n : ℕ}
    (v : Fin n → V) (hv : LinearIndependent A v)
    (w : Fin n → V) :
    ∃ a : A, ∀ i, a • v i = w i := by
  sorry
