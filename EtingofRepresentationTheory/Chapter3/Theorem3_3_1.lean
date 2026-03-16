import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Module
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Theorem 3.3.1: Irreducible Representations of Direct Sums of Matrix Algebras

Let A = ⊕ᵢ Mat_{dᵢ}(k). Then the irreducible representations of A are
V₁ = k^{d₁}, …, Vᵣ = k^{dᵣ}, and any finite dimensional representation of A is a direct
sum of copies of V₁, …, Vᵣ.

The core of this result is that each matrix algebra Mat_d(k) has a unique
irreducible representation, namely the standard representation k^d. The full
theorem follows because the irreducible representations of a direct sum of
algebras are exactly the irreducible representations of the individual factors.
-/

open Matrix.Module

/-- The standard representation k^d is the unique irreducible representation of Mat_d(k).
Every irreducible representation of ⊕ᵢ Mat_{dᵢ}(k) is isomorphic to one of the standard
representations k^{dⱼ} (for some factor j). Etingof Theorem 3.3.1. -/
theorem Etingof.irreducible_reps_of_matrix_algebra (k : Type*) [Field k]
    (d : ℕ) [NeZero d] (V : Type*)
    [AddCommGroup V] [Module k V] [Module (Matrix (Fin d) (Fin d) k) V]
    [IsScalarTower k (Matrix (Fin d) (Fin d) k) V]
    [FiniteDimensional k V] [IsSimpleModule (Matrix (Fin d) (Fin d) k) V] :
    Nonempty (V ≃ₗ[Matrix (Fin d) (Fin d) k] (Fin d → k)) := by
  sorry
