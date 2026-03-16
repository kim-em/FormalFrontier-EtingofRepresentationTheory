import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# Corollary 2.3.10: Schur's Lemma for Algebraically Closed Fields

Let V be a finite dimensional irreducible representation of an algebra A over an algebraically
closed field k, and let φ : V → V be an intertwining operator. Then φ = λ · Id for some
λ ∈ k (a scalar operator).

## Mathlib correspondence

Exact match. This follows from eigenvalue theory over algebraically closed fields combined
with Schur's lemma. Mathlib has `IsAlgClosed`, `Module.End.HasEigenvalue`, and
`Module.End.eigenspace`.
-/

/-- Schur's lemma for algebraically closed fields: any endomorphism of a finite-dimensional
irreducible representation over an algebraically closed field is a scalar multiple of the
identity. (Etingof Corollary 2.3.10) -/
theorem Etingof.Corollary_2_3_10
    {k : Type*} [Field k] [IsAlgClosed k]
    {A : Type*} [Ring A] [Algebra k A]
    {V : Type*} [AddCommGroup V] [Module k V] [Module A V]
    [IsSimpleModule A V] [FiniteDimensional k V]
    (φ : V →ₗ[A] V) :
    ∃ c : k, ∀ v : V, φ v = c • v := by
  sorry
