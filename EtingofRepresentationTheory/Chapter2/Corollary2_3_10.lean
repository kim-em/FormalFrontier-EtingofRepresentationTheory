import Mathlib.RepresentationTheory.AlgebraRepresentation.Basic

/-!
# Corollary 2.3.10: Schur's Lemma for Algebraically Closed Fields

Let V be a finite dimensional irreducible representation of an algebra A over an algebraically
closed field k, and let φ : V → V be an intertwining operator. Then φ = λ · Id for some
λ ∈ k (a scalar operator).

## Mathlib correspondence

Exact match. This is `IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed` in Mathlib:
the algebra map from k to End_A(V) is bijective, so every A-endomorphism is scalar.
-/

/-- Schur's lemma for algebraically closed fields: any endomorphism of a finite-dimensional
irreducible representation over an algebraically closed field is a scalar multiple of the
identity. (Etingof Corollary 2.3.10) -/
theorem Etingof.Corollary_2_3_10
    {k : Type*} [Field k] [IsAlgClosed k]
    {A : Type*} [Ring A] [Algebra k A]
    {V : Type*} [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
    [IsSimpleModule A V] [FiniteDimensional k V]
    (φ : V →ₗ[A] V) :
    ∃ c : k, ∀ v : V, φ v = c • v := by
  obtain ⟨c, hc⟩ := (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed k).2 φ
  exact ⟨c, fun v => by simp [← hc]⟩
