import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Nilpotent.Defs

/-!
# Lemma 3.8.2: Endomorphisms of Indecomposable Representations

Let W be a finite dimensional indecomposable representation of A. Then:

(i) Any homomorphism θ : W → W is either an isomorphism or nilpotent.

(ii) If θₛ : W → W, s = 1, …, n, are nilpotent homomorphisms, then so is
     θ := θ₁ + ⋯ + θₙ.

The proof of (i) uses generalized eigenspaces: they are subrepresentations and W is their
direct sum, so θ can have only one eigenvalue.

The proof of (ii) is by induction on n, using that if the sum were an isomorphism,
the inverse composed with each summand would give nilpotent maps summing to the identity.
-/

/-- Any endomorphism of a finite dimensional indecomposable representation is either
an isomorphism or nilpotent. Etingof Lemma 3.8.2(i). -/
theorem Etingof.endo_indecomposable_iso_or_nilpotent (k : Type*) (A : Type*) (W : Type*)
    [Field k] [Ring A] [Algebra k A]
    [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W]
    [FiniteDimensional k W]
    (hW : ¬ ∃ (M N : Submodule A W), M ≠ ⊥ ∧ N ≠ ⊥ ∧ M ⊔ N = ⊤ ∧ M ⊓ N = ⊥)
    (θ : W →ₗ[A] W) :
    Function.Bijective θ ∨ IsNilpotent θ := by
  sorry

/-- A sum of nilpotent endomorphisms of an indecomposable representation is nilpotent.
Etingof Lemma 3.8.2(ii). -/
theorem Etingof.sum_nilpotent_endo_indecomposable (k : Type*) (A : Type*) (W : Type*)
    [Field k] [Ring A] [Algebra k A]
    [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W]
    [FiniteDimensional k W]
    (hW : ¬ ∃ (M N : Submodule A W), M ≠ ⊥ ∧ N ≠ ⊥ ∧ M ⊔ N = ⊤ ∧ M ⊓ N = ⊥)
    {n : ℕ} (θ : Fin n → (W →ₗ[A] W)) (hθ : ∀ i, IsNilpotent (θ i)) :
    IsNilpotent (∑ i, θ i) := by
  sorry
