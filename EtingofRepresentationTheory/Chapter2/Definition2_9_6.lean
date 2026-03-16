import Mathlib.Algebra.Lie.Basic

/-!
# Definition 2.9.6: Homomorphism of Lie Algebras

Let 𝔤₁, 𝔤₂ be Lie algebras. A **homomorphism of Lie algebras** φ : 𝔤₁ → 𝔤₂ is a
linear map such that φ([a, b]) = [φ(a), φ(b)] for all a, b ∈ 𝔤₁.

## Mathlib correspondence

This is `LieHom R L₁ L₂` (notation `L₁ →ₗ⁅R⁆ L₂`).
-/

/-- A homomorphism of Lie algebras, in the sense of Etingof Definition 2.9.6.
This is `LieHom k L₁ L₂` (notation `L₁ →ₗ⁅k⁆ L₂`) in Mathlib. -/
abbrev Etingof.LieAlgebraHom (k : Type*) (L₁ L₂ : Type*) [CommRing k]
    [LieRing L₁] [LieRing L₂] [LieAlgebra k L₁] [LieAlgebra k L₂] :=
  L₁ →ₗ⁅k⁆ L₂
