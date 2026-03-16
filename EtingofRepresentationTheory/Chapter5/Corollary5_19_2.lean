import Mathlib

/-!
# Corollary 5.19.2: Schur-Weyl Decomposition

As a representation of Sₙ × GL(V), V⊗ⁿ decomposes as
  V⊗ⁿ ≅ ⊕_λ Vλ ⊗ Lλ
where Vλ are irreducible Sₙ-representations (Specht modules) and
Lλ = Hom_{Sₙ}(Vλ, V⊗ⁿ) are distinct irreducible GL(V)-representations (or zero).

## Mathlib correspondence

Requires Schur-Weyl duality, which is not yet in Mathlib.
-/

/-- Schur-Weyl decomposition: as an Sₙ × GL(V) representation,
V⊗ⁿ ≅ ⊕_λ Vλ ⊗ Lλ where Lλ = Hom_{Sₙ}(Vλ, V⊗ⁿ).
(Etingof Corollary 5.19.2) -/
theorem Etingof.Corollary5_19_2
    {k : Type*} [Field k] [IsAlgClosed k]
    {V : Type*} [AddCommGroup V] [Module k V] [Module.Finite k V]
    (n : ℕ) :
    -- V⊗ⁿ ≅ ⊕_λ Vλ ⊗ Lλ as Sₙ × GL(V) representations
    (sorry : Prop) := by
  sorry
