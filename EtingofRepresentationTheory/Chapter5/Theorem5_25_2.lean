import Mathlib

/-!
# Theorem 5.25.2: Principal Series Representations of GL₂(𝔽_q)

(1) If λ₁ ≠ λ₂, then V(λ₁, λ₂) is irreducible.
(2) If λ₁ = λ₂ = μ, then V(λ₁, λ₂) = ℂ_μ ⊕ W_μ where W_μ is
    a q-dimensional irreducible representation of G.
(3) W_μ ≅ W_ν iff μ = ν; V(λ₁, λ₂) ≅ V(λ'₁, λ'₂) iff {λ₁, λ₂} = {λ'₁, λ'₂}.

## Mathlib correspondence

Uses `GaloisField` and finite group representation theory.
The principal series construction is not in Mathlib.
-/

/-- Principal series representations V(λ₁, λ₂) of GL₂(𝔽_q): irreducibility
and classification. (Etingof Theorem 5.25.2) -/
theorem Etingof.Theorem5_25_2
    (p : ℕ) [hp : Fact (Nat.Prime p)] (n : ℕ) (hn : 0 < n) :
    let q := p ^ n
    -- V(λ₁,λ₂) is irreducible when λ₁ ≠ λ₂; decomposes as ℂ_μ ⊕ W_μ when λ₁ = λ₂ = μ
    (sorry : Prop) := by
  sorry
