import Mathlib

/-!
# Theorem 5.4.4: Character Vanishing or Scalar Action

For an irreducible representation V of G and a conjugacy class C such that
gcd(|C|, dim V) = 1: for any g ∈ C, either χ_V(g) = 0 or g acts as a scalar
on V (i.e., ρ(g) = λ · id for some root of unity λ).

The proof uses Lemma 5.4.5 (roots of unity average) and the fact that
χ_V(g)/dim(V) is an algebraic integer when gcd(|C|, dim(V)) = 1.

## Mathlib correspondence

Uses `IsIntegral`, `IsPrimitiveRoot`, character theory.
-/

open CategoryTheory in
/-- If gcd(|C|, dim V) = 1 for an irreducible V and conjugacy class C containing g, then
either χ_V(g) = 0 or g acts as a scalar on V. (Etingof Theorem 5.4.4) -/
theorem Etingof.Theorem5_4_4
    (G : Type) [Group G] [Fintype G] [DecidableEq G]
    (V : FDRep ℂ G) [Simple V]
    (g : G)
    (h_coprime : Nat.Coprime
      (Fintype.card { h : G // IsConj g h })
      (Module.finrank ℂ V)) :
    V.character g = 0 ∨ ∃ (c : ℂ), V.ρ g = c • LinearMap.id := by
  sorry
