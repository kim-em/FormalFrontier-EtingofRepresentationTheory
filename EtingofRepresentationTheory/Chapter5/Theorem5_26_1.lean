import Mathlib

/-!
# Theorem 5.26.1: Artin's Theorem

Let X be a conjugation-invariant system of subgroups of a finite group G.
Two conditions are equivalent:

(i) Any element of G belongs to a subgroup H ∈ X.

(ii) The character of any irreducible representation of G belongs to the
ℚ-span of characters of induced representations Ind_H^G V, where H ∈ X
and V is an irreducible representation of H.

## Mathlib correspondence

Uses `Subgroup`, `Fintype`, and character theory. Induced representations
and Artin's theorem are not yet in Mathlib.
-/

/-- Artin's theorem: a conjugation-invariant system of subgroups X covers G
iff every irreducible character is a ℚ-linear combination of induced
characters from subgroups in X. (Etingof Theorem 5.26.1) -/
theorem Etingof.Theorem5_26_1
    (G : Type*) [Group G] [Fintype G] [DecidableEq G]
    (X : Set (Subgroup G)) :
    -- (i) ⇔ (ii): element coverage ↔ character ℚ-span condition
    (sorry : Prop) := by
  sorry
