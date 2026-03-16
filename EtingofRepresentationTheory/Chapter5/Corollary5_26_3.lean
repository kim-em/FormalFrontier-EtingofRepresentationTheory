import Mathlib

/-!
# Corollary 5.26.3: Characters from Cyclic Subgroups

Any irreducible character of a finite group is a rational linear combination
of induced characters from its cyclic subgroups.

This follows from Artin's theorem (Theorem 5.26.1) since every element
belongs to the cyclic subgroup it generates.

## Mathlib correspondence

Uses `Subgroup.zpowers` for cyclic subgroups. The result itself is not in Mathlib.
-/

/-- Any irreducible character of a finite group is a ℚ-linear combination of
characters induced from cyclic subgroups. (Etingof Corollary 5.26.3) -/
theorem Etingof.Corollary5_26_3
    (G : Type*) [Group G] [Fintype G] [DecidableEq G] :
    -- Every irreducible character of G is in the ℚ-span of
    -- {Ind_{⟨g⟩}^G χ | g ∈ G, χ irreducible character of ⟨g⟩}
    (sorry : Prop) := by
  sorry
