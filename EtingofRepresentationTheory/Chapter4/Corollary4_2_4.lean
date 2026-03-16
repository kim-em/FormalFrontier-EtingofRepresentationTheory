import Mathlib

/-!
# Corollary 4.2.4: Representations Determined by Characters

If k has characteristic 0, any finite dimensional representation of G is determined
by its character: χ_V = χ_W implies V ≅ W.

This follows from the orthogonality of characters (Theorem 4.5.1) and the fact that
the multiplicity of each irreducible in a representation can be recovered from
the character via the inner product formula.

## Mathlib correspondence

Uses `Representation.character` from `Mathlib.RepresentationTheory.Character`.
-/

/-- In characteristic 0, representations are determined by their characters.
(Etingof Corollary 4.2.4) -/
theorem Etingof.Corollary4_2_4
    (G : Type) [Group G] [Fintype G] [DecidableEq G]
    (V W : FDRep ℂ G)
    (h : FDRep.character V = FDRep.character W) :
    Nonempty (V ≅ W) := by
  sorry
