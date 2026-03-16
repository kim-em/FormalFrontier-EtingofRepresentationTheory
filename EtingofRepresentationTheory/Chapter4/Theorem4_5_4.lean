import Mathlib

/-!
# Theorem 4.5.4: Second Orthogonality Relation (Column Orthogonality)

For g, h ∈ G, let Z_g denote the centralizer of g. Then:
$$\sum_V \chi_V(g) \overline{\chi_V(h)} = \begin{cases} |Z_g|, & \text{if } g \sim h \\ 0, & \text{otherwise} \end{cases}$$

where the sum runs over all irreducible representations V and g ~ h means g and h
are conjugate.

The proof computes the trace of the operator x ↦ gxh⁻¹ on ℂ[G] in two ways:
via the regular representation decomposition and via direct computation on basis elements.

## Mathlib correspondence

This is the column (or second) orthogonality relation. Not directly in Mathlib as of v4.28.
-/

/-- Second orthogonality relation for characters. (Etingof Theorem 4.5.4) -/
theorem Etingof.Theorem4_5_4
    (G : Type*) [Group G] [Fintype G] [DecidableEq G]
    (g h : G) :
    -- Σ_V χ_V(g) * conj(χ_V(h)) = |Z_g| if g ~ h, else 0
    True := by  -- TODO: needs character sum and centralizer API
  sorry
