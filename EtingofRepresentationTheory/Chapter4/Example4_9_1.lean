import Mathlib

/-!
# Example 4.9.1: Tensor Product Multiplicities

Tensor product decomposition tables for S₃, S₄, and A₅.

**S₃ examples:**
- ℂ₊ ⊗ ℂ₋ = ℂ₋
- ℂ₋ ⊗ ℂ₋ = ℂ₊
- ℂ² ⊗ ℂ² = ℂ₊ ⊕ ℂ₋ ⊕ ℂ²

For S₄ and A₅, similar multiplication tables show how tensor products decompose
into irreducibles, computed using the formula:
  n_{ij}^k = (χ_i · χ_j, χ_k) = (1/|G|) Σ_g χ_i(g) χ_j(g) χ_k(g)*

## Mathlib correspondence

Tensor product decomposition multiplicities are not systematically in Mathlib.
-/

/-- For S₃, the tensor product of the standard 2-dimensional representation with itself
decomposes as ℂ₊ ⊕ ℂ₋ ⊕ ℂ², i.e., the tensor square has dimension 4 = 1 + 1 + 2.
(Etingof Example 4.9.1) -/
theorem Etingof.Example4_9_1_S3_tensor :
    -- ℂ² ⊗ ℂ² ≅ ℂ₊ ⊕ ℂ₋ ⊕ ℂ² for S₃
    True := by  -- TODO: needs explicit representation construction
  sorry
