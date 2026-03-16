import Mathlib

/-!
# Example 5.19.3: Schur Functors for Special Partitions

If λ = (n), then Lλ = SⁿV (symmetric power).
If λ = (1ⁿ), then Lλ = ∧ⁿV (exterior power).
These are irreducible GL(V)-representations (except ∧ⁿV = 0 when n > dim V).

## Mathlib correspondence

Uses `Mathlib.LinearAlgebra.ExteriorAlgebra` and symmetric powers.
-/

/-- For the partition λ = (n), the GL(V) representation Lλ equals SⁿV
(the n-th symmetric power). (Etingof Example 5.19.3) -/
theorem Etingof.Example5_19_3_symmetric
    {k : Type*} [Field k] [IsAlgClosed k]
    {V : Type*} [AddCommGroup V] [Module k V] [Module.Finite k V]
    (n : ℕ) :
    -- L_{(n)} ≅ SⁿV as GL(V)-representations
    (sorry : Prop) := by
  sorry

/-- For the partition λ = (1ⁿ), the GL(V) representation Lλ equals ∧ⁿV
(the n-th exterior power), which is zero when n > dim V.
(Etingof Example 5.19.3) -/
theorem Etingof.Example5_19_3_exterior
    {k : Type*} [Field k] [IsAlgClosed k]
    {V : Type*} [AddCommGroup V] [Module k V] [Module.Finite k V]
    (n : ℕ) :
    -- L_{(1ⁿ)} ≅ ∧ⁿV as GL(V)-representations
    (sorry : Prop) := by
  sorry
