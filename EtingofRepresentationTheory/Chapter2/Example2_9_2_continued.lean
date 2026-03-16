import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.Subalgebra

/-!
# Example 2.9.2 (continued): Lie Subalgebras

(5) Any subspace 𝔞 of a Lie algebra 𝔤 which is closed under the commutator map [·, ·],
i.e., such that [a, b] ∈ 𝔞 if a, b ∈ 𝔞. Such a subspace is called a **Lie subalgebra** of 𝔤.

## Mathlib correspondence

Exact match. `LieSubalgebra R L` in Mathlib captures exactly this concept.
-/

/-- A Lie subalgebra is a subspace closed under the Lie bracket. (Etingof Example 2.9.2(5)) -/
example (k : Type*) [CommRing k] (L : Type*) [LieRing L] [LieAlgebra k L]
    (S : LieSubalgebra k L) : LieAlgebra k S := inferInstance
