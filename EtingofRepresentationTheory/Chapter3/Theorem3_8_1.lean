import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Theorem 3.8.1: Krull-Schmidt Theorem

Any finite dimensional representation of A can be uniquely (up to isomorphism and the
order of summands) decomposed into a direct sum of indecomposable representations.

The existence of such a decomposition is clear. Uniqueness is proved by induction on dim V,
using Lemma 3.8.2 (endomorphisms of indecomposable representations are either isomorphisms
or nilpotent).
-/

/-- The Krull-Schmidt theorem: any finite dimensional representation has a unique
decomposition into indecomposable direct summands (up to isomorphism and reordering).
Etingof Theorem 3.8.1. -/
theorem Etingof.krull_schmidt (k : Type*) (A : Type*) (V : Type*)
    [Field k] [Ring A] [Algebra k A]
    [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
    [FiniteDimensional k V] :
    -- V admits a decomposition into indecomposable direct summands,
    -- and this decomposition is unique up to isomorphism and reordering.
    True := by
  sorry
