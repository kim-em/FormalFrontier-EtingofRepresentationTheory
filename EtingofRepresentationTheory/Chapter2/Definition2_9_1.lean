import Mathlib.Algebra.Lie.Basic

/-!
# Definition 2.9.1: Lie Algebra

(𝔤, [·, ·]) is a **Lie algebra** if [·, ·] satisfies the Jacobi identity:
[[a, b], c] + [[b, c], a] + [[c, a], b] = 0.

## Mathlib correspondence

This is `LieAlgebra R L` with `LieRing L`. The Jacobi identity is built into `LieRing`.
-/

/-- A Lie algebra, in the sense of Etingof Definition 2.9.1.
This is `LieAlgebra k L` with `LieRing L` in Mathlib. -/
abbrev Etingof.LieAlgebraDef (k : Type*) (L : Type*) [CommRing k] [LieRing L] :=
  LieAlgebra k L
