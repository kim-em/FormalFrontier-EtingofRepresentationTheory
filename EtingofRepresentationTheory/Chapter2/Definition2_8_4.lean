import Mathlib.Algebra.Algebra.Basic
import Mathlib.Combinatorics.Quiver.Path

/-!
# Definition 2.8.4: Path Algebra of a Quiver

The **path algebra** P_Q of a quiver Q is the algebra whose basis is formed by oriented
paths in Q, including the trivial paths pᵢ, i ∈ I, corresponding to the vertices of Q,
and multiplication is the concatenation of paths.

## Mathlib correspondence (partial)

Mathlib has `Quiver.Path` (composable sequences of arrows) and path categories.
The full path algebra as a k-algebra needs construction. We provide a sorry'd definition.
-/

-- not in Mathlib as of v4.28 (path algebra as a k-algebra)
/-- The path algebra of a quiver Q over a field k, in the sense of Etingof Definition 2.8.4.
The basis consists of oriented paths in Q, with multiplication given by path concatenation
(zero if paths are not composable). -/
noncomputable def Etingof.PathAlgebra (k : Type*) (Q : Type*) [Field k] [Quiver Q]
    [DecidableEq Q] : Type* :=
  sorry
