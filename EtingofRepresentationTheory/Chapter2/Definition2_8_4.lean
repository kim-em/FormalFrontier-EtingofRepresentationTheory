import Mathlib.Algebra.Algebra.Basic
import Mathlib.Combinatorics.Quiver.Path
import Mathlib.Data.Finsupp.Defs

/-!
# Definition 2.8.4: Path Algebra of a Quiver

The **path algebra** P_Q of a quiver Q is the algebra whose basis is formed by oriented
paths in Q, including the trivial paths pᵢ, i ∈ I, corresponding to the vertices of Q,
and multiplication is the concatenation of paths.

## Mathlib correspondence (partial)

Mathlib has `Quiver.Path` (composable sequences of arrows) and path categories.
We define the path algebra as the free k-module on the type of all oriented paths
(pairs of vertices together with a path between them), equipped with a ring structure
from path concatenation.
-/

/-- The type of all oriented paths in a quiver: a triple (source, target, path). -/
def Etingof.QuiverPathIndex (Q : Type*) [Quiver Q] : Type _ :=
  Σ (a : Q) (b : Q), Quiver.Path a b

/-- The path algebra of a quiver Q over a field k, in the sense of Etingof Definition 2.8.4.
The basis consists of oriented paths in Q, with multiplication given by path concatenation
(zero if paths are not composable). -/
noncomputable def Etingof.PathAlgebra (k : Type*) (Q : Type*) [Field k] [Quiver Q]
    [DecidableEq Q] : Type _ :=
  Etingof.QuiverPathIndex Q →₀ k
