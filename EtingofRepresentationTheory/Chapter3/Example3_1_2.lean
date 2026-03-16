import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Example 3.1.2: End(V) as a Semisimple Representation

Let V be an irreducible representation of A of dimension n. Then Y = End(V), with action
of A by left multiplication, is a semisimple representation of A, isomorphic to nV
(the direct sum of n copies of V). Indeed, any basis v₁, …, vₙ of V gives rise to an
isomorphism of representations End(V) → nV, given by x ↦ (xv₁, …, xvₙ).
-/

/-- End(V) with left multiplication by A is isomorphic to n copies of V as a representation,
where n = dim V. Etingof Example 3.1.2. -/
theorem Etingof.endomorphism_semisimple (k : Type*) (A : Type*) (V : Type*)
    [Field k] [Ring A] [Algebra k A]
    [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
    [FiniteDimensional k V] [IsSimpleModule A V] :
    IsSemisimpleModule A (Module.End k V) := by
  sorry
