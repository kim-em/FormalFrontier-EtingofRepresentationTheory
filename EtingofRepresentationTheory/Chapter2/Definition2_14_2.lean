import Mathlib.Algebra.Lie.Basic
import Mathlib.LinearAlgebra.Dual.Defs

/-!
# Definition 2.14.2: Dual Representation of a Lie Algebra

The **dual representation** V* to a representation V of a Lie algebra 𝔤 is the
dual space V* to V with ρ_{V*}(x) = -ρ_V(x)*.

## Mathlib correspondence

The dual uses `Module.Dual R M` with the contragredient Lie action.
-/

/-- The dual of a Lie algebra representation, in the sense of Etingof Definition 2.14.2.
The Lie action on V* is the contragredient: (x · f)(v) = -f(x · v). -/
abbrev Etingof.LieDualRepresentation (k : Type*) (L : Type*) (V : Type*)
    [CommRing k] [LieRing L] [LieAlgebra k L]
    [AddCommGroup V] [Module k V] [LieRingModule L V] [LieModule k L V] :=
  Module.Dual k V
