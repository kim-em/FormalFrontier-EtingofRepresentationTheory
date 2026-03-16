import Mathlib.LinearAlgebra.Dual.Defs


/-!
# Definition 3.3.2: Dual Representation

Let V be a representation of any algebra A. Then the dual representation V* is the
representation of the opposite algebra A^op (or, equivalently, right A-module) with the action

  (f · a)(v) := f(av).

## Mathlib correspondence

`Module.Dual R M` is the dual vector space. For group representations,
`Representation.dual` gives the contragredient.
-/

/-- The dual representation in the sense of Etingof Definition 3.3.2.
Given a left A-module V, the dual V* = Hom_k(V, k) is naturally an A^op-module.
This is `Module.Dual` in Mathlib. -/
abbrev Etingof.DualRepresentation (k : Type*) (V : Type*)
    [CommSemiring k] [AddCommMonoid V] [Module k V] :=
  Module.Dual k V
