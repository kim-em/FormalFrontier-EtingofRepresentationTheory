import Mathlib.Algebra.Lie.Basic

/-!
# Definition 2.9.7: Representation of a Lie Algebra

A **representation** of a Lie algebra 𝔤 is a vector space V with a homomorphism of
Lie algebras ρ : 𝔤 → End V.

## Mathlib correspondence

This is `LieModule R L M` — a Lie module structure on M over the Lie algebra L.
-/

/-- A representation of a Lie algebra, in the sense of Etingof Definition 2.9.7.
This is `LieModule k L V` in Mathlib. -/
abbrev Etingof.LieAlgebraRepresentation (k : Type*) (L : Type*) (V : Type*)
    [CommRing k] [LieRing L] [LieAlgebra k L] [AddCommGroup V] [Module k V]
    [LieRingModule L V] :=
  LieModule k L V
