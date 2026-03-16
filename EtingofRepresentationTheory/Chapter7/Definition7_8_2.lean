import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Definition 7.8.2: Short Exact Sequence

A **short exact sequence** is an exact sequence of the form:
0 → X → Y → Z → 0

This holds iff X → Y is injective, Y → Z is surjective, and the induced map
Y/X → Z is an isomorphism. Short exact sequences correspond to extensions of Z by X.

## Mathlib correspondence

Exact match: `CategoryTheory.ShortComplex` and `CategoryTheory.ShortComplex.ShortExact`.
-/

/-- A short complex in an abelian category, in the sense of Etingof Definition 7.8.2.
A short exact sequence is a `ShortComplex` satisfying `ShortExact`.
This is `CategoryTheory.ShortComplex` in Mathlib. -/
abbrev Etingof.ShortComplex (C : Type*) [CategoryTheory.Category C]
    [CategoryTheory.Limits.HasZeroMorphisms C] := CategoryTheory.ShortComplex C
