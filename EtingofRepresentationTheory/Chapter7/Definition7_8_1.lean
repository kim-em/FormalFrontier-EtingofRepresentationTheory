import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.Exact

/-!
# Definition 7.8.1: Complex, Differentials, Cohomology, Exact Sequence

A sequence of objects C_i (i ∈ ℤ) of an abelian category C and morphisms
d_i : C_i → C_{i+1} is a **complex** if the composition of any two consecutive
arrows is zero. The d_i are called **differentials**.

The **cohomology** is H^i = Ker(d_i)/Im(d_{i-1}). The complex is **exact** in the
i-th term if H^i = 0, and is an **exact sequence** if exact in all terms.

## Mathlib correspondence

Exact match:
- `HomologicalComplex` for complexes
- `HomologicalComplex.homology` for cohomology
- `CategoryTheory.Exact` for exactness
-/

open CategoryTheory

/-- A cochain complex in an abelian category, in the sense of Etingof Definition 7.8.1.
This is `CochainComplex` (= `HomologicalComplex` with `ComplexShape.up ℤ`) in Mathlib. -/
abbrev Etingof.CochainComplex' (C : Type*) [Category C]
    [Limits.HasZeroMorphisms C] := _root_.CochainComplex C ℤ
