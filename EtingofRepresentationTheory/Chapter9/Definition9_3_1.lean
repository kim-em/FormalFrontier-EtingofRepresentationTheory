import Mathlib.Data.Matrix.Basic
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.Order.JordanHolder

/-!
# Definition 9.3.1: Cartan matrix

The **Cartan matrix** of a finite dimensional algebra A is the matrix C = (cᵢⱼ), where
cᵢⱼ = [Pⱼ : Mᵢ] is the multiplicity of Mᵢ in the Jordan–Hölder series of Pⱼ.

By Proposition 9.2.3, cᵢⱼ = dim Hom_A(Pᵢ, Pⱼ). Thus C has nonneg integer entries and
positive diagonal entries.

## Mathlib correspondence

Not directly in Mathlib. The Cartan matrix is specific to representation theory of
finite dimensional algebras. Jordan–Hölder series exist in Mathlib
(`Mathlib.Order.JordanHolder`), but the multiplicity-counting function for a specific
composition factor is not yet available.

## Formalization approach

We define the Cartan matrix parametrically: given an indexing type `ι` for the simple
modules and a function that computes the Jordan–Hölder multiplicity of the i-th simple
in the j-th projective indecomposable, the Cartan matrix is simply the matrix of those
multiplicities. The multiplicity function itself is left as a parameter since its
construction requires the full Jordan–Hölder theory for modules, which is not yet
assembled in Mathlib.
-/

/-- The Cartan matrix of a finite dimensional algebra, in the sense of Etingof Definition 9.3.1.

Given `n` isomorphism classes of simple modules M₁, …, Mₙ and corresponding projective
covers P₁, …, Pₙ, the Cartan matrix is the `n × n` matrix with entries
`cᵢⱼ = [Pⱼ : Mᵢ]`, the Jordan–Hölder multiplicity of Mᵢ in Pⱼ.

The multiplicity function `jhMultiplicity i j` is taken as a parameter. By Proposition
9.2.3, this equals `dim_k Hom_A(Pᵢ, Pⱼ)` when the algebra is finite-dimensional over
an algebraically closed field. -/
def Etingof.cartanMatrix {n : ℕ} (jhMultiplicity : Fin n → Fin n → ℕ) :
    Matrix (Fin n) (Fin n) ℕ :=
  Matrix.of jhMultiplicity
