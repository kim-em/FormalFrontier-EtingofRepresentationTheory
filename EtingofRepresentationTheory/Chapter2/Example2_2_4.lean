import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.FreeAlgebra
import Mathlib.Algebra.MonoidAlgebra.Basic

/-!
# Example 2.2.4: Examples of Algebras

Examples of algebras over k:
1. A = k.
2. A = k[x₁, …, xₙ] — the algebra of polynomials.
3. A = End V — the algebra of endomorphisms of a vector space V.
4. The free algebra A = k⟨x₁, …, xₙ⟩.
5. The group algebra A = k[G] of a group G.

## Mathlib correspondence

Exact match. All five examples have Mathlib counterparts:
- k as an algebra over itself
- `MvPolynomial` for polynomial algebras
- `Module.End` for endomorphism algebras
- `FreeAlgebra` for free algebras
- `MonoidAlgebra` for group algebras
-/

/-- k is an algebra over itself. (Etingof Example 2.2.4(1)) -/
example (k : Type*) [CommRing k] : Algebra k k := inferInstance

/-- The polynomial algebra k[X] is an algebra over k. (Etingof Example 2.2.4(2)) -/
noncomputable example (k : Type*) [CommRing k] : Algebra k (Polynomial k) := inferInstance

/-- End(V) is an algebra over k. (Etingof Example 2.2.4(3)) -/
example (k : Type*) [CommRing k] (V : Type*) [AddCommGroup V] [Module k V] :
    Algebra k (Module.End k V) := inferInstance

/-- The free algebra k⟨x₁, …, xₙ⟩ is an algebra over k. (Etingof Example 2.2.4(4)) -/
example (k : Type*) [CommRing k] (n : Type*) : Algebra k (FreeAlgebra k n) := inferInstance

/-- The group algebra k[G] is an algebra over k. (Etingof Example 2.2.4(5)) -/
noncomputable example (k : Type*) [CommRing k] (G : Type*) [Group G] :
    Algebra k (MonoidAlgebra k G) := inferInstance
