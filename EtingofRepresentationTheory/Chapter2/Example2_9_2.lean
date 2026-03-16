import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.OfAssociative

/-!
# Example 2.9.2: Examples of Lie Algebras

(1) Any space 𝔤 with [·, ·] = 0 (abelian Lie algebra).
(2) Any associative algebra A with [a, b] = ab − ba, in particular End(V), denoted 𝔤𝔩(V).
(3) Any subspace U of an associative algebra A closed under [·, ·].
(4) The space Der(A) of derivations of an algebra A.

## Mathlib correspondence

Exact match. Mathlib has `LieAlgebra`, `LieRing`, abelian Lie algebras, and the Lie bracket
on associative algebras via `LieRing` instances from `Mathlib.Algebra.Lie.OfAssociative`.
-/

/-- Any associative algebra has a Lie algebra structure via [a, b] = ab - ba.
(Etingof Example 2.9.2(2)) -/
example (k : Type*) [CommRing k] (A : Type*) [Ring A] [Algebra k A] :
    LieRing A := inferInstance

/-- End(V) = 𝔤𝔩(V) is a Lie algebra. (Etingof Example 2.9.2(2)) -/
example (k : Type*) [CommRing k] (V : Type*) [AddCommGroup V] [Module k V] :
    LieAlgebra k (Module.End k V) := inferInstance
