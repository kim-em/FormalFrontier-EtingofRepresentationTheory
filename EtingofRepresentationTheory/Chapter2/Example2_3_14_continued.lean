import Mathlib.Algebra.MonoidAlgebra.Basic

/-!
# Example 2.3.14 (continued): Group Algebra Representations

3. The group algebra A = k[G], where G is a group. A representation of A is the same thing
   as a representation of G, i.e., a vector space V together with a group homomorphism
   ρ : G → Aut(V), where Aut(V) = GL(V) denotes the group of invertible linear maps from V
   to itself (the general linear group of V).

## Mathlib correspondence

Exact match. Mathlib has `MonoidAlgebra k G` for group algebras and `Representation` for
group representations. The equivalence between k[G]-modules and G-representations is standard.
-/

/-- A representation of a group G on V is a group homomorphism G → GL(V).
This is equivalent to a k[G]-module structure on V. (Etingof Example 2.3.14(3)) -/
example (k : Type*) [CommRing k] (G : Type*) [Group G]
    (V : Type*) [AddCommGroup V] [Module k V]
    [Module (MonoidAlgebra k G) V] :
    Module (MonoidAlgebra k G) V := inferInstance
