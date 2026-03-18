import Mathlib.Algebra.Lie.Classical
import Mathlib.Algebra.Lie.Semisimple.Defs
import Mathlib.Algebra.Lie.Sl2
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Theorem 2.1.1: Classification of irreducible representations of U(sl(2))

Let k = ℂ be the field of complex numbers. Then:

(i) The algebra U(sl(2)) has exactly one irreducible representation V_d of each dimension d,
up to equivalence; this representation is realized in the space of homogeneous polynomials of
two variables x, y of degree d - 1.

(ii) Any indecomposable finite dimensional representation of U(sl(2)) is irreducible. That is,
any finite dimensional representation of U(sl(2)) is a direct sum of irreducible representations.

## Mathlib correspondence

Partial match. Mathlib has `LieAlgebra`, `LieModule`,
`LieAlgebra.SpecialLinear.sl` (special linear Lie algebra), and
`LieModule.IsIrreducible`, but the classification of irreducible
sl(2)-representations and complete reducibility are not in Mathlib.

## Formalization note

We formalize sl(2, ℂ) as `LieAlgebra.SpecialLinear.sl (Fin 2) ℂ`,
the traceless 2×2 complex matrices.
Part (i) states existence and uniqueness (up to Lie module isomorphism) of an irreducible
representation in each positive dimension. Part (ii) states complete reducibility: every
finite-dimensional Lie module over sl(2, ℂ) has a complemented lattice of Lie submodules.
-/

open scoped Matrix

namespace Etingof

/-- The Lie algebra sl(2, ℂ), the traceless 2×2 complex matrices. -/
abbrev sl2 : LieSubalgebra ℂ (Matrix (Fin 2) (Fin 2) ℂ) := LieAlgebra.SpecialLinear.sl (Fin 2) ℂ

/-- Part (i): For each positive integer d, there is exactly one irreducible representation
of sl(2, ℂ) of dimension d, up to isomorphism.
(Etingof Theorem 2.1.1(i)) -/
theorem Theorem_2_1_1_i (d : ℕ+) :
    -- Existence: there is an irreducible representation of dimension d
    (∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V)
       (_ : LieRingModule sl2 V) (_ : LieModule ℂ sl2 V),
       Module.finrank ℂ V = d ∧ LieModule.IsIrreducible ℂ sl2 V) ∧
    -- Uniqueness: any two irreducible representations of the same dimension are isomorphic
    (∀ (V W : Type) [AddCommGroup V] [Module ℂ V] [LieRingModule sl2 V] [LieModule ℂ sl2 V]
       [AddCommGroup W] [Module ℂ W] [LieRingModule sl2 W] [LieModule ℂ sl2 W],
       Module.finrank ℂ V = d → LieModule.IsIrreducible ℂ sl2 V →
       Module.finrank ℂ W = d → LieModule.IsIrreducible ℂ sl2 W →
       Nonempty (V ≃ₗ⁅ℂ, sl2⁆ W)) := sorry

/-- Part (ii): Any finite-dimensional representation of sl(2, ℂ) is completely reducible.
Every Lie submodule has a complementary Lie submodule, i.e., the lattice of Lie submodules
is complemented. This is equivalent to saying every finite-dimensional representation
decomposes as a direct sum of irreducible representations.
(Etingof Theorem 2.1.1(ii)) -/
theorem Theorem_2_1_1_ii (V : Type*) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [LieRingModule sl2 V] [LieModule ℂ sl2 V] :
    ComplementedLattice (LieSubmodule ℂ sl2 V) := sorry

end Etingof
