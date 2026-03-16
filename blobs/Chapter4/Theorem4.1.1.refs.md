# References: Maschke's theorem

## External Dependencies

- **Fields: definition, algebraically closed fields, field extensions, finite fields, characteristic of a field** (undergraduate_prerequisite)
  Mathlib (exact): `Field`, `IsAlgClosed`, `IntermediateField`, `CharP`, `GaloisField`
  All core field theory is well-covered. `Field`, `IsAlgClosed`, `CharP` are standard typeclasses. Finite fields via `GaloisField` and `FiniteField.card`.
- **Vector spaces over a field: definition, dimension, subspaces, quotient spaces, direct sums, bases** (undergraduate_prerequisite)
  Mathlib (exact): `Module`, `FiniteDimensional`, `Module.finrank`, `Submodule`, `Submodule.Quotient`, `DirectSum`, `Basis`
  Vector spaces are modeled as `Module k V` where `k` is a `Field`. Dimension via `Module.finrank`. Full support for subspaces, quotients, direct sums, and bases.
- **Groups: definition, subgroups, normal subgroups, quotient groups, group homomorphisms, group actions, conjugacy classes, center of a group** (undergraduate_prerequisite)
  Mathlib (exact): `Group`, `Subgroup`, `Subgroup.Normal`, `QuotientGroup.Quotient`, `MonoidHom`, `MulAction`, `ConjClasses`, `Subgroup.center`
  Comprehensive group theory. All listed concepts have direct Mathlib counterparts.
- **Group algebra k[G]: construction, basis indexed by group elements, convolution product** (undergraduate_prerequisite)
  Mathlib (exact): `MonoidAlgebra`
  `MonoidAlgebra k G` is the group algebra. It has the correct basis and convolution product structure. For finite groups, this is `k[G]`.
- **Dimension counting arguments: if V = W ⊕ W' as vector spaces then dim V = dim W + dim W'; rank-nullity theorem** (folklore)
  Mathlib (exact): `LinearMap.rank_range_add_rank_ker`, `Submodule.finrank_sup_add_finrank_inf_eq`, `Module.finrank`
  Rank-nullity via `LinearMap.rank_range_add_rank_ker`. Dimension of direct sums available. `Module.finrank` for finite-dimensional spaces.
- **Averaging (Reynolds) operator for finite group actions: (1/|G|) Σ_g ρ(g) is the projection onto invariants when char k does not divide |G|** (folklore)
  Mathlib (partial): `Representation`, `IsSemisimpleModule`
  The averaging operator is not explicitly named in Mathlib, but `IsSemisimpleModule` captures its consequence (complete reducibility). Maschke's theorem (semisimplicity of group algebra when char k ∤ |G|) is available via the semisimplicity framework.
  External source [natural_language]: Serre, 'Linear Representations of Finite Groups' — Section 1.3
