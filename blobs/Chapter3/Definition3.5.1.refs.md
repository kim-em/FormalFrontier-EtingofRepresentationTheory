# References: Radical of a finite dimensional algebra

## Mathlib Coverage (exact)

- `Ideal.jacobson`

The Jacobson radical is `Ideal.jacobson ⊥` (intersection of all maximal left ideals). For finite dimensional algebras this equals the radical.

## External Dependencies

- **Modules over rings: left modules, right modules, submodules, quotient modules, free modules, simple modules** (undergraduate_prerequisite)
  Mathlib (exact): `Module`, `Submodule`, `Submodule.Quotient`, `Module.Free`, `IsSimpleModule`
  Full module theory. Mathlib uses left modules by convention. `IsSimpleModule` for simple modules. Free modules via `Module.Free`.
- **Jordan-Hölder theorem: any two composition series of a finite-length module have the same length and the same composition factors (up to reordering and isomorphism)** (external_result)
  Mathlib (partial): `CompositionSeries`, `JordanHolderLattice`
  `CompositionSeries` and `JordanHolderLattice` provide the framework. The Jordan-Hölder theorem is stated in terms of lattices satisfying `JordanHolderLattice`. The connection to module composition series requires showing modules form a `JordanHolderLattice`.
  External source [natural_language]: Lang, 'Algebra' — Chapter III, Section 3
