# External Dependency Analysis (Stage 2.2)

External dependencies are mathematical concepts, definitions, and results that Etingof's
"Introduction to Representation Theory" uses but does not prove.

## Summary

| Category | Count | Description |
|----------|-------|-------------|
| `undergraduate_prerequisite` | 33 | Standard undergraduate algebra, linear algebra, and analysis |
| `external_result` | 15 | Named theorems from outside the book, cited or assumed |
| `folklore` | 10 | Well-known facts used without proof or citation |
| **Total** | **58** | |

163 of 578 items (28%) reference at least one external dependency.

## Chapter Breakdown

| Chapter | Items Referencing External Deps | Primary External Dependencies |
|---------|-------------------------------|-------------------------------|
| 2 (Basic Notions) | 36 | Fields, vector spaces, linear algebra, groups, rings, tensor products, Lie algebras |
| 3 (General Results) | 17 | Zorn's lemma, Jordan-Hölder theorem, Wedderburn-Artin, nilpotent ideals |
| 4 (Finite Groups: Basics) | 16 | Group algebra, characters, inner products, symmetric group |
| 5 (Finite Groups: Further) | 43 | Algebraic integers, partitions/Young diagrams, symmetric polynomials, finite fields |
| 6 (Quiver Representations) | 9 | Graph theory, Dynkin diagrams, quadratic forms |
| 7 (Categories) | 18 | Set theory, abelian categories, adjoint functors, natural transformations |
| 8 (Homological Algebra) | 9 | Exact sequences, Hom functor, free modules, Ext functors |
| 9 (Finite-Dim Algebras) | 15 | Idempotents, Nakayama's lemma, Hochschild cohomology, deformation theory |

Chapter 1 is a brief introduction with no formal mathematical content requiring external dependencies.

## Mathlib Areas Likely Needed

Based on the external dependencies, these Mathlib areas are critical for formalization:

- **Mathlib.Algebra.Group**: Group theory basics, subgroups, quotient groups, group actions
- **Mathlib.Algebra.Ring**: Ring theory, ideals, quotient rings
- **Mathlib.Algebra.Module**: Module theory, free modules, simple modules
- **Mathlib.LinearAlgebra**: Vector spaces, linear maps, dual spaces, tensor products, bilinear forms
- **Mathlib.LinearAlgebra.Matrix**: Matrix operations, trace, determinant, eigenvalues
- **Mathlib.RingTheory**: Semisimple rings, Jacobson radical, Wedderburn-Artin
- **Mathlib.GroupTheory.SpecificGroups.Symmetric**: Symmetric group, permutations, cycle decomposition
- **Mathlib.Combinatorics.Partition**: Partitions, Young diagrams/tableaux
- **Mathlib.FieldTheory.Finite**: Finite fields, field extensions
- **Mathlib.NumberTheory.NumberField**: Algebraic integers (for Burnside's theorem proof)
- **Mathlib.CategoryTheory**: Categories, functors, natural transformations, abelian categories, adjunctions
- **Mathlib.Algebra.Homology**: Chain complexes, exact sequences, Ext functors
- **Mathlib.Algebra.Lie**: Lie algebras, universal enveloping algebras
- **Mathlib.RepresentationTheory**: Group representations, characters (if available)
- **Mathlib.Order.Zorn**: Zorn's lemma

## Heaviest Dependencies

Items with the most external prerequisites:

1. **Theorem 4.5.1** (Character orthogonality) — 8 external deps
2. **Theorem 4.1.1** (Maschke's theorem) — 6 external deps
3. **Discussion 5.25.1** (GL_2(F_q) conjugacy classes) — 5 external deps
4. **Definition 4.6.1** (Characters) — 5 external deps
5. **Lemma 5.4.5** (Roots of unity algebraic integer lemma) — 5 external deps

## Validation

Run `python3 scripts/validate_external_deps.py` to verify `dependencies/external.json`
against the schema and `progress/items.json`.
