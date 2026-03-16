# External Sources for Mathlib Coverage Gaps (Stage 2.5)

## Overview

From Stage 2.4, we identified **52 items** with incomplete Mathlib coverage:
- **16 full gaps** (no Mathlib coverage) — all in book definitions
- **36 partial matches** (21 definitions + 15 external dependencies)

This document summarizes available external sources for these gaps.

## Coverage Summary

| Category | Total gaps/partial | With external sources | Uncovered |
|----------|-------------------|----------------------|-----------|
| Definition gaps (full) | 16 | 16 | 0 |
| Definition gaps (partial) | 21 | 21 | 0 |
| External dep gaps (partial) | 15 | 15 | 0 |
| **Total** | **52** | **52** | **0** |

All 52 gap/partial items have at least one external source identified.

## Source Types

### Other Formal Systems

**MathComp (Coq)** is the most relevant formal source, particularly for:
- Character theory (classfun.v, character.v) — covers Frobenius-Schur indicator, virtual characters, class functions, orthogonality
- This directly addresses 4 definition gaps: Frobenius-Schur indicator, real/complex/quaternionic types, virtual representations, character properties

No other Lean 4 libraries outside Mathlib provide significant representation theory coverage. The Lean ecosystem's representation theory is concentrated in Mathlib.

### Natural Language Sources — Key References by Topic Area

**Quiver representations (Chapter 6 gaps — 10 items)**:
- **Schiffler, "Quiver Representations"** — Primary reference. Covers all quiver-related gaps: path algebras, dimension vectors, sinks/sources, reflection functors, roots, Dynkin diagrams. Highly detailed, suitable for formalization.
- **Assem, Simson, Skowroński, "Elements of the Representation Theory of Associative Algebras, Vol. 1"** — Complementary reference with different proof approaches.

**Symmetric group representations (Chapter 5 gaps — 6 items)**:
- **Serre, "Linear Representations of Finite Groups"** — Frobenius-Schur indicator, real/complex/quaternionic classification, virtual representations. Complete proofs.
- **Fulton, "Young Tableaux"** — Kostka numbers, semistandard tableaux, Young diagrams.
- **Sagan, "The Symmetric Group"** — Alternative treatment bridging combinatorics and representation theory.
- **Green, "Polynomial Representations of GL_n"** — Algebraic/polynomial representations of GL(V).

**Homological algebra (Chapter 8-9 gaps — 8 items)**:
- **Weibel, "An Introduction to Homological Algebra"** — Ext/Tor functors, projective dimension, global dimension.
- **Assem, Simson, Skowroński, Vol. 1** — Cartan matrices, projective covers, blocks, basic algebras.
- **Auslander, Reiten, Smalø, "Representation Theory of Artin Algebras"** — Advanced treatment of homological dimensions and Artin algebra structure.

**Ring theory and module theory (supporting gaps)**:
- **Lam, "A First Course in Noncommutative Rings"** — Wedderburn-Artin, Morita equivalence, nilpotent ideals.
- **Anderson & Fuller, "Rings and Categories of Modules"** — Projective covers, progenerators, Morita theory.

## Remaining Uncovered Gaps

**None.** Every gap and partial item has at least one detailed natural language source with step-by-step proofs suitable for formalization guidance.

## Recommendations for Formalization Order

Based on source availability and dependency structure:

1. **Start with items having MathComp formalizations** — Frobenius-Schur indicator, virtual characters, character properties. The Coq formalizations provide a tested proof strategy that can be adapted to Lean.

2. **Quiver representations are self-contained** — The Chapter 2 quiver definitions (2.8.x) and Chapter 6 items form a coherent block. Schiffler's textbook provides a complete, formalization-ready treatment.

3. **Homological algebra items (Chapter 9) depend on each other** — Projective covers → Cartan matrix → blocks → basic algebras. Formalize in this order using Assem-Simson-Skowroński.

4. **Symmetric group combinatorics (Chapter 5) can proceed independently** — Young tableaux, Kostka numbers, and polynomial representations of GL(V) use different machinery from the algebra/module items.

## Source Usefulness Ratings

| Rating | Count | Description |
|--------|-------|-------------|
| High | 66 | Direct, detailed proofs suitable for formalization |
| Medium | 19 | Useful context but may need adaptation or supplementation |
| Low | 2 | Tangential reference; different proof system or approach |

Total: 87 source entries across 52 gap/partial items (1.7 sources per item on average).

The high proportion of "high usefulness" ratings reflects that these are well-studied mathematical topics with multiple standard textbook treatments.
