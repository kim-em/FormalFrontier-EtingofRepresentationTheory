# Phase 2 Completion Summary: Dependency Mapping

**Date:** 2026-03-16
**Scope:** Stages 2.1–2.5 (all research stages of Phase 2)
**Status:** Complete. Stage 2.6 (Readiness Report) remains — that is a separate deliverable and a human checkpoint.

## Timeline

| Stage | Issue(s) | PR(s) | Completed |
|-------|----------|-------|-----------|
| 2.1: Internal Dependency Analysis | #454 | #462 | 2026-03-16 |
| 2.2: External Dependency Analysis | #470 | #462 | 2026-03-16 |
| 2.1–2.2 Accuracy Review | #473 | #476 | 2026-03-16 |
| 2.3: Blueprint Assembly | #462 | #480 | 2026-03-16 |
| 2.3 Blueprint Review | #477 | #487 | 2026-03-16 |
| 2.4 part 1: Mathlib Coverage (External Deps) | #472 | #479 | 2026-03-16 |
| 2.4 part 1 Review | #483 | #490 | 2026-03-16 |
| 2.4 part 2: Mathlib Coverage (Book Definitions) | #474 | #486 | 2026-03-16 |
| 2.4 part 2 Review | #492 | #495 | 2026-03-16 |
| 2.5: External Sources Research | #478 | #491 | 2026-03-16 |
| 2.5 Review | #492 | #493 | 2026-03-16 |

All of Phase 2's research stages completed within one calendar day (2026-03-16), with 7 PRs merged since the last summarize (#471).

## Key Metrics

### Items and Dependencies
- **583 items** in the formalization DAG (from `items.json`)
- **583 internal dependency entries** (conservative: each item depends on all predecessors)
- **58 external dependencies** (33 undergraduate prerequisites, 15 external results, 10 folklore)
- 163 of 583 items (28%) reference at least one external dependency

### Mathlib Coverage — External Dependencies (58 entries)
- **34 exact matches** (59%) — Mathlib has the needed concept or theorem
- **15 partial matches** (26%) — infrastructure exists but specific theorem is absent
- **9 missing** (16%) — no Mathlib coverage (e.g., Dynkin diagrams, Gabriel's theorem, Schur-Weyl duality, Frobenius reciprocity, Hochschild cohomology)

### Mathlib Coverage — Book Definitions (83 entries)
- **46 exact matches** (55%) — direct Mathlib equivalent exists
- **21 partial matches** (25%) — building blocks available, assembly needed
- **16 gaps** (19%) — must be defined from scratch (e.g., Frobenius determinant, virtual representations, quiver-specific concepts, projective dimension, blocks)

Best coverage: Chapter 7 (categories, 92% exact), Chapter 2 (basic rep theory, 76% exact).
Weakest coverage: Chapter 6 (quiver representations), Chapter 5 (advanced group reps), Chapter 9 (finite dimensional algebras).

### External Sources for Gaps (52 items researched)
- **100% of gap and partial items** have at least one identified external source
- 87 source entries total (1.7 sources per item on average)
- 66 rated "high usefulness" — directly formalization-ready
- Primary formal source: MathComp (Coq) for character theory
- Primary natural language sources: Schiffler (quiver representations), Serre/Fulton (symmetric groups), Weibel/Auslander-Reiten-Smalø (homological algebra)

## Data Files Produced

| File | Description |
|------|-------------|
| `dependencies/internal.json` | Internal dependency graph (583 entries) |
| `dependencies/external.json` | External dependencies (58 entries) |
| `blueprint/src/content.tex` | leanblueprint LaTeX with 583 items and dependency edges |
| `research/mathlib-coverage-external.json` | Mathlib coverage for 58 external deps |
| `research/mathlib-coverage-definitions.json` | Mathlib coverage for 83 book definitions |
| `research/external-sources.json` | External sources for 52 gap/partial items |
| `research/review-mathlib-coverage-external.md` | Review of external deps coverage |
| `research/mathlib-coverage-definitions-summary.md` | Summary of definitions coverage |
| `research/external-sources-summary.md` | Summary of external sources |
| `reviews/stage-2.3-blueprint-review.md` | Blueprint assembly review |

## Quality Findings from Reviews

### Dependency Accuracy Review (#473/#476)
- **Internal dependencies:** 100% accurate on 10-item spot check. Zero false negatives.
- **External dependencies:** Descriptions accurate, but **~50% item-attribution error rate** — the external dependency *descriptions* are correct (the right mathematical concepts are identified), but the *item IDs* attributing which book items use them are often wrong. Recommendation: use descriptions (not item attributions) for downstream stages; fix attributions during Stage 3.3 dependency trimming.

### Blueprint Assembly Review (#477/#487)
- All 583 items present with correct labels and environment types
- Internal dependency edges match `dependencies/internal.json` exactly (10-item spot check)
- External dependency nodes included in DAG
- HTML blueprint builds successfully via plastex

### Mathlib Coverage Review — External Deps (#483/#490)
- Coverage classifications (exact/partial/missing) are accurate
- **4 wrong Mathlib declaration names** found and corrected: `FiniteField`, `ZMod.legendreSym`, `CategoryTheory.Functor.PreservesFiniteLimits`, `CategoryTheory.Functor.Representable`
- Pattern identified: some "missing" entries list existing infrastructure names (correct behavior, but potentially confusing for automation)

### Mathlib Coverage Review — Definitions (#492/#495)
- Coverage breakdown validated (55%/25%/19%)
- Chapter-level analysis confirmed

### External Sources Review (#492/#493)
- All 52 gap/partial items have sources
- Source usefulness ratings validated

## Limitations and Honest Assessment

1. **Conservative dependencies are very conservative.** Every item depends on all predecessors — the DAG is essentially linear. This is correct per plan (trimming happens in Stage 3.3), but it means the blueprint's visual dependency graph is not informative about true mathematical dependencies until formalization is done.

2. **External dependency item attribution is unreliable.** While the *existence* and *description* of all 58 external dependencies is validated, which specific book items use each dependency is wrong ~50% of the time. This doesn't block Stage 2.6 or Stage 3 (the descriptions are what matter for Mathlib lookup), but it means `dependencies/external.json` should not be trusted for item-level dependency tracking.

3. **No `#check` verification was done for definitions coverage.** The external deps review (#490) verified Mathlib names with `#check`; the definitions coverage (#495) was validated at the classification level but individual Mathlib declaration names were not systematically verified against the compiler.

4. **Phase 2 does not include Stage 2.6 (Readiness Report) or Stage 2.7 (Reference Attachment).** These are downstream deliverables. Stage 2.6 is the human checkpoint before Phase 3 begins.

## What's Next

- **Stage 2.6: Readiness Report** (#484, unclaimed) — synthesize all Phase 2 data into a human-readable readiness assessment. This is the human checkpoint before Phase 3 formalization begins.
- **Stage 2.6 Review** (#494) — blocked on #484.
- After human approval at Stage 2.6, proceed to Stage 2.7 (Reference Attachment) and then Phase 3 (Formalization).
