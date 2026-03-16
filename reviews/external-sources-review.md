# Review: External Sources Research (Stage 2.5)

**Reviewed**: `research/external-sources.json` and `research/external-sources-summary.md`
**Cross-referenced against**: `research/mathlib-coverage-definitions.json`, `research/mathlib-coverage-external.json`
**Date**: 2026-03-16

## Summary

The external sources research is **mostly reliable within its stated scope**, but has a **critical scope gap**: 9 external dependencies with zero Mathlib coverage ("missing") were entirely excluded from the research. The data that IS present has accurate gap attributions (100% match for definitions) and references generally real, well-known mathematical texts. However, two MathComp source claims are fabricated.

**Overall reliability**: Moderate — good within scope, but incomplete scope and 2 fabricated sources reduce confidence.

## Critical Issues

### 1. Missing external dependencies excluded from research (9 items)

The research claims to cover "52 items" (16 gaps + 36 partial), but this count excludes all 9 external dependencies with `match_quality: "missing"` in `mathlib-coverage-external.json`. These are the items with ZERO Mathlib coverage — arguably the most important to find alternative sources for:

| External Dependency | Impact |
|---|---|
| Dynkin diagram classification | Required for Chapter 6 |
| Gabriel's theorem | Central to Chapter 6 |
| Krull-Schmidt theorem | Used across Chapters 2-3 |
| Schur-Weyl duality | Central to Chapter 5 |
| Frobenius reciprocity | Central to Chapter 5 |
| Mackey's theorem | Used in Chapter 5 |
| Generalized Schur orthogonality | Used in Chapters 4-5 |
| Deformation theory of algebras | Central to Chapter 10 |
| Hochschild cohomology | Central to Chapter 10 |

The summary misleadingly states "Remaining Uncovered Gaps: None" — this is only true for the 52 items in scope, not for the full set of gap/partial/missing items.

**Recommendation**: A follow-up issue should research external sources for these 9 missing external dependencies before the Readiness Report.

### 2. Fabricated MathComp Frobenius-Schur indicator references

Two entries claim MathComp (Coq) has a Frobenius-Schur indicator formalization:

- **Chapter5/Definition5.1.1** (complex/real/quaternionic types): Claims "character.v has Frobenius-Schur indicator and real/complex classification" — rated **high** usefulness
- **Chapter5/Definition5.1.4** (Frobenius-Schur indicator): Claims "character.v, cfun_indicator" — rated **high** usefulness

**Verification**: Web search confirms `cfun_indicator` in MathComp's `classfun.v` is a *class function indicator* (indicator function for conjugacy class subsets), NOT the Frobenius-Schur indicator ν(χ). No search results show MathComp has a Frobenius-Schur indicator formalization at all. These two "high usefulness" other_formal sources are **fabricated**.

**Impact**: Agents relying on these sources during Phase 3 would waste time looking for non-existent MathComp formalizations.

## Positive Findings

### Definition gap attribution: 100% accurate (37/37)

Every definition in `external-sources.json` has a `coverage_status` that exactly matches the `match_quality` in `mathlib-coverage-definitions.json`. No misattributions.

### External dependency attribution: 100% accurate (15/15)

All 15 external dependency entries in `external_dependency_gaps` correctly reflect their `partial` status from `mathlib-coverage-external.json` (descriptions match after accounting for truncation).

### Verified source references

The following textbook/paper references were spot-checked and confirmed as real, correctly attributed works:

| Item | Source | Verification |
|---|---|---|
| Chapter5/Definition5.7.1 | MathComp vcharacter.v | Confirmed: [vcharacter.v](https://github.com/math-comp/math-comp/blob/master/mathcomp/character/vcharacter.v) exists with virtual character theory (`'Z[irr G]`, `dirr G`, etc.) |
| Chapter5/Definition5.14.2 | Fulton, "Young Tableaux" | Real book (LMS Student Texts), Chapters 1-2 cover Kostka numbers |
| Chapter5/Definition5.14.2 | Stanley, EC2 Section 7.10 | Real reference, Section 7.10 covers symmetric functions and Kostka numbers |
| Chapter6/Definition6.6.3 | BGP 1973 paper | Real paper: Bernstein, Gelfand, Ponomarev (1973), Uspekhi Mat. Nauk |
| Chapter6/Definition6.6.3 | Schiffler Section 4.5 | Real book (Springer CMS, 2014), Section 4.5 covers reflection functors |
| Chapter9/Definition9.7.2 | Assem-Simson-Skowroński Section I.6 | Real book, Section I.6 covers basic algebras |
| Characters (ext dep) | MathComp classfun.v, character.v | Confirmed: [classfun.v](https://math-comp.github.io/htmldoc_1_10_0/mathcomp.character.classfun.html) and [character.v](https://math-comp.github.io/htmldoc/mathcomp.character.character.html) exist |

### Usefulness ratings are calibrated appropriately

- 66 high, 19 medium, 2 low (total 87 sources across 52 items)
- Low ratings applied to tangential references (MathComp mxalgebra.v for Wedderburn, MathComp module decomposition for indecomposable modules) — reasonable
- Medium ratings for supplementary references — reasonable
- High ratings for primary textbook treatments with detailed proofs — reasonable (excluding the 2 fabricated entries)

## Minor Issues

### 3. lean_library source references Mathlib itself

The "Combinatorics of partitions and Young diagrams" external dep entry includes a `lean_library` source: "Mathlib Nat.Partition and YoungDiagram — partial coverage". This is Mathlib itself, not an external source. The whole point of Stage 2.5 is to find sources OUTSIDE Mathlib for coverage gaps.

This doesn't cause downstream harm (it just restates known information) but is logically inconsistent.

### 4. Summary statistics are internally consistent

Verified: 87 total source entries = 79 natural_language + 7 other_formal + 1 lean_library. Matches the summary's claim. Usefulness breakdown matches (66 high + 19 medium + 2 low = 87).

## Recommendations

1. **Before Stage 2.6**: Create a follow-up issue to research external sources for the 9 missing external dependencies. The Readiness Report needs this data.
2. **Correct the 2 fabricated MathComp entries**: Remove or downgrade the Frobenius-Schur indicator claims for items 5.1.1 and 5.1.4. The natural language sources (Serre, Fulton & Harris) for these items are valid — only the MathComp references are wrong.
3. **Remove the Mathlib self-reference**: The lean_library entry for "Combinatorics of partitions" should be removed or reclassified.

## Spot-Check Sample Coverage

| Criterion | Required | Achieved |
|---|---|---|
| Entries spot-checked | ≥8 | 10 |
| Source types covered | All 3 | lean_library, other_formal, natural_language |
| Usefulness levels covered | All 3 | high, medium, low |
| Chapters represented | ≥3 | Chapters 2, 5, 6, 9, external deps |
| Fabricated sources found | — | 2 (MathComp Frobenius-Schur) |
| Attribution errors found | — | 0 (all 52 correct) |
