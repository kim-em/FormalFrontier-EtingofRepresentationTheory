# Sorry Landscape Analysis — Wave 30

Generated 2026-03-23 by summarize session (issue #1638).

## Summary

**51 sorries** across 24 files. Down from 61 sorries / 26 files in wave 29 (−10 sorries, −2 files). Chapters 3, 4, 7, 8 remain 100% sorry-free. 242 of 266 Lean files (91.0%) are sorry-free. 564 of 583 items (96.7%) sorry-free.

13 PRs merged since wave 29 (#1617–#1635 + #1640). Key wins:
- **Theorem_Dynkin_classification** became sorry-free (−6 sorries, PR #1634) — entire Dynkin diagram classification proved
- **Lemma5_25_3** became sorry-free (−1 sorry, PR #1631) — elliptic norm-squared sum computation complete
- **Problem6_9_1** reduced from 2 → 1 sorry (PRs #1617, #1628, #1632) — nilpotent decomposition nearly complete
- **Proposition6_6_6** reduced from 3 → 2 sorries — reflection functor round-trip progress
- **Theorem5_26_1** helper `class_fun_vanishes_on_subgroup_of_orthogonal` proved (PR #1635)
- **artin_Q_span_of_induced_chars** partially proved (PR #1640, 2 sorries remain within)

| Tier | Count | % | Description |
|------|-------|---|-------------|
| Tier 1 — Achievable | 1 | 2% | Standard math, Mathlib APIs exist |
| Tier 2 — Hard but tractable | 7 | 14% | Non-trivial proofs, novel approaches needed |
| Tier 3 — Blocked on infrastructure | ~26 | 51% | Missing Mathlib or project infrastructure |
| Tier 4 — Deep blockers | ~17 | 33% | SchurModule, Clifford theory, major gaps |

## Chapter Breakdown

| Chapter | Sorries | Files | Delta from Wave 29 |
|---------|---------|-------|---------------------|
| Ch2 | 1 | 1 | 0 |
| Ch5 | 35 | 10 | −1 sorry, −2 files (Lemma5_25_3 sorry-free) |
| Ch6 | 10 | 8 | −9 sorries (Dynkin: −6, Problem6_9_1: −1, Prop6_6_6: −1, other: −1) |
| Ch9 | 3 | 3 | 0 |
| Infra | 2 | 2 | 0 |

## Files That Became Sorry-Free Since Wave 29

- **Theorem_Dynkin_classification.lean** — Complete Dynkin diagram classification (A_n, B_n, C_n, D_n, E₆, E₇, E₈, F₄, G₂). PR #1634 proved the reciprocal inequality, eliminating the last sorry.
- **Lemma5_25_3.lean** — Elliptic norm-squared sum computation for GL₂(𝔽_q) character theory. PR #1631 proved `elliptic_sum_algebraic_core`.

## Tier 1 — Achievable (1 sorry)

### Theorem5_15_1 — 1 sorry
**File:** `Chapter5/Theorem5_15_1.lean`
**Nature:** `alternating_kostka_eq_zero_of_strict_dom` — alternating Kostka identity for strict dominance.
**Status:** Issue #1580 (unclaimed). FDRep bridge complete. Dependency: Vandermonde orthogonality (#1592).

## Tier 2 — Hard but Tractable (7 sorries)

### Theorem5_25_2 — 6 sorries
**File:** `Chapter5/Theorem5_25_2.lean`
**Nature:** Principal series character computation helper lemmas.

### Problem6_9_1 — 1 sorry
**File:** `Chapter6/Problem6_9_1.lean`
**Nature:** `decomp_of_ker_sum_ge_two` — Q₂-rep decomposability. Down from 2 → 1. All nilpotent decomposition sub-cases proved (PRs #1617, #1628, #1632). Remaining sorry is the final assembly.

## Tier 3 — Blocked on Infrastructure (~26 sorries)

### Blocker Cluster 1: SchurModule & Characters (Ch5, ~20 sorries)
**Files:** Theorem5_23_2 (9), Theorem5_22_1 (3), PolytabloidBasis (2), Theorem5_18_4 (4), Proposition5_21_1 (2)
**Missing:** Concrete SchurModule definition. Everything downstream blocked.

### Blocker Cluster 2: Theorem5_25_2 Principal Series (Ch5, 6 sorries)
**File:** Theorem5_25_2
**Status:** Parts 1, 2, 3a have complete proof terms. 6 helper lemma sorries remain.

### Blocker Cluster 3: Theorem5_26_1 Artin's Theorem (Ch5, 2 sorries)
**File:** Theorem5_26_1
**Status:** `class_fun_vanishes_on_subgroup_of_orthogonal` proved (PR #1635). `artin_Q_span_of_induced_chars` partially proved (PR #1640, 2 sorries remain). Two top-level sorries: inducedCharacter linkage (line 264) and ℚ-span dimension bound (line 361).

### Blocker Cluster 4: Gabriel's Theorem (Ch6, 7 sorries)
**Files:** Corollary6_8_3 (1), Corollary6_8_4 (1), Problem6_1_5_theorem (2), Proposition6_6_7 (1), Theorem6_5_2 (1), CoxeterInfrastructure (1)
**Progress:** CoxeterInfrastructure down from 2 → 1 sorry. Proposition6_6_6 down from 3 → 2. Dynkin classification now complete — unblocks downstream.

### Blocker Cluster 5: Finite-Dimensional Algebras (Ch9, 3 sorries)
**Files:** Theorem9_2_1 (1), MoritaStructural (1), Example9_4_4 (1)
**Status:** Unchanged since wave 28.

### Blocker Cluster 6: Reflection Functor (Ch6, 2 sorries)
**Files:** Proposition6_6_6 (2)
**Status:** Down from 3 → 2 sorries. Remaining: arrow cases in naturality proof.

## Tier 4 — Deep Blockers (~17 sorries)

### Mackey Machine (Ch5, 5 sorries)
**File:** Theorem5_27_1
**Missing:** Clifford theory infrastructure. No path without ~500 lines of new theory.

### GL₂(𝔽_q) Classification residual (Ch5, 6 sorries)
**File:** Theorem5_25_2 (helper lemmas)
**Missing:** Character computation helpers.

### Gabriel's Theorem Classification (Ch2, 1 sorry)
**File:** Theorem2_1_2
**Missing:** Full Gabriel's theorem depends on Ch6 Gabriel cluster.

### Morita/Basic Algebra Infrastructure (2 sorries)
**Files:** Infrastructure/BasicAlgebraExistence (1), Infrastructure/MoritaStructural (1)
**Missing:** Existence of basic Morita-equivalent algebra.

### Coxeter element infrastructure (1 sorry)
**File:** CoxeterInfrastructure.lean
**Status:** Down from 2 → 1 sorry. `admissibleOrdering_exists` remains.

### Proposition5_22_2 (1 sorry)
**File:** Chapter5/Proposition5_22_2.lean
**Status:** Blocked on SchurModule construction.

## Definition-Level Sorries (Regression Check)

The following definition-level sorries remain. These make downstream theorems vacuous:

1. **Theorem5_22_1.lean:38** — `SchurModule` is entirely sorry'd (`FDRep k ... := sorry`)
2. **Theorem5_22_1.lean:46** — `schurPolynomial` sorry'd (`MvPolynomial ... := sorry`)
3. **Theorem5_23_2.lean:62,65,68** — `AlgIrrepGL` instances (AddCommGroup, Module, Finite) sorry'd
4. **Theorem5_23_2.lean:76,79** — `AlgIrrepGLDual` instances sorry'd
5. **Proposition5_21_1.lean:334** — `kostkaNumber` sorry'd (`ℚ := sorry`)
6. **Problem6_1_5_theorem.lean:33** — `IsFiniteTypeQuiver` sorry'd (`Prop := sorry`)

These are the highest-priority blockers. Until SchurModule is constructed (~20 downstream sorries are vacuous).

## Per-File Sorry Detail

| File | Sorries | Nature |
|------|---------|--------|
| Theorem5_23_2 | 9 | SchurModule instances + character formulas |
| Theorem5_25_2 | 6 | Principal series character helpers |
| Theorem5_27_1 | 5 | Mackey machine (Clifford theory) |
| Theorem5_18_4 | 4 | Young symmetrizer character formula |
| Theorem5_22_1 | 3 | SchurModule + schurPolynomial defs + theorem |
| Theorem5_26_1 | 2 | Artin's theorem helpers |
| PolytabloidBasis | 2 | Linear independence + straightening |
| Proposition5_21_1 | 2 | kostkaNumber def + character expansion |
| Problem6_1_5_theorem | 2 | IsFiniteTypeQuiver def + iff theorem |
| Proposition6_6_6 | 2 | Reflection functor naturality cases |
| Theorem2_1_2 | 1 | Gabriel's theorem statement |
| Theorem5_15_1 | 1 | Alternating Kostka strict dominance |
| Proposition5_22_2 | 1 | Schur polynomial character formula |
| Problem6_9_1 | 1 | Q₂-rep decomposability |
| Corollary6_8_3 | 1 | Indecomposable → positive root |
| Corollary6_8_4 | 1 | Bijection: indec reps ↔ positive roots |
| CoxeterInfrastructure | 1 | Admissible ordering existence |
| Proposition6_6_7 | 1 | Reflection functor preserves indec |
| Theorem6_5_2 | 1 | Indecomposable decomposition uniqueness |
| Example9_4_4 | 1 | Homological dimension of polynomial ring |
| MoritaStructural (Ch9) | 1 | Morita equivalence construction |
| Theorem9_2_1 | 1 | Artin-Wedderburn block structure |
| BasicAlgebraExistence | 1 | Basic algebra existence |
| MoritaStructural (Infra) | 1 | Morita structural infrastructure |

## Strategic Recommendations

1. **Biggest single win:** Theorem5_15_1 (#1580). Only 1 sorry for entire Frobenius character formula. FDRep bridge now complete.

2. **Highest ROI recent progress:** Ch6 dropped 9 sorries in one wave. Dynkin classification complete — this unblocks Gabriel theorem chain further. CoxeterInfrastructure `admissibleOrdering_exists` is the next Ch6 bottleneck.

3. **Critical path:** SchurModule remains the mega-blocker. ~20 sorries (39%) transitively blocked. This is the project's critical path and the hardest remaining work.

4. **Strong momentum:** −10 sorries since wave 29 (−16% reduction). Two major files became sorry-free. 96.7% of items now sorry-free.

5. **Near-completion candidates:** Problem6_9_1 (1 sorry), CoxeterInfrastructure (1 sorry), Proposition6_6_6 (2 sorries) are all close to done.

## Trajectory

| Wave | Sorries | Files | Items sorry-free | Date |
|------|---------|-------|------------------|------|
| 28 | 66 | 27 | 560/583 (96.1%) | 2026-03-22 |
| 29 | 61 | 26 | 562/583 (96.4%) | 2026-03-23 |
| 30 | 51 | 24 | 564/583 (96.7%) | 2026-03-23 |
