# Sorry Landscape Analysis — Wave 31

Generated 2026-03-24 by summarize session (issue #1671).

## Summary

**52 sorries** across 24 files. Up from 51 / 24 in wave 30 (+1 sorry, 0 files). Chapters 3, 4, 7, 8 remain 100% sorry-free. 243 of 267 Lean files (91.0%) are sorry-free. 565 of 583 items (96.9%) sorry-free.

3 PRs merged since wave 30 (#1639, #1664, #1674). Key changes:
- **Theorem5_26_1** became sorry-free — Artin's theorem fully proved (PR #1648, merged before Wave 30 but miscounted in that audit)
- **PowerSumCauchyIdentity.lean** added (PR #1639) with 1 sorry — `cauchyRHS_coeff_diag` coefficient extraction
- **principalSeries_decomp** proved (PR #1674) — V(μ,μ) ≅ W_μ ⊕ det·χ_μ decomposition. Decomposed existing sorries into more specific sub-lemmas (net +2 in Theorem5_25_2)
- **indecomposable_bilinearForm_eq_two** proved (PR #1664) — B(d(V),d(V))=2 for indecomposable V

### Wave 30 Corrections

The Wave 30 audit listed Theorem5_26_1 as having 2 sorries and Theorem5_25_2 as having 6. At the Wave 30 commit, Theorem5_26_1 was already sorry-free (0) and Theorem5_25_2 had 8 actual sorries. The errors canceled, giving the correct total of 51. This wave uses a more precise counting methodology.

| Tier | Count | % | Description |
|------|-------|---|-------------|
| Tier 1 — Achievable | 2 | 4% | Standard math, clear path exists |
| Tier 2 — Hard but tractable | 9 | 17% | Non-trivial proofs, novel approaches needed |
| Tier 3 — Blocked on infrastructure | ~24 | 46% | Missing Mathlib or project infrastructure |
| Tier 4 — Deep blockers | ~17 | 33% | SchurModule, Clifford theory, major gaps |

## Chapter Breakdown

| Chapter | Sorries | Files | Delta from Wave 30 |
|---------|---------|-------|---------------------|
| Ch2 | 1 | 1 | 0 |
| Ch5 | 36 | 11 | +1 sorry, +1 file (PowerSumCauchyIdentity added; Theorem5_26_1 correction: was already 0) |
| Ch6 | 10 | 8 | 0 |
| Ch9 | 3 | 3 | 0 |
| Infra | 2 | 2 | 0 |

## Files That Became Sorry-Free Since Wave 30

- **Theorem5_26_1.lean** — Artin's theorem: character span equals element coverage. PR #1648 proved `artin_Q_span_of_induced_chars`, the final sorry. (Note: this was already sorry-free at the Wave 30 commit but miscounted in that audit.)

## Open PRs (In-Flight Work)

Three open PRs will change the sorry landscape when merged:

1. **PR #1673** (CI passing) — `principalSeries_simple_of_ne`: V(χ₁,χ₂) irreducible when χ₁ ≠ χ₂. Closes #1646.
2. **PR #1676** (CI failing) — `cauchyProd_coeff_perm`: makes `cauchyRHS_coeff_diag` sorry-free in PowerSumCauchyIdentity. Closes #1670.
3. **PR #1672** (CI failing) — Theorem9_2_1 progress: 1 → 2 sorries (decomposition into precise sub-goals). Closes #1669.

## Tier 1 — Achievable (2 sorries)

### Theorem5_15_1 — 1 sorry
**File:** `Chapter5/Theorem5_15_1.lean`
**Nature:** `alternating_kostka_eq_zero_of_strict_dom` — alternating Kostka identity for strict dominance.
**Status:** FDRep bridge complete. PowerSumCauchyIdentity infrastructure advancing (PR #1676 in-flight).

### PowerSumCauchyIdentity — 1 sorry
**File:** `Chapter5/PowerSumCauchyIdentity.lean`
**Nature:** `cauchyRHS_coeff_diag` — coefficient extraction from Cauchy product.
**Status:** PR #1676 claims to make this sorry-free (CI failing, needs fix).

## Tier 2 — Hard but Tractable (9 sorries)

### Theorem5_25_2 — 8 sorries
**File:** `Chapter5/Theorem5_25_2.lean`
**Nature:** Principal series character computation + decomposition helpers. PR #1674 proved `principalSeries_decomp` but introduced sub-lemma sorries for `complementW_simple`, `complementW_character`, etc.
**Progress:** Core decomposition V(μ,μ) ≅ W_μ ⊕ det·χ_μ is now proved. PR #1673 advancing `principalSeries_simple_of_ne`.

### Problem6_9_1 — 1 sorry
**File:** `Chapter6/Problem6_9_1.lean`
**Nature:** `decomp_of_ker_sum_ge_two` — Q₂-rep decomposability via transfer from AB-invariant to Q₂-invariant decomposition. Issue #1637 unclaimed.

## Tier 3 — Blocked on Infrastructure (~24 sorries)

### Blocker Cluster 1: SchurModule & Characters (Ch5, ~20 sorries)
**Files:** Theorem5_23_2 (9), Theorem5_22_1 (3), PolytabloidBasis (2), Theorem5_18_4 (4), Proposition5_21_1 (2)
**Missing:** Concrete SchurModule definition. Everything downstream blocked. This is the project's critical path.

### Blocker Cluster 2: Gabriel's Theorem Chain (Ch6, 7 sorries)
**Files:** Corollary6_8_3 (1), Corollary6_8_4 (1), Problem6_1_5_theorem (2), Proposition6_6_7 (1), Theorem6_5_2 (1), CoxeterInfrastructure (1)
**Status:** `indecomposable_bilinearForm_eq_two` proved (PR #1667). Chain still blocked on `indecomposable_reduces_to_simpleRoot` (type-changing iterated reflection functor).

### Blocker Cluster 3: Reflection Functor (Ch6, 2 sorries)
**Files:** Proposition6_6_6 (2)
**Status:** Unchanged. Remaining: arrow cases in naturality proof.

### Blocker Cluster 4: Finite-Dimensional Algebras (Ch9, 3 sorries)
**Files:** Theorem9_2_1 (1), MoritaStructural (1), Example9_4_4 (1)
**Status:** PR #1672 in-flight for Theorem9_2_1 (rank property proved, surjectivity + dimension matching remain).

## Tier 4 — Deep Blockers (~17 sorries)

### Mackey Machine (Ch5, 5 sorries)
**File:** Theorem5_27_1
**Missing:** Clifford theory infrastructure. No path without ~500 lines of new theory.

### GL₂(𝔽_q) Classification residual (Ch5, 8 sorries)
**File:** Theorem5_25_2 (helper lemmas)
**Status:** Active work — principalSeries_decomp proved, sub-lemma infrastructure advancing. PR #1673 in-flight for `principalSeries_simple_of_ne`.

### Gabriel's Theorem Classification (Ch2, 1 sorry)
**File:** Theorem2_1_2
**Missing:** Full Gabriel's theorem depends on Ch6 Gabriel cluster.

### Morita/Basic Algebra Infrastructure (2 sorries)
**Files:** Infrastructure/BasicAlgebraExistence (1), Infrastructure/MoritaStructural (1)
**Missing:** Existence of basic Morita-equivalent algebra.

### Coxeter element infrastructure (1 sorry)
**File:** CoxeterInfrastructure.lean
**Status:** `admissibleOrdering_exists` remains.

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

No new definition-level sorries since Wave 30. Until SchurModule is constructed, ~20 downstream sorries (38%) are vacuous.

## Per-File Sorry Detail

| File | Sorries | Nature |
|------|---------|--------|
| Theorem5_23_2 | 9 | SchurModule instances + character formulas |
| Theorem5_25_2 | 8 | Principal series decomposition + character helpers |
| Theorem5_27_1 | 5 | Mackey machine (Clifford theory) |
| Theorem5_18_4 | 4 | Young symmetrizer character formula |
| Theorem5_22_1 | 3 | SchurModule + schurPolynomial defs + theorem |
| PolytabloidBasis | 2 | Linear independence + straightening |
| Proposition5_21_1 | 2 | kostkaNumber def + character expansion |
| Problem6_1_5_theorem | 2 | IsFiniteTypeQuiver def + iff theorem |
| Proposition6_6_6 | 2 | Reflection functor naturality cases |
| Theorem2_1_2 | 1 | Gabriel's theorem statement |
| Theorem5_15_1 | 1 | Alternating Kostka strict dominance |
| PowerSumCauchyIdentity | 1 | Cauchy product coefficient extraction |
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

1. **Highest-ROI in-flight work:** PR #1673 (principalSeries_simple_of_ne, CI passing) — merge this first to reduce Theorem5_25_2 sorry count. PR #1676 (cauchyProd_coeff_perm) needs CI fix but would make PowerSumCauchyIdentity sorry-free.

2. **Best unclaimed work:** Problem6_9_1 (#1637, difficulty 5) — Q₂-transfer is the last sorry. CoxeterInfrastructure `admissibleOrdering_exists` would unblock the Gabriel chain.

3. **Critical path unchanged:** SchurModule remains the mega-blocker. ~20 sorries (38%) transitively blocked. This is the project's critical path and the hardest remaining work.

4. **Velocity observation:** Wave 30 → 31 saw only +1 net sorry (from decomposition). The sorry count is stabilizing as remaining sorries are increasingly difficult. Active PR pipeline (3 open PRs) suggests continued progress.

5. **Near-completion candidates:** PowerSumCauchyIdentity (1 sorry, PR in-flight), Problem6_9_1 (1 sorry, unclaimed), CoxeterInfrastructure (1 sorry).

## Trajectory

| Wave | Sorries | Files | Items sorry-free | Date |
|------|---------|-------|------------------|------|
| 28 | 66 | 27 | 560/583 (96.1%) | 2026-03-22 |
| 29 | 61 | 26 | 562/583 (96.4%) | 2026-03-23 |
| 30 | 51 | 24 | 564/583 (96.7%) | 2026-03-23 |
| 31 | 52 | 24 | 565/583 (96.9%) | 2026-03-24 |
