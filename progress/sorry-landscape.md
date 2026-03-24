# Sorry Landscape Analysis — Wave 33

Generated 2026-03-24 by summarize session (issue #1695).

## Summary

**43 sorries** across 22 files. Down from 45 / 23 in wave 32 (−2 sorries, −1 file). Chapters 3, 4, 7, 8 remain 100% sorry-free. 245 of 267 Lean files (91.8%) are sorry-free. 566 of 583 items (97.1%) sorry-free.

3 PRs merged since wave 32 (#1690, #1692, #1693). Key changes:
- **Theorem9_2_1.lean** became sorry-free — `hσ_surj` (surjectivity of block assignment σ) proved (PR #1692)
- **Theorem5_25_2** went from 2 → 1 sorry (−1): `complementW_iso_implies_eq` + `Theorem5_25_2_part3b` proved (PR #1690). Only `principalSeries_iso_swap` remains.
- **Problem6_9_1** refactored (PR #1693) — no sorry change

| Tier | Count | % | Description |
|------|-------|---|-------------|
| Tier 1 — Achievable | 1 | 2% | Standard math, clear path exists |
| Tier 2 — Hard but tractable | 2 | 5% | Non-trivial proofs, self-contained |
| Tier 3 — Blocked on SchurModule | ~21 | 49% | Missing SchurModule definition |
| Tier 4 — Deep blockers | ~19 | 44% | Clifford theory, Gabriel chain, Morita |

## Chapter Breakdown

| Chapter | Sorries | Files | Delta from Wave 32 |
|---------|---------|-------|---------------------|
| Ch2 | 1 | 1 | 0 |
| Ch5 | 28 | 9 | −1 sorry (Theorem5_25_2 2→1) |
| Ch6 | 10 | 8 | 0 |
| Ch9 | 2 | 2 | −1 sorry, −1 file (Theorem9_2_1 sorry-free) |
| Infra | 2 | 2 | 0 |

## Files That Became Sorry-Free Since Wave 32

- **Theorem9_2_1.lean** — Artin-Wedderburn block structure (classification of indecomposable projective modules). PR #1692 proved `hσ_surj`, the last sorry.

## Open PRs (In-Flight Work)

No open PRs.

## Tier 1 — Achievable (1 sorry)

### Theorem5_15_1 — 1 sorry
**File:** `Chapter5/Theorem5_15_1.lean`
**Nature:** `alternatingKostka_norm_sq_eq_one` — proves ∑_ν L(λ,ν)² = 1. Key step in the Frobenius character formula.
**Status:** PowerSumCauchyIdentity is sorry-free, providing the `cauchyRHS_coeff_diag` infrastructure. Issue #1688 created for this work.

## Tier 2 — Hard but Tractable (2 sorries)

### Theorem5_25_2 — 1 sorry
**File:** `Chapter5/Theorem5_25_2.lean`
**Nature:** `principalSeries_iso_swap` (line 2493) — V(χ₁,χ₂) ≅ V(χ₂,χ₁), symmetry of principal series under character permutation.
**Progress:** Major improvement over recent waves: 8 → 2 → 1 sorry. PR #1690 proved `complementW_iso_implies_eq` and `Theorem5_25_2_part3b`. Only character symmetry remains. Issue #1694 created.

### Problem6_9_1 — 1 sorry
**File:** `Chapter6/Problem6_9_1.lean`
**Nature:** `decomp_of_ker_sum_ge_two` — Q₂-rep decomposability via transfer from AB-invariant to Q₂-invariant decomposition. PR #1693 refactored but didn't prove. Issue #1637 unclaimed.

## Tier 3 — Blocked on SchurModule (~21 sorries)

### SchurModule & Characters (Ch5, 21 sorries)
**Files:** Theorem5_23_2 (9), Theorem5_18_4 (4), Theorem5_22_1 (3), PolytabloidBasis (2), Proposition5_21_1 (2), Proposition5_22_2 (1)
**Missing:** Concrete SchurModule definition (Theorem5_22_1:38 is `sorry`). Everything downstream is blocked. This is the project's critical path — 49% of all remaining sorries.

## Tier 4 — Deep Blockers (~19 sorries)

### Mackey Machine (Ch5, 5 sorries)
**File:** Theorem5_27_1
**Missing:** Clifford theory infrastructure. No path without ~500 lines of new theory.

### Gabriel's Theorem Chain (Ch6, 9 sorries)
**Files:** Corollary6_8_3 (1), Corollary6_8_4 (1), Problem6_1_5_theorem (2), Proposition6_6_6 (2), Proposition6_6_7 (1), Theorem6_5_2 (1), CoxeterInfrastructure (1)
**Status:** Unchanged. Chain blocked on `indecomposable_reduces_to_simpleRoot` (type-changing iterated reflection functor) and `admissibleOrdering_exists`.

### Gabriel's Theorem Classification (Ch2, 1 sorry)
**File:** Theorem2_1_2
**Missing:** Full Gabriel's theorem depends on Ch6 Gabriel cluster.

### Morita/Basic Algebra Infrastructure (3 sorries)
**Files:** MoritaStructural Ch9 (1), BasicAlgebraExistence (1), MoritaStructural Infra (1)
**Missing:** Existence of basic Morita-equivalent algebra. Progenerator-to-algebra construction.

### Homological Dimension (Ch9, 1 sorry)
**File:** Example9_4_4
**Status:** `homologicalDimension (MvPolynomial (Fin n) k) = n` — standalone result.

## Definition-Level Sorries (Regression Check)

The following definition-level sorries remain. These make downstream theorems vacuous:

1. **Theorem5_22_1.lean:38** — `SchurModule` is entirely sorry'd (`FDRep k ... := sorry`)
2. **Theorem5_22_1.lean:46** — `schurPolynomial` sorry'd (`MvPolynomial ... := sorry`)
3. **Theorem5_23_2.lean:59** — `AlgIrrepGL` sorry'd (type definition)
4. **Theorem5_23_2.lean:62,65,68** — `AlgIrrepGL` instances (AddCommGroup, Module, Finite) sorry'd
5. **Theorem5_23_2.lean:73** — `AlgIrrepGLDual` sorry'd (type definition)
6. **Theorem5_23_2.lean:76,79** — `AlgIrrepGLDual` instances sorry'd
7. **Proposition5_21_1.lean:334** — `kostkaNumber` sorry'd (`ℚ := sorry`)
8. **Problem6_1_5_theorem.lean:33** — `IsFiniteTypeQuiver` sorry'd (`Prop := sorry`)

No new definition-level sorries since Wave 30. Until SchurModule is constructed, ~21 downstream sorries (49%) are vacuous.

## Per-File Sorry Detail

| File | Sorries | Nature | Delta |
|------|---------|--------|-------|
| Theorem5_23_2 | 9 | SchurModule instances + character formulas | 0 |
| Theorem5_27_1 | 5 | Mackey machine (Clifford theory) | 0 |
| Theorem5_18_4 | 4 | Young symmetrizer character formula | 0 |
| Theorem5_22_1 | 3 | SchurModule + schurPolynomial defs + theorem | 0 |
| PolytabloidBasis | 2 | Linear independence + straightening | 0 |
| Proposition6_6_6 | 2 | Reflection functor naturality cases | 0 |
| Proposition5_21_1 | 2 | kostkaNumber def + character expansion | 0 |
| Problem6_1_5_theorem | 2 | IsFiniteTypeQuiver def + iff theorem | 0 |
| Theorem5_25_2 | 1 | principalSeries_iso_swap (character symmetry) | **−1** |
| Theorem5_15_1 | 1 | Alternating Kostka norm squared | 0 |
| Proposition5_22_2 | 1 | Schur polynomial character formula | 0 |
| Corollary6_8_3 | 1 | Indecomposable → positive root | 0 |
| Corollary6_8_4 | 1 | Bijection: indec reps ↔ positive roots | 0 |
| CoxeterInfrastructure | 1 | Admissible ordering existence | 0 |
| Proposition6_6_7 | 1 | Reflection functor preserves indec | 0 |
| Theorem6_5_2 | 1 | Indecomposable decomposition uniqueness | 0 |
| Problem6_9_1 | 1 | Q₂-rep decomposability | 0 |
| BasicAlgebraExistence | 1 | Basic algebra existence | 0 |
| MoritaStructural (Ch9) | 1 | Morita equivalence construction | 0 |
| MoritaStructural (Infra) | 1 | Morita structural infrastructure | 0 |
| Example9_4_4 | 1 | Homological dimension of polynomial ring | 0 |
| Theorem2_1_2 | 1 | Gabriel's theorem statement | 0 |

**Removed since Wave 32:** Theorem9_2_1 (was 1 sorry, now 0)

## Strategic Recommendations

1. **Highest-ROI unclaimed work:** Issue #1688 (`alternatingKostka_norm_sq_eq_one` in Theorem5_15_1) — PowerSumCauchyIdentity is sorry-free, so the infrastructure is ready. This would close the Frobenius character formula.

2. **Active work:** Issue #1694 (`principalSeries_iso_swap` in Theorem5_25_2) — claimed, in progress. Would reduce Theorem5_25_2 to 0 sorries, making the entire GL₂(𝔽_q) principal series classification complete.

3. **Next-best target:** Problem6_9_1 `decomp_of_ker_sum_ge_two` (issue #1637) — Q₂-rep decomposability via AB-invariant transfer. PR #1693 set up helper infrastructure.

4. **Critical path unchanged:** SchurModule remains the mega-blocker. ~21 sorries (49%) transitively blocked. This is the project's critical path and the hardest remaining work.

5. **Velocity observation:** Wave 32 → 33 saw −2 net sorries from only 3 PRs. The GL₂(𝔽_q) cluster is nearing completion (1 sorry from 8 three waves ago). Chapter 9 saw its first file go sorry-free.

6. **Stale comment:** Theorem5_25_2.lean:1192 contains "For now, sorry the augmentation computation" but the augmentation is actually proved below. Cosmetic only.

## Trajectory

| Wave | Sorries | Files | Items sorry-free | Date |
|------|---------|-------|------------------|------|
| 28 | 66 | 27 | 560/583 (96.1%) | 2026-03-22 |
| 29 | 61 | 26 | 562/583 (96.4%) | 2026-03-23 |
| 30 | 51 | 24 | 564/583 (96.7%) | 2026-03-23 |
| 31 | 52 | 24 | 565/583 (96.9%) | 2026-03-23 |
| 32 | 45 | 23 | 565/583 (96.9%) | 2026-03-24 |
| 33 | 43 | 22 | 566/583 (97.1%) | 2026-03-24 |
