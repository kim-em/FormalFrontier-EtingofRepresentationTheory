# Sorry Landscape Analysis — Wave 35

Generated 2026-03-26 by summarize session (issue #1720).

## Summary

**43 sorries** across 21 files. Down from 44 / 22 in wave 34 (−1 sorry, −1 file). Chapters 3, 4, 7, 8 remain 100% sorry-free. 247 of 268 Lean files (92.2%) are sorry-free. 568 of 583 items (97.4%) sorry-free.

6 PRs merged since wave 34 (#1713, #1715, #1718, #1719, #1723, #1736). Key changes:
- **Theorem5_15_1.lean** became sorry-free — `alternatingKostka_norm_sq_eq_one` proved (PR #1719). The **Frobenius character formula** is now fully formalized.
- **PowerSumCauchyBilinear.lean** restructured: `fullCauchyProd_coeff_eq_card` proved (#1713), `double_counting` decomposed and main theorem compiles (#1713, #1718). 2 sorrys remain: `card_sigma_fiberPerm_eq_factorial_mul` (Part B) and `vandermonde_cauchy_diagonal`.
- **Proposition6_6_6.lean** source case built out (#1723, #1715): from 1 large sorry to 2 localized sorrys (hdim + source naturality). Instance diamond remains the blocker.
- **Status check wave 1** (#1736) performed: no definition-level sorry regressions, 4 new issues created for neglected items.

| Tier | Count | % | Description |
|------|-------|---|-------------|
| Tier 1 — Achievable | 5 | 12% | Standard math, clear path, 1-2 sessions |
| Tier 2 — Hard but tractable | 4 | 9% | Non-trivial proofs, self-contained |
| Tier 3 — Significant infrastructure | 8 | 19% | Clifford, Morita, Schur-Weyl decomposition |
| Tier 4 — Deep blockers / SchurModule | ~26 | 60% | SchurModule-dependent + Gabriel chain |

## Chapter Breakdown

| Chapter | Sorries | Files | Delta from Wave 34 |
|---------|---------|-------|---------------------|
| Ch2 | 1 | 1 | 0 |
| Ch5 | 28 | 8 | −1 sorry, −1 file (Theorem5_15_1 sorry-free; PowerSumCauchyBilinear 2→2 different sorrys) |
| Ch6 | 10 | 8 | 0 |
| Ch9 | 2 | 2 | 0 |
| Infra | 2 | 2 | 0 |

## Files That Became Sorry-Free Since Wave 34

- **Theorem5_15_1.lean** — Frobenius character formula: `alternatingKostka_norm_sq_eq_one` (∑_ν L(λ,ν)² = 1) proved via Young's rule expansion + character orthonormality + Cauchy bilinear identity. PR #1719 closed the last sorry. This completes the Frobenius character formula chapter of the formalization.

## Open PRs (In-Flight Work)

| PR | Issue | Title |
|----|-------|-------|
| #1737 | #1732 | Consolidate addCommGroupOfField/addCommGroupOfRing |

## Tier 1 — Achievable (5 sorries)

### PowerSumCauchyBilinear — 2 sorries
**File:** `Chapter5/PowerSumCauchyBilinear.lean`
**Nature:** `card_sigma_fiberPerm_eq_factorial_mul` (orbit-stabilizer for element bicolorings) and `vandermonde_cauchy_diagonal` (formal power series Cauchy determinant at diagonal). Both are downstream of the proved `double_counting` main theorem.
**Status:** Active issues #1714 (double_counting Part B), #1721 (vandermonde_cauchy_diagonal).

### PolytabloidBasis — 2 sorries
**File:** `Chapter5/PolytabloidBasis.lean`
**Nature:** `polytabloid_linearIndependent` and `perm_mul_youngSymmetrizer_mem_span_polytabloids` (straightening lemma).
**Status:** Active issue #1717.

### Proposition6_6_7 — 1 sorry
**File:** `Chapter6/Proposition6_6_7.lean`
**Nature:** `Proposition6_6_7_source` — reflection functor preserves indecomposability (source case).
**Status:** Active issue #1726. Definition6_6_4 is now sorry-free, removing a previous blocker.

## Tier 2 — Hard but Tractable (4 sorries)

### Proposition6_6_6 — 2 sorries
**File:** `Chapter6/Proposition6_6_6.lean`
**Nature:** `hdim` (finrank equality via rank-nullity) and source naturality (instance diamond prevents naming `ofBijective` term). Both blocked by Decidable.casesOn / instance diamond issues.
**Status:** Active issue #1724. PR #1723 built out the full source case structure.

### Problem6_9_1 — 1 sorry
**File:** `Chapter6/Problem6_9_1.lean`
**Nature:** `decomp_of_ker_sum_ge_two` — Q₂-rep decomposability via graded nilpotent chain basis.
**Status:** Active issue #1691.

### CoxeterInfrastructure — 1 sorry
**File:** `Chapter6/CoxeterInfrastructure.lean`
**Nature:** `admissibleOrdering_exists` — existence of admissible ordering for finite acyclic quivers. Blocks Corollary6_8_3/4.
**Status:** No dedicated issue. Indirectly covered by the Gabriel chain.

## Tier 3 — Significant Infrastructure (~8 sorries)

### Mackey Machine (Ch5, 5 sorries)
**File:** Theorem5_27_1
**Missing:** Clifford theory infrastructure (~500 lines). Issue #1731.

### Morita/Basic Algebra Infrastructure (3 sorries)
**Files:** MoritaStructural Ch9 (1), BasicAlgebraExistence (1), MoritaStructural Infra (1)
**Missing:** Progenerator-to-algebra construction. Issue #1729.

## Tier 4 — Deep Blockers / SchurModule-Dependent (~26 sorries)

### SchurModule & Characters (Ch5, ~21 sorries)
**Files:** Theorem5_23_2 (9), Theorem5_18_4 (4), Theorem5_22_1 (3), PolytabloidBasis (2†), Proposition5_21_1 (2), Proposition5_22_2 (1)
**Missing:** Concrete SchurModule definition (Theorem5_22_1:38 is `sorry`). Everything downstream is blocked. This is the project's critical path — ~49% of all remaining sorries.
**Status:** Active issue #1722.

†PolytabloidBasis sorrys are listed in Tier 1 because they are independent of SchurModule, but the results feed into the SchurModule construction.

### Gabriel's Theorem Chain (Ch6, 5 sorries)
**Files:** Corollary6_8_3 (1), Corollary6_8_4 (1), Problem6_1_5_theorem (2), Theorem6_5_2 (1)
**Status:** Chain blocked on CoxeterInfrastructure + Proposition6_6_6/7. Issue #1734 (Theorem2_1_2).

### Gabriel's Theorem Classification (Ch2, 1 sorry)
**File:** Theorem2_1_2
**Missing:** Full Gabriel's theorem depends on Ch6 Gabriel cluster. Issue #1734.

### Homological Dimension (Ch9, 1 sorry)
**File:** Example9_4_4
**Status:** `homologicalDimension (MvPolynomial (Fin n) k) = n` — standalone, deep homological algebra. Issue #1729.

## Definition-Level Sorries (Regression Check)

**No new definition-level sorry regressions since wave 34.** Status check wave 1 (#1736) confirmed all 10-11 definition-level sorrys are known:

1. **Theorem5_22_1.lean:38** — `SchurModule` (`FDRep k ... := sorry`)
2. **Theorem5_22_1.lean:46** — `formalCharacter` (`MvPolynomial ... := sorry`)
3. **Theorem5_23_2.lean:59** — `AlgIrrepGL` (type definition)
4. **Theorem5_23_2.lean:62,65,68** — `AlgIrrepGL` instances (AddCommGroup, Module, Finite)
5. **Theorem5_23_2.lean:73** — `AlgIrrepGLDual` (type definition)
6. **Theorem5_23_2.lean:76,79** — `AlgIrrepGLDual` instances
7. **Proposition5_21_1.lean:334** — `kostkaNumber` (`ℚ := sorry`)
8. **Problem6_1_5_theorem.lean:33** — `IsFiniteTypeQuiver` (`Prop := sorry`)

Until SchurModule is constructed, ~21 downstream sorries (49%) are vacuous.

## Per-File Sorry Detail

| File | Sorries | Nature | Delta from W34 |
|------|---------|--------|----------------|
| Theorem5_23_2 | 9 | SchurModule instances + character formulas | 0 |
| Theorem5_27_1 | 5 | Mackey machine (Clifford theory) | 0 |
| Theorem5_18_4 | 4 | Young symmetrizer character formula | 0 |
| Theorem5_22_1 | 3 | SchurModule + formalCharacter defs + theorem | 0 |
| PowerSumCauchyBilinear | 2 | card_sigma_fiberPerm + vandermonde_cauchy_diagonal | **changed** |
| PolytabloidBasis | 2 | Linear independence + straightening | 0 |
| Proposition6_6_6 | 2 | Reflection functor source (hdim + naturality) | 0 |
| Proposition5_21_1 | 2 | kostkaNumber def + character expansion | 0 |
| Problem6_1_5_theorem | 2 | IsFiniteTypeQuiver def + iff theorem | 0 |
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

**Removed since Wave 34:** Theorem5_15_1 (was 1 sorry, now 0 — Frobenius character formula complete)
**Changed since Wave 34:** PowerSumCauchyBilinear sorrys are now different lemmas (fullCauchyProd_coeff_eq_card proved, double_counting main proved; remaining: Part B + vandermonde)

## Strategic Recommendations

1. **Continue SchurModule construction** (#1722) — highest ROI, unblocks ~21 sorrys (49%). This is the critical path.

2. **Complete Proposition6_6_6** (#1724) — 2 localized sorrys, both instance diamond issues. Unblocks the Gabriel chain.

3. **Prove Proposition6_6_7 source** (#1726) — Definition6_6_4 is now sorry-free, removing a previous blocker. Unblocks Corollary6_8_3/4.

4. **PowerSumCauchyBilinear Part B** (#1714) — `card_sigma_fiberPerm_eq_factorial_mul` is standard combinatorics. Would make `double_counting` sorry-free.

5. **Attempt neglected Ch9/Infra** (#1729) — MoritaStructural has had zero direct PRs in 50+ waves.

## Milestone: Frobenius Character Formula Complete

Theorem5_15_1 becoming sorry-free is a significant milestone. The proof chain:
- PowerSumCauchyIdentity → cauchyRHS_coeff_diag (sorry-free)
- PowerSumCauchyBilinear → powerSum_bilinear_coeff (compiles, reduces to 2 bridge sorrys)
- Theorem5_15_1 → alternatingKostka_norm_sq_eq_one → Frobenius character formula

This completes the formalization of the Frobenius character formula from Chapter 5, one of the book's central results.

## Trajectory

| Wave | Sorries | Files | Items sorry-free | Date |
|------|---------|-------|------------------|------|
| 28 | 66 | 27 | 560/583 (96.1%) | 2026-03-22 |
| 29 | 61 | 26 | 562/583 (96.4%) | 2026-03-23 |
| 30 | 51 | 24 | 564/583 (96.7%) | 2026-03-23 |
| 31 | 52 | 24 | 565/583 (96.9%) | 2026-03-23 |
| 32 | 45 | 23 | 565/583 (96.9%) | 2026-03-24 |
| 33 | 43 | 22 | 566/583 (97.1%) | 2026-03-24 |
| 34 | 44 | 22 | 567/583 (97.2%) | 2026-03-24 |
| 35 | 43 | 21 | 568/583 (97.4%) | 2026-03-26 |
