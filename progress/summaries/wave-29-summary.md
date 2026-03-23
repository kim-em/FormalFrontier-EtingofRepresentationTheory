# Wave 29 Summary

**Date:** 2026-03-23
**Issue:** #1608
**PRs merged since wave 28:** 18

## Key Metrics

| Metric | Wave 28 | Wave 29 | Delta |
|--------|---------|---------|-------|
| Total sorries | 66 | 61 | −5 |
| Files with sorry | 27 | 26 | −1 |
| Sorry-free files | 238/265 (89.8%) | 240/266 (90.2%) | +2 files sorry-free |
| Sorry-free items | 560/583 (96.1%) | 562/583 (96.4%) | +2 items |

## Per-Chapter Breakdown

| Chapter | Sorries | Files | Delta |
|---------|---------|-------|-------|
| Ch2 | 1 | 1 | −1 sorry |
| Ch3 | 0 | 0 | — |
| Ch4 | 0 | 0 | — |
| Ch5 | 36 | 12 | −3 sorries, −1 file |
| Ch6 | 19 | 8 | −1 sorry |
| Ch7 | 0 | 0 | — |
| Ch8 | 0 | 0 | — |
| Ch9 | 3 | 3 | 0 |
| Infra | 2 | 2 | 0 |

## Key Wins

### Files Became Sorry-Free
- **Theorem2_1_1.lean** — sl(2,ℂ) complete reducibility (both parts i and ii). PR #1611 completed the final case via weight-space/complement arguments.
- **GL2NormalizerInfra.lean** — GL₂(𝔽_q) normalizer theory. PR #1612 proved normalizer_card (|N_{GL₂}(K)| = 2|K|) via normalizer decomposition N = K ∪ σK.

### Sorry Reductions
- **Theorem5_26_1** 3→2 sorries: frobenius_char_reciprocity proved (PR #1612)
- **Proposition6_6_6** 5→3 sorries: hψ_inj + hdim type-class workaround (PR #1598)
- **Problem6_9_1**: 2/3 nilpotent_nontrivial_decomp cases proved (PR #1606)

### Infrastructure Advances
- **FDRep bridge completed**: spechtModuleFDRep_simple proved (PR #1601), closing #1591
- **CoxeterInfrastructure** created (PR #1605): foundation for Gabriel theorem chain
- **exists_sink_of_dynkin_orientation** proved via counting argument (PR #1607)
- **Proposition6_6_7** sink-case mapLinear lemmas proved (PR #1600)

## All Merged PRs (18)

| PR | Title |
|----|-------|
| #1583 | Reduce Theorem_2_1_1_ii sorry count from 2 to 1 |
| #1584 | Meditate: review blockers, proof patterns, skill updates |
| #1585 | Prove frobeniusMatrix_not_in_elliptic |
| #1586 | Reduce alternating Kostka identity to norm-squared sub-lemma |
| #1587 | Decompose equivAt_eq_sink for Proposition6_6_6 |
| #1588 | Maintenance: merge ready PRs, close #1196 |
| #1590 | Coxeter work (1381) |
| #1596 | Review: wave 28 sorry audit and stale claim check |
| #1597 | Partial FDRep bridge for Specht module (3/4 deliverables) |
| #1598 | Proposition6_6_6 type-class workaround (hψ_inj + hdim) |
| #1599 | Reduce GL2NormalizerInfra sorries from 4 to 1 |
| #1600 | Proposition6_6_7 sink-case mapLinear lemmas |
| #1601 | Prove spechtModuleFDRep_simple (4th FDRep bridge deliverable) |
| #1604 | Coxeter work (1381) |
| #1605 | Coxeter element infrastructure for Gabriel theorem chain |
| #1606 | Prove 2/3 cases of nilpotent_nontrivial_decomp |
| #1607 | Prove exists_sink_of_dynkin_orientation counting argument |
| #1611 | Complete proof of Theorem 2.1.1(ii) — sl(2,ℂ) complete reducibility |
| #1612 | Prove frobenius_char_reciprocity and normalizer_card |

## Remaining Blockers

### Critical Path: SchurModule (~20 sorries, 33% of total)
The concrete SchurModule definition (Theorem5_22_1.lean) remains the single largest blocker. All of Theorem5_23_2 (9 sorries), Theorem5_18_4 (4 sorries), PolytabloidBasis (2 sorries), and parts of Proposition5_21_1 are transitively blocked.

### Gabriel Theorem Chain (~8 sorries)
CoxeterInfrastructure now exists but needs admissibleOrdering_exists and coxeterElement_power_sink proved. Proposition6_6_6 still has 3 sorries from Decidable.casesOn opacity.

### Mackey Machine (5 sorries)
Theorem5_27_1 requires Clifford theory infrastructure (~500 lines). No progress this wave.

### Definition-Level Sorries (6 definitions)
SchurModule, schurPolynomial, AlgIrrepGL instances, kostkaNumber, IsFiniteTypeQuiver remain sorry'd. These make downstream theorems vacuous.

## Recommendations for Next Wave

1. **Vandermonde orthogonality (#1592)**: Dependency for Theorem5_15_1 (#1580). FDRep bridge is now complete, so this is unblocked.
2. **CoxeterInfrastructure proofs**: admissibleOrdering_exists and coxeterElement_power_sink would unblock the Gabriel theorem chain.
3. **Proposition6_6_6 remaining 3 sorries**: Investigate Decidable.casesOn opacity workaround.
4. **SchurModule construction**: Highest long-term ROI but difficulty 5+. Consider decomposition into sub-tasks.
