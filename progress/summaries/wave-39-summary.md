# Wave 39 Summary

**Date:** 2026-03-28
**Issue:** #1890
**PRs merged since wave 38:** 35+

## Key Metrics

| Metric | Wave 38 | Wave 39 | Delta |
|--------|---------|---------|-------|
| Total sorries | 27 | 29 | +2 (decomposition) |
| Files with sorry | 19 | 17 | −2 |
| Sorry-free files | 252/271 (93.0%) | 255/272 (93.8%) | +3 files sorry-free |
| Sorry-free items | 570/583 (97.8%) | 571/583 (97.9%) | +1 item |

## Per-Chapter Breakdown

| Chapter | Sorries | Files | Delta |
|---------|---------|-------|-------|
| Ch2 | 1 | 1 | 0 |
| Ch3 | 0 | 0 | — |
| Ch4 | 0 | 0 | — |
| Ch5 | 16 | 6 | +4 sorries (decomposition), −1 file |
| Ch6 | 7 | 7 | −2 sorries |
| Ch7 | 0 | 0 | — |
| Ch8 | 0 | 0 | — |
| Ch9 | 3 | 3 | +1 sorry (decomposition), +1 file |
| Infra | 2 | 1 | −1 sorry, −1 file |

## Files That Became Sorry-Free

1. **Theorem5_18_4.lean** — Partition-indexed Schur-Weyl decomposition proved (#1830).
2. **PowerSumCauchyBilinear.lean** — Orbit-stabilizer computation proved.
3. **Infrastructure/MoritaStructural.lean** — Removed as dead code (#1835).

## Key Wins

### Hilbert Syzygy Theorem (7 PRs)
- Shapiro lemma for Ext fully proved (no sorry)
- Ext^n(k,k) ≠ 0 for polynomial residue field proved
- Polynomial extension SES constructed
- extendScalars preserves projective dimension proved
- Major infrastructure for both upper and lower bounds

### Morita Theory (9 PRs)
- cornerFunctor_full proved (A-linearity of lift map)
- exists_basic_morita_equivalent proved
- MoritaStructural restructured into 3 independent components
- pi_matrix_single_generates_ideal proved (fullness of idempotent)
- End_A(Ae) ≃ₐ[k] (CornerRing e)^op infrastructure

### Mackey Machine
- Character formula (part iv) proved via sum reindexing + fiber decomposition
- inducedRepV construction (map_one', map_mul') proved

### Schur-Weyl / Character Theory
- Theorem5_18_4 fully proved (partition decomposition)
- Theorem5_23_2 part (i) proved (complete reducibility)
- Theorem5_22_1 decomposed into 3 independent trace formula sub-lemmas
- Young symmetrizer generalized to arbitrary CharZero fields
- Schur polynomial shift identity proved
- Vandermonde determinant infrastructure

### Gabriel Chain
- Proposition6_6_6_source reduced from 2→1 sorry (hdim proved)
- Proposition6_6_7 fully proved (wave 38, but landed in this period)
- indecomposable_reduces_to_simpleRoot proved

## Remaining Blockers

### Cluster A: Polytabloid Linear Independence (6 sorries)
Right-multiplication dominance (`right_pq_dominance`) is the key blocker. LEFT multiplication dominance exists but RIGHT multiplication requires different reasoning about entry vs position permutations.

### Cluster B: Weyl Character Formula (4 sorries)
Three independent sub-lemmas in Theorem5_22_1 plus Proposition5_22_2. Well-decomposed; each can be tackled independently.

### Cluster C: Gabriel Chain (7 sorries)
Proposition6_6_6_source (1 sorry) is the keystone. Source naturality instance diamond is the last blocker.

### Cluster D: Mackey Machine (3 sorries)
Parts (i), (ii), (iii) of Theorem5_27_1. Require Clifford theory infrastructure.

## Trajectory

| Wave | Sorries | Files | Items sorry-free | Date |
|------|---------|-------|------------------|------|
| 33 | 43 | 22 | 566/583 (97.1%) | 2026-03-24 |
| 34 | 44 | 22 | 567/583 (97.2%) | 2026-03-24 |
| 35 | 43 | 21 | 568/583 (97.4%) | 2026-03-26 |
| 36 | 37 | 22 | 568/583 (97.4%) | 2026-03-27 |
| 37 | 33 | 21 | 568/583 (97.4%) | 2026-03-27 |
| 38 | 27 | 19 | 570/583 (97.8%) | 2026-03-27 |
| 39 | 29 | 17 | 571/583 (97.9%) | 2026-03-28 |

## Assessment

The sorry count tick-up from 27→29 masks significant progress. The actual proof content increased dramatically — 35+ PRs in ~24 hours represents the highest throughput wave to date. The decomposition of coarse sorrys (Theorem5_22_1 from 1→3, Example9_4_4 from 1→2) into independent, more tractable sub-tasks is a healthy pattern that enables parallel work.

The project is in a mature phase where remaining sorrys are genuinely hard mathematical problems. The low-hanging fruit is exhausted. The 6 dependency clusters are well-understood, and strategic focus on keystone sorrys (Proposition6_6_6_source, right_pq_dominance) can cascade into significant reductions.
