# Sorry Landscape Analysis — Wave 45

Generated 2026-04-06 by summarize session (issue #2151).

## Summary

**15 sorries** across 8 files. Up from 10 / 8 in wave 44: **+5 sorries, 0 files**. The increase is entirely due to architectural refactoring: the polytabloid definition switch (#2132) and TabloidRepresentation introduction (#2146) added 4 new evaluation-lemma sorries to PolytabloidBasis, and Corollary6_8_4 gained 1 sorry from infrastructure decomposition (#2157). No net sorry *removal* this wave — progress was structural (InfiniteTypeConstructions proved sorry-free, new proof infrastructure added).

Chapters 3, 4, 7, 8 remain 100% sorry-free. 273 of 281 Lean files (97.1%) are sorry-free. 580/583 items (99.5%) sorry-free.

13 PRs merged since wave 44 (#2126–#2157). Key changes:

- **InfiniteTypeConstructions sorry-free** (#2127, #2154, #2155) — All 4 sorries eliminated. Star K_{1,4} construction, subgraph embedding indecomposability, and starRep_isIndecomposable all proved. File went 4→0.
- **Star/tree degree ≥ 4 infinite type** (#2144, #2145, #2156) — New theorems: star_subgraph_not_finite_type, tree_degree_ge_4_not_finite_type. Proves Case 1 of non-ADE tree classification.
- **Polytabloid definition switch** (#2132) — Changed polytabloid from partition-based to T-dependent column antisymmetrizer. Added 4 new sorry'd evaluation lemmas (polytabloid_mem_spechtModule, polytabloid_apply, polytabloid_self_coeff, polytabloid_support).
- **TabloidRepresentation** (#2146) — New representation infrastructure. polytabloidTab_linearIndependent proved.
- **Corollary6_8_4 infrastructure** (#2157) — Added reflFunctorMinus_equivAt_eq. Decomposed 1 sorry into 2 more specific sorries (Dynkin-specific positive root argument + reflection functor chain step).
- **Swap operator infrastructure** (#2137) — swapOp definition for Problem6_9_1 compatible chain basis.
- **MoritaStructural helpers** (#2139) — jacobson_smul_eq_bot_of_semisimple proved sorry-free. Radical preservation infrastructure for #2135.

**Net sorry change: +5.** This is the first wave with a sorry *increase*. The increase is intentional — decomposing coarse sorry blocks into finer-grained ones to enable parallel work. The underlying mathematical progress (InfiniteTypeConstructions fully proved, new infinite type theorems) is substantial.

**Definition-level sorries: 0.** All mathematical objects are constructed. No regression.

## Chapter Breakdown

| Chapter | Sorries | Files | Delta from Wave 44 |
|---------|---------|-------|---------------------|
| Ch2 | 1 | 1 | 0 |
| Ch5 | 9 | 3 | +4 sorries (PolytabloidBasis 3→7), 0 files |
| Ch6 | 4 | 3 | +1 sorry (Corollary6_8_4 1→2), 0 files |
| Ch9 | 1 | 1 | 0 |

## Files That Became Sorry-Free Since Wave 44

(None — no files crossed the 0-sorry threshold this wave.)

## Files That Regressed

1. **PolytabloidBasis.lean** — 3→7. Four new sorry'd evaluation lemmas added by polytabloid definition switch (#2132) and TabloidRepresentation introduction (#2146): `polytabloid_mem_spechtModule`, `polytabloid_apply`, `polytabloid_self_coeff`, `polytabloid_support`. These are routine lemmas (difficulty ~3-5) needed to connect the new polytabloid definition to the existing proof infrastructure.
2. **Corollary6_8_4.lean** — 1→2. PR #2157 decomposed the single `indecomposable_of_positive_root` sorry into two more specific sub-goals: (a) Dynkin positive root argument (B(α,α)=2 → α is simple), (b) reflection functor chain step (universe-polymorphic transport).

## Per-File Sorry Detail

| File | Sorries | Nature | Delta from W44 |
|------|---------|--------|----------------|
| PolytabloidBasis (Ch5) | 7 | polytabloid_mem_spechtModule + polytabloid_apply + polytabloid_self_coeff + polytabloid_support + polytabloid_linearIndependent + column_standard_in_span' + garnir general case | **+4** |
| FormalCharacterIso (Ch5) | 1 | iso_of_glWeightSpace_finrank_eq (complete reducibility of GL_N reps) | 0 |
| TabloidModule (Ch5) | 1 | polytabloid_syt_dominance (PQ transformation dominance) | 0 |
| MoritaStructural (Ch9) | 1 | projective lift surjectivity (progenerator theory) | 0 |
| Theorem2_1_2 (Ch2) | 1 | Gabriel's theorem (finite rep type ↔ Dynkin) | 0 |
| Corollary6_8_4 (Ch6) | 2 | Dynkin positive root argument + reflection functor chain step | **+1** |
| Problem6_1_5_theorem (Ch6) | 1 | Theorem_6_1_5 forward direction (positive definiteness → finite type) | 0 |
| Problem6_9_1 (Ch6) | 1 | off_diagonal_nilpotent_product_decomp (compatible chain basis) | 0 |

## Merged PRs Since Wave 44 (13)

### Gabriel Theorem Chain / Infinite Type (Ch6)
| PR | Title |
|----|-------|
| #2127 | Prove InfiniteTypeConstructions sorry-free (4→0 sorries) |
| #2144 | Star K_{1,4} infinite type construction (1 sorry) |
| #2145 | Subgraph embedding transfers infinite type |
| #2154 | Prove starRep_isIndecomposable sorry (1 sorry removed) |
| #2155 | Prove subgraph embedding indecomposability (1 sorry removed) |
| #2156 | Prove star subgraph and tree degree ≥ 4 infinite type |
| #2157 | Corollary6_8_4 proof infrastructure (2 sorries remain) |

### Schur-Weyl / Polytabloid (Ch5)
| PR | Title |
|----|-------|
| #2126 | Deep analysis of polytabloid_syt_dominance |
| #2132 | Switch polytabloid to T-dependent column antisymmetrizer |
| #2146 | Introduce TabloidRepresentation and polytabloidTab_linearIndependent |

### Morita Theory (Ch9)
| PR | Title |
|----|-------|
| #2139 | Sorry-free helpers for MoritaStructural radical preservation (#2135) |

### Problem 6.9.1 (Ch6)
| PR | Title |
|----|-------|
| #2137 | Swap operator infrastructure for Problem 6.9.1(c) (#2083) |

### Infrastructure / Fixes
| PR | Title |
|----|-------|
| #2136 | Fix PR #2133 |

## Open PRs (pending merge)

| PR | Title | Status |
|----|-------|--------|
| #2159 | Prove lifting/splitting steps of MoritaStructural sorry (#2135) | Open, CI pending |
| #2158 | PolytabloidBasis architecture assessment and skill updates (meditate #2152) | Open, CI cancelled |
| #2148 | Sorry-free helpers and proof strategy for MoritaStructural (#2135) | Open, CI cancelled |

## Active Work Items (claimed)

| Issue | Title | Impact |
|-------|-------|--------|
| #2150 | Prove PolytabloidBasis evaluation lemmas (polytabloid_apply, self_coeff, support) | 4→0 sorry (evaluation lemmas) |
| #2135 | Prove MoritaStructural projective lift surjectivity | 1→0 sorry |

## Unclaimed Work Items

| Issue | Title | Impact |
|-------|-------|--------|
| #2083 | Prove compatible_chain_basis_decomp (Problem6_9_1) | 1→0 sorry |
| #2104 | Restructure straightening WF induction for Garnir expansion | Unblocks garnir general case |
| #2124 | Prove SYT entry comparison lemma (polytabloid_syt_dominance) | Unblocks #2125, #2088, #2106 |

## Dependency Clusters

### Cluster A: Polytabloid Basis (Ch5, 8 sorries)
**Files:** PolytabloidBasis (7), TabloidModule (1)
**Key sorries:**
- `polytabloid_mem_spechtModule` — NEW: show polytabloid ∈ Specht module under new T-dependent definition
- `polytabloid_apply` — NEW: evaluation formula for the new polytabloid definition
- `polytabloid_self_coeff` — NEW: e_T(σ_T) = 1 for the new definition
- `polytabloid_support` — NEW: support characterization via PQ decomposition
- `polytabloid_linearIndependent` — needs polytabloid_syt_dominance first (#2088→#2106)
- `column_standard_in_span'` — straightening algorithm (difficulty ~7)
- garnir general case — **FALSE statement** per wave 44 analysis. Needs multiset Dershowitz-Manna ordering (#2104)
- `polytabloid_syt_dominance` — PQ transformation dominance. Sub-task #2124 for entry comparison lemma.
**Status:** Increased from 4→8 due to polytabloid definition switch. The 4 new evaluation lemmas (#2150, claimed) are routine (difficulty 3-5). The 4 original sorries remain at difficulty 7-9. The architectural change is necessary — the old partition-based column antisymmetrizer was provably incorrect.
**Critical path:** #2150 (evaluation lemmas) → #2124 (SYT comparison) → #2088 (dominance) → #2106 (linearIndependent). Spanning direction blocked on #2104 (Garnir restructuring).

### Cluster B: Weyl Character Formula (Ch5, 1 sorry)
**Files:** FormalCharacterIso (1)
**Remaining:**
- `iso_of_glWeightSpace_finrank_eq` — GL_N complete reducibility (Schur-Weyl duality)
**Status:** Unchanged. Requires deep infrastructure (Schur module decomposition for polynomial GL_N reps).

### Cluster D: Gabriel Theorem Chain (Ch6, 4 sorries)
**Files:** Corollary6_8_4 (2), Problem6_1_5_theorem (1), Problem6_9_1 (1)
**Status:** Up from 3→4 sorries (Corollary6_8_4 decomposed 1→2). But major progress: InfiniteTypeConstructions is now fully sorry-free (was 4 sorries in wave 43). New theorems for star subgraphs and trees with degree ≥ 4 vertices.
**Key changes:**
- InfiniteTypeConstructions: 4→0 (fully proved across #2127, #2154, #2155)
- Corollary6_8_4: 1→2 (decomposed into more specific sub-goals by #2157)
- Problem6_1_5_theorem: unchanged at 1 (forward direction needs non-Dynkin → infinite type)
- Problem6_9_1: unchanged at 1 (compatible chain basis, #2083 unclaimed)

### Cluster E: Morita Theory (Ch9, 1 sorry)
**Files:** MoritaStructural (1)
**Remaining:**
- Projective lift surjectivity (progenerator theory)
**Status:** Unchanged at 1. Helper infrastructure added (#2139). PRs #2148 and #2159 are open with further progress.

### Isolated
- **Theorem2_1_2** (1 sorry): Gabriel's theorem classification. Depends on Clusters A and D.

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
| 36 | 37 | 22 | 568/583 (97.4%) | 2026-03-27 |
| 37 | 33 | 21 | 568/583 (97.4%) | 2026-03-27 |
| 38 | 27 | 19 | 570/583 (97.8%) | 2026-03-27 |
| 39 | 29 | 17 | 571/583 (97.9%) | 2026-03-28 |
| 40 | 23 | 13 | 571/583 (97.9%) | 2026-04-02 |
| 41* | 28 | 14 | 577/583 (98.9%) | 2026-04-03 |
| 42 | 25 | 14 | 577/583 (98.9%) | 2026-04-03 |
| 43 | 13 | 10 | 579/583 (99.3%) | 2026-04-04 |
| 44 | 10 | 8 | 580/583 (99.5%) | 2026-04-05 |
| 45 | 15 | 8 | 580/583 (99.5%) | 2026-04-06 |

*Wave 41 corrected from reported 25/11 to actual 28/14.

Wave 45 is the first wave with a sorry *increase* (10→15). This is not a regression — it reflects intentional architectural decomposition. The polytabloid definition switch (#2132) was necessary because the old partition-based column antisymmetrizer was mathematically incorrect. The Corollary6_8_4 decomposition (#2157) splits an opaque sorry into two clearly-scoped sub-goals. Meanwhile, InfiniteTypeConstructions went from 4 sorries (wave 43) to 0, which is genuine mathematical progress.

**Honest assessment:** The sorry count metric is no longer monotonically decreasing. At this stage of the project, architectural correctness matters more than sorry count. The 4 new evaluation lemmas in PolytabloidBasis are routine (claimed by #2150) and should be closed quickly. The hard sorries remain: polytabloid_syt_dominance (difficulty 8), garnir restructuring (difficulty 9), compatible_chain_basis (difficulty 9), and positive definiteness forward direction.

## Strategic Recommendations

1. **PolytabloidBasis evaluation lemmas** (#2150, claimed) — Close the 4 new routine sorries (polytabloid_apply, polytabloid_self_coeff, polytabloid_support, polytabloid_mem_spechtModule). This brings PolytabloidBasis back to 3 sorries and unblocks downstream work. Highest priority for sorry count reduction.

2. **MoritaStructural** (#2135, claimed) — PRs #2148 and #2159 are open. If merged and the remaining sorry is closed, eliminates Cluster E entirely.

3. **polytabloid_syt_dominance** (#2124) — The SYT entry comparison lemma remains the critical path for the independence direction. Difficulty 8, novel combinatorial argument. Unblocks the longest dependency chain: #2124 → #2088 → #2106.

4. **Problem6_9_1 compatible chain basis** (#2083) — PID module theory argument. If successful, eliminates one of 4 Gabriel chain sorries.

5. **Corollary6_8_4** — Now has 2 specific sub-goals. The Dynkin positive root argument may be tractable with the new InfiniteTypeConstructions infrastructure. The reflection functor chain step needs universe-polymorphic transport.

6. **Garnir restructuring** (#2104) — Blocked on multiset Dershowitz-Manna ordering. High risk, high reward. Unblocks spanning direction of polytabloid basis.

7. **FormalCharacterIso** — Requires Schur module complete reducibility. Major infrastructure gap. Lowest priority given difficulty.
