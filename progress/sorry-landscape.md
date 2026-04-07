# Sorry Landscape Analysis — Wave 46

Generated 2026-04-08 by summarize session (issue #2202).

## Summary

**15 sorries** across 8 files. Same count as wave 45 (15/8), but the composition shifted: Corollary6_8_4 dropped from 2→1 (source/sink reflection functor cases proved), while PolytabloidBasis went from 7→8 (false evaluation lemmas removed, replaced by properly-scoped coefficient lemmas).

Chapters 3, 4, 7, 8 remain 100% sorry-free. 273 of 281 Lean files (97.2%) are sorry-free. 580/583 items (99.5%) sorry-free.

14 PRs merged since wave 45 (#2158–#2203). Key changes:

- **Corollary6_8_4 source/sink cases proved** (#2184, #2197) — Resolved typeclass synthesis blocker, then proved both source and sink reflection functor cases. Sorry count 2→1. Only the mixed vertex case remains (requires admissible ordering backward construction).
- **Extended Dynkin infrastructure** (#2196) — Defined Ẽ_6 and Ẽ_8 adjacency matrices and basic graph properties. Foundation for non-ADE tree classification.
- **PolytabloidBasis restructuring** (#2162, #2172) — Proved `polytabloid_apply` and `polytabloid_self_coeff` are FALSE for T-dependent definition (removed 2 false sorries). Restructured Garnir/straightening: removed false `garnir_columnInvCount_decrease`, replaced with direct sorry + documentation of two correct approaches. Net: 7→8 sorries (better-scoped).
- **YoungSymmetrizer convention fix** (#2178) — Changed from a·b to b·a multiplication order.
- **swapOp infrastructure** (#2180) — Infrastructure lemmas for Problem6_9_1 compatible chain basis.
- **Radical preservation** (#2166) — Proved radical preservation by module category equivalences (sorry-free).

**Net sorry change: 0.** Corollary6_8_4 −1, PolytabloidBasis +1. The Corollary6_8_4 progress is genuine proof work; the PolytabloidBasis change is architectural cleanup (removing false lemmas, adding correct replacements).

**Definition-level sorries: 0.** All mathematical objects are constructed. No regression.

## Chapter Breakdown

| Chapter | Sorries | Files | Delta from Wave 45 |
|---------|---------|-------|---------------------|
| Ch2 | 1 | 1 | 0 |
| Ch5 | 10 | 3 | +1 sorry (PolytabloidBasis 7→8), 0 files |
| Ch6 | 3 | 3 | −1 sorry (Corollary6_8_4 2→1), 0 files |
| Ch9 | 1 | 1 | 0 |

## Files That Became Sorry-Free Since Wave 45

(None — no files crossed the 0-sorry threshold this wave.)

## Per-File Sorry Detail

| File | Sorries | Nature | Delta from W45 |
|------|---------|--------|----------------|
| PolytabloidBasis (Ch5) | 8 | polytabloid_mem_spechtModule + youngSymmetrizer_one_coeff + youngSymmetrizer_rowPerm_coeff + youngSymmetrizer_support + youngSymmetrizer_pq_coeff + polytabloid_linearIndependent + column_standard_in_span' + perm_mul_youngSymmetrizer_mem_span_polytabloids | **+1** |
| FormalCharacterIso (Ch5) | 1 | iso_of_glWeightSpace_finrank_eq (complete reducibility of GL_N reps) | 0 |
| TabloidModule (Ch5) | 1 | polytabloid_syt_dominance (PQ transformation dominance) | 0 |
| MoritaStructural (Ch9) | 1 | projective lift surjectivity (progenerator theory) | 0 |
| Theorem2_1_2 (Ch2) | 1 | Gabriel's theorem (finite rep type ↔ Dynkin) | 0 |
| Corollary6_8_4 (Ch6) | 1 | Mixed vertex case: admissible ordering backward construction | **−1** |
| Problem6_1_5_theorem (Ch6) | 1 | Theorem_6_1_5 forward direction (positive definiteness → finite type) | 0 |
| Problem6_9_1 (Ch6) | 1 | off_diagonal_nilpotent_product_decomp (compatible chain basis) | 0 |

## Merged PRs Since Wave 45 (14)

### Gabriel Theorem Chain / Infinite Type (Ch6)
| PR | Title |
|----|-------|
| #2184 | Resolve typeclass synthesis blocker in Corollary6_8_4 |
| #2196 | Define Ẽ_6 and Ẽ_8 adjacency matrices and basic graph properties |
| #2197 | Prove source and sink reflection functor cases in Corollary6_8_4 |

### Schur-Weyl / Polytabloid (Ch5)
| PR | Title |
|----|-------|
| #2162 | polytabloid_apply and polytabloid_self_coeff are FALSE for T-dependent definition |
| #2172 | Remove false garnir_columnInvCount_decrease, restructure straightening |
| #2178 | Fix YoungSymmetrizer convention from a·b to b·a |

### Morita Theory (Ch9)
| PR | Title |
|----|-------|
| #2166 | Prove radical preservation by module category equivalences |

### Problem 6.9.1 (Ch6)
| PR | Title |
|----|-------|
| #2180 | swapOp infrastructure lemmas for compatible chain basis |

### Documentation / Analysis
| PR | Title |
|----|-------|
| #2158 | PolytabloidBasis architecture assessment and skill updates |
| #2177 | Corollary6_8_4 synthesis blocker diagnosis |
| #2182 | Analysis of #2143, #2124, #2179 (all difficulty 8+) |

### Infrastructure / Fixes
| PR | Title |
|----|-------|
| #2160 | Wave 45 sorry landscape update |
| #2167 | Rebase and re-trigger CI on 3 mergeable PRs |
| #2203 | Rebase PR #2191 and re-trigger CI on #2192/#2190 |

## Open PRs (pending merge)

| PR | Title | Status |
|----|-------|--------|
| #2200 | Prove etilde8_not_finite_type via Ẽ_6 subgraph embedding | CI failed |
| #2198 | Ẽ_6 representation construction (indecomposability sorry) | CI failed |
| #2192 | Fix CI build errors in Problem6_9_1 and Theorem5_22_1 | CI pending |
| #2191 | Extended Dynkin D̃_n infinite type proof | CI pending |
| #2190 | Fix Problem6_9_1 + Theorem5_22_1 build errors | CI pending |
| #2183 | Prove YoungSymmetrizer coefficient lemmas and polytabloid_mem_spechtModule (6 sorries) | CI failed |
| #2175 | Infrastructure: equivalence preserves Module.Finite | CI cancelled |
| #2168 | Refactor: remove dead polytabloid_syt_dominance sorry (TabloidModule 1→0) | CI failed |

**Note:** PRs #2192 and #2190 are competing fixes for #2188 (main CI breakage). Whichever passes CI first should merge; the other should close. Multiple PRs (#2200, #2198, #2183, #2168) have CI failures likely caused by the same main-branch build errors — they should be rebased after #2188 is resolved.

## Active Work Items (claimed)

| Issue | Title | Impact |
|-------|-------|--------|
| #2179 | Close compatible_product_decomp sorry using pure generator replacement | 1→0 sorry (Problem6_9_1) |

## Unclaimed Work Items

| Issue | Title | Impact |
|-------|-------|--------|
| #2088 | Prove polytabloid_syt_dominance in TabloidModule (1→0 sorry) | Unblocks #2106 (linearIndependent) |
| #2143 | Non-ADE tree classification: contains infinite-type subgraph | Major Ch6 milestone |
| #2170 | Prove Corollary6_8_4 mixed vertex case (1→0 sorry) | Closes Corollary6_8_4 |

## Blocked Work Items

| Issue | Blocked on | Title |
|-------|-----------|-------|
| #2199 | (no dep listed) | Prove etilde6Rep_isIndecomposable (Ẽ_6 indecomposability) |
| #2187 | #2185 | Non-ADE tree case analysis combining all infinite-type subgraphs |
| #2174 | #2173 | Prove head_isomorphism using Module.Finite + Wedderburn-Artin |
| #2112 | #2143 | Close positive definiteness sorry in Theorem_6_1_5 forward direction |
| #2106 | #2088 | Close polytabloid_linearIndependent after polytabloid_syt_dominance |

## Stale Issues (recommend closing)

| Issue | Reason |
|-------|--------|
| #1733 | Theorem5_18_4 is now sorry-free (was 4 sorries when filed) |
| #1729 | Infrastructure is now sorry-free; Ch9 reduced to 1 sorry (MoritaStructural) — superseded by more specific issues |
| #2001 | Proposition5_14_1.lean is sorry-free — issue may be resolved |
| #1842 | TabloidSetoid RIGHT coset refactor — may be superseded by polytabloid definition switch (#2132) |

## Dependency Clusters

### Cluster A: Polytabloid Basis (Ch5, 9 sorries)
**Files:** PolytabloidBasis (8), TabloidModule (1)
**Key sorries:**
- `polytabloid_mem_spechtModule` — show polytabloid ∈ Specht module under T-dependent definition
- `youngSymmetrizer_one_coeff` — coefficient of identity in YoungSymmetrizer (NEW, replaces false polytabloid_apply)
- `youngSymmetrizer_rowPerm_coeff` — coefficient of row permutations (NEW)
- `youngSymmetrizer_support` — support characterization (renamed from polytabloid_support)
- `youngSymmetrizer_pq_coeff` — PQ decomposition coefficient (NEW)
- `polytabloid_linearIndependent` — needs polytabloid_syt_dominance first (#2088→#2106)
- `column_standard_in_span'` — straightening algorithm (difficulty ~7)
- `perm_mul_youngSymmetrizer_mem_span_polytabloids` — straightening lemma (replaces false garnir approach)
- `polytabloid_syt_dominance` — PQ transformation dominance (TabloidModule)
**Status:** Slightly up from 8→9. PR #2162 proved 2 evaluation lemmas FALSE (polytabloid_apply, polytabloid_self_coeff). PR #2172 restructured garnir into direct straightening approach. PR #2183 (open, CI failed) would close 6 of these if merged. The coefficient lemmas are the critical path — PR #2181 targets them.
**Critical path:** Coefficient lemmas (PR #2181/2183) → #2088 (dominance) → #2106 (linearIndependent). Spanning direction needs #2104-style restructuring.

### Cluster B: Weyl Character Formula (Ch5, 1 sorry)
**Files:** FormalCharacterIso (1)
**Remaining:**
- `iso_of_glWeightSpace_finrank_eq` — GL_N complete reducibility (Schur-Weyl duality)
**Status:** Unchanged. Requires deep infrastructure (Schur module decomposition for polynomial GL_N reps).

### Cluster D: Gabriel Theorem Chain (Ch6, 3 sorries)
**Files:** Corollary6_8_4 (1), Problem6_1_5_theorem (1), Problem6_9_1 (1)
**Status:** Down from 4→3. Corollary6_8_4 source/sink cases proved (#2197). Extended Dynkin Ẽ_6/Ẽ_8 definitions added (#2196). D̃_n proof in open PR (#2191).
**Key changes:**
- Corollary6_8_4: 2→1 (source/sink proved, mixed vertex remains)
- Problem6_1_5_theorem: unchanged at 1 (forward direction needs non-Dynkin → infinite type)
- Problem6_9_1: unchanged at 1 (compatible chain basis, #2179 claimed)

### Cluster E: Morita Theory (Ch9, 1 sorry)
**Files:** MoritaStructural (1)
**Remaining:**
- Projective lift surjectivity (progenerator theory)
**Status:** Unchanged at 1. Radical preservation proved (#2166).

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
| 46 | 15 | 8 | 580/583 (99.5%) | 2026-04-08 |

*Wave 41 corrected from reported 25/11 to actual 28/14.

The sorry count has stabilized at 15 for two waves. This reflects the project entering a "hard sorry" phase: the remaining 15 sorries are all difficulty 7+ (combinatorial arguments, admissible ordering theory, Schur-Weyl duality, progenerator theory). Quick wins have been exhausted.

**Honest assessment:** The project is at 99.5% item-level completion (580/583). The remaining 15 sorries are concentrated in 4 dependency clusters. The most tractable near-term targets are: (1) PR #2183 merging to close 6 PolytabloidBasis coefficient sorries, (2) Corollary6_8_4 mixed vertex case (#2170), (3) Problem6_9_1 compatible chain basis (#2179, claimed). The hardest remaining sorries (polytabloid_syt_dominance, FormalCharacterIso, Theorem2_1_2) require novel mathematical arguments.

## Strategic Recommendations

1. **Unblock main CI** (#2188) — PRs #2192/#2190 are pending. Once one merges, 6+ other PRs can be rebased and merged. This is the highest-priority bottleneck.

2. **YoungSymmetrizer coefficient lemmas** (PR #2183, open) — Would close 6 of 8 PolytabloidBasis sorries if CI passes after rebase. Highest sorry-count-reduction potential.

3. **Corollary6_8_4 mixed vertex** (#2170) — Down to 1 sorry. Admissible ordering backward construction is well-scoped. Difficulty 7.

4. **Problem6_9_1 compatible chain basis** (#2179, claimed) — PID module theory argument. In progress.

5. **Extended Dynkin proofs** (PRs #2191, #2200, #2198) — D̃_n, Ẽ_8, Ẽ_6 infinite type proofs are in open PRs. Once merged, unblocks non-ADE tree classification (#2143 → #2187 → #2112).

6. **Close stale issues** — #1733, #1729, #2001, #1842 should be closed or updated.

7. **polytabloid_syt_dominance** (#2088) — The critical path for polytabloid linear independence. Difficulty 8, novel combinatorial argument. No active PR.

8. **FormalCharacterIso** — Requires Schur module complete reducibility. Major infrastructure gap. Lowest priority.
