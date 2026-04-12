# Sorry Landscape Analysis — Wave 50

Generated 2026-04-13 by summarize session (issue #2309).

## Summary

**13 sorries** across 5 files (up from 10/6 in wave 49). Chapters 3, 4, 7, 8, 9 are 100% sorry-free.

279 of 284 Lean files (98.2%) are sorry-free. 581/583 items (99.7%) sorry-free.

**Definition-level sorries: 0.** All mathematical objects are constructed.

**Why sorries went UP 10→13:** Continued decomposition strategy. The `non_ade_graph_not_finite_type` sorry (1) was decomposed into 2 sub-cases (`not_posdef_single_branch_infinite_type` + `non_adjacent_branches_infinite_type`); the `polytabloidTab_column_standard_in_span` sorry (1) was decomposed into 3 sub-sorries (`garnir_polytabloid_identity`, `garnir_twisted_in_lower_span`, `garnir_straightening_step`); and a new sorry appeared in Proposition5_22_2 (`glWeightSpace_schurModule_iSup_eq_top`). Meanwhile, **MoritaStructural (Ch9) became sorry-free** — the major achievement of this wave.

### Merges since wave 49 (15 PRs, 2026-04-12):

| PR | Date | Title | Sorry Impact |
|----|------|-------|-------------|
| #2272 | 04-12 | Decompose straightening theorem sorry 1→2, prove induction skeleton | SpechtModuleBasis 1→2 |
| #2278 | 04-12 | Decompose non_ade_graph_not_finite_type, prove degree ≥ 4 and triangle | InfiniteTypeConstructions decompose |
| #2280 | 04-12 | Weight decomposition infrastructure for Schur modules | Proposition5_22_2 +1 sorry |
| #2281 | 04-12 | Meditate wave 48 — endgame strategy review and skill updates | Documentation |
| #2282 | 04-12 | Prove head_isomorphism, reduce MoritaStructural 2→1 | MoritaStructural 2→1 |
| #2289 | 04-12 | Prove eq_of_rowStandard_of_toTabloid_eq (row-standard uniqueness) | Infrastructure |
| #2290 | 04-12 | Prove acyclic_deg_le_2_posdef, reduce sorry 1→2 | InfiniteTypeConstructions infra |
| #2291 | 04-12 | Prove graph_with_list_cycle_infinite_type | InfiniteTypeConstructions infra |
| #2292 | 04-12 | Prove semisimple_iso_of_finrank_hom_eq, close Ch9 MoritaStructural | **MoritaStructural 1→0** |
| #2293 | 04-12 | Decompose acyclic_branch sorry 1→3, prove tree acyclicity lemmas | InfiniteTypeConstructions decompose |
| #2297 | 04-12 | Replace zero maps with real edge maps for etilde7/t125 | InfiniteTypeConstructions fix |
| #2298 | 04-12 | Prove adjacent_branches_infinite_type D̃₅ embedding | InfiniteTypeConstructions infra |
| #2304 | 04-12 | Decompose garnir_straightening_step into focused sub-problems | SpechtModuleBasis 2→3 |
| #2305 | 04-12 | Remove duplicate graph_with_list_cycle_infinite_type, fix call site | Bug fix |
| #2306 | 04-12 | Prove acyclic_path_posdef sub-goals (connectivity + 2-regular cycle) | InfiniteTypeConstructions infra |

**Net: 1 sorry genuinely closed (MoritaStructural), 4 decomposition sorries introduced (net +3). Files with sorries: 6→5 (MoritaStructural cleared).**

### Files that became sorry-free since wave 49:
- **MoritaStructural** (Ch9) — closed by PR #2292 (semisimple_iso_of_finrank_hom_eq). Ch9 is now entirely sorry-free.

### Files that gained sorries since wave 49:
- **InfiniteTypeConstructions** (Ch6) — 4→5 (non_ade_graph decomposed into single_branch + non_adjacent_branches; offset by several infrastructure proofs)
- **SpechtModuleBasis** (Ch5) — 1→3 (garnir_straightening decomposed into 3 sub-problems)
- **Proposition5_22_2** (Ch5) — 1→2 (weight space supremum sorry added for dimension infrastructure)

## Chapter Breakdown

| Chapter | Sorries | Files | Delta from Wave 49 |
|---------|---------|-------|---------------------|
| Ch2 | 2 | 1 | 0 |
| Ch5 | 6 | 3 | +3 (decompositions in SpechtModuleBasis + Proposition5_22_2) |
| Ch6 | 5 | 1 | +1 (decomposition in InfiniteTypeConstructions) |
| Ch9 | 0 | 0 | **−1 (MoritaStructural closed!)** |

## Per-File Sorry Detail

| File | Sorries | Theorems | Delta |
|------|---------|----------|-------|
| InfiniteTypeConstructions (Ch6) | 5 | `etilde6v2Rep_isIndecomposable` (line 2097), `etilde7Rep_isIndecomposable` (line 2339), `t125Rep_isIndecomposable` (line 2551), `not_posdef_single_branch_infinite_type` (line 3595), `non_adjacent_branches_infinite_type` (line 3631) | **+1** |
| SpechtModuleBasis (Ch5) | 3 | `garnir_polytabloid_identity` (line 509), `garnir_twisted_in_lower_span` (line 534), `garnir_straightening_step` (line 559) | **+2** |
| Theorem2_1_2 (Ch2) | 2 | Forward direction: finite rep type → positive definite (line 156), Backward: Dynkin → finite rep type (line 162) | 0 |
| Proposition5_22_2 (Ch5) | 2 | `glWeightSpace_schurModule_iSup_eq_top` (line 301), `h_dim`: dimension equality for det-twisted Schur module (line 346) | **+1** |
| FormalCharacterIso (Ch5) | 1 | `iso_of_glWeightSpace_finrank_eq` (line 116, GL_N complete reducibility) | 0 |

## Open PRs (2)

| PR | Title | CI Status | Mergeable |
|----|-------|-----------|-----------|
| #2307 | Decompose single_branch_not_posdef_infinite_type, prove Ẽ₆ case | FAILURE | Yes |
| #2312 | Prove non_adjacent_branches_infinite_type (multi-branch → infinite type) | FAILURE | Yes |

**Both PRs have failing CI.** These need attention before they can merge.

## Blocked Issues (3)

| Issue | Blocked on | Title |
|-------|-----------|-------|
| #2256 | Theorem2_1_2 chain | Prove backward direction (Dynkin → finite rep type) |
| #2255 | Theorem2_1_2 chain | Prove positive definiteness in forward direction |
| #1571 | — | Reconcile repo with FormalFrontier templates (stale) |

## Claimed Work Items

| Issue | Title | Status |
|-------|-------|--------|
| #2309 | Update sorry landscape wave 50 | Claimed (this session) |
| #2310 | Prove indecomposability of etilde6v2, etilde7, t125 | Claimed |
| #2311 | Prove Garnir straightening sub-lemmas | Claimed |

## Unclaimed Work Items

| Issue | Title | Impact |
|-------|-------|--------|
| #2247 | Prove Theorem_2_1_2 (Gabriel's theorem) | 2→0 sorry, difficulty 9 |
| #2263 | Prove iso_of_formalCharacter + Proposition5_22_2 h_dim | 2→0 sorry |
| #2302 | Prove not_posdef_single_branch_infinite_type | 1→0 sorry, difficulty 7 (has failing PR #2307) |

## Dependency Clusters

### Cluster A: Polytabloid/Straightening (Ch5, 6 sorries)
**Files:** SpechtModuleBasis (3), Proposition5_22_2 (2), FormalCharacterIso (1)
**Key sorries:**
- `garnir_polytabloid_identity` — algebraic sum manipulation (difficulty 5)
- `garnir_twisted_in_lower_span` — combinatorial heart of straightening (difficulty 8)
- `garnir_straightening_step` — combines the above two
- `glWeightSpace_schurModule_iSup_eq_top` — weight spaces span Schur module
- `h_dim` in Proposition5_22_2 — dimension equality
- `iso_of_glWeightSpace_finrank_eq` — GL_N complete reducibility (difficulty 8)
**Status:** Up from 3→6 due to decompositions. Issue #2311 (claimed) targets the 3 Garnir sorries. Issue #2263 (unclaimed) targets Proposition5_22_2. The decomposition makes each sub-problem independently attackable.
**Critical path:** Garnir sub-sorries are self-contained; Proposition5_22_2 and FormalCharacterIso are independent.

### Cluster B: Infinite Type Classification (Ch6, 5 sorries)
**Files:** InfiniteTypeConstructions (5)
**Key sorries:**
- 3× `*_isIndecomposable`: etilde6v2, etilde7, t125 (representation indecomposability)
- `not_posdef_single_branch_infinite_type`: T(p,q,r) classification (PR #2307, failing CI)
- `non_adjacent_branches_infinite_type`: multi-branch case (PR #2312, failing CI)
**Status:** Up from 4→5 (decomposition). Major infrastructure landed: graph cycle infinite type (#2291), acyclic path positive definiteness (#2290, #2306), adjacent branches (#2298), tree acyclicity (#2293). Issue #2310 (claimed) targets indecomposability. Two PRs in flight for branch classification but both have CI failures.
**Critical path:** Branch classification sorries block `not_posdef_infinite_type` → forward direction of Gabriel's theorem.

### Cluster C: Morita Theory (Ch9) — CLOSED
**Files:** MoritaStructural — **sorry-free** as of PR #2292.
**Status:** Complete. Ch9 has 0 remaining sorries.

### Cluster D: Gabriel's Theorem (Ch2, 2 sorries)
**Files:** Theorem2_1_2 (2)
**Key sorries:** Forward direction (positive definiteness from finite type) and backward direction (Dynkin → finite rep type)
**Status:** Unchanged from wave 49. Both directions blocked on Cluster B completion (forward) and ADE classification infrastructure (backward). Issues #2255, #2256 blocked.

## Trajectory

| Wave | Sorries | Files | Items sorry-free | Date |
|------|---------|-------|------------------|------|
| 28 | 66 | 27 | 560/583 (96.1%) | 2026-03-22 |
| 33 | 43 | 22 | 566/583 (97.1%) | 2026-03-24 |
| 38 | 27 | 19 | 570/583 (97.8%) | 2026-03-27 |
| 43 | 13 | 10 | 579/583 (99.3%) | 2026-04-04 |
| 44 | 10 | 8 | 580/583 (99.5%) | 2026-04-05 |
| 45 | 15 | 8 | 580/583 (99.5%) | 2026-04-06 |
| 46 | 15 | 8 | 580/583 (99.5%) | 2026-04-08 |
| 47 | 9 | 6 | 581/583 (99.7%) | 2026-04-11 |
| 48 | 8 | 6 | 581/583 (99.7%) | 2026-04-11 |
| 49 | 10 | 6 | 581/583 (99.7%) | 2026-04-12 |
| **50** | **13** | **5** | **581/583 (99.7%)** | **2026-04-13** |

**Note on wave 50 increase:** The raw sorry count increased 10→13 because of continued decomposition (non_ade_graph 1→2, garnir_straightening 1→3, Proposition5_22_2 +1). One genuine sorry was closed (MoritaStructural). The file count decreased 6→5. Each remaining sorry is smaller and more focused than the monolithic ones they replaced.

## Honest Assessment

The project continues in the endgame with **decomposition as the primary strategy**. The headline achievement is **Chapter 9 becoming sorry-free** — the first chapter to clear all sorries since the endgame began. The sorry count increase (10→13) is entirely from decomposition; the "effective difficulty" per sorry has decreased.

**Concerns:**
1. **Two PRs with failing CI** (#2307, #2312) — these represent work that may need significant rework. If the CI failures are due to merge conflicts with the 15 PRs that landed, rebasing may suffice; if they're due to proof errors, the approaches may need revisiting.
2. **Cluster A growing** (3→6 sorries) — the Garnir straightening and Schur module dimension proofs are hard (difficulty 5-8). The decomposition helps parallelization but doesn't reduce total difficulty.
3. **No item-level progress** — items.json still shows 581/583. The 2 remaining items (Theorem2.1.2, Corollary6.8.4) have not changed status, though Corollary6.8.4 has no actual sorry tactics remaining and may need a status update.

**Most tractable targets (by difficulty):**
1. `garnir_polytabloid_identity` (#2311, claimed, difficulty 5) — algebraic sum manipulation
2. `not_posdef_single_branch_infinite_type` (#2302, has failing PR #2307, difficulty 7) — T(p,q,r) case analysis
3. `non_adjacent_branches_infinite_type` (has failing PR #2312) — multi-branch embedding
4. `glWeightSpace_schurModule_iSup_eq_top` — weight space decomposition

**Hard targets:**
5. `*_isIndecomposable` ×3 (#2310, claimed) — nilpotent invariant complement arguments
6. `garnir_twisted_in_lower_span` (#2311, claimed, difficulty 8) — combinatorial heart of straightening
7. `iso_of_glWeightSpace_finrank_eq` — GL_N complete reducibility, difficulty 8
8. Theorem2_1_2 forward/backward — top-level, blocked on Clusters B and D

**CI needs attention** — both open PRs have failing CI. Fixing these should be prioritized over new work.

## Strategic Recommendations

1. **Fix failing PRs #2307 and #2312** — unblocking these is higher priority than new work. Check if the failures are merge conflicts (likely given 15 PRs merged) or proof errors.

2. **Update Corollary6.8.4 status** — the file has no sorry tactics. If it's truly sorry-free, update items.json to `sorry_free` (gaining 581→582 items done).

3. **Focus on Cluster B** — the infinite type classification is the critical path to Gabriel's theorem. The 3 indecomposability proofs (#2310, claimed) are independent and parallelizable.

4. **Garnir sub-lemmas** (#2311, claimed) — the polytabloid identity (difficulty 5) should be attempted first as a quick win.

5. **Accept long-term sorries** — FormalCharacterIso (`iso_of_glWeightSpace_finrank_eq`, GL_N complete reducibility) and possibly the 3 indecomposability proofs may represent genuinely hard formalization beyond current Mathlib infrastructure.
