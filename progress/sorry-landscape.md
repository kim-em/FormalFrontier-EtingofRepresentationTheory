# Sorry Landscape Analysis — Wave 52

Generated 2026-04-17 by summarize session (issue #2365).

## Summary

**17 sorries** across 4 files (down from 21/5 in wave 51). The sorry count
decreased by 4, driven by 7 closures (T(1,2,2) posdef proved, T(1,5,2)/T(1,2,5)
eliminated as unprovable, twistedPolytabloid_col_eq proved, h_dim proved,
3 leaf cases consolidated to 1) offset by 3 additions (dTildeRep_isIndecomposable,
tree_two_leaf_posdef h_bound/h_strict decomposition).

282 of 285 Lean files (98.9%) are sorry-free. 582/583 items (99.8%) sorry-free.

**Definition-level sorries: 0.** All mathematical objects are constructed.

### Merges since wave 51 (13 PRs, 2026-04-16 through 2026-04-17):

| PR | Date | Title | Sorry Impact |
|----|------|-------|-------------|
| #2337 | 04-16 | Fix PR #2323 merge conflicts (garnir_twisted_in_lower_span rebase) | Build fix |
| #2338 | 04-16 | Update sorry landscape and progress summary (Wave 51, ~30 PRs) | Docs only |
| #2339 | 04-16 | refactor: extract leaf_case helper in non_adjacent_branches_infinite_type (3→1 sorry) | InfiniteTypeConstructions 3→1 |
| #2340 | 04-16 | fix: close 2 unprovable sorries via embed_t125_in_tree | InfiniteTypeConstructions −2 (T(1,5,2) and T(1,2,5) were Ẽ₈, not E₈) |
| #2342 | 04-16 | fix: restrict etilde6v2Rep_isIndecomposable to m ≥ 1 (statement fix only) | Statement fix |
| #2350 | 04-16 | progress: decompose #2331 into sub-issues #2347-#2349 | Docs only |
| #2351 | 04-16 | Prove iso_of_glWeightSpace_finrank_eq + Proposition5_22_2 h_dim | Proposition5_22_2 −1 (h_dim proved) |
| #2352 | 04-16 | feat: WIP tree_two_leaf_posdef helper + strengthened acyclic_path_posdef_aux | InfiniteTypeConstructions infra (+2 new sub-sorries from decomposition) |
| #2353 | 04-17 | feat: prove T(1,2,2)=E₆ posdef in single_branch_leaf_case | InfiniteTypeConstructions −1 (T(1,2,2) proved) |
| #2358 | 04-17 | feat: D̃_n infrastructure (adj, quiver, rep, not_finite_type) — indecomposability sorry | InfiniteTypeConstructions +1 (new dTildeRep_isIndecomposable) |
| #2368 | 04-17 | feat: add E₈ posdef helper infrastructure | InfiniteTypeConstructions infra |
| #2369 | 04-17 | 2364 | Minor fix |
| #2370 | 04-17 | feat: prove h_decomp in tree_two_leaf_posdef + fix signature | InfiniteTypeConstructions: h_decomp proved (1 of 3 sub-sorries closed); also fixed soundness bug by adding h_deg_le2 hypothesis |

**Net:**
- Genuine closures: 5 (T(1,2,2) posdef, twistedPolytabloid_col_eq, h_dim, T(1,5,2) and T(1,2,5) eliminated)
- Consolidation: 3→1 (leaf cases in non_adjacent_branches)
- New sorries from decomposition: 2 (tree_two_leaf_posdef h_bound/h_strict)
- New sorries from infrastructure: 1 (dTildeRep_isIndecomposable)
- Raw count change: 21 → 17 (−4)
- Files with sorries: 5 → 4 (Proposition5_22_2 cleared)

**Soundness fixes in this wave:**
- PR #2342 restricted `etilde6v2Rep_isIndecomposable` to `m ≥ 1` (statement was false for m=0)
- PR #2370 added `h_deg_le2` hypothesis to `tree_two_leaf_posdef` (was false without it;
  counterexample: tree with two degree-3 vertices has QF=0 on nonzero vector)
- PR #2340 identified T(1,5,2) and T(1,2,5) as actually Ẽ₈ (9 vertices), not E₈ (8 vertices) —
  these sorries were literally unprovable as stated

## Chapter Breakdown

| Chapter | Sorries | Files | Delta from Wave 51 |
|---------|---------|-------|---------------------|
| Ch2 | 2 | 1 | 0 |
| Ch5 | 2 | 2 | −2 (twistedPolytabloid_col_eq proved, h_dim proved) |
| Ch6 | 13 | 1 | −2 (net: T(1,2,2)+T(1,5,2)+T(1,2,5) removed, leaf cases 3→1; dTilde+h_bound/h_strict added) |
| Ch9 | 0 | 0 | 0 |

## Per-File Sorry Detail

### InfiniteTypeConstructions (Ch6) — 13 sorries

**Indecomposability (4):**
- Line 2177 — `dTildeRep_isIndecomposable` (**NEW** — D̃_n arbitrary path-length; #2358)
- Line 2331 — `etilde6v2Rep_isIndecomposable` (Ẽ₆ mixed orientation, m ≥ 1)
- Line 2578 — `etilde7Rep_isIndecomposable` (Ẽ₇ sink orientation)
- Line 2790 — `t125Rep_isIndecomposable` (T(1,2,5) sink orientation)

**`tree_two_leaf_posdef` sub-sorries (2):**
- Line 4434 — `h_bound`: V² ≤ QF adj x₀₀ (graph reduction approach; needs Fin.succAbove)
- Line 4436 — `h_strict`: x₀₀ ≠ 0 → V² < QF adj x₀₀ (same approach as h_bound)

**`single_branch_leaf_case` ADE positive-definiteness (4):**
- Line 5431 — T(1,4,2) = E₇ posdef
- Line 5435 — T(1,3,2) = E₆ posdef
- Line 5486 — T(1,2,4) = E₇ posdef
- Line 5489 — T(1,2,3) = E₆ posdef

**`single_branch_leaf_case` D-type positive-definiteness (2):**
- Line 5900 — D-type (a₃ leaf) posdef
- Line 5916 — D-type (a₂ leaf) posdef

**`non_adjacent_branches_infinite_type` (1):**
- Line 6327 — leaf_case (subgraph embedding to Ẽ₆/Ẽ₇/T(1,2,5))

### SpechtModuleBasis (Ch5) — 1 sorry
- Line 632 — `garnir_twisted_in_lower_span` (combinatorial heart, difficulty 8)

### FormalCharacterIso (Ch5) — 1 sorry
- Line 221 — `iso_of_formalCharacter_eq_schurPoly` (GL_N complete reducibility / Schur-Weyl, difficulty 8)

### Theorem2_1_2 (Ch2) — 2 sorries (unchanged)
- Line 171 — Forward bridge: `not_posdef_not_HasFiniteRepresentationType`
  (needs per-field ∀k∀Q quantifier refactor of InfiniteTypeConstructions)
- Line 210 — Backward bridge: `isDynkinDiagram_HasFiniteRepresentationType`
  (needs positive root enumeration + Iso bridge to Chapter 2 setup)

## Open PRs (3)

| PR | Title | CI Status | Impact |
|----|-------|-----------|--------|
| #2354 | feat: WIP e7_tree_posdef + apply at T(1,3,2)/T(1,2,3) sorries | SUCCESS | Partial: E₇ posdef helper, would close 2 of 4 ADE sorries |
| #2355 | feat: fill E₇ posdef sorry sites and delete mk_e8_distinct | SUCCESS | Would close T(1,4,2) and T(1,2,4) sorries (−2) |
| #2367 | feat: WIP etilde7Rep_isIndecomposable - structural framework | SUCCESS | Partial: structural framework only, sorry remains |

All 3 open PRs have passing CI. If #2354 and #2355 merge, that would close all 4 E₇/E₆ posdef sorries
(T(1,4,2), T(1,3,2), T(1,2,4), T(1,2,3)), reducing InfiniteTypeConstructions to 9 sorries.

**Note:** PRs #2354 and #2355 may have merge conflicts with each other since both modify
the same region of InfiniteTypeConstructions.lean. The second to merge will need a rebase.

## Claimed Issues

| Issue | Title | Status |
|-------|-------|--------|
| #2361 | Fill tree_two_leaf_posdef helper sorries (3 sorry sites) | Claimed (partial PR #2370 merged) |
| #2362 | Fill D-type leaf posdef sorries in single_branch_leaf_case (2 sorry sites) | Claimed |
| #2363 | Fill non_adjacent_branches leaf_case sorry (subgraph embedding) | Claimed |
| #2365 | Update sorry landscape and progress summary (Wave 52) | Claimed (this session) |

## Unclaimed Issues

| Issue | Title | Impact |
|-------|-------|--------|
| #2255 | Prove positive definiteness in Theorem_2_1_2 forward direction | 1→0 sorry (Ch2), difficulty 8 |
| #2256 | Prove Theorem_2_1_2 backward direction (Dynkin → finite rep type) | 1→0 sorry (Ch2), difficulty 9 |
| #2366 | Meditate wave 49: endgame strategy review | Strategic review |

## Replan Issues (need new plans)

| Issue | Title | Notes |
|-------|-------|-------|
| #2325 | Prove Dynkin positive definiteness in single_branch_leaf_case (9→4 sorries) | Original 9 decomposed; #2340/#2353 closed 5; PRs #2354/#2355 address 4 more |
| #2331 | Prove leaf-case sorries in non_adjacent_branches | Decomposed into #2347-#2349 |
| #2332 | Prove iso_of_glWeightSpace_finrank_eq + Proposition5_22_2 h_dim | h_dim proved in #2351; iso remains |
| #2334 | Prove etilde6v2Rep_isIndecomposable | Statement fixed in #2342 |
| #2335 | Prove etilde7Rep_isIndecomposable | WIP in PR #2367 |
| #2336 | Prove t125Rep_isIndecomposable | Unclaimed |
| #2341 | Fix etilde6v2Rep_isIndecomposable statement | Done in #2342, needs close |
| #2344 | Prove T(1,2,3)/T(1,3,2)=E₇ posdef | WIP in PR #2354 |
| #2346 | Prove D-type leaf posdef | Unclaimed |
| #2347 | Build D̃_n infrastructure | Done in #2358, needs close |

## Dependency Clusters

### Cluster A: Polytabloid/Straightening (Ch5, 2 sorries) — SHRINKING
**Files:** SpechtModuleBasis (1), FormalCharacterIso (1)
**Key sorries:**
- `garnir_twisted_in_lower_span` — combinatorial heart of straightening (difficulty 8)
- `iso_of_formalCharacter_eq_schurPoly` — GL_N complete reducibility (difficulty 8)
**Status:** Down 4→2 since wave 51 (twistedPolytabloid_col_eq and h_dim proved).
Proposition5_22_2.lean is now sorry-free. Both remaining sorries are genuinely hard.

### Cluster B: Infinite Type Classification (Ch6, 13 sorries) — SHRINKING
**Files:** InfiniteTypeConstructions (13)
**Sub-clusters:**
- **B1: Indecomposability (4)**: dTilde (new), etilde6v2, etilde7, t125. All difficulty 8.
  WIP structural framework for etilde7 in PR #2367.
- **B2: ADE posdef (4)**: T(1,4,2), T(1,3,2), T(1,2,4), T(1,2,3). All E₆/E₇ type.
  PRs #2354/#2355 address all 4.
- **B3: D-type leaf posdef (2)**: a₃ leaf, a₂ leaf. Graph reduction to path + pendant.
  Issue #2362 claimed.
- **B4: tree_two_leaf_posdef (2)**: h_bound, h_strict. Graph reduction via Fin.succAbove.
  Issue #2361 claimed (partial PR #2370 merged).
- **B5: non_adjacent_branches leaf_case (1)**: Subgraph embedding.
  Issue #2363 claimed.
**Status:** Down 15→13. Significant structural progress: E₈ cases eliminated,
T(1,2,2) proved, leaf cases consolidated, tree_two_leaf_posdef partially proved.
3 open PRs with passing CI could further reduce to 9 or fewer.

### Cluster C: Morita Theory (Ch9) — CLOSED (wave 50)
**Status:** Complete.

### Cluster D: Gabriel's Theorem (Ch2, 2 sorries) — UNCHANGED
**Status:** Both bridges remain. Forward bridge blocked on Cluster B completion +
∀k∀Q refactor. Backward bridge needs positive root enumeration.

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
| 50 | 13 | 5 | 581/583 (99.7%) | 2026-04-13 |
| 51 | 21 | 5 | 582/583 (99.8%) | 2026-04-17 |
| **52** | **17** | **4** | **582/583 (99.8%)** | **2026-04-17** |

**Wave 52 trend:** First net decrease in sorry count since wave 48. The
decomposition-then-close cycle is working: wave 51 decomposed large sorries into
small ones, wave 52 closed several of them. Files with sorries dropped 5→4
(Proposition5_22_2 cleared).

## Honest Assessment

The project remains in the **endgame phase**, with the decomposition-dominant
period giving way to individual sorry closures.

**Strengths:**
1. **First net sorry decrease in 4 waves.** 21→17 after waves of increasing counts
   from decomposition. The strategy of decompose-then-close is bearing fruit.
2. **One file cleared.** Proposition5_22_2.lean is now sorry-free (h_dim proved).
3. **3 soundness bugs found and fixed.** The wave's most valuable contribution may be
   catching false statements (etilde6v2 for m=0, tree_two_leaf_posdef without h_deg_le2,
   T(1,5,2)/T(1,2,5) being Ẽ₈ not E₈). Each could have led to hours of futile proving.
4. **3 open PRs with passing CI.** If merged, would close 4 more sorries.
5. **All remaining Ch6 sorries are independent.** High parallelizability.

**Concerns:**
1. **4 indecomposability sorries remain the hardest cluster.** Each requires proving
   that specific quiver representations have no nontrivial idempotent endomorphisms.
   No single proof has been completed yet (etilde7 WIP in #2367 is structural only).
   The dTildeRep_isIndecomposable sorry was added this wave.
2. **Cluster A (Ch5) sorries are both difficulty 8.** garnir_twisted_in_lower_span and
   iso_of_formalCharacter_eq_schurPoly have had no progress since wave 50.
3. **Gabriel's Theorem bridges (#2255, #2256) still unclaimed.** These are the
   final link between Chapter 6 (infinite type constructions) and Chapter 2
   (Gabriel's theorem statement). Both require substantial bridging infrastructure.
4. **10 replan issues need cleanup.** Several are done (#2341, #2347) or partially
   done and need new plans reflecting current state.

**If all 3 open PRs merge + 3 claimed issues complete:**
- Sorries would drop to ~8-10 (4 indecomposability + 2 Ch5 + 2 Ch2)
- All posdef/leaf-case sorries would be closed
- Remaining work would be concentrated on the genuinely hard problems

**Most tractable targets:**
1. **4× ADE posdef** (PRs #2354/#2355 ready to merge) — difficulty 3-5
2. **2× D-type leaf posdef** (#2362 claimed) — graph reduction, difficulty 5
3. **1× non_adjacent_branches leaf_case** (#2363 claimed) — subgraph embedding, difficulty 5
4. **2× tree_two_leaf_posdef** (#2361 claimed) — Fin.succAbove reduction, difficulty 6

**Hard targets:**
5. **4× indecomposability** (dTilde, etilde6v2, etilde7, t125) — difficulty 8
6. **garnir_twisted_in_lower_span** — combinatorial, difficulty 8
7. **iso_of_formalCharacter_eq_schurPoly** — Schur-Weyl, difficulty 8
8. **2× Theorem_2_1_2 bridges** (#2255, #2256) — bridging + infrastructure, difficulty 8-9

## Strategic Recommendations

1. **Merge the 3 open PRs.** All have passing CI. This would immediately close
   4 sorries and reduce the ADE posdef cluster to 0.

2. **Clean up replan issues.** Close #2341 (done), #2347 (done), and update
   #2325, #2331, #2332, #2335, #2344 to reflect current state.

3. **Prioritize the posdef/leaf closures.** Issues #2361, #2362, #2363 together
   would clear 5 sorries (h_bound, h_strict, D-type a₃, D-type a₂, leaf_case).
   These are all difficulty 5-6 and parallelizable.

4. **Consider a unified approach for indecomposability.** The null root method
   (showing the adjacency matrix has a null eigenvector whose components are all
   nonzero) might work for all 4 indecomposability sorries with a shared helper.
   This was suggested in the wave 49 meditate (#2366) but hasn't been explored.

5. **Start the Theorem_2_1_2 bridges.** The forward bridge (#2255) needs the
   ∀k∀Q refactor of InfiniteTypeConstructions. The field-generic infrastructure
   in FieldGenericInfiniteType.lean (#2328) is a start. This work is independent
   of the remaining posdef closures.
