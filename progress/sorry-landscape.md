# Sorry Landscape Analysis — Wave 53

Generated 2026-04-17 by summarize session (issue #2393).

## Summary

**13 sorries** across 4 files (down from 17/4 in wave 52). The sorry count
decreased by 4, driven by 9 genuine closures (all posdef + leaf_case) offset
by 5 additions (etilde7 expanded 1→4 sub-sorries, 2 path infrastructure
sorries now visible after leaf_case closure).

281 of 285 Lean files (98.6%) are sorry-free. 582/583 items (99.8%) sorry-free.

**Definition-level sorries: 0.** All mathematical objects are constructed.

### Merges since wave 52 (14 PRs, 2026-04-17):

| PR | Date | Title | Sorry Impact |
|----|------|-------|-------------|
| #2371 | 04-17 | doc: update sorry landscape (Wave 52, 21→17 sorries) | Docs only |
| #2367 | 04-17 | feat: WIP etilde7Rep_isIndecomposable - structural framework | etilde7 1→4 sub-sorries (structural expansion) |
| #2355 | 04-17 | feat: fill E₇ posdef sorry sites and delete mk_e8_distinct | −2 (T(1,4,2) and T(1,2,4) closed) |
| #2354 | 04-17 | feat: WIP e7_tree_posdef + apply at T(1,3,2)/T(1,2,3) sorries | −2 (T(1,3,2) and T(1,2,3) closed) |
| #2376 | 04-17 | fix: add 1≤m to etilde7/t125 indecomposability (m=0 is decomposable) | Soundness fix |
| #2381 | 04-17 | feat: prove tree_embed_adj_eq + scaffold leaf_case D̃ embedding | Infra |
| #2382 | 04-17 | feat: prove tree_embed_adj_eq + scaffold leaf_case for D̃ embedding | Infra |
| #2385 | 04-17 | feat: fill tree_two_leaf_posdef sorry sites | −2 (h_bound and h_strict closed) |
| #2386 | 04-17 | feat: fill e7_tree_posdef sorry (E₇ QF positive definite) | Infra (helper used by #2354/#2355) |
| #2387 | 04-17 | feat: fill D-type leaf posdef sorries (closes #2383) | −2 (D-type a₃ and a₂ leaf closed) |
| #2390 | 04-17 | feat: replace Garnir set with proper cross-column set | Structural fix (enables garnir_twisted proof) |
| #2391 | 04-17 | fix: reverse Ẽ₆ edge 3→4 to 4→3 (injective orientation) | Soundness fix (etilde6v2 now provable) |
| #2392 | 04-17 | Meditate wave 49: endgame strategy review | Strategic review |
| #2396 | 04-17 | feat: fill non_adjacent_branches leaf_case sorry (D̃ subgraph embedding) | −1 (leaf_case closed) |

**Net:**
- Genuine closures: 9 (ADE posdef ×4, D-type leaf ×2, tree_two_leaf ×2, leaf_case ×1)
- Structural expansion: +3 (etilde7 1→4 sub-sorries via PR #2367)
- Newly visible: +2 (walk_to_nodup_path, dTilde_nodup_path_between — were dependencies of leaf_case)
- Raw count change: 17 → 13 (−4)
- Files with sorries: 4 → 4 (unchanged)

**Soundness fixes in this wave:**
- PR #2376 added `1 ≤ m` hypothesis to `etilde7Rep_isIndecomposable` and
  `t125Rep_isIndecomposable` (both false for m=0 — representation is decomposable)
- PR #2391 reversed Ẽ₆ edge 3→4 to 4→3 (surjective map lost information, making
  etilde6v2Rep decomposable for all m ≥ 1; injective orientation fixes this)

**Structural fixes:**
- PR #2390 replaced Garnir set `{p₁, p₂}` with proper cross-column set (old set
  only supported same-row swaps, making `garnir_twisted_in_lower_span` unprovable)

## Chapter Breakdown

| Chapter | Sorries | Files | Delta from Wave 52 |
|---------|---------|-------|---------------------|
| Ch2 | 2 | 1 | 0 |
| Ch5 | 2 | 2 | 0 |
| Ch6 | 9 | 1 | −4 (net: posdef/leaf ×9 closed; etilde7 +3, path infra +2) |
| Ch9 | 0 | 0 | 0 |

## Per-File Sorry Detail

### InfiniteTypeConstructions (Ch6) — 9 sorries

**Indecomposability — dTilde (1):**
- Line 2177 — `dTildeRep_isIndecomposable` (D̃_n arbitrary path-length)
  Issue #2384 (path infrastructure) is a prerequisite.

**Indecomposability — Ẽ₆ (1):**
- Line 2332 — `etilde6v2Rep_isIndecomposable` (Ẽ₆ mixed orientation, m ≥ 1)
  Issue #2379 claimed. Edge orientation fixed in #2391.

**Indecomposability — Ẽ₇ sub-sorries (4):**
- Line 2748 — N-invariance of W₁(4) under nilpotentShiftLin
- Line 2751 — N-invariance of W₂(4) under nilpotentShiftLin
- Line 2785 — Center-is-bot: W(0) = ⊥ (key mathematical challenge, uses m ≥ 1)
- Line 2792 — Propagation: W(0) = ⊥ → all W(v) = ⊥ via injectivity

  Issue #2394 claimed. Structural framework from PR #2367 merged.
  The center-is-bot sorry (line 2785) is the hardest sub-goal.

**Indecomposability — T(1,2,5) (1):**
- Line 3008 — `t125Rep_isIndecomposable` (T(1,2,5), m ≥ 1)
  Issue #2395 unclaimed. Same pattern as Ẽ₇ but with 9 vertices.

**Path infrastructure (2):**
- Line 7968 — `dTilde_nodup_path_between` (explicit D̃ path construction)
- Line 7990 — `walk_to_nodup_path` (trim walk to simple path via acyclicity)

  Issue #2384 claimed. These were dependencies of leaf_case; now the remaining
  sorries after leaf_case was closed by #2396.

### SpechtModuleBasis (Ch5) — 1 sorry
- Line 670 — `garnir_twisted_in_lower_span` (combinatorial heart, difficulty 8)
  Issue #2380 unclaimed. Cross-column Garnir set now in place (#2390).

### FormalCharacterIso (Ch5) — 1 sorry
- Line 221 — `iso_of_formalCharacter_eq_schurPoly` (GL_N complete reducibility / Schur-Weyl, difficulty 8)
  No active issue. Identified as Mathlib gap by meditate wave 49.

### Theorem2_1_2 (Ch2) — 2 sorries (unchanged since wave 43)
- Line 171 — Forward bridge: `not_posdef_not_HasFiniteRepresentationType`
  (needs per-field ∀k∀Q quantifier refactor of InfiniteTypeConstructions)
- Line 210 — Backward bridge: `isDynkinDiagram_HasFiniteRepresentationType`
  (needs positive root enumeration + Iso bridge to Chapter 2 setup)

## Open PRs

None. All 3 PRs from wave 52 (#2354, #2355, #2367) have merged.

## Active Issues

| Issue | Title | Status |
|-------|-------|--------|
| #2379 | Prove etilde6v2Rep_isIndecomposable (Ẽ₆, m≥1) | Claimed |
| #2384 | Prove walk_to_nodup_path + dTilde_nodup_path_between | Claimed |
| #2393 | Update sorry landscape (Wave 53) | Claimed (this session) |
| #2394 | Prove etilde7Rep_isIndecomposable sub-sorries | Claimed |

## Unclaimed Issues

| Issue | Title | Impact |
|-------|-------|--------|
| #2255 | Prove positive definiteness in Theorem_2_1_2 forward direction | 1→0 sorry (Ch2), difficulty 8 |
| #2256 | Prove Theorem_2_1_2 backward direction (Dynkin → finite rep type) | 1→0 sorry (Ch2), difficulty 9 |
| #2380 | Prove garnir_twisted_in_lower_span (Ch5 straightening heart) | 1→0 sorry (Ch5), difficulty 8 |
| #2395 | Prove t125Rep_isIndecomposable (T(1,2,5), m≥1) | 1→0 sorry (Ch6), difficulty 8 |

## Dependency Clusters

### Cluster A: Polytabloid/Straightening (Ch5, 2 sorries) — STALLED
**Files:** SpechtModuleBasis (1), FormalCharacterIso (1)
**Key sorries:**
- `garnir_twisted_in_lower_span` — cross-column Garnir set now available (#2390), but proof not attempted
- `iso_of_formalCharacter_eq_schurPoly` — identified as Mathlib gap (Schur-Weyl duality)
**Status:** Unchanged since wave 50. Both are difficulty 8. The Garnir set structural
fix (#2390) unblocks `garnir_twisted_in_lower_span` in principle.

### Cluster B: Infinite Type Classification (Ch6, 9 sorries) — RAPIDLY SHRINKING
**Files:** InfiniteTypeConstructions (9)
**Sub-clusters:**
- **B1: Indecomposability (6+1)**: 4 theorems with 6 sorry sites total (dTilde 1, etilde6v2 1,
  etilde7 4, t125 1). Plus 2 path infrastructure sorries that support dTilde.
  etilde6v2 has edge orientation fix (#2391). etilde7 has structural framework (#2367).
  t125 follows the same pattern as etilde7.
- **B2–B5: posdef/leaf-case: ALL CLOSED.** This is the major achievement of wave 53.
  - ADE posdef: closed by #2354/#2355
  - D-type leaf posdef: closed by #2387
  - tree_two_leaf_posdef: closed by #2385
  - non_adjacent_branches leaf_case: closed by #2396

### Cluster C: Morita Theory (Ch9) — CLOSED (wave 50)

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
| 52 | 17 | 4 | 582/583 (99.8%) | 2026-04-17 |
| **53** | **13** | **4** | **582/583 (99.8%)** | **2026-04-17** |

**Wave 53 trend:** Second consecutive net decrease (17→13). The posdef/leaf-case
sorry category is now **completely eliminated** — all 9 posdef and embedding sorries
from wave 52 are closed. The remaining 13 sorries are concentrated in the hardest
problems: indecomposability proofs (7), path infrastructure (2), Ch5 combinatorics (2),
and Ch2 bridges (2).

## Honest Assessment

The project has completed its **tractable sorry elimination phase**. All posdef,
leaf-case, and graph embedding sorries are closed. What remains is exclusively
hard problems (difficulty 8+).

**Strengths:**
1. **All posdef/leaf-case sorries eliminated.** Wave 53 closed 9 of 13 Ch6 sorries
   from wave 52. Sub-clusters B2–B5 are fully resolved.
2. **Consecutive sorry decreases.** Waves 52-53 show 21→17→13, confirming the
   decompose-then-close strategy is working.
3. **Soundness improving.** Two more statement fixes this wave (etilde7/t125 for
   m=0, Ẽ₆ edge orientation). Each fix prevents hours of futile proof attempts.
4. **Structural fixes for Ch5.** The Garnir set replacement (#2390) makes
   `garnir_twisted_in_lower_span` provable in principle for the first time.
5. **4 issues actively claimed.** etilde6v2 (#2379), etilde7 (#2394), path infra
   (#2384), and this summarize session (#2393).

**Concerns:**
1. **All remaining sorries are difficulty 8+.** The tractable work is done. Every
   remaining sorry requires either deep algebraic reasoning (indecomposability),
   hard combinatorics (Garnir), Mathlib gaps (Schur-Weyl), or bridging infrastructure
   (Ch2). There are no more "easy wins."
2. **No indecomposability proof has been completed yet.** Despite structural progress
   (etilde7 framework, dTilde infrastructure, soundness fixes), no single
   `*_isIndecomposable` theorem has been proved. This is the critical path.
3. **Cluster A stalled for 5 waves.** `garnir_twisted_in_lower_span` and
   `iso_of_formalCharacter_eq_schurPoly` have had no proof progress since wave 48,
   though the Garnir set structural fix may now unblock the former.
4. **Gabriel's Theorem bridges still unclaimed.** #2255 and #2256 need substantial
   infrastructure work that is independent of Cluster B.
5. **Etilde7 has the most sub-sorries (4).** The center-is-bot sorry is identified
   as the key mathematical challenge, requiring m ≥ 1 nilpotent coupling argument.

**Current priority ordering:**
1. **Indecomposability proofs** (7 sorries across 4 theorems) — critical path for Cluster B
2. **Path infrastructure** (2 sorries) — prerequisite for dTilde indecomposability
3. **garnir_twisted_in_lower_span** (1 sorry) — newly unblocked by Garnir set fix
4. **Gabriel's Theorem bridges** (2 sorries) — independent work, can proceed in parallel
5. **iso_of_formalCharacter_eq_schurPoly** (1 sorry) — Mathlib gap, hardest remaining sorry

**If all claimed issues complete:**
- etilde6v2 (#2379): −1 sorry
- etilde7 (#2394): −4 sorries
- path infra (#2384): −2 sorries
- Total: 13 → 6 (dTilde 1, t125 1, Ch5 2, Ch2 2)
