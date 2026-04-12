# Sorry Landscape Analysis — Wave 49

Generated 2026-04-12 by summarize session (issue #2273).

## Summary

**10 sorries** across 6 files (up from 8/6 in wave 48). Chapters 3, 4, 7, 8 remain 100% sorry-free.

278 of 284 Lean files (97.9%) are sorry-free. 581/583 items (99.7%) sorry-free.

**Definition-level sorries: 0.** All mathematical objects are constructed.

**Why sorries went UP 8→10:** Wave 48 counted only "primary" sorries. PRs #2257 (Theorem_2_1_2 decomposition, 1→2), #2252 (InfiniteTypeConstructions restructure, 0→4) deliberately decomposed monolithic sorries into sub-problems. Net: 3 old sorries were closed (Problem6_1_5_theorem, Corollary6_8_4, PolytabloidBasis×3) while 5 structural sub-sorries were introduced. The decomposition makes each sorry independently attackable.

### Merges since wave 48 (17 PRs, 2026-04-11 to 2026-04-12):

| PR | Date | Title | Sorry Impact |
|----|------|-------|-------------|
| #2237 | 04-11 | Equivariant injection V_λ → M^λ (tabloid projection) | Infrastructure |
| #2240 | 04-11 | Fix CI workflow for OOM | CI fix |
| #2241 | 04-11 | Review session: merged 6 PRs, fixed CI | Review |
| #2242 | 04-11 | Progress file for #2212 analysis | Documentation |
| #2243 | 04-11 | Generalized polytabloidTab infrastructure | Infrastructure |
| #2244 | 04-11 | Proof skeleton for head_isomorphism | MoritaStructural infra |
| #2248 | 04-11 | dim V_λ ≥ |SYT(λ)| via tabloidProjection bridge | Polytabloid infra |
| #2250 | 04-11 | Break circular import, restructure Theorem_6_1_5 | Refactoring |
| #2251 | 04-12 | Proof skeleton for head_isomorphism | MoritaStructural infra |
| #2252 | 04-12 | Ẽ₇/T(1,2,5) infinite type + close Problem6_1_5_theorem | **Problem6_1_5 1→0**, InfiniteTypeConstructions +4 |
| #2254 | 04-12 | Restructure dim V_λ = |SYT(λ)|, remove 3 sorries | **PolytabloidBasis 3→0** |
| #2257 | 04-12 | Theorem_2_1_2 infrastructure and forward direction | Theorem2_1_2 1→2 (decomposed) |
| #2259 | 04-12 | Prove iso_of_glWeightSpace_finrank_eq | **FormalCharacterIso stays 1** (different sorry) |
| #2264 | 04-12 | Consolidate MoritaStructural 2→1 | MoritaStructural 2→1 |
| #2267 | 04-12 | Decompose straightening theorem 1→2, prove induction skeleton | SpechtModuleBasis new sorry |
| #2268 | 04-12 | Replace broken etilde6Rep with etilde6v2Rep | InfiniteTypeConstructions fix |
| #2269 | 04-12 | Prove exists_column_standard_mul | Straightening infrastructure |

**Net: 5 old sorries closed, 7 decomposition sorries introduced. Files with sorries: 6→6 (different set).**

### Files that became sorry-free since wave 48:
- **Problem6_1_5_theorem** (Ch6) — closed by PR #2252 (Ẽ₇/T(1,2,5) infinite type proofs)
- **Corollary6_8_4** (Ch6) — previously had 1 sorry, now 0
- **PolytabloidBasis** (Ch5) — 3→0 via restructuring into SpechtModuleBasis (#2254)

### Files that gained sorries since wave 48:
- **InfiniteTypeConstructions** (Ch6) — 0→4 (indecomposability proofs + graph classification)
- **Theorem2_1_2** (Ch2) — 1→2 (decomposed into forward/backward directions)
- **SpechtModuleBasis** (Ch5) — new file, 1 sorry (straightening)

## Chapter Breakdown

| Chapter | Sorries | Files | Delta from Wave 48 |
|---------|---------|-------|---------------------|
| Ch2 | 2 | 1 | +1 (decomposed) |
| Ch5 | 3 | 3 | −1 (PolytabloidBasis 3→0, new: SpechtModuleBasis+Proposition5_22_2) |
| Ch6 | 4 | 1 | +2 (InfiniteTypeConstructions new; Problem6_1_5+Corollary6_8_4 closed) |
| Ch9 | 1 | 1 | 0 |

## Per-File Sorry Detail

| File | Sorries | Theorems | Delta |
|------|---------|----------|-------|
| InfiniteTypeConstructions (Ch6) | 4 | `etilde6v2Rep_isIndecomposable` (line 2097), `etilde7Rep_isIndecomposable` (line 2272), `t125Rep_isIndecomposable` (line 2407), `non_ade_graph_not_finite_type` (line 2477) | **new** |
| Theorem2_1_2 (Ch2) | 2 | Forward direction: finite rep type → positive definite (line 156), Backward: Dynkin → finite rep type (line 162) | **+1** |
| MoritaStructural (Ch9) | 1 | `head_isomorphism`: progenerator lift surjectivity (line 530) | 0 |
| SpechtModuleBasis (Ch5) | 1 | `polytabloidTab_column_standard_in_span`: Garnir straightening (line 311) | **new** |
| Proposition5_22_2 (Ch5) | 1 | `h_dim`: dimension equality for det-twisted Schur module (line 297) | **new** |
| FormalCharacterIso (Ch5) | 1 | `iso_of_glWeightSpace_finrank_eq` (line 116, GL_N complete reducibility) | 0 |

## Open PRs (2)

| PR | Title | CI Status | Mergeable |
|----|-------|-----------|-----------|
| #2272 | Decompose straightening theorem sorry 1→2, prove induction skeleton | SUCCESS | Yes |
| #2278 | Decompose non_ade_graph_not_finite_type, prove degree ≥ 4 and triangle cases | PENDING | Yes |

**Note:** PR #2272 is ready to merge (CI passing). PR #2278 CI still running.

## Blocked Issues (5)

| Issue | Blocked on | Title |
|-------|-----------|-------|
| #2271 | PR #2272 | Prove garnir_straightening_step |
| #2270 | PR #2272 | Prove eq_of_rowStandard_of_toTabloid_eq |
| #2256 | Theorem2_1_2 chain | Prove backward direction (Dynkin → finite rep type) |
| #2255 | Theorem2_1_2 chain | Prove positive definiteness in forward direction |
| #1571 | — | Reconcile repo with FormalFrontier templates (stale) |

## Claimed Work Items

| Issue | Title | Status |
|-------|-------|--------|
| #2273 | Update sorry landscape wave 49 | Claimed (this session) |
| #2263 | Prove iso_of_formalCharacter + Proposition5_22_2 h_dim | Claimed |

## Unclaimed Work Items

| Issue | Title | Impact |
|-------|-------|--------|
| #2247 | Prove Theorem_2_1_2 (Gabriel's theorem) | 2→0 sorry, difficulty 9 |
| #2274 | Meditate wave 48: endgame strategy review | Strategic |
| #2276 | Prove MoritaStructural head_isomorphism | 1→0 sorry, difficulty 6 |
| #2277 | Prove not_posdef_infinite_type (graph classification) | 1→0 sorry, difficulty 7 |

## Dependency Clusters

### Cluster A: Polytabloid/Straightening (Ch5, 3 sorries)
**Files:** SpechtModuleBasis (1), Proposition5_22_2 (1), FormalCharacterIso (1)
**Key sorries:**
- `polytabloidTab_column_standard_in_span` — Garnir straightening (SpechtModuleBasis line 311). PR #2272 ready to merge; blocked issues #2270/#2271 provide sub-steps.
- `h_dim` in Proposition5_22_2 — dimension equality for det-twisted Schur module (#2263, claimed)
- `iso_of_glWeightSpace_finrank_eq` — GL_N complete reducibility (FormalCharacterIso, difficulty 8)
**Status:** Down from 4→3 since wave 48. PolytabloidBasis cleared. Straightening decomposed into independently-attackable pieces. #2263 (claimed) targets Proposition5_22_2.
**Critical path:** PR #2272 merges → #2270/#2271 unblock → straightening sorry closes. #2263 addresses h_dim independently.

### Cluster B: Infinite Type Classification (Ch6, 4 sorries)
**Files:** InfiniteTypeConstructions (4)
**Key sorries:**
- 3× `*_isIndecomposable`: etilde6v2, etilde7, t125 (representation indecomposability proofs)
- 1× `non_ade_graph_not_finite_type`: graph classification case analysis
**Status:** New cluster. Problem6_1_5_theorem is now sorry-free. The remaining sorries are the representation-theoretic indecomposability proofs and the pure graph theory case analysis. PR #2278 in flight for the graph classification decomposition.
**Critical path:** #2277 (unclaimed) addresses graph classification. Indecomposability proofs are independent.

### Cluster C: Morita Theory (Ch9, 1 sorry)
**Files:** MoritaStructural (1)
**Remaining:** head_isomorphism (k-linear Hom adjunction)
**Status:** Consolidated from 2→1 sorry (PR #2264). Issue #2276 (unclaimed, difficulty 6, ~100 lines) provides clear 3-step plan.

### Cluster D: Gabriel's Theorem (Ch2, 2 sorries)
**Files:** Theorem2_1_2 (2)
**Key sorries:** Forward direction (positive definiteness from finite type) and backward direction (Dynkin → finite rep type)
**Status:** Decomposed from 1→2 (PR #2257). Top-level result depending on Clusters B (non-ADE → infinite type) and classification infrastructure. Issues #2255, #2256 blocked on chain completion.

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
| **49** | **10** | **6** | **581/583 (99.7%)** | **2026-04-12** |

**Note on wave 49 increase:** The raw sorry count increased because monolithic sorries were deliberately decomposed into sub-problems. The "effective difficulty" decreased — each sorry is now smaller and independently attackable. 5 old sorries were genuinely closed; 7 smaller ones introduced.

## Honest Assessment

The project is in the endgame with a **decomposition strategy** actively running. The 10→10 sorry count masks real progress: Problem6_1_5_theorem (major theorem), Corollary6_8_4 (entire file), and PolytabloidBasis (3 sorries) were all closed. The CI infrastructure issues from wave 48 are resolved (6 blocked PRs all merged).

**Most tractable targets (by difficulty):**
1. `head_isomorphism` (#2276, unclaimed, difficulty 6) — Clear 3-step plan, ~100 lines
2. `polytabloidTab_column_standard_in_span` — PR #2272 ready to merge, unblocks sub-steps
3. `non_ade_graph_not_finite_type` (#2277, unclaimed, difficulty 7) — Pure graph theory, PR #2278 in flight
4. `h_dim` in Proposition5_22_2 (#2263, claimed) — Dimension equality

**Hard targets:**
5. `*_isIndecomposable` ×3 — Require nilpotent invariant complement arguments for each family
6. `iso_of_glWeightSpace_finrank_eq` — GL_N complete reducibility, difficulty 8
7. Theorem2_1_2 forward/backward — Top-level, depends on other clusters

**CI is healthy** — all 6 previously-blocked PRs merged. PR #2272 ready to merge now.

## Strategic Recommendations

1. **Merge PR #2272 immediately** — CI passing, unblocks straightening sub-issues #2270/#2271.

2. **Prioritize #2276 (head_isomorphism)** — Lowest difficulty (6), clear plan, closes Ch9 entirely. Only 1 sorry in all of Ch9.

3. **#2277 (graph classification)** — Pure combinatorics, independent of all other clusters. PR #2278 already attacking it.

4. **Indecomposability proofs** (etilde6v2, etilde7, t125) — These are the "irreducible core" that may be hardest. Each requires constructing a proof that the representation cannot decompose. Consider whether these can be done by explicit matrix computation (e.g., `native_decide` or `norm_num` for small cases, then generalization).

5. **Accept some long-term sorries** — FormalCharacterIso and the 3 indecomposability proofs may represent genuinely hard formalization work that could be deferred.
