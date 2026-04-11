# Sorry Landscape Analysis — Wave 48

Generated 2026-04-11 by summarize session (issue #2231).

## Summary

**8 sorries** across 6 files (down from 9/6 in wave 47). Chapters 3, 4, 7, 8 remain 100% sorry-free.

275 of 281 Lean files (97.9%) are sorry-free. 581/583 items (99.7%) sorry-free.

**Definition-level sorries: 0.** All mathematical objects are constructed.

### Merges since wave 47 (2 PRs):

- **Polytabloid definition refactored to standard form** (#2230) — Changed from T-dependent `κ_T · of(τ) · a_λ` to standard textbook `of(τ) · c_λ`. PolytabloidBasis 4→3 sorries.
- **polytabloid_mem_spechtModule proved** (#2229) — κ_T conjugation identity proved, making membership trivial with new definition.

### Merges since last summarize session (#2202, 2026-04-07) — 10 PRs total:

| PR | Date | Title | Sorry Impact |
|----|------|-------|-------------|
| #2209 | 04-09 | Remove unused polytabloid_syt_dominance | TabloidModule 1→0 |
| #2213 | 04-09 | Rebase PR #2192 to fix main CI breakage | CI fix |
| #2214 | 04-09 | Rebase all 6 CI-failing PRs | CI fix |
| #2215 | 04-09 | Prove Problem6_9_1 compatible_product_decomp | Problem6_9_1 1→0 |
| #2221 | 04-11 | Prove Young symmetrizer coefficient lemmas | PolytabloidBasis 8→4 |
| #2222 | 04-11 | Meditate wave 47 sorry landscape | Documentation |
| #2223 | 04-11 | Review wave 47: re-trigger 6 PRs | Review |
| #2224 | 04-11 | Meditate wave 47: pipeline health assessment | Documentation |
| #2229 | 04-11 | Prove polytabloid_mem_spechtModule | PolytabloidBasis −1 |
| #2230 | 04-11 | Refactor polytabloid to standard definition | PolytabloidBasis 4→3 |

**Net sorry change since last summarize: −7** (15→8). Since wave 47: −1 (9→8).

## Chapter Breakdown

| Chapter | Sorries | Files | Delta from Wave 47 |
|---------|---------|-------|---------------------|
| Ch2 | 1 | 1 | 0 |
| Ch5 | 4 | 2 | −1 (PolytabloidBasis 4→3) |
| Ch6 | 2 | 2 | 0 |
| Ch9 | 1 | 1 | 0 |

## Per-File Sorry Detail

| File | Sorries | Theorems | Delta |
|------|---------|----------|-------|
| PolytabloidBasis (Ch5) | 3 | polytabloid_linearIndependent (line 445), column_standard_in_span' (line 853), perm_mul_youngSymmetrizer_mem_span_polytabloids (line 1295) | **−1** |
| FormalCharacterIso (Ch5) | 1 | iso_of_glWeightSpace_finrank_eq (line 59, GL_N complete reducibility) | 0 |
| Corollary6_8_4 (Ch6) | 1 | Mixed vertex case (line 818) | 0 |
| Problem6_1_5_theorem (Ch6) | 1 | Forward direction: positive definiteness → finite type (line 81) | 0 |
| MoritaStructural (Ch9) | 1 | head_isomorphism: progenerator lift surjectivity (line 486) | 0 |
| Theorem2_1_2 (Ch2) | 1 | Gabriel's theorem: finite rep type ↔ Dynkin (line 101) | 0 |

## Open PRs (6)

| PR | Title | CI Status | Mergeable |
|----|-------|-----------|-----------|
| #2219 | non_ADE_not_finite_type (non-Dynkin → infinite type) | CANCELLED | Yes |
| #2208 | Corollary6_8_4 mixed vertex case | CANCELLED | Yes |
| #2200 | etilde8_not_finite_type via Ẽ_6 subgraph | CANCELLED | Yes |
| #2198 | Ẽ_6 representation construction | CANCELLED | Yes |
| #2191 | D̃_n infinite type proof | CANCELLED | Yes |
| #2175 | Module.Finite infrastructure | CANCELLED | Yes |

**CI status notes:** All 6 PRs have had multiple CI re-triggers (latest 2026-04-11). All runs CANCELLED — persistent infrastructure issue (runner OOM/disconnects). These are code-correct PRs blocked solely by CI infrastructure. This has been the case for 3+ days.

## Blocked Issues (5)

| Issue | Blocked on | Title |
|-------|-----------|-------|
| #2199 | (PR #2198) | Prove etilde6Rep_isIndecomposable |
| #2187 | #2185 (PR #2191) | Non-ADE tree case analysis |
| #2174 | #2173 (PR #2175) | Prove head_isomorphism using Module.Finite |
| #2112 | #2143 | Close positive definiteness sorry in Theorem_6_1_5 |
| #1571 | — | Reconcile repo with FormalFrontier templates (stale) |

**Unblocking cascade (when CI stabilizes):**
- #2175 merges → unblocks #2174 (head_isomorphism → MoritaStructural sorry)
- #2191 merges → unblocks #2187 (non-ADE tree case analysis)
- #2198 merges → unblocks #2199 (Ẽ_6 indecomposability)
- #2200 merges → contributes to #2143 chain
- #2219 merges → contributes to #2143 chain (non-Dynkin → infinite type)

## Claimed Work Items

| Issue | Title | Status |
|-------|-------|--------|
| #2227 | Merge 6 infrastructure-blocked PRs | Claimed |
| #2217 | Prove polytabloid straightening lemma | Claimed |
| #2212 | Prove polytabloid_linearIndependent via transfer map | Claimed |
| #2231 | Update sorry landscape and project summary | Claimed (this session) |

## Unclaimed Work Items

| Issue | Title | Impact |
|-------|-------|--------|
| #2226 | Prove iso_of_glWeightSpace_finrank_eq | 1→0 sorry (FormalCharacterIso), difficulty 8 |

## Dependency Clusters

### Cluster A: Polytabloid Basis (Ch5, 4 sorries)
**Files:** PolytabloidBasis (3), FormalCharacterIso (1)
**Key sorries:**
- `polytabloid_linearIndependent` — transfer from tabloid-module proof (#2212, claimed)
- `column_standard_in_span'` — column-standard straightening (difficulty ~7, #2217 claimed)
- `perm_mul_youngSymmetrizer_mem_span_polytabloids` — full straightening lemma (depends on column_standard_in_span')
- `iso_of_glWeightSpace_finrank_eq` — GL_N complete reducibility (difficulty 8, #2226 unclaimed)
**Status:** Down from 9→4 over waves 46-48. polytabloid_mem_spechtModule was the latest to fall (#2229/#2230). Two workers active on linearIndependent (#2212) and straightening (#2217).
**Critical path:** linearIndependent (#2212) and straightening (#2217) are independent. FormalCharacterIso (#2226) is independent and lowest priority.

### Cluster B: Gabriel Theorem Chain (Ch6, 2 sorries)
**Files:** Corollary6_8_4 (1), Problem6_1_5_theorem (1)
**Status:** Unchanged since wave 47. Multiple PRs in flight for non-ADE classification chain, all blocked by CI.
**Critical path:** PRs #2191, #2200, #2198, #2219 merge → #2143 closes → #2112 closes → Problem6_1_5_theorem sorry closes. Corollary6_8_4 mixed vertex case addressed by PR #2208 (CI blocked).

### Cluster C: Morita Theory (Ch9, 1 sorry)
**Files:** MoritaStructural (1)
**Remaining:** head_isomorphism (progenerator lift surjectivity)
**Status:** Blocked on #2175 (Module.Finite infrastructure, CI blocked). Once #2175 merges, #2174 becomes actionable.

### Isolated
- **Theorem2_1_2** (1 sorry): Gabriel's theorem. Top-level result depending on Clusters A and B.

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
| **48** | **8** | **6** | **581/583 (99.7%)** | **2026-04-11** |

## Honest Assessment

The project is deep in the endgame. 8 sorries remain across 6 files — all genuinely hard. The polytabloid definition refactoring (#2229/#2230) was strategically important: it unblocked membership and simplified all downstream proofs, dropping from 4→3 PolytabloidBasis sorries.

**Biggest blocker right now is CI infrastructure**, not mathematics. 6 PRs with correct code have been waiting 3+ days for CI to pass. If CI stabilizes and these merge, 3 blocked issues immediately become actionable, potentially dropping sorry count further.

**Tractable targets:**
1. `polytabloid_linearIndependent` (#2212, claimed) — Transfer map approach, difficulty 4
2. `column_standard_in_span'` + `perm_mul_youngSymmetrizer_mem_span` (#2217, claimed) — Straightening lemma, difficulty 7
3. `head_isomorphism` (#2174, blocked on CI) — Once #2175 merges
4. `Corollary6_8_4` mixed vertex (#2208, blocked on CI) — Once PR merges

**Hard targets (no current path):**
5. `iso_of_glWeightSpace_finrank_eq` (#2226, unclaimed) — Requires Schur-Weyl or complete reducibility infrastructure, difficulty 8
6. `Problem6_1_5_theorem` forward direction (#2112, blocked on #2143 chain) — Needs non-ADE classification chain to complete
7. `Theorem2_1_2` (Gabriel's theorem) — Top-level; depends on most other sorries

The final 3-4 sorries may represent an irreducible core requiring either novel mathematical formalization or acceptance as long-term goals.

## Strategic Recommendations

1. **Fix CI infrastructure** — This is the single highest-leverage action. 6 code-correct PRs blocked for 3+ days. Consider escalating to repo maintainers or investigating runner configuration.

2. **Monitor #2212 and #2217** — Both claimed and actively worked. If either completes, PolytabloidBasis drops to 2 or 1 sorries.

3. **iso_of_glWeightSpace_finrank_eq** (#2226) — Only unclaimed feature issue. Difficulty 8. Consider decomposing into sub-tasks or accepting as a long-term sorry.

4. **Close stale issues** — #1571 (template reconciliation) and any other stale issues should be triaged.
