# Sorry Landscape Analysis — Wave 47

Generated 2026-04-11 by meditate session (issue #2220).

## Summary

**9 sorries** across 6 files (down from 15/8 in wave 46). The sorry count dropped by 6 — the largest single-wave reduction since wave 43.

275 of 281 Lean files (97.9%) are sorry-free. 580/583 items (99.5%) sorry-free. Chapters 3, 4, 7, 8 remain 100% sorry-free.

Key merges since wave 46 (5 PRs merged):

- **YoungSymmetrizer coefficient lemmas proved** (#2221) — `youngSymmetrizer_support`, `youngSymmetrizer_pq_coeff`, `youngSymmetrizer_one_coeff`, `youngSymmetrizer_rowPerm_coeff` all proved. PolytabloidBasis 8→4 sorries.
- **Problem6_9_1 proved** (#2215) — `compatible_product_decomp` closed. Problem6_9_1 → 0 sorry.
- **TabloidModule cleaned up** (#2209) — Removed unused sorry'd `polytabloid_syt_dominance`. TabloidModule → 0 sorry.
- **CI fixed** (#2213, #2214) — Main branch CI breakage resolved, 6 PRs rebased.

**Net sorry change: −6.** PolytabloidBasis −4 (coefficient lemmas proved), Problem6_9_1 −1 (proved), TabloidModule −1 (unused sorry removed).

**Definition-level sorries: 0.** All mathematical objects are constructed.

## Chapter Breakdown

| Chapter | Sorries | Files | Delta from Wave 46 |
|---------|---------|-------|---------------------|
| Ch2 | 1 | 1 | 0 |
| Ch5 | 5 | 2 | −5 (PolytabloidBasis 8→4, TabloidModule 1→0) |
| Ch6 | 2 | 2 | −1 (Problem6_9_1 1→0) |
| Ch9 | 1 | 1 | 0 |

## Files That Became Sorry-Free Since Wave 46

- **TabloidModule.lean** (Ch5): Removed unused `polytabloid_syt_dominance` (#2209)
- **Problem6_9_1.lean** (Ch6): `compatible_product_decomp` proved (#2215)

## Per-File Sorry Detail

| File | Sorries | Theorems | Delta |
|------|---------|----------|-------|
| PolytabloidBasis (Ch5) | 4 | polytabloid_mem_spechtModule, polytabloid_linearIndependent, column_standard_in_span', perm_mul_youngSymmetrizer_mem_span_polytabloids | **−4** |
| FormalCharacterIso (Ch5) | 1 | iso_of_glWeightSpace_finrank_eq (GL_N complete reducibility) | 0 |
| Corollary6_8_4 (Ch6) | 1 | Corollary6_8_4 mixed vertex case | 0 |
| Problem6_1_5_theorem (Ch6) | 1 | forward direction (positive definiteness → finite type) | 0 |
| MoritaStructural (Ch9) | 1 | head_isomorphism (progenerator lift surjectivity) | 0 |
| Theorem2_1_2 (Ch2) | 1 | Gabriel's theorem (finite rep type ↔ Dynkin) | 0 |

## Open PRs (7)

| PR | Title | CI Status | Mergeable |
|----|-------|-----------|-----------|
| #2219 | non_ADE_not_finite_type (non-Dynkin → infinite type) | IN_PROGRESS | Yes |
| #2208 | Corollary6_8_4 mixed vertex case | RE-TRIGGERED | Yes |
| #2200 | etilde8_not_finite_type via Ẽ_6 subgraph | RE-TRIGGERED | Yes |
| #2198 | Ẽ_6 representation construction | RE-TRIGGERED | Yes |
| #2191 | D̃_n infinite type proof | RE-TRIGGERED | Yes |
| #2183 | YoungSymmetrizer coefficient lemmas (6 sorries) | CANCELLED | **CONFLICTS** |
| #2175 | Module.Finite infrastructure | RE-TRIGGERED | Yes |

**CI status notes:** 5 PRs (#2175, #2191, #2198, #2200, #2208) have CI re-triggered and currently running. #2219 is a new PR with CI in progress. #2183 has merge conflicts (superseded by #2221 which merged the coefficient lemmas directly) and CANCELLED CI — should be closed.

**PR #2183 should be closed:** Its content (YoungSymmetrizer coefficient lemmas) was independently proved and merged in #2221. The PR has merge conflicts and stale CI. The remaining sorry reduction it offered (polytabloid_mem_spechtModule) can be pursued separately.

## Blocked Issues (5)

| Issue | Blocked on | Title |
|-------|-----------|-------|
| #2199 | (PR #2198) | Prove etilde6Rep_isIndecomposable |
| #2187 | #2185 (PR #2191) | Non-ADE tree case analysis |
| #2174 | #2173 (PR #2175) | Prove head_isomorphism using Module.Finite |
| #2112 | #2143 | Close positive definiteness sorry in Theorem_6_1_5 |
| #1571 | — | Reconcile repo with FormalFrontier templates (stale) |

**Unblocking cascade:** When CI passes:
- #2175 merges → unblocks #2174 (head_isomorphism → MoritaStructural sorry)
- #2191 merges → unblocks #2187 (non-ADE tree case analysis)
- #2198 merges → unblocks #2199 (Ẽ_6 indecomposability)
- #2200 merges → contributes to #2143 chain
- #2219 merges → contributes to #2143 chain (non-Dynkin → infinite type)

If all 5 re-triggered PRs pass CI and merge, #2187 and #2174 become unblocked. #2143 (non-ADE classification) becomes closer to closure, which would unblock #2112.

## Claimed Work Items

| Issue | Title | Agent |
|-------|-------|-------|
| #2217 | Prove polytabloid straightening lemma | Claimed 1 day ago |
| #2218 | Review 6 re-triggered PRs | Claimed 1 day ago |

## Unclaimed Work Items

| Issue | Title | Impact |
|-------|-------|--------|
| #2212 | Prove polytabloid_linearIndependent via transfer map | 1→0 sorry (PolytabloidBasis) |

## Dependency Clusters

### Cluster A: Polytabloid Basis (Ch5, 5 sorries)
**Files:** PolytabloidBasis (4), FormalCharacterIso (1)
**Key sorries:**
- `polytabloid_mem_spechtModule` — e_T ∈ V_λ (T-dependent definition complicates membership)
- `polytabloid_linearIndependent` — transfer from tabloid-module proof (#2212)
- `column_standard_in_span'` — column-standard straightening (difficulty ~7)
- `perm_mul_youngSymmetrizer_mem_span_polytabloids` — full straightening lemma
- `iso_of_glWeightSpace_finrank_eq` — GL_N complete reducibility (deep infrastructure)
**Status:** Down from 9→5. The 4 coefficient lemma sorries were closed by #2221. The remaining 4 in PolytabloidBasis are the genuinely hard problems. #2212 (linearIndependent via transfer) is unclaimed and tractable. #2217 (straightening) is claimed.
**Critical path:** polytabloid_mem_spechtModule → linearIndependent (#2212) → straightening (#2217). FormalCharacterIso is independent and lowest priority.

### Cluster B: Gabriel Theorem Chain (Ch6, 2 sorries)
**Files:** Corollary6_8_4 (1), Problem6_1_5_theorem (1)
**Status:** Down from 3→2. Problem6_9_1 proved (#2215). Multiple PRs in flight for the non-ADE classification chain.
**Critical path:** PRs #2191, #2200, #2198, #2219 merge → #2143 closes → #2112 closes → Problem6_1_5_theorem sorry closes. Corollary6_8_4 mixed vertex case (#2170) is independent.

### Cluster C: Morita Theory (Ch9, 1 sorry)
**Files:** MoritaStructural (1)
**Remaining:** head_isomorphism (progenerator lift surjectivity)
**Status:** Blocked on #2175 (Module.Finite infrastructure, CI re-triggered). Once #2175 merges, #2174 becomes actionable.

### Isolated
- **Theorem2_1_2** (1 sorry): Gabriel's theorem. Depends on Clusters A and B.

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
| **47** | **9** | **6** | **580/583 (99.5%)** | **2026-04-11** |

After a two-wave plateau at 15 sorries, significant progress resumed. The −6 drop came from three focused efforts: coefficient lemma proofs (#2221), Problem6_9_1 closure (#2215), and TabloidModule cleanup (#2209).

**Honest assessment:** The project has broken through the "hard sorry" plateau. 9 sorries remain, all genuinely difficult. The most tractable targets are: (1) polytabloid_linearIndependent via transfer map (#2212, unclaimed), (2) Corollary6_8_4 mixed vertex case (#2170, when CI PRs merge), (3) head_isomorphism (#2174, when #2175 merges). The remaining sorry count is approaching the irreducible core — the final 4-5 sorries may each require novel mathematical arguments or significant infrastructure.

## Strategic Recommendations

1. **Wait for CI results** — 5 PRs have re-triggered CI. Once they pass and merge, 3 blocked issues unblock. This is the highest-leverage action and requires no code work.

2. **Close PR #2183** — Superseded by #2221. Has merge conflicts and stale CI.

3. **polytabloid_linearIndependent** (#2212, unclaimed) — Transfer map from group algebra to tabloid module. Well-scoped, difficulty 4. Would reduce PolytabloidBasis to 3 sorries.

4. **Corollary6_8_4 mixed vertex** (#2170) — Once PR #2208 merges (has CI re-triggered), review whether additional work remains.

5. **head_isomorphism** (#2174) — Blocked on #2175 (CI re-triggered). Once merged, this becomes actionable.

6. **Close #1842** (stale) — TabloidSetoid RIGHT coset refactor, likely superseded.

7. **Update items.json** — Problem6_9_1 should be marked sorry_free (proved in #2215).
