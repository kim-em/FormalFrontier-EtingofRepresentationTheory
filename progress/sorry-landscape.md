# Sorry Landscape Analysis — Wave 44

Generated 2026-04-05 by summarize session (issue #2122).

## Summary

**10 sorries** across 8 files. Down from 13 / 10 in wave 43: **−3 sorries, −2 files**. Chapters 3, 4, 7, 8 remain 100% sorry-free. 272 of 280 Lean files (97.1%) are sorry-free. 580/583 items (99.5%) sorry-free.

12 PRs merged since wave 43 (#2087–#2120). Key changes:

- **Theorem5_22_1 sorry-free** (#2081) — `iso_of_glWeightSpace_finrank_eq` proved and moved to FormalCharacterIso.lean. Cluster B file is clean, but the sorry now lives in FormalCharacterIso (see note below).
- **Theorem6_5_2 sorry-free** (#2098) — `Theorem_6_5_2c_bijection` proved via Corollary6_8_3 + Corollary6_8_4.
- **CoxeterInfrastructure sorry-free** (#2115) — `one_round_or_simpleRoot` proved. Unblocks Corollary6_8_4.
- **MoritaStructural 2→1** (#2092) — `Module.Finite` transport proved. One sorry remains.
- **Problem6_1_5_theorem 1→1** (#2099, #2109) — Backward direction completed (#2109 proved B(d,d)=2 bridge). Forward direction positive definiteness sorry persists.
- **YoungSymmetrizer convention switch** (#2116) — Refactored from b_λ*a_λ to a_λ*b_λ. No sorry count change but unblocks polytabloid proofs.
- **Polytabloid analysis** (#2107, #2120) — Deep meditation on the 4-sorry cluster. Identified false statement (garnir_columnInvCount_decrease) and incorrect difficulty estimates.

**Net sorry change: −3.** Three files became sorry-free. One file (FormalCharacterIso) regressed from 0→1 due to sorry relocation from Theorem5_22_1.

**Definition-level sorries: 0.** All mathematical objects are constructed. No regression.

**Note on FormalCharacterIso regression:** Wave 43 reported FormalCharacterIso as sorry-free. PR #2081 moved `iso_of_glWeightSpace_finrank_eq` from Theorem5_22_1 to FormalCharacterIso, making Theorem5_22_1 sorry-free but FormalCharacterIso now has 1 sorry. The theorem was not actually proved — only relocated. This is honest accounting; the total count reflects the actual state.

## Chapter Breakdown

| Chapter | Sorries | Files | Delta from Wave 43 |
|---------|---------|-------|---------------------|
| Ch2 | 1 | 1 | 0 |
| Ch5 | 5 | 3 | 0 sorries, 0 files (FormalCharacterIso gained 1, Theorem5_22_1 lost 1) |
| Ch6 | 3 | 3 | −2 sorries, −2 files |
| Ch9 | 1 | 1 | −1 sorry, 0 files |

## Files That Became Sorry-Free Since Wave 43

1. **Theorem5_22_1.lean** — 1→0. `iso_of_glWeightSpace_finrank_eq` moved to FormalCharacterIso (#2081). The Weyl character formula file is now clean.
2. **CoxeterInfrastructure.lean** — 1→0. `one_round_or_simpleRoot` proved (#2115). This unblocks Corollary6_8_4.
3. **Theorem6_5_2.lean** — 1→0. `Theorem_6_5_2c_bijection` proved (#2098) via Corollary6_8_3 (existence) + Corollary6_8_4 (uniqueness).

## Files That Regressed

1. **FormalCharacterIso.lean** — 0→1. `iso_of_glWeightSpace_finrank_eq` relocated here from Theorem5_22_1 (#2081). The sorry needs Schur module complete reducibility infrastructure.

## Per-File Sorry Detail

| File | Sorries | Nature | Delta from W43 |
|------|---------|--------|----------------|
| PolytabloidBasis (Ch5) | 3 | polytabloid_linearIndependent + column_standard_in_span' + garnir case | 0 |
| FormalCharacterIso (Ch5) | 1 | iso_of_glWeightSpace_finrank_eq (complete reducibility of GL_N reps) | **+1** |
| TabloidModule (Ch5) | 1 | polytabloid_syt_dominance (PQ transformation dominance) | 0 |
| MoritaStructural (Ch9) | 1 | projective lift surjectivity (progenerator theory) | **−1** |
| Theorem2_1_2 (Ch2) | 1 | Gabriel's theorem (finite rep type ↔ Dynkin) | 0 |
| Corollary6_8_4 (Ch6) | 1 | indecomposable_of_positive_root (was blocked on CoxeterInfrastructure, now unblocked) | 0 |
| Problem6_1_5_theorem (Ch6) | 1 | Theorem_6_1_5 forward direction (positive definiteness → finite type) | 0 |
| Problem6_9_1 (Ch6) | 1 | off_diagonal_nilpotent_product_decomp (compatible chain basis) | 0 |

## Merged PRs Since Wave 43 (12)

### Gabriel Theorem Chain (Ch6)
| PR | Title |
|----|-------|
| #2098 | Prove Theorem_6_5_2c_bijection (1→0 sorry) |
| #2099 | Prove Theorem_6_1_5 backward direction in Problem6_1_5_theorem (1→0 sorry) |
| #2109 | Prove B(d,d)=2 bridge in Problem6_1_5_theorem backward direction (2→1 sorry) |
| #2115 | Prove one_round_or_simpleRoot sorry-free in CoxeterInfrastructure (1→0 sorry) |

### Weyl Character (Ch5)
| PR | Title |
|----|-------|
| #2081 | Prove iso_of_glWeightSpace_finrank_eq in Theorem5_22_1 (1→0 sorry, moved to FormalCharacterIso) |

### Schur-Weyl / Polytabloid (Ch5)
| PR | Title |
|----|-------|
| #2107 | Meditate: PolytabloidBasis approach redesign for 4 remaining sorries |
| #2116 | Refactor: switch YoungSymmetrizer from b_λ*a_λ to a_λ*b_λ convention |
| #2120 | Progress: deep analysis of polytabloid cluster sorries (#2117) |

### Morita Theory (Ch9)
| PR | Title |
|----|-------|
| #2092 | Prove Module.Finite transport in MoritaStructural (2→1 sorry) |
| #2108 | Progress: fix build errors and prove projective lift surjectivity in MoritaStructural |

### Infrastructure / Strategy
| PR | Title |
|----|-------|
| #2087 | Wave 43 sorry landscape update |
| #2091 | Progress: kernel dimension infrastructure for Problem6_9_1 |
| #2093 | Wave 44 endgame strategy review and skill updates |

## Open PRs (pending merge)

| PR | Title | Status |
|----|-------|--------|
| #2127 | Prove InfiniteTypeConstructions sorry-free (4→0 sorries) | Open, CI pending |
| #2126 | Progress: deep analysis of polytabloid_syt_dominance | Open |
| #2119 | Refactor: restructure straightening WF induction | CI failed |

## Active Work Items (claimed)

| Issue | Title | Impact |
|-------|-------|--------|
| #2083 | Prove compatible_chain_basis_decomp (Problem6_9_1) | 1→0 sorry |
| #2105 | Prove column_standard_in_span' (difficulty reassessed from 3→7) | 1→0 sorry |

## Unclaimed Work Items

| Issue | Title | Impact |
|-------|-------|--------|
| #2124 | Prove SYT entry comparison lemma (polytabloid_syt_dominance) | Unblocks #2125, #2106 |
| #2110 | Prove cycle subgraphs give infinite representation type | Unblocks #2111, #2112 |
| #2106 | Close polytabloid_linearIndependent (blocked on #2088) | 1→0 sorry |

## Dependency Clusters

### Cluster A: Polytabloid Basis (Ch5, 4 sorries)
**Files:** PolytabloidBasis (3), TabloidModule (1)
**Key sorries:**
- `polytabloid_linearIndependent` — needs polytabloid_syt_dominance first (#2088→#2106)
- `column_standard_in_span'` — straightening algorithm (difficulty reassessed to ~7, #2105)
- `garnir_columnInvCount_decrease` — **FALSE statement** per wave 44 analysis. Needs multiset Dershowitz-Manna ordering (#2104)
- `polytabloid_syt_dominance` — PQ transformation dominance. Sub-task #2124 created for entry comparison lemma.
**Status:** Unchanged at 4 sorries. Major analysis work completed: the garnir metric is provably false, the convention switch is done, and a concrete decomposition plan exists. No sorry reduction yet.
**Critical insight:** garnir_columnInvCount_decrease on a FALSE statement is the key blocker for the spanning direction. The independence direction is blocked on polytabloid_syt_dominance.

### Cluster B: Weyl Character Formula (Ch5, 1 sorry)
**Files:** FormalCharacterIso (1)
**Remaining:**
- `iso_of_glWeightSpace_finrank_eq` — GL_N complete reducibility (Schur-Weyl duality)
**Status:** Theorem5_22_1.lean is now sorry-free. The sorry was relocated to FormalCharacterIso. This is the last sorry for the Weyl character cluster but requires deep infrastructure (Schur module decomposition for polynomial GL_N reps). Cluster B is NOT eliminated — the sorry was moved, not proved.

### Cluster D: Gabriel Theorem Chain (Ch6, 3 sorries)
**Files:** Corollary6_8_4 (1), Problem6_1_5_theorem (1), Problem6_9_1 (1)
**Status:** Down from 5→3. Theorem6_5_2 and CoxeterInfrastructure both sorry-free. CoxeterInfrastructure completion **unblocks Corollary6_8_4** — this is now actionable.
**Key change:** `one_round_or_simpleRoot` proved (#2115) removes the universe constraint blocker. Corollary6_8_4 can now be attempted.
**Open PR #2127** may partially address Problem6_1_5_theorem forward direction by providing infinite type constructions for cycle subgraphs.
**Dependency chain:** Problem6_9_1 is independent. Problem6_1_5_theorem forward direction needs infinite type construction for non-Dynkin graphs. Corollary6_8_4 is now unblocked.

### Cluster E: Morita Theory (Ch9, 1 sorry)
**Files:** MoritaStructural (1)
**Remaining:**
- Projective lift surjectivity (progenerator theory)
**Status:** Down from 2→1. Module.Finite transport proved (#2092). One sorry remains: needs Nakayama-style surjection via progenerator theory.

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

*Wave 41 corrected from reported 25/11 to actual 28/14.

Wave 44 continues the downward trend: −3 sorries, −2 files (net). The project crossed the 99.5% items-sorry-free threshold. Three files became sorry-free (Theorem5_22_1, CoxeterInfrastructure, Theorem6_5_2), though FormalCharacterIso regressed due to sorry relocation.

**Honest assessment:** The rate of sorry reduction is slowing. Wave 43 eliminated 12 sorries; wave 44 eliminated only 3 (and one was a relocation). The remaining 10 sorries are all genuinely hard — deep combinatorial proofs (polytabloid cluster), infrastructure gaps (progenerator theory, Schur-Weyl duality), and standalone theorem proofs (Gabriel's theorem). There are no more "low-hanging fruit" sorries. Each remaining sorry likely requires 100+ lines of novel proof.

## Strategic Recommendations

1. **Corollary6_8_4** — NOW UNBLOCKED by CoxeterInfrastructure completion (#2115). This is the highest-priority newly-actionable item. The `indecomposable_of_positive_root` proof can now use `one_round_or_simpleRoot`.

2. **Problem6_1_5_theorem forward direction** — PR #2127 (InfiniteTypeConstructions) provides cycle graph infinite type. If merged, this provides key infrastructure for the forward direction's contrapositive argument.

3. **polytabloid_syt_dominance** (#2124) — The SYT entry comparison lemma is the critical path for the independence direction of the polytabloid cluster. Difficulty 8, novel combinatorial argument.

4. **Problem6_9_1 compatible chain basis** (#2083, claimed) — PID module theory argument. If successful, eliminates one of 3 Gabriel chain sorries.

5. **PolytabloidBasis spanning direction** — Blocked on #2104 (restructure WF induction). The `garnir_columnInvCount_decrease` sorry is on a FALSE statement. Needs multiset ordering approach. PR #2119 attempts this but CI is failing.

6. **MoritaStructural** — 1 sorry remains. Requires Nakayama-style progenerator infrastructure. Substantial new development needed.

7. **FormalCharacterIso** — Requires Schur module complete reducibility. This is a major infrastructure gap (Schur-Weyl duality formalization).
