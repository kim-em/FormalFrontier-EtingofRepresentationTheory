# Wave 50 Summary

**Date:** 2026-04-13
**Issue:** #2309
**PRs merged since wave 49:** 15 (#2272, #2278, #2280–#2282, #2289–#2293, #2297–#2298, #2304–#2306)

## Headline

**Chapter 9 (Morita Theory) is now sorry-free.** PR #2292 closed the last sorry in
`MoritaStructural.lean` by proving `semisimple_iso_of_finrank_hom_eq`. This is the
first chapter to fully clear since the endgame began.

## Key Achievements

- **MoritaStructural sorry-free** (PR #2292): proved the semisimple module isomorphism
  using finrank equality of Hom spaces. The head_isomorphism proof is now complete.
  Ch9 joins Ch3, Ch4, Ch7, Ch8 as fully formalized.

- **Infinite type infrastructure** (PRs #2278, #2290, #2291, #2293, #2298, #2305, #2306):
  Major progress on the Gabriel's theorem critical path. Proved graph cycle → infinite type,
  acyclic path positive definiteness, adjacent branches D̃₅ embedding, and tree acyclicity
  lemmas. The graph classification sorry was decomposed into 2 focused sub-cases.

- **Garnir straightening decomposition** (PRs #2272, #2304): the monolithic straightening
  sorry was decomposed into 3 independently-attackable sub-problems: the polytabloid
  identity (difficulty 5), twisted polytabloid in lower span (difficulty 8), and the
  combining step.

- **Weight decomposition infrastructure** (PR #2280): added GL_N weight space machinery
  for Schur modules, needed for Proposition 5.22.2.

- **Row-standard uniqueness** (PR #2289): proved eq_of_rowStandard_of_toTabloid_eq,
  unblocking downstream straightening work.

## Metrics

| Metric | Wave 49 | Wave 50 | Delta |
|--------|---------|---------|-------|
| Sorries | 10 | 13 | +3 (decomposition) |
| Files with sorries | 6 | 5 | −1 |
| Items sorry-free | 581/583 | 582/583 | +1 (Corollary6.8.4) |
| Chapters sorry-free | 5/9 | 6/9 | +1 (Ch9) |

## Sorry Breakdown by Cluster

| Cluster | Wave 49 | Wave 50 | Status |
|---------|---------|---------|--------|
| A: Polytabloid/Straightening (Ch5) | 3 | 6 | Decomposed, 2 issues claimed |
| B: Infinite Type (Ch6) | 4 | 5 | Major infra progress, 2 failing PRs |
| C: Morita Theory (Ch9) | 1 | **0** | **CLOSED** |
| D: Gabriel's Theorem (Ch2) | 2 | 2 | Blocked on B |

## Active Work

- **#2310** (claimed): Indecomposability proofs for etilde6v2, etilde7, t125
- **#2311** (claimed): Garnir straightening sub-lemmas
- **#2307** (PR, failing CI): Single branch not_posdef decomposition
- **#2312** (PR, failing CI): Non-adjacent branches infinite type

## Concerns

1. **Two open PRs have failing CI** — these need immediate attention (rebase or fix)
2. **Sorry count trending up** — decomposition is good strategy but makes headline
   numbers look worse. Raw count: 8→10→13 over waves 48-50.
3. **Hardest sorries remain** — indecomposability (×3), GL_N complete reducibility,
   Garnir twisted span, and Gabriel's theorem directions are all difficulty 7-9.

## Recommendations for Wave 51

1. Fix failing PRs #2307 and #2312 (highest priority — lost work if abandoned)
2. Complete Garnir polytabloid identity (difficulty 5, quick win)
3. Continue indecomposability proofs (3 independent, parallelizable)
4. Assess whether FormalCharacterIso sorry is feasible or should be deferred
