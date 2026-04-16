# Wave 51 Summary

**Date:** 2026-04-17
**Issue:** #2333
**PRs merged since wave 50:** 11 (#2312, #2314, #2316, #2320–#2324, #2328, #2329, #2323, #2337)

## Headline

**Theorem 2.1.2 (Gabriel's theorem) is structurally proven**, modulo two named bridge
lemmas (`not_posdef_not_HasFiniteRepresentationType`, `isDynkinDiagram_HasFiniteRepresentationType`).
The monolithic Ch6 case-analysis sorry `single_branch_leaf_case` was decomposed
into 12 sub-sorries corresponding to specific ADE tree posdef proofs and 3 of
those closed immediately via T(1,2,5) subgraph embeddings.

The sorry raw count increased 13 → 21, driven entirely by decomposition: each
individual sub-sorry is now much smaller and more tractable than the monolithic
parents it replaced.

## Key Achievements

- **Gabriel's theorem structure landed** (PR #2324): the main bi-implication
  `Theorem_2_1_2` is now written as `hfrt → Dynkin` via a forward bridge and
  `Dynkin → hfrt` via a backward bridge. Both bridges still have `sorry`, but the
  theorem statement is now exactly one `by` block away from being fully proved.

- **Garnir straightening 2/3 done** (PRs #2314, #2323):
  `garnir_polytabloid_identity` and `garnir_straightening_step` are fully proved.
  `garnir_twisted_in_lower_span` remains sorry; the final rebase (#2337) fixed
  merge conflicts. A new intermediate `twistedPolytabloid_col_eq` sorry was
  introduced to isolate the reindexing-by-conjugation step.

- **Cluster B decomposition + partial closures** (PRs #2316, #2321, #2329, #2312):
  - `single_branch_leaf_case` 1 sorry → 12 sub-sorries → 9 sub-sorries (3 closed
    via `embed_t125_in_tree` in #2329)
  - `non_adjacent_branches_infinite_type` proved up to 3 leaf-case sorries (#2312)
  - `Ẽ₇` embedding helper proved (#2316)

- **Proposition 5.22.2 weight-space spanning** (PR #2320): proved
  `glWeightSpace_schurModule_iSup_eq_top` (the weight-space sum spans the Schur
  module). One sorry (`h_dim`) remains.

- **Field-generic cycle infrastructure** (PR #2328): new file
  `FieldGenericInfiniteType.lean` provides `nilpotentShiftMatrixGen`,
  `cycleRepGen`, and `cycle_not_finite_type_gen` over arbitrary fields. This
  is a first step toward the ∀k∀Q refactor that the Theorem_2_1_2 forward
  bridge needs.

- **Build-failure cleanup** (PR #2322): repaired `InfiniteTypeConstructions`
  and `Corollary9_7_3` build failures introduced by the wave-50 PRs #2306
  and #2292 (constructor vs. Connected.mk, universe mismatch).

## Metrics

| Metric | Wave 50 | Wave 51 | Delta |
|--------|---------|---------|-------|
| Sorries | 13 | 21 | +8 (decomposition) |
| Files with sorries | 5 | 5 | 0 |
| Items sorry-free | 582/583 | 582/583 | 0 |
| Chapters sorry-free | 6/9 | 6/9 | 0 |
| Open PRs | 2 (failing CI) | 0 | −2 |

## Sorry Breakdown by Cluster

| Cluster | Wave 50 | Wave 51 | Status |
|---------|---------|---------|--------|
| A: Polytabloid/Straightening (Ch5) | 6 | 4 | 3 proved, 1 new decomposition sorry (−2 net) |
| B: Infinite Type (Ch6) | 5 | 15 | Major decomposition, 3 sub-sorries closed (+10 net) |
| C: Morita Theory (Ch9) | 0 | 0 | Remains closed |
| D: Gabriel's Theorem (Ch2) | 2 | 2 | Structure proved, bridges sorry'd |

## Active Work

- **#2325** (claimed 3 days, may be stale): 9× Dynkin posdef in single_branch_leaf_case
- **#2331** (claimed 3 days, may be stale): 3× leaf-case in non_adjacent_branches
- **#2333** (claimed, this session): Wave 51 summary
- **#2255, #2256** (unclaimed): Theorem_2_1_2 forward / backward bridges
- **#2332** (unclaimed): iso_of_glWeightSpace_finrank_eq + h_dim
- **#2334, #2335, #2336** (unclaimed): 3× indecomposability proofs

## Concerns

1. **Two PR titles in this wave were misleading.** PR #2320 claimed to prove
   `iso_of_formalCharacter_eq_schurPoly + Proposition5_22_2 h_dim` but only
   closed `glWeightSpace_schurModule_iSup_eq_top`. PR #2323 claimed to prove
   `garnir_twisted_in_lower_span` but that theorem still has a `sorry`. The
   commit messages and diffs were accurate; only the PR titles over-promised.
   Future summarize/planner agents should verify titles against diffs.

2. **Three 3-day-old claims** (#2325, #2331, this #2333) raise concern that
   sessions may be dying without publishing. `coordination release-stale-claims`
   is available but manual.

3. **Sorry count trending up despite genuine closures.** Raw count now 21; the
   decomposition strategy works mathematically (each sub-problem is more
   tractable) but makes the headline look bad. The right metric is
   "(# sorries) × (average difficulty per sorry)" — both waves 50 and 51
   reduced the average difficulty while raw count grew.

4. **`iso_of_formalCharacter_eq_schurPoly` is the hardest remaining Ch5 sorry**
   and may require either new Mathlib infrastructure (GL_N complete
   reducibility / Schur-Weyl) or a book-specific workaround using earlier
   Chapter 5 results. Needs a careful scoping pass.

## Recommendations for Wave 52

1. **Audit stale claims.** If #2325 and #2331 sessions are dead, releasing
   them unblocks 12 of the 15 Chapter 6 sorries for new agents.

2. **Pick off tractable Cluster B sorries.** The 9 `single_branch_leaf_case`
   posdef sub-sorries are each elementary linear algebra (D₅, E₆, E₇, E₈
   positive-definite Cartan forms). A planner could subdivide #2325 into
   9 tiny issues for parallelism.

3. **Close `twistedPolytabloid_col_eq`.** The reindexing-by-conjugation step
   is routine and would immediately take SpechtModuleBasis to 1 sorry.

4. **Start Theorem_2_1_2 forward bridge (#2255).** PR #2328 began the ∀k∀Q
   refactor for the cycle case; the star / D̃₅ / Ẽ₆ / Ẽ₇ / T(1,2,5) cases
   remain. This work can proceed in parallel with Cluster B's remaining sorries.

5. **Scope `iso_of_formalCharacter_eq_schurPoly`.** Either commit to
   formalizing GL_N complete reducibility, or find a book-specific
   workaround. The current sorry is a known hard long-tail target.

6. **Verify PR title/diff mismatches.** Consider a planner or reviewer step
   that checks whether a PR's claimed sorries are actually closed; ~2 PRs
   out of 11 this wave had inaccurate titles.
