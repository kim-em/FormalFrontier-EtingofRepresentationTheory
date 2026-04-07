# Wave 46 Summary

**Date:** 2026-04-08
**Sorries:** 15 (unchanged from wave 45)
**Files with sorries:** 8 (unchanged)
**Items sorry-free:** 580/583 (99.5%)

## What Changed

This wave saw genuine proof progress offset by architectural cleanup, resulting in a net-zero sorry change.

**Proof progress:**
- Corollary6_8_4 went 2→1 sorry. PR #2184 resolved a typeclass synthesis blocker, and PR #2197 proved both the source case (F⁻ at source) and sink case (F⁺ at sink) of the reflection functor step. Only the mixed vertex case remains.
- Extended Dynkin infrastructure expanded: Ẽ_6 and Ẽ_8 adjacency matrices and graph properties defined (#2196), enabling non-ADE classification work.
- Radical preservation by module category equivalences proved sorry-free (#2166).

**Architectural cleanup:**
- PolytabloidBasis went 7→8 sorry. PR #2162 proved that `polytabloid_apply` and `polytabloid_self_coeff` are FALSE for the T-dependent definition (−2 false sorries). PR #2172 removed the false `garnir_columnInvCount_decrease` and restructured straightening with proper sorry placeholders (+3 properly-scoped sorries).
- YoungSymmetrizer convention fixed from a·b to b·a (#2178).

## CI Bottleneck

Main branch has a build breakage (#2188) with two competing fix PRs (#2192, #2190) both pending CI. 6+ other PRs are blocked on this. Resolving #2188 is the single highest-impact action.

## Open PR Pipeline

8 open PRs, most blocked on #2188 CI fix. Notable:
- PR #2183 would close 6 PolytabloidBasis sorries (biggest potential sorry reduction)
- PR #2191 adds D̃_n infinite type proof
- PRs #2200/#2198 add Ẽ_8 infinite type and Ẽ_6 representation construction

## Stale Issues Identified

- #1733: Theorem5_18_4 is now sorry-free (was 4 sorries when filed)
- #1729: Infrastructure sorry-free, Ch9 down to 1 — superseded by specific issues
- #2001: Proposition5_14_1 is sorry-free
- #1842: TabloidSetoid refactor may be superseded by polytabloid definition switch
