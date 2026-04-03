# Sorry Landscape Analysis — Wave 42

Generated 2026-04-03 by summarize session (issue #2051).

## Summary

**25 sorries** across 14 files. Changed from 25 / 11 in wave 41: **0 net sorries, +3 files**. Chapters 3, 4, 7, 8 remain 100% sorry-free. 266 of 280 Lean files (95.0%) are sorry-free. 577/583 items (98.9%) sorry-free.

**Data correction:** Wave 41 reported 25 sorries / 11 files but missed 3 files that had existing sorries (CoxeterInfrastructure, Problem6_1_5_theorem, Theorem6_5_2). The true wave 41 count was 28 sorries / 14 files. Against corrected wave 41, wave 42 is **−3 sorries, 0 files**.

7 PRs merged since wave 41 (#2018–#2059). Key changes:

- **Proposition5_14_1 sorry-free** (#2048) — Convention swap regression fixed (2→0 sorries). Cluster F eliminated.
- **PolytabloidBasis 6→3** (#2018) — T_col_inc proved; 3 garnir/column helpers closed.
- **FormalCharacterIso 2→1** (#2059) — formalCharacter_shift_of_weightSpace_finrank proved.
- **Theorem5_22_1 2→5** (#2042, #2058) — Trace formula scaffolded into 5 specific helpers. Net +3 from decomposition.
- **Theorem5_27_1 4→2** — exists_simple_subrep and hWχ_nz proved (PRs merged on main or resolved). 2 helpers remain with open PRs (#2047, #2049) not yet merged.
- **Corollary6_8_3 1→2** (#2050) — Proof restructured with parallel reflection chain. Temporary +1 from scaffolding.
- **Proposition5_22_2 NEW** (#2059) — 1 sorry introduced (zero-component weight space vanishing).
- **OrientationDefs extracted** (#2057) — Circular import broken for Corollary6_8_4. No sorry count change.

**Net sorry change: −3** (against corrected wave 41). Convention swap regression fully recovered. Three garnir helpers proved. FormalCharacterIso shift formula proved. Scaffolding expanded Theorem5_22_1 and Corollary6_8_3.

**Definition-level sorries: 0.** All mathematical objects are constructed. No regression.

## Chapter Breakdown

| Chapter | Sorries | Files | Delta from Wave 41 (corrected) |
|---------|---------|-------|-------------------------------|
| Ch2 | 1 | 1 | 0 |
| Ch5 | 13 | 6 | −4 sorries, −1 file (Proposition5_14_1 sorry-free; PolytabloidBasis 6→3; FormalCharacterIso 2→1; Theorem5_22_1 2→5; Theorem5_27_1 4→2; Proposition5_22_2 +1 NEW) |
| Ch6 | 7 | 6 | +1 sorry, 0 files (Corollary6_8_3 1→2 from restructuring) |
| Ch9 | 4 | 1 | 0 |

## Files That Became Sorry-Free Since Wave 41

1. **Proposition5_14_1.lean** — 2 sorries → 0. Convention swap regression fixed (#2048). Young symmetrizer proofs adapted to RowSymmetrizer * ColumnAntisymmetrizer convention.

## New Files With Sorries

1. **Proposition5_22_2.lean** — 1 sorry (NEW). Zero-component weight vanishing for det-twisted Schur module. Introduced during formalCharacter shift proof (#2059).

## Per-File Sorry Detail

| File | Sorries | Nature | Delta from W41 |
|------|---------|--------|----------------|
| Theorem5_22_1 | 5 | finrank_glWeightSpace trace + coeff_restrictLastVar + restrictLastVar_alternantDet + charValue_remove_trailing_zero + charValue_reduce_to_n | **+3** (scaffolded) |
| MoritaStructural (Ch9) | 4 | surjection_with_trivial_kernel_head + Module.Finite transport + equivFunctorLinear + AlgEquiv scalar | 0 |
| PolytabloidBasis | 3 | polytabloid_linearIndependent + column_standard_in_span' + garnir_identity_expansion | **−3** |
| Corollary6_8_3 | 2 | indecomposable_simpleRoot_iso + iteration tracking | **+1** |
| Theorem5_27_1 | 2 | exists_character_in_rep + exists_nonzero_map_from_induced | **−2** |
| FormalCharacterIso | 1 | iso_of_formalCharacter_eq | **−1** |
| Proposition5_22_2 | 1 | zero-component weight vanishing (det-twist) | **NEW** |
| TabloidModule | 1 | polytabloid_syt_dominance (PQ transformation) | 0 |
| Theorem2_1_2 | 1 | Gabriel's theorem | 0 |
| Corollary6_8_4 | 1 | indecomposable_of_positive_root | 0 |
| CoxeterInfrastructure | 1 | one_round_or_simpleRoot (universe constraint blocker) | 0 |
| Problem6_1_5_theorem | 1 | Theorem_6_1_5 (finite type ↔ Dynkin) | 0 |
| Problem6_9_1 | 1 | off_diagonal_nilpotent_product_decomp (compatible chain basis) | 0 |
| Theorem6_5_2 | 1 | Theorem_6_5_2c_bijection (dim vector bijection) | 0 |

## Merged PRs Since Wave 41 (7)

### Weyl Character / Young Symmetrizer (Ch5)
| PR | Title |
|----|-------|
| #2048 | Fix: Proposition5_14_1 convention swap regression (2→0 sorries) |
| #2042 | Scaffold tensor basis helpers for finrank_weight_eq_card_sum |
| #2058 | Prove finrank_weight_eq_card_sum trace formula decomposition (5→5 sorries) |
| #2059 | Prove formalCharacter_shift_of_weightSpace_finrank (2→1 sorry) |

### Schur-Weyl / Polytabloid (Ch5)
| PR | Title |
|----|-------|
| #2018 | Prove T_col_inc — column-increasing for row-sorted column-standard fillings |

### Gabriel Theorem Chain (Ch6)
| PR | Title |
|----|-------|
| #2050 | Restructure Corollary6_8_3 proof with parallel reflection chain |
| #2057 | Extract OrientationDefs to break circular import for Corollary6_8_4 |

## Open PRs (pending merge)

| PR | Title | Status |
|----|-------|--------|
| #2047 | Prove exists_character_in_rep (2→1 sorry) | CI cancelled |
| #2049 | Prove exists_nonzero_map_from_induced: Mackey Frobenius reciprocity | CI failed |

## Active Work Items (claimed)

| Issue | Title | Impact |
|-------|-------|--------|
| #2053 | Corollary6_8_3 recovery lemma + iteration tracking | 2→0 sorry |
| #2054 | charValue stability chain in Theorem5_22_1 | 5→1 sorry |
| #2055 | garnir_identity_expansion in PolytabloidBasis | 3→2 sorry |

## Dependency Clusters

### Cluster A: Polytabloid Basis (Ch5, 4 sorries)
**Files:** PolytabloidBasis (3), TabloidModule (1)
**Key sorries:**
- `polytabloid_linearIndependent` — needs tabloid projection approach
- `column_standard_in_span'` — straightening algorithm
- `garnir_identity_expansion` — Garnir identity expansion (active: #2055)
- `polytabloid_syt_dominance` — PQ transformation dominance ordering
**Status:** Down from 7 to 4 (3 garnir/column helpers proved by #2018). Active work on garnir_identity_expansion (#2055).

### Cluster B: Weyl Character Formula (Ch5, 7 sorries)
**Files:** Theorem5_22_1 (5), FormalCharacterIso (1), Proposition5_22_2 (1)
**Key sorries:**
- `finrank_glWeightSpace_eq_restricted_trace` — weight space finrank via Young symmetrizer trace
- `coeff_restrictLastVar` — coefficient extraction through variable restriction
- `restrictLastVar_alternantDet` — Vandermonde determinant under x_N=0 restriction
- `charValue_remove_trailing_zero` + `charValue_reduce_to_n` — charValue canonical form (active: #2054)
- `iso_of_formalCharacter_eq` — isomorphism from formal character equality
- zero-component weight vanishing (Proposition5_22_2)
**Status:** Net +2 from scaffolding (2→5 in Theorem5_22_1), but shift formula proved (FormalCharacterIso 2→1). Active work on charValue chain (#2054, targeting 5→1).

### Cluster C: Mackey Machine (Ch5, 2 sorries)
**Files:** Theorem5_27_1 (2)
**Remaining:**
1. `exists_character_in_rep` — simultaneous diagonalization / Maschke + Schur (open PR #2047)
2. `exists_nonzero_map_from_induced` — Frobenius reciprocity construction (open PR #2049, CI failing)
**Status:** Down from 4 to 2. Two helpers proved. Two open PRs pending CI fixes.

### Cluster D: Gabriel Theorem Chain (Ch6, 7 sorries)
**Files:** Corollary6_8_3 (2), Corollary6_8_4 (1), CoxeterInfrastructure (1), Problem6_1_5_theorem (1), Problem6_9_1 (1), Theorem6_5_2 (1)
**Status:** Corollary6_8_3 restructured with parallel reflection chain (#2050). OrientationDefs extracted (#2057) to unblock Corollary6_8_4. Active work on recovery lemma (#2053).
**Note:** CoxeterInfrastructure sorry (one_round_or_simpleRoot) is blocked by Lean universe constraints. Problem6_1_5_theorem and Theorem6_5_2 each have 1 sorry carried from earlier waves (miscounted as 0 in wave 41).

### Cluster E: Morita Theory (Ch9, 4 sorries)
**Files:** MoritaStructural (4)
**Key sorries:**
- `exists_surjection_with_trivial_kernel_head` — Nakayama-style argument
- Module.Finite transport through equivalence
- `equivFunctorLinear` — Eilenberg-Watts k-linearity
- AlgEquiv k-algebra scalar preservation
**Status:** Unchanged from wave 41. All 4 sorries relate to the Eilenberg-Watts k-linearity gap.

### Isolated
- **Theorem2_1_2** (1 sorry): Gabriel's theorem classification. Depends on Cluster D completion.

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

*Wave 41 corrected from reported 25/11 to actual 28/14 (3 files with existing sorries were miscounted as sorry-free).

Wave 42 shows steady progress: −3 net sorries (corrected). Proposition5_14_1 convention regression fully recovered. PolytabloidBasis cluster shrinking. Theorem5_22_1 expanded from scaffolding but has active work targeting 5→1. Three claimed issues (#2053, #2054, #2055) could reduce sorries by up to 8 if successful.

## Strategic Recommendations

1. **Fix open PR CI** (#2047 exists_character_in_rep, #2049 exists_nonzero_map_from_induced) — These would bring Theorem5_27_1 to 0 sorries, completing Cluster C. Priority: rebase onto main and fix CI failures.

2. **Cluster B charValue chain** (#2054) — Active work targeting Theorem5_22_1 5→1. If successful, this is the single largest sorry reduction available.

3. **Cluster D Gabriel corollaries** (#2053) — Active work on Corollary6_8_3 recovery lemma (2→0). CoxeterInfrastructure sorry blocked by universe constraints — may need architectural rethink.

4. **PolytabloidBasis garnir** (#2055) — Active work on garnir_identity_expansion (3→2). After that, 2 hard sorries remain (linearIndependent + column_standard_in_span').

5. **MoritaStructural Eilenberg-Watts** — 4 unchanged sorries. No active work. May need a dedicated Eilenberg-Watts k-linearity construction or alternative approach.

6. **Data quality**: Update items.json — several files with sorries aren't tracked as non-sorry-free items (PolytabloidBasis, MoritaStructural, etc. missing from non-sorry-free list). Also correct for files wave 41 miscounted.
