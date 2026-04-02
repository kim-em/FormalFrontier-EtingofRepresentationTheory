# Sorry Landscape Analysis — Wave 41

Generated 2026-04-03 by summarize session (issue #2020).

## Summary

**25 sorries** across 11 files. Changed from 23 / 13 in wave 40: **+2 sorries, −2 files**. Chapters 3, 4, 7, 8 remain 100% sorry-free. 268 of 279 Lean files (96.1%) are sorry-free. 577/583 items (98.9%) sorry-free.

19 PRs merged since wave 40 (#1996–#2024). Key changes:

- **CoxeterInfrastructure sorry-free** (#2003) — Type-changing iterated reflection functors proved. Was Cluster D keystone; unblocks Corollary6_8_3 and Corollary6_8_4.
- **Problem6_1_5_theorem sorry-free** — Finite type ↔ Dynkin classification now fully proved.
- **Theorem6_5_2 sorry-free** — Indecomposable decomposition uniqueness proved.
- **Problem6_9_1 2→1** — One IsCompl condition resolved.
- **Theorem5_22_1 3→2** — One trace formula sorry closed (charValue bridge or stability).
- **Theorem5_27_1 3→4** (#2019, #2009, #2000) — Orbit injectivity proved, simple_fdRep_isIrreducible proved. Completeness proof scaffolded with 4 sorry'd helpers (exists_character_in_rep, exists_simple_subrep, exists_nonzero_map_from_induced, categorical bridge). Net +1 from restructuring.
- **Proposition5_14_1 0→2** (#2002) — Young symmetrizer convention swap (b_λ·a_λ → a_λ·b_λ) broke two proofs. Regression.
- **PolytabloidBasis 4→6** (#2002, #1999, #2005) — Convention swap regression (+2 sorries). Coset direction fix landed but convention change introduced new breakage.
- **MoritaStructural 2→4** (#2004, #1964) — regular_module_iso proved but restructuring exposed 2 new Eilenberg-Watts sorries (k-linearity of equivalence-induced ring iso).
- **MoritaStructural regular_module_iso proved** (#2004) — F(B₁) ≅ B₂ proved. BasicAlgebraExistence remains sorry-free.
- **equivEndAlgEquiv k-linearity proved** (#1964) — Scalar preservation proved, but exposed deeper Eilenberg-Watts gap.

**Net sorry change: +2** (regression from convention swaps and restructuring). Three files became sorry-free, but sorry count rose due to scaffolding and convention change regressions.

**Definition-level sorries: 0.** All mathematical objects are constructed. No regression.

## Chapter Breakdown

| Chapter | Sorries | Files | Delta from Wave 40 |
|---------|---------|-------|---------------------|
| Ch2 | 1 | 1 | 0 |
| Ch5 | 17 | 7 | +2 sorries, +1 file (Proposition5_14_1 regressed 0→2; PolytabloidBasis 4→6; Theorem5_27_1 3→4; Theorem5_22_1 3→2) |
| Ch6 | 3 | 3 | −2 sorries, −2 files (CoxeterInfrastructure sorry-free; Problem6_1_5_theorem sorry-free; Theorem6_5_2 sorry-free; Problem6_9_1 2→1) |
| Ch9 | 4 | 1 | +2 sorries (MoritaStructural 2→4 from restructuring) |

## Files That Became Sorry-Free Since Wave 40

1. **CoxeterInfrastructure.lean** — 1 sorry → 0. Type-changing iterated reflection functors proved (#2003). Keystone for Gabriel chain.
2. **Problem6_1_5_theorem.lean** — 1 sorry → 0. Finite type ↔ Dynkin classification proved.
3. **Theorem6_5_2.lean** — 1 sorry → 0. Indecomposable decomposition uniqueness proved.

## New Files With Sorries

1. **Proposition5_14_1.lean** — 2 sorries (REGRESSION). Young symmetrizer convention swap (#2002) broke two proofs that used `of_row_mul_RowSymmetrizer`.

## Per-File Sorry Detail

| File | Sorries | Nature | Delta from W40 |
|------|---------|--------|----------------|
| PolytabloidBasis | 6 | linearIndependent + column_standard_in_span + garnir helpers | **+2** |
| MoritaStructural (Ch9) | 4 | Nakayama + Module.Finite + Eilenberg-Watts k-linearity (×2) | **+2** |
| Theorem5_27_1 | 4 | exists_character_in_rep + exists_simple_subrep + exists_nonzero_map_from_induced + categorical bridge | **+1** |
| Theorem5_22_1 | 2 | Trace formula + charValue bridge | **−1** |
| Proposition5_14_1 | 2 | Convention swap regression (RowSymmetrizer/ColumnAntisymmetrizer) | **NEW** |
| FormalCharacterIso | 2 | iso_of_formalCharacter_eq + shift formula | 0 |
| Problem6_9_1 | 1 | IsCompl condition (pW/qW) | **−1** |
| Corollary6_8_3 | 1 | Indecomposable → positive root (reflection chain) | 0 |
| Corollary6_8_4 | 1 | Bijection: indec reps ↔ positive roots | 0 |
| TabloidModule | 1 | polytabloid_syt_dominance (PQ transformation) | 0 |
| Theorem2_1_2 | 1 | Gabriel's theorem | 0 |

## Merged PRs Since Wave 40 (19)

### Mackey Machine (Ch5)
| PR | Title |
|----|-------|
| #2000 | Prove orbit injectivity for Mackey machine |
| #2009 | Prove simple_fdRep_isIrreducible (1/2 sorrys resolved) |
| #2019 | Scaffold completeness proof for Theorem 5.27.1 (Mackey machine) |

### Weyl Character / Young Symmetrizer (Ch5)
| PR | Title |
|----|-------|
| #2002 | Fix: swap YoungSymmetrizer to b_λ·a_λ convention |
| #2006 | Prove Frobenius character bridge (N=n case) |
| #2014 | Prove canonicalBP scaffolding lemmas (3 of 4 bridge sorries) |
| #2015 | Fix: align YoungSymmetrizerZ/K convention and eliminate titsForm timeout |

### Schur-Weyl / Polytabloid (Ch5)
| PR | Title |
|----|-------|
| #1999 | Fix: correct LEFT/RIGHT coset mismatch in column_standard_coset_has_syt' |
| #2005 | Prove hp_row in column_standard_coset_has_syt' |
| #2024 | Fix: correct polytabloid_syt_dominance direction and rename minimal→maximal |

### Gabriel Theorem Chain (Ch6)
| PR | Title |
|----|-------|
| #2003 | Prove CoxeterInfrastructure type-changing iterated reflection functors (keystone) |

### Morita Theory (Ch9)
| PR | Title |
|----|-------|
| #1964 | Prove equivEndAlgEquiv k-linearity |
| #2004 | Prove basic_morita_regular_module_iso: F(B₁) ≅ B₂ |

### Other
| PR | Title |
|----|-------|
| #1981 | Refactor: restructure q2_nontrivial_decomp with correct product-compatible decomposition |
| #1987 | Define garnirSet, garnirElement, prove garnir_row_annihilates |
| #1993 | Prove helper lemmas for polytabloid basis straightening |
| #1996 | Wave 40 sorry landscape update |
| #1997 | Meditate wave 40 — pattern review + skill updates |
| #2008 | Review: close stale PRs and rebase broken CI PRs |

## Dependency Clusters

### Cluster A: Polytabloid Basis (Ch5, 7 sorries)
**Files:** PolytabloidBasis (6), TabloidModule (1)
**Key sorries:**
- `polytabloid_linearIndependent` — needs tabloid projection approach
- `column_standard_in_span'` — straightening algorithm
- 4 garnir/column helpers
- `polytabloid_syt_dominance` — PQ transformation dominance ordering
**Status:** Convention swap (#2002) caused +2 regression. Coset direction fixed (#1999). Active work on garnir infrastructure.

### Cluster B: Weyl Character Formula (Ch5, 4 sorries)
**Files:** Theorem5_22_1 (2), FormalCharacterIso (2)
**Key sorries:**
- `finrank_weight_eq_card_sum` — trace formula: weight finrank via Young symmetrizer
- `charValue_eq_spechtModuleCharacter` or stability — bridge between polynomial charValue and Specht module trace
- `iso_of_formalCharacter_eq` — isomorphism from formal character equality
- `formalCharacter_shift_of_weightSpace_finrank` — character shift formula
**Status:** Down 1 sorry from wave 40. Frobenius bridge (N=n case) proved (#2006). canonicalBP lemmas proved (#2014).

### Cluster C: Mackey Machine (Ch5, 4 sorries)
**Files:** Theorem5_27_1 (4)
**Remaining:** 4 sorry'd helpers in completeness proof scaffold:
1. `exists_character_in_rep` — simultaneous diagonalization / Maschke + Schur
2. `exists_simple_subrep` — nonzero FDRep has simple subrep (IsArtinianObject)
3. `exists_nonzero_map_from_induced` — Frobenius reciprocity construction
4. `hWχ_nz` — categorical bridge (weightSpace ≠ ⊥ → FDRep ≠ 0)
**Status:** Orbit injectivity proved (#2000). simple_fdRep_isIrreducible proved (#2009). Completeness scaffolded (#2019). Up 1 sorry from restructuring.

### Cluster D: Gabriel Theorem Chain (Ch6, 3 sorries)
**Files:** Corollary6_8_3 (1), Corollary6_8_4 (1), Problem6_9_1 (1)
**Status:** Major progress! CoxeterInfrastructure cleared (#2003), Problem6_1_5_theorem cleared, Theorem6_5_2 cleared. Down from 5 to 3 sorries. Remaining sorries are in the final corollaries and Problem6_9_1.

### Cluster E: Morita Theory (Ch9, 4 sorries)
**Files:** MoritaStructural (4)
**Key sorries:**
- Nakayama-style argument for F(B₁) surjection
- Module.Finite transport through equivalence
- Eilenberg-Watts k-linearity (×2: equivFunctorLinear + AlgEquiv scalar)
**Status:** Up from 2 to 4 due to restructuring exposing deeper Eilenberg-Watts gap. regular_module_iso proved (#2004). k-linearity partially proved (#1964).

### Cluster F: Convention Swap Regression (Ch5, 2 sorries)
**Files:** Proposition5_14_1 (2)
**Sorries:** Two proofs broken by Young symmetrizer convention swap from ColumnAntisymmetrizer * RowSymmetrizer to RowSymmetrizer * ColumnAntisymmetrizer.
**Status:** NEW regression. Clear fix path (adapt proofs to new convention).

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
| 41 | 25 | 11 | 577/583 (98.9%) | 2026-04-03 |

Wave 41 shows a mixed picture: +2 sorries (convention swap regressions) but −2 files and +6 items became sorry-free (items.json was stale). Item completion jumped from 97.9% to 98.9% after correcting stale entries. The file count (11) is at a project low.

## Strategic Recommendations

1. **Fix Proposition5_14_1 convention regression** (2 sorries) — Clear fix path: adapt proofs to new ColumnAntisymmetrizer * RowSymmetrizer convention. Quick win to recover from regression.

2. **Cluster D corollaries** (Corollary6_8_3, Corollary6_8_4) — With CoxeterInfrastructure now sorry-free (#2003), these may be unblocked. Check if the remaining sorries can now be closed.

3. **Mackey completeness helpers** (#1782, #2023) — 4 sorry'd helpers in Theorem5_27_1. Each is well-scoped. `hWχ_nz` (categorical bridge) is likely the easiest.

4. **PolytabloidBasis straightening** — 6 sorries, the largest cluster. Convention swap regression contributed +2. Active work needed on garnir infrastructure and linearIndependence.

5. **MoritaStructural Eilenberg-Watts** — 4 sorries all related to the same conceptual gap (k-linearity of category equivalences). May need a dedicated Eilenberg-Watts construction.
