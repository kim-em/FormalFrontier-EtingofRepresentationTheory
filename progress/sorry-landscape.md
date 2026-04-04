# Sorry Landscape Analysis — Wave 43

Generated 2026-04-04 by summarize session (issue #2086).

## Summary

**13 sorries** across 10 files. Down from 25 / 14 in wave 42: **−12 sorries, −4 files**. Chapters 3, 4, 7, 8 remain 100% sorry-free. 270 of 280 Lean files (96.4%) are sorry-free. 579/583 items (99.3%) sorry-free.

14 PRs merged since wave 42 (#2061–#2082). This was the largest single-wave sorry reduction since tracking began. Key changes:

- **Theorem5_27_1 sorry-free** (#2047, #2049, #2069) — Mackey machine: exists_character_in_rep + exists_nonzero_map_from_induced both proved. Cluster C eliminated.
- **FormalCharacterIso sorry-free** (#2070) — iso_of_formalCharacter_eq proved.
- **Proposition5_22_2 sorry-free** (#2077) — Weight space det-twist vanishing proved.
- **Corollary6_8_3 sorry-free** (#2080) — Recovery lemma and iteration tracking proved (2→0).
- **Theorem5_22_1 5→1** (#2068, #2075) — charValue stability chain proved (5→1 via #2068), then finrank_glWeightSpace_eq_restricted_trace proved (#2075). One sorry remains: iso_of_glWeightSpace_finrank_eq.
- **MoritaStructural 4→2** (#2073, #2082) — KLinearMoritaEquivalent bypass (4→3), then equivEndAlgEquiv scalar preservation proved (3→2).
- **Corollary6_8_4 1→1** — Admissible sinks condition proved (#2076), but core sorry remains (depends on CoxeterInfrastructure).
- **PolytabloidBasis 3→3** (#2078) — garnir_identity_expansion infrastructure: single-column case proved, blocker identified. Net sorry count unchanged.

**Net sorry change: −12.** Largest single-wave reduction. Four files became sorry-free. Two clusters eliminated (C: Mackey Machine, partial B: Weyl Character).

**Definition-level sorries: 0.** All mathematical objects are constructed. No regression.

## Chapter Breakdown

| Chapter | Sorries | Files | Delta from Wave 42 |
|---------|---------|-------|---------------------|
| Ch2 | 1 | 1 | 0 |
| Ch5 | 5 | 3 | −8 sorries, −3 files |
| Ch6 | 5 | 5 | −2 sorries, −1 file |
| Ch9 | 2 | 1 | −2 sorries, 0 files |

## Files That Became Sorry-Free Since Wave 42

1. **Theorem5_27_1.lean** — 2→0. Mackey machine completed: exists_character_in_rep (#2047) and exists_nonzero_map_from_induced (#2049) proved after CI fixes (#2069).
2. **FormalCharacterIso.lean** — 1→0. iso_of_formalCharacter_eq proved via formal character injectivity (#2070).
3. **Proposition5_22_2.lean** — 1→0. Weight space det-twist vanishing proved (#2077).
4. **Corollary6_8_3.lean** — 2→0. Recovery lemma + iteration tracking proved (#2080).

## Per-File Sorry Detail

| File | Sorries | Nature | Delta from W42 |
|------|---------|--------|----------------|
| PolytabloidBasis | 3 | polytabloid_linearIndependent + column_standard_in_span' + garnir_identity_expansion | 0 |
| MoritaStructural (Ch9) | 2 | exists_surjection_with_trivial_kernel_head + Module.Finite transport | **−2** |
| Theorem5_22_1 | 1 | iso_of_glWeightSpace_finrank_eq (isomorphism from equal weight space finranks) | **−4** |
| TabloidModule | 1 | polytabloid_syt_dominance (PQ transformation) | 0 |
| Theorem2_1_2 | 1 | Gabriel's theorem (finite rep type ↔ Dynkin) | 0 |
| Corollary6_8_4 | 1 | indecomposable_of_positive_root (depends on CoxeterInfrastructure) | 0 |
| CoxeterInfrastructure | 1 | one_round_or_simpleRoot (universe constraint blocker) | 0 |
| Problem6_1_5_theorem | 1 | Theorem_6_1_5 (finite type ↔ Dynkin) | 0 |
| Problem6_9_1 | 1 | off_diagonal_nilpotent_product_decomp (compatible chain basis) | 0 |
| Theorem6_5_2 | 1 | Theorem_6_5_2c_bijection (dim vector bijection) | 0 |

## Merged PRs Since Wave 42 (14)

### Weyl Character / Young Symmetrizer (Ch5)
| PR | Title |
|----|-------|
| #2068 | Prove charValue stability chain in Theorem5_22_1 (5→1 sorry) |
| #2070 | Prove iso_of_formalCharacter_eq in FormalCharacterIso (1→0 sorry) |
| #2075 | Prove finrank_glWeightSpace_eq_restricted_trace in Theorem5_22_1 (2→1 sorry) |
| #2077 | Prove weight space det-twist vanishing in Proposition5_22_2 (1→0 sorry) |

### Schur-Weyl / Polytabloid (Ch5)
| PR | Title |
|----|-------|
| #2078 | Progress: garnir_identity_expansion infrastructure (single-column case proved) |

### Mackey Machine (Ch5)
| PR | Title |
|----|-------|
| #2047 | Prove exists_character_in_rep (2→1 sorry) |
| #2049 | Prove exists_nonzero_map_from_induced: Mackey Frobenius reciprocity |
| #2069 | Fix CI on Mackey machine PRs #2047 and #2049 |

### Gabriel Theorem Chain (Ch6)
| PR | Title |
|----|-------|
| #2074 | Prove F⁻ functoriality reflectionFunctorMinus_map_iso (1→0 sorry) |
| #2076 | Prove admissible sinks condition for replicated orderings |
| #2080 | Prove Corollary6_8_3 recovery lemma and iteration tracking (2→0 sorry) |

### Morita Theory (Ch9)
| PR | Title |
|----|-------|
| #2073 | KLinearMoritaEquivalent bypass for MoritaStructural (4→3 sorry) |
| #2082 | Prove equivEndAlgEquiv scalar preservation in MoritaStructural (3→2 sorry) |

### Meditate / Infrastructure
| PR | Title |
|----|-------|
| #2061 | Wave 42 pattern review and skill updates |

## Open PRs (pending merge)

| PR | Title | Status |
|----|-------|--------|
| #2081 | Prove iso_of_glWeightSpace_finrank_eq in Theorem5_22_1 (1→0 sorry) | CI cancelled — needs re-run |

## Active Work Items (claimed)

| Issue | Title | Impact |
|-------|-------|--------|
| #2083 | Prove compatible_chain_basis_decomp (Problem6_9_1) | 1→0 sorry |

## Dependency Clusters

### Cluster A: Polytabloid Basis (Ch5, 4 sorries)
**Files:** PolytabloidBasis (3), TabloidModule (1)
**Key sorries:**
- `polytabloid_linearIndependent` — needs tabloid projection approach
- `column_standard_in_span'` — straightening algorithm
- `garnir_identity_expansion` — multi-column Garnir expansion (single-column case done, #2078)
- `polytabloid_syt_dominance` — PQ transformation dominance ordering
**Status:** Unchanged at 4. Single-column garnir case proved (#2078) but multi-column blocker identified. These are the deepest combinatorial sorries in the project.

### Cluster B: Weyl Character Formula (Ch5, 1 sorry)
**Files:** Theorem5_22_1 (1)
**Remaining:**
- `iso_of_glWeightSpace_finrank_eq` — isomorphism from equal weight space finranks
**Status:** Dramatically reduced from 7→1. Open PR #2081 targets this last sorry (CI needs re-run). If merged, Cluster B is eliminated.

### Cluster D: Gabriel Theorem Chain (Ch6, 5 sorries)
**Files:** Corollary6_8_4 (1), CoxeterInfrastructure (1), Problem6_1_5_theorem (1), Problem6_9_1 (1), Theorem6_5_2 (1)
**Status:** Corollary6_8_3 eliminated (2→0, #2080). F⁻ functoriality proved (#2074). Admissible sinks proved (#2076). Corollary6_8_4 still blocked by CoxeterInfrastructure universe constraint. Active work on Problem6_9_1 compatible chain basis (#2083).
**Dependency chain:** CoxeterInfrastructure → Corollary6_8_4 (blocked). Problem6_1_5_theorem and Theorem6_5_2 are independent.

### Cluster E: Morita Theory (Ch9, 2 sorries)
**Files:** MoritaStructural (2)
**Remaining:**
- `exists_surjection_with_trivial_kernel_head` — Nakayama-style surjection (progenerator theory)
- `Module.Finite` transport through equivalence
**Status:** Down from 4→2. KLinearMoritaEquivalent bypass (#2073) and scalar preservation (#2082) eliminated 2 sorries. Remaining 2 are tightly coupled: both need progenerator theory or composition series infrastructure.

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
| 43 | 13 | 10 | 579/583 (99.3%) | 2026-04-04 |

*Wave 41 corrected from reported 25/11 to actual 28/14.

Wave 43 is the largest single-wave reduction: −12 sorries, −4 files. The project crossed the 99% items-sorry-free threshold. Four complete files became sorry-free. Two clusters (C: Mackey Machine, partial B: Weyl Character) essentially eliminated. The remaining 13 sorries are concentrated in hard combinatorial proofs (Polytabloid Basis) and infrastructure gaps (Morita progenerator theory, Gabriel chain universe constraints).

## Strategic Recommendations

1. **Re-run CI on PR #2081** (iso_of_glWeightSpace_finrank_eq) — This would bring Theorem5_22_1 to 0 sorries, fully eliminating Cluster B. Highest-priority low-effort action.

2. **Problem6_9_1 compatible chain basis** (#2083, active) — If successful, reduces Cluster D by 1. The compatible chain basis is a concrete linear algebra argument.

3. **CoxeterInfrastructure universe constraint** — one_round_or_simpleRoot blocks Corollary6_8_4. May need architectural rethink (universe polymorphism or restructuring the induction). This is the key blocker for Cluster D.

4. **PolytabloidBasis** — 3 sorries, all deep combinatorial proofs. The garnir multi-column case is the current frontier. polytabloid_linearIndependent and column_standard_in_span' are the hardest remaining sorries in the project.

5. **MoritaStructural progenerator theory** — 2 sorries need either: (a) progenerator infrastructure showing equivalences preserve f.g. projective generators, or (b) Module.Finite transfer for k-linear equivalences. Both require substantial new infrastructure.

6. **Theorem2_1_2 / Problem6_1_5_theorem / Theorem6_5_2** — Three independent Cluster D sorries. Each is a standalone proof that could be tackled independently. Gabriel's theorem (Theorem2_1_2) is the most impactful but hardest.
