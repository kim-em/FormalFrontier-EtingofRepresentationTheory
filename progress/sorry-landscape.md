# Sorry Landscape Analysis — Wave 29

Generated 2026-03-23 by summarize session (issue #1608).

## Summary

**61 sorries** across 26 files. Down from 66 sorries / 27 files in wave 28 (−5 sorries, −1 file). Chapters 3, 4, 7, 8 remain 100% sorry-free. 240 of 266 Lean files (90.2%) are sorry-free. 562 of 583 items (96.4%) sorry-free.

18 PRs merged since wave 28. Key wins:
- **Theorem 2.1.1 (sl(2,ℂ) complete reducibility)** became sorry-free (PR #1611)
- **GL2NormalizerInfra** became sorry-free (PR #1612)
- **Theorem5_26_1** reduced from 3 → 2 sorries (PR #1612, frobenius_char_reciprocity proved)
- **Proposition6_6_6** reduced from 5 → 3 sorries (PR #1598, hψ_inj + hdim proved)
- **FDRep bridge** completed: spechtModuleFDRep_simple proved (PR #1601)
- **CoxeterInfrastructure** created (PR #1605) — 2 sorries, foundation for Gabriel theorem chain
- **Problem6_9_1** partial: 2/3 nilpotent_nontrivial_decomp cases proved (PR #1606)

| Tier | Count | % | Description |
|------|-------|---|-------------|
| Tier 1 — Achievable | 1 | 2% | Standard math, Mathlib APIs exist |
| Tier 2 — Hard but tractable | 14 | 23% | Non-trivial proofs, novel approaches needed |
| Tier 3 — Blocked on infrastructure | ~29 | 47% | Missing Mathlib or project infrastructure |
| Tier 4 — Deep blockers | ~17 | 28% | SchurModule, Clifford theory, major gaps |

## Chapter Breakdown

| Chapter | Sorries | Files | Delta from Wave 28 |
|---------|---------|-------|---------------------|
| Ch2 | 1 | 1 | −1 sorry (Theorem2_1_1 now sorry-free) |
| Ch5 | 36 | 12 | −3 sorries, −1 file (GL2NormalizerInfra now sorry-free) |
| Ch6 | 19 | 8 | −1 sorry (+1 new file CoxeterInfra, −2 Prop6_6_6) |
| Ch9 | 3 | 3 | 0 |
| Infra | 2 | 2 | 0 |

## Files That Became Sorry-Free Since Wave 28

- **Theorem2_1_1.lean** — sl(2,ℂ) complete reducibility. Both parts (i) and (ii) now proved. PR #1611 completed the final case.
- **GL2NormalizerInfra.lean** — GL₂(𝔽_q) normalizer theory. normalizer_card (|N_{GL₂}(K)| = 2|K|) proved. PR #1612.

## Tier 1 — Achievable (1 sorry)

### Theorem5_15_1 — 1 sorry
**File:** `Chapter5/Theorem5_15_1.lean`
**Nature:** `alternating_kostka_eq_zero_of_strict_dom` — alternating Kostka identity for strict dominance.
**Status:** Issue #1580 (unclaimed). FDRep bridge now complete (#1591 closed, PR #1601). Dependency: Vandermonde orthogonality (#1592).

## Tier 2 — Hard but Tractable (14 sorries)

### Theorem_Dynkin_classification — 6 sorries
**File:** `Chapter6/Theorem_Dynkin_classification.lean`
**Nature:** n≥5 arm extraction and exceptional type cases (D_n, E₆, E₇, E₈).

### Theorem5_25_2 — 6 sorries
**File:** `Chapter5/Theorem5_25_2.lean`
**Nature:** Principal series character computation helper lemmas.

### Proposition6_6_6 — 3 sorries
**File:** `Chapter6/Proposition6_6_6.lean`
**Nature:** Reflection functor round-trip (F⁻F⁺V ≅ V). Down from 5 → 3 (PR #1598). Remaining 3 blocked by Decidable.casesOn opacity.

### CoxeterInfrastructure — 2 sorries
**File:** `Chapter6/CoxeterInfrastructure.lean`
**Nature:** New infrastructure for Gabriel theorem chain. admissibleOrdering_exists and coxeterElement_power_sink.

### Proposition5_21_1 — 2 sorries
**File:** `Chapter5/Proposition5_21_1.lean`
**Nature:** Character expansion in terms of Schur polynomials. 1 definition-level sorry (kostkaNumber).

### Problem6_9_1 — 2 sorries
**File:** `Chapter6/Problem6_9_1.lean`
**Nature:** `decomp_of_ker_sum_ge_two` — Q₂-rep decomposability. 2/3 nilpotent decomp cases proved (PR #1606).

### Problem6_1_5_theorem — 2 sorries
**File:** `Chapter6/Problem6_1_5_theorem.lean`
**Nature:** IsFiniteTypeQuiver definition + theorem. 1 definition-level sorry.

### PolytabloidBasis — 2 sorries
**File:** `Chapter5/PolytabloidBasis.lean`
**Nature:** Linear independence + straightening lemma.

### Lemma5_25_3 — 1 sorry
**File:** `Chapter5/Lemma5_25_3.lean`
**Nature:** Elliptic norm-squared sum computation.

### Proposition5_22_2 — 1 sorry
**File:** `Chapter5/Proposition5_22_2.lean`
**Nature:** Schur polynomial character formula. Blocked on SchurModule.

### Corollary6_8_3 — 1 sorry
**File:** `Chapter6/Corollary6_8_3.lean`
**Nature:** Indecomposable quiver reps have positive roots as dimension vectors.

### Corollary6_8_4 — 1 sorry
**File:** `Chapter6/Corollary6_8_4.lean`
**Nature:** Bijection between indecomposable reps and positive roots. Down from 3 → 1.

### Proposition6_6_7 — 1 sorry
**File:** `Chapter6/Proposition6_6_7.lean`
**Nature:** Reflection functor preserves indecomposability (source case).

### Theorem6_5_2 — 1 sorry
**File:** `Chapter6/Theorem6_5_2.lean`
**Nature:** Part (c) uniqueness of indecomposable decomposition.

## Tier 3 — Blocked on Infrastructure (~29 sorries)

### Blocker Cluster 1: SchurModule & Characters (Ch5, ~20 sorries)
**Files:** Theorem5_23_2 (9), Theorem5_22_1 (3), PolytabloidBasis (2), Theorem5_18_4 (4), Proposition5_21_1 (2)
**Missing:** Concrete SchurModule definition. Everything downstream blocked.

### Blocker Cluster 2: Theorem5_25_2 Principal Series (Ch5, 6 sorries)
**File:** Theorem5_25_2
**Status:** Parts 1, 2, 3a have complete proof terms. 6 helper lemma sorries remain.

### Blocker Cluster 3: Theorem5_26_1 Artin's Theorem (Ch5, 2 sorries)
**File:** Theorem5_26_1
**Status:** Down from 3 → 2 (PR #1612). `class_fun_vanishes_on_subgroup_of_orthogonal` and `artin_Q_span_of_induced_chars` remain.

### Blocker Cluster 4: Gabriel's Theorem (Ch6, ~8 sorries)
**Files:** Corollary6_8_3 (1), Corollary6_8_4 (1), Problem6_1_5_theorem (2), Proposition6_6_7 (1), Theorem6_5_2 (1), CoxeterInfrastructure (2)
**Progress:** CoxeterInfrastructure created (PR #1605). exists_sink_of_dynkin_orientation proved (PR #1607). Proposition6_6_6 reduced.

### Blocker Cluster 5: Finite-Dimensional Algebras (Ch9, 3 sorries)
**Files:** Theorem9_2_1 (1), MoritaStructural (1), Example9_4_4 (1)
**Status:** Unchanged from wave 28. Corollary9_7_3 was already sorry-free.

## Tier 4 — Deep Blockers (~17 sorries)

### Mackey Machine (Ch5, 5 sorries)
**File:** Theorem5_27_1
**Missing:** Clifford theory infrastructure. No path without ~500 lines of new theory.

### GL₂(𝔽_q) Classification residual (Ch5, 6 sorries)
**File:** Theorem5_25_2 (helper lemmas)
**Missing:** Character computation helpers.

### Gabriel's Theorem Classification (Ch2, 1 sorry)
**File:** Theorem2_1_2
**Missing:** Full Gabriel's theorem depends on Ch6 Gabriel cluster.

### Morita/Basic Algebra Infrastructure (2 sorries)
**Files:** Infrastructure/BasicAlgebraExistence (1), Infrastructure/MoritaStructural (1)
**Missing:** Existence of basic Morita-equivalent algebra.

### Coxeter element infrastructure (2 sorries)
**File:** CoxeterInfrastructure.lean
**Status:** New file created (PR #1605). `admissibleOrdering_exists` and `coxeterElement_power_sink` need proofs.

## Definition-Level Sorries (Regression Check)

The following definition-level sorries remain. These make downstream theorems vacuous:

1. **Theorem5_22_1.lean:38** — `SchurModule` is entirely sorry'd (`FDRep k ... := sorry`)
2. **Theorem5_22_1.lean:46** — `schurPolynomial` sorry'd (`MvPolynomial ... := sorry`)
3. **Theorem5_23_2.lean:62,65,68** — `AlgIrrepGL` instances (AddCommGroup, Module, Finite) sorry'd
4. **Theorem5_23_2.lean:76,79** — `AlgIrrepGLDual` instances sorry'd
5. **Proposition5_21_1.lean:334** — `kostkaNumber` sorry'd (`ℚ := sorry`)
6. **Problem6_1_5_theorem.lean:33** — `IsFiniteTypeQuiver` sorry'd (`Prop := sorry`)

These are the highest-priority blockers. Until SchurModule is constructed (~20 downstream sorries are vacuous).

## Strategic Recommendations

1. **Biggest single win:** Theorem5_15_1 (#1580). Only 1 sorry for entire Frobenius character formula. FDRep bridge now complete. Vandermonde orthogonality (#1592) is the key dependency.

2. **Highest ROI infrastructure:** Coxeter element proofs in CoxeterInfrastructure.lean. Unblocks Gabriel theorem chain (~8 sorries in Ch6).

3. **Critical path:** SchurModule remains the mega-blocker. ~20 sorries (33%) transitively blocked. This is the project's critical path and the hardest remaining work.

4. **Steady progress:** −5 sorries since wave 28. Two files became sorry-free. The decomposition strategy continues working well.

5. **Milestone reached:** Theorem 2.1.1 (sl(2,ℂ) complete reducibility) is now fully proved — a significant mathematical result.
