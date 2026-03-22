# Sorry Landscape Analysis — Wave 28

Generated 2026-03-22 by review session (issue #1595).

## Summary

**66 sorries** across 27 files. Down from 75 sorries / 28 files in wave 27 (−9 sorries, −1 file). Chapters 3, 4, 7, 8 remain 100% sorry-free. 238 of 265 Lean files (90%) are sorry-free.

Key changes since wave 27:
- **Corollary9_7_3.lean** became sorry-free (sorry pushed to infrastructure)
- Theorem2_1_1 reduced from 2 → 1 sorry (complement_case_sub proved)
- Corollary6_8_3 reduced from 3 → 2 sorries (base case proved via IsOrientationOf)
- Corollary6_8_4 reduced from 3 → 1 sorry (strong induction restructure)
- Theorem9_2_1 reduced from 2 → 1 sorry
- Ch9 reduced from 5 → 3 sorries total
- Lemma5_25_3 reduced from 2 → 1 sorry
- Theorem5_26_1 reduced from 4 → 3 sorries

| Tier | Count | % | Description |
|------|-------|---|-------------|
| Tier 1 — Achievable | 2 | 3% | Standard math, Mathlib APIs exist |
| Tier 2 — Hard but tractable | 14 | 21% | Non-trivial proofs, novel approaches needed |
| Tier 3 — Blocked on infrastructure | ~33 | 50% | Missing Mathlib or project infrastructure |
| Tier 4 — Deep blockers | ~17 | 26% | SchurModule, Clifford theory, major gaps |

## Chapter Breakdown

| Chapter | Sorries | Files | Delta from Wave 27 |
|---------|---------|-------|---------------------|
| Ch2 | 2 | 2 | −1 sorry |
| Ch5 | 39 | 12 | −2 sorries |
| Ch6 | 20 | 8 | −3 sorries |
| Ch9 | 3 | 3 | −2 sorries, −1 file |
| Infra | 2 | 2 | −1 sorry |

## Files That Became Sorry-Free Since Wave 27

- **Corollary9_7_3.lean** — Ch9 Morita equivalence corollary (sorry pushed to Infrastructure/BasicAlgebraExistence)

## Tier 1 — Achievable (2 sorries)

### Theorem2_1_1 — 1 sorry
**File:** `Chapter2/Theorem2_1_1.lean`
**Nature:** sl(2) complete reducibility — main induction step.
**Status:** Reduced from 2 to 1. `complement_case_sub` N=W case proved. Issue #1541 (claimed, active).

### Theorem5_15_1 — 1 sorry
**File:** `Chapter5/Theorem5_15_1.lean`
**Nature:** `alternating_kostka_eq_zero_of_strict_dom` — alternating Kostka identity for strict dominance.
**Status:** Issue #1580 (unclaimed). Blocked on Specht module FDRep bridge (#1591, claimed) and Vandermonde orthogonality (#1592, blocked).

## Tier 2 — Hard but Tractable (14 sorries)

### Lemma5_25_3 — 1 sorry
**File:** `Chapter5/Lemma5_25_3.lean`
**Nature:** Elliptic norm-squared sum. Reduced from 2 → 1.
**Status:** GL₂ normalizer infrastructure (#1517, claimed).

### GL2NormalizerInfra — 2 sorries
**File:** `Chapter5/GL2NormalizerInfra.lean`
**Nature:** GL₂ normalizer cardinality helpers.
**Status:** Active work via #1517.

### Theorem_Dynkin_classification — 6 sorries
**File:** `Chapter6/Theorem_Dynkin_classification.lean`
**Nature:** n≥5 arm extraction and exceptional type cases (D_n, E₆, E₇, E₈).

### Proposition6_6_6 — 5 sorries
**File:** `Chapter6/Proposition6_6_6.lean`
**Nature:** Reflection functor round-trip (F⁻F⁺V ≅ V).
**Status:** Issue #1594 targets 2 tractable sorries (hψ_inj, hdim). 3 remaining blocked by Decidable.casesOn opacity.

### Problem6_9_1 — 1 sorry
**File:** `Chapter6/Problem6_9_1.lean`
**Nature:** `decomp_of_ker_sum_ge_two` — Q₂-rep decomposability from kernel dimension.
**Status:** Issue #1572 (unclaimed). Requires nilpotent cyclic decomposition.

### Proposition5_21_1 — 2 sorries
**File:** `Chapter5/Proposition5_21_1.lean`
**Nature:** Character expansion in terms of Schur polynomials.

### Proposition5_22_2 — 1 sorry
**File:** `Chapter5/Proposition5_22_2.lean`
**Nature:** Schur polynomial character formula.

## Tier 3 — Blocked on Infrastructure (~33 sorries)

### Blocker Cluster 1: SchurModule & Characters (Ch5, ~20 sorries)
**Files:** Theorem5_23_2 (9), Theorem5_22_1 (3), PolytabloidBasis (2), Theorem5_18_4 (4), Proposition5_21_1 (2)
**Missing:** Concrete SchurModule definition. Everything downstream blocked.

### Blocker Cluster 2: Theorem5_25_2 Principal Series (Ch5, 6 sorries)
**File:** Theorem5_25_2
**Status:** Parts 1, 2, 3a have complete proof terms. 6 helper lemma sorries remain.

### Blocker Cluster 3: Theorem5_26_1 Artin's Theorem (Ch5, 3 sorries)
**File:** Theorem5_26_1
**Status:** Down from 4 → 3 sorries. Forward direction helpers decomposed.

### Blocker Cluster 4: Gabriel's Theorem (Ch6, ~8 sorries)
**Files:** Corollary6_8_3 (2), Corollary6_8_4 (1), Problem6_1_5_theorem (2), Proposition6_6_7 (2), Theorem6_5_2 (1)
**Missing:** Coxeter element infrastructure (blocker #1589). Reflection functor round-trip (Prop 6.6.6).
**Progress:** IsOrientationOf added, base case proved, Corollary6_8_4 reduced from 3→1.

### Blocker Cluster 5: Finite-Dimensional Algebras (Ch9, 3 sorries)
**Files:** Theorem9_2_1 (1), MoritaStructural (1), Example9_4_4 (1)
**Status:** Down from 5 → 3. Corollary9_7_3 now sorry-free. Infrastructure files hold remaining sorries.

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

### Coxeter element infrastructure (blocker #1589)
New blocker identified this wave. Needed for Gabriel theorem chain. See issue for analysis.

## Strategic Recommendations

1. **Highest ROI:** Theorem2_1_1 (1 sorry, sl(2) complete reducibility). Active work in #1541.

2. **Biggest single-item impact:** Theorem5_15_1 (#1580). Only 1 sorry remaining for entire Frobenius character formula. Dependency chain: #1591 → #1592 → #1593 → #1580.

3. **Unblock cascade:** Proposition6_6_6 (#1594, 2 tractable sorries). Unblocks downstream Gabriel theorem chain.

4. **Steady progress:** −9 sorries since wave 27. The decomposition strategy continues working well. Ch9 chain cleaned up significantly.

5. **SchurModule remains the mega-blocker:** ~20 sorries (30%) transitively blocked. This is the project's critical path.

6. **New blocker documented:** Coxeter element infrastructure (#1589) now properly scoped. This is the root cause of the Gabriel theorem chain's remaining sorries.
