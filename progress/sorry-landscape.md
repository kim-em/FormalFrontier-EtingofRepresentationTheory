# Sorry Landscape Analysis — Wave 34

Generated 2026-03-24 by review session (issue #1710).

## Summary

**44 sorries** across 22 files. Up from 43 / 22 in wave 33 (+1 sorry net, same file count). Chapters 3, 4, 7, 8 remain 100% sorry-free. 246 of 268 Lean files (91.8%) are sorry-free. 567 of 583 items (97.2%) sorry-free.

6 PRs merged since wave 33 (#1701, #1704, #1705, #1706, #1709). Key changes:
- **Theorem5_25_2.lean** became sorry-free — `principalSeries_iso_swap` proved (PR #1705). GL₂(𝔽_q) principal series classification is now complete.
- **PowerSumCauchyBilinear.lean** added (PRs #1701, #1704) with 2 new sorrys: `fullCauchyProd_coeff_eq_card` and `double_counting`. These are infrastructure for the bilinear Cauchy identity.
- PR #1706 added FDRep morphism extensionality skill patterns (no sorry change)
- PR #1709 was a meditate session reviewing patterns (no sorry change)

| Tier | Count | % | Description |
|------|-------|---|-------------|
| Tier 1 — Achievable | 3 | 7% | Standard math, clear path exists |
| Tier 2 — Hard but tractable | 1 | 2% | Non-trivial proofs, self-contained |
| Tier 3 — Blocked on SchurModule | ~21 | 48% | Missing SchurModule definition |
| Tier 4 — Deep blockers | ~19 | 43% | Clifford theory, Gabriel chain, Morita |

## Chapter Breakdown

| Chapter | Sorries | Files | Delta from Wave 33 |
|---------|---------|-------|---------------------|
| Ch2 | 1 | 1 | 0 |
| Ch5 | 29 | 10 | +1 sorry, +1 file (PowerSumCauchyBilinear new; Theorem5_25_2 sorry-free) |
| Ch6 | 10 | 8 | 0 |
| Ch9 | 2 | 2 | 0 |
| Infra | 2 | 2 | 0 |

## Files That Became Sorry-Free Since Wave 33

- **Theorem5_25_2.lean** — GL₂(𝔽_q) principal series: irreducibility, non-isomorphism, classification. PR #1705 proved `principalSeries_iso_swap` (V(χ₁,χ₂) ≅ V(χ₂,χ₁)), the last sorry. This completes the entire GL₂ principal series formalization.

## Open PRs (In-Flight Work)

No open PRs.

## Tier 1 — Achievable (3 sorries)

### Theorem5_15_1 — 1 sorry
**File:** `Chapter5/Theorem5_15_1.lean`
**Nature:** `alternatingKostka_norm_sq_eq_one` — proves ∑_ν L(λ,ν)² = 1. Key step in the Frobenius character formula.
**Status:** PowerSumCauchyIdentity is sorry-free, providing the `cauchyRHS_coeff_diag` infrastructure. Issue #1688 created for this work.

### PowerSumCauchyBilinear — 2 sorries (NEW)
**File:** `Chapter5/PowerSumCauchyBilinear.lean`
**Nature:** `fullCauchyProd_coeff_eq_card` (coefficient = matrix count) and `double_counting` (core combinatorial identity). These are the bilinear extension of the Cauchy identity.
**Status:** Issue #1707 covers these. Infrastructure is clean (240 lines). The `powerSum_bilinear_coeff` theorem correctly reduces to these two sorrys.

## Tier 2 — Hard but Tractable (1 sorry)

### Problem6_9_1 — 1 sorry
**File:** `Chapter6/Problem6_9_1.lean`
**Nature:** `decomp_of_ker_sum_ge_two` — Q₂-rep decomposability via transfer from AB-invariant to Q₂-invariant decomposition. Issue #1691 created (compatible chain basis approach).

## Tier 3 — Blocked on SchurModule (~21 sorries)

### SchurModule & Characters (Ch5, 21 sorries)
**Files:** Theorem5_23_2 (9), Theorem5_18_4 (4), Theorem5_22_1 (3), PolytabloidBasis (2), Proposition5_21_1 (2), Proposition5_22_2 (1)
**Missing:** Concrete SchurModule definition (Theorem5_22_1:38 is `sorry`). Everything downstream is blocked. This is the project's critical path — 48% of all remaining sorries.

## Tier 4 — Deep Blockers (~19 sorries)

### Mackey Machine (Ch5, 5 sorries)
**File:** Theorem5_27_1
**Missing:** Clifford theory infrastructure. No path without ~500 lines of new theory.

### Gabriel's Theorem Chain (Ch6, 9 sorries)
**Files:** Corollary6_8_3 (1), Corollary6_8_4 (1), Problem6_1_5_theorem (2), Proposition6_6_6 (2), Proposition6_6_7 (1), Theorem6_5_2 (1), CoxeterInfrastructure (1)
**Status:** Unchanged. Chain blocked on `indecomposable_reduces_to_simpleRoot` (type-changing iterated reflection functor) and `admissibleOrdering_exists`.

### Gabriel's Theorem Classification (Ch2, 1 sorry)
**File:** Theorem2_1_2
**Missing:** Full Gabriel's theorem depends on Ch6 Gabriel cluster.

### Morita/Basic Algebra Infrastructure (3 sorries)
**Files:** MoritaStructural Ch9 (1), BasicAlgebraExistence (1), MoritaStructural Infra (1)
**Missing:** Existence of basic Morita-equivalent algebra. Progenerator-to-algebra construction.

### Homological Dimension (Ch9, 1 sorry)
**File:** Example9_4_4
**Status:** `homologicalDimension (MvPolynomial (Fin n) k) = n` — standalone result.

## Definition-Level Sorries (Regression Check)

The following definition-level sorries remain. These make downstream theorems vacuous:

1. **Theorem5_22_1.lean:38** — `SchurModule` is entirely sorry'd (`FDRep k ... := sorry`)
2. **Theorem5_22_1.lean:46** — `schurPolynomial` sorry'd (`MvPolynomial ... := sorry`)
3. **Theorem5_23_2.lean:59** — `AlgIrrepGL` sorry'd (type definition)
4. **Theorem5_23_2.lean:62,65,68** — `AlgIrrepGL` instances (AddCommGroup, Module, Finite) sorry'd
5. **Theorem5_23_2.lean:73** — `AlgIrrepGLDual` sorry'd (type definition)
6. **Theorem5_23_2.lean:76,79** — `AlgIrrepGLDual` instances sorry'd
7. **Proposition5_21_1.lean:334** — `kostkaNumber` sorry'd (`ℚ := sorry`)
8. **Problem6_1_5_theorem.lean:33** — `IsFiniteTypeQuiver` sorry'd (`Prop := sorry`)

No new definition-level sorries since Wave 30. Until SchurModule is constructed, ~21 downstream sorries (48%) are vacuous.

## Proof Quality Notes (Wave 34 Audit)

### Theorem5_25_2.lean (2958 lines)
- **Linter fixes applied**: 4 `show` → `change` replacements, 1 unused variable prefixed, 2 no-op `congr 1` removed
- **Remaining warnings**: 2 `congr 1` flagged as no-op by linter but actually needed (remove breaks `ext`), 1 flexible `simp` warning
- **File size concern**: At 2958 lines, approaching split threshold. Character computation section (`principalSeries_char_diagElt`) could be extracted. Not urgent — file is logically cohesive.
- **Heartbeat usage**: `set_option maxHeartbeats 4000000` at line 1583 is aggressive. 800k and 1.6M settings elsewhere are within normal range.
- **Stale comment**: Line 1192 says "For now, sorry the augmentation computation" but the augmentation is proved. Cosmetic only.

### PowerSumCauchyBilinear.lean (240 lines)
- Clean, well-structured. Good docstrings.
- `powerSum_bilinear_coeff` correctly reduces to the two sorry'd lemmas.
- No redundant tactics or AI-generated bloat detected.

## Per-File Sorry Detail

| File | Sorries | Nature | Delta |
|------|---------|--------|-------|
| Theorem5_23_2 | 9 | SchurModule instances + character formulas | 0 |
| Theorem5_27_1 | 5 | Mackey machine (Clifford theory) | 0 |
| Theorem5_18_4 | 4 | Young symmetrizer character formula | 0 |
| Theorem5_22_1 | 3 | SchurModule + schurPolynomial defs + theorem | 0 |
| PowerSumCauchyBilinear | 2 | Bilinear Cauchy identity core lemmas | **NEW** |
| PolytabloidBasis | 2 | Linear independence + straightening | 0 |
| Proposition6_6_6 | 2 | Reflection functor naturality cases | 0 |
| Proposition5_21_1 | 2 | kostkaNumber def + character expansion | 0 |
| Problem6_1_5_theorem | 2 | IsFiniteTypeQuiver def + iff theorem | 0 |
| Theorem5_15_1 | 1 | Alternating Kostka norm squared | 0 |
| Proposition5_22_2 | 1 | Schur polynomial character formula | 0 |
| Corollary6_8_3 | 1 | Indecomposable → positive root | 0 |
| Corollary6_8_4 | 1 | Bijection: indec reps ↔ positive roots | 0 |
| CoxeterInfrastructure | 1 | Admissible ordering existence | 0 |
| Proposition6_6_7 | 1 | Reflection functor preserves indec | 0 |
| Theorem6_5_2 | 1 | Indecomposable decomposition uniqueness | 0 |
| Problem6_9_1 | 1 | Q₂-rep decomposability | 0 |
| BasicAlgebraExistence | 1 | Basic algebra existence | 0 |
| MoritaStructural (Ch9) | 1 | Morita equivalence construction | 0 |
| MoritaStructural (Infra) | 1 | Morita structural infrastructure | 0 |
| Example9_4_4 | 1 | Homological dimension of polynomial ring | 0 |
| Theorem2_1_2 | 1 | Gabriel's theorem statement | 0 |

**Removed since Wave 33:** Theorem5_25_2 (was 1 sorry, now 0)
**Added since Wave 33:** PowerSumCauchyBilinear (2 sorrys, new file)

## Strategic Recommendations

1. **Highest-ROI unclaimed work:** Issue #1688 (`alternatingKostka_norm_sq_eq_one` in Theorem5_15_1) — PowerSumCauchyIdentity is sorry-free, so the infrastructure is ready. This would close the Frobenius character formula.

2. **New Cauchy bilinear sorrys:** Issue #1707 covers the 2 PowerSumCauchyBilinear sorrys (`fullCauchyProd_coeff_eq_card`, `double_counting`). These are standard combinatorial arguments — achievable.

3. **Problem6_9_1:** Issue #1691 proposes compatible chain basis approach. Last sorry in the Q₂-rep decomposability proof.

4. **Critical path unchanged:** SchurModule remains the mega-blocker. ~21 sorries (48%) transitively blocked. This is the project's critical path and the hardest remaining work.

5. **Milestone:** Theorem5_25_2 becoming sorry-free completes the GL₂(𝔽_q) principal series formalization — from 8 sorrys four waves ago to 0. This is the largest individual proof completion in recent project history.

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
