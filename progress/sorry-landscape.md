# Sorry Landscape Analysis — Wave 55

Generated 2026-04-24 by summarize session (issue #2469).

## Summary

**7 sorries** across 4 files (down from 14/4 in wave 54). The headline
movement is the **Ẽ/T scaffolding collapse** (PR #2441 collapsed ten
refuted sub-sorries into three top-level placeholder sorries) plus
**Wall 2 (D̃_n) moving off the framework wall** into a single mechanical
residual.

282 of 286 Lean files (98.6%) are sorry-free. 582/583 items (99.8%) sorry-free.

**Definition-level sorries: 0.** All mathematical objects are constructed.

### Key story for wave 55

- **Wall 1 (Ẽ/T framework, Kim's decision):** unchanged mathematically.
  10 refuted sub-sorries collapsed into 3 top-level `sorry`s (one per
  representation) so that downstream code is no longer cluttered with
  sub-sorry scaffolding everyone knows is unprovable as stated. The
  framework decision (Option A vs. B vs. A+C / B+C) still gates these.
- **Wall 2 (D̃_n indecomposability):** **resolved as a wall.** The
  `DTildeVertex k` custom inductive (Wall 2 Option a) was implemented
  in stages — PRs #2448 (Stage A vertex type), #2449 (Stage B
  migration), #2460 (Stage C main math `dTildeRep'_isIndecomposable`),
  #2475 (Stage C transport skeleton, partial). What remains is **one
  Fin-transport lemma** (`dTildeRep_mapLinear_transport`) that is
  Lean-mechanical, not framework-blocked. Now claimed by issue #2479.
- **Wall 3 (Garnir straightening):** unchanged framework status. Wave
  55 added the soundness fix #2443 (flipped dominance direction) and
  refuted a follow-on attempt #2454 (`garnir_term_sametab_rowInv_lt`
  counter-example). One sorry at `SpechtModuleBasis.lean:964`. Issue
  #2450 unclaimed.
- **`iso_of_formalCharacter_eq_schurPoly` (the Mathlib-gap sorry):**
  no longer treated as a Mathlib gap. Wave-55 worked it as an
  in-project formalization, scoped into a 6-issue Schur-Weyl chain
  (`progress/schur-weyl-scoping.md` filed via PR #2442). Wave-55
  landed sub-issues #1 (#2461) and #4 (#2462), and most of the
  bimodule-foundation chain culminating in
  `Theorem5_18_1_bimodule_decomposition` (PRs #2467, #2473, #2476).

### Merges since wave 54 (16 PRs, 2026-04-23T11:44Z → 2026-04-24T00:14Z):

| PR | Date | Title | Sorry Impact |
|----|------|-------|--------------|
| #2435 | 04-23 | doc: wave-54 sorry landscape + design-walls snapshot (#2434) | Docs only |
| #2442 | 04-23 | doc: scope Schur-Weyl / FormalCharacterIso sorry (#2440) | Docs only |
| #2443 | 04-23 | fix: flip dominance direction in Garnir straightening (Wall 3) | Soundness fix |
| #2448 | 04-24 | feat: add DTildeVertex k inductive + dim function (Wall 2 Stage A) | Infra |
| #2441 | 04-24 | refactor(Ch6): collapse refuted Ẽ/T sub-sorry scaffolding (#2437) | **−7** (cosmetic) |
| #2455 | 04-24 | progress: counter-example refutes garnir_term_sametab_rowInv_lt (#2454) | Docs only |
| #2449 | 04-24 | Migrate dTildeRep to DTildeVertex k (Wall 2 Option a, Stage B) | Infra |
| #2460 | 04-24 | feat(Ch6): Wall 2 Stage C main math (dTildeRep'_isIndecomposable) | Wall 2 closure |
| #2461 | 04-24 | feat(Ch5): tensor-degree homogeneity from formalCharacter = schurPoly (Schur-Weyl #1) | Schur-Weyl ✓ |
| #2462 | 04-24 | feat(Ch5): schurPoly_linearIndependent (Schur-Weyl #4) | Schur-Weyl ✓ |
| #2464 | 04-24 | progress: Schur-Weyl #3 blocked on bimodule foundation | Docs only |
| #2467 | 04-24 | feat(Ch5): Theorem5_18_1 bimodule — isotypic decomp + Schur evaluation iso foundations | Infra |
| #2470 | 04-24 | progress: planner triage cycle — close 3 replan, file Schur-Weyl #2 + wave-55 summarize | Docs only |
| #2473 | 04-24 | feat(Ch5): bimodule helpers — centralizerToEndA, B-module on V →[A] E, range lemma | Infra |
| #2475 | 04-24 | feat(Ch6): Wall 2 Stage C transport skeleton (#2459 partial) — 4/8 arrow cases + #2474 residual | Wall 2 progress |
| #2476 | 04-24 | feat(Ch5): assemble Theorem5_18_1_bimodule_decomposition from committed helpers | Infra |

**Net counts:**
- Wall 1 cosmetic collapse: −7 (10 → 3 sorries; same framework wall)
- Wall 2 main math closed: 0 (already opaque to the count; new sorry
  `dTildeRep_mapLinear_transport` introduced as the single Stage C
  residual, balancing the closure)
- Schur-Weyl chain: 0 visible sorry change (chain operates entirely on
  unblocking the lone `iso_of_formalCharacter_eq_schurPoly` sorry; new
  theorems landed are sorry-free supporting infrastructure)
- Raw count: 14 → 7 (−7, all from the Ẽ/T scaffolding collapse)
- Files: 4 → 4 (unchanged)

## Chapter Breakdown

| Chapter | Sorries | Files | Delta from Wave 54 |
|---------|---------|-------|--------------------|
| Ch2     | 1       | 1     | 0                  |
| Ch5     | 2       | 2     | 0                  |
| Ch6     | 4       | 1     | −7 (Ẽ/T collapse)  |
| Ch9     | 0       | 0     | 0                  |

## Per-File Sorry Detail

### InfiniteTypeConstructions (Ch6) — 4 sorries

**dTilde transport residual (1): mechanical, claimed**
- Line 2958 — `dTildeRep_mapLinear_transport` (Wall 2 Stage C residual)
  Map-agreement transport between the `Fin (k + 6)`-indexed
  `dTildeRep` and the `DTildeVertex k`-indexed `dTildeRep'`. Four of
  eight arrow cases close by `rfl`; the four remaining cases
  (`pathMid → pathMid`, `pathMid → branchRight`, `rightLeaf1 →
  branchRight`, `rightLeaf2 → branchRight`) need explicit pointwise
  analysis to commute `▸`-casts on `dTildeRepMap`'s dimension equation
  with `LinearEquiv.funCongrLeft` reindexing. Issue #2479 active.

**Ẽ/T framework wall (3): refuted, awaits Kim's decision**
- Line 3178 — `etilde6v2Rep_isIndecomposable (m hm)`
- Line 3433 — `etilde7Rep_isIndecomposable (m hm)`
- Line 3660 — `t125Rep_isIndecomposable (m hm)`

  All three theorems are provably **false** for every m ≥ 1 in their
  current single-nilpotent-twist construction (the `e_m` direction
  peels off as a 1-dim summand at the center). Sub-sorry scaffolding
  was collapsed in PR #2441 — the underlying refutation, design doc
  (`progress/indecomposability-framework-investigation.md`), and
  framework decision (Wall 1) are unchanged. The remaining single
  sorry per theorem is a pointer to the framework wall, not work to
  be done.

### SpechtModuleBasis (Ch5) — 1 sorry: REFUTED FRAMEWORK
- Line 964 — `garnir_twisted_in_lower_span` (combinatorial heart)
  Refuted at λ=(2,2), σ=swap(0,1). PR #2443 flipped the dominance
  direction in the statement (a soundness fix); the body remains
  open. Wave-55 also closed the follow-on `garnir_term_sametab_rowInv_lt`
  approach via counter-example (#2454). Issue #2450 unclaimed; the
  whole-sum cancellation strategy referenced in its body has not yet
  been attempted.

### FormalCharacterIso (Ch5) — 1 sorry: SCHUR-WEYL CHAIN ACTIVE
- Line 395 — `iso_of_formalCharacter_eq_schurPoly`
  Re-scoped from "Mathlib gap" to "6-issue in-project chain" by
  `progress/schur-weyl-scoping.md` (PR #2442). Sub-issues landed:
  #1 (#2461 tensor-degree homogeneity), #4 (#2462 schurPoly linear
  independence), and the bimodule foundations
  (#2467, #2473, #2476: `isotypicDirectSumEquiv`,
  `schurEvaluationEquiv`, `centralizerToEndA`,
  `homIsotypicBridge`, `Theorem5_18_1_bimodule_decomposition`).
  Active now: #2472 (Theorem5_18_4 bimodule upgrade), #2477
  (Schur-Weyl #2a polynomial-to-tensor bridge); blocked: #2478, #2458
  pending these.

### Theorem2_1_2 (Ch2) — 1 sorry: blocked on Wall 1
- Line 173 — Forward bridge: `not_posdef_not_HasFiniteRepresentationType`
  Backward bridge proved by #2403 (wave 54). Forward bridge needs
  per-field infinite-type results from the Ẽ/T constructions, gated on
  Wall 1's framework decision. Issue #2401 carries this dependency.

## Open PRs

None.

## Active Issues

| Issue | Title | Status |
|-------|-------|--------|
| #2469 | summarize: wave-55 sorry landscape + design-walls refresh | Claimed (this session) |
| #2479 | feat(Ch6): close dTildeRep_mapLinear_transport (Wall 2 Stage C residual) | Claimed |
| #2477 | feat(Ch5): bridge hom deg-n polys ↪ V^⊗n ⊗ (V^*)^⊗n (Schur-Weyl #2a) | Claimed |
| #2472 | feat(Ch5): upgrade Theorem5_18_4_decomposition using bimodule form | Claimed |

## Unclaimed Issues

| Issue | Title | Status |
|-------|-------|--------|
| #2450 | Prove garnir_twisted_in_lower_span (Wall 3 residual) | Awaits Wall 3 framework |
| #2436 | Framework decision: affine Dynkin infinite type (Ẽ_n / T(p,q,r)) | replan, awaits Kim |

## Blocked Issues

| Issue | Blocked on |
|-------|-----------|
| #2478 | #2477 (Schur-Weyl #2b consumes #2a output) |
| #2458 | #2472 (Schur-Weyl #3 consumes Theorem5_18_4 bimodule upgrade) |
| #2401 | #2436 (Theorem2_1_2 forward needs Ẽ/T framework) |

## Dependency Clusters

### Cluster A: Polytabloid/Straightening (Ch5, 2 sorries)
**Files:** SpechtModuleBasis (1, framework wall), FormalCharacterIso (1, active chain)

- `garnir_twisted_in_lower_span` — Wall 3 framework wall. Two prior
  approaches refuted (per-term dominance #2425, per-term classification
  #2451–#2454). Issue #2450 unclaimed. Awaits commitment to Option 1
  (column-induction), Option 2 (broader-τ set), or Option 3
  (maximal-tabloid corner case).
- `iso_of_formalCharacter_eq_schurPoly` — Schur-Weyl chain in active
  flight. 6 sub-issues; sub-issues #1 and #4 done, foundations done,
  #2/#2a/#2b and #3 in progress, then #5/#6 not yet filed. Estimate
  3–5 worker-sessions remaining.

### Cluster B: Infinite Type Classification (Ch6, 4 sorries) — FRAMEWORK WALL + 1 RESIDUAL
**Files:** InfiniteTypeConstructions (4)

- **B1 (Ẽ/T framework, 3 sorries)**: Wall 1. Same status as wave 54;
  awaits Kim's option choice.
- **B2 (dTilde Wall 2 residual, 1 sorry)**: `dTildeRep_mapLinear_transport`.
  Mechanical Lean-level transport between `Fin (k + 6)` and
  `DTildeVertex k` indexings. Issue #2479 claimed; expected to close
  Wall 2 entirely once landed.

### Cluster C: Morita Theory (Ch9) — CLOSED (wave 50)

### Cluster D: Gabriel's Theorem (Ch2, 1 sorry) — UNCHANGED
**Status:** Forward bridge still blocked on Cluster B1 framework
decision via #2436 → #2401 chain.

## Trajectory

| Wave | Sorries | Files | Items sorry-free | Date       |
|------|---------|-------|------------------|------------|
| 28   | 66      | 27    | 560/583 (96.1%)  | 2026-03-22 |
| 33   | 43      | 22    | 566/583 (97.1%)  | 2026-03-24 |
| 38   | 27      | 19    | 570/583 (97.8%)  | 2026-03-27 |
| 43   | 13      | 10    | 579/583 (99.3%)  | 2026-04-04 |
| 44   | 10      | 8     | 580/583 (99.5%)  | 2026-04-05 |
| 45   | 15      | 8     | 580/583 (99.5%)  | 2026-04-06 |
| 46   | 15      | 8     | 580/583 (99.5%)  | 2026-04-08 |
| 47   | 9       | 6     | 581/583 (99.7%)  | 2026-04-11 |
| 48   | 8       | 6     | 581/583 (99.7%)  | 2026-04-11 |
| 49   | 10      | 6     | 581/583 (99.7%)  | 2026-04-12 |
| 50   | 13      | 5     | 581/583 (99.7%)  | 2026-04-13 |
| 51   | 21      | 5     | 582/583 (99.8%)  | 2026-04-17 |
| 52   | 17      | 4     | 582/583 (99.8%)  | 2026-04-17 |
| 53   | 13      | 4     | 582/583 (99.8%)  | 2026-04-17 |
| 54   | 14      | 4     | 582/583 (99.8%)  | 2026-04-23 |
| **55** | **7** | **4** | **582/583 (99.8%)** | **2026-04-24** |

**Wave 55 trend:** Raw count halved (14 → 7). The drop is partly
cosmetic (Ẽ/T scaffolding collapse, −7) and partly real (Wall 2
core math landed, leaving only a mechanical residual). Three of the
remaining 7 sorries are framework-wall stubs. Two are framework-wall
items (Garnir #2450, Wall 3) plus framework-blocked downstream
(Theorem 2.1.2 forward). Two are actively-worked items (the dTilde
residual #2479; the Schur-Weyl chain ending at FormalCharacterIso).

## Honest Assessment

Wave 55 is the wave where **the wall map shrank**. Three observations:

**Strengths:**
1. **Wall 2 is materially closed.** The `DTildeVertex k` Option-a
   refactor (#2448 → #2449 → #2460 → #2475) replaced the
   definitional-reduction blocker with a working inductive vertex
   type, and the main indecomposability proof landed
   (`dTildeRep'_isIndecomposable` in #2460). What remains is one
   Fin-transport lemma — Lean mechanics, not mathematics.
2. **Schur-Weyl chain is a real plan in flight.** What was previously
   a "Mathlib gap" sorry-of-the-month was scoped (PR #2442) into six
   sub-issues, and four of them landed in wave 55 (foundations:
   `isotypicDirectSumEquiv`, `schurEvaluationEquiv`,
   `centralizerToEndA`, `homIsotypicBridge`,
   `Theorem5_18_1_bimodule_decomposition` plus sub-issues #1 and #4).
   Two more (#2 and #3) are claimed and in progress.
3. **Ẽ/T scaffolding cleanup.** PR #2441 collapsed 10 refuted
   sub-sorries into 3 single sorries that mark the framework wall
   without polluting the file with sub-sorry detail nobody plans to
   close as stated. Cosmetic, but improves signal in the file.
4. **Soundness improved on Wall 3.** PR #2443 corrected the dominance
   direction in `garnir_twisted_in_lower_span`'s statement; PR #2454
   ruled out one tempting follow-on lemma by counter-example. The
   framework wall is unchanged but the available paths are narrower
   and better understood.

**Concerns:**
1. **Ẽ/T framework decision (Wall 1) is now the longest-running open
   item in the project.** Issue #2436 is `human-oversight`; two
   worker agents have skipped it asking for Kim's option choice (3rd
   skip blocked by coordination). Until Kim picks A / B / A+C / B+C,
   these 3 sorries cannot be addressed and Theorem 2.1.2 forward
   cannot be unblocked.
2. **Wall 3 (Garnir) is still a framework wall.** The classical result
   is true, but no in-project worker has committed to one of the
   three approach options (column-induction, broader-τ, corner-case).
   Issue #2450 has been unclaimed for ~24 hours.
3. **Schur-Weyl chain success is provisional.** The main risk noted in
   `progress/schur-weyl-scoping.md` was that abstract `L_i` from
   `Theorem5_18_4_decomposition` may force the identification step
   to be rebuilt from `5_18_1` directly. The bimodule track (#2466 →
   #2471 → #2472) is precisely that rebuild, and it's well underway,
   but the Schur-module identification (#2458) is still blocked on
   #2472 landing. The chain is short of "done", just on a clear path.
4. **`dTildeRep_mapLinear_transport` (Wall 2 residual) is non-trivial.**
   Issue #2479 documents that the previous worker tried multiple
   strategies (`generalize_proofs`, HEq casting, `dif_*` simp) and
   the `▸`-cast obstruction is real. May need a refactor of
   `dTildeRepMap` rather than a direct proof.

**Current priority ordering:**
1. **Kim's framework decision on Wall 1 (#2436).** Unblocks 3 sorries
   directly + 1 downstream (Theorem 2.1.2 forward).
2. **#2479** (dTilde transport residual) — closes Wall 2 entirely.
3. **#2477 → #2478 → #2458** (Schur-Weyl #2a → #2b → #3) — chips at
   `iso_of_formalCharacter_eq_schurPoly`. #2472 in parallel for #3.
4. **#2450** (Wall 3 Garnir) — needs framework choice; unclaimed.
5. **Theorem 2.1.2 forward** — gated on (1).

**If Wall 1 is resolved**: 3 sorries either disappear (Option B
refactor replaces them with new well-posed sub-sorries) or move to a
different proof path (Option A). Combined with successful execution
of the Schur-Weyl chain (≈ 3–5 more worker sessions) and the dTilde
residual (1 more session), the project floor would be Wall 3 (1
sorry) + Theorem 2.1.2 forward (1 sorry, then easily provable once
the per-field infrastructure exists). That is a one-decision-plus-a-week
path to single-digit sorries with a clear shape, rather than the
multi-month estimate that wave 54 reported.
