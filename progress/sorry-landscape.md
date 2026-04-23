# Sorry Landscape Analysis — Wave 54

Generated 2026-04-23 by summarize session (issue #2434).

## Summary

**14 sorries** across 4 files (up from 13/4 in wave 53). Raw count rose
by 1, but the substantive change is qualitative: three separate
framework-level refutations were discovered since wave 53, and the
remaining sorries now split cleanly into "blocked on framework
decisions" (11) and "one genuinely provable item" (1, forward Gabriel
bridge) and "Mathlib gaps" (2).

281 of 285 Lean files (98.6%) are sorry-free. 582/583 items (99.8%) sorry-free.

**Definition-level sorries: 0.** All mathematical objects are constructed.

### Design walls discovered this wave

Wave 54 is notable less for sorry movement than for **three separate
framework refutations** that moved the remaining work off the
worker-fillable path and onto the planner / human-decision path. See
`progress/design-walls-wave54.md` for a one-page decision sheet.

1. **Ẽ₆ / Ẽ₇ / T(1,2,5) `_isIndecomposable` refuted for all m ≥ 1.**
   The single-nilpotent-twist framework in these three explicit
   representations admits an explicit 1-dimensional decomposition off
   the "missed `e_m` direction" of the N-image. All ten sub-sorries in
   these theorems (lines 2380, 2397, 2400, 2425 in etilde6v2; 3001,
   3004, 3038 in etilde7; 3477, 3480, 3502 in t125) are unprovable as
   stated. Design doc: `progress/indecomposability-framework-investigation.md`
   (merged in #2432).

2. **`garnir_twisted_in_lower_span` + `garnir_straightening_step`
   refuted** by concrete counter-example at λ=(2,2), σ=swap(0,1)
   (session 9cfda69f on #2425, 2026-04-23). The outer Specht-basis
   theorem `polytabloidTab_column_standard_in_span` is classically
   true, but the Garnir-based induction currently used in
   `SpechtModuleBasis.lean:911-942` loses essential ψ_τ terms at
   lower-dominated tabloids. Progress: `progress/20260423T112112Z_9cfda69f.md`.

3. **`dTildeRep_isIndecomposable` blocked on Lean-level vertex
   indexing.** `dTildeDim k m v` does not reduce by `rfl`/`dsimp` at
   k-dependent vertices, making the case-split style proof unworkable
   without either a deep refactor of the vertex type (custom inductive
   rather than `Fin (k + 6)`) or acceptance of `finCongr` cast bridges
   through the proof (session 0fa9a788 on closed issue #2431).

### Merges since wave 53 (18 PRs, 2026-04-17T14Z → 2026-04-23T11Z):

| PR | Date | Title | Sorry Impact |
|----|------|-------|-------------|
| #2398 | 04-17 | feat: prove etilde7 propagation sorry (1/4 sub-sorries) | −1 (etilde7: 4→3) |
| #2399 | 04-17 | feat: t125Rep_isIndecomposable structural framework (5 sorries) | +4 (t125: 1→5) |
| #2402 | 04-18 | feat: prove t125Arm1Embed and embedSkipBlockB injectivity (2/5 sorries) | −2 (t125: 5→3) |
| #2403 | 04-18 | feat: prove backward bridge of Gabriel's theorem (1/2 sorries) | −1 (Ch2: 2→1) |
| #2405 | 04-18 | doc: report etilde7Rep decomposability bug (blocks #2394) | Docs only |
| #2408 | 04-18 | fix: fill zero blocks in etilde7Arm1Embed and t125Arm1Embed (#2406) | Infra |
| #2410 | 04-18 | feat: prove walk_to_nodup_path + dTilde_nodup_path_between | −2 (path infra) |
| #2411 | 04-18 | feat: document Ẽ₆ indecomposability proof strategy | Docs only |
| #2412 | 04-18 | fix: add w ∉ ColumnSubgroup hypothesis to garnir_twisted_in_lower_span | Soundness fix |
| #2414 | 04-23 | feat: set up etilde6v2Rep_isIndecomposable framework (5 sub-sorries) | +4 (etilde6v2: 1→5) |
| #2415 | 04-23 | fix: resolve circularity in garnir_twisted_in_lower_span (#2413) | Structural fix |
| #2421 | 04-23 | Prove garnir_straightening_step k=0 case | Sub-case closed |
| #2422 | 04-23 | feat: prove etilde6v2 hbot3 sub-sorry via Γ surjectivity (#2420) | −1 (etilde6v2: 5→4) |
| #2423 | 04-23 | progress: counter-example refutes etilde6v2Rep_isIndecomposable | **Refutation** |
| #2426 | 04-23 | refactor: Garnir straightening uses tabloid-dominance induction (#2424) | Structural refactor |
| #2429 | 04-23 | chore: progress entry — analyze Ẽ₇ hN₁/hN₂ obstruction | Docs only |
| #2432 | 04-23 | chore: design doc — affine Dynkin indecomposability framework | **Design doc** |
| #2433 | 04-23 | chore: progress entry — refutation of garnir_twisted_in_lower_span framework (#2425) | **Refutation** |

**Net:**
- Genuine closures: 6 (etilde7 propagation, t125 injectivity ×2,
  Gabriel backward, path infra ×2)
- Framework expansions: +8 (etilde6v2 +4, t125 +4 — sub-sorries made
  visible, then partially closed)
- Raw count change: 13 → 14 (+1)
- Files with sorries: 4 → 4 (unchanged)

**Soundness fixes in this wave:**
- PR #2412 added `w ∉ ColumnSubgroup` hypothesis to `garnir_twisted_in_lower_span`.
- PR #2415 resolved circular-dependency chain in Garnir straightening.

**Structural refactors:**
- PR #2426 changed `garnir_straightening_step` induction from row-inversion
  measure to tabloid-dominance measure (setting up the framework that
  was then refuted by #2425 analysis).

## Chapter Breakdown

| Chapter | Sorries | Files | Delta from Wave 53 |
|---------|---------|-------|---------------------|
| Ch2 | 1 | 1 | −1 (backward bridge closed by #2403) |
| Ch5 | 2 | 2 | 0 (garnir refactored in place, still 1 sorry) |
| Ch6 | 11 | 1 | +2 (net: framework expansion −6 closed +8 visible) |
| Ch9 | 0 | 0 | 0 |

## Per-File Sorry Detail

### InfiniteTypeConstructions (Ch6) — 11 sorries

**Indecomposability — dTilde (1): BLOCKED (Lean-level)**
- Line 2177 — `dTildeRep_isIndecomposable` (D̃_n arbitrary path-length)
  Blocked on `dTildeDim` definitional reduction. Issue #2431 closed
  with replan. Two recommended options (see design-walls-wave54):
  custom inductive vertex type vs. `finCongr` cast bridges.

**Indecomposability — Ẽ₆ (4): REFUTED**
- Line 2380 — `leaf24_containment` (W(2) ⊆ W(4) as subspaces)
- Line 2397 — `hN₁` (N-invariance of W₁(2) under nilpotentShiftLin)
- Line 2400 — `hN₂` (N-invariance of W₂(2) under nilpotentShiftLin)
- Line 2425 — `hbot0` (propagation W(2)=⊥ ⟹ W(0)=⊥)

  `etilde6v2Rep_isIndecomposable (m : ℕ) (hm : 1 ≤ m)` is provably
  **false** for all m ≥ 1 via the explicit 1-dim decomposition peeling
  off the missed `e_m` direction in block D. Sub-sorries cannot be
  closed as stated. Framework change required.

**Indecomposability — Ẽ₇ (3): REFUTED**
- Line 3001 — `hN₁` (N-invariance of W₁(4))
- Line 3004 — `hN₂` (N-invariance of W₂(4))
- Line 3038 — `hbot0` (propagation W(4)=⊥ ⟹ W(0)=⊥)

  Same fatal pattern as Ẽ₆. `etilde7Rep 1` admits an explicit
  decomposition (see `indecomposability-framework-investigation.md`).
  Sub-sorries unprovable as stated.

**Indecomposability — T(1,2,5) (3): REFUTED**
- Line 3477 — `hN₁` (N-invariance of W₁(8))
- Line 3480 — `hN₂` (N-invariance of W₂(8))
- Line 3502 — `hbot0` (propagation W(8)=⊥ ⟹ W(0)=⊥)

  Same pattern. `t125Rep 1` admits an explicit decomposition. Sub-sorries
  unprovable as stated.

### SpechtModuleBasis (Ch5) — 1 sorry: REFUTED
- Line 942 — `garnir_twisted_in_lower_span` (combinatorial heart)
  Refuted at λ=(2,2), σ=swap(0,1). The outer theorem
  `polytabloidTab_column_standard_in_span` is classically true, but
  the current Garnir-based induction framework is unsound. Framework
  change required (see design-walls-wave54: column-induction vs.
  broader-τ set vs. maximal-tabloid corner case).

### FormalCharacterIso (Ch5) — 1 sorry: MATHLIB GAP
- Line 221 — `iso_of_formalCharacter_eq_schurPoly`
  Requires Schur-Weyl duality / GL_N complete reducibility. Not
  refuted — genuinely provable, but the Mathlib infrastructure does
  not yet exist. Identified as Mathlib gap by meditate wave 49.

### Theorem2_1_2 (Ch2) — 1 sorry: PROVABLE, BLOCKED ON CH6
- Line 173 — Forward bridge: `not_posdef_not_HasFiniteRepresentationType`
  Backward bridge proved by #2403. Forward bridge needs per-field
  infinite type result, which requires working indecomposability
  proofs in Ch6 (cluster B above) + a ∀k∀Q refactor of
  InfiniteTypeConstructions. Unblocks once Cluster B is resolved.

## Open PRs

None.

## Active Issues

| Issue | Title | Status |
|-------|-------|--------|
| #2434 | summarize: wave-54 sorry landscape + design-walls snapshot | Claimed (this session) |

## Unclaimed Issues

None actionable at the current design-wall state. New issues must
follow planner decisions on the three design walls.

## Dependency Clusters

### Cluster A: Polytabloid/Straightening (Ch5, 2 sorries) — FRAMEWORK WALL
**Files:** SpechtModuleBasis (1), FormalCharacterIso (1)
**Key sorries:**
- `garnir_twisted_in_lower_span` — refuted by counter-example (#2425).
  Outer Specht-basis theorem is true, but current induction framework
  cannot prove it. Three options on the planner's desk
  (column-induction / broader-τ / corner-case).
- `iso_of_formalCharacter_eq_schurPoly` — Mathlib gap (Schur-Weyl).
**Status:** Stalled pending framework decision.

### Cluster B: Infinite Type Classification (Ch6, 11 sorries) — FRAMEWORK WALL
**Files:** InfiniteTypeConstructions (11)
**Sub-clusters:**
- **B1a (D̃_n, Lean-level blocker, 1 sorry)**: `dTildeRep_isIndecomposable`
  blocked by `dTildeDim` definitional-reduction failure at k-dependent
  vertices. Not a mathematical wall — a Lean-level vertex-indexing
  strategy decision.
- **B1b (Ẽ_n / T(p,q,r), framework refuted, 10 sorries)**:
  `etilde6v2Rep`, `etilde7Rep`, `t125Rep` `_isIndecomposable` theorems
  all false for m ≥ 1. Framework change required. Design doc
  `indecomposability-framework-investigation.md` lays out the options:
  Option A (book's Tits-form orbit-counting argument, 6+ months of
  algebraic-geometry infrastructure) vs. Option B (stronger explicit
  construction with multiple coupling twists or γ-style center-to-center
  iso).

### Cluster C: Morita Theory (Ch9) — CLOSED (wave 50)

### Cluster D: Gabriel's Theorem (Ch2, 1 sorry) — IMPROVED
**Status:** Backward bridge closed by #2403. Forward bridge remains
(1 sorry at line 173), blocked on cluster B completion + ∀k∀Q
refactor.

## Trajectory

| Wave | Sorries | Files | Items sorry-free | Date |
|------|---------|-------|------------------|------|
| 28 | 66 | 27 | 560/583 (96.1%) | 2026-03-22 |
| 33 | 43 | 22 | 566/583 (97.1%) | 2026-03-24 |
| 38 | 27 | 19 | 570/583 (97.8%) | 2026-03-27 |
| 43 | 13 | 10 | 579/583 (99.3%) | 2026-04-04 |
| 44 | 10 | 8 | 580/583 (99.5%) | 2026-04-05 |
| 45 | 15 | 8 | 580/583 (99.5%) | 2026-04-06 |
| 46 | 15 | 8 | 580/583 (99.5%) | 2026-04-08 |
| 47 | 9 | 6 | 581/583 (99.7%) | 2026-04-11 |
| 48 | 8 | 6 | 581/583 (99.7%) | 2026-04-11 |
| 49 | 10 | 6 | 581/583 (99.7%) | 2026-04-12 |
| 50 | 13 | 5 | 581/583 (99.7%) | 2026-04-13 |
| 51 | 21 | 5 | 582/583 (99.8%) | 2026-04-17 |
| 52 | 17 | 4 | 582/583 (99.8%) | 2026-04-17 |
| 53 | 13 | 4 | 582/583 (99.8%) | 2026-04-17 |
| **54** | **14** | **4** | **582/583 (99.8%)** | **2026-04-23** |

**Wave 54 trend:** Raw count inched up (13→14), but the headline is
qualitative: three framework-level walls were discovered, moving the
project from "execute on existing plan" to "planner needs to make
design decisions". Genuine closures (6) are offset by framework
expansions that made sub-sorries visible (+8). Most remaining sorries
are now known to be **unprovable as stated**, not pending work.

## Honest Assessment

Wave 54 is the wave the project hit **three walls at once**, and the
shape of the remaining work changed as a result. The raw count is
basically flat; what changed is our understanding of what those
sorries actually mean.

**Strengths:**
1. **Gabriel's theorem backward bridge closed.** PR #2403 closes one
   of the two long-standing Ch2 bridges. The remaining forward bridge
   is still blocked on Ch6, but one side is now done.
2. **Path infrastructure closed.** PR #2410 closed
   `walk_to_nodup_path` + `dTilde_nodup_path_between`, eliminating the
   two path-infra sorries that had been visible since wave 53.
3. **Three hard questions cleanly answered.** Rather than spending
   more worker sessions grinding on refuted sorries, the three
   framework walls are documented with design docs and counter-examples.
   This is a net-positive even though the sorry count didn't drop.
4. **Soundness improved.** `garnir_twisted_in_lower_span` got the
   missing `w ∉ ColumnSubgroup` hypothesis (#2412); the circularity
   chain was resolved (#2415).

**Concerns:**
1. **Ch6 indecomposability cluster is stuck.** Ten of 11 Ch6 sorries
   are in refuted theorems. They cannot be closed without either
   (a) restructuring the explicit representations, or (b) switching
   to the book's orbit-counting proof strategy (Option A in the design
   doc, 6+ months of Lean algebraic-geometry infrastructure).
2. **Ch5 straightening is stuck too.** The classical result is true
   but the current framework can't prove it. Three alternative
   framework sketches are on the planner's desk; none have been
   committed to.
3. **`dTildeRep` is the only non-refuted Ch6 item**, and it's blocked
   on Lean-level vertex indexing rather than mathematics. The split
   between "mathematical wall" (10 sorries) and "Lean-level wall"
   (1 sorry) is worth remembering.
4. **No worker-fillable sorries remain.** Every item on the list
   requires either a framework decision (human input) or a Mathlib
   gap closure (big piece of work). The agent-worker flow is at an
   idle point until a planner acts on the three design walls.
5. **FormalCharacterIso Mathlib gap is the only non-framework-wall
   non-refuted remaining item.** It needs Schur-Weyl duality, which
   is big-Mathlib work. Unchanged since wave 48.

**Current priority ordering:**
1. **Planner triage of the three design walls** (see
   `design-walls-wave54.md`). Nothing else unblocks.
2. **Once Ẽ_n / T(p,q,r) framework decided**: either refactor the
   Rep definitions (Option B) or begin Tits-form scaffolding (Option A).
   10 Ch6 sorries gated on this.
3. **Once Garnir framework decided**: restart Ch5 straightening with
   the chosen induction measure. 1 Ch5 sorry gated on this.
4. **Once dTildeDim strategy decided**: either inductive vertex type
   or `finCongr` cast bridges. 1 Ch6 sorry gated on this.
5. **Ch2 forward bridge**: blocked on Cluster B resolution, so
   deferred to after step 2.
6. **`iso_of_formalCharacter_eq_schurPoly`**: independent Mathlib-gap
   work. Can be attempted in parallel, but remains the hardest
   remaining sorry.

**If the three design walls are resolved**: the 10 refuted Ẽ/T
sub-sorries either disappear (Option B refactor replaces them with
new, well-posed sub-sorries) or move to a different proof path
(Option A). The Ch5 sorry similarly gets a new well-posed framework.
The remaining floor is then Ch2 forward bridge + dTildeDim +
FormalCharacterIso = 3 sorries, all of which are genuinely provable
given the framework decisions.
