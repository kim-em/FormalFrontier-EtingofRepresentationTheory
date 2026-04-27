# Sorry Landscape Analysis — Wave 57

Generated 2026-04-27 by summarize session (issue #2591).

## Summary

**7 sorries** across 4 files (down from 8/4 in wave 56). Net delta:
**−1**. The Schur-Weyl equivariance decomposition anchor
`glTensorRep_equivariant_schurWeyl_decomposition` (issue #2540) closed
via PR #2578, landing the only sorry that wave 56 introduced as a
decomposition anchor on the Schur-Weyl chain. The remaining sorries are
unchanged in *kind* from wave 56: 3 Wall 1 framework stubs in Ch6, 1
Theorem 2.1.2 forward bridge in Ch2 (blocked on Wall 1), 2 Wall 3 chain
sorries in `SpechtModuleBasis`, and the top-of-chain Schur-Weyl goal
`iso_of_formalCharacter_eq_schurPoly` in `FormalCharacterIso`.

284 of 288 Lean files (98.6%) are sorry-free. 582/583 items (99.8%)
sorry-free.

**Definition-level sorries: 0.** All mathematical objects are
constructed.

### Key story for wave 57

- **Wall 1 (Ẽ/T framework, Kim's decision):** unchanged. 3 sorries; same
  refutation structure as waves 55/56. Issue #2436 still
  `human-oversight + replan`, still awaiting Kim's option choice
  (A / B / A+C / B+C). Now the longest-running open item by a wide
  margin.
- **Wall 2 (D̃_n indecomposability):** **STILL CLOSED.** No regression.
- **Wall 3 (Garnir straightening):** **chain advanced, but its glue
  step was rejected as unsound and replaced.** Wave 56's C.1.b
  algorithm A landed via PR #2541 (issue #2532 closed). C.1.a.ii
  pigeonhole helper PR #2550 is open but `CONFLICTING` (in repair
  flow). The original C.1.c glue plan (#2533) was closed via
  supersession after worker session `add8c41f` showed Step 1's
  upstream `TP ∈ V^λ` lemma was unsound; replacement issue **#2605**
  (Wall 3 C.1.c rev2 — mutual-induction restructure, `critical-path`)
  now carries the closure plan. Both #2520 (C.2) and #2500 (final
  assembly D) are re-blocked on #2605.
- **Schur-Weyl chain:** **massive C-tier progress.** The equivariance
  anchor #2540 closed; an explicit-eval analogue
  `Theorem5_18_4_GL_rep_decomposition_explicit` landed (#2579) for
  downstream consumers; the polynomial identity
  `(∑ Xᵢ)^n = ∑ dim(Specht_λ)·schurPoly_λ` landed (#2606); the
  formalCharacter-of-glTensorRep identity landed (#2600); both
  `Module.Finite k (V i)` and `Module.Finite k (S' i)` now propagate
  through the bimodule existential chain (#2586, #2604); reviewers
  audited the critical-path PRs (#2603 audit on #2578 + #2579).
  Remaining: irreducibility of `L_i` (#2582 claimed) and irreducibility
  of `SchurModule` (decomposed into #2610 + #2611 with #2612 final
  assembly), then #2493 final assembly, then #2482, then #2483 closes
  the line-399 sorry.

### Merges since wave 56 (23 substantive PRs, 2026-04-24T10:15Z → 2026-04-27T20:01Z):

Tabulated in chronological order. "Sorry Impact" annotates the
net-of-this-wave effect on the raw sorry count.

| PR    | Time (UTC) | Title | Sorry Impact |
|-------|-----------:|-------|--------------|
| #2562 | 04-27 14:09 | review(Ch5): audit FormalCharacterIso PRs #2516 + #2534 — PASS | Review |
| #2566 | 04-27 14:14 | review(Ch5 #2554): Schur-Weyl plumbing audit (#2528 + #2551) — all PASS | Review |
| #2567 | 04-27 14:23 | review(Ch5 #2557): explicit bimodule with evaluation formula audit (#2509) | Review |
| #2569 | 04-27 14:28 | review(Ch5 #2561): Schur-Weyl #2a foundations audit — PASS | Review |
| #2575 | 04-27 14:31 | doc(review #2560): Schur-Weyl L_i FDRep GL_N audit (PR #2504) — PASS-with-followups | Review |
| #2576 | 04-27 14:42 | review-finding(Ch5 #2568): drop [CharZero k] from Schur-Weyl #2a foundations | Style |
| #2577 | 04-27 15:00 | review-finding(Ch5 #2559): drop unused [CharZero k] from formalCharacter additivity | Style |
| #2578 | 04-27 15:06 | feat(Ch5 #2540): close `glTensorRep_equivariant_schurWeyl_decomposition` | **−1** (Schur-Weyl ✓) |
| #2579 | 04-27 15:31 | feat(Ch5 #2572): `Theorem5_18_4_GL_rep_decomposition_explicit` | Infra |
| #2584 | 04-27 16:05 | doc(Ch5 #2564): tracker note for upstream Mathlib PR (`eq_of_eval_eq_on_gl`) | Docs |
| #2585 | 04-27 16:06 | refactor(Ch5 #2565): drop [CharZero k] from `eval_polyRightTransl` / `hP_mul_of_hP` | Style |
| #2586 | 04-27 16:12 | refactor(Ch5 #2573): propagate `Module.Finite k (V i)` into bimodule existential | Infra |
| #2587 | 04-27 16:14 | doc(Ch5 #2571): SMulCommClass docstring on Theorem5_18_1_bimodule_decomposition | Docs |
| #2588 | 04-27 16:20 | doc(Ch5 #2570): Theorem5_18_4 docstring corrections | Docs |
| #2541 | 04-27 16:59 | feat(Ch5 #2532): Wall 3 C.1.b — Leading-tabloid elimination (Algorithm A) | Infra (chain) |
| #2598 | 04-27 17:10 | refactor(Ch5 #2574): tighten heartbeat bumps in Theorem5_18_1 | Style |
| #2599 | 04-27 17:10 | refactor(Ch5 #2589): consume `_explicit` in `glTensorRep_equivariant_schurWeyl_decomposition` | Infra |
| #2600 | 04-27 17:16 | feat(Ch5 #2580): Schur-Weyl L_i (part C-1) — formalCharacter of `glTensorRep` = (∑ Xᵢ)^n | Infra |
| #2603 | 04-27 17:22 | review(Ch5 #2592): audit Schur-Weyl L_i critical-path PRs #2578 + #2579 — PASS | Review |
| #2604 | 04-27 17:37 | refactor(Ch5 #2594): propagate `Module.Finite k (V i / S i)` into `_explicit` chain | Infra |
| #2606 | 04-27 17:54 | feat(Ch5 #2581): Schur-Weyl L_i (part C-2) — polynomial identity `(∑ Xᵢ)^n = ∑ dim·s_λ` | Infra |
| #2607 | 04-27 18:03 | refactor(Ch5 #2590): delegate `Theorem5_18_4_GL_rep_decomposition` to `_explicit` variant | Infra |
| #2631 | 04-27 20:01 | review(Ch5 #2608): Schur-Weyl L_i polynomial C-1 + C-2 audit (#2600 + #2606) — PASS | Review |

(Excludes ~26 progress/planner-cycle commits, including 19 consecutive
no-op cycles between 17036e94 and a6110459 as the queue stabilised
around the residual ~6-issue pool.)

**Net counts:**
- Schur-Weyl equivariance anchor closed: −1 (`glTensorRep_equivariant_schurWeyl_decomposition`).
- Wall 3 C.1.b landed (PR #2541) but the helper sorry it was paired
  with (`twistedPolytabloid_pigeonhole_pair`) is still open on PR #2550;
  no net change in `SpechtModuleBasis` sorry count this wave.
- Raw count: 8 → 7 (−1). Files: 4 → 4 (unchanged).
- Infra / review / style / docs: 22 substantive total; no regressions.

## Chapter Breakdown

| Chapter | Sorries | Files | Delta from Wave 56 |
|---------|---------|-------|--------------------|
| Ch2     | 1       | 1     | 0                  |
| Ch5     | 3       | 2     | −1 (Schur-Weyl equivariance closed) |
| Ch6     | 3       | 1     | 0                  |
| Ch9     | 0       | 0     | 0                  |

## Per-File Sorry Detail

### InfiniteTypeConstructions (Ch6) — 3 sorries: WALL 1 FRAMEWORK

All three sorries are **refuted-as-stated** pointers to Wall 1. Same
status as waves 55/56. Each theorem is provably **false** for every
m ≥ 1 in its current single-nilpotent-twist construction (the `e_m`
direction peels off as a 1-dim summand at the center).

| Line | Theorem | Status |
|-----:|---------|--------|
| 3344 | `etilde6v2Rep_isIndecomposable (m hm)` | Refuted; awaits Wall 1 decision |
| 3599 | `etilde7Rep_isIndecomposable (m hm)` | Refuted; awaits Wall 1 decision |
| 3826 | `t125Rep_isIndecomposable (m hm)` | Refuted; awaits Wall 1 decision |

Reference: `progress/indecomposability-framework-investigation.md`.
Framework issue: #2436 (`human-oversight`, `replan`). Downstream:
`not_posdef_not_HasFiniteRepresentationType` (Theorem 2.1.2 forward).

### SpechtModuleBasis (Ch5) — 2 sorries: WALL 3 CHAIN ACTIVE

The Wall 3 chain advanced this wave: Algorithm A (C.1.b) landed via
PR #2541, but the C.1.c glue step was rejected as unsound and
restructured.

- **Line 1375 — `twistedPolytabloid_pigeonhole_pair`** (C.1.a.ii)
  The combinatorial pigeonhole core. **Issue #2543 has-pr (PR #2550
  open, `CONFLICTING`).** PR sits in the repair queue for merge-conflict
  resolution. The sign-reversing involution scaffold consuming this
  helper landed in wave-56 (PR #2544); `twistedPolytabloid_support_bound`
  remains fully proved modulo this one sorry. Line shifted from 1094
  (wave 56) to 1375 due to intervening PR #2541.

- **Line 1614 — `garnir_twisted_in_lower_span`** (final Wall 3 sorry)
  The combinatorial heart of the straightening theorem. The wave-56
  closure plan (#2533, C.1.c glue) was closed via supersession after
  worker session `add8c41f` analysed and refuted Step 1's upstream
  `TP ∈ V^λ` lemma. The mutual-induction replacement plan **#2605**
  (`critical-path`, unclaimed) is the new closure path. Both #2520
  (C.2 τ classification) and #2500 (Wall 3 part D final assembly) are
  re-blocked on #2605. Line shifted from 1332 (wave 56) to 1614 due to
  PR #2541.

### FormalCharacterIso (Ch5) — 1 sorry: SCHUR-WEYL CHAIN ACTIVE

- **Line 399 — `iso_of_formalCharacter_eq_schurPoly`**
  The top-of-chain goal sorry, unchanged in *position* since wave-43
  but with substantial chain progress this wave. Schur-Weyl chain
  status:
  - `#1` ✅ merged (PR #2461): tensor-degree homogeneity.
  - `#2a` ✅ merged (PRs #2502, #2511, #2538): polynomial-tensor
    bridge construction + injectivity + equivariance. Audited PASS
    via #2569 / #2566 (this wave).
  - `#2b` ✅ merged (PRs #2528, #2539): polynomial rep embedding.
  - `#3 Part A` ✅ merged (PR #2504, audited #2575).
  - `#3 Part B` ✅ merged (PR #2542 + PR #2578): equivariance anchor
    closed this wave.
  - `#3 Part C-1` ✅ merged (PR #2600, audited PASS in PR #2631 / #2608).
  - `#3 Part C-2` ✅ merged (PR #2606, audited PASS in PR #2631 / #2608).
  - `#3 Part C-3` (#2582) — irreducibility of `L_i`. **claimed.**
  - `#3 Part C-4` (#2583) — was decomposed into #2610 (image of
    primitive idempotent c_λ) + #2611 (transfer simplicity from
    diagonalActionImage to GL_N) + #2612 (final assembly,
    `blocked` on #2610 + #2611).
  - `#3 Part C` final assembly (#2493) — blocked on #2612.
  - `#4` ✅ merged (PR #2462): `schurPoly_linearIndependent`.
  - `#5` (#2482) blocked on #2493.
  - `#6` (#2483) — closes line-399 sorry, blocked on #2482.
  - Collateral infra landed this wave: explicit-eval analogue
    (#2579), `Module.Finite (V i)` propagation (#2586), explicit-chain
    `Module.Finite (V i / S i)` (#2604), heartbeat tightening (#2598),
    polynomial identity (#2606), formalCharacter identity (#2600),
    delegation refactor (#2607).

  The line-774 wave-56 sorry (`glTensorRep_equivariant_schurWeyl_decomposition`)
  is **gone**. The file dropped from 2 sorries to 1 this wave.

### Theorem2_1_2 (Ch2) — 1 sorry: blocked on Wall 1

- **Line 173 — `not_posdef_not_HasFiniteRepresentationType`** (forward)
  Backward bridge proved by #2403 (wave 54). Forward bridge needs
  per-field infinite-type results from the Ẽ/T constructions, gated on
  Wall 1's framework decision. Issue #2401 carries this dependency.
  Unchanged since wave 54.

## Open PRs

| PR | Status | Branch |
|----|--------|--------|
| #2550 | mergeable=CONFLICTING, CI SUCCESS | agent/f70c31f1 — Wall 3 C.1.a.ii pigeonhole (in repair queue) |

PR #2541 (Wall 3 C.1.b Algorithm A) **landed** this wave. PR #2541
was the wave-56 "open repair" entry; it is now closed.

## Active / Claimed Issues

| Issue | Title | Status |
|-------|-------|--------|
| #2591 | summarize: wave-57 sorry landscape + design-walls refresh | claimed (this session) |
| #2582 | Schur-Weyl L_i (part C-3): irreducibility of `L_i` | claimed |

## Unclaimed Issues (`agent-plan`, FIFO order)

| Issue | Title | Notes |
|-------|-------|-------|
| #2605 | Wall 3 C.1.c rev2 — mutual-induction restructure | **critical-path**; unblocks #2520 + #2500 |
| #2601 | refactor(Ch5): tighten heartbeat bump on equivariance theorem | hygiene |
| #2602 | refactor(Ch5): extract `glHom` + per-component-`ρ` helpers | pure refactor (#2590 closed → unblocked this wave) |
| #2610 | Schur-Weyl L_i C-4a: image of primitive idempotent c_λ is simple | independent of #2611 |
| #2611 | Schur-Weyl L_i C-4b: transfer simplicity to GL_N | independent of #2610 |

## Replan / Human-oversight Issues

| Issue | Title | Status |
|-------|-------|-------|
| #2436 | Framework decision: affine Dynkin infinite type (Ẽ_n / T(p,q,r)) | replan, `human-oversight`, awaits Kim |

## Blocked Issues (depends-on transitively)

| Issue | Title | Blocked on |
|-------|-------|-----------|
| #2543 | Wall 3 C.1.a.ii pigeonhole | has-pr (#2550 in repair) |
| #2520 | Wall 3 #2499 C.2 — τ classification | #2605 |
| #2500 | Wall 3 #2450 part D — final assembly | #2605 + #2520 |
| #2493 | Schur-Weyl L_i (part C): final assembly | #2612 |
| #2612 | Schur-Weyl L_i C-4c: final assembly `schurModule_isSimple` | #2610 + #2611 |
| #2482 | polynomial GL_N-rep decomposes as direct sum of Schur modules (#5) | #2493 |
| #2483 | close `iso_of_formalCharacter_eq_schurPoly` (#6) | #2482 |
| #2401 | Prove Theorem2_1_2 bridges (forward + backward) | #2436 |
| #2564 | Mathlib upstream tracker: `MvPolynomial.eq_of_eval_eq_on_gl` | upstream Mathlib PR |

## Dependency Clusters

### Cluster A: Polytabloid / Straightening (Ch5, 2 sorries)
**Files:** SpechtModuleBasis (2 sorries — both Wall 3 chain)

- `twistedPolytabloid_pigeonhole_pair` (line 1375) — issue #2543,
  has-pr (PR #2550 in repair).
- `garnir_twisted_in_lower_span` (line 1614) — Wall 3 final assembly,
  blocked through #2500 → #2605.

Wall 3 chain diagram (current):

```
PR #2550 (C.1.a.ii pigeonhole, CONFLICTING) ──→ kills line 1375 once repaired
PR #2541 ✅ (C.1.b algorithm A) ─────────────→ landed this wave
                                                      │
#2605 (C.1.c rev2 mutual induction, critical-path) ──┴─→ #2520 (C.2 τ) ──┐
                                                                        │
                                                                        ├─→ #2500 (part D assembly) → kills line 1614
                                                                        │
                                                                        ┘
```

### Cluster B: Schur-Weyl chain closing `iso_of_formalCharacter_eq_schurPoly` (Ch5, 1 sorry)
**Files:** FormalCharacterIso (1 sorry — top-of-chain goal)

Wave 57 closes the equivariance anchor (#2540). The chain is now
purely C-tier irreducibility plus assembly:

```
#2582 (C-3, claimed) ──┐
                        │
#2610 (C-4a) ─┐         │
              ├─→ #2612 (C-4c assembly) ──→ #2493 (C final assembly) ──→ #2482 (#5) ──→ #2483 (#6) ──→ kills line 399
#2611 (C-4b) ─┘
```

### Cluster C: Ẽ/T framework wall (Ch6, 3 sorries) + blocked downstream (Ch2, 1 sorry)

**Files:** InfiniteTypeConstructions (3), Theorem2_1_2 (1)

- B1 (Wall 1): 3 sorries. Awaits Kim's Option A / B / A+C / B+C.
- B2 (Theorem 2.1.2 forward): 1 sorry blocked on B1.

Status unchanged since wave 54.

### Cluster D: Morita Theory (Ch9) — CLOSED (wave 50)

## Trajectory

| Wave | Sorries | Files | Items sorry-free | Date       |
|------|---------|-------|------------------|------------|
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
| 55   | 7       | 4     | 582/583 (99.8%)  | 2026-04-24 |
| 56   | 8       | 4     | 582/583 (99.8%)  | 2026-04-24 |
| **57** | **7** | **4** | **582/583 (99.8%)** | **2026-04-27** |

**Wave 57 trend:** Raw count back down to 7 (matching wave 55's count
and floor). Of the 7 current sorries:

- 3 are framework-wall stubs (Wall 1 Ẽ/T, await Kim).
- 1 is framework-blocked downstream (Theorem 2.1.2 forward → #2436).
- 2 are on the active Wall 3 chain (helper PR #2550 in repair, final
  assembly blocked through restructured C.1.c rev2 #2605).
- 1 is the top-of-chain Schur-Weyl goal (line 399), now blocked
  through `#2493 → #2612 → {#2610, #2611}` plus #2582.

## Honest Assessment

Wave 57 is the **Schur-Weyl C-tier wave**: the equivariance anchor
closed and the polynomial-identity infrastructure landed wholesale.

**Strengths:**

1. **Schur-Weyl equivariance closed.** The wave-56 decomposition anchor
   (`glTensorRep_equivariant_schurWeyl_decomposition`, line 774) closed
   via PR #2578. This kills the wave-56 net-positive and restores the
   sorry count to 7 — matching wave-55's count.

2. **Schur-Weyl C-1 + C-2 polynomial identities landed.** PR #2600
   established `formalCharacter (glTensorRep V n) = (∑ Xᵢ)^n` and
   PR #2606 established the polynomial identity
   `(∑ Xᵢ)^n = ∑ dim(Specht_λ) · schurPoly_λ`. Together with the
   equivariance anchor, the polynomial-side scaffolding for Schur-Weyl
   #5 / #6 is now complete; only the irreducibility steps (#2582, then
   #2610/#2611/#2612) remain before #2493 → #2482 → #2483.

3. **Explicit-eval analogue infrastructure.** PR #2579 introduced
   `Theorem5_18_4_GL_rep_decomposition_explicit` — an explicit-eval
   analogue of `Theorem5_18_4_GL_rep_decomposition` with bundled
   `FDRep` summands, ready for downstream consumers. PR #2607 then
   delegated the original to the explicit variant. PR #2599 had
   `glTensorRep_equivariant_schurWeyl_decomposition` consume the
   explicit form. Net effect: a single source of truth for
   downstream Schur-Weyl work, via the `_explicit` definition.

4. **`Module.Finite` propagation through bimodule chain.** PRs #2586
   (`V i`) and #2604 (`V i / S i` into `_explicit`) closed long-standing
   gaps that downstream proofs need. Both originated as review
   findings and closed cleanly.

5. **Wall 3 C.1.b Algorithm A landed.** PR #2541 (issue #2532 closed)
   completes the leading-tabloid elimination layer. Two open PRs at
   wave-56 are now down to one (#2550 in repair).

6. **Review chain caught up.** Seven review PRs landed
   (#2562, #2566, #2567, #2569, #2575, #2603, #2631) plus three
   review-finding refactors (#2576, #2577, #2585), covering every
   Schur-Weyl foundation tier through the equivariance + explicit pair
   *and* the polynomial-identity C-1 + C-2 landings. Audit queue is in
   lockstep with the feature queue.

**Concerns:**

1. **Wall 1 remains the longest-running open item.** Issue #2436 has
   not moved since wave 54. Until Kim picks A / B / A+C / B+C, these
   3 Ch6 sorries cannot be addressed and Theorem 2.1.2 forward
   (Cluster C downstream) cannot be unblocked. This wave is the third
   in a row with no Wall 1 movement. It now bottlenecks 4 of the 7
   remaining sorries (3 Ch6 + 1 Ch2).

2. **Wall 3 C.1.c was rejected mid-wave.** The wave-56 closure plan
   for the Wall 3 final-assembly glue step (#2533) was found unsound
   when worker session `add8c41f` reviewed it: Step 1's upstream
   lemma `TP ∈ V^λ` does not hold in general (missing a span-correction
   factor). #2533 was closed via supersession; replacement #2605
   (mutual-induction restructure) was filed and is `critical-path`,
   unclaimed. **This is the second proof-strategy refutation in the
   Wall 3 chain** (the first was the per-fibre strategy refuted at
   wave 56 #2521); the project now has two superseded plans on this
   chain. The mutual-induction strategy is not yet validated against
   counter-examples.

3. **PR #2550 has been in repair for ~3 days.** The wave-56 doc
   already flagged it as `mergeable=UNKNOWN`; it has since concretised
   to `CONFLICTING`. CI passes but the merge conflict is not
   self-resolving. The repair flow is dispatched but the conflict
   surface (rebases over PR #2541's substantial Wall 3 C.1.b code) is
   non-trivial.

4. **Schur-Weyl C-4 was decomposed mid-wave.** Issue #2583 (the
   original C-4 statement) was decomposed into #2610 + #2611 + #2612.
   This is a normal success path (per the worker-flow skill), but it
   indicates the original C-4 estimate was undersized. #2493 is now
   blocked one issue deeper than wave-56 predicted.

5. **Planner queue stagnation.** 18 consecutive no-op planner cycles
   ran between PR #2614 and PR #2627 with `POD_QUEUE_DEFICIT=3` flagged
   each cycle. The deficit was traced to GitHub search-index lag (~30
   min between label edits and search-API visibility) and is
   artifactual. This is a coordination-tool gap, not a productivity
   gap, but it does mean ~50 min of agent time was burned on no-ops.

**Current priority ordering:**

1. **Kim's framework decision on Wall 1 (#2436).** Unblocks 3 Ch6
   sorries + 1 Ch2 downstream. No worker action available until then.
2. **PR #2550 repair (Wall 3 C.1.a.ii pigeonhole).** `CONFLICTING`;
   in repair queue. Closes #2543 and kills the line-1375 sorry.
3. **#2605 (Wall 3 C.1.c rev2, critical-path).** Mutual-induction
   restructure. Substantial work but unblocks the entire Wall 3 D
   final-assembly chain (#2520 → #2500).
4. **#2582 (Schur-Weyl C-3) + #2610 + #2611 (Schur-Weyl C-4a/b).**
   Three independent simplicity sub-proofs; #2582 is claimed,
   #2610/#2611 are unclaimed. Together with #2612 final assembly they
   unblock #2493 → #2482 → #2483 → kills the line-399 sorry.
5. **#2601 / #2602 (refactor hygiene).** Lower priority; both pure
   refactor. #2608 review closed this wave (PR #2631 PASS); no
   pending audit on the polynomial-side critical path.

**If Wall 1 is resolved and the active chains close**: 4 Ch6/Ch2
framework-stub sorries are replaced or re-proved, Wall 3 closes
(−2 Ch5), Schur-Weyl closes (−1 Ch5). Floor would be **0 sorries**.
The narrowest path runs `#2436 → re-prove Ch6 + Ch2` plus
`PR #2550 → #2605 → #2520 → #2500 + (#2582 ∥ #2610 ∥ #2611) → #2612 → #2493 → #2482 → #2483`.
Closure window: subject to Kim's decision plus ~3 worker-days for the
chain completions, slightly looser than wave-56's "one decision plus a
day" estimate due to the C-4 decomposition and Wall 3 restructure.

## Design walls snapshot

- **Wall 1 unchanged.** Awaiting Kim's framework decision on #2436.
- **Wall 2 still closed.**
- **Wall 3 chain in flight, with one strategic pivot.** PR #2541
  (C.1.b) landed; PR #2550 (C.1.a.ii) in repair; #2605 (C.1.c rev2,
  mutual induction) replaces the rejected #2533. Final assembly
  (#2500) re-blocked through #2605.
- **Schur-Weyl chain advanced.** Equivariance anchor closed
  (#2540 ✓), polynomial identities (#2580, #2581) landed, explicit
  variant (#2572) landed, `Module.Finite` propagation (#2573, #2594)
  landed. Remaining: irreducibility tier (#2582, #2610, #2611, #2612)
  → assembly chain (#2493 → #2482 → #2483).

Refer to `progress/design-walls-wave57.md` for the updated decision
sheet.
