# Wave 57 — Design Walls Inbox

Snapshot of framework-level decisions blocking worker progress. Wave 56
recorded one wall (Wall 1) plus two active chains (Wall 3, Schur-Weyl).
Wave 57 closes the Schur-Weyl equivariance anchor and advances the
Schur-Weyl chain into pure C-tier irreducibility work, but flags one
strategic pivot in Wall 3 (the C.1.c glue step's #2533 plan was
rejected as unsound; replacement #2605 with mutual induction is now the
critical path). Wall 1 is unchanged for the third consecutive wave.

---

## Wall 1 — Ẽ_n / T(p,q,r) indecomposability framework — UNCHANGED

**Context.** `etilde6v2Rep_isIndecomposable`,
`etilde7Rep_isIndecomposable`, and `t125Rep_isIndecomposable` remain
provably **false** for every m ≥ 1 in their current
single-nilpotent-twist construction. No mathematical movement since
wave 54; see
`progress/indecomposability-framework-investigation.md` for the
explicit counter-examples.

**File state.** 3 sorries at lines 3344, 3599, 3826 of
`Chapter6/InfiniteTypeConstructions.lean` (line numbers unchanged from
wave 56).

**Options** (unchanged):

- **Option A — Book's Tits-form / orbit-counting argument.** Lean
  algebraic-geometry infrastructure (orbit maps, dimension of
  quasi-projective varieties, constructible sets). Estimate: 6+
  months.

- **Option B — Stronger explicit construction.** Couple multiple arms
  to block D/F with independent nilpotents, or add a γ-style
  center-to-center iso bridging independent arms. Estimate: weeks per
  case.

- **Option C — Subgraph transfer for non-sporadic T(p,q,r).** Partial
  step; does not close the sporadic Ẽ₆ / Ẽ₇ / Ẽ₈.

**Blocks.** 3 Ch6 sorries + 1 downstream Ch2 sorry (Theorem 2.1.2
forward bridge, via blocked issue #2401).

**Status.** Issue #2436 is `human-oversight`, `replan`. Wave 57 is the
third consecutive wave with no Wall 1 movement. The issue is the
single longest-running open item in the project; it now bottlenecks
4 of the remaining 7 sorries (57%).

**Asks of Kim:** select Option A, B, A+C, or B+C — see the issue body
for full context.

---

## Wall 2 — `dTildeDim` vertex-type strategy — REMOVED

**Status: still closed.** No regression in wave 57. PR #2495 (wave 56)
landed `dTildeRep_mapLinear_transport` via the `dTildeCast` refactor,
followed by polish #2517 / #2524 and review audit #2518. Ch6 Wall 2
line remains sorry-free.

---

## Wall 3 — Garnir straightening induction measure — CHAIN IN FLIGHT, ONE STRATEGIC PIVOT

**Context.** `garnir_twisted_in_lower_span`
(`SpechtModuleBasis.lean:1614`) — combinatorial heart of the
straightening theorem. Promoted from "wall" to "chain" in wave 56 with
the dominance-induction commitment (PR #2529).

**Wave-57 chain delta:**

- **Part A** — `garnirColReindex` + sign tracking. **Landed** wave 56
  (PR #2503).
- **Part B** — `garnir_pigeonhole_collapse`. **Landed** wave 56
  (PR #2505).
- **Part C** — residual whole-sum grouping (parent #2499):
  - **C.1** — parent #2519, decomposed into:
    - **C.1.a** — support bound. Main theorem landed wave 56 (PR
      #2536). Helpers:
      - **C.1.a.i** — fibre-coefficient-zero. Sign-reversing
        involution scaffold landed wave 56 (PR #2544). Pigeonhole
        helper split into:
      - **C.1.a.ii** — `twistedPolytabloid_pigeonhole_pair`.
        **Issue #2543, has-pr (PR #2550 open, `CONFLICTING`, in
        repair queue).** No change in wave 57 — the repair has not
        landed yet.
    - **C.1.b** — Leading-tabloid elimination (Algorithm A).
      **CLOSED this wave** via PR #2541 (issue #2532 closed).
    - **C.1.c** — glue C.1.a + C.1.b. **STRATEGIC PIVOT.** Wave-56's
      issue #2533 (Step-1-then-Step-2 glue plan) was closed via
      supersession after worker session `add8c41f` showed Step 1's
      upstream `TP ∈ V^λ` lemma was unsound (the twisted polytabloid
      does not in general lie in V^λ without an additional
      span-correction factor). Replacement issue **#2605** (Wall 3
      C.1.c rev2 — mutual-induction restructure) is filed and
      labeled `critical-path`. Unclaimed.
  - **C.2** — τ classification into broadened disjunction.
    **Issue #2520 re-blocked** on #2605 (was on #2533).
- **Part D** — final assembly closing `garnir_twisted_in_lower_span`.
  **Issue #2500 re-blocked** on #2605 + #2520.

**Strategic pivot rationale (`add8c41f`):** The wave-56 plan committed
to a two-step C.1.c glue: Step 1 prove `TP w σ ∈ V^λ` (the span of
polytabloids), Step 2 reduce TP via support-bound + Algorithm A. The
worker showed Step 1 is provably false in general — `V^λ` is the
ℂ-span of polytabloids `e_τ` for column-standard `τ`, but the column-
standardisation of `w · q⁻¹ · σ` introduces sign and reindexing
factors that take the term **outside** `V^λ` until Algorithm A is
applied. The corrected mutual-induction strategy in #2605 interleaves
Algorithm A with the support-bound reduction so that no intermediate
term needs to live in `V^λ` outside the induction's scope.

**Status.** Two open PRs at wave-56 (#2541, #2550) → one this wave
(#2550 only; #2541 landed). Plus one new critical-path issue (#2605)
replacing the rejected #2533.

**Risk.** This is the chain's **second** mid-strategy refutation
(first was #2521 in wave 56 retiring per-fibre reduction, now this
one retiring "TP ∈ V^λ first"). Both refutations were caught by
worker sessions before substantial Lean work was wasted, which is the
process working as designed. But it does mean the mutual-induction
plan in #2605 has not been independently validated against the wave-55
λ=(2,2) counter-examples — the prudent next step on #2605 is to
sanity-check the strategy against those before committing to a
multi-day proof effort.

---

## Active design topic (not a wall) — Schur-Weyl chain

**Context.** `iso_of_formalCharacter_eq_schurPoly`
(`Chapter5/FormalCharacterIso.lean:399`) — the top-of-chain goal sorry.
Wave 55 scoped this into a 6-issue chain; wave 56 advanced through
Part B; wave 57 closes the equivariance anchor and lands all of the
polynomial-side foundations.

**Sub-issue progress (wave 57 delta vs wave 56):**

| Sub | Issue | Wave-56 | Wave-57 | Summary |
|-----|-------|---------|---------|---------|
| #1  | #2461 | ✅ merged | ✅ merged | Tensor-degree homogeneity |
| #2a | #2477 | ✅ merged | ✅ merged | Polynomial bridge |
| #2b | #2478 | ✅ merged | ✅ merged | `polynomialRep_embeds_in_tensorPower` |
| #3 A | #2491 | ✅ merged | ✅ merged | L_i FDRep GL_N structure |
| #3 B | #2492 / #2540 | partial (#2540 claimed) | ✅ merged (PR #2578) | Equivariance anchor |
| #3 C-1 | #2580 | not yet filed | ✅ merged (PR #2600) | formalCharacter (∑ Xᵢ)^n |
| #3 C-2 | #2581 | not yet filed | ✅ merged (PR #2606) | Polynomial identity |
| #3 C-3 | #2582 | not yet filed | claimed | Irreducibility of `L_i` |
| #3 C-4a | #2610 | not yet filed | unclaimed | Image of `c_λ` is simple |
| #3 C-4b | #2611 | not yet filed | unclaimed | Transfer simplicity to GL_N |
| #3 C-4c | #2612 | not yet filed | blocked on #2610 + #2611 | Final `schurModule_isSimple` |
| #3 C  | #2493 | blocked on #2540 | blocked on #2612 | Final `schurWeyl_gl_decomposition` |
| #4  | #2462 | ✅ merged | ✅ merged | `schurPoly_linearIndependent` |
| #5  | #2482 | blocked on #2493 | blocked on #2493 | polynomial GL_N-rep ⊕ Schur modules |
| #6  | #2483 | blocked on #2482 | blocked on #2482 | Final assembly |

**Collateral infra landed this wave:**
- PR #2578: equivariance anchor closed (#2540).
- PR #2579: `Theorem5_18_4_GL_rep_decomposition_explicit` (#2572).
- PR #2586: `Module.Finite k (V i)` propagation (#2573).
- PR #2598: heartbeat-bump tightening in `Theorem5_18_1` (#2574).
- PR #2599: consume `_explicit` in equivariance theorem (#2589).
- PR #2604: `Module.Finite k (V i / S i)` propagation (#2594).
- PR #2607: delegate `Theorem5_18_4_GL_rep_decomposition` to
  `_explicit` (#2590).
- PRs #2562, #2566, #2567, #2569, #2575, #2603: review audits across
  the foundation tier.
- PRs #2576, #2577, #2585: drop unused `[CharZero k]` instances.
- PRs #2587, #2588: docstring fixes.

**Why still not a wall.** The chain remains on schedule. The
mid-wave decomposition of #2583 into #2610 + #2611 + #2612 is normal
sub-issue refinement (the original #2583 conflated two independent
simplicity proofs into one). All sub-issues are well-scoped; no
framework decision needed.

**Remaining sorry on the chain:**
`iso_of_formalCharacter_eq_schurPoly`
(`FormalCharacterIso.lean:399`) — closes via #2483 once #2482 →
#2493 → #2612 → {#2610, #2611} ∥ #2582 cascade unblocks. The
line-774 wave-56 anchor `glTensorRep_equivariant_schurWeyl_decomposition`
is **gone**.

**Open follow-ups (audit / hygiene, not on the critical path):**
- #2608 (review): audit Schur-Weyl L_i polynomial C-1 + C-2 (#2600 +
  #2606). **CLOSED this wave** via PR #2631 — both PRs PASS, zero new
  sorries introduced.
- #2601 (refactor): tighten heartbeat bump on equivariance theorem.
- #2602 (refactor): extract `glHom` + per-component-`ρ` helpers.
  Unblocked this wave (#2590 closed).

---

## Meta

- **Wall 1** still needs Kim's framework decision. No worker action
  available. Longest-running open item in the project; third
  consecutive wave with no movement.
- **Wall 2** is closed. No further design needed.
- **Wall 3** is a chain with one strategic pivot. C.1.b landed
  (PR #2541 ✓); C.1.a.ii in repair (#2550); C.1.c rev2 (#2605,
  critical-path, unclaimed) replaces the rejected #2533. The mutual-
  induction strategy in #2605 should be sanity-checked against the
  wave-55 λ=(2,2) counter-examples before committing to multi-day
  Lean work.
- **Schur-Weyl chain** advances; equivariance anchor closed
  (#2540 ✓), polynomial identities landed (#2580, #2581), `Module.Finite`
  propagation landed (#2573, #2594). Irreducibility tier
  (#2582, #2610, #2611, #2612) is the residual blocker for #2493 →
  #2482 → #2483.

**For comparison with wave 56:** wave-56 had 1 wall (Wall 1, human-
gated) + 1 active chain (Wall 3, promoted from wall) + 1 ongoing
chain (Schur-Weyl). Wave-57 has the same structural shape: **1 wall**
(Wall 1) + **1 active chain** (Wall 3, with pivot) + **1 ongoing
chain** (Schur-Weyl, with equivariance anchor closed). The wave-57
distinguishing event is the **Schur-Weyl equivariance closure** plus
the **polynomial-identity wholesale landing** (C-1 + C-2) — a
substantial single-wave delivery on the Schur-Weyl side, paired with a
strategic pivot on the Wall 3 side.
