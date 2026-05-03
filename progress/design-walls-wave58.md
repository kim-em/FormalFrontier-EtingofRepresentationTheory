# Wave 58 — Design Walls Inbox

Snapshot of framework-level decisions blocking worker progress.
Wave 57 recorded one wall (Wall 1) plus two active chains (Wall 3
with one strategic pivot, Schur-Weyl). Wave 58 retains the same
structural shape but with substantial structural movement on both
chains: Wall 3 has had two more redesign meditates (now three total
pivots since wave 56) and is escalated to a third meditate (#2676);
Schur-Weyl C-tier closed C-3 (#2582), C-4a sub-α (#2665), and C-4b
(#2646). Wall 1 is unchanged for the **fourth** consecutive wave.

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
`Chapter6/InfiniteTypeConstructions.lean` (line numbers unchanged
since wave 56).

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

**Status.** Issue #2436 is `human-oversight`, `replan`. Wave 58 is the
**fourth** consecutive wave with no Wall 1 movement. The issue is the
single longest-running open item in the project; it now bottlenecks
4 of the remaining 7 sorries (57%) — same proportion as wave 57, but
extended by another week.

**Asks of Kim:** select Option A, B, A+C, or B+C — see the issue body
for full context.

---

## Wall 2 — `dTildeDim` vertex-type strategy — REMOVED

**Status: still closed.** No regression in wave 58. Ch6 Wall 2 line
remains sorry-free.

---

## Wall 3 — Garnir straightening induction measure — CHAIN IN FLIGHT, THREE PIVOTS TOTAL

**Context.** `garnir_twisted_in_lower_span`
(`SpechtModuleBasis.lean:1726`, was 1614 in wave 57) — combinatorial
heart of the straightening theorem. Promoted from "wall" to "chain"
in wave 56 with the dominance-induction commitment (PR #2529).

**Wave-58 chain delta (substantial — full chain reorganization):**

- **Part A** — `garnirColReindex` + sign tracking. **Landed** wave 56
  (PR #2503).
- **Part B** — `garnir_pigeonhole_collapse`. **Landed** wave 56
  (PR #2505).
- **Part C** — residual whole-sum grouping (parent #2499):
  - **C.1** — parent #2519, decomposed into:
    - **C.1.a** — support bound. Main theorem landed wave 56 (PR
      #2536). Helpers:
      - **C.1.a.i** — fibre-coefficient-zero. Sign-reversing
        involution scaffold landed wave 56 (PR #2544).
      - **C.1.a.ii** — `twistedPolytabloid_pigeonhole_pair`.
        **Issue #2543, has-pr (PR #2550 open, `CONFLICTING`,
        static ~10 days).** No change in wave 58 — the repair has
        not landed.
    - **C.1.b** — Leading-tabloid elimination (Algorithm A).
      **Landed** wave 57 via PR #2541.
    - **C.1.c** — glue C.1.a + C.1.b. **THIRD STRATEGIC PIVOT.**
      Wave-57's #2605 (mutual-induction restructure) was decomposed
      this wave into aux helper #2648 + glue. Aux was further
      decomposed:
      - sub-X (#2651) **landed** via PR #2653
        (`polytabloidTab_in_lower_span_of_dominates`).
      - sub-Y (#2652) **abandoned** after a worker proved the
        col-std-at-tabloid existence sub-lemma is unsound (third
        refutation in the chain).
      The aux helper was redesigned via meditate **#2660** →
      `progress/algorithm-A-redesign.md` (merged via PR #2663). The
      redesign produced:
      - R1 (#2666) **landed** via PR #2669
        (`in_L_of_in_V_of_supp_bounded`).
      - R2 (#2667 — Algorithm A core). Two consecutive workers
        attempted R2 and both hit the **Q_high cancellation
        obstruction**: Strategy A's per-`q` dispatch leaves the
        Q_high region (where IH does not apply) requiring a
        sign-reversing involution simultaneously in `q` and the
        `Classical.choose`-defined `γ_q`. #2667 was closed forward
        to meditate **#2676** (R3).
      - R3 (#2676, **claimed `critical-path`**) — Q_high cancellation
        involution. Five deliverables: verify/refute sub-claim 3.1.3
        (`Q_eq' = ∅` for "Neither" `w`); construct/refute the
        involution `φ : Q_high → Q_high`; if construction fails,
        pivot to Strategy B (Q_eq'-via-cosets) or Strategy C (refactor
        TP into a different basis).
  - **C.2** — τ classification into broadened disjunction.
    **Issue #2520 still unclaimed; body references closed deps;
    semantically blocked on #2676.**
- **Part D** — final assembly closing `garnir_twisted_in_lower_span`.
  **Issue #2500 still unclaimed; body references closed deps;
  semantically blocked on #2676 + #2520.**

**Strategic pivot rationale (wave 58, third pivot):** The wave-57
plan #2605 committed to a mutual-induction restructure where the
Algorithm A aux helper (`garnir_twisted_in_lower_span_aux`) would
discharge the body via an Algorithm A loop. A worker on session
`494d71d1` proved that the col-std-at-tabloid existence sub-lemma
(needed by Algorithm A's loop step) is provably false in general:
column-standardization can fail to land at a column-standard
representative of any given tabloid orbit. The redesign note
`algorithm-A-redesign.md` (merged via #2663) replaces the unsound
combinatorial step with a well-posed reduction `f_w(σ) ∈ L_σ ⇐
f_w(σ) ∈ V` (where `V := span_ℂ {polytabloidTab : SYT → TabloidRep}`)
plus three candidate strategies (A, B, C) for closing `f_w(σ) ∈ V`.
Strategy A's per-`q` dispatch creates four regions (Q_low / Q_eq /
Q_eq' / Q_high), of which two (Q_eq', Q_high) need the IH sidestepped.
The Q_high case in particular needs the Q_high involution that #2676
investigates.

**Status.** One open PR carry-over (#2550, `CONFLICTING` ~10d). One
new critical-path meditate (#2676, claimed). Two unclaimed final-
assembly issues (#2520, #2500) with stale bodies awaiting R3 output.

**Risk.** This is the chain's **third** mid-strategy refutation
(per-fibre at wave 56, "TP ∈ V^λ first" at wave 57, col-std-at-tabloid
existence at wave 58). All three were caught by worker sessions
before substantial Lean work was wasted — the process is working as
designed. But each refutation costs roughly one wave of planner +
worker turnover, and the project now has three superseded plans on
this single chain. Strategy A (`algorithm-A-redesign.md` §2-3) has
**not** been independently validated against the wave-55 `λ=(2,2)`
counter-examples; doing so should be R3 meditate #2676's first step,
before committing to multi-day Lean work on the Q_high involution
itself. If Strategy A is also refuted, Strategies B / C remain as
fallbacks, but each costs another redesign cycle.

---

## Active design topic (not a wall) — Schur-Weyl chain

**Context.** `iso_of_formalCharacter_eq_schurPoly`
(`Chapter5/FormalCharacterIso.lean:399`) — the top-of-chain goal
sorry. Wave 55 scoped this into a 6-issue chain; wave 56 advanced
through Part B; wave 57 closed the equivariance anchor and landed
the polynomial-side foundations; wave 58 closes C-3 and lands the
bulk of the C-4 abstract algebraic infrastructure.

**Sub-issue progress (wave 58 delta vs wave 57):**

| Sub | Issue | Wave-57 | Wave-58 | Summary |
|-----|-------|---------|---------|---------|
| #1  | #2461 | ✅ merged | ✅ merged | Tensor-degree homogeneity |
| #2a | #2477 | ✅ merged | ✅ merged | Polynomial bridge |
| #2b | #2478 | ✅ merged | ✅ merged | `polynomialRep_embeds_in_tensorPower` |
| #3 A | #2491 | ✅ merged | ✅ merged | L_i FDRep GL_N structure |
| #3 B | #2492 / #2540 | ✅ merged | ✅ merged | Equivariance anchor |
| #3 C-1 | #2580 | ✅ merged | ✅ merged | formalCharacter (∑ Xᵢ)^n |
| #3 C-2 | #2581 | ✅ merged | ✅ merged | Polynomial identity |
| #3 C-2 combined | (none) | not yet filed | ✅ merged (PR #2637) | Combined dimension form |
| #3 C-3 | #2582 | claimed | **✅ closed via decomposition** (PR #2634 + #2646 + #2670) | Irreducibility of `L_i` |
| #3 C-3 wrapper | #2633 | not yet filed | ✅ merged (PR #2670) | `Theorem5_18_4_GL_rep_decomposition_simple` |
| #3 C-4a | #2610 | unclaimed | ✅ merged (decomposed; see C-4a-i / C-4a-ii) | Image of `c_λ` is simple |
| #3 C-4a-i | #2643 | not yet filed | decomposed into sub-α/β/γ | Algebraic block analysis |
| #3 C-4a-i sub-α | #2655 | not yet filed | ✅ merged (PR #2665) | Block factorization of `c_λ` |
| #3 C-4a-i sub-β | #2656 | not yet filed | replan; decomposed into β.1/β.2/β.3 | Off-block vanishing |
| #3 C-4a-i β.1 | #2682 | not yet filed | claimed | A-equivariant trace formula |
| #3 C-4a-i β.2 | #2683 | not yet filed | blocked on #2682 | Specht bridge |
| #3 C-4a-i β.3 | #2684 | not yet filed | blocked on #2682 + #2683 | Off-block assembly |
| #3 C-4a-i sub-γ | #2657 | not yet filed | blocked on #2656 cluster | Rank-1 projection |
| #3 C-4a-ii | #2644 | not yet filed | claimed ~6 days (possibly stale) | Abstract idempotent simplicity |
| #3 C-4b | #2611 | unclaimed | ✅ merged (PR #2646) | Transfer simplicity to GL_N |
| #3 C-4c | #2612 | blocked | blocked on #2644 + #2657 cluster | Final `schurModule_isSimple` |
| #3 C  | #2493 | blocked on #2612 | blocked on #2612 | Final `schurWeyl_gl_decomposition` |
| #4  | #2462 | ✅ merged | ✅ merged | `schurPoly_linearIndependent` |
| #5  | #2482 | blocked on #2493 | blocked on #2493 | polynomial GL_N-rep ⊕ Schur modules |
| #6  | #2483 | blocked on #2482 | blocked on #2482 | Final assembly |

**Collateral infra landed this wave:**
- PR #2637: combined dimension-form polynomial identity.
- PR #2640: heartbeat tightening on equivariance theorem.
- PR #2646: Schur-Weyl L_i C-4b transfer simplicity to GL_N.
- PR #2650: heartbeat tightening on `Theorem5_18_1_explicit`.
- PR #2654: MonoidAlgebra-simplicity transfer helper.
- PR #2662: drop `[CharZero k]` from `formalCharacter_glTensorRep_eq_pow`.
- PR #2664: extract `glHom` + per-component `ρ` helpers (refactor).
- PR #2665: Schur-Weyl L_i C-4a-i sub-α block factorization of `c_λ`.
- PR #2670: `Theorem5_18_4_GL_rep_decomposition_simple` wrapper.
- PR #2647 / PR #2677 / PR #2679 / PR #2680: audit reviews PASS.

**Why still not a wall.** The chain remains on schedule. The mid-wave
decompositions (#2582 worker decomposition into #2611 + #2633; #2643
into sub-α/β/γ; #2656 into β.1/β.2/β.3) are normal sub-issue
refinement (the original issues conflated multiple independent
algebraic steps). All sub-issues are well-scoped; no framework
decision needed.

**Remaining sorry on the chain:**
`iso_of_formalCharacter_eq_schurPoly`
(`FormalCharacterIso.lean:399`) — closes via #2483 once #2482 →
#2493 → #2612 → {#2644, #2657-via-#2656-cluster} cascade unblocks.
The line-774 wave-56 anchor and the entire Part B / C-1 / C-2 / C-3
plumbing are **all done**.

**Open follow-ups (audit / hygiene, not on the critical path):**
- All audits caught up. No pending review issues.

---

## Meta

- **Wall 1** still needs Kim's framework decision. No worker action
  available. Longest-running open item in the project; **fourth**
  consecutive wave with no movement.
- **Wall 2** is closed. No further design needed.
- **Wall 3** is a chain with **three strategic pivots** since wave
  56. R1 (#2669 ✓) + sub-X (#2653 ✓) helpers landed; R2 escalated to
  meditate #2676 (claimed, critical-path) after Q_high cancellation
  obstruction. Strategy A in `algorithm-A-redesign.md` should be
  sanity-checked against the wave-55 `λ=(2,2)` counter-examples
  before committing to multi-day Lean work on the Q_high involution.
  Final assembly issues #2520 / #2500 remain unclaimed with stale
  bodies; planner re-narration needed after #2676 produces output.
- **Schur-Weyl chain** advanced significantly: C-3 closed (#2582 ✓),
  C-4b landed (#2611 ✓ → PR #2646), C-4a sub-α landed (#2655 ✓ →
  PR #2665), wrapper landed (#2633 ✓ → PR #2670). Residual: C-4a-ii
  (#2644 claimed ~6d) + C-4a-i β-cluster (#2682 claimed / #2683 / #2684)
  + sub-γ (#2657) → #2612 → #2493 → #2482 → #2483.

**For comparison with wave 57:** wave-57 had 1 wall (Wall 1, human-
gated) + 1 active chain (Wall 3, with one pivot) + 1 ongoing chain
(Schur-Weyl, with equivariance anchor closed). Wave-58 has the same
structural shape: **1 wall** (Wall 1) + **1 active chain** (Wall 3,
with three pivots and meditate-in-flight) + **1 ongoing chain**
(Schur-Weyl, with C-3 closed and C-4 well-decomposed). The wave-58
distinguishing event is the **Schur-Weyl C-3 closure plus full C-4
decomposition** on the Schur-Weyl side, paired with the **third
Wall 3 strategic pivot** (col-std-at-tabloid existence refutation,
Algorithm A redesign via #2660 / #2663, R3 escalation to meditate
#2676). Net sorry count is unchanged for the fourth wave running —
both critical paths are 2-3 substantive PRs from a closure but
neither has fired yet.
