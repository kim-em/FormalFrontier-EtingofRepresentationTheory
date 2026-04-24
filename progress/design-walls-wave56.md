# Wave 56 — Design Walls Inbox

Snapshot of framework-level decisions blocking worker progress. The
wave-55 snapshot listed three walls and one active design topic; wave
56 closes Wall 2 outright, records that Wall 3 has decomposed into an
in-flight proof chain, and leaves Wall 1 unchanged. The Schur-Weyl
chain continues to advance normally.

---

## Wall 1 — Ẽ_n / T(p,q,r) indecomposability framework — UNCHANGED

**Context.** `etilde6v2Rep_isIndecomposable`,
`etilde7Rep_isIndecomposable`, and `t125Rep_isIndecomposable` remain
provably **false** for every m ≥ 1 in their current single-nilpotent-twist
construction. No mathematical movement since wave-55; see
`progress/indecomposability-framework-investigation.md` for the explicit
counter-examples.

**File state.** 3 sorries at lines 3344, 3599, 3826 of
`Chapter6/InfiniteTypeConstructions.lean` (line numbers shifted from
wave-55 due to intervening edits; the theorems are the same).

**Options** (unchanged):

- **Option A — Book's Tits-form / orbit-counting argument.** Lean
  algebraic-geometry infrastructure (orbit maps, dimension of
  quasi-projective varieties, constructible sets). Estimate: 6+ months.

- **Option B — Stronger explicit construction.** Couple multiple arms
  to block D/F with independent nilpotents, or add a γ-style
  center-to-center iso bridging independent arms. Estimate: weeks per
  case.

- **Option C — Subgraph transfer for non-sporadic T(p,q,r).** Partial
  step; does not close the sporadic Ẽ₆ / Ẽ₇ / Ẽ₈.

**Blocks.** 3 Ch6 sorries + 1 downstream Ch2 sorry (Theorem 2.1.2
forward bridge, via blocked issue #2401).

**Status.** Issue #2436 is `human-oversight`, `replan`. Three worker
agents have now tried to claim it since wave-55 (session `a3facc9e` in
PR #2526 among them). `coordination claim` correctly blocks these as
the issue is in `replan` state.

**Asks of Kim:** select Option A, B, A+C, or B+C — see the issue body
for full context. Longest-running open item.

---

## Wall 2 — `dTildeDim` vertex-type strategy — REMOVED

**Resolution.** PR #2495 landed the `dTildeRep_mapLinear_transport`
residual via a `dTildeCast` refactor that commutes `▸`-casts on
`dTildeRepMap`'s dimension equation with `LinearEquiv.funCongrLeft`
reindexing. Follow-up polish landed in PR #2524 (style: `show` → `change`),
and the wall was independently audited (PR #2518 / issue #2506 — all
four soundness questions passed).

**Residual sorry count after this wave: 0.** Wall 2 is no longer a
wall.

---

## Wall 3 — Garnir straightening induction measure — PROMOTED TO CHAIN

**Context.** `garnir_twisted_in_lower_span`
(`SpechtModuleBasis.lean:1332`) remains the combinatorial heart of the
straightening theorem. Wave-55 classified this as a framework wall
needing a commitment to one of Options 1–3. **Wave 56 committed to
dominance-induction (meditate PR #2529) and decomposed the proof into
a concrete multi-stage chain.**

**Chain structure (all issues filed and owned):**

- **Part A** — `garnirColReindex` + sign tracking (column-restandardizer
  API). **Landed:** PR #2503.
- **Part B** — `garnir_pigeonhole_collapse` (math heart). **Landed:**
  PR #2505.
- **Part C** — residual whole-sum grouping (parent #2499):
  - **C.1** — `twistedPolytabloid w σ` as ℂ-combination of polytabloids
    ψ_τ. Parent #2519 was itself decomposed:
    - **C.1.a** — support bound. Main theorem landed PR #2536. Two
      helpers:
      - **C.1.a.i** — fibre-coefficient-zero helper. Sign-reversing
        involution scaffold landed PR #2544; pigeonhole split into:
      - **C.1.a.ii** — `twistedPolytabloid_pigeonhole_pair`. **Issue
        #2543 has-pr (PR #2550 open).**
    - **C.1.b** — Leading-tabloid elimination (Algorithm A). **Issue
      #2532 has-pr (PR #2541 open, in repair).**
    - **C.1.c** — glue C.1.a + C.1.b. **Issue #2533 blocked** on
      #2543 + #2532.
  - **C.2** — τ classification into broadened disjunction. **Issue
    #2520 blocked** on #2533.
- **Part D** — final assembly closing `garnir_twisted_in_lower_span`.
  **Issue #2500 blocked** on #2533 + #2520.

**Meditate correctness anchor.** PR #2529 / issue #2522 developed the
**whole-sum cancellation strategy** (Garnir straightening by dominance
induction), validated on the three λ=(2,2) counter-examples from
wave-55 (σ=swap(0,1); w ∈ {(0,2,1), swap(1,2), (0,1,2)}). The previous
per-fibre reduction strategy was refuted mid-wave (PR #2521, session
`811935af`) and replaced with whole-sum grouping. The new strategy is
the correctness anchor for all downstream sub-issues.

**Status.** 2 open PRs (#2550, #2541) + 4 blocked sub-issues. No
framework decision needed — Wall 3 is promoted from wall to active
multi-stage proof.

**Risk.** The glue step (#2533) and final assembly (#2500) have not
yet been attempted. C.1.a was found mid-wave to need further
decomposition than the issue predicted; similar granularity surprises
at the glue step are possible.

---

## Active design topic (not a wall) — Schur-Weyl chain

**Context.** `iso_of_formalCharacter_eq_schurPoly`
(`Chapter5/FormalCharacterIso.lean:399`) — the top-of-chain goal
sorry. Wave-55 scoped this into a 6-issue chain; wave-56 executed the
bulk of the infrastructure.

**Sub-issue progress (wave 56 delta vs wave 55):**

| Sub | Issue | Wave-55 | Wave-56 | Summary |
|-----|-------|---------|---------|---------|
| #1  | #2461 | ✅ merged | ✅ merged | Tensor-degree homogeneity |
| #2a | #2477 | claimed | ✅ merged (PRs #2502, #2511, #2538) | Polynomial bridge |
| #2b | #2478 | blocked | ✅ merged (PRs #2528, #2539) | `polynomialRep_embeds_in_tensorPower` |
| #3  | #2458→#2491/2/3 | blocked | Part A ✅ (#2504), Part B partial (#2542 + #2540 claimed), Part C blocked (#2493) |
| #4  | #2462 | ✅ merged | ✅ merged | `schurPoly_linearIndependent` |
| #5  | #2482 | not yet filed | filed, blocked on #2493 | polynomial GL_N-rep ⊕ Schur modules |
| #6  | #2483 | not yet filed | filed, blocked on #2482 | final assembly |

**Collateral infra landed this wave:**
- PR #2509: explicit bimodule decomposition with evaluation formula.
- PR #2516: `formalCharacter` direct-sum additivity.
- PR #2534: trivial-tensor character multiplicativity.
- PR #2551: `hP_mul` derivation (from `ρ.map_mul` + `[CharZero k]`).

**Remaining sorry on the chain:**
`glTensorRep_equivariant_schurWeyl_decomposition`
(`FormalCharacterIso.lean:774`) — issue #2540, claimed. Expected ~1
session.

**Why still not a wall.** The chain is on schedule; sub-issues are
well-scoped and foundations land cleanly. Remaining risk is confined
to #2540's equivariance proof and the final #2483 assembly. No
framework decision needed.

---

## Meta

- **Wall 1** still needs Kim's framework decision. No worker action
  available. Longest-running open item in the project.
- **Wall 2** is closed. No further design needed.
- **Wall 3** is a chain, not a wall. 2 PRs open (#2550, #2541); the
  remaining sub-issues are ordered and owned.
- **Schur-Weyl chain** advances as a healthy multi-issue feature; one
  intentional decomposition anchor (#2540) remains.

**For comparison with wave 55:** wave-55 had 3 walls (Wall 1 urgent,
Wall 2 closeable mechanical, Wall 3 stale framework) + 1 healthy chain.
Wave-56 has **1 wall** (Wall 1, still human-gated) + **1 active chain**
(Wall 3, promoted from wall) + **1 ongoing chain** (Schur-Weyl). This
is the first wave since Wall 3 was first identified where the
framework-wall count is down to 1.
