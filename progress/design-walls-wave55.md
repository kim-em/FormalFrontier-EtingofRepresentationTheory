# Wave 55 — Design Walls Inbox

Snapshot of framework-level decisions blocking worker progress. The
wave-54 snapshot listed three walls. Wave 55 closes one of them
(Wall 2, by Option a), shrinks one (Wall 1, scaffolding collapse but
same wall), and leaves one unchanged (Wall 3). It also surfaces an
ongoing **non-wall** design topic (Schur-Weyl chain) that is in active
flight.

This file is short on purpose. The detail is in the linked documents.

---

## Wall 1 — Ẽ_n / T(p,q,r) indecomposability framework — UNCHANGED

**Context.** `etilde6v2Rep_isIndecomposable`,
`etilde7Rep_isIndecomposable`, and `t125Rep_isIndecomposable` are all
provably **false** for every m ≥ 1 in their current single-nilpotent-twist
construction. The mathematical refutation is unchanged from wave 54;
see `progress/indecomposability-framework-investigation.md` for the
explicit counter-examples (`etilde7Rep 1` and `t125Rep 1`).

**Wave 55 change:** PR #2441 collapsed the 10 refuted sub-sorries into
3 single sorries — one per representation, at lines 3178, 3433, 3660 of
`Chapter6/InfiniteTypeConstructions.lean`. The single sorries each carry
a comment explaining that the framework is refuted and pointing at this
wall. **No mathematical movement.** The collapse is purely a visibility /
hygiene improvement.

`d5tildeRep_isIndecomposable` continues to escape this wall via its
γ-style center-to-center iso bridge (nilpotent `I − N` is unipotent
hence invertible).

**Options** (unchanged from wave 54):

- **Option A — Book's Tits-form / orbit-counting argument.** Lean
  algebraic-geometry infrastructure (orbit maps, dimension of
  quasi-projective varieties, constructible sets). Estimate: 6+ months.

- **Option B — Stronger explicit construction.** Couple multiple arms
  to block D/F with independent nilpotents, or add a γ-style
  center-to-center iso bridging independent arms. Estimate: weeks per
  case; the four `etilde{6,7,8}Rep` / `t125Rep` cases must each be
  reworked.

- **Option C — Subgraph transfer for non-sporadic T(p,q,r).** Partial
  step useful alongside A or B; does not close the sporadic Ẽ₆ / Ẽ₇ /
  Ẽ₈.

**Blocks.** 3 Ch6 sorries + 1 downstream Ch2 sorry (Theorem 2.1.2
forward bridge, via blocked issue #2401).

**Status.** Issue #2436 is `human-oversight`. Two worker agents have
already skipped it requesting Kim's option choice. A third claim
attempt was correctly blocked by `coordination claim` (the issue is in
`replan` state and cannot be re-claimed).

**Asks of Kim:** select Option A, B, A+C, or B+C — see the issue body
for full context.

---

## Wall 2 — `dTildeDim` vertex-type strategy — RESOLVED (Option a)

**Context.** Wave 54 noted that `dTildeRep_isIndecomposable` was
blocked at the Lean level: `dTildeDim k m v` did not reduce by
`rfl`/`dsimp` at k-dependent vertices because the definition
case-split on `v.val`'s position relative to `k + 6` was opaque to the
elaborator.

**Wave 55 resolution.** Wall 2 chose **Option a (custom inductive
vertex type)** and executed it in stages:

| Stage | PR    | What landed |
|-------|-------|-------------|
| A     | #2448 | `DTildeVertex k` inductive + `dTildeDim'` by pattern matching |
| B     | #2449 | Migrate `dTildeRep'` to `DTildeVertex k`, providing `dTildeRep'_isIndecomposable` |
| C₁    | #2460 | Main math: `dTildeRep'_isIndecomposable` proof complete |
| C₂    | #2475 | Stage C transport skeleton — 4/8 arrow cases by `rfl`, 4/8 deferred |

**Residual.** A single sorry remains at
`Chapter6/InfiniteTypeConstructions.lean:2958` —
`dTildeRep_mapLinear_transport`. This is the **map-agreement transport**
lemma between the original `Fin (k + 6)`-indexed `dTildeRep` and the
new `DTildeVertex k`-indexed `dTildeRep'`. The four hard arrow cases
(`pathMid → pathMid`, `pathMid → branchRight`, `rightLeaf1 →
branchRight`, `rightLeaf2 → branchRight`) need explicit pointwise
analysis to commute `▸`-casts on `dTildeRepMap`'s dimension equation
with `LinearEquiv.funCongrLeft` reindexing in `dTildeTransportEquiv`.

**Status.** Issue #2479 (`feat(Ch6): close dTildeRep_mapLinear_transport
via refactor or per-primitive lemmas (Wall 2 Stage C residual)`) is
**claimed**. Issue body documents that previous strategies
(`generalize_proofs`, HEq casting via `eqRec_heq_self`, `simp` with
`dif_*` lemmas) all failed; the recommended approach is either a
refactor of `dTildeRepMap` to make the cast structure transparent, or
per-primitive lemmas (`dTildePathId_transport`, `starEmbed1_transport`,
`starEmbed2_transport`) that absorb the cast into named bridges.

**Implication.** This wall no longer requires a framework decision. It
is a Lean-mechanics task. Once #2479 lands, Wall 2 is fully closed.

---

## Wall 3 — Garnir straightening induction measure — UNCHANGED

**Context.** `garnir_twisted_in_lower_span`
(`SpechtModuleBasis.lean:964`) is **false** at λ=(2,2), σ=swap(0,1) in
its previous form. Wave 55 included PR #2443 (a soundness fix flipping
the dominance direction in the statement) and PR #2455 (counter-example
refuting the `garnir_term_sametab_rowInv_lt` follow-on). The
combinatorial heart sorry remains.

**Session analysis.**
- Session 9cfda69f on closed issue #2425 — original refutation.
- Session on closed issue #2454 — refutation of follow-on
  (`progress/20260423T...md` for #2455 details).

**Options** (unchanged from wave 54):

- **Option 1 — Column-based induction (classical James Ch. 8 / Fulton
  Ch. 7).** Rewrite `SpechtModuleBasis` to traverse via column
  rearrangements rather than row-inversion count. ~100 lines of
  inductive restructuring.

- **Option 2 — Broaden the allowed τ set.** Permit τ's whose tabloid
  is strictly dominated by σ's, with a corresponding adjustment in
  `polytabloidTab_column_standard_in_span`.

- **Option 3 — Maximal-tabloid corner case.** Column-restandardize σ
  explicitly for the maximal-but-row-inverted edge case rather than
  routing through the Garnir identity.

The `#2450` issue body suggests a fresh angle —
**whole-sum cancellation** (showing that the entire Garnir term sum
collapses to a sum of dominated polytabloids, not by per-term
classification but by recognising algebraic cancellation across the
sum). This is a refinement of Option 1's spirit; no commitment yet.

**Blocks.** 1 Ch5 sorry (`garnir_twisted_in_lower_span`). Downstream:
`polytabloidTab_column_standard_in_span` → Ch5 dimV_λ theorem.

**Status.** Issue #2450 is `agent-plan` and unclaimed. No worker has
attempted whole-sum cancellation yet.

---

## Active design topic (not a wall) — Schur-Weyl chain

**Context.** `iso_of_formalCharacter_eq_schurPoly`
(`Chapter5/FormalCharacterIso.lean:395`) was wave 54's "Mathlib gap"
sorry. Wave 55 reframed it via `progress/schur-weyl-scoping.md`
(PR #2442) as a **6-issue in-project chain**, not a multi-month
Mathlib build.

**Sub-issue progress (wave 55):**

| Sub | Issue | Status     | What it does                                              |
|-----|-------|------------|-----------------------------------------------------------|
| #1  | #2461 | ✅ merged  | Tensor-degree homogeneity from `formalCharacter = schurPoly` |
| #2a | #2477 | claimed    | Bridge homogeneous deg-n polys in `g_ij` ↪ `V^⊗n ⊗ (V^*)^⊗n` as GL_N-rep |
| #2b | #2478 | blocked on #2477 | Assemble poly GL_N-rep embedding into `(V^⊗n)^m` via matrix coefficients |
| #3  | #2458 | blocked on #2472 | Identify `Theorem5_18_4` `L_i` summands with `SchurModule` |
| #4  | #2462 | ✅ merged  | `schurPoly_linearIndependent`                             |
| #5  | —     | not yet filed | (filed after #2 and #3 land)                          |
| #6  | —     | not yet filed | (final wrap-up to the original sorry)                  |

**Bimodule foundation track** (parallel work to support #3):
- PR #2467: `isotypicDirectSumEquiv` + `schurEvaluationEquiv`
- PR #2473: `centralizerToEndA` + `centralizerModuleHom` + range lemma
- PR #2476: `homIsotypicBridge` + `Theorem5_18_1_bimodule_decomposition`
  (full bimodule form `E ≃[k] ⨁ᵢ Vᵢ ⊗[k] Lᵢ` with `Lᵢ := Vᵢ →ₗ[A] E` as
  a genuine `B`-module).
- Issue #2472 (claimed): upgrade `Theorem5_18_4_decomposition` to use
  the bimodule form. Unblocks #2458.

**Why this isn't a wall.** No framework decision needed. The chain
exists; sub-issues are well-scoped; foundations land cleanly. Risk: if
#2472 (Theorem5_18_4 bimodule upgrade) hits an obstacle that forces a
rebuild from `Theorem5_18_1` directly rather than through
`5_18_4_partition_decomposition` (the noted risk in
`schur-weyl-scoping.md`), the chain may need re-scoping. But that's
risk, not a current wall.

**Status.** Active. Next planner cycle should not introduce friction
here — workers can keep advancing #2472, #2477, #2478 in parallel,
with #2458 coming online when #2472 lands.

---

## Meta

- **Wall 1** still needs Kim's framework decision. No worker action
  available.
- **Wall 2** closes when #2479 lands. No further design needed.
- **Wall 3** still needs framework commitment. Issue #2450 unclaimed;
  no worker has tried whole-sum cancellation yet.
- **Schur-Weyl chain** advances normally as a multi-issue feature, not
  a wall.

**For comparison with wave 54:** the wave-54 inbox listed three walls
of equal urgency; the wave-55 inbox has one urgent unblocking (Wall 1,
Kim), one closeable mechanical residual (Wall 2 / #2479), one stale
framework wall (Wall 3 / #2450), and one healthy chain in flight
(Schur-Weyl / 4 active issues).
