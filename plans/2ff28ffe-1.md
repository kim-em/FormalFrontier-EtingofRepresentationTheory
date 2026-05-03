## Current state

Wall 3 closure is gated on a single sorry —
`garnir_twisted_in_lower_span` at
`EtingofRepresentationTheory/Chapter5/SpechtModuleBasis.lean:1681`.
The redesign note `progress/algorithm-A-redesign.md` (merged via
#2663, meditate #2660) reduced the goal to

```
twistedPolytabloid w σ ∈ V
  (V := Submodule.span ℂ (Set.range (polytabloidTab : SYT → TabloidRep)))
```

and recommended **Strategy A** — a per-`q` dispatch on `Q_λ` via
column-restandardisation `γ_q := garnirColReindex σ w q` and
`τ_q := γ_q · w · q⁻¹ · σ`, with the IH
`ψ_{τ'} ∈ V` available at strictly smaller `(srRank, rowInvCount')`.

The dispatch yields four regions

```
Q_low  := { q | [τ_q] ≺ [σ] }                       -- IH applies
Q_eq   := { q | [τ_q] = [σ] ∧ rowInv τ_q < rowInv σ}-- IH applies
Q_eq'  := { q | [τ_q] = [σ] ∧ rowInv τ_q ≥ rowInv σ}-- IH does NOT apply
Q_high := { q | [τ_q] ≻ [σ] }                       -- IH does NOT apply
```

and reduces the proof to two open sub-claims:

* **3.1.2 (Q_high cancellation)** — the partial sum
  `Σ_{q ∈ Q_high} sign(q) · δ_{[w q⁻¹ σ]}` vanishes via a
  sign-reversing involution `φ : Q_high → Q_high`.
* **3.1.3 (Q_eq' empty)** — for "Neither" `w` (`w ≠ 1`,
  `w ∉ ColumnSubgroup`, `w ∉ RowSubgroup`), `Q_eq' = ∅`.

Two consecutive workers attempted Strategy A on issue #2667 and
escalated:

* Session `1c0e4a24` ran ~10 hours, no commits.
* Session `7bb361bf` performed a focused investigation
  (see [#2667 comment](https://github.com/FormalFrontier/Etingof-RepresentationTheory-draft1/issues/2667#issuecomment-)) and skipped with `replan`, formally
  invoking the redesign note's R3 escalation path (§5.3). Their
  investigation isolated the obstruction:

> Q_high arises EITHER because `[w q⁻¹ σ] ≻ [σ]` (in which case the
> existing involution in `twistedPolytabloid_apply_of_not_dominates`
> handles it) OR because `[w q⁻¹ σ] ⪯ [σ]` and `γ_q` strictly increased
> dominance to push past `[σ]`. The latter case is NOT covered by any
> existing involution. Furthermore `γ_q = garnirColReindex σ w q` is
> `Classical.choose`-defined, so the involution must be constructed
> in terms of the original `q` and the column-restandardisation
> structure simultaneously.

This is exactly the contingency the redesign note §5.3 anticipated.

## Deliverables

Produce a meditate note at
`progress/q-high-involution.md` containing:

1. **Sub-claim 3.1.3 verification (or refutation)**.
   Determine whether `Q_eq' = ∅` for "Neither" `w`. Two routes:
   * If empty: prove it directly (~1 page argument). The dispatch
     simplifies to `Q_low ∪ Q_eq` (IH closes) plus `Q_high`
     (involution still needed).
   * If non-empty: produce a counter-example `(λ, σ, w, q)` and
     describe how the sub-case must be handled (likely routes
     through Sub-claim 3.1.1 residual cancellation).

2. **Sub-claim 3.1.2 attack — the Q_high involution**.
   Either:
   * **(a)** Construct an explicit map `φ : Q_high → Q_high` with
     `φ ∘ φ = id`, `sign(φ(q)) = -sign(q)`, and
     `[w · φ(q)⁻¹ · σ] = [w · q⁻¹ · σ]` (so the corresponding `δ`
     terms cancel). Validate on the running example
     `λ = (2,2)`, `σ = swap(0,1)` (the `Q_high` case identified in
     the redesign note §4.2). Sketch a Lean-level proof outline
     including the well-foundedness of `Q_high`-stability and
     the bookkeeping for `γ_q`.

     Reference template:
     `twistedPolytabloid_apply_of_not_dominates`
     (`SpechtModuleBasis.lean:1506`) gives `q ↦ q · swap(a₁, a₂)`
     where `(a₁, a₂)` is a pigeonhole-derived column pair with
     same `w`-image row. The Q_high analog must additionally
     **stay within Q_high** (the existing involution has no such
     constraint), which is the key new requirement.

   * **(b)** Refute (a) — produce an explicit `(λ, σ, w)` where
     `Σ_{q ∈ Q_high} sign(q) · δ_{[w q⁻¹ σ]} ≠ 0`, and document
     why no involution can exist.

3. **Pivot plan if (b)**.
   If the involution is refuted, spell out the next attack:
   * Strategy C from the redesign note §3.3 (coarser support
     filtration measure replacing `srRank`), with concrete
     pseudocode and a re-decomposition into follow-up issues.
   * OR a third strategy if the worker discovers one during the
     investigation.

4. **Re-decomposition**.
   Based on the meditate's findings, list the follow-up
   implementation issues. Each must be single-session-sized
   (≤ 200 lines, ≤ 2 files). Suggested shape:
   * R2.a — `twistedPolytabloid_mem_V_Q_low_eq` (the easy regions
     via IH), ~60–100 lines.
   * R2.b — Q_high cancellation lemma (the involution from
     Deliverable 2(a)), ~80–150 lines.
   * R2.c — Final assembly of `twistedPolytabloid_mem_V` and the
     ≤ 5-line corollary `garnir_twisted_in_lower_span` via R1
     (`in_L_of_in_V_of_supp_bounded`, line 1438, already merged).

   For each follow-up: title, one-paragraph scope, dependencies.
   The next planner cycle will turn these into `feature` issues.

5. **Counter-example record (additive)**.
   Append any new counter-examples discovered during the
   investigation to `progress/algorithm-A-redesign.md` §4 (or to
   the new note, cross-referenced). Future workers must not retry
   refuted constructions.

## Context

* **File under investigation**:
  `EtingofRepresentationTheory/Chapter5/SpechtModuleBasis.lean`,
  specifically the `garnir_twisted_in_lower_span` sorry at line
  1681, and the surrounding `twistedPolytabloid` /
  `garnirColReindex` machinery.
* **Existing API the meditate may consume**:
  - line 1506: `twistedPolytabloid_apply_of_not_dominates`
    (the involution template for sub-claim 3.1.2 — `q ↦ q · swap(a₁, a₂)`
    with `(a₁, a₂)` a column pair sharing the same `w`-image row).
  - line 1668: `twistedPolytabloid_support_bound` (gives
    `[α] ⪯ [σ]` for non-zero coefficient on `δ_{[α]}`).
  - line 1438: `in_L_of_in_V_of_supp_bounded` (R1 bridge — closes
    `f_w(σ) ∈ L_σ` once we have `f_w(σ) ∈ V`).
  - lines 925–976: `garnirColReindex` family (col-restandardisation
    machinery; `γ_q` is `Classical.choose`-defined here).
  - line 1444: `twistedPolytabloid_pigeonhole_pair`
    (sign-cancellation skeleton, useful precedent).
* **Predecessor analyses** (read end-to-end before starting):
  - `progress/algorithm-A-redesign.md` §3.1 (Strategy A), §3.3
    (Strategy C fallback), §4 (counter-example record), §5.3
    (R3 scope — exactly this issue).
  - [#2667 skip comment](https://github.com/FormalFrontier/Etingof-RepresentationTheory-draft1/issues/2667) by session `7bb361bf`
    (the most recent and most concrete obstruction analysis).
* **Sibling issues consuming this work**: the meditate's output
  unblocks the entire Wall 3 closure path:
  - #2543 / PR #2550 (`twistedPolytabloid_pigeonhole_pair` C.1.a.ii) —
    independent companion lemma, currently in repair queue.
  - #2520, #2500 (Wall 3 D-side) — depend on the
    `garnir_twisted_in_lower_span` closure.
  - Closing #2667 reduces the sorry count from 7 → 6 across the
    entire repository.

## Strategy notes (from the redesign note §5.3 and #2667 worker)

* **Stay focused on Q_high.** The R1 bridge and the per-`q` dispatch
  for `Q_low ∪ Q_eq` are not in dispute; they will be implemented
  cleanly once the involution exists. This meditate is purely about
  the sub-claim 3.1.2 obstruction.
* **`λ = (2,2)`, `σ = swap(0,1)` is the smallest concrete case
  exercising Q_high**; pencil-and-paper verification on this
  example is mandatory before claiming an involution works.
* **Do not retry Strategy B.** The redesign note §3.2 proved it
  circular (`Σ_{Neither} ∈ V ⇔ ψ_σ ∈ V`).
* **Do not retry the col-std existence sub-lemma.** The redesign
  note §1.4 + §4 documents why it is impossible (the `[{2,3}|{0,1}]`
  counter-example for `λ = (2,2)`).

## Verification

* `progress/q-high-involution.md` exists with sections for each of
  the five deliverables above.
* The meditate produces either:
  * an explicit Q_high involution + Lean-level proof outline + small
    re-decomposition into ≤ 3 feature issues, OR
  * a refutation of Strategy A 3.1.2 + a concrete Strategy C (or
    alternative) plan + re-decomposition.
* The follow-up issue list is concrete enough that the next planner
  cycle can post `feature` issues without further analysis (titles,
  scopes, dependencies, ≤ 200-line sizing).
* If a code-level prototype is produced (e.g. a small `Q_high`
  finset construction in Lean), it lands as a separate PR and
  `lake build EtingofRepresentationTheory.Chapter5.SpechtModuleBasis`
  succeeds with no new sorries.
* No changes to the off-limits files (`.claude/CLAUDE.md`, `PLAN.md`).
