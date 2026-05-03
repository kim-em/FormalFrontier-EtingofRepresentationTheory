## Current state

#2652 (`garnir_twisted_in_lower_span_aux` Algorithm A loop + col-std
existence) was skipped by a worker who identified a mathematical gap
in the issue's proof outline.

Quoting the worker's [skip comment on #2652](https://github.com/FormalFrontier/Etingof-RepresentationTheory-draft1/issues/2652):

> The col-std existence sub-lemma is harder than its ~30-50 line
> estimate suggests. It requires either:
>
> - (a) restricting to specific row-inversion choices (e.g., the
>   "leftmost" row inversion satisfying additional column-flatness
>   conditions), or
> - (b) accepting that not every `α` with `[α] = [σ]` admits a col-std
>   rep at smaller rowInv, and routing those cases through the IH
>   dispatch (b) of the Algorithm A loop.
>
> Either way, the IH-case dispatch becomes the dominant work, not a
> fallback. The companion λ=(2,2) counter-example `[{2,3}|{0,1}]`
> (which has *no* col-std rep) shows the IH case is essential for
> `[α] ≺ [σ]` too, not just `[α] = [σ]`.

The original Algorithm A outline assumed a uniform col-std existence
construction; the counter-example shows this fails. The next step is
not to write code — it is to redesign Algorithm A.

## Deliverables

Produce a meditate note at
`progress/algorithm-A-redesign.md` containing:

1. **Investigation summary**: Re-read the proof of
   `garnir_twisted_in_lower_span` in the book (Chapter 5; see the blob
   files under `blobs/Chapter5/`) and the existing partial machinery
   in `EtingofRepresentationTheory/Chapter5/SpechtModuleBasis.lean`.
   Confirm whether a col-std existence construction is feasible at all
   (option (a) above) — and if so, identify the precise
   "column-flatness" / "leftmost row inversion" condition under which
   it works. If not, document the counter-examples that rule it out.

2. **Redesigned Algorithm A**: Spell out the strong-induction step,
   handling both `[α] = [σ]` and `[α] ≺ [σ]` cases via the IH
   dispatch, with explicit Lean-level pseudocode for each branch.
   The dispatch must close `garnir_twisted_in_lower_span_aux`'s
   conclusion under the existing IH hypothesis at strictly smaller
   `(srRank, rowInvCount')`.

3. **Re-decomposition**: Based on the redesign, list the follow-up
   implementation issues that should be created. Each should be
   single-session-sized (≤200 lines, ≤2 files). Suggested shape:
   - sub-A (if applicable): col-std existence sub-lemma under the
     identified restricted condition, ~50-80 lines.
   - sub-B: Algorithm A main loop on `supp(TP)` with the IH-dispatch,
     ~150-200 lines.
   - sub-C (optional): any auxiliary `tabloidStrictDominates` / row-
     inversion bookkeeping helpers extracted from the redesigned proof.

   For each follow-up: title, one-paragraph scope, and the
   dependencies among them. The next planner cycle will create them
   as `feature` issues.

4. **Counter-example record**: Document the λ=(2,2) counter-example
   `[{2,3}|{0,1}]` that the worker identified, and any others
   discovered during the investigation. These belong in
   `progress/algorithm-A-redesign.md` so future workers don't try the
   same failed construction.

## Context

* File under investigation:
  `EtingofRepresentationTheory/Chapter5/SpechtModuleBasis.lean`,
  specifically the `garnir_twisted_in_lower_span` sorry around line
  1600 and the surrounding `garnir_straightening_step` /
  `polytabloidTab_column_standard_in_span` machinery.
* Book reference: `blobs/Chapter5/` — read the relevant blob for the
  Garnir straightening proof.
* Existing API:
  - `garnirColReindex` at `SpechtModuleBasis.lean:925-948` (column
    reindexing for the `[α] ≺ [σ]` direct construction case).
  - `tabloidStrictDominates`, `rowInvCount'`, `tabloidDominates`,
    `polytabloidTab` (all in `SpechtModuleBasis.lean`).
  - `polytabloidTab_in_lower_span_of_dominates` (just merged via
    PR #2653 from #2651) — bridge lemma usable in the IH dispatch.
  - `tabloidSupport_straightening` (bound on `supp(TP)`).
* Predecessor analysis: the skip comment on #2652 contains the full
  step-by-step reasoning for why the original outline fails; read it
  end-to-end before starting.
* Sibling issues consuming this work: #2649 (sub-B packed mutual
  induction restructure) currently depends on the descendant of the
  redesigned algorithm; #2520 and #2500 depend on #2649.

## Verification

* `progress/algorithm-A-redesign.md` exists, with sections for each
  of the four deliverables above.
* The redesigned algorithm closes the original goal (no `sorry`
  expected as part of this meditate task — that's for the follow-up
  implementation issues).
* The follow-up issue list is concrete enough that the next planner
  can create the issues directly from the meditate note.
* No code changes (this is a planning task; document-only commit).
