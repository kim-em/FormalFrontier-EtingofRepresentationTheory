## Current state

PR #2495 (merged 2026-04-24T04:04:45Z, commit `da5c8df`) closed the
last Wall 2 sorry — `dTildeRep_mapLinear_transport` at
`EtingofRepresentationTheory/Chapter6/InfiniteTypeConstructions.lean:2958`
— via a `dTildeCast` refactor. This was the **framework closure of Wall 2**
(D̃_n indecomposability chain, four hard arrow cases), so it deserves an
independent audit before downstream work leans on it.

The merged change introduced (or substantially reshaped) the cast
infrastructure around `dTildeRepMap` and `dTildeTransportEquiv` to make
the dimension equation commute with `LinearEquiv.funCongrLeft`
reindexing. This is the kind of change where subtle `▸`-cast errors can
sit undetected and surface later as bogus `IsIndecomposable` proofs.

## Deliverables

Audit PR #2495's merged code in
`EtingofRepresentationTheory/Chapter6/InfiniteTypeConstructions.lean`.
The review must answer, in writing, each of:

1. **Soundness**: does `dTildeCast` (or whatever refactor landed) actually
   commute `▸`-casts on `dTildeRepMap`'s dimension equation with
   `LinearEquiv.funCongrLeft` reindexing? Confirm on at least two of the
   four hard arrow cases (`pathMid → pathMid`, `pathMid → branchRight`,
   `rightLeaf1 → branchRight`, `rightLeaf2 → branchRight`) by tracing
   the definitional unfolding.
2. **Consistency with Stage C main math**: `dTildeRep'_isIndecomposable`
   (PR #2460) relied on `dTildeRep'` being structurally nice. Does the
   transport lemma now let `dTildeRep_isIndecomposable` depend on
   `dTildeRep'_isIndecomposable` without introducing circularity or
   transport-only assumptions?
3. **No hidden sorry**: confirm that all four arrow cases are
   discharged by actual proof terms, not by `by sorry` in a helper
   that the top-level lemma calls through.
4. **Book fidelity**: the whole point of `DTildeVertex k` (Wall 2 Option a)
   was to keep the on-paper D̃_n argument available in Lean. Does the
   transport refactor preserve this — i.e., does a mathematician reading
   only the statements of `dTildeRep_isIndecomposable` and
   `dTildeRep'_isIndecomposable` get the expected D̃_n infinite-type
   result without needing to internalise the cast machinery?

**Output**: A review progress file
`progress/<timestamp>_wall2-stage-c-review.md` with
**Findings** (Pass / Issues / Recommendations) addressing each of the
four questions above. Findings that require action must be filed as
separate follow-up issues (with the `review-finding` style used in
issue #2489 — a dedicated feature issue with a `review-finding`
prefix in the title if the project convention supports it, else just
a plain feature issue that references this review).

## Context

- Merged PR: #2495 (commit `da5c8df`).
- Parent issue: #2479 (claimed by session `bbc039f3-28e1-4f57-a7d3-7ded7ee3194b`,
  closed by the merge).
- Wall 2 design trail: `progress/design-walls-wave55.md` §"Wall 2".
- Stage progression: #2448 (Stage A vertex type) → #2449 (Stage B
  migration) → #2460 (Stage C main math) → #2475 (Stage C transport
  skeleton, 4/8 cases) → #2495 (this, Stage C residual).
- Precedent: #2486 (review of bimodule foundation) landed via #2490
  and correctly identified #2489 (B-linearity drift). Use the same
  workflow: audit, write findings, file follow-up issues only for real
  concerns.

## Verification

- `lake build EtingofRepresentationTheory.Chapter6.InfiniteTypeConstructions`
  succeeds at HEAD (should be a no-op; the merge already built).
- The four soundness questions above are each answered in the review
  progress file with either "Pass — (reasoning)" or "Issue: (link to
  follow-up)".
- If any follow-up issues are filed, this review issue's closing PR
  should link them by number.

## Scope

- 1 worker-session of careful reading. No new proofs expected.
- Pure review — do not modify any Lean source during the review
  itself; fixes go into follow-up feature issues.
