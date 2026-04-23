## Current state

A counter-example posted on #2417 shows that `etilde6v2Rep_isIndecomposable`
(Ẽ₆ with mixed orientation, lines 2322+ of
`EtingofRepresentationTheory/Chapter6/InfiniteTypeConstructions.lean`) is
**false** for `m = 1`: an explicit non-trivial invariant complement `(W₁, W₂)`
with both components non-trivial at every vertex verifies all 6 edge
invariances. Details on #2417 and in
`progress/2026-04-23T07-56-48Z_d25b71e0.md`.

Consequently, all three Ẽ₆ sub-sorries (#2417 `leaf24_containment`,
#2418 `hN₁`/`hN₂`, #2419 `hbot0`) are unprovable as stated and have been
closed. The 3.1 rule ("Definitions Must Be Constructed") is violated: the
representation object used here does not prove what it claims to prove.

The book uses `etilde6v2Rep` (or an analog) to prove Ẽ₆ is of infinite
representation type, which is one of the key Chapter 6 results that in
turn feeds `Theorem2_1_2`'s forward bridge (#2401). This is the current
blocker for finishing Stage 3.

The analogous constructions for Ẽ₇ (`etilde7Rep`, #2394/#2427/#2428) and
T(1,2,5) (`t125Rep`, #2400) were designed on the same structural template
(mixed orientation, nilpotent coupling on arm 1, `(p,q) ↦ (p+q, p, q, Nq)`
or similar). They may share the same soundness issue. Until this is
resolved, every Ẽ₇/T(1,2,5) sub-sorry is blocked.

## Deliverables

1. **Diagnose Ẽ₇ and T(1,2,5)**: Attempt to construct explicit
   decompositions of `etilde7Rep 1` and `t125Rep 1` mirroring the Ẽ₆
   counter-example. Either (a) find counter-examples, confirming the
   frameworks are unsound; or (b) identify why they resist decomposition
   (structural asymmetry, longer arm, etc.) despite Ẽ₆ failing.

2. **Re-read the book** (Chapter 6 of Etingof, *Representation Theory*).
   The infinite-type proof for E₆/E₇/E₈ (and for T(p,q,r) when
   1/p + 1/q + 1/r ≤ 1) is given there. Record the book's precise
   orientation / representation and compare to what the Lean code
   implements. If the Lean construction diverges from the book, that is
   the likely root cause of the unsoundness.

3. **Propose a corrected framework**: One of:
   - A new representation definition (or new map definitions) that is
     genuinely indecomposable. State it precisely and give a sketch of
     why it is indecomposable. (This is a *definition-level* change.)
   - Or: a proof strategy that works for the existing definition, with a
     clear explanation of why the counter-example on #2417 fails for
     Ẽ₇/T(1,2,5) even though it succeeds for Ẽ₆.

4. **Output a design document** at
   `progress/indecomposability-framework-investigation.md` (or similar)
   summarising: (a) what was verified (counter-examples, book analysis),
   (b) the recommended corrected framework, (c) a concrete next-issue
   plan that a subsequent planner can use to create Stage-3 feature
   issues for filling the new sub-sorries. This document does not need
   to contain Lean proofs.

5. **Optional (if time permits)**: prototype the corrected definition
   in a separate file or commented block, with only the Lean signature
   (no proofs).

## Context

- **Counter-example for Ẽ₆**: on #2417 (full edge-by-edge verification)
  and `progress/2026-04-23T07-56-48Z_d25b71e0.md`.
- **Framework file**:
  `EtingofRepresentationTheory/Chapter6/InfiniteTypeConstructions.lean`
  (currently 3000+ lines).
- **Related analyses**:
  - #2427 comment — Ẽ₇ `hN₁/hN₂` dead-end analysis (session e902034b).
  - #2428 comment — Ẽ₇ `hbot0` dimension-counting gap (session 8ce17ca2).
  - #2404 — earlier counter-example attempt for Ẽ₇ (m=1, claimed
    decomposable; since revisited).
  - `progress/meditate-wave49.md` — earlier strategy review.
- **Book chapter**: Etingof *Representation Theory*, Chapter 6 (see
  `blobs/Chapter6/` for transcribed content).
- **Downstream dependencies**: #2401 (Theorem2_1_2 forward bridge),
  plus Corollary 6.8.3 / 6.8.4 (Ch6 closing results) indirectly.

This is **critical-path**: all remaining Chapter 6 indecomposability
work (and the Ch2 theorem that depends on it) is blocked until the
framework question is resolved. It is also the largest conceptual risk
in the project — if the book's proof does not work in Lean at the
current abstraction level, that is a major finding.

## Verification

- A clear design document in `progress/` explaining what is known and
  recommended.
- Either (a) explicit counter-examples refuting the current Ẽ₇/T(1,2,5)
  constructions, or (b) a justified argument for why they differ from
  the refuted Ẽ₆ case.
- Concrete recommendation: either a definition-level fix (with
  signature) or a proof strategy that specifically explains the
  mechanism blocking the Ẽ₆ counter-example pattern.

This is expected to require **deep mathematical engagement with the
book** — not tactical Lean work. A meditate session is the right forum.
