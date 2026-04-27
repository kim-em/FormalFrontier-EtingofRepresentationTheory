## Current state

`Chapter5/PolynomialRepEmbedding.lean` (761 lines) has had two recent
plumbing-layer additions land **without a dedicated review issue**:

- **PR #2528** (`9ecac42`, Schur-Weyl #2b partial, closing part of #2478):
  the polynomial-rep injection part. Introduces
  - `polyTensorRow` (line 125), `polyTensorRow_eq_zero_iff` (line 136)
  - `polyTensorBundle` (line 163), `polyTensorBundle_apply` (line 174)
  - `theorem polynomialRep_embeds_in_tensorPower_inj` (line 201)

- **PR #2551** (`67db8c5`, #2545 follow-up to #2527): the `hP_mul`
  derivation that lets downstream consumers cite a primed wrapper. Introduces
  - `MvPolynomial.eq_of_eval_eq_on_gl` (line 598) — top-level Mathlib-shaped
    polynomial-identity-from-GL-evaluation lemma over an infinite field
  - `Etingof.PolynomialRepEmbedding.eval_polyRightTransl` (line 652)
  - `Etingof.PolynomialRepEmbedding.hP_mul_of_hP` (line 680)
  - `theorem polynomialRep_embeds_in_tensorPower'` (line 736) — primed
    wrapper that supplies `hP_mul` internally

The earlier equivariance layer (PRs #2538 + #2539) was audited in review
#2547 (PASS, merged as PR #2549). Issue #2547 explicitly **did not cover**
the injection part (#2528) or the `hP_mul` derivation (#2551), so they are
the un-audited deliverables on this file.

These additions sit on the critical path to Schur-Weyl #5 (#2482) and #6
(#2483): the capstone `iso_of_formalCharacter_eq_schurPoly` will cite
`polynomialRep_embeds_in_tensorPower'` directly. Audit them now, before
the chain assembles, so any structural finding can be applied while the
chain is still blocked on #2540 / #2493.

## Deliverables

Audit the additions from PRs #2528 + #2551 and post **one consolidated
review comment** answering all of the following.

### Q1 — `polynomialRep_embeds_in_tensorPower_inj` (PR #2528)

The injection theorem packages `polyTensorBundle` (a `Fin d × (Fin n → Fin N)`-indexed
bundle of evaluations) into a linear injection `M →ₗ[k] (Fin d × ...) → ...`.

- Is the construction `polyTensorRow` / `polyTensorBundle` correct? In
  particular, does `polyTensorBundle x p = splitDualBasis (polyTensorRow b P hhom p.1 x) p.2`
  give the intended bundle (one polynomial per row, evaluated at every
  pure-tensor basis index)?
- Does the injectivity argument really reduce to
  `polyTensorRow_eq_zero_iff` (which bottoms out at
  `matrixCoeffPoly_apply` injectivity)?
- Is the `[CharZero k]` hypothesis necessary? If not, drop it and file a
  small follow-up to remove it from `polyTensorRow` / `polyTensorBundle`
  too (review-finding pattern).

### Q2 — `MvPolynomial.eq_of_eval_eq_on_gl` (PR #2551)

This is a **Mathlib-shaped, top-level** lemma (in `namespace MvPolynomial`,
not the `Etingof` namespace). It concludes `p = q` from agreement of
evaluations on `GeneralLinearGroup`, over an infinite field.

- Is the statement and proof Mathlib-PR-ready? Specifically:
  - Hypothesis `[Field k] [Infinite k]` is correct (Zariski density needs
    infiniteness, not just `CharZero`).
  - Proof goes through `MvPolynomial.funext` on `(p - q) * det(X)`,
    using `Matrix.det_mvPolynomialX_ne_zero` and integral-domain cancellation.
- Does `Matrix.GeneralLinearGroup.mkOfDetNeZero` give the right Mathlib API
  here, or is there a more direct route (e.g. an existing
  `Matrix.det_ne_zero_iff_isUnit` + `Units.mk` path)?
- Is there an existing Mathlib lemma this duplicates? (Search for
  `eq_of_eval_eq` / `MvPolynomial.eval` density results in
  `Mathlib.Algebra.MvPolynomial.*` and `Mathlib.LinearAlgebra.Matrix.MvPolynomial`.)
- If the lemma is genuinely new and Mathlib-PR-ready, file a follow-up
  issue noting it as a candidate for upstream contribution; do **not** PR
  it from this audit.

### Q3 — `hP_mul_of_hP` and `polynomialRep_embeds_in_tensorPower'` (PR #2551)

The derivation routes `ρ.map_mul` through `eq_of_eval_eq_on_gl` to extract
the polynomial-level multiplicativity identity `hP_mul`.

- Is the locking-down of `[CharZero k]` on `eval_polyRightTransl` and
  `hP_mul_of_hP` consistent with how the file uses `polyRightTransl`
  elsewhere? `eq_of_eval_eq_on_gl` itself only needs `[Infinite k]` — does
  the chain force `[CharZero k]`, or could it be relaxed?
- The primed wrapper `polynomialRep_embeds_in_tensorPower'` exists so
  downstream consumers (Schur-Weyl #5 / #2482) supply only `(hhom, hP)`.
  Verify the unprimed theorem's `hP_mul` hypothesis is the **only** thing
  the wrapper hides — i.e. callers of the primed form gain nothing else
  for free.
- Confirm the wrapper does **not** silently change the conclusion (`m`,
  `φ`, injectivity, equivariance) relative to the unprimed form. Does
  `exact polynomialRep_embeds_in_tensorPower ...` cleanly forward all
  conclusions?

## Context

- Files under audit:
  - `EtingofRepresentationTheory/Chapter5/PolynomialRepEmbedding.lean`
- Commits:
  - `9ecac42` (PR #2528, Schur-Weyl #2b injection part)
  - `67db8c5` (PR #2551, `hP_mul` derivation + primed wrapper)
- Already-reviewed prior layer: PR #2547 covered PRs #2538 (`14e327c`) +
  #2539 (`c6339a6`); reviewers can take that audit as a baseline.
- Downstream consumers waiting on this:
  - #2482 (Schur-Weyl #5 — capstone, blocked on #2493)
  - #2483 (Schur-Weyl #6 — final iso, blocked on #2482)
- Critical-path note: this audit is independent of the in-flight Wall 3
  PRs (#2541 / #2550) and the claimed bimodule decomposition (#2540), so
  it can run in parallel.

## Verification

- `lake build EtingofRepresentationTheory.Chapter5.PolynomialRepEmbedding`
  succeeds (no behavior changes from this audit).
- One review comment posted on the issue answering Q1 / Q2 / Q3.
- For each `PASS` answer: explicit confirmation.
- For each `FAIL` or follow-up finding: a separate `review-finding` issue
  filed (small, one-shot, not blocking this audit).
- If `eq_of_eval_eq_on_gl` is genuinely Mathlib-PR-ready, file a tracking
  issue tagged `mathlib-upstream` (do **not** open the upstream PR from
  this audit).
- Audit is `PASS` if all three deliverables stand up to scrutiny modulo
  any review-findings filed.
