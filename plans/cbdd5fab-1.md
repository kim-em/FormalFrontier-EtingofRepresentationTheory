## Current state

PR #2646 (merged 2026-04-27, closes issue #2611) introduced
**`SchurWeylGLTransfer.lean` from scratch** — a 530-line file giving
the Zariski-density / Vandermonde-inversion machinery that transfers
B-side simplicity to GL_N. The file has subsequently been built upon
by PR #2654 (MonoidAlgebra simplicity helper, audited via #2672/#2679)
and PR #2670 (`Theorem5_18_4_GL_rep_decomposition_simple` wrapper, also
audited via #2672/#2679), but the **foundational PR #2646 itself has
never been audited**. The audit chain went directly from #2647 (B-side
simplicity at the bimodule level, PR #2634) to #2671 / #2672 / #2673
(downstream Schur-Weyl GL_N transfer wrappers), skipping the
`SchurWeylGLTransfer.lean` foundation.

## Deliverables

Run a 10-question audit of PR #2646 (`SchurWeylGLTransfer.lean`,
commit `8da93e7`) and post a `progress/reviews/<date>-schur-weyl-Li-C-4b-foundation.md`
note recording PASS/FAIL for each question with file:line citations.
Then close this issue.

The audit must specifically check the new declarations:

1. **`submodule_coeffs_mem_of_eval_mem`** — Vandermonde inversion:
   if `p : ℕ → α` evaluated at `n+1` distinct scalars `c_i` lies in a
   submodule `M`, then every coefficient `p i` lies in `M`.
2. **`mixedTensorPow` / `mixedTensorPow_univ`** — Pure-tensor expansion
   support for `(f - c•1)^⊗n`.
3. **`tensorPowCoeff` + `tensorPowCoeff_zero`** — The "i-th coefficient"
   of the polynomial `(f - c•1)^⊗n` viewed as a polynomial in `c`,
   with the boundary case `tensorPowCoeff n f 0 = f^⊗n`.
4. **`tensorPow_sub_smul_eq_sum_coeff`** — Multilinear expansion
   `(f - c•1)^⊗n = ∑_i c^i • A_i(f)`.
5. **`exists_finset_isUnit_sub_smul_one`** — Cofinite invertibility:
   for `f : End k V` over an infinite field with `Module.Finite k V`,
   `f - c•1` is a unit for all but finitely many `c`. (Uses charpoly
   has finitely many roots.)
6. **`tensorPow_mem_span_unitsTensorPow`** — The span lemma:
   `f^⊗n ∈ k-span{g^⊗n : g ∈ Units(End k V)}`.
7. **`adjoin_unitsTensorPow_eq_diagonalActionImage`** — Algebra
   equality `Algebra.adjoin k {g^⊗n : g ∈ Units(End k V)} =
   diagonalActionImage`.
8. **`submodule_smul_mem_diagonalActionImage_of_unit_smul_mem`** —
   The submodule transfer step.
9. **`submodule_eq_bot_or_top_of_unit_smul_mem`** — The simplicity
   transfer corollary used by downstream wrappers.

## Verification questions (answer each PASS / FAIL with citation)

1. **No sorries.** `git grep -c "sorry" EtingofRepresentationTheory/Chapter5/SchurWeylGLTransfer.lean`
   returns 0 (or only inside doc strings).
2. **Build is green.** `lake build EtingofRepresentationTheory.Chapter5.SchurWeylGLTransfer`
   succeeds against current `main`.
3. **Each declaration's signature matches its docstring.** No "claims
   X but proves Y" mismatches. Cite file:line for any drift.
4. **Hypotheses are necessary.** No unused `[CharZero k]`, `[IsAlgClosed k]`,
   or `[Field k]` instances. (Per the project hygiene push that produced
   PRs #2576 / #2577 / #2585 / #2662, audit each declaration for stray
   instance hypotheses.)
5. **Vandermonde inversion is correctly stated.** The hypothesis on
   `submodule_coeffs_mem_of_eval_mem` requires `n+1` *distinct* scalars,
   not `n` of them, and the conclusion covers `i ∈ Finset.range (n+1)`.
6. **`exists_finset_isUnit_sub_smul_one` actually witnesses cofinite
   invertibility.** The lemma needs `[Infinite k]` (or some equivalent)
   so that the cofinite set has elements; verify the hypothesis is in
   place and used.
7. **`adjoin_unitsTensorPow_eq_diagonalActionImage` proves equality,
   not just one inclusion.** Both `≤` and `≥` directions are present.
8. **Heartbeat bumps are documented + minimal.** The commit message
   notes 800k maxHeartbeats / 400k synthInstance. Verify these are set
   on the specific declaration that needs them and not blanket-applied.
9. **Universe levels are unambiguous.** No spurious `universe`
   declarations or unnecessary `.{u}` annotations leaking out.
10. **Downstream usage in PR #2654 / PR #2670 actually depends on the
    public API.** Spot-check that `SchurWeylGLTransfer` exports the
    declarations consumed by `isSimpleModule_monoidAlgebra_GL_of_centralizer_simple`
    (`SchurWeylGLTransfer.lean:553`) and
    `Theorem5_18_4_GL_rep_decomposition_simple` (the #2670 wrapper).
    Any private-but-needed declarations should be flagged.

## Output

Create `progress/reviews/<YYYY-MM-DD>-schur-weyl-Li-C-4b-foundation.md`
with a per-question PASS/FAIL table plus a one-paragraph summary.
PASS overall = all 10 PASS or only doc-only / hygiene-style nits.
FAIL = any soundness, scope, or build problem; file follow-up issues
for each FAIL (do not fix in this PR).

## Context

- File audited: `EtingofRepresentationTheory/Chapter5/SchurWeylGLTransfer.lean`
- Commit: `8da93e7` (PR #2646, merged 2026-04-27)
- Closes: issue #2611
- Built upon by: PR #2654 (#2672 audit), PR #2670 (#2672 audit)
- Audit chain extended: ✅ #2549 → … → #2647 → #2671 → #2672 → #2673 → **this**

## Sizing

Small. Read 530 lines, run 10 checks, write a one-page note. ~50–100
lines of audit prose, no Lean changes (any FAILs become follow-up issues).
