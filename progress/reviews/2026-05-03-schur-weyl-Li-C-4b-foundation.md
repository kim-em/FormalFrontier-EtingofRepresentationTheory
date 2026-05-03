# Schur-Weyl L_i C-4b foundation audit — PR #2646 (`SchurWeylGLTransfer.lean`)

**Issue**: #2688 (review).
**Session**: `09ff9b7b` (2026-05-03).
**Scope**: audit the foundational `EtingofRepresentationTheory/Chapter5/SchurWeylGLTransfer.lean`
introduced by PR #2646 (commit `8da93e7`, +530 lines, closed #2611) and
extended by PR #2654 (`isSimpleModule_monoidAlgebra_GL_of_centralizer_simple`,
commit `dcecd08`) and PR #2670 (`Theorem5_18_4_GL_rep_decomposition_simple`,
commit `2624bcd`). The file now totals 802 lines.

The audit chain `✅ #2549 → … → #2647 → #2671 → #2672 → #2673` had skipped
the foundation file itself (PRs #2654 and #2670 — auditors of the wrappers
in #2672/#2679 — implicitly relied on the unaudited base). This note
closes that gap.

---

## Per-question PASS/FAIL

| # | Question | Verdict |
|---|---|---|
| 1 | No sorries | **PASS** |
| 2 | Build is green | **PASS** |
| 3 | Signatures match docstrings | **PASS** |
| 4 | Hypotheses necessary | **PASS with hygiene nits** |
| 5 | Vandermonde inversion stated correctly | **PASS** |
| 6 | `exists_finset_isUnit_sub_smul_one` cofiniteness | **PASS** |
| 7 | `adjoin_unitsTensorPow_eq_diagonalActionImage` is equality | **PASS** |
| 8 | Heartbeat bumps documented + minimal | **PASS with nits** |
| 9 | Universe levels unambiguous | **PASS** |
| 10 | Downstream usage in #2654 / #2670 | **PASS** |

**Overall: PASS** — all 10 checks pass; a handful of doc-only / hygiene-style
nits documented below for an optional follow-up.

---

## Q1 — No sorries: **PASS**

`grep -c "sorry" EtingofRepresentationTheory/Chapter5/SchurWeylGLTransfer.lean`
returns `0`. No `sorry` markers anywhere in the file (including doc strings).

## Q2 — Build is green: **PASS**

`lake build EtingofRepresentationTheory.Chapter5.SchurWeylGLTransfer` against
`a25eb01` (current main): completes successfully, "Build completed
successfully (8031 jobs)". No errors. Lint warnings only (see Q4/Q8 below).

## Q3 — Signatures match docstrings: **PASS**

Each declaration's signature is consistent with its stated purpose:

- `submodule_coeffs_mem_of_eval_mem` (`SchurWeylGLTransfer.lean:41-83`):
  Vandermonde inversion. Hypothesis `Function.Injective c` on `c : Fin (n+1) → k`
  + `∀ j, ∑ i, c j ^ i • m i ∈ W` ⇒ `∀ i, m i ∈ W`. Matches doc.
- `mixedTensorPow` / `mixedTensorPow_univ` (`:97-109`): `f` on slots in `s`,
  `1` outside, with `_univ` collapsing to `f^⊗n`. Matches doc.
- `tensorPowCoeff` / `tensorPowCoeff_zero` (`:115-133`): coefficient of `c^i`
  in `(f - c•1)^⊗n`, with the boundary case `i = 0 ↦ f^⊗n`. Matches doc.
- `tensorPow_sub_smul_eq_sum_coeff` (`:188-271`): the multilinear expansion.
  Matches doc.
- `exists_finset_isUnit_sub_smul_one` (`:281-297`): cofinite invertibility.
  Matches doc.
- `tensorPow_mem_span_unitsTensorPow` (`:308-359`): the span lemma. Matches.
- `adjoin_unitsTensorPow_eq_diagonalActionImage` (`:365-380`): the algebra
  equality. Matches.
- `submodule_smul_mem_diagonalActionImage_of_unit_smul_mem` (`:401-490`):
  the submodule transfer. Matches.
- `submodule_eq_bot_or_top_of_unit_smul_mem` (`:495-528`): the simplicity
  transfer corollary. Matches.
- `isSimpleModule_monoidAlgebra_GL_of_centralizer_simple` (`:553-629`):
  MonoidAlgebra-side simplicity transfer. Matches.
- `Theorem5_18_4_GL_rep_decomposition_simple` (`:659-800`): the GL_N
  decomposition wrapper with the simplicity clause. Matches.

No "claims X but proves Y" drift detected.

## Q4 — Hypotheses necessary: **PASS with hygiene nits**

Spot-check of each instance bracket:

- `submodule_coeffs_mem_of_eval_mem`: `[Field k]` is necessary for
  `(V.det)⁻¹` (line 82) and `inv_mul_cancel₀` (line 83). ✓
- `mixedTensorPow` family: only the variable-block `[Field k]`,
  `[AddCommGroup V]`, `[Module k V]`. All needed. ✓
- `exists_finset_isUnit_sub_smul_one` (line 281): `[Field k]` + `[Module.Finite k V]`.
  Internally derives `Module.Free` from `Field` (via `of_divisionRing`); both
  necessary. ✓
- `tensorPow_mem_span_unitsTensorPow` (line 308): `[Module.Finite k V]`,
  `[Infinite k]`. The `[Infinite k]` is genuinely needed at line 321
  (`hSc_infinite : (↑S : Set k)ᶜ.Infinite`). ✓
- `adjoin_unitsTensorPow_eq_diagonalActionImage` (line 365): same. ✓
- `submodule_smul_mem_diagonalActionImage_of_unit_smul_mem` (line 401):
  `[Module.Finite k V]`, `[Infinite k]` — both needed via the inner
  `tensorPow_mem_span_unitsTensorPow` call (line 432). ✓
- `submodule_eq_bot_or_top_of_unit_smul_mem` (line 495):
  `[Module.Finite k V]`, `[Infinite k]`,
  `[IsSimpleModule (diagonalActionImage k V n) M]` — all needed. ✓
- `isSimpleModule_monoidAlgebra_GL_of_centralizer_simple` (line 553):
  - `[Field k]` + `[Module.Finite k M]` + `[Module (diagonalActionImage…) M]`
    + `[IsScalarTower …]` + `[IsSimpleModule (diagonalActionImage…) M]`
    + `[IsAlgClosed k]`.
  - **Nit 1**: `[IsAlgClosed k]` is stronger than needed. Only `[Infinite k]`
    is invoked (via the helper `submodule_eq_bot_or_top_of_unit_smul_mem`).
    `[IsAlgClosed k]` does provide `[Infinite k]` by instance, so this
    compiles, but `[Infinite k]` would be tighter. *Optional tightening.*
  - **Nit 2**: `[Module.Finite k M]` does not appear to be used in the
    proof body — neither the helper transfer lemma nor `isSimpleModule_iff`
    nor `Submodule.nontrivial_iff` need it. The proof uses only
    `Module.Finite k (Fin N → k) := inferInstance` (line 569), which is
    independent of `[Module.Finite k M]`. *Optional removal.*
- `Theorem5_18_4_GL_rep_decomposition_simple` (line 659): `[Field k]` +
  `[IsAlgClosed k]` + `[CharZero k]`. `[IsAlgClosed k]` and `[CharZero k]`
  are both required by the call to `Theorem5_18_4_bimodule_decomposition_explicit`
  (line 687) — `IsAlgClosed` for splitness over the algebraically closed
  field, `CharZero` for `symGroupImage_isSemisimpleRing` (Maschke). ✓

The two nits are pure hygiene — they do not affect soundness or callers.
None warrant a follow-up issue on their own; they could be cleaned up in
a future refactor session that touches this file.

## Q5 — Vandermonde inversion correctness: **PASS**

`submodule_coeffs_mem_of_eval_mem` (`:41-47`):

```lean
{n : ℕ} (m : Fin (n + 1) → M)
(c : Fin (n + 1) → k) (hc : Function.Injective c)
(h : ∀ j : Fin (n + 1), ∑ i : Fin (n + 1), c j ^ (i : ℕ) • m i ∈ W) :
∀ i : Fin (n + 1), m i ∈ W
```

- The evaluation points `c : Fin (n + 1) → k` give exactly `n + 1` values,
  with `Function.Injective c` enforcing distinctness. The Vandermonde
  determinant for `n + 1` distinct nodes is non-zero
  (`Matrix.det_vandermonde_ne_zero_iff`, line 51).
- The conclusion `∀ i : Fin (n + 1), m i ∈ W` covers all `n + 1` coefficients.
- The statement does **not** require the coefficient sum to start at `i = 0`;
  it ranges over `Fin (n + 1)`, which is `{0, 1, …, n}`.

Hypothesis and conclusion are correctly specified.

## Q6 — `exists_finset_isUnit_sub_smul_one` cofiniteness: **PASS**

The lemma itself does **not** require `[Infinite k]` — only
`[Module.Finite k V]`. This is correct: the cardinality bound on the
finite "bad" set comes from the charpoly having at most `dim V` roots,
which is a statement about *the size of the bad set*, not about `k`'s
overall cardinality. `[Infinite k]` is needed only by downstream callers
(`tensorPow_mem_span_unitsTensorPow`, line 308) when they need the
*complement* to be non-empty.

The hypothesis is correctly placed (downstream, not here).

## Q7 — `adjoin_unitsTensorPow_eq_diagonalActionImage` is equality: **PASS**

Lines 365-380: `apply le_antisymm`, then both `≤` and `≥` directions are
discharged:
- `≤` (line 371-374): every `g^⊗n` for `g : (Module.End k V)ˣ` is `f^⊗n`
  for `f := g.val`, so it lies in `Algebra.adjoin k {f^⊗n : f ∈ End k V}`
  by `Algebra.subset_adjoin`.
- `≥` (line 375-380): every `f^⊗n` is in the *span* of `{g^⊗n : g ∈ Units}`
  by `tensorPow_mem_span_unitsTensorPow`, hence in the adjoin via
  `Algebra.span_le_adjoin`.

Both inclusions are present; this is an honest `=`.

## Q8 — Heartbeat bumps: **PASS with style nits**

Three heartbeat-bumped declarations:

| Line | Declaration | mH / synthInstance.mH | Comment present? |
|------|-------------|----------------------|------------------|
| 396  | `submodule_smul_mem_diagonalActionImage_of_unit_smul_mem` | 800k / 400k | Yes (`:394-395`, block-comment) |
| 547  | `isSimpleModule_monoidAlgebra_GL_of_centralizer_simple`   | 800k / 400k | **Missing** (linter flags) |
| 635  | `Theorem5_18_4_GL_rep_decomposition_simple`               | 3.2M / 1.6M | Yes (`:631-634`, block-comment) |

The 800k / 400k pattern is the standard for nested
`Algebra.adjoin_induction` + `Submodule.span_induction` with subtype-
membership predicates and matches the other heartbeat-bumped declarations
in `Theorem5_18_1.lean` and `Theorem5_18_4.lean` (also flagged by the
linter for missing inline comments — this is a project-wide style
inconsistency, not a SchurWeylGLTransfer-specific issue).

The 3.2M / 1.6M on `Theorem5_18_4_GL_rep_decomposition_simple` is justified
by the 11-binder existential output and per-`i` transport through
`Subalgebra.equivOfEq`, matching the budgets used by
`_GL_rep_decomposition_explicit`.

Lint warnings:
- `:396`, `:547`, `:635`: "Please, add a comment explaining the need for
  modifying the maxHeartbeat limit, as in `set_option maxHeartbeats … in
  -- reason for change`". Linter wants the explanation on the same line
  or an immediate `-- comment` after the `in`, not a separate block-comment
  preceding the declaration. The block-comments at `:394-395` and `:631-634`
  do exist and explain the bump, but in a form the linter doesn't recognise.

The bumps are minimal-scope (`set_option … in` on a single declaration each,
not blanket-applied). No follow-up issue needed — this is a
project-wide-style nit shared with several other Chapter 5 files.

## Q9 — Universe levels: **PASS**

- `universe u v` declared at line 27.
- `(k : Type u)` and `{V : Type v}` at lines 29 and 94 — both used.
- `Theorem5_18_4_GL_rep_decomposition_simple` (line 659) instantiates
  `S : ι → Type u` and the `L i : FDRep k (GL_N (Fin N))` so that the final
  `DirectSum ι (fun i => S i ⊗[k] (L i : Type u))` typechecks at `Type u`.
  This matches the universe pattern used by
  `Theorem5_18_4_GL_rep_decomposition_explicit` (its companion in
  `Theorem5_18_4.lean`).
- No spurious `.{u}` annotations leak out.

Universe handling is consistent.

## Q10 — Downstream usage in PRs #2654 / #2670: **PASS**

Both downstream PRs *added their declarations to this same file* rather
than importing from elsewhere:

- **PR #2654** (`isSimpleModule_monoidAlgebra_GL_of_centralizer_simple`,
  `:553-629`) consumes the foundation declarations
  `submodule_eq_bot_or_top_of_unit_smul_mem` (`:495`),
  `submodule_smul_mem_diagonalActionImage_of_unit_smul_mem` (`:401`),
  and the `adjoin_unitsTensorPow_eq_diagonalActionImage` chain.
- **PR #2670** (`Theorem5_18_4_GL_rep_decomposition_simple`, `:659-800`)
  consumes `isSimpleModule_monoidAlgebra_GL_of_centralizer_simple`
  (`:787-790`).

A repo-wide grep (`SchurWeylGLTransfer`) finds zero importing files
outside the file itself; this is expected, since the wrappers it exports
are not yet consumed by downstream Chapter 5 work (the planned consumers
are documented in `plans/b850fd41-2.md`). All public API is exported
under `namespace Etingof` and is accessible to future consumers. The only
`private` declaration is `map_piecewise_neg_smul_eq` (`:137`) — a
purely internal scalar-extraction lemma not needed by callers.

Public API surface (exported, no `private`):
- `submodule_coeffs_mem_of_eval_mem`
- `mixedTensorPow`, `mixedTensorPow_univ`
- `tensorPowCoeff`, `tensorPowCoeff_zero`
- `tensorPow_sub_smul_eq_sum_coeff`
- `exists_finset_isUnit_sub_smul_one`
- `tensorPow_mem_span_unitsTensorPow`
- `adjoin_unitsTensorPow_eq_diagonalActionImage`
- `submodule_smul_mem_diagonalActionImage_of_unit_smul_mem`
- `submodule_eq_bot_or_top_of_unit_smul_mem`
- `isSimpleModule_monoidAlgebra_GL_of_centralizer_simple`
- `Theorem5_18_4_GL_rep_decomposition_simple`

No private-but-needed declarations flagged.

---

## Other observations (style-only, not affecting verdict)

For completeness, the lint warnings on this file (none of which are
soundness issues):

- `:153-154`: `simp [Finset.piecewise_eq_of_mem _ _ _ hj, hj]` —
  `Finset.piecewise_eq_of_mem` is unused; `simp [hj]` alone would suffice.
- `:179, 204, 243, 247, 252`: `show` used as a tactic (linter prefers
  `show` only for explicit goal-state annotation).
- `:251`: line exceeds 100 characters.
- `:522`: `simp at hx` is "flexible" — linter prefers `simp only [...]`.
- `:396, 547, 635`: maxHeartbeats inline-comment style (see Q8).

These are all standard Chapter 5 style nits matching the patterns flagged
elsewhere in `Theorem5_18_1.lean`, `Theorem5_18_4.lean`, and
`Lemma5_18_3.lean`. No follow-up issues filed.

---

## Summary

`SchurWeylGLTransfer.lean` is a sound, well-structured 802-line foundation
for the Schur-Weyl GL_N transfer chain. The Vandermonde-inversion machinery
(`submodule_coeffs_mem_of_eval_mem`), the polynomial expansion of
`(f - c•1)^⊗n`, the cofinite invertibility result, and the algebra equality
`Algebra.adjoin … = diagonalActionImage` are all correctly stated, well-
proved, and free of soundness concerns. The two simplicity-transfer lemmas
(`submodule_eq_bot_or_top_of_unit_smul_mem`,
`isSimpleModule_monoidAlgebra_GL_of_centralizer_simple`) and the
GL_N-decomposition wrapper (`Theorem5_18_4_GL_rep_decomposition_simple`)
build cleanly on top.

Two optional hygiene tightenings on
`isSimpleModule_monoidAlgebra_GL_of_centralizer_simple`'s instance brackets
(`[IsAlgClosed k]` → `[Infinite k]`; remove unused `[Module.Finite k M]`)
are noted but not severe enough to file follow-up issues — they should be
folded into the next refactor session that touches this file.

The audit chain `✅ #2549 → … → #2647 → #2671 → #2672 → #2673 → #2688` is
now complete for the Schur-Weyl L_i C-4b foundation.
