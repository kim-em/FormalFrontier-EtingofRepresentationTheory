# Audit: PR #2634 — Schur-Weyl L_i B-side simplicity

**Issue:** #2638
**PR audited:** https://github.com/FormalFrontier/Etingof-RepresentationTheory-draft1/pull/2634
**PR author session:** `bbbe77dd-0af9-48a3-ad1a-b2706cdfc512`
**Audit session:** `448b416a-52fb-4d0f-ad1d-2cf48afc064f`
**Date:** 2026-04-28
**Verdict:** **PASS-with-followups**

## Scope

Three artifacts:

1. New helper `Etingof.isSimpleModule_homA_centralizer`
   (`Theorem5_18_1.lean:540-616`) — Schur on the multiplicity space.
2. New `IsSimpleModule (centralizer A) (V i →ₗ[A] E)` clause on
   `Theorem5_18_1_bimodule_decomposition_explicit` (line 803-805)
   and corresponding propagation through
   `Theorem5_18_4_bimodule_decomposition_explicit` (line 472-475).
3. Heartbeat bump on `Theorem5_18_1_bimodule_decomposition_explicit`
   from 3.2M / 1.2M to 6.4M / 2.4M (line 772-773).

## Q1 — Helper proof correctness: **PASS**

The proof reduces simplicity to `isSimpleModule_iff_toSpanSingleton_surjective`
and discharges both clauses correctly:

* **Nontrivial witness**: `V.subtype : V →ₗ[A] E` is nonzero. Proven by
  contradiction: `V.subtype = 0 ⇒ every v : ↥V coerces to 0 ⇒ V is trivial`,
  contradicting `IsSimpleModule.nontrivial`.
* **Surjectivity** (cyclic = full): for nonzero `f : V →ₗ[A] E`,
  - Schur on the simple `V` gives `LinearMap.ker f = ⊥` (case-split on
    `eq_bot_or_eq_top` for the simple module `V`; top contradicts `f ≠ 0`),
    hence `f` is injective.
  - For target `g`, `IsSemisimpleModule.extension_property f hinj g`
    yields `h : E →ₗ[A] E` with `h ∘ₗ f = g`.
  - `h.restrictScalars k` lies in `centralizer(A)`: `A`-linearity of `h`
    applied to `(⟨a, ha⟩ : ↥A)` gives `h (a e) = a (h e)`, which is the
    centralizer condition.
  - The post-composition action `b ↦ b.val ∘ f` recovers `g` via
    `centralizerToEndA` definitional unfolding (the SMul instance is
    `smul b f := (centralizerToEndA k E A b).comp f`, line 433).

Mathematical content matches Etingof Theorem 5.18.1(iii)'s standard proof
of multiplicity-space simplicity. All imported lemmas
(`extension_property`, `mem_centralizer_iff`, `toSpanSingleton_apply`)
are used with correct signatures.

## Q2 — Theorem5_18_1 clause correctness: **PASS**

Clause is in the same `Subalgebra.centralizer k (A : Set ...)` namespace
convention as the rest of the file, inserted between the `Module.Finite`
and the equivalence — the natural position for additional "data block"
clauses. Proof body at lines 902-906 hoists `hL_simp` via direct
application of `isSimpleModule_homA_centralizer` (with `haveI :
IsSimpleModule (↥A) ↥(V' (φ.symm i))` pulled from `V'_simple`). No
sorry, no circularity. Order of existential refines (line 907-911)
matches signature.

## Q3 — Theorem5_18_4 propagation: **PASS**

Propagation is mechanical: `Theorem5_18_4_bimodule_decomposition_explicit`
calls `Theorem5_18_1_bimodule_decomposition_explicit` directly (line 484),
so the new clause flows through automatically. The destructure in
`Theorem5_18_4_GL_rep_decomposition_explicit` (line 571) was correctly
updated to `_, e, he` (placeholder skipping the new clause), with comment
noting the GL_N-side bridge is follow-up work. Existential signature
mirrors Theorem5_18_1's structure.

## Q4 — Heartbeat bump tightness: **FAIL — over-allocated**

Empirical bisection at `Theorem5_18_1_bimodule_decomposition_explicit`
(merged value: `maxHeartbeats 6400000` / `synthInstance.maxHeartbeats 2400000`):

| `maxHeartbeats` | `synthInstance.maxHeartbeats` | Outcome |
|----------------:|------------------------------:|---------|
| 3 200 000       | 1 200 000                     | FAIL (timeout at line 986 isDefEq + line 920 tactic) |
| 3 400 000       | 1 300 000                     | **PASS** |
| 3 600 000       | 1 400 000                     | **PASS** |
| 4 000 000       | 1 500 000                     | **PASS** |
| 6 400 000       | 2 400 000 (merged)            | PASS |

The merged values are ~88% above the empirical minimum
(3.4M / 1.3M). A reasonable safety buffer would be
`maxHeartbeats 4000000 / synthInstance.maxHeartbeats 1500000` (about
18% headroom over the minimum), matching the bisection-tightening
discipline already applied to other declarations in this file (cf. the
"empirical minimum is between X and Y" comment block at lines 463-469
and 618-623). Filed as **F1** below.

Per-build re-bisection on every CI run is wasteful; the recommendation
is a single follow-up PR that lowers the bump and updates the rationale
comment. The same bisection style was applied successfully in
PR #2598 (#2574-followup) and PR #2640 (#2601-followup).

## Q5 — Naming hygiene: **PASS** (with minor observation)

`isSimpleModule_homA_centralizer` matches Mathlib's lowercase
`isSimpleModule_<X>` convention (e.g. `isSimpleModule_iff_isAtom`,
`isSimpleModule_weylGroupRootRep`). The suffix `homA_centralizer`
parses as "the homA hom-space, simple over centralizer" — readable
but lightly underspecified (a stricter reading would be
`isSimpleModule_centralizer_homA` for "B-action on the hom-space").
Not blocking.

Docstring is accurate, includes the proof sketch (Schur ⇒ injective ⇒
extend ⇒ centralizer), and ties the result back to the bimodule
decomposition statement. Length appropriate.

## Q6 — Universe / typeclass parameters: **PASS**

Helper signature:

```lean
theorem isSimpleModule_homA_centralizer
    (A : Subalgebra k (Module.End k E))
    [IsSemisimpleModule A E]
    (V : Submodule A E) [IsSimpleModule A V] :
```

Section variables in scope: `[Field k]`, `[AddCommGroup E]`,
`[Module k E]`, `[Module.Finite k E]`. Lean 4 auto-binding only
includes section variables actually referenced by the
declaration's type/proof, so unused ones don't pollute the signature.

Typeclasses on the explicit binders are exactly what the proof needs:
`IsSemisimpleModule A E` for `extension_property` and
`IsSimpleModule A V` for Schur (`eq_bot_or_eq_top`). No spurious
`[CharZero k]` (matches the cleanup pattern from #2576/#2577/#2585),
no spurious `[FiniteDimensional]` or `[FaithfulSMul A E]`.

## Q7 — Downstream consumer impact: **PASS**

Searched the project for `Theorem5_18_1_bimodule_decomposition_explicit`
and `Theorem5_18_4_bimodule_decomposition_explicit`:

* `Theorem5_18_1.lean:794` — definition.
* `Theorem5_18_1.lean:484` — internal call from
  `Theorem5_18_4_bimodule_decomposition_explicit`'s proof; receives the
  whole tuple unchanged.
* `Theorem5_18_4.lean:464` — definition.
* `Theorem5_18_4.lean:571` — destructure in
  `Theorem5_18_4_GL_rep_decomposition_explicit`; updated to skip new
  clause.
* `FormalCharacterIso.lean:745` — only a docstring reference, no
  destructure.

No other consumers. `lake build EtingofRepresentationTheory.Chapter5.FormalCharacterIso`
succeeds at HEAD (8051 jobs). All existing destructuring patterns continue
to compile.

## Q8 — Build at HEAD: **PASS**

Both target builds at HEAD = `cc882f7..008eb7c` (after
fast-forward to `origin/main`):

* `lake build EtingofRepresentationTheory.Chapter5.Theorem5_18_1`:
  8026 jobs, success.
* `lake build EtingofRepresentationTheory.Chapter5.Theorem5_18_4`:
  8030 jobs, success.

(Linter warnings about `maxHeartbeats` comment placement — covered as
**F2** below.)

## Q9 — Sorry impact: **PASS**

`git show b05331c2 -- EtingofRepresentationTheory/Chapter5/Theorem5_18_1.lean
EtingofRepresentationTheory/Chapter5/Theorem5_18_4.lean | grep -E "^\+.*\bsorry\b|^-.*\bsorry\b"`
yields no output — PR #2634 introduced and removed zero `sorry`.

Current Chapter 5 actual `sorry` statements (excluding docstring/comment
mentions): 3 across 2 files
(`FormalCharacterIso.lean:399`, `SpechtModuleBasis.lean:1375, 1614`).
This is lower than the wave-57 baseline of 7 quoted in the issue body —
the difference is stale docstring-only mentions in `PolytabloidBasis.lean`
(theorems moved to `SpechtModuleBasis.lean`, docstrings still say
"sorry"). Not introduced by PR #2634; flagged as **F3**.

## Q10 — Follow-up hooks

* **F1** — Heartbeat bump tightening on
  `Theorem5_18_1_bimodule_decomposition_explicit`. See Q4 bisection table.
  Recommendation: lower to `maxHeartbeats 4000000` /
  `synthInstance.maxHeartbeats 1500000` and update the comment. Trivial
  refactor PR. Filed as **#2645** per the established pattern
  (#2598, #2640).
* **F2** — Three `linter.style.maxHeartbeats` warnings on
  `Theorem5_18_1.lean:544, 624, 772` and `Theorem5_18_4.lean:677`. The
  linter wants the rationale comment placed *between* the
  `set_option ... in` lines and the `theorem`, not above. Cosmetic,
  bundled into **#2645**.
* **F3** — Stale docstring `sorry` mentions in
  `PolytabloidBasis.lean:24, 26` (the theorems moved to
  `SpechtModuleBasis.lean`). Not from PR #2634; bundle into a future
  janitorial PR or close as won't-fix. Lowest priority.

None of F1/F2/F3 invalidates the merged work. F1 is the only one with
measurable build-time cost.

## Summary

PR #2634 cleanly exposes the B-side simplicity half of Schur-Weyl
Theorem 5.18.4(iii) by introducing `isSimpleModule_homA_centralizer` and
propagating it through the explicit bimodule existentials in
`Theorem5_18_1`/`Theorem5_18_4`. The helper proof is mathematically
correct (Schur ⇒ injection ⇒ extension via `IsSemisimpleModule.extension_property`
⇒ centralizer-action recovery). The single substantive concern is the
heartbeat bump (Q4): empirical bisection shows the merged 6.4M / 2.4M
is about 88% over the minimum-passing 3.4M / 1.3M; tightening to
4M / 1.5M is recommended (F1).
