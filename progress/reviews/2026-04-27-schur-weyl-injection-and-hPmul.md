# Schur-Weyl plumbing audit — PRs #2528 + #2551 (PolynomialRepEmbedding)

**Issue**: #2554 (review).
**Session**: `eda43592` (2026-04-27).
**Scope**: audit the un-reviewed plumbing additions in
`Chapter5/PolynomialRepEmbedding.lean`:

- **PR #2528** (`9ecac42`, `feat(Ch5 #2478): polynomialRep_embeds_in_tensorPower
  injection (Schur-Weyl #2b partial)`, +341 lines): the polynomial-rep
  injection — `polyTensorRow`, `polyTensorRow_eq_zero_iff`,
  `polyTensorBundle`, `polyTensorBundle_apply`,
  `polynomialRep_embeds_in_tensorPower_inj`.
- **PR #2551** (`67db8c5`, `feat(Ch5): derive hP_mul from ρ.map_mul via
  MvPolynomial.funext + detPoly trick (#2527 follow-up)`, +190 lines): the
  `hP_mul` derivation — `MvPolynomial.eq_of_eval_eq_on_gl`,
  `eval_polyRightTransl`, `hP_mul_of_hP`,
  `polynomialRep_embeds_in_tensorPower'`.

The intervening equivariance layer (PRs #2538 + #2539) was already audited
in #2547 (PASS). This audit covers the injection part (#2528) and the
`hP_mul` derivation (#2551), as called out in the issue body.

`lake build EtingofRepresentationTheory.Chapter5.PolynomialRepEmbedding`
passes (8033/8033, no errors; only pre-existing `linter.style.show`
warnings in the bridge file, none in PolynomialRepEmbedding.lean itself).

File now at **761 lines** (was 571 post-PR #2539; +190 from PR #2551).
Crosses the 500-line soft threshold — see file-size note at the bottom.

---

## Q1 — `polyTensorRow` / `polyTensorBundle` / injection: **PASS**

### Bundle construction is correct

`polyTensorBundle_apply` (line 174-181) reads:

```
polyTensorBundle x p =
  splitDualBasis (polyTensorRow b P hhom p.1 x) p.2
```

with index types `p : Fin d × (Fin n → Fin N)`:

- `p.1 ∈ Fin d` — basis-row index of the polynomial rep `M`.
- `p.2 ∈ Fin n → Fin N` — `(V*)^⊗n`-standard-basis index.

Tracing: for each basis row `a = p.1`, `polyTensorRow ... a x ∈ V^⊗n ⊗
(V*)^⊗n` is the bridge of the row-`a` matrix-coefficient polynomial of
`x`. Then `splitDualBasis` (line 54-60) decomposes `V^⊗n ⊗ (V*)^⊗n` as
`((Fin n → Fin N) → V^⊗n)` via the dual-standard-basis decomposition of
the `(V*)^⊗n` factor. Evaluating at `p.2` extracts the `p.2`-th `V^⊗n`
component. ✓

This realises the intended bundle: one polynomial per row, evaluated at
every pure-tensor basis index of `(V*)^⊗n`. The bridge sends the
homogeneous polynomial `Σ_{f} c_f X_{f(1)} … X_{f(n)}` to
`Σ_f c_f · (e_{f.1} ⊗ … ⊗ e_{f.1}) ⊗ (e^*_{f.2} ⊗ … ⊗ e^*_{f.2})`; the
`splitDualBasis` strips the second factor, giving a `Fin (N^n)`-indexed
direct sum of `V^⊗n`. The first factor (which is what's left in each
coordinate) is the `V^⊗n`-vector built from the `f.1` row indices —
exactly the data Schur-Weyl wants. ✓

### Injectivity reduction

`polynomialRep_embeds_in_tensorPower_inj` (lines 201-281) follows this
chain:

1. `polyTensorBundle x = 0` (function on `Fin d × (Fin n → Fin N)`).
2. ⟹ for each `a, j`: `splitDualBasis (polyTensorRow ... a x) j = 0`.
3. ⟹ for each `a`: `splitDualBasis (polyTensorRow ... a x) = 0`
   (via `funext`).
4. ⟹ for each `a`: `polyTensorRow ... a x = 0` (since `splitDualBasis`
   is a `LinearEquiv`, via `LinearEquiv.map_eq_zero_iff`).
5. ⟹ for each `a`: `matrixCoeffPoly k N b P a x = 0`
   (via `polyTensorRow_eq_zero_iff`, which bottoms out at
   `homogeneousPolyToTensor_injective`). ✓
6. ⟹ for every `g, a`: `b.coord a (ρ g x) = 0`
   (via `eval_matrixCoeffPoly`, evaluating the matrix-coefficient
   identity at the entries of `g`).
7. ⟹ for every `g`: `ρ g x = 0` (since `b.repr` is injective and all
   coordinates vanish).
8. Set `g = 1`: `x = ρ 1 x = 0` (by `ρ.map_one`). ✓

Each step is sound. Step 5 is the **critical** one — it bottoms out at
`homogeneousPolyToTensor_injective`, exactly as the audit prompt asks.

### `[CharZero k]` necessity

The hypothesis is **necessary at the current granularity**:

- `polyTensorRow` and `polyTensorBundle` reference
  `homogeneousPolyToTensor` (`PolynomialTensorBridge.lean:124`), which
  sits inside the `variable [CharZero k]` block (line 167) of the bridge
  file.
- `polyTensorRow_eq_zero_iff` and the injection theorem cite
  `homogeneousPolyToTensor_injective` (line 276), whose proof uses the
  symmetrisation factor `(n!)⁻¹` — genuinely needs `n! ≠ 0`, hence
  `CharZero k` (or a weaker `Nat.factorial n ≠ 0` in `k`).

The injection's hypothesis is therefore tight against the bridge's own
hypothesis; relaxing it would require relaxing the bridge first
(replacing `[CharZero k]` with `[Nat.factorial n ≠ 0 in k]`-style data),
which is a separate substantial refactor not in scope. **No follow-up
filed for this** — it's correct as stated.

---

## Q2 — `MvPolynomial.eq_of_eval_eq_on_gl`: **PASS** (Mathlib-PR-ready)

### Statement and proof are correct

The lemma (lines 598-639) reads:

```
{k : Type*} [Field k] [Infinite k] {N : ℕ}
{p q : MvPolynomial (Fin N × Fin N) k}
(h : ∀ g : GL N k, eval (entries of g) p = eval (entries of g) q) :
p = q
```

Proof strategy:

1. Apply `MvPolynomial.funext` to `(p - q) * det(X)`. At every `s : Fin
   N × Fin N → k`:
   - If `det(eval s X) = 0`, the product evaluates to 0 trivially.
   - If `det(eval s X) ≠ 0`, then `s` defines `mkOfDetNeZero ... ∈ GL N
     k`, and the hypothesis gives `eval s p = eval s q`, so the product
     evaluates to 0.
2. Hence `(p - q) * det(X) = 0` as polynomial.
3. `Matrix.det_mvPolynomialX_ne_zero` gives `det(X) ≠ 0`.
4. `MvPolynomial σ k` is an integral domain (since `k` is), so
   `mul_eq_zero.mp ... |>.resolve_right` extracts `p - q = 0`.
5. `sub_eq_zero.mp` finishes. ✓

Each step is sound. The funext-step replaces a Zariski-density argument
with a more constructive multiplication trick — clean and idiomatic for
Lean.

### Hypothesis `[Field k] [Infinite k]` is correct

- `[Infinite k]` is needed by `MvPolynomial.funext` (line 80, 84 in
  `Mathlib.Algebra.MvPolynomial.Funext`).
- `[Field k]` is needed by `Matrix.GeneralLinearGroup.mkOfDetNeZero`
  (line 116 in `Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs`),
  which constructs `GL N k` from `det A ≠ 0`. Over a general commutative
  ring this would need `IsUnit (det A)` instead.

`[CharZero k]` is **not** needed (and not used). The PR correctly weakens
to `[Infinite k]`. ✓

### Mathlib-PR-ready check

Searched Mathlib (`Mathlib/Algebra/MvPolynomial/*` and
`Mathlib/LinearAlgebra/Matrix/MvPolynomial.lean`) for similar lemmas:

- `MvPolynomial.funext` and `MvPolynomial.funext_set` are the only
  evaluation-density lemmas. `funext_set` requires evaluation agreement
  on a *product* of infinite sets — not directly applicable to the
  Zariski-dense GL set.
- `det_mvPolynomialX_ne_zero` exists but has no companion polynomial-
  identity lemma using it.
- No hits on `eq_of_eval_eq_on_gl` / `eval_eq_on_gl` / similar names.

The lemma is genuinely new and Mathlib-shaped:

- Top-level (in `namespace MvPolynomial`, not project namespace).
- Hypothesis-minimal (`[Field k] [Infinite k]` is tight).
- Proof uses only Mathlib infrastructure (`MvPolynomial.funext`,
  `Matrix.det_mvPolynomialX_ne_zero`, `mkOfDetNeZero`).

**Recommendation**: file a `mathlib-upstream` tracking issue noting it as
a candidate for upstream contribution. Filing it as a follow-up
(see Findings, F1).

### Mathlib API choice

`Matrix.GeneralLinearGroup.mkOfDetNeZero` is the right Mathlib API —
it is the canonical "matrix-with-nonzero-det → GL element" construction
over a field. The alternative `Matrix.det_ne_zero_iff_isUnit` +
`Units.mk` path would re-derive the same content less directly.
`mkOfDetNeZero` is correct. ✓

---

## Q3 — `hP_mul_of_hP` and primed wrapper: **PASS**

### `[CharZero k]` chain consistency

The `[CharZero k]` propagation through PR #2551:

- `eval_polyRightTransl` (line 652): declares `[CharZero k]`. The
  intrinsic content (a substitution + AlgHom-extension) does not need
  `CharZero` — the proof uses `MvPolynomial.algHom_ext`,
  `polyRightTransl_X`, and `Matrix.mul_apply`.
- `hP_mul_of_hP` (line 680): declares `[CharZero k]`. Calls
  `eval_polyRightTransl` (`[CharZero k]`) and
  `MvPolynomial.eq_of_eval_eq_on_gl` (`[Infinite k]` only).

I verified empirically by removing `[CharZero k]` from
`eval_polyRightTransl`: the build fails because
`PolynomialTensorBridge.polyRightTransl_X` (used in the proof) carries
`[CharZero k]` from the bridge file's section variable (line 167) via
auto-binding. So `[CharZero k]` here is **propagated from upstream**
(`polyRightTransl_X`'s declaration site), not intrinsically needed.

This means: if a future cleanup adds `omit [CharZero k] in` to
`polyRightTransl_X` (line 403 in the bridge file), then
`eval_polyRightTransl` and `hP_mul_of_hP` could drop `[CharZero k]` and
require only `[Field k] [Infinite k]`. This is a worthwhile cleanup
because the chain bottoms out at `eq_of_eval_eq_on_gl` — which itself
only needs `[Infinite k]` — but it requires touching the bridge file
too.

**Filing as a follow-up** (F2) — minor cleanup, not a defect. Currently
all downstream Schur-Weyl consumers carry `[CharZero k]`, so it costs
nothing functionally.

The audit-prompt question "could it be relaxed?" — answer: **yes, with a
one-line `omit [CharZero k] in` on `polyRightTransl_X`**. Not blocking.

### Primed wrapper hides only `hP_mul`

Direct text comparison of the two theorems:

`polynomialRep_embeds_in_tensorPower` (line 474, signature lines
479-501): takes `hpoly : ∃ d b P, hhom ∧ hP ∧ hP_mul`.

`polynomialRep_embeds_in_tensorPower'` (line 736, signature lines
741-756): takes `hpoly' : ∃ d b P, hhom ∧ hP`.

Conclusions are *textually identical* (both lines 750-756 and 495-501):

```
∃ (m : ℕ) (φ : M →ₗ[k] (Fin m → TensorPower k (StdV k N) n)),
  Function.Injective φ ∧
  ∀ (g : GL N k) (x : M) (i : Fin m),
    φ (ρ g x) i = PiTensorProduct.map (fun _ => Matrix.toLin' g) (φ x i)
```

The body of the wrapper (line 757-759):

```
obtain ⟨d, b, P, hhom, hP⟩ := hpoly'
exact polynomialRep_embeds_in_tensorPower k N n ρ halg
  ⟨d, b, P, hhom, hP, fun g a c' => hP_mul_of_hP k N b P ρ hP g a c'⟩
```

The wrapper:
1. Destructures `hpoly'` to `(d, b, P, hhom, hP)`.
2. Calls the unprimed theorem with the same `(d, b, P, hhom, hP)` plus
   the derived `hP_mul := hP_mul_of_hP k N b P ρ hP`.
3. Forwards the result via `exact`.

So the only thing the primed form hides is `hP_mul`. The conclusion
(`m`, `φ`, injectivity, equivariance) is forwarded *verbatim* from the
unprimed form. ✓

### Hypothesis content of `hP_mul_of_hP` is honest

Sketch: by `eq_of_eval_eq_on_gl`, it suffices to show evaluation
agreement at every `h ∈ GL N k`:

- LHS: `eval_h (polyRightTransl g (P a c'))`. By `eval_polyRightTransl`,
  this is `eval_{h·g}(P a c')`. By `hP`, this is `b.coord a (ρ(h·g)(b
  c'))`. By `ρ.map_mul`, this is `b.coord a (ρ h (ρ g (b c')))`.
- RHS: `eval_h (Σ_c eval_g(P c c') • P a c) = Σ_c eval_g(P c c') ·
  eval_h(P a c) = Σ_c b.coord c (ρ g (b c')) · b.coord a (ρ h (b c))`
  (by `hP` twice).
- Expanding `ρ g (b c') = Σ_c b.coord c (ρ g (b c')) • b c` (basis
  representation), then pushing `ρ h` and `b.coord a` through the
  `k`-linear sum, both sides match.

Proof at lines 697-727 follows this structure exactly. No content
smuggled in. ✓

---

## Findings — non-blocking follow-ups

Two follow-up issues to file (small, one-shot, not blocking the audit):

### F1 — Mathlib-upstream candidate: `eq_of_eval_eq_on_gl`

`MvPolynomial.eq_of_eval_eq_on_gl` (PolynomialRepEmbedding.lean:598) is
genuinely Mathlib-shaped, hypothesis-minimal, and uses only Mathlib
infrastructure. File a `mathlib-upstream` tracking issue (do **not** PR
upstream from this audit, per the prompt).

### F2 — Bridge cleanup: `polyRightTransl_X` could be `omit [CharZero k]`

`Chapter5/PolynomialTensorBridge.lean:403` carries `[CharZero k]` via
section auto-binding, but its proof body (`unfold polyRightTransl; rw
[MvPolynomial.aeval_X]`) doesn't actually need it. Add `omit [CharZero
k] in` before the lemma. Cascade: `eval_polyRightTransl` and
`hP_mul_of_hP` in PolynomialRepEmbedding.lean can then drop `[CharZero
k]` too, leaving the polynomial-identity-from-GL-evaluation chain
requiring only `[Field k] [Infinite k]` — matching the underlying
`eq_of_eval_eq_on_gl`. One-line bridge change + two-line consumer
relaxation.

### Minor opportunistic cleanups (not worth dedicated issues)

- `polynomialRep_embeds_in_tensorPower_inj` (line 277-281) and
  `polynomialRep_embeds_in_tensorPower` (line 556-559) duplicate the
  "set `g = 1` to recover `x = 0`" coda. Could be factored into a helper
  `representation_eq_zero_of_forall : (∀ g, ρ g x = 0) → x = 0`. Five
  lines saved across two theorems; pick up opportunistically.
- `polyTensorRow_eq_zero_iff` (lines 142-154) has a verbose
  `show ... ↔ ... from ⟨..., ...⟩` block that could be replaced with a
  `LinearMap.comp_apply` rewrite + simpler `(homogeneousPolyToTensor_injective
  _ _ _).eq_iff_eq_zero`-style step. Slop flag, ~10 lines.

---

## Summary — all checks PASS

| Focus | Result | Notes |
|-------|--------|-------|
| Q1 injection construction & necessity of `[CharZero k]` | PASS | `polyTensorBundle x p = splitDualBasis (polyTensorRow ...) p.2` is the intended bundle; injection bottoms out at `homogeneousPolyToTensor_injective`; `[CharZero k]` is tight against the bridge. |
| Q2 `eq_of_eval_eq_on_gl` correctness & Mathlib-readiness | PASS | Statement & proof correct (`[Field k] [Infinite k]` tight); no Mathlib duplicate; Mathlib-PR-ready (file F1 upstream tracker). |
| Q3 `hP_mul_of_hP` chain & primed wrapper | PASS | `[CharZero k]` propagated from `polyRightTransl_X` upstream; primed wrapper hides only `hP_mul`, conclusion identical to unprimed form; derivation is honest. |

**No correctness defects found. No CONCERN or FAIL findings.**

Two small follow-up issues to file (F1 mathlib-upstream tracker; F2
bridge cleanup). Minor opportunistic cleanups (set-`g=1` coda
deduplication; verbose `show` block) noted for future passes; not worth
dedicated issues.

## File-size observation

`PolynomialRepEmbedding.lean` has grown from 571 (post-PR #2539) to
**761 lines** (post-PR #2551, +190). Crosses the 500-line soft threshold
substantially; still well under the 1000-line hard cap. Content is
cohesive (single theorem chain ending in the primed wrapper). No split
recommended at this wave — but if the next wave adds another sizeable
chunk (e.g. an `IsAlgebraicRepresentation → hpoly'` helper for #2482
consumption), revisit and consider splitting the
`MvPolynomial.eq_of_eval_eq_on_gl` namespace block into its own file
`Chapter5/MvPolynomialGLEval.lean`.
