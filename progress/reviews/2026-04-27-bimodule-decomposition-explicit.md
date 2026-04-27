# Explicit bimodule decomposition audit — PR #2509

**Issue**: #2557 (review).
**Session**: `530abd68` (2026-04-27).
**Scope**: audit the three artifacts landed by PR #2509
(`589cbd5` + `5cc8d43` + `35b0269`, closed issue #2489):

1. `schurEvaluationEquiv_apply_tmul`
   (`Theorem5_18_1.lean:179-213`)
2. `Theorem5_18_1_bimodule_decomposition_explicit`
   (`Theorem5_18_1.lean:693-876`)
3. `Theorem5_18_4_bimodule_decomposition_explicit`
   (`Theorem5_18_4.lean:463-479`)

These artifacts sit on the Schur-Weyl chain critical path and must
be sound before downstream PRs (#2540, #2482, #2483) consume the
evaluation formula.

Both files build cleanly (`lake build` passes — only style-linter
warnings, no errors). File sizes: `Theorem5_18_1.lean` 877 lines,
`Theorem5_18_4.lean` 587 lines — both within the 1000-line hard cap.

---

## Q1 — `schurEvaluationEquiv_apply_tmul` correctness: **PASS**

The lemma claims
```
schurEvaluationEquiv k A V M h (v ⊗ₜ f) = f v.
```
The proof reduces this to one `step1 := rfl` claim followed by a
`funext`-driven application of `endOfSimpleEquivAlgClosed_symm_smul_apply`
and `e.symm_apply_apply`.

### Tracing the `step1 := rfl`

`schurEvaluationEquiv` (`Theorem5_18_1.lean:140-170`) builds the iso
as `(TP.congr (refl V) (e1.trans (e2.trans e3))).trans (e4.trans e5)`,
where:

| Step | Type signature | Action on relevant input |
|------|----------------|--------------------------|
| `e1` = `homCongrRightOverSubring k A V e` | `(V →ₗ[A] M) ≃ₗ[k] (V →ₗ[A] (Fin n → V))` | `f ↦ e.toLinearMap.comp f` |
| `e2` = `homPiCurryEquiv k A V (Fin n)` | `(V →ₗ[A] (Fin n → V)) ≃ₗ[k] (Fin n → V →ₗ[A] V)` | `f' ↦ fun j => (proj j).comp f'` |
| `e3` = `piCongrRight (fun _ => endOfSimpleEquivAlgClosed.symm)` | `(Fin n → V →ₗ[A] V) ≃ₗ[k] (Fin n → k)` | `g ↦ fun j => (endOfSimpleEquivAlgClosed).symm (g j)` |
| `e4` = `TP.piScalarRight k k V (Fin n)` | `V ⊗[k] (Fin n → k) ≃ₗ[k] (Fin n → V)` | `v ⊗ₜ (fun j => cⱼ) ↦ fun j => cⱼ • v` |
| `e5` = `e.symm.restrictScalars k` | `(Fin n → V) ≃ₗ[k] M` | `e.symm` |

Tracing `v ⊗ₜ f`:
1. `TP.congr (refl) (e1.trans (e2.trans e3))` applied to `v ⊗ₜ f`
   gives `v ⊗ₜ (fun j => endOfSimpleEquivAlgClosed.symm
   ((proj j).comp (e.toLinearMap.comp f)))`.
2. `e4` (a `TP.piScalarRight`) on a pure tensor `v ⊗ₜ (fun j => cⱼ)`
   reduces componentwise to `fun j => cⱼ • v` — definitional on
   pure tensors.
3. `e5` applies `e.symm`.

Endpoint matches `step1` exactly:
```
e.symm (fun j =>
  (endOfSimpleEquivAlgClosed k A V).symm
    ((LinearMap.proj j).comp (e.toLinearMap.comp f)) • v)
```
Each step uses constructor-level `defeq` (`TP.congr_tmul`, `refl_apply`,
`piScalarRight_tmul` are all `rfl`-level on pure tensors), and the
build accepts the `rfl`. Honest. ✓

### Auxiliary checks

- **`endOfSimpleEquivAlgClosed_symm_smul_apply` semantics** —
  `endOfSimpleEquivAlgClosed k A V : k ≃ₗ[k] (V →ₗ[A] V)` is `End_A V → k`
  (lines 64-71); the `.symm φ • v = φ v` form (lines 77-94) is the
  standard "extract the scalar" identity, derived from
  `Algebra.algebraMap_eq_smul_one` and `LinearMap.congr_fun`. Correctly
  applied in `step1`'s `hv` branch (line 207). ✓
- **`hv j`** identifies `(proj j).comp (e ∘ f) v = e (f v) j` (line 205).
  This is `LinearMap.proj_apply ∘ LinearMap.comp_apply`; `rfl` is
  honest. ✓
- **Closing `e.symm_apply_apply`** (line 213) — after `funext` rewrites
  the inner argument to `e (f v)`, applying `e.symm` gives `f v`. ✓

No scalar-factor / sign / `congr`-noise drift. Lemma proves exactly
what it claims.

---

## Q2 — `Theorem5_18_1_bimodule_decomposition_explicit`: **PASS**

The theorem produces the existential
```
∃ ι Fintype DecidableEq V (Simple V) (Distinct V), ∃ e, ∀ i v l,
  e.symm (of i (v ⊗ₜ l)) = l v
```
specialized to `V : ι → Submodule A E`, `Lᵢ := V i →ₗ[A] E`.

### `perComp_symm_tmul` (lines 749-778)

The `perComp` per-component iso is built (line 657 / 746) as
```
sE.symm.trans (TP.congr (refl k _) br)
```
where `sE = schurEvaluationEquiv` and `br = homIsotypicBridge`. So
`(perComp c).symm = (TP.congr refl br).symm.trans sE`.

Proof rewrites:
1. `LinearEquiv.trans_symm` flips the chain.
2. `LinearEquiv.symm_symm` cancels the inner `.symm.symm`.
3. `LinearEquiv.trans_apply` peels into composition.
4. `TP.congr_symm` + `LinearEquiv.refl_symm` simplify the inner symm.
5. `TP.congr_tmul` + `LinearEquiv.refl_apply` evaluate on the pure
   tensor.
6. `schurEvaluationEquiv_apply_tmul` reduces the outer `sE` to the
   evaluation `(br.symm l) v`.

After these rewrites the goal is
`((br.symm l) v : E) = l v`. `homIsotypicBridge.symm` (lines 521-527)
is constructed with `invFun g := g.codRestrict c (...)`, so
`br.symm l = l.codRestrict c _`, and
`(l.codRestrict c h v).val = l v` is `rfl` (constructor of `Subtype`).
The closing `rfl` (line 778) is honest. ✓

### Reindexing and full chain (lines 779-876)

The total iso `e2.trans (e3.trans e4)` chains
- `e2`: `(isotypicDirectSumEquiv).symm.restrictScalars k`,
- `e3`: `DFinsupp.mapRange.linearEquiv perComp`,
- `e4`: `DirectSum.lequivCongrLeft k φ`.

The forward-direction proof verifies `etotal (l v) =
DirectSum.of _ i (v ⊗ₜ l)` step-by-step:
- `iSupIndep.linearEquiv_symm_apply` (line 828) places `l v` in the
  correct `DFinsupp.single` slot — uses
  `range_le_isotypicComponent_of_simple` to discharge `l v ∈ (φ.symm i).1`.
- `DFinsupp.mapRange_single` (line 856) lifts through `e3` cleanly.
- `DirectSum.lequivCongrLeft_apply` (line 869) reindexes via `φ`.

The case split (`hk : k' = i`) uses `DirectSum.of_eq_same` /
`DFinsupp.single_eq_same` for the matching index and
`DirectSum.of_eq_of_ne` / `DFinsupp.single_eq_of_ne` for the
non-matching indices. The injectivity of `φ.symm` (line 874) is
correctly invoked.

The reindexing **commutes** with the per-component evaluation: `e4`
just shuffles the index from `isotypicComponents A E` to `Fin m`, the
per-component formula `e.symm (of i (v ⊗ₜ l)) = l v` survives because
`of` is the canonical injection at index `i`, and `lequivCongrLeft`
acts by precomposing the index. ✓

### B-equivariance doc-string claim (lines 684-688)

The doc-string states that the evaluation formula implies
```
e.symm (of i (v ⊗ₜ (b • l))) = b.val (l v) = b.val (e.symm (of i (v ⊗ₜ l))).
```
Under the natural `Module ↥(centralizer A) (V_i →ₗ[A] E)` structure
(post-composition by `b`), `(b • l) v = b.val (l v)` definitionally.
So the `e.symm`-image of the pure-tensor basis indeed coincides with
`b.val` applied to the `l v` of the unscaled basis. Correct logic.
The theorem itself **does not** state B-equivariance — only the
evaluation formula — and the doc-string says "implies" / "is the
form required by", not "proves". Descriptive, not overpromising. ✓

---

## Q3 — `Theorem5_18_4_bimodule_decomposition_explicit`: **PASS**

The signature (lines 463-475) is the **direct specialization** of
(2) with `A := symGroupImage k V n` and `E := TensorPower k V n`:

| (2) generic | (3) specialized |
|-------------|-----------------|
| `V : ι → Submodule A E` | `S : ι → Submodule (symGroupImage k V n) (TensorPower k V n)` |
| `↥(V i) ⊗[k] (↥(V i) →ₗ[A] E)` | `↥(S i) ⊗[k] (↥(S i) →ₗ[symGroupImage k V n] TensorPower k V n)` |
| `e.symm (of i (v ⊗ₜ l)) = l v` | identical, with the specialized `S`/`L` |

No silent rebinding of summand types or evaluation-formula domain.

### Proof: pure transport (lines 476-479)

```
haveI := symGroupImage_isSemisimpleRing k V n
haveI := symGroupImage_faithfulSMul k V n hN
exact Theorem5_18_1_bimodule_decomposition_explicit k (TensorPower k V n)
  (symGroupImage k V n)
```

Four lines, no extra content, no proof obligation beyond the two
typeclass instances. ✓

### `[CharZero k]` necessity

The hypothesis is **genuinely required**, dispatched via
`symGroupImage_isSemisimpleRing` (`Theorem5_18_4.lean:166-174`) which
needs `[CharZero k]` to apply Maschke's theorem (the group algebra
`k[Sₙ]` is semisimple iff char `k` does not divide `|Sₙ| = n!`).

Without `[CharZero k]`, `symGroupImage k V n` is not necessarily a
semisimple ring, and the typeclass `[IsSemisimpleRing A]` required by
(2) cannot be discharged. So (3)'s `[CharZero k]` is **not** spurious;
removing it would break the proof, not just the linter.

This is consistent with the non-explicit
`Theorem5_18_4_bimodule_decomposition` (line 414) which also takes
`[CharZero k]` for the same reason. **Not** in scope of #2559 (which
targets `formalCharacter_coeff` and downstream).

`hN : n ≤ Module.finrank k V` is needed for
`symGroupImage_faithfulSMul`. Both hypotheses match the expected
preconditions for the (2)-call.

---

## Q4 — Heartbeat bumps and closure usage: **PASS-with-followup**

Both `_explicit` theorems carry
```
set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1200000 in
```
(`Theorem5_18_1.lean:671-672`, `Theorem5_18_4.lean:446-447`).

### Necessity

The bumps compile. I did **not** run the
"reduce-and-check-timeout" experiment — each iteration is an 8000+
job rebuild, prohibitively expensive in this audit window. The
existential output of (2) packs ≈12 ∀-binders with subalgebra-wrapped
ring instance chains, which is the documented reason for the bumps
in adjacent constructions (lines 537-538 of the same file, for the
non-explicit `Theorem5_18_1_bimodule_decomposition`).

The (3) bump is even less worth tightening on its own — it is a
direct transport call whose own elaboration is trivial; the bump
exists purely to stay above (2)'s budget through unification.

### `decide` / `omega` usage

`grep` shows **zero** `decide` / `omega` calls inside either
`_explicit` theorem (the only `omega` in `Theorem5_18_4.lean` is line
359, far outside the audit scope). No brittleness against future
Mathlib bumps from `omega`/`decide` heuristics. ✓

### Linter warning (low-priority follow-up)

The `linter.style.maxHeartbeats` linter complains at both call sites
because the comment justifying the bump is placed **above** the
`set_option` rather than between options:

```
-- Heartbeat bumps match `Theorem5_18_1_bimodule_decomposition_explicit`.
set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1200000 in
```

The linter wants:

```
set_option maxHeartbeats 3200000 in
-- reason for change
set_option synthInstance.maxHeartbeats 1200000 in
...
```

This is a **pre-existing pattern** affecting 9+ existing call sites
(`Theorem5_18_1.lean:345, 424, 463, 480, 509, 537, 671`;
`Theorem5_18_4.lean:392, 446, 494`). Not specific to PR #2509. A
file-wide cleanup would address all of them; spinning a dedicated
follow-up just for the two new sites is not worth the noise. **Flag
for a future opportunistic cleanup pass** but no separate issue
filed.

---

## Q5 — Doc-string vs. theorem statement: **PASS**

### B-equivariance claim (Q2 doc-string)

Already validated under Q2: the wording "implies" / "is the form
required by" is descriptive of what callers will derive, not what
the theorem itself proves. Logic is sound. ✓

### Cross-references

| Reference in doc-string | State (verified via `gh issue view`) | Accurate? |
|------------------------|--------------------------------------|-----------|
| "Schur-Weyl #3 in #2458" | #2458 CLOSED (original tracker, decomposed into #2540 etc.) | ✓ Cross-reference still meaningful — #2458 captures the original Schur-Weyl #3 plan |
| "character-additivity arguments (Schur-Weyl #3, #5, #6)" | #2540 OPEN, #2482 OPEN, #2483 OPEN | ✓ |
| Issue #2489 (parent) | CLOSED by PR #2509 | ✓ |

No stale or misleading references. ✓

---

## Q6 — Downstream usability: **PASS**

The downstream consumers cited in the issue body:

### `glTensorRep_equivariant_schurWeyl_decomposition` (#2540, FormalCharacterIso.lean:758-774)

Currently a `sorry` (line 774). Output type uses
`S : ι → Type u` (not `Submodule`) and
`L : ι → FDRep k (GL_N k)` (not `↥(S i) →ₗ[symGroupImage k V n] V^⊗n`).

To bridge from (3) to this consumer, #2540 must:
1. Apply `Theorem5_18_4_bimodule_decomposition_explicit` to get
   Submodule summands and the evaluation formula.
2. Coerce each `S i : Submodule _ _` to `↥(S i) : Type v`. Since
   `V := Fin N → k` makes `v = u` (variable instantiation), the
   resulting type lives in `Type u` — matches the consumer's
   `S : ι → Type u`.
3. Wrap each `Lᵢ` hom-space as `FDRep k (GL_N k)` using
   `Theorem5_18_4_GL_rep_decomposition` (`Theorem5_18_4.lean:510-585`,
   already merged) — that theorem composes
   `GL_N → centralizer(symGroupImage)` with
   `Module.toModuleEnd k (Lᵢ)` to produce the GL_N representation.
   Note `Theorem5_18_4_GL_rep_decomposition` consumes the **non**-
   explicit `Theorem5_18_1_bimodule_decomposition`; #2540 instead
   needs the **explicit** version's evaluation formula to derive
   GL_N-equivariance, then re-package as FDRep.

The signature of (3) is **sufficient**: ι, Submodule summands, and
the pure-tensor evaluation formula are exactly what's needed for
the equivariance argument. No spurious or restrictive instance
hypothesis missing.

### `polynomial_rep_decomposition_via_schurWeyl` (#2482), `iso_of_formalCharacter_eq_schurPoly` (#2483)

Both blocked on #2540 / #2482 chain; their consumption of (3) is
mediated by `glTensorRep_equivariant_schurWeyl_decomposition`. No
direct shape mismatch identified.

### Universe alignment

`Theorem5_18_4_bimodule_decomposition_explicit` is parameterized in
`V : Type v`. With the consumer's `V := Fin N → k`, `v = u`, so
the Submodule summands `↥(S i)` live in `Type u` — matches the
downstream `Type u` expectation. ✓

### No `Module.Free k` or other restrictive hypothesis

The explicit theorem only requires `[Field k] [IsAlgClosed k]
[Module.Finite k E]` (inherited from variable section), plus
`[IsSemisimpleRing A] [FaithfulSMul A E]`. No `Module.Free`, no
characteristic restriction, no projectivity. ✓

---

## Summary — all checks PASS

| Focus | Result | Notes |
|-------|--------|-------|
| Q1 `schurEvaluationEquiv_apply_tmul` | PASS | `step1 := rfl` traces honestly through the 5-step chain; helper lemma applied with correct semantics. |
| Q2 (2)'s evaluation formula and reindexing | PASS | `perComp_symm_tmul` rfl is honest (homIsotypicBridge.symm = codRestrict); reindexing via `lequivCongrLeft` commutes with per-component formula. |
| Q3 (3) Schur-Weyl specialization | PASS | Pure transport from (2). `[CharZero k]` necessary for Maschke. Signature exact specialization. |
| Q4 heartbeat bumps + closure usage | PASS-with-followup | Bumps compile, no decide/omega in scope. Linter complains about comment placement (pre-existing pattern, 9+ call sites — defer to opportunistic cleanup). |
| Q5 doc-strings vs. statements | PASS | Doc-strings descriptive, not overpromising. Cross-references valid. |
| Q6 downstream usability | PASS | Signature matches #2540's needs; universe alignment correct; no spurious hypotheses. |

**No correctness defects found. No DEFECT or CONCERN findings. No
new follow-up issues filed.**

The (Q4) maxHeartbeats-comment-placement issue is pre-existing and
noisy across the file; appropriate to address in a future
file-wide cleanup, not as a dedicated #2509 follow-up.

Build verification: `lake build EtingofRepresentationTheory.Chapter5.Theorem5_18_1
EtingofRepresentationTheory.Chapter5.Theorem5_18_4` succeeds (`/tmp/build-2557.log`).
