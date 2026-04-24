# Schur-Weyl equivariance audit — PRs #2538 + #2539

**Issue**: #2547 (review).
**Session**: `18da5fb1` (2026-04-24).
**Scope**: audit the Schur-Weyl equivariance layer landed in the
last wave.

- PR #2538 — `feat(Ch5 #2527 Part A): bridge equivariance —
  polyToTensor_rightTransl + homogeneousPolyToTensor_equivariant`
  (+314 lines; `Chapter5/PolynomialTensorBridge.lean`).
- PR #2539 — `feat(Ch5 #2537): polynomialRep_embeds_in_tensorPower
  equivariance (#2527 Part B)` (+357 lines;
  `Chapter5/PolynomialRepEmbedding.lean`).

Together these deliver the equivariant embedding that downstream
#2482 (Schur-Weyl #5) and #2483 (Schur-Weyl #6) consume.

Both files carry **zero sorries** (`grep -n sorry` empty). Neither
file exceeds the 1000-line hard cap (`wc -l`: 677 and 571 lines
respectively; both over the 500-line soft threshold but content is
cohesive — see final notes).

---

## R1 — Statement correctness (highest priority): **PASS**

Verified that each equivariance lemma's action conventions are
consistent on both sides.

### Polynomial side: `polyRightTransl`
(`PolynomialTensorBridge.lean:299-302`)

```
polyRightTransl g := aeval (fun ij => ∑ l, X (i, l) * C (g l ij.2))
```

So `polyRightTransl g (X_{i,j}) = ∑_l X_{i,l} · g_{l,j}`. That is
the substitution pulling back `X_{ij}` along `M ↦ M·g`, which
means `(polyRightTransl g P)(M) = P(M·g)`. The docstring at line
297 (`(g · P)(X) = P(X·g)`) is correct.

Composition: `polyRightTransl (gh)` corresponds to `M ↦ P(M·gh) =
P((M·g)·h)`, hence `polyRightTransl(gh) = polyRightTransl(g) ∘
polyRightTransl(h)` (covariant functorial on the substitution
side). The bridge lines this up with `tgtGLAction` on the tensor
side.

### Tensor side: `tgtGLAction`
(`PolynomialTensorBridge.lean:307-309`)

```
tgtGLAction g := TensorProduct.map (PiTensorProduct.map (fun _ => g.toLin')) id
```

So `tgtGLAction g = (g^⊗n) ⊗ id` on `V^⊗n ⊗ (V^*)^⊗n`.
Composition: `tgtGLAction(gh) = tgtGLAction g ∘ tgtGLAction h` (by
functoriality of `PiTensorProduct.map`). Matches `polyRightTransl`.

**Both actions compose in the same direction** — no
contravariant/covariant flip. ✓

### Core equivariance: `polyToTensor_rightTransl_of_isHomogeneous`
(`PolynomialTensorBridge.lean:616-660`)

Traced the monomial case directly:

- LHS: `polyToTensor (polyRightTransl g (∏_l X(f l)))`.
  - By `polyRightTransl_prod` (lines 414-435): expands to
    `∑_c C(∏_l g_{c l, (f l).2}) · ∏_l X((f l).1, c l)`.
  - By `polyToTensor_prod_X` (line 551): each `∏_l X(h l) ↦
    symTensor h`.
  - So LHS = `∑_c (∏_l g_{c l, (f l).2}) • symTensor (l ↦ ((f l).1, c l))`.
- RHS: `tgtGLAction g (polyToTensor (∏_l X(f l))) =
  tgtGLAction g (symTensor f)`.
  - By `tgtGLAction_symTensor` (lines 346-377): expands to
    `∑_c (∏_l g_{c l, (f l).2}) • symTensor (l ↦ ((f l).1, c l))`.

Same index structure, same scalar, same tensor. The key check is
that `polyRightTransl g` replaces the column index (second
component of the pair) but keeps the row index (first component)
fixed, while `tgtGLAction g` acts on the `V^⊗n` (row) factor by
the matrix `g` and leaves `(V^*)^⊗n` (column) alone. These two
moves exactly mirror one another through `polyToTensor`. ✓

### Consistency of the `toLin'_stdBasis` lemma
(`PolynomialTensorBridge.lean:312-320`)

`toLin' g (e_j) = ∑_b g_{b,j} • e_b`. This is the standard
column-convention identification of `Matrix (Fin N) (Fin N) k`
with `End (Fin N → k)` via `Matrix.toLin'`, where `g` acts on the
column vector from the left. Consistent with both sides of the
equivariance above. ✓

### Bundled assembly: `polynomialRep_embeds_in_tensorPower`
(`PolynomialRepEmbedding.lean:474-567`)

The equivariance conclusion (lines 497-501) is:

```
φ (ρ g x) i = PiTensorProduct.map (fun _ => Matrix.toLin' g) (φ x i)
```

Direction: `ρ g` on `M` corresponds to `PiTensorProduct.map
g.toLin'` pointwise on each of the `m` coordinates of the target.
This is the standard way GL_N acts on `(V^⊗n)^m` coordinate-wise,
so #2482's step 1 (embed `M` into `(V^⊗n)^m`) consumes this as
a morphism of `GL_N`-reps. ✓

No contravariant flip, no action-direction mismatch. Matches what
Theorem 5.18.4's decomposition of `V^⊗n` expects.

---

## R2 — `hP_mul` semantic load: **PASS**

The hypothesis (`PolynomialRepEmbedding.lean:488-494`) states:

```
polyRightTransl g (P a c') = ∑ c, eval_g (P c c') • P a c
```

**Derivation from `ρ.map_mul` + `hP` + `[Infinite k]`:**

Evaluation-level identity (holds for every `h ∈ GL_N`):

1. `eval_h (polyRightTransl g (X_{ij})) = eval_h (∑_l X_{i,l} · C(g_{l,j}))
   = ∑_l h_{i,l} · g_{l,j} = (h·g)_{i,j} = eval_{h·g}(X_{ij})`.
   So `eval_h ∘ polyRightTransl g = eval_{h·g}` as ring
   homomorphisms on generators, hence on all polynomials.
2. `eval_{h·g}(P a c') = b.coord_a (ρ(h·g)(b c'))` (by `hP`).
3. By `ρ.map_mul`: `ρ(h·g) = ρ(h) ∘ ρ(g)`, so `ρ(h·g)(b c') =
   ρ(h)(ρ(g)(b c')) = ρ(h)(∑_c eval_g(P c c') · b c) = ∑_c
   eval_g(P c c') · ρ(h)(b c)`.
4. Taking `b.coord_a`: `eval_{h·g}(P a c') = ∑_c eval_g(P c c') ·
   eval_h(P a c) = eval_h(∑_c eval_g(P c c') • P a c)`.

So `eval_h(polyRightTransl g (P a c')) = eval_h(Σ_c eval_g(P c c') • P a c)`
for every `h ∈ GL_N(k)`.

**Polynomial-level lift:** The set `{h : det h ≠ 0}` is
Zariski-dense in `k^{N²}` when `k` is infinite (`det` is a nonzero
polynomial, so `{det = 0}` is nowhere-dense). Two polynomials that
agree on a Zariski-dense subset must be equal. `CharZero k` gives
`Infinite k`. This is the `MvPolynomial.funext` + detPoly trick
called out in the docstring at lines 456-473. ✓

**Cross-reference with #2545**: the follow-up issue correctly
scopes this derivation: it identifies the need for an
`MvPolynomial.funext`-style lemma over `[Infinite k]`, and flags
the detPoly-as-witness trick. Scope matches what's actually
needed. No extra content smuggled in.

The hypothesis is **not** stronger than claimed — it is precisely
what the evaluation-level identity lifts to once we invoke
density, and the docstring is an accurate sketch of the
derivation. Semantic load is honest.

---

## R3 — Simp/ext proofs: **PASS**

The only significant `suffices` + `TensorProduct.ext'` + `simp`
reduction is `splitDualBasis_tgtGLAction`
(`PolynomialRepEmbedding.lean:288-309`).

### Does the `suffices` weaken the claim? No.

Original goal (line 289-292):

```
splitDualBasis (tgtGLAction g z) j =
  PiTensorProduct.map (fun _ => g.toLin') (splitDualBasis z j)
```

`suffices h` upgrades this to the universal LinearMap equality

```
(proj_j ∘ splitDualBasis ∘ tgtGLAction g) =
  PiTensorProduct.map (...) ∘ (proj_j ∘ splitDualBasis)
```

as maps on `PolyTensorTgt` (i.e. for all `z`). Applying `h` at the
specific `z` via `congrArg (·z)` (+ `simpa`) recovers the original
goal exactly. The suffices **strengthens** to a universal form,
rather than weakening — no silent reduction of the claim.

### Does `TensorProduct.ext'` + the simp set close the goal correctly?

On elementary tensors `u ⊗ v`:
- LHS: `splitDualBasis ((g^⊗n) u ⊗ v) j = bDual.equivFun(v)(j) •
  (g^⊗n) u` (by `LinearEquiv.lTensor_tmul` +
  `TensorProduct.piScalarRightHom_tmul`).
- RHS: `PiTensorProduct.map (fun _ => g.toLin')
  (bDual.equivFun(v)(j) • u) = bDual.equivFun(v)(j) • (g^⊗n) u`
  (by `map_smul`).

Match. The `simp only` lemma list (lines 306-309) contains
`TensorProduct.piScalarRight_apply`,
`TensorProduct.piScalarRightHom_tmul`, `LinearEquiv.lTensor_tmul`,
and `map_smul` — exactly the lemmas needed. No ad-hoc `suffices`
introduces a weaker claim. ✓

Other uses of simp/ext in the PRs (`tgtGLAction_seqTensor`,
`tgtGLAction_symTensor`) also unpack to index-level identities
that pattern-match the `polyRightTransl` side — already addressed
under R1.

---

## R4 — Reindex choice: **PASS**

The injection-only theorem (`polynomialRep_embeds_in_tensorPower_inj`,
line 225) uses `LinearEquiv.piCongrLeft`; the full equivariant
theorem (`polynomialRep_embeds_in_tensorPower`, line 510) uses
`LinearEquiv.funCongrLeft k X e.symm`.

### Why the switch?

`funCongrLeft` has an unfolding lemma
`(funCongrLeft k X e.symm f)(i) = f(e.symm i)` that is immediate,
whereas `piCongrLeft` requires an `Eq.mpr`/type-cast dance through
the dependent function. The equivariance proof
(`polynomialRep_embeds_in_tensorPower` lines 560-567) needs to
rewrite the goal at a concrete index `i : Fin m` via `change`, so
the simpler unfolding of `funCongrLeft` is the right tool.

### Is this a silent change of action?

Both `piCongrLeft` and `funCongrLeft` are *reindexing*
equivalences — they shuffle coordinates of a Pi type along a
bijection of the index set, without touching the values. The
GL_N action `PiTensorProduct.map g.toLin'` on each coordinate
commutes with coordinate reindexing (it is pointwise). So both
reindexings are GL_N-equivariant: `reindex (g · f) = g · reindex
f`.

The equivariance proof uses this commutation implicitly, via
`change polyTensorBundle ... (e.symm i) = PiTensorProduct.map ...
(polyTensorBundle ... (e.symm i))`, where the `change` pulls both
sides through the reindex. This is sound. ✓

---

## R5 — Unused / redundant imports and hypotheses: **Minor cleanups (non-blocking)**

### Unused hypotheses

Two underscore-prefixed hypotheses `_halg : IsAlgebraicRepresentation
N ρ` in `polynomialRep_embeds_in_tensorPower_inj` (line 205) and
`polynomialRep_embeds_in_tensorPower` (line 478) are intentionally
unused by the proof. The concrete content of algebraicity is
already captured by the `hpoly` existential; `_halg` is purely
documentary. **Could be dropped** without loss, but keeping it is
a reasonable style choice for signaling intended usage. Not
blocking — matches the convention from
`polynomialRep_embeds_in_tensorPower_inj` that was already merged
in PR #2528.

### Unused `with` bindings

In `matrixCoeffPoly_polyRightTransl`
(`PolynomialRepEmbedding.lean:335-339`):

```
set eg : ... := PolynomialTensorBridge.polyRightTransl ... with hegd
set eval_g : ... := fun p => MvPolynomial.eval ... with hevalg
```

`hegd` and `hevalg` are never referenced (verified by grep). The
`set ... with` pattern introduces these bindings gratuitously. A
plain `let` or bare `set` would be cleaner. Not blocking — pure
slop flag, one-line cleanup.

### Imports

Both files use `import Mathlib` (maximal import). No targeted
imports to trim at this granularity — the project-wide convention
is fine for these files.

### Typeclass use

- `[CharZero k]` is used transitively through
  `polyTensorRow` → `homogeneousPolyToTensor` (the symmetrizer
  factor `(n! : k)⁻¹` needs `n! ≠ 0`). ✓
- `[Module.Finite k M]` is used implicitly via the basis
  `(Fin d)`-indexing. ✓
- `[Field k]` is used throughout. ✓

No unused typeclasses identified.

---

## R6 — Downstream usability: **PASS (with an expected caveat)**

The exposed signature (`PolynomialRepEmbedding.lean:474-501`)
delivers:

```
∃ (m : ℕ) (φ : M →ₗ[k] (Fin m → TensorPower k V n)),
  Function.Injective φ ∧
  (∀ g x i, φ (ρ g x) i = PiTensorProduct.map (g^⊗n) (φ x i))
```

### Matches #2482 step 1?

#2482's proof outline (§5 Step E, step 1): *"Embed M into (V^⊗n)^m
using #2478 (polynomialRep_embeds_in_tensorPower) for some m."*

- `φ : M →ₗ[k] (Fin m → V^⊗n)` — matches. ✓
- `Function.Injective φ` — matches. ✓
- Equivariance with `g ↦ g^⊗n` on each coordinate of `(V^⊗n)^m`
  — matches what `Theorem5_18_4_decomposition` expects of `V^⊗n`
  as a GL_N-rep. ✓

### Caveat: `hP_mul` hypothesis must be discharged at the call site

To cite the full equivariant theorem, #2482 needs to construct the
`hpoly` witness, which now includes the polynomial-level
multiplicativity identity as a third conjunct. This is the
content of #2545 — when #2545 lands as a local lemma (or a bundled
`IsAlgebraicRepresentation → hpoly` helper), #2482 plugs it in
trivially. In the interim, #2482 can either derive `hP_mul`
inline or block on #2545.

This is expected (called out in the docstring at lines 456-473 and
the issue body) — not a defect of the equivariance layer.

### Impedance mismatch?

None found. The `(Fin n → Fin N)` fibre of the target is indexed by
the `Fin (N^n)` Cartesian enumeration, reindexed to `Fin m` via
`e : Fin d × (Fin n → Fin N) ≃ Fin m`. The action is pointwise on
each `Fin m` coordinate, which is exactly the shape `Theorem 5.18.4`
feeds through as `V^⊗n ⊕ V^⊗n ⊕ ⋯` (one copy per coordinate).

---

## Summary — all checks PASS

| Focus | Result | Notes |
|-------|--------|-------|
| R1 statement correctness | PASS | Actions compose same direction; monomial expansion matches on both sides. |
| R2 `hP_mul` semantic load | PASS | Derivable from `ρ.map_mul + hP + [CharZero k]`; #2545 correctly scopes the deferred derivation. |
| R3 simp/ext proofs | PASS | `splitDualBasis_tgtGLAction`'s `suffices` strengthens, not weakens; simp set is tight. |
| R4 reindex choice | PASS | `funCongrLeft` vs `piCongrLeft` is an API choice for unfolding ease; both are reindexings, both equivariant for pointwise actions. |
| R5 unused hypotheses | Minor cleanups | `_halg` documentary (keep or drop); `hegd`/`hevalg` unused (one-line drop). Non-blocking. |
| R6 downstream usability | PASS | Signature matches #2482 step 1; only caveat is discharging `hP_mul` at the call site (#2545). |

**No correctness defects found. No CONCERN or FAIL findings. No
follow-up issues needed.** The minor R5 cleanups (drop
unused `hegd`/`hevalg`) are too small to warrant a dedicated
issue; can be picked up opportunistically.

## File-size observation

- `PolynomialTensorBridge.lean`: 677 lines (was ~291 pre-PR #2502 +
  #2528 + #2538; now extended with the equivariance layer).
- `PolynomialRepEmbedding.lean`: 571 lines (was ~290 pre-PR #2539;
  doubled in size for the equivariance).

Both cross the 500-line soft threshold but remain well under the
1000-line hard cap. Content is cohesive (a single theorem chain
per file). No split recommended at this wave — revisit if future
work (e.g. #2545's hP_mul derivation) pushes either past ~800
lines.
