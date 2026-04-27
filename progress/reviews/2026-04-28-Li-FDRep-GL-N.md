# Schur-Weyl L_i FDRep GL_N audit — PR #2504

**Issue**: #2560 (review).
**Session**: `156dbd0c` (2026-04-28).
**Scope**: audit the Schur-Weyl L_i → FDRep GL_N infrastructure that
landed in PR #2504 (single commit `330d99d`, +233 lines, closed #2491).

PR #2504 introduces three artifacts:
- `centralizerModuleHom_smulCommClass` (new global instance,
  `Chapter5/Theorem5_18_1.lean:467-478`).
- Extended signature of `Theorem5_18_1_bimodule_decomposition`
  (`Chapter5/Theorem5_18_1.lean:539-669`) — adds `∀ i, SMulCommClass B
  k (L i)` and `∀ i, Module.Finite k (L i)` to the existential output.
- New `Theorem5_18_4_GL_rep_decomposition`
  (`Chapter5/Theorem5_18_4.lean:496-585`) — bundles each `Lᵢ` as a
  `FDRep k (GL_N k)` via `glHom : GL_N → centralizer(symGroupImage)`
  composed with `Module.toModuleEnd k Lᵢ`.

Both files build clean, no sorries introduced.

---

## Q1 — `centralizerModuleHom_smulCommClass`: **PASS**

Definition (`Theorem5_18_1.lean:468-478`):
```lean
instance centralizerModuleHom_smulCommClass
    {A : Subalgebra k (Module.End k E)}
    {V : Type*} [AddCommGroup V] [Module k V]
    [Module A V] [IsScalarTower k A V] :
    SMulCommClass (↥(Subalgebra.centralizer k (A : Set (Module.End k E)))) k
      (V →ₗ[A] E) where
  smul_comm b c f := by
    refine LinearMap.ext fun v => ?_
    show b.val ((c • f) v) = c • b.val (f v)
    rw [LinearMap.smul_apply, map_smul]
```

**Proof correctness**: ✓
- `(b • c • f) v` reduces by the `centralizerModuleHom`
  (`Theorem5_18_1.lean:427-461`) `smul` definition to
  `b.val ((c • f) v)` (post-composition by `b.val`).
- `(c • b • f) v = c • ((b • f) v) = c • b.val (f v)` by
  `LinearMap.smul_apply` + the same `centralizerModuleHom` definition.
- The `show` step normalizes both sides to the form
  `b.val ((c • f) v) = c • b.val (f v)` (defeq).
- `rw [LinearMap.smul_apply]` rewrites `(c • f) v` to `c • f v`.
- `rw [map_smul]` applies `b.val.map_smul` (since
  `b.val : Module.End k E` is `k`-linear), closing the goal.

**Diamond risk**: ✓ none.
- Mathlib has no instance `SMulCommClass S k (V →ₗ[A] E)` for
  `S = Subalgebra.centralizer …` — the `Module B (V →ₗ[A] E)`
  structure itself is custom (`centralizerModuleHom`, post-composition
  by `b.val`, not derived from any standard mechanism). Mathlib's
  generic `LinearMap.smulCommClass` derivations require the second
  scalar to act on the codomain via a `SMul` that already commutes;
  here the centralizer "scalar" is *post-composition by an
  endomorphism*, not a base-ring action, so Mathlib's automation does
  not reach this instance.
- `grep` over the project confirms exactly one declaration site.

**Heartbeat bumps**: `maxHeartbeats 400000` and
`synthInstance.maxHeartbeats 400000`. The proof body is four lines.
The surrounding `centralizerModuleHom` (`Theorem5_18_1.lean:424-461`)
uses only `synthInstance.maxHeartbeats 400000`. The new
`maxHeartbeats 400000` likely guards against the `Subalgebra → Ring →
Module.End` synthesis chain on the way to elaborating
`b.val ((c • f) v) = c • b.val (f v)`. Empirical reduction is
plausible but **low-priority hygiene** (filed as F5 below).

**Acceptance**: instance proves the displayed `SMulCommClass` with
no defeq drift, no diamond risk.

---

## Q2 — Extended signature of `Theorem5_18_1_bimodule_decomposition`: **PASS**

The new clauses
```lean
(_ : ∀ i, SMulCommClass
      (↥(Subalgebra.centralizer k (A : Set (Module.End k E))))
      k (L i))
(_ : ∀ i, Module.Finite k (L i))
```
are discharged by `inferInstance` in the `refine` block
(`Theorem5_18_1.lean:606-615`).

**SMulCommClass clauses**: ✓ inferable from the new
`centralizerModuleHom_smulCommClass` instance (Q1).

**Module.Finite k (L i) chain**: ✓
- New helper hypothesis 1 (line 595-597):
  ```lean
  haveI : ∀ c, Module.Finite k ↥(V' c) := fun c =>
    Module.Finite.of_injective ((V' c).subtype.restrictScalars k)
      Subtype.val_injective
  ```
  - `(V' c).subtype : V' c →ₗ[A] E` (subspace inclusion).
  - `.restrictScalars k : V' c →ₗ[k] E` — k-linear restriction.
  - Injectivity = `Subtype.val_injective` (the underlying function is
    the inclusion, which is injective).
  - With `Module.Finite k E` (the file-level hypothesis on `E`),
    `Module.Finite.of_injective` yields `Module.Finite k (V' c)`.
- New helper hypothesis 2 (line 598-605):
  ```lean
  haveI : ∀ c, Module.Finite k ((↥(V' c) : Type v) →ₗ[A] E) := fun c => by
    haveI : Module.Finite k ((↥(V' c) : Type v) →ₗ[k] E) := inferInstance
    exact Module.Finite.of_injective
      (LinearMap.restrictScalarsₗ k A (↥(V' c)) E k)
      (LinearMap.restrictScalars_injective _)
  ```
  - `restrictScalarsₗ` direction: from
    `Mathlib/Algebra/Module/LinearMap/Defs.lean:993`,
    `restrictScalarsₗ : (M →ₗ[S] N) →ₗ[R₁] M →ₗ[R] N` — so applying
    `LinearMap.restrictScalarsₗ k A (V' c) E k` produces
    `(V' c →ₗ[A] E) →ₗ[k] (V' c →ₗ[k] E)`. ✓ correct direction
    (A-linear → k-linear).
  - `LinearMap.restrictScalars_injective`
    (`Mathlib/Algebra/Module/LinearMap/Defs.lean:442`) gives the
    underlying-function injectivity, which matches
    `restrictScalarsₗ.toFun = restrictScalars` definitionally. ✓
  - `Module.Finite k ((V' c) →ₗ[k] E)` follows by `inferInstance`
    from `Module.Finite k (V' c)` + `Module.Finite k E`.

**Heartbeat bumps**: `maxHeartbeats 1600000 → 3200000` (2x),
`synthInstance.maxHeartbeats 800000 → 1600000` (2x). Comment
attached. Adding two universe-polymorphic `∀ i` clauses to a 13-clause
existential, each triggering a `Subalgebra → Ring → Module.End` chain,
plausibly justifies the bump. Empirically tightening the bumps is a
**low-priority hygiene** task (F5 below) — not worth blocking on.

**Acceptance**: extended existential output is consistent with the
proof body (no missing/spurious binders), all `inferInstance`
discharges land cleanly.

---

## Q3 — `Theorem5_18_4_GL_rep_decomposition`: **PASS**

### `glHom : GL_N → centralizer(symGroupImage)`
(`Theorem5_18_4.lean:546-573`)

`g ↦ PiTensorProduct.map (fun _ => Matrix.mulVecLin g.val)`.

**Membership claim**: After `rw [h_eq]`, the goal becomes membership
in `diagonalActionImage k V n`.
- `diagonalActionImage = Algebra.adjoin k (Set.range fun f =>
  PiTensorProduct.map (fun _ => f))` (`Theorem5_18_4.lean:70-73`).
- `PiTensorProduct.map (fun _ => mulVecLin g.val)` is exactly the
  generator with `f = mulVecLin g.val`, hence in `Algebra.subset_adjoin`.
- ✓ proof is correct.

**`map_one'`**: `mulVecLin (1 : Matrix _ _ k) = LinearMap.id` is
`Matrix.mulVecLin_one`. After `funext + rw + PiTensorProduct.map_id`,
the goal closes by `rfl`. ✓

**`map_mul'`**: `mulVecLin (g₁ * g₂) = (mulVecLin g₁).comp (mulVecLin
g₂)` is `Matrix.mulVecLin_mul`. Verified via
`Mathlib/LinearAlgebra/PiTensorProduct.lean:502`:
```
theorem map_comp : map (fun i => g i ∘ₗ f i) = map g ∘ₗ map f
```
matches the direction the proof relies on. After
`rw [this, PiTensorProduct.map_comp]`, the goal reduces to
`map(g₁) ∘ₗ map(g₂) = map(g₁) * map(g₂)` which is `rfl` in
`End k (TensorPower k V n)` (composition = multiplication). ✓

### `ρ i : GL_N → End k (L' i)`
(`Theorem5_18_4.lean:575-580`)

`(Module.toModuleEnd k (L' i) (S := centralizer)).toMonoidHom.comp
glHom`.

- `Module.toModuleEnd : S →+* End R M` requires `Semiring S`,
  `Module S M`, `SMulCommClass S R M`
  (`Mathlib/Algebra/Module/LinearMap/End.lean:268-273`). All three are
  in scope: `centralizer` is a Subalgebra (hence Semiring), `Module
  centralizer (L' i)` from `hL'_Bmod`, `SMulCommClass centralizer k
  (L' i)` from the new `hL'_smul` clause (Q2). ✓
- The wiring `Q1 → Q2 → Q3` goes through cleanly.

### `FDRep.of (ρ i)` finiteness
(`Theorem5_18_4.lean:582-583`)

`FDRep.of` requires `Module.Finite k (L' i)`
(`Mathlib/RepresentationTheory/FDRep.lean:136`). Provided by `hL'_fin`
(Q2). ✓

### Existential output

The output exposes `S i` (simple `symGroupImage`-modules) and
`L i : FDRep k (GL_N k)` separately, with the iso
`TensorPower k V n ≃ₗ[k] DirectSum ι (S i ⊗[k] (L i : Type u))`
**only `k`-linear** (no GL_N-equivariance claim). The `(L i : Type u)`
ascription works because `FDRep` has `CoeSort (FDRep R G) (Type u)`
(`FDRep.lean:81`), and `FGModuleCat.of_carrier` makes
`(FDRep.of (ρ i) : Type u) = L' i` definitionally
(`Mathlib/Algebra/Category/FGModuleCat/Basic.lean:109-110`,
`of_carrier : of R V = V := rfl`). So the original opaque `e` from
`Theorem5_18_1_bimodule_decomposition` is reused as-is via `⟨e⟩`
without any retyping.

**Acceptance**: the existential is constructible with the data shown.
No GL_N-equivariance is proved or claimed in the theorem statement
itself.

---

## Q4 — Downstream usability for #2540 / #2493: **DEFECT (planning)**

### Signature mismatch with `glTensorRep_equivariant_schurWeyl_decomposition`
(`FormalCharacterIso.lean:758-774`, issue #2540, claimed)

The downstream `glTensorRep_equivariant_schurWeyl_decomposition`
existential (line 760-773) requires:
```lean
∃ (ι) ... (S : ι → Type u) ... (_ : ∀ i, Module.Finite k (S i))
       (L : ι → FDRep k GL_N),
  ∃ (e : TensorPower k V n ≃ₗ[k] DirectSum ι (S i ⊗ (L i))),
    ∀ g v, e (glTensorRep k N n g v) = ... e v ...
```

PR #2504's `Theorem5_18_4_GL_rep_decomposition` produces:
```lean
∃ (ι) ... (S) ... (_ : Module symGroupImage S i) (_ : IsSimpleModule …)
       (_ : pairwise_distinct) (L : ι → FDRep k GL_N),
  Nonempty (TensorPower k V n ≃ₗ[k] DirectSum ι (S i ⊗ (L i)))
```

Two mismatches:

1. **`Module.Finite k (S i)` not propagated.** The PR's body has
   `Module.Finite k ↥(V' c)` (line 595-597) but the existential
   output only carries `AddCommGroup + Module k + Module symGroupImage
   + IsSimpleModule`. The downstream worker would have to either
   (a) re-derive `Module.Finite k (S i)` from
   `IsSimpleModule symGroupImage (S i)` + finite-dim symGroupImage —
   which requires a Mathlib lemma that simple modules over a
   finite-dim k-algebra are k-finite (not currently in Mathlib for
   this exact signature), or (b) extend the existential. **(b) is
   strictly cleaner.** Filed as F4.

2. **`Nonempty (≃ₗ)` vs explicit `e`.** This is the more substantive
   gap. The downstream worker for #2540 must prove
   `e (glTensorRep g v) = (RHS-action g (e v))` for all `g, v`. To do
   this they need a *specific* `e` whose action on pure tensors is
   computable — i.e., the evaluation form
   `e.symm (of i (v ⊗ l)) = l v` from
   `Theorem5_18_1_bimodule_decomposition_explicit`
   (`Theorem5_18_1.lean:693`-end). The PR's
   `Theorem5_18_4_GL_rep_decomposition` is built on
   `Theorem5_18_1_bimodule_decomposition` (not `_explicit`), so the
   `e` it returns is opaque. The downstream worker effectively
   **bypasses this PR** and reconstructs the FDRep bundling on top of
   `Theorem5_18_4_bimodule_decomposition_explicit` themselves. The
   PR's `Theorem5_18_4_GL_rep_decomposition` becomes dead code as far
   as the equivariance chain is concerned. Filed as F3.

### #2493 (final assembly, blocked on #2540)

#2493 consumes the GL_N-equivariant version produced by #2540 (Step
1: "apply `Theorem5_18_4_GL_rep_decomposition` to get `V^⊗n ≅ ⨁ S i ⊗
L i` with L i : FDRep k GL_N"). Once #2540 produces a usable
equivariant version — likely as `_GL_rep_decomposition_explicit` or
similar — #2493's Step 1 has its input. No other signature concerns
specific to #2493.

### `[CharZero k]` hypothesis on `Theorem5_18_4_GL_rep_decomposition`

Traced: `[CharZero k]` is needed via `symGroupImage_isSemisimpleRing
k V n` (`Theorem5_18_4.lean:166-174`) which uses Maschke's theorem in
char 0 (`NeZero ((n!) : k)`). Then `Theorem5_18_1_bimodule_decomposition`
needs `IsSemisimpleRing A` for `A = symGroupImage`. Also
`Theorem5_18_4_centralizers k V n hN'` carries `[CharZero k]`
(`Theorem5_18_4.lean:268-269`). So `[CharZero k]` is genuinely
needed; not a spurious hypothesis.

### No spurious `Module.Free k V` hypothesis blocking specialization

The specialization to `V = Fin N → k` is clean. `Module.Finite k V`
follows by `inferInstance` (`Pi → Fin N → k`).

**Acceptance**: signature of (3) is **partially incompatible** with
#2540's downstream consumer — would require a `_explicit` analogue
to be useful. F3 (planning, medium-priority) and F4 (Module.Finite k S
i, low-priority) capture the gap.

---

## Q5 — Doc-string honesty: **PASS-with-followups**

### `Theorem5_18_4_GL_rep_decomposition` doc-string
(`Theorem5_18_4.lean:496-509`)

Two minor issues:

1. **"...each `Lᵢ` is a full finite-dimensional `GL_N(k)`-representation
   (an irreducible polynomial representation)."** The theorem
   constructs the FDRep structure but does **not** prove
   irreducibility (`IsSimpleModule k (L i)` or analogous over GL_N).
   The doc-string should describe what's proved, not what's
   mathematically true. Filed as F1 (doc-string overclaim).

2. **"The `GL_N` action is built by composing `GL_N →
   diagonalActionImage`..."** The proof actually composes
   `GL_N → centralizer(symGroupImage)` and uses the centralizer
   identity `centralizer = diagonalActionImage` (h_eq) to discharge
   membership. The end-result action is the same, but the literal
   construction goes through the centralizer. Minor, possibly
   confusing for a reader trying to follow the proof from the
   doc-string. (Folded into F1.)

### `Theorem5_18_1_bimodule_decomposition` doc-string
(`Theorem5_18_1.lean:539-551`)

The doc-string describes the decomposition `E ≅ ⨁ Vᵢ ⊗ Lᵢ` and notes
that `Lᵢ` are genuine `B`-modules (not just k-vector spaces). The PR
**adds two new existential clauses** (`SMulCommClass` and
`Module.Finite k (L i)`), but the doc-string was not updated to
mention them. A reader looking at the doc-string would not learn that
the theorem now provides finiteness or the SMulCommClass. Filed as F2
(doc-string staleness).

### Cross-references

The PR file does not embed `#2491` cross-references in the doc-string
(those live in the PR description / commit message). ✓

---

## Q6 — Heartbeat-budget cleanliness: **PASS-with-followups**

| Declaration | maxHeartbeats | synthInstance.maxHeartbeats |
|-------------|---------------|----------------------------|
| `centralizerModuleHom_smulCommClass` (new) | 400000 | 400000 |
| `Theorem5_18_1_bimodule_decomposition` (modified) | 1600000 → 3200000 | 800000 → 1600000 |
| `Theorem5_18_4_GL_rep_decomposition` (new) | 3200000 | 1600000 |

- `centralizerModuleHom_smulCommClass`'s `maxHeartbeats 400000` is the
  most likely candidate for empirical reduction (4-line proof). Filed
  as F5 (low-priority).
- `Theorem5_18_1_bimodule_decomposition`'s 2x-bump rationale is
  documented in an inline comment (`Theorem5_18_1.lean:533-536`) —
  "universe-polymorphic ∀-binders … deep `Subalgebra → Ring →
  Module.End` instance chain." Adding two clauses to a 13-clause
  existential plausibly justifies a doubling, though a tighter bump
  (1.5x) might suffice.
- `Theorem5_18_4_GL_rep_decomposition`'s 3200000/1600000 matches the
  upstream (`Theorem5_18_1_bimodule_decomposition`) and accounts for
  the additional `glHom` / `ρ` monoid-hom compositions, each
  triggering its own `Subalgebra → Ring → Module.End` synthesis.
  Reasonable.

No `decide` / `omega` calls in the new code that would be brittle
under future Mathlib bumps. ✓

---

## Findings

| ID | Severity | Issue | Description |
|----|----------|-------|-------------|
| F1 | low | #2570 | Doc-string overclaim in `Theorem5_18_4_GL_rep_decomposition`: "irreducible polynomial representation" not proven; "`GL_N → diagonalActionImage`" elides the centralizer-identity step. |
| F2 | low | #2571 | `Theorem5_18_1_bimodule_decomposition` doc-string out of sync with the new `SMulCommClass` and `Module.Finite k (L i)` existential clauses. |
| F3 | medium | #2572 | `Theorem5_18_4_GL_rep_decomposition` returns `Nonempty (≃ₗ)` (opaque). Downstream issue #2540 (claimed) needs an explicit `e` for the equivariance proof — likely an `_explicit` analogue using `Theorem5_18_4_bimodule_decomposition_explicit` as the base. |
| F4 | low | #2573 | `Module.Finite k (S i)` not propagated into the existential output of `Theorem5_18_4_GL_rep_decomposition`. Downstream #2540 requires it. |
| F5 | low | #2574 | `centralizerModuleHom_smulCommClass`'s `maxHeartbeats 400000` (and possibly `synthInstance.maxHeartbeats 400000`) may be reducible. `Theorem5_18_1_bimodule_decomposition`'s 2x bump (1.6M → 3.2M, 0.8M → 1.6M) may be empirically tightenable. |

---

## Verdict: **PASS-with-followups**

The PR closes #2491 ("part A: endow bimodule L_i with FDRep GL_N
structure") cleanly. All three artifacts are mathematically correct
and their proofs hold under audit. The five findings are either
cosmetic (F1, F2, F5) or planning-level usability gaps (F3, F4) that
do not invalidate the PR's content.

The most actionable follow-up is **F3**: the downstream consumer
(#2540, claimed) cannot use `Theorem5_18_4_GL_rep_decomposition`
directly to prove GL_N-equivariance because the iso is opaque — an
`_explicit` analogue is required. Filing F3 now ensures the in-flight
worker sees the recommendation.

No correctness blocker. No code changes proposed in this audit's PR
(review-only, per protocol).
