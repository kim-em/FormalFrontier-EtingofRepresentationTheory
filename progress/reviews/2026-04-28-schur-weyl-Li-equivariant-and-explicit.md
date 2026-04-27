# Schur-Weyl L_i critical-path audit — PRs #2578 + #2579

**Issue**: #2592 (review).
**Session**: `ace60dfc` (2026-04-28).
**Scope**: audit the two un-audited links of the Schur-Weyl L_i critical
path that landed 2026-04-27.

| PR | Theorem | Closes | Lines | Merge |
|----|---------|--------|-------|-------|
| #2578 | `glTensorRep_equivariant_schurWeyl_decomposition` (`Chapter5/FormalCharacterIso.lean`) | #2540 | +171/-3 | 0cc1dc7 |
| #2579 | `Theorem5_18_4_GL_rep_decomposition_explicit` (`Chapter5/Theorem5_18_4.lean`) | #2572 | +165/0 | 6d43568 |

Both PRs are on the L_i critical path. PR #2578 closes a definition-level
sorry (the equivariance anchor) and PR #2579 introduces a re-usable
explicit form bundling `S i : Submodule`, `L_carrier i`, evaluation
formula and (after PR #2599's extension) the action formula.

> **Important context for this audit**: PR #2599 (`refactor(Ch5 #2589):
> consume Theorem5_18_4_GL_rep_decomposition_explicit in
> glTensorRep_equivariant_schurWeyl_decomposition`, merge commit
> `80b425c`, 2026-04-28) landed *between* PRs #2578/#2579 and this
> audit. It refactored the consumer in #2578 to delegate to the
> producer in #2579 and added an action-formula clause to
> `Theorem5_18_4_GL_rep_decomposition_explicit`.
>
> Where the audit examines current code, it audits the post-#2599
> state. Where it examines the originally-merged PR diff, that is
> stated explicitly. The audit verdicts apply to both the original
> form and the post-#2599 form unless noted otherwise.

`grep -n sorry` returns no hits in the audited regions of either file
(confirmed for `Chapter5/FormalCharacterIso.lean:740-848` and
`Chapter5/Theorem5_18_4.lean:593-770`).

---

## PR #2578 — equivariant Schur-Weyl decomposition

### Q1 — `glHom : GL_N → centralizer(symGroupImage)`: **PASS**

Original `Chapter5/FormalCharacterIso.lean:783-815` (post-#2599 the
`glHom` construction was hoisted into `Theorem5_18_4_GL_rep_decomposition_explicit`).

```
toFun := fun g => ⟨PiTensorProduct.map
    (fun _ : Fin n => Matrix.mulVecLin (R := k) g.val), by
  rw [h_eq]
  exact Algebra.subset_adjoin ⟨Matrix.mulVecLin g.val, rfl⟩⟩
```

Underlying linear map: `g ↦ PiTensorProduct.map (fun _ ↦ mulVecLin g)`,
which is exactly `glTensorRep k N n g` per `Chapter5/Theorem5_22_1.lean:217-220`.
This is `g^{⊗n}` on tensor factors. ✓

Membership in centralizer: the rewrite `h_eq : centralizer(symGroupImage) =
diagonalActionImage` (from `(Theorem5_18_4_centralizers k V n hN').2.symm`)
reduces the obligation to membership in `diagonalActionImage`. By
definition (`Theorem5_18_4.lean:70-73`), `diagonalActionImage` is
`Algebra.adjoin k (Set.range (fun f : Module.End k V ↦ PiTensorProduct.map
(fun _ ↦ f)))`, so `Algebra.subset_adjoin ⟨Matrix.mulVecLin g.val, rfl⟩`
discharges membership. ✓

`map_one'`: reduces `PiTensorProduct.map (fun _ ↦ mulVecLin 1) = 1` via
`Matrix.mulVecLin_one` and `PiTensorProduct.map_id`. Same pattern as the
existing `glTensorRep.map_one'` (Theorem5_22_1.lean:221-228). ✓

`map_mul'`: reduces via `Matrix.mulVecLin_mul` and `PiTensorProduct.map_comp`.
Same pattern as `glTensorRep.map_mul'`. ✓

The duplication with `glTensorRep` is real and acknowledged in the
PR's progress note ("duplicates glTensorRep's monoid-hom"); see F2
below for follow-up. The hoist into `_explicit` (PR #2579) carried the
duplication forward; PR #2599 then dropped the second copy in
`FormalCharacterIso.lean`, so the `glHom` construction now exists in
exactly one place (`Theorem5_18_4.lean:675-702`).

### Q2 — `ρ i` direct construction (avoiding the diamond): **PASS**

`FormalCharacterIso.lean:817-849` (original; now in
`Theorem5_18_4.lean:730-756`):

```
let ρ : ∀ i, GL_N →* Module.End k (↥(V' i) →ₗ[A] E) := fun i =>
{ toFun := fun g =>
  { toFun := fun l => (centralizerToEndA k E A (glHom g)).comp l
    map_add' := … (LinearMap.add_apply, map_add)
    map_smul' := … (LinearMap.smul_apply, RingHom.id_apply,
                    LinearMap.comp_apply, LinearMap.map_smul_of_tower) }
  map_one' := … (rw [map_one (glHom), map_one (centralizerToEndA)]; rfl)
  map_mul' := … (rw [map_mul (glHom), map_mul (centralizerToEndA)]; rfl) }
```

Mathematical content: `(ρ i g) l := (centralizerToEndA (glHom g)).comp l`
is post-composition of an A-linear map by an A-linear endomorphism (the
output of `centralizerToEndA`, which is the canonical embedding
`centralizer(A) → End_A(E)` per `Theorem5_18_1.lean:400-422`). The
result is again A-linear, hence lives in `↥(V' i) →ₗ[A] E`. ✓

Why direct (not via `Module.toModuleEnd ∘ glHom`): the canonical path
would compose `glHom : GL_N → centralizer(A)` with the implicit
`Module ↥(centralizer A) (V →ₗ[A] E)` instance from
`centralizerModuleHom` (`Theorem5_18_1.lean:427-461`). But after
`Theorem5_18_1_bimodule_decomposition_explicit` the `↥(V' i)`-side
carries `AddCommGroup` via `Submodule.addCommGroup` (Submodule is a
sub-AddCommGroup of an `AddCommGroup E`), while the
`Module ↥(centralizer A) _`-instance derivation re-discovers a
distinct `AddCommGroup` via the `AddSubmonoid → CommMonoid` chain.
Both inhabit `AddCommGroup ↥(V' i)` but are not definitionally equal —
that is the diamond the progress note describes. Building `ρ` directly
sidesteps the synthesis, treating `(centralizerToEndA (glHom g))` as
an explicit `Module.End A E` and post-composing manually. ✓

`map_one'` / `map_mul'`: the proofs use `change` to rewrite the goal
into `(centralizerToEndA (glHom 1)) (l v) = l v` and similarly for
`mul`, then close via `map_one`/`map_mul` propagated through both
ring homs (`glHom` is a `MonoidHom`, `centralizerToEndA` a `RingHom`).
The closing `rfl` works because `(LinearMap.id : End A E).comp l = l`
and the End-`mul` is composition. ✓

The `map_smul'` proof verifies that post-composition is `k`-linear on
the hom-space; `LinearMap.map_smul_of_tower` covers this since the
A-linear map `l` is automatically k-linear via the IsScalarTower
instance established earlier. ✓

### Q3 — `Module.Finite k` derivations: **PASS**

`hSi_fin` (`FormalCharacterIso.lean:797-799` in current file;
`816-818` in original PR):
```
fun i => Module.Finite.of_injective ((V' i).subtype.restrictScalars k)
  Subtype.val_injective
```
Standard pattern: a Submodule of an ambient `Module.Finite k E` is
itself `Module.Finite k`, witnessed by the injective k-linear inclusion
`↥(V' i) →ₗ[k] E`. ✓

`hLi_fin` (PR #2578 original; same in #2579):
```
haveI : Module.Free k (↥(V' i)) := Module.Free.of_divisionRing k _
haveI : Module.Finite k (↥(V' i) →ₗ[k] E) :=
  Module.Finite.linearMap k k (↥(V' i)) (TensorPower k V n)
exact Module.Finite.of_injective
  (LinearMap.restrictScalarsₗ k A (↥(V' i)) (TensorPower k V n) k)
  (LinearMap.restrictScalars_injective _)
```

Verification:
- `Module.Free.of_divisionRing`: `k` is a Field, hence a DivisionRing,
  hence every k-module is Free. ✓
- `Module.Finite.linearMap` (mathlib `LinearAlgebra/FreeModule/Finite/Matrix.lean:47`):
  signature requires `Module.Free R M`, `Module.Finite R M`,
  `Module.Finite S N`. With R = S = k, M = ↥(V' i), N = E: M is
  Free (just established) and Finite (from `hSi_fin`); N is Finite
  (from the ambient `Module.Finite k (TensorPower k V n)`). ✓
- `LinearMap.restrictScalarsₗ k A (↥(V' i)) E k` is the canonical
  k-linear inclusion `(↥(V' i) →ₗ[A] E) ↪ (↥(V' i) →ₗ[k] E)`
  (every A-linear map is k-linear). It is injective on the underlying
  function — `LinearMap.restrictScalars_injective` packages this. ✓

The whole derivation is sound and uses only stable mathlib API. ✓

### Q4 — Equivariance proof: **PASS**

The proof reduces equivariance to one identity on pure tensors:
```
DirectSum.linearMap_ext k fun i =>
  TensorProduct.ext' fun s l => …
```
After the reduction (`FormalCharacterIso.lean:817-836` post-#2599):

LHS chain:
- `e.symm (DirectSum.lof k ι _ i (s ⊗ₜ l))`
- `= e.symm (DirectSum.of _ i (s ⊗ₜ l))` by `DirectSum.lof_eq_of`
- `= (L_carrier i l) s` by the eval clause `he` (post-#2599; in the
  original PR #2578 the corresponding step was `= l s` directly via
  `Theorem5_18_1_bimodule_decomposition_explicit`'s `h_eval`).
- Apply `glTensorRep g` on top.

RHS chain:
- `e.symm` of the directSum action = `e.symm (DirectSum.lmap (fun i ↦
  ((trivial _ ↥(V' i)).tprod (L i).ρ) g) (DirectSum.of _ i (s ⊗ₜ l)))`
- `= e.symm (DirectSum.of _ i (((trivial _).tprod (L i).ρ) g (s ⊗ₜ l)))`
  by `DirectSum.lmap_of`
- `= e.symm (DirectSum.of _ i (s ⊗ₜ ((L i).ρ g l)))`
  by `Representation.tprod_apply` + `TensorProduct.map_tmul`
  + `Representation.trivial_apply` (g acts trivially on s)
- `= (L_carrier i ((L i).ρ g l)) s` by `he i s _`.

Final goal (post-#2599):
`glTensorRep g ((L_carrier i l) s) = (L_carrier i ((L i).ρ g l)) s`
discharged via `(h_act i g l s).symm`.

Original PR #2578's final step closed via `rfl` directly because
`L_carrier` did not exist there — both sides definitionally reduced
to `PiTensorProduct.map (mulVecLin g) (l s)` (since `(ρ i g l) =
(centralizerToEndA (glHom g)).comp l`, evaluating at `s` gives
`(glHom g).val (l s)`). Both routes correctly establish the same
identity. ✓

The post-pure-tensor step that lifts back to the full equivariance
claim:
- `LinearMap.congr_fun h_lin (e v)`
- Substitute `e.symm (e v) = v` via `e.symm_apply_apply`
- Apply `LinearEquiv.eq_symm_apply` to recover `e (glTensorRep g v) =
  ds_act g (e v)`.

Standard `e.symm`-based equivariance bootstrapping. ✓

### Q5 — Heartbeat bump tightness: **PASS-with-followup (F1)**

The bump is `set_option maxHeartbeats 6400000 in` (vs the file default
of 200000). The PR commentary says "kernel whnf timeout during
type-checking the existential output." The accompanying
`synthInstance.maxHeartbeats 1600000` was already in place in the
prior `sorry`-bodied version.

After PR #2599's refactor, the proof body is significantly simpler:
the `glHom` / `ρ` / `Module.Finite k (V →ₗ[A] E)` derivations have
been hoisted into `Theorem5_18_4_GL_rep_decomposition_explicit`. The
new body just `obtain`s from `_explicit`, derives one `Module.Finite k
(↥(S' i))`, and runs the equivariance reduction.

The 6400000 bump may now be unnecessary or could be tightened toward
the 3200000 used on `_GL_rep_decomposition_explicit` itself. This is
the same cleanup pattern as #2574 (which tightened
`Theorem5_18_1.lean` heartbeat bumps after upstream simplifications).

Filed as **F1** below — non-blocking hygiene.

---

## PR #2579 — explicit GL_N decomposition

### Q6 — Signature shape (`S i : Submodule`, `L i : FDRep`, `L_carrier`): **PASS**

`Chapter5/Theorem5_18_4.lean:633-656` (current; the original existential
shape was `∃ … e, ∀ i v l, e.symm (…) = (L_carrier i l) v`, post-#2599
extended to `∃ … e, (∀ i v l, …) ∧ (∀ i g l v, action_formula)`).

- `S i : Submodule (symGroupImage k V n) (TensorPower k V n)` ✓
  (concrete A-submodule, not just a Type).
- `L i : FDRep k (Matrix.GeneralLinearGroup (Fin N) k)` ✓
  (FDRep, not a bare `Module k`).
- `L_carrier i : (L i : Type u) ≃ₗ[k] (↥(S i) →ₗ[A] V^⊗n)` ✓
  (k-linear iso explicitly identifying the bundled FDRep carrier with
  the explicit hom-space). The doc-string accurately notes this is
  `LinearEquiv.refl` after `FGModuleCat.of_carrier := rfl`.

Compared to `Theorem5_18_4_GL_rep_decomposition` (the non-explicit
form), this signature drops the bundled `Module (symGroupImage) (S i)`
clause (subsumed by `S i : Submodule …`) and adds `S i : Submodule`,
`L_carrier`, `e` as concrete data, plus the eval and action formulas.

### Q7 — Eval formula threading via `Theorem5_18_(1|4)_bimodule_decomposition_explicit`: **PASS**

Threading chain:

1. `Theorem5_18_1_bimodule_decomposition_explicit` (`Theorem5_18_1.lean:711-722`)
   exposes the eval clause:
   ```
   ∀ (i : ι) (v : ↥(V i)) (l : ↥(V i) →ₗ[A] E),
     e.symm (DirectSum.of _ i (v ⊗ₜ[k] l)) = l v
   ```
2. `Theorem5_18_4_bimodule_decomposition_explicit` (`Theorem5_18_4.lean:464-480`)
   re-exports this clause verbatim by direct delegation
   (`exact Theorem5_18_1_bimodule_decomposition_explicit k …`).
3. `Theorem5_18_4_GL_rep_decomposition_explicit`'s body (line 666-667)
   `obtain`s `⟨ι, hι, hι_dec, S', hS'_simp, hS'_dist, e, he⟩` from
   step 2. The `he` witness is the eval clause.
4. The final `refine` (line 768) returns
   `⟨ι, hι, hι_dec, S', hS'_simp, hS'_dist, L, L_carrier, e, he, ?_⟩`.
   The `he` is plugged into the eval slot of the new conjunctive
   existential; since `L_carrier i = LinearEquiv.refl k _`, the rewrite
   `(L_carrier i l) v = l v` is `rfl`, so `he` discharges the
   `(L_carrier i l) v` form directly. ✓

The threading is verbatim and free of fragility. ✓

### Q8 — Manual `ρ` construction shape vs PR #2578: **PASS-with-followup (F2)**

The two manual `ρ` constructions in the originally-merged PRs were
character-for-character identical (modulo the per-component carrier
type `↥(V' i)` vs `↥(S' i)`). The progress note for PR #2579
acknowledges this: "I copied #2540's two key technical patterns:
… `ρ i` construction: build each `ρ i` manually as a record …
This bypasses an instance-synthesis diamond …".

After PR #2599 the duplication in `FormalCharacterIso.lean` is gone
(the consumer now uses the `ρ` bundled inside `_explicit`). However,
duplication remains between:

- `Theorem5_18_4_GL_rep_decomposition` (non-explicit; manually
  constructs `glHom` and uses `Module.toModuleEnd ∘ glHom` for `ρ`,
  `Theorem5_18_4.lean:548-589`), and
- `Theorem5_18_4_GL_rep_decomposition_explicit` (manually constructs
  `glHom` and bypasses the diamond with the per-component ρ-record,
  `Theorem5_18_4.lean:675-756`).

These are not identical — the non-explicit form goes via
`Module.toModuleEnd` (which works for it because the bimodule-decomp
without `_explicit` ships the `Module ↥(centralizer) Lᵢ` instance
that triggers the diamond *only* when the `_explicit` chain re-derives
it from a Submodule's `AddCommGroup`). So #2590's planned refactor
("delegate non-explicit to explicit") will inherit the manual record.

Filed as **F2** below — orthogonal to #2590 (#2590 deletes the
duplication; F2 documents that the underlying pattern itself can be
extracted into a helper). Non-blocking.

### Q9 — Mutual recursion on line 654 (per #2590's heads-up): **PASS — concern dismissed**

Issue #2590 flags:
> Heads-up: the current `Theorem5_18_4_GL_rep_decomposition_explicit`
> body (line 654) calls the non-explicit form *internally*. Read that
> body carefully — a naïve refactor will create mutual recursion.

Inspection of the current file (`Theorem5_18_4.lean:633-770`):

- Line 654 is part of the existential **statement**, not the body
  (it is the `((L_carrier i l) v))` line in the eval clause).
- The body (lines 656-770) `obtain`s from
  `Theorem5_18_4_bimodule_decomposition_explicit` (line 666-667) and
  uses only `Theorem5_18_4_centralizers` (line 672) and
  `centralizerToEndA` (lines 734-754). It does **not** reference
  `Theorem5_18_4_GL_rep_decomposition`.

There is no mutual-recursion risk. The "line 654" claim in #2590 is
stale (or the line numbers shifted). Filed as **F3** — needs an
amendment to #2590 so the next worker doesn't waste investigation
time on a non-issue. Non-blocking.

### Q10 — Doc-string accuracy: **PASS**

`Chapter5/Theorem5_18_4.lean:599-632`:

- "Strengthens `Theorem5_18_4_GL_rep_decomposition` by concretizing
  the summand types and producing an explicit iso whose inverse on
  pure tensors is the evaluation map" — accurate.
- "`S i : Submodule (symGroupImage k V n) (V^⊗n)` (Specht-module
  realisations as concrete submodules)" — matches the existential.
- "`L i : FDRep k (GL_N k)` whose carrier is `↥(S i) →ₗ[A] V^⊗n`,
  with the `GL_N`-action given by post-composition with `g ↦ g^{⊗n}`
  (which lies in `centralizer(symGroupImage)` by the centralizer
  identity)" — matches the construction (Q1, Q2). The phrase "the
  centralizer identity" refers to `Theorem5_18_4_centralizers`.
- "a `k`-linear iso `L_carrier i : (L i : Type u) ≃ₗ[k]
  (↥(S i) →ₗ[A] V^⊗n)` identifying the bundled FDRep carrier with
  the explicit hom-space (it is `LinearEquiv.refl` after the
  `FGModuleCat.of_carrier` defeq)" — matches the definition
  `let L_carrier := fun i => LinearEquiv.refl k _` (line 762-764).
- Eval formula: `e.symm (of i (v ⊗ₜ l)) = (L_carrier i l) v` —
  matches the existential clause.
- Action formula: "`(L_carrier i ((L i).ρ g l)) v =
  PiTensorProduct.map (fun _ ↦ mulVecLin g.val) ((L_carrier i l) v)`"
  — matches the second conjunct (added by PR #2599); proof closes
  by `rfl` (line 770), confirming the chain
  `(L i).ρ g l = ρ i g l = (centralizerToEndA (glHom g)).comp l`,
  applied at v gives `(glHom g).val (l v) = PiTensorProduct.map
  (mulVecLin g.val) (l v)`.
- Universe-polymorphic carrier discussion ("when stating the
  existential, `(L i : Type u)` is universally quantified and not
  yet concretised, so an `l : (L i : Type u)` cannot be applied to
  `v` as a linear map without the explicit identification") —
  accurate motivation for `L_carrier`; this is a real defeq trap
  documented elsewhere (e.g. `glTensorRep_equivariant_…`'s pre-#2599
  workaround).

All doc-string claims check out. ✓

---

## Findings

### F1 — Heartbeat bump on `glTensorRep_equivariant_schurWeyl_decomposition` may be tightenable post-#2599 (hygiene)

The `set_option maxHeartbeats 6400000` bump on
`FormalCharacterIso.lean:760` was justified in PR #2578 because the
proof body contained the `glHom` / `ρ` / `Module.Finite` derivations
inline. PR #2599 hoisted those into
`Theorem5_18_4_GL_rep_decomposition_explicit` (heartbeat 3200000); the
consumer body is now a thin reduction (`obtain` + per-component
`Module.Finite k ↥(S' i)` + the equivariance chain).

Worth re-attempting at 3200000 (matching `_explicit`) and bisecting
downward. Same pattern as #2574 (Theorem5_18_1 tightening).

Non-blocking; tracked as a follow-up `feature` issue.

### F2 — Manual `glHom` + `ρ` record-construction pattern can be extracted (refactor)

The pattern
```
let glHom : GL_N →* centralizer(A) := { toFun := fun g ↦ ⟨g^{⊗n}, _⟩,
  map_one' := …, map_mul' := … }
```
appears in `Theorem5_18_4.lean:552-579` (`_GL_rep_decomposition`) and
again in `Theorem5_18_4.lean:675-702` (`_GL_rep_decomposition_explicit`).
The same per-record `ρ i` construction with the diamond-bypassing
post-composition appears in lines 730-756 of the explicit form (after
PR #2599's hoist).

After #2590 lands (delegating non-explicit to `_explicit`), the
duplication will be cut to exactly one site. F2 then becomes a smaller
question: should the `(MonoidHom-into-centralizer-of-symGroupImage)` and
the `(per-component-post-composition-into-End_k(V →ₗ[A] E))`
construction be extracted into named helpers in `Theorem5_18_1.lean`
or `Theorem5_18_4.lean`, so future Schur-Weyl-shaped theorems do not
re-discover them?

Non-blocking; lower priority than F1. Tracked as a follow-up
`feature` issue (tagged `maybe-do-after-#2590`).

### F3 — Issue #2590's "line 654 mutual recursion" heads-up is stale

`Theorem5_18_4_GL_rep_decomposition_explicit`'s body does not call
`Theorem5_18_4_GL_rep_decomposition`. The claim in #2590 is incorrect
on the current code. Recommendation: amend #2590's body to drop the
stale heads-up (replace with a one-line confirmation that the
dependency runs only in the direction explicit → bimodule_explicit
→ centralizers).

Non-blocking; comment posted on #2590.

---

## Summary

**Result**: **PASS-with-followups**.

All ten question categories check out:

- **PR #2578**: Q1 (glHom correctness), Q2 (ρ direct construction
  bypassing the diamond), Q3 (Module.Finite derivations), Q4
  (equivariance proof) all sound. Q5 flagged as a heartbeat-tightening
  opportunity (F1) post-#2599.
- **PR #2579**: Q6 (signature shape), Q7 (eval-formula threading),
  Q10 (doc-string accuracy) all sound. Q8 (ρ duplication) flagged as
  refactor opportunity (F2). Q9's mutual-recursion concern in #2590 is
  stale — confirmed PASS, comment-amendment requested (F3).

Three non-blocking follow-ups (F1 hygiene, F2 refactor, F3 doc-edit on
#2590); zero blocking findings. The Schur-Weyl L_i critical path is
clean through PR #2579.
