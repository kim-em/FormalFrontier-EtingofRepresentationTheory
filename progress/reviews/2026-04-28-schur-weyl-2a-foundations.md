# Schur-Weyl #2a foundations audit — PR #2511

**Issue**: #2561 (review).
**Session**: `b5a0a349` (2026-04-28).
**Scope**: audit the un-audited foundation tier directly underneath the
already-audited equivariance layer (PRs #2538 + #2539 audited in #2549,
PR #2528 + #2551 audited in #2554).

PR #2511 — `feat(Ch5): polyRightTransl + tgtGLAction defs and bijection
helpers (Schur-Weyl #2a foundations, partial #2496)` (+206 lines on
`Chapter5/PolynomialTensorBridge.lean`; merge commit `14d5a200`).

Four commits:

- `842b62f` — `polyRightTransl` def, `tgtGLAction` def, `toLin'_stdBasis`,
  `tgtGLAction_seqTensor`.
- `bd2e60a` — `tgtGLAction_symTensor` (bijection step on RHS).
- `8980110` — `prod_X_eq_monomial_fn`, `polyRightTransl_X`,
  `polyRightTransl_prod`.
- `8923c709` — progress note (no Lean change).

The file carries **zero sorries** in the audited section
(`grep -n sorry EtingofRepresentationTheory/Chapter5/PolynomialTensorBridge.lean`
returns no hits in lines 290-435).

---

## Q1 — `polyRightTransl` definition correctness: **PASS**

`PolynomialTensorBridge.lean:299-302`:
```
noncomputable def polyRightTransl (g : Matrix (Fin N) (Fin N) k) :
    MvPolynomial (Fin N × Fin N) k →ₐ[k] MvPolynomial (Fin N × Fin N) k :=
  MvPolynomial.aeval fun ij : Fin N × Fin N =>
    ∑ l : Fin N, MvPolynomial.X (R := k) (ij.1, l) * MvPolynomial.C (g l ij.2)
```

On generators, `polyRightTransl g (X_{ij}) = ∑_l X_{ij.1, l} · C(g_{l,
ij.2}) = ∑_l X_{i,l} · g_{l,j}`. The matrix product `X · g` has entry
`(X · g)_{ij} = ∑_l X_{i,l} · g_{l,j}`. Index ordering matches.

The doc-string asserts "the action coming from `(g · P)(X) = P(X · g)`":
the substitution `M ↦ M · g` pulls back monomials by exactly the same
formula, so `(polyRightTransl g P)(M) = P(M · g)`. ✓

`MvPolynomial.aeval` produces an `AlgHom`, so the `→ₐ[k]` is free.
This was already cross-verified during audit #2549 (R1) and matches
the polynomial-side action used by `polyTensorRow_equivariant`
(`PolynomialRepEmbedding.lean:383-424`).

## Q2 — `tgtGLAction` definition correctness: **PASS**

`PolynomialTensorBridge.lean:307-309`:
```
noncomputable def tgtGLAction (g : Matrix (Fin N) (Fin N) k) :
    PolyTensorTgt k N n →ₗ[k] PolyTensorTgt k N n :=
  TensorProduct.map (PiTensorProduct.map fun _ : Fin n => g.toLin') LinearMap.id
```

This is the `g^⊗n ⊗ id` action on `V^⊗n ⊗ (V^*)^⊗n`. `g.toLin'` is the
genuine matrix action (not transpose / dual): on the standard basis,
`g.toLin' (e_j) = ∑_b g_{b,j} · e_b` (verified in Q3). The `LinearMap.id`
on the second factor preserves `(V^*)^⊗n` as the doc-string claims —
no spurious transpose / dualization. ✓

Composition direction: `tgtGLAction (h * g) = tgtGLAction h ∘
tgtGLAction g` by functoriality of `PiTensorProduct.map` and
`TensorProduct.map`. This matches `polyRightTransl(h * g) =
polyRightTransl h ∘ polyRightTransl g` (covariant on substitution
side). Both sides compose in the same direction — confirmed in
audit #2549 (R1).

## Q3 — `toLin'_stdBasis` proof: **PASS**

`PolynomialTensorBridge.lean:312-320`:
```
lemma toLin'_stdBasis (g : Matrix (Fin N) (Fin N) k) (j : Fin N) :
    Matrix.toLin' g (stdBasis k N j) = ∑ b : Fin N, g b j • stdBasis k N b
```

Proof chain:
- `ext i` reduces to entry-by-entry equality.
- `rw [stdBasis, Pi.basisFun_apply]` unfolds `stdBasis k N j = Pi.single j 1`.
- `rw [Matrix.toLin'_apply]` reduces to `(g.mulVec (Pi.single j 1)) i`.
- `rw [Matrix.mulVec_single]` unfolds via the standard mul-vec-singleton
  identity, producing an `MulOpposite.op a` smul that becomes trivial when
  `a = 1` (the next two rewrites `MulOpposite.op_one, one_smul` discharge
  it).
- The closing `simp only` chain (with `Pi.single_apply`, `mul_ite`,
  `Finset.sum_ite_eq`, `Finset.mem_univ, if_true`) collapses the indicator
  sum on the RHS to the single surviving term `g i j`.

The kept index is `b` (running variable for the RHS sum); when extracted
at coordinate `i`, the indicator collapses to the term `b = i`, leaving
`g i j` on both sides. Pure linear algebra preliminary — no
characteristic dependence, no transpose convention issue. ✓

## Q4 — `tgtGLAction_seqTensor` proof: **PASS**

`PolynomialTensorBridge.lean:323-341`. Statement:
```
tgtGLAction g (seqTensor f) =
  ∑ b : Fin n → Fin N, (∏ l, g (b l) (f l).2) •
    seqTensor (fun l => ((f l).1, b l))
```

Trace:
1. `unfold tgtGLAction seqTensor` exposes the
   `TensorProduct.map (PiTensorProduct.map ·) id` structure on
   `(⨂_l e_{(f l).2}) ⊗ (⨂_l e_{(f l).1}^*)`.
2. `TensorProduct.map_tmul, LinearMap.id_apply, PiTensorProduct.map_tprod`
   pushes the action through the tensor product, leaving the second
   `(V^*)^⊗n`-factor unchanged. LHS becomes
   `(tprod (fun l => g.toLin' (stdBasis (f l).2))) ⊗ (tprod_dual)`.
3. `simp_rw [toLin'_stdBasis]` (Q3) replaces each
   `g.toLin' (stdBasis (f l).2)` with `∑ b, g b (f l).2 • stdBasis k N b`.
4. `MultilinearMap.map_sum (PiTensorProduct.tprod k) ...` distributes the
   per-coordinate sum across the `tprod`. The summation index is
   `b : Fin n → Fin N` (one choice per coordinate of `Fin n`), exactly the
   shape required by the lemma's RHS.
5. `simp_rw [MultilinearMap.map_smul_univ]` factors the per-coordinate
   scalars `g (b l) (f l).2` out of `tprod`, giving the product
   `∏ l, g (b l) (f l).2`. The product index ordering matches; no scalar
   gets transported across a `tmul`.
6. `rw [TensorProduct.sum_tmul]` distributes the `b`-sum across the outer
   `⊗`, then `Finset.sum_congr rfl; intro b _; rw [TensorProduct.smul_tmul']`
   pulls the scalar across `⊗ₜ` to the outer `•`.

The dual-side `(V^*)^⊗n` factor is preserved verbatim throughout — it
sits behind the `LinearMap.id` and is never touched. The coefficient
extracted is `∏ l, g (b l) (f l).2` (not the transpose `g (f l).2 (b l)`).
The displayed expansion matches the proof. ✓

## Q5 — `tgtGLAction_symTensor` proof and bijection: **PASS**

`PolynomialTensorBridge.lean:346-377`. Statement:
```
tgtGLAction g (symTensor f) =
  ∑ c, (∏ l, g (c l) (f l).2) • symTensor (fun l => ((f l).1, c l))
```

Trace:
1. `unfold symTensor` (applies to **both** sides). LHS becomes
   `tgtGLAction g (n!⁻¹ • ∑_τ seqTensor (f ∘ τ))`; RHS expands the
   per-`c` `symTensor` factor into `n!⁻¹ • ∑_τ seqTensor ((·) ∘ τ)`.
2. `rw [LinearMap.map_smul, map_sum]` pushes `tgtGLAction` through the
   `n!⁻¹ •` and `∑_τ` on the LHS.
3. `simp_rw [tgtGLAction_seqTensor]` (Q4) per τ converts each LHS
   summand to `∑_b (∏_l g (b l) ((f∘τ) l).2) •
     seqTensor (l ↦ ((f∘τ) l).1, b l)`. LHS shape is now
   `n!⁻¹ • ∑_τ ∑_b X(τ, b)`.
4. **Pulling `n!⁻¹` outside the c-sum on RHS**:
   `simp_rw [smul_comm _ ((n.factorial : k)⁻¹), ← Finset.smul_sum]`
   rewrites `(∏ ...) • (n!⁻¹ • ∑_τ ...)` to
   `n!⁻¹ • ((∏ ...) • ∑_τ ...)` (smul-comm), then factors the `n!⁻¹`
   out of the c-sum (← smul_sum). RHS becomes
   `n!⁻¹ • ∑_c (∏ ...) • ∑_τ ...`. The `n!⁻¹` factor is preserved
   verbatim — there is no division-by-`n!` step that would require
   `CharZero k` (this is purely formal manipulation of an element-level
   scalar). ✓
5. `congr 1` discharges the `n!⁻¹ •` factor on both sides.
6. `simp_rw [Finset.smul_sum]` distributes the per-c scalar through the
   τ-sum on RHS, giving `∑_c ∑_τ (∏_l g (c l) (f l).2) •
     seqTensor (l ↦ ((f l).1, c l) ∘ τ)`.
7. `rw [Finset.sum_comm]` swaps `∑_c ∑_τ → ∑_τ ∑_c`.
8. `Finset.sum_congr rfl fun τ _ => ?_` reduces to the per-τ identity.

**Bijection step**:
9. `Fintype.sum_equiv (Equiv.arrowCongr τ (Equiv.refl (Fin N))) _ _ ?_`
   reindexes the LHS `b`-sum via `b ↦ b ∘ τ.symm`. The signature of
   `Fintype.sum_equiv` requires `∀ b, LHS_summand(b) =
   RHS_summand((arrowCongr τ refl) b)`, i.e.
   `∀ b, LHS_summand(b) = RHS_summand(b ∘ τ.symm)`.

   Per `b`:
   - LHS_summand(b) = `(∏_l g (b l) (f (τ l)).2) • seqTensor (l ↦ ((f (τ l)).1, b l))`
   - RHS_summand(b ∘ τ.symm) =
     `(∏_l g (b (τ.symm l)) (f l).2) • seqTensor (m ↦ ((f (τ m)).1, (b ∘ τ.symm)(τ m)))`
     = `(∏_l g (b (τ.symm l)) (f l).2) • seqTensor (m ↦ ((f (τ m)).1, b m))`
     (since `(b ∘ τ.symm)(τ m) = b m`).

   The seqTensor parts agree directly. The product parts agree via the
   reindex `l ↦ τ⁻¹(l)`: `∏_l g (b (τ.symm l)) (f l).2 =
   ∏_m g (b m) (f (τ m)).2` (substitute `l = τ m`). Lean closes both
   parts:
   - product: `Fintype.prod_equiv τ _ _ ?_; intro l; simp
     [Equiv.arrowCongr_apply]` — applies the τ-reindex.
   - seqTensor: `congr 1; funext l; simp [Equiv.arrowCongr_apply]` —
     uses `(b ∘ τ.symm) (τ l) = b l`.

The bijection is correctly applied; the product and seqTensor reindexing
match the τ-permutation; the `(n!)⁻¹` factor is preserved on both sides.
The displayed equation is exactly what the proof produces. ✓

## Q6 — Polynomial-side helpers: **PASS**

`prod_X_eq_monomial_fn` (`PolynomialTensorBridge.lean:384-399`):
states `(∏_l X (f l)) = monomial (∑_l Finsupp.single (f l) 1) 1`.
Proof: Finset induction on `Finset.univ`, base case `simp`, step uses
`MvPolynomial.X = monomial (single _ 1) 1` (definitional `from rfl`)
and `MvPolynomial.monomial_mul, mul_one`. The `key : ∀ s, ...`
generalization is required because Finset induction needs an arbitrary
finite-set parameter. Sound.

`polyRightTransl_X` (`PolynomialTensorBridge.lean:402-408`):
states `polyRightTransl g (X ij) = ∑ l, X (ij.1, l) * C (g l ij.2)`.
Proof: `unfold polyRightTransl; rw [aeval_X]`. This is a one-line
`aeval_X` unfolding — no characteristic dependence. (The unnecessary
`[CharZero k]` instance is the subject of finding F1 below, already
tracked in #2565.) ✓

`polyRightTransl_prod` (`PolynomialTensorBridge.lean:413-435`):
states `polyRightTransl g (∏_l X (f l)) = ∑_c C (∏_l g (c l) (f l).2) *
∏_l X ((f l).1, c l)`. Trace:
- `rw [map_prod]` pushes `polyRightTransl g` through `∏_l`.
- `simp_rw [polyRightTransl_X]` replaces each per-l factor with the
  per-l sum `∑_j X((f l).1, j) * C(g j (f l).2)`.
- `rw [Finset.prod_univ_sum]` distributes the prod over per-l sums to
  a single big sum indexed by choice functions
  `Fintype.piFinset _`. The `Fintype.piFinset_univ` rewrite identifies
  this with `(Finset.univ : Finset (Fin n → Fin N))`.
- Per-c bookkeeping: `Finset.prod_mul_distrib` splits the per-l
  `(X * C)` factors, `(map_prod C).symm` packs the per-l `C(g _ _)`s
  into a single `C` of a product, then `ring` rearranges to the RHS
  shape.

This **matches** Q1's index ordering: `polyRightTransl g (∏_l X(a_l,
b_l)) = ∑_c C(∏_l g(c_l, b_l)) · ∏_l X(a_l, c_l)`, which is exactly
`(g · P)(X) = P(X · g)` for `P = ∏_l X(a_l, b_l)`:
`P(X · g) = ∏_l (X·g)_{a_l, b_l} = ∏_l (∑_{c_l} X_{a_l, c_l} ·
g_{c_l, b_l}) = ∑_c (∏_l X_{a_l, c_l}) · (∏_l g_{c_l, b_l})`. ✓

These helpers feed into `polyToTensor_rightTransl_of_isHomogeneous`
(`PolynomialTensorBridge.lean:616-660`), audited in #2549 — the
bridge equivariance theorem cites both `polyRightTransl_prod` (line
646) and `prod_X_eq_monomial_fn` indirectly via `polyToTensor_prod_X`
(which itself uses `prod_X_eq_monomial_fn` at line 555). No clarity
issues flagged in #2549.

## Q7 — Downstream usability and signature consistency: **PASS**

Downstream consumers are:

- `polyToTensor_rightTransl_of_isHomogeneous`
  (`PolynomialTensorBridge.lean:616-660`, audited in #2549):
  uses `polyRightTransl_prod` and `tgtGLAction_symTensor`. Both
  signatures match — the bridge equivariance proof reads as a clean
  composition of the foundations.
- `polyTensorRow_equivariant`
  (`PolynomialRepEmbedding.lean:383-424`, audited in #2549): uses
  `homogeneousPolyToTensor_equivariant` and
  `polyRightTransl_isHomogeneous`. Carries `[CharZero k]` legitimately
  (downstream of `polyToTensor_prod_X` which transitively needs
  `tensorToPoly_symTensor` whose proof uses
  `inv_mul_cancel₀ ((n!) ≠ 0)` — genuine `CharZero`).
- `splitDualBasis_tgtGLAction`
  (`PolynomialRepEmbedding.lean:288-309`, audited in #2554): uses
  `tgtGLAction` definition directly. Signature matches.
- `matrixCoeffPoly_polyRightTransl`
  (`PolynomialRepEmbedding.lean:315-379`, audited in #2554): uses
  `polyRightTransl` directly via the `hP_mul` hypothesis.
- `eval_polyRightTransl` and `hP_mul_of_hP`
  (`PolynomialRepEmbedding.lean:652, 680`, audited in #2554): use
  `polyRightTransl_X`. Both currently carry `[CharZero k]` because the
  upstream `polyRightTransl_X` unnecessarily inherits it (F1 below;
  tracked in #2565).

**No spurious instance hypothesis** — i.e. no downstream consumer had
to **add** an instance because the foundations were missing it. The
opposite direction (foundations carrying unused `[CharZero k]`) is the
hygiene finding F1, not a usability blocker.

**No transpose / dual fix-up** in any downstream proof. The
`g.toLin'` action on `V` (column-vector convention, `g.toLin' (e_j) =
∑_b g_{b,j} e_b` per Q3) lines up with the polynomial-side substitution
`X_{ij} ↦ ∑_l X_{i,l} g_{l,j}` (Q1) without flips.

## Q8 — Doc-string honesty: **PASS**

- `polyRightTransl` (line 296-298): "Right-translation as an algebra
  hom on `MvPolynomial (Fin N × Fin N) k`. On generators: `X_{ij} ↦
  Σ_l X_{il} · C(g_{l,j})`. This is the action coming from
  `(g · P)(X) = P(X · g)`." — matches Q1.
- `tgtGLAction` (line 304-306): "The `g^⊗n ⊗ id` action on `V^⊗n ⊗
  (V^*)^⊗n`. The matrix `g` acts on the first `V^⊗n` factor by tensor
  power; the second `(V^*)^⊗n` factor is left unchanged." — matches Q2.
- `toLin'_stdBasis` (line 311): "Expansion of `g.toLin'` on a standard
  basis vector." — accurate.
- `tgtGLAction_seqTensor` (line 322): "Expansion of `tgtGLAction g` on
  a `seqTensor`." — accurate.
- `tgtGLAction_symTensor` (line 343-345): "Expansion of `tgtGLAction
  g` on a `symTensor`. The bijection `(σ, b) ↔ (σ, b ∘ σ⁻¹)` matches
  the inner sum on the LHS with the inner sum coming from
  `symTensor`'s expansion on the RHS." — accurate; matches Q5.
- `prod_X_eq_monomial_fn` (line 381-383): "A product of `X`s equals
  the monomial whose Finsupp records each pair's multiplicity." —
  accurate.
- `polyRightTransl_X` (line 401): "`polyRightTransl g` evaluated on a
  single `X`-generator." — accurate.
- `polyRightTransl_prod` (line 410-413): "Expansion of
  `polyRightTransl g` on a product `∏_l X (f l)`. The result is a sum
  over choice functions `c : Fin n → Fin N`, with constant multiplier
  `C(∏_l g (c l) (f l).2)` on the substituted monomial `∏_l X((f l).1,
  c l)`." — matches Q6.

All doc-strings describe **what the artifact computes**, not what
downstream consumers will derive. ✓

---

## Findings

### F1 — Unnecessary `[CharZero k]` on the entire `## GL_N-equivariance` block (hygiene)

The file has `variable [CharZero k]` at `PolynomialTensorBridge.lean:167`,
which is required by `tensorToPoly_symTensor` (line 171, uses
`inv_mul_cancel₀` on `(n!)⁻¹`). Everything below — including the entire
`## GL_N-equivariance` section (lines 290-435) — picks up
`[CharZero k]` via section auto-binding.

None of the foundation definitions or lemmas in lines 290-435 actually
use `CharZero k`:

- **defs**: `polyRightTransl` (line 299), `tgtGLAction` (line 307).
- **lemmas**: `toLin'_stdBasis` (line 312), `tgtGLAction_seqTensor`
  (line 323), `tgtGLAction_symTensor` (line 346),
  `prod_X_eq_monomial_fn` (line 384, already `private`),
  `polyRightTransl_X` (line 403), `polyRightTransl_prod` (line 414).

The pattern `omit [CharZero k] in` already appears in this file at line
187 (for `prod_X_canonicalSeq`) and line 594 (for
`polyRightTransl_isHomogeneous`) — so the author was aware of the
instance-relaxation pattern and used it for two adjacent lemmas, but
not for the `## GL_N-equivariance` block.

**Status**: Issue #2565 already partially addresses this, scoped to
`polyRightTransl_X` and its downstream consumers
`eval_polyRightTransl` / `hP_mul_of_hP`. The other six artifacts in
the block are not covered by #2565 and warrant a follow-up. Filed as
**finding F1**, see follow-up issue created with this audit.

This is not a blocker — every current downstream caller carries
`[CharZero k]` legitimately. F1 is a hygiene cleanup that documents
intent and mirrors the `[Infinite k]`-floor of the
`MvPolynomial.eq_of_eval_eq_on_gl` chain.

---

## Summary

**Result**: **PASS-with-followups**.

All eight question categories check out:
- Q1-Q2: definitions match the documented mathematical actions.
- Q3-Q5: proofs are mathematically correct, with clean bijection
  handling and correct `(n!)⁻¹` preservation in Q5.
- Q6: polynomial-side helpers correctly compute `(g · P)(X) =
  P(X · g)` on products of `X`s, with index ordering matching Q1.
- Q7: downstream consumers (audited in #2549, #2554) use the
  foundations without adding spurious instances or fix-ups.
- Q8: doc-strings honestly describe what each artifact computes.

One non-blocking hygiene finding (F1) on `[CharZero k]` propagation;
a follow-up `review-finding` issue extends the existing #2565 cleanup
to cover the rest of the foundations.
