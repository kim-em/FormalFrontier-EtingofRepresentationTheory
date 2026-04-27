# Schur-Weyl L_i polynomial C-1 + C-2 audit — PRs #2600 + #2606

**Issue**: #2608 (review).
**Session**: `85542f89` (2026-04-27).
**Scope**: audit the two polynomial-side links of the Schur-Weyl L_i
critical path that landed 2026-04-27 (after the equivariance/explicit
form audit #2592 closed via PR #2603).

| PR | Theorem | Closes | Lines | Merge |
|----|---------|--------|-------|-------|
| #2600 | `formalCharacter_glTensorRep_eq_pow` (`Chapter5/FormalCharacterIso.lean`) | #2580 | +229/-8 | 2026-04-27T17:16Z |
| #2606 | `sum_X_pow_eq_sum_charValue_smul_schurPoly` (`Chapter5/SchurWeylPolynomialIdentity.lean`) | #2581 | +217/-7 | 2026-04-27T17:54Z |

Both PRs are on the Schur-Weyl L_i critical path. Together with the
equivariant-decomposition audit #2592 (PRs #2578 + #2579) they cover
the full polynomial-side input to the Schur-Weyl L_i final assembly
(#2493). The remaining two C-tier sub-issues are #2582 and #2583 (L_i
and `SchurModule` simplicity), neither of which interacts with the
polynomial identities.

`grep -n sorry` returns **one** hit in the audited regions:
`Chapter5/FormalCharacterIso.lean:399` (the existing top-level
`iso_of_formalCharacter_eq_schurPoly` placeholder for issue #2483 / #6).
This sorry pre-dates both PRs and is not introduced by either of
them. `Chapter5/SchurWeylPolynomialIdentity.lean` and the new code in
`Chapter5/Proposition5_21_1.lean` (the `_univ` refactor) and
`Chapter5/Theorem5_22_1.lean` (the privacy relaxations) contain zero
sorries.

---

## PR #2600 — `formalCharacter glTensorRep = (∑ Xᵢ)^n`

### Q1 — statement is the standard multinomial form: **PASS**

`Chapter5/FormalCharacterIso.lean:1042-1048`:

```
theorem formalCharacter_glTensorRep_eq_pow (N n : ℕ) :
    formalCharacter k N (FDRep.of (glTensorRep k N n)) =
      (∑ i : Fin N, MvPolynomial.X i) ^ n
```

`N` is the dimension of the standard module `V = Fin N → k`, `n` is
the tensor power. The polynomial sum runs over `i : Fin N` (one
variable per coordinate of `V`), the power exponent is `n`, and the
character is computed for the diagonal `GL_N(k)`-action `g ↦ g^{⊗n}`
on `V^{⊗n}` (`glTensorRep k N n` per `Theorem5_22_1.lean:217-220`).
This is exactly `(X_1 + ⋯ + X_N)^n` — no off-by-one, correct variable
identification.

Note the issue body (#2580) called the theorem
`formalCharacter_glTensorRep_eq_sum_X_pow`; the landed name is
`formalCharacter_glTensorRep_eq_pow` (8 chars shorter, same content).
Naming difference only — flagged below as F2.

### Q2 — proof path: direct, not via `formalCharacter_tensorPower`: **PASS**

The proof is entirely direct (the `formalCharacter_tensorPower`
hypothetical mentioned in the audit question does not exist as a
separate lemma in the codebase). Trace:

1. `tensorStdBasis_mem_glWeightSpace`
   (`FormalCharacterIso.lean:951-963`): each
   `tensorStdBasis k N n f` lies in the weight space at weight
   `tensorWeight N f` (= the multiset of color counts of `f`). Proof:
   the diagonal action multiplies a tensor basis vector by
   `t^{count_i(f)}` per `glTensorRep_diagUnit_basis`
   (`Theorem5_22_1.lean:843-862`).
2. `tensorStdBasis_repr_eq_zero_of_ne_weight`
   (`FormalCharacterIso.lean:949-985`): coordinates of vectors in the
   weight space at `μ` vanish on basis vectors with different weight.
   The proof picks an index `i` where `tensorWeight f` and `μ` differ,
   uses `exists_unit_pow_ne` to find a unit `t` with
   `t^{(tw f) i} ≠ t^{μ i}`, and concludes via `linear_combination`.
3. `glWeightSpace_glTensorRep_eq_span`
   (`FormalCharacterIso.lean:988-1018`): the weight space at `μ` =
   span of basis vectors with `tensorWeight = μ`. By
   `linearCombination_repr` and the previous step.
4. `finrank_glWeightSpace_glTensorRep`
   (`FormalCharacterIso.lean:1022-1033`): `finrank_span_eq_card`
   applied to the linearly-independent subfamily.
5. `formalCharacter_glTensorRep_eq_pow`
   (`FormalCharacterIso.lean:1042-1048`): coefficient-wise comparison
   via `formalCharacter_coeff` (LHS) and `sum_X_pow_coeff` (RHS).

Path is clean, locally elementary, no detours through general tensor
power machinery. ✓

### Q3 — multinomial expansion is symbolic via `Finset.sum_pow'`: **PASS**

Three private helpers do the polynomial-side bookkeeping:

- `sum_X_pow_eq_sum_prod` (`FormalCharacterIso.lean:967-973`): expands
  `(∑ X)^n = ∑_{f : Fin n → Fin N} ∏_j X_{f j}` via
  `Finset.sum_pow'` + `Fintype.piFinset_univ`. This is the standard
  symbolic multinomial expansion in any commutative semiring. No
  numeric specialisation, no `Fin n → Fin N` coercion gymnastics.
- `sum_X_pow_eq_sum_monomial` (`FormalCharacterIso.lean:976-980`):
  composes with `prod_X_eq_monomial_tensorWeight` to reach
  `∑_f monomial (tensorWeight N f) 1`.
- `sum_X_pow_coeff` (`FormalCharacterIso.lean:983-991`): coefficient
  extraction at `μ` via `coeff_sum`, `coeff_monomial`, and
  `Finset.sum_boole` to count `{f : tensorWeight N f = μ}`.

Indexing matches the downstream consumer
`finrank_glWeightSpace_glTensorRep` (also `Fintype.card_subtype` on
`{f // tensorWeight N f = μ}`). ✓

### Q4 — heartbeat bumps: **PASS**

PR #2600 introduces **no new** heartbeat bumps. The only
`set_option maxHeartbeats` in `Chapter5/FormalCharacterIso.lean`
(line 760, value 6400000) pre-dates this PR (it gates
`glTensorRep_equivariant_schurWeyl_decomposition`, audited as F1
in #2592). The new lemmas (lines 949-1048) all compile with default
heartbeats. The renames in `Theorem5_22_1.lean` and the
collision-avoidance rename in `Proposition5_22_2.lean` introduce
nothing.

### Q5 — typeclass assumptions: **PASS-with-followup (F1)**

The new theorem inherits `[Field k]`, `[IsAlgClosed k]`,
`[CharZero k]` from the variable scope at
`FormalCharacterIso.lean:228`. Of these:

- `[Field k]` and `[IsAlgClosed k]` are required (`exists_unit_pow_ne`
  needs both, transitively via
  `tensorStdBasis_repr_eq_zero_of_ne_weight`).
- `[CharZero k]` is **not required**: the proof uses only
  `formalCharacter_coeff` (which `omit [CharZero k] in` at
  `Theorem5_22_1.lean:508`), `sum_X_pow_coeff` (purely polynomial,
  no CharZero), `finrank_glWeightSpace_glTensorRep` (uses no CharZero
  facts), and `Fintype.card_subtype` (combinatorial).

The supporting private lemmas
`tensorStdBasis_mem_glWeightSpace`,
`tensorStdBasis_repr_eq_zero_of_ne_weight`,
`glWeightSpace_glTensorRep_eq_span`, and
`finrank_glWeightSpace_glTensorRep` likewise carry an unnecessary
`[CharZero k]`.

Applying `omit [CharZero k] in` to the new lemmas would relax the
hypothesis correctly. Non-blocking; downstream consumers in the
Schur-Weyl assembly all carry `[CharZero k]` already (it's needed for
the orthogonality / Frobenius-character chain). Tracked as F1.

---

## PR #2606 — Schur-Weyl polynomial identity

### Q6 — indexing is `BoundedPartition N n`, matching `schurPoly_linearIndependent`: **PASS**

`Chapter5/SchurWeylPolynomialIdentity.lean:74-79`:

```
theorem sum_X_pow_eq_sum_charValue_smul_schurPoly (N n : ℕ) :
    (∑ i : Fin N, (MvPolynomial.X i : MvPolynomial (Fin N) ℚ)) ^ n =
      ∑ lam : BoundedPartition N n,
        charValue N lam (trivialCycleType n) • schurPoly N lam.parts
```

`BoundedPartition N n` per `Proposition5_21_1.lean:320-326` is
`{ parts : Fin N → ℕ // Antitone parts ∧ ∑ i, parts i = n }`. The
audit-question phrasing "parts ≤ N, sum = n" is slightly imprecise —
the actual constraint is *at most N parts* (functor `Fin N → ℕ`)
weakly decreasing summing to `n` — but the indexing **does** match
the expected `BoundedPartition` semantics and **does** match the
indexing of `schurPoly_linearIndependent` modulo the
`sum = n` restriction.

`schurPoly_linearIndependent` (`FormalCharacterIso.lean:98-100`)
indexes over `{lam : Fin N → ℕ // Antitone lam}` — all antitone weights,
no sum constraint. The Schur-Weyl polynomial identity restricts
the index set to `{lam : Antitone ∧ sum = n}` (i.e. degree-`n`
homogeneous), which is consistent because the LHS `(∑ X)^n` is
homogeneous of degree `n` and `schurPoly N lam.parts` for `λ` not
summing to `n` doesn't appear (zero coefficient). `BoundedPartition`'s
weakly-decreasing constraint matches `Antitone`. ✓

### Q7 — coefficient sourcing: factors through `Proposition5_21_1_univ`: **PASS**

The proof is two lines:

```
rw [← psumPart_trivialCycleType N n]
exact Proposition5_21_1_univ N (trivialCycleType n)
```

`psumPart_trivialCycleType` (`SchurWeylPolynomialIdentity.lean:48-53`)
proves `psumPart (trivialCycleType n) = (∑ Xᵢ)^n` by collapsing
`Multiset.replicate n 1` under `Multiset.map (psum)` then
`Multiset.prod_replicate`, finally using `psum_one : psum 1 = ∑ Xᵢ`
(Mathlib `RingTheory/MvPolynomial/Symmetric/Defs.lean:360`).

`Proposition5_21_1_univ` (`Proposition5_21_1.lean:570-572`) is the
**universe form** of Proposition 5.21.1, refactored from the
existing `Proposition5_21_1` (which is now a 3-line existential
wrapper). The proof body of `_univ` is unchanged — it's the same
proof that previously used `lams = Finset.univ` as its existential
witness. This refactor is API-only.

So the chain is: `(∑ Xᵢ)^n = psumPart (trivialCycleType n) =
∑_λ charValue N λ (trivialCycleType n) • schurPoly N λ.parts`
(by Frobenius character formula, Proposition 5.21.1 specialised to
the trivial cycle type). Mathematically standard: the trivial cycle
type is the cycle type of the identity permutation, so its `psumPart`
is `p_1^n = (∑ X)^n`, and the Frobenius formula expresses the result
as a charValue-weighted sum of Schur polynomials. ✓

The downstream "charValue at identity = Specht-module dimension"
identification is provided as a separate lemma
`charValue_trivialCycleType_eq_spechtFinrank`
(`SchurWeylPolynomialIdentity.lean:101-109`). See Q10 below for the
mismatch between the issue body's expected form and the landed form.

### Q8 — no sorries, no decide, minimal cast usage: **PASS**

Across `SchurWeylPolynomialIdentity.lean`, `Proposition5_21_1.lean`
diff, and `Theorem5_22_1.lean` privacy relaxation: **zero sorries,
zero `decide`, zero `convert` invocations**.

- `trivialCycleType` (`SchurWeylPolynomialIdentity.lean:35-41`)
  uses `omega` on `Multiset.mem_replicate` and `simp` on
  `Multiset.sum_replicate`. Standard.
- `psumPart_trivialCycleType` is `unfold` + `change` + `rw`. The
  `change` is a definitional unfolding of `psumPart` to expose
  `Multiset.map (psum) (Multiset.replicate n 1)` — necessary because
  the `psumPart` definition has `(μ.parts.map (psum σ R)).prod`
  pattern that needs `change` to expose for the `Multiset.replicate`
  rewrite. Justified.
- `sum_X_pow_eq_sum_charValue_smul_schurPoly` is two `rw`s. Clean.
- `fullCycleTypePartition_one`: `apply Nat.Partition.ext` + `change`
  + `rw [Equiv.Perm.cycleType_one, …]`. Clean.
- `spechtModuleCharacter_one`: `unfold` + `rw [show ... from
  map_one ..., LinearMap.trace_one]`. The inline `show` proof of
  `spechtModuleAction n la 1 = 1` via `map_one (spechtModuleRep n la)`
  is a clean way to avoid a separate helper. Acceptable.
- `charValue_trivialCycleType_eq_spechtFinrank`: 3-line `rw` chain.
  The statement uses one `lam.sum_eq ▸` cast — see F3 below.

No unjustified casts in proofs. ✓

### Q9 — heartbeat bumps: **PASS**

`Chapter5/SchurWeylPolynomialIdentity.lean` introduces **no
heartbeat bumps**. The `Proposition5_21_1` refactor (split into
`_univ` + existential wrapper) introduces no bumps either —
`Proposition5_21_1_univ`'s body is the unchanged proof of the
original theorem (just instantiated `lams = Finset.univ` directly).
The privacy relaxation on `charValue_eq_spechtModuleCharacter`
(`Theorem5_22_1.lean:2487`) is a one-keyword change with no proof
modification. ✓

### Q10 — residual sorries / form mismatch: **PASS-with-followup (F3)**

No residual sorries in `Chapter5/SchurWeylPolynomialIdentity.lean`,
`Chapter5/Proposition5_21_1.lean`, or
`Chapter5/Theorem5_22_1.lean` (excluding pre-existing sorries
unrelated to either PR; the only sorry on the audited path is
`FormalCharacterIso.lean:399`'s `iso_of_formalCharacter_eq_schurPoly`
placeholder for #2483, which is not introduced by either PR).

**Form mismatch** (F3): the issue body (#2608, also #2581) describes
the deliverable as

> `(∑ Xᵢ)^n = ∑_λ (Module.finrank · SpechtModule) • schurPoly N λ`.

The actual landed theorem
`sum_X_pow_eq_sum_charValue_smul_schurPoly`
gives the coefficient as `charValue N lam (trivialCycleType n)` —
a rational number — and provides the
"`charValue at identity = dim(Specht)`" identification as a separate
lemma `charValue_trivialCycleType_eq_spechtFinrank`. This separate
lemma lives in `ℂ` (because `SpechtModule` is defined over `ℂ` in
`Chapter5/Theorem5_12_2_Irreducible.lean:26-28`).

So the dimension-form statement
`(∑Xᵢ)^n = ∑_λ (dim(SpechtModule) : ℚ) • schurPoly`
does not exist in one piece. A downstream consumer who wants to
substitute "dim(Specht)" for "charValue" must either (a) move the
polynomial identity into `MvPolynomial (Fin N) ℂ` via `MvPolynomial.map
(algebraMap ℚ ℂ)` (then both sides cast cleanly because
`charValue_trivialCycleType_eq_spechtFinrank` is stated in `ℂ`), or
(b) prove a `ℚ`-valued or `ℕ`-valued version of the dimension bridge.

Mathematically the bridge `charValue at identity = dim(Specht)` is
correct; the value is a non-negative integer and lives in `ℕ`,
but the codebase plumbing through `spechtModuleCharacter`'s `ℂ`-trace
forces the cast. This is a small architectural friction that the
final-assembly consumer (#2493) will need to resolve. Tracked as F3 —
non-blocking, since the `ℂ`-bridge already provides everything needed
and only minor cast bookkeeping remains.

---

## Findings

### F1 — `formalCharacter_glTensorRep_eq_pow` (PR #2600) carries `[CharZero k]` unnecessarily (hygiene)

`Chapter5/FormalCharacterIso.lean:1042` and the four supporting
private lemmas at `949`, `985`, `988`, `1022` all inherit
`[CharZero k]` from the file-scope variable at line 228, but none
of them rely on `CharZero` (the proof goes through
`formalCharacter_coeff` which `omit [CharZero k] in`,
`sum_X_pow_coeff` which is purely polynomial, and
`finrank_glWeightSpace_glTensorRep` which uses no CharZero facts).

Wrapping the new lemmas in `omit [CharZero k] in` would relax the
hypothesis correctly. Non-blocking — every downstream consumer
already has `[CharZero k]` for orthogonality reasons — but worth
filing for hygiene parity with `formalCharacter_coeff` and the other
`omit [CharZero k] in` neighbours (lines 461, 476, 517, 566, 583,
600, 635, 656).

Tracked as a follow-up `feature` issue.

### F2 — Theorem name divergence between issue body and landed code (cosmetic)

Issue #2580 specified the deliverable as
`formalCharacter_glTensorRep_eq_sum_X_pow`. The landed name is
`formalCharacter_glTensorRep_eq_pow`. Both are reasonable; the
landed name is shorter. No action needed beyond updating the issue
body if it's still discoverable.

Not tracked separately — purely cosmetic, the naming choice in the
landed PR is fine on its own merits.

### F3 — `sum_X_pow_eq_sum_charValue_smul_schurPoly` (PR #2606) doesn't directly produce the dimension-form expected by the issue body (form-mismatch)

The issue body (#2581 and #2608) calls for
`(∑ Xᵢ)^n = ∑_λ (Module.finrank · SpechtModule) • schurPoly N λ`.
The landed theorem produces the `charValue`-coefficient form, with
a separate `ℂ`-cast bridge `charValue_trivialCycleType_eq_spechtFinrank`.

A downstream consumer (the final-assembly target in #2493) will
need either:

1. A combined theorem in `MvPolynomial (Fin N) ℂ` that bundles the
   identity with the `ℂ`-cast dimension substitution, or
2. A `ℕ`-valued or `ℚ`-valued version of
   `charValue_trivialCycleType_eq_spechtFinrank` (justified because
   the `ℂ`-equality factors as `(↑(Nat.cast)) ↔ (↑(Nat.cast))` for
   non-negative integer values on both sides).

Either path is a small additional lemma. Tracked as a follow-up
`feature` issue. Non-blocking — the `ℂ`-bridge provides everything
needed for the final assembly; this F3 is just about reducing
bookkeeping at the call site.

---

## Summary

**Result for PR #2600**: **PASS-with-followup (F1)**.

All five question categories check out. Q1 (statement form), Q2 (proof
path), Q3 (symbolic multinomial expansion), Q4 (no new heartbeat
bumps), and Q10's content for #2600 (no introduced sorries) all
sound. Q5 flagged as a hygiene opportunity (F1: `omit [CharZero k] in`
should be applied to the new lemmas). Naming divergence noted as F2
but no action required.

**Result for PR #2606**: **PASS-with-followup (F3)**.

All five question categories check out. Q6 (indexing matches
`schurPoly_linearIndependent`), Q7 (proof factors cleanly through
`Proposition5_21_1_univ`), Q8 (no sorries, no decide, minimal casts),
Q9 (no heartbeat bumps) all sound. Q10 flagged as a form-mismatch
between the issue body's expected dimension-form statement and the
landed `charValue`-form statement (F3). Both PRs together close out
the polynomial-side audit coverage of the Schur-Weyl L_i critical
path. Together with the equivariance-side coverage (#2592 covering
PRs #2578 + #2579), the full Schur-Weyl L_i polynomial+equivariance
infrastructure is now audited; only the simplicity clauses (#2582 +
#2583) remain to round out C-tier auditability.

Two non-blocking follow-ups (F1 hygiene on PR #2600, F3 form-cleanup
on PR #2606); zero blocking findings.
