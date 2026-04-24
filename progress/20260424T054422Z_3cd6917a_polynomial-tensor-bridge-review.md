## Accomplished

Review session on issue #2507 — audit of PR #2502 (`PolynomialTensorBridge.lean`,
the construction + injectivity portion of Schur-Weyl sub-issue #2a).

The file is `EtingofRepresentationTheory/Chapter5/PolynomialTensorBridge.lean`,
~291 lines (the issue body's "~1200 lines" is incorrect — it presumably
counted dependent infrastructure, but the file itself is well under the
500-line review-difficulty threshold). Build is clean
(`lake build EtingofRepresentationTheory.Chapter5.PolynomialTensorBridge`
succeeds, one minor unused-section-variable linter warning).

`grep -n sorry` returns zero matches in the file. No definitional sorries
either (Definitions Must Be Constructed: ✓).

## Findings

### Q1 — `seqTensor` / `symTensor` sanity: **Pass**

* `symTensor f := (n.factorial : k)⁻¹ • Σ_σ seqTensor (f ∘ σ)` (line 89-90).
  The `1/n!` scalar is correct: there are exactly `Fintype.card (Equiv.Perm (Fin n)) = n!`
  terms in the sum, so dividing by `n!` makes the symmetrizer idempotent on
  permutation-invariant tensors. The `[CharZero k]` hypothesis (introduced at
  line 167) ensures `(n! : k) ≠ 0`, so the inverse is well-defined.
* `symTensor_comp_perm` (line 94-101): proven by reindexing the sum via
  `Fintype.sum_equiv (Equiv.mulLeft τ)`. The argument is `f ∘ τ ∘ σ`
  which in Mathlib's `Equiv.Perm` convention parses as `f ∘ (τ * σ)`
  (since for `Equiv.Perm α`, `(τ * σ) x = τ (σ x)`). After
  `simp only [Equiv.coe_mulLeft]`, `mulLeft τ σ = τ * σ`, so the
  required equation `seqTensor (f ∘ τ ∘ σ) = seqTensor (f ∘ (τ * σ))`
  holds by `rfl`. The proof closes correctly.

The 1/n! is **not** off-by-one. (`1/(n-1)!` would not symmetrise; `1/(n+1)!` would
under-correct the average.) Symmetric and the sum is over the symmetric
group — hence Sym group has order `n!` and the average needs `1/n!`.

### Q2 — `canonicalSeq` well-definedness: **Pass**

`canonicalSeq s hs i := (Finsupp.toMultiset s).toList.get ⟨i.val, h⟩` where
`h` is built from:
  ```
  rw [Multiset.length_toList, Finsupp.card_toMultiset]
  exact hs ▸ i.isLt
  ```

* `Multiset.length_toList m : m.toList.length = m.card`. ✓
* `Finsupp.card_toMultiset f : (toMultiset f).card = f.sum (fun _ => id)`
  (verified at `Mathlib/Data/Finsupp/Multiset.lean:66`). ✓
* `hs : s.sum (·) = n`, so `hs ▸ i.isLt : i.val < n` becomes
  `i.val < s.sum (·)`. ✓

So the list has length **exactly `n`** and the index proof obligation is
discharged purely from `hs` and arithmetic — no classical-choice artefact
beyond the noncomputability of `Multiset.toList` itself, which is
universal to multiset enumeration and unavoidable.

### Q3 — `multisetToTensor` handles `|s| ≠ n`: **Pass**

```
multisetToTensor s :=
  if hs : s.sum (·) = n then symTensor (canonicalSeq s hs) else 0
```

`tensorToPoly_multisetToTensor` (line 227-233) uses `split_ifs with hs`:

* `hs` true: rewrites via `tensorToPoly_symTensor` then `prod_X_canonicalSeq`.
* `hs` false: `simp` closes via `tensorToPoly k N n 0 = 0` (`map_zero`)
  matching the RHS `0` from `if_neg`.

`split_ifs` correctly splits the matching `if-then-else` on both LHS
(from `multisetToTensor`) and RHS (from the lemma's stated `if`), keeping
the branches in lockstep. `0 ↦ 0` is verified.

### Q4 — Left-inverse chain + use of homogeneity hypothesis: **Pass**

`tensorToPoly_polyToTensor_eq_self (p) (hp : p.IsHomogeneous n)` (line 238-271):

The proof expands `p = ∑_{v ∈ p.support} monomial v (coeff v p)` via
`MvPolynomial.as_sum`, applies `polyToTensor` then `tensorToPoly`
linearly across the sum, and verifies each summand. For each `s` in the
support:

1. `coeff s p ≠ 0` (from `mem_support_iff`).
2. **`hp` is genuinely used**: `hp hcoeff_ne` gives `Finsupp.weight 1 s = n`,
   which `Finsupp.weight_apply` + `simpa` reduces to `s.sum (·) = n`.
3. This `hsn` is the discharge for `if_pos hsn` in
   `tensorToPoly_multisetToTensor`. Without `hp`, the off-degree branch
   would give `0` and the round trip would fail.

The hypothesis is therefore **load-bearing**, not vestigial. Removing
`hp` would not just weaken the lemma — it would make it false (e.g.,
for `p = X_{0,0} : MvPolynomial _ k`, applying `polyToTensor`
projects it to the degree-`n` component, which is `0` for `n ≠ 1`).

The `congr 2; exact p.as_sum` rewrite pattern is unusual but
operationally sound — it conjures the rewrite back into a usable form
after the initial `conv_rhs => rw [p.as_sum]`. (Could be simplified;
see "Recommendation" below.)

### Q5 — `prod_X_canonicalSeq` key identity: **Pass**

Line 191-223. The chain:

```
∏ l : Fin n, X (canonicalSeq s hs l)
  --[List.prod_ofFn]-->
(List.ofFn fun l => X (canonicalSeq s hs l)).prod
  --[hmap: List.ext_getElem]-->
((toMultiset s).toList.map X).prod
  --[Multiset.coe_toList ; map_coe ; prod_coe]-->
((toMultiset s).map X).prod
  --[Finsupp.toMultiset_map]-->
(toMultiset (mapDomain X s)).prod
  --[Finsupp.prod_toMultiset]-->
(mapDomain X s).prod (fun a n => a^n)
  --[Finsupp.prod_mapDomain_index_inj X_injective]-->
s.prod (fun a n => (X a)^n)
  --[MvPolynomial.prod_X_pow_eq_monomial]-->
monomial s 1
```

Each step verified against Mathlib:

* `Finsupp.toMultiset_map (f : α →₀ ℕ) (g : α → β) : f.toMultiset.map g = toMultiset (f.mapDomain g)`
  (`Finsupp/Multiset.lean:69`) — matches direction used.
* `Finsupp.prod_toMultiset (f : α →₀ ℕ) [CommMonoid α] : f.toMultiset.prod = f.prod (fun a n => a^n)`
  (`Finsupp/Multiset.lean:80`) — direction matches.
* `Finsupp.prod_mapDomain_index_inj (hf : Injective f) : (s.mapDomain f).prod h = s.prod (fun a b => h (f a) b)`
  (`Finsupp/Basic.lean:402`).
* `MvPolynomial.X_injective : Function.Injective (X : σ → MvPolynomial σ R)` —
  applied to `X : Fin N × Fin N → MvPolynomial (Fin N × Fin N) k`. The
  index-type and coefficient-type instantiations are correct: this is the
  same `X` that appears in `polyToTensor`'s monomial basis identification
  (line 268-270 uses `monomial s 1 = basisMonomials (Fin N × Fin N) k s`,
  built from the same `X`).
* `MvPolynomial.prod_X_pow_eq_monomial : ∏ x ∈ s.support, X x ^ s x = monomial s 1`
  (`Mathlib/Algebra/MvPolynomial/Basic.lean:362`) — closes the goal after
  unfolding `Finsupp.prod`.

**No bug.** `X_injective` is applied at the correct variable type.

### Q6 — `tensorBasis` indexing / factor order: **Pass**

```
tensorBasis :
    Module.Basis ((Fin n → Fin N) × (Fin n → Fin N)) k (PolyTensorTgt k N n) :=
  (Basis.piTensorProduct (V)).tensorProduct (Basis.piTensorProduct (V*))
```

`tensorBasis_apply (ij)` (line 147-151) proves
`tensorBasis ij = (tprod (V at ij.1)) ⊗ₜ (tprod (V* at ij.2))`,
matching `Module.Basis.tensorProduct_apply'` from
`Mathlib/LinearAlgebra/TensorProduct/Basis.lean:50`:
`tensorProduct b c i = b i.1 ⊗ₜ c i.2`. So `(ij.1, ij.2)` corresponds
respectively to (V-part, V*-part).

Cross-check against `seqTensor_eq_tensorBasis` (line 154-156):

`seqTensor f` is defined (line 83-85) with V-part `f.2` and V*-part
`f.1` (note the swap: `(f i).2` for V, `(f i).1` for V*). The lemma
states `seqTensor f = tensorBasis (fun l => (f l).2, fun l => (f l).1)`,
so `(ij.1, ij.2) = ((f.2), (f.1))`. Substituting back:

* V-part of `tensorBasis (f.2, f.1)` = `tprod (stdBasis ∘ f.2)` ✓ (matches `seqTensor`)
* V*-part of `tensorBasis (f.2, f.1)` = `tprod (stdDualBasis ∘ f.1)` ✓ (matches `seqTensor`)

And `tensorToPoly` (line 141-144) sends `tensorBasis ij ↦ ∏_l X (ij.2 l, ij.1 l)`,
swapping the indices. Substituting `(ij.1, ij.2) = ((f.2), (f.1))`:
`X (ij.2 l, ij.1 l) = X (f.1 l, f.2 l) = X ((f l).1, (f l).2) = X (f l)`.
✓ Matches `tensorToPoly_seqTensor`'s claim.

The convention is internally consistent: a sequence `f : Fin n → Fin N × Fin N`
has its second coordinate index the V (covariant) factor and its first
coordinate index the V* (contravariant) factor, while the polynomial variable
`X (a, b)` has `a` for the V*-index and `b` for the V-index. This matches the
book's matrix-coefficient convention `g_{i,j} = ⟨e_i*, g e_j⟩`.

### Q7 — `homogeneousPolyToTensor_injective` / `Subtype.ext`: **Pass**

Line 275-287. `apply Subtype.ext` reduces `p = q` (in
`homogeneousSubmodule`) to `p.val = q.val` (the underlying polynomials).
Then `tensorToPoly_polyToTensor_eq_self` is invoked on each side using
`p.property` / `q.property` (the `IsHomogeneous` witness — the subtype
*does* carry homogeneity, so this is the right place to extract it).

`hpq : homogeneousPolyToTensor p = homogeneousPolyToTensor q` is
unfolded to `polyToTensor p.val = polyToTensor q.val` (since the `comp`
with `Submodule.subtype` is just value-projection). Applying
`tensorToPoly` to both sides and substituting via `hp, hq` closes
`p.val = q.val`.

`Subtype.ext` does not drop information here — it only converts equality
of subtype elements to equality of values, and we still hold both
`property` witnesses (used to invoke the left-inverse lemma). Correct
use.

## Recommendations / minor issues (non-blocking)

* **Unused section variable `[CharZero k]` in `prod_X_canonicalSeq`**
  (build linter warning, line 191): the lemma does not use field
  characteristic. It's pulled in because the `variable [CharZero k]`
  declaration at line 167 puts it into auto-included scope. Could be
  fixed with `omit [CharZero k] in` before the lemma, or by reordering
  so `prod_X_canonicalSeq` (which is char-agnostic) appears before line 167.
  Filed as separate follow-up (cosmetic only).

* **`congr 2; exact p.as_sum` ribbon** in `tensorToPoly_polyToTensor_eq_self`
  (line 244-247) is operationally sound but stylistically heavy. The
  `conv_rhs => rw [p.as_sum]` already moved the RHS to sum form; the
  `congr 2; exact p.as_sum` then re-introduces it on the LHS via a
  `show` rewrite. This whole pattern could likely collapse to
  `conv_lhs => rw [p.as_sum]; rw [map_sum, map_sum]`. Not a soundness
  issue — just verbose.

Neither is a correctness concern. No follow-up feature issues required
for soundness.

## Current frontier

* Review of #2502 / issue #2507 complete. **Verdict: Pass on all 7 questions.**
* One follow-up issue filed (linter cleanup, `omit [CharZero k]` in
  `prod_X_canonicalSeq`).
* Sibling equivariance issue #2496 remains claimed by another worker;
  this review does not affect that work.

## Overall project progress

* **Sorries on `main`**: 7 across 4 files (unchanged — review made no
  source changes).
* **Schur-Weyl chain**:
  * #2a construction + injectivity ✅ **and audited as sound**.
  * #2a equivariance (#2496) claimed.
  * Downstream #2478, #2482 can lean on this foundation with
    confidence.

## Next step

* The next planner cycle can confidently keep #2478, #2482 in the
  cascade — the foundational construction is verified.
* If/when #2496 lands, a similar focused review is warranted for the
  equivariance proof (parallel structure: term-by-term match on a
  bijection of `(σ, b) ↔ (τ, c)` permutation+choice pairs).
* The minor linter cleanup follow-up issue can be picked up by any
  worker session.

## Blockers

None.
