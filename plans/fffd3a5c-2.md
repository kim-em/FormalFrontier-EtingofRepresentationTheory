## Current state

PR #2502 (merged 2026-04-24T04:19:18Z, commit `db52a50`) landed the
**construction + injectivity** portion of Schur-Weyl sub-issue #2a,
in a new file
`EtingofRepresentationTheory/Chapter5/PolynomialTensorBridge.lean`
(~1200 lines, fully sorry-free). This file is the foundation of the
Schur-Weyl chain's "#2" step — the bridge from homogeneous-degree-n
polynomials in matrix entries into `V^⊗n ⊗ (V^*)^⊗n`.

The sibling issue #2496 (GL_N-equivariance of the same bridge) is
currently claimed. Downstream issues #2478 (Schur-Weyl #2b, matrix
coefficients) and #2482 (Schur-Weyl #5, polynomial GL_N-rep
decomposition) all rely on this construction. Before those land it is
worth an independent audit: the constructions are **non-trivial linear
algebra** (`seqTensor`, `symTensor` with the `(1/n!) · Σ_σ` symmetriser,
`canonicalSeq` via `Finsupp.toMultiset.toList`, `tensorBasis`,
`tensorToPoly`) and the left-inverse chain has several delicate
rewrites (`Finsupp.prod_mapDomain_index_inj`, `MvPolynomial.X_injective`,
`Finsupp.prod_toMultiset`).

## Deliverables

Audit the merged code in
`EtingofRepresentationTheory/Chapter5/PolynomialTensorBridge.lean`.
Answer in writing:

1. **`seqTensor` / `symTensor` sanity**: `symTensor f := (1/n!) Σ_σ seqTensor (f ∘ σ)`
   is the characteristic-zero symmetriser. Verify:
   - it is invariant under post-composition with a permutation
     (`symTensor_comp_perm`) — does the proof hold?
   - the `1/n!` scalar is correct (not `1/(n-1)!` or similar off-by-one).
2. **`canonicalSeq` well-definedness**: `canonicalSeq s hs` picks the
   i-th element of `(Finsupp.toMultiset s).toList`. For `s : Fin N × Fin N →₀ ℕ`
   with `|s| = n`, does the output have length exactly `n`? Is the
   list-index proof obligation provably discharged, or does it rely on
   a classical-choice artefact?
3. **`multisetToTensor` handles `|s| ≠ n`**: the `if-then-else` branch
   returns `0` when the support size doesn't match. Verify the
   `tensorToPoly_multisetToTensor` statement covers both branches
   correctly, in particular that `0 ↦ 0` in the off-diagonal case.
4. **Left-inverse chain**: `tensorToPoly_polyToTensor_eq_self (p, hp : p.IsHomogeneous n)`
   proves `tensorToPoly (polyToTensor p) = p`. Trace through the
   `MvPolynomial.as_sum` → `Finsupp.prod_toMultiset` → monomial path.
   Does the homogeneity hypothesis `hp` get genuinely used (to discharge
   the `if |s| = n then … else 0` branch), or is it vestigial?
5. **`prod_X_canonicalSeq` key identity**: this is "the key identity"
   per the worker's session notes
   (`progress/20260424T041559Z_fe4ae311.md`). Verify that the chain
   `∏ l : Fin n → List.ofFn → (toMultiset s).toList.map X → multiset prod →
    Finsupp.toMultiset_map → Finsupp.prod_toMultiset →
    Finsupp.prod_mapDomain_index_inj MvPolynomial.X_injective →
    MvPolynomial.prod_X_pow_eq_monomial` actually discharges the goal.
   If any step relies on `MvPolynomial.X_injective` being applied to the
   wrong variable type, that's a bug.
6. **Type of `tensorBasis`**: does `tensorBasis : Module.Basis ((Fin n → Fin N) × (Fin n → Fin N)) k _`
   really index the tensor product basis correctly? In particular, check
   the order of factors matches what `tensorToPoly` assumes.
7. **`homogeneousPolyToTensor_injective`**: the final injectivity
   theorem. Is the `Subtype.ext` use correct, or does it accidentally
   project away information that was needed?

**Output**: A review progress file
`progress/<timestamp>_polynomial-tensor-bridge-review.md` with
findings per each of the 7 questions above (Pass / Issue / Recommendation).
For any Issue, file a follow-up feature issue referencing this review.

## Context

- Merged PR: #2502 (commit `db52a50`).
- Parent issue: #2477 (closed as decomposed; sibling residual #2496).
- Worker session notes:
  `progress/20260424T041559Z_fe4ae311.md` — detailed breakdown of the
  left-inverse construction, especially the `prod_X_canonicalSeq`
  identity and its rewrite chain.
- Scoping document: `progress/schur-weyl-scoping.md` §5 Step D.
- Downstream consumers (blocked): #2478 (embedding into `(V^⊗n)^m`),
  #2482 (polynomial GL_N-rep decomposition), #2496 (equivariance).
- Precedent: #2486 (bimodule foundation review) correctly caught a
  B-linearity drift (→ #2489). Same workflow applies here.

## Verification

- `lake build EtingofRepresentationTheory.Chapter5.PolynomialTensorBridge`
  succeeds at HEAD (should be a no-op; already built).
- Each of the 7 questions above is answered in the review progress file.
- Any follow-up issues are filed with clear reference to this review
  and to the specific definition / theorem they patch.

## Scope

- 1 worker-session of careful reading, possibly with a few `#check` /
  `#eval` sanity checks. No new proofs expected.
- Pure review — do not modify any Lean source; fixes go into
  follow-up feature issues.
