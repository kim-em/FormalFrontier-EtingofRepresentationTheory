## Current state

The proof of `iso_of_formalCharacter_eq_schurPoly`
(`FormalCharacterIso.lean:221`) uses the fact that Schur polynomials
are linearly independent (not merely injective as a function). The
existing in-project result `schurPoly_injective`
(`FormalCharacterIso.lean:72`) gives "equal Schur polynomials ⟹ equal
antitone partitions"; we need the stronger **Schur-Weyl sub-issue 4**
(`progress/schur-weyl-scoping.md`, Step D).

Linear independence is the classical Vandermonde / alternant argument
and is low-risk. It is needed by later Schur-Weyl sub-issues #5
(equivariant semisimplicity + multiplicity extraction) and #6 (final
assembly of the iso).

## Deliverables

Add a linear-independence theorem to
`EtingofRepresentationTheory/Chapter5/FormalCharacterIso.lean` (or a
neighbouring helper file — author's choice):

```lean
/-- The Schur polynomials `{schurPoly N lam : lam antitone}` are
linearly independent in `MvPolynomial (Fin N) ℚ`. -/
theorem schurPoly_linearIndependent (N : ℕ) :
    LinearIndependent ℚ (fun (lam : {lam : Fin N → ℕ // Antitone lam}) =>
      schurPoly N lam.val) := sorry
```

**Proof outline** (scoping doc §5 Step D):

1. `schurPoly N lam * vandermonde N = alternant(lam + δ)` where
   `δ = (N-1, N-2, …, 0)` and `alternant(μ)` is the Weyl alternant
   polynomial. Look up `schurPoly_mul_vandermonde` in-project (or
   prove it — it is the core ingredient of `schurPoly_injective`).
2. Alternants `{alternant(lam + δ) : lam antitone}` are linearly
   independent because they are indexed by distinct strictly-decreasing
   compositions `lam + δ` and each has a single leading monomial that
   determines it.
3. Multiplying by a nonzero polynomial (`vandermonde N`) preserves
   linear independence, so Schur polynomials are linearly independent.

**If `schurPoly_mul_vandermonde` or similar is not in the project**,
you may need to prove that as a helper — include it as a private
lemma or split into a further sub-issue (leave a `Decomposed into
#<sub>, #<this>` breadcrumb).

**Alternative approach** (if the Vandermonde route is too heavy): use
character evaluation on the diagonal matrices. Two distinct antitone
partitions give distinct characters on any sufficiently generic
diagonal matrix, and linear independence of characters on a single
such element suffices (classical Dedekind argument).

## Context

- Scoping doc: `progress/schur-weyl-scoping.md`, Step D / sub-issue 4
  (lines 316–378).
- Source sorry: `EtingofRepresentationTheory/Chapter5/FormalCharacterIso.lean:221`
  (`iso_of_formalCharacter_eq_schurPoly`).
- Existing related results:
  - `schurPoly_injective` (`FormalCharacterIso.lean:72`) — the weaker
    form this issue strengthens.
  - `schurPoly_mul_vandermonde` — check if present; if yes, use as-is,
    if not, prove as a helper.
- Not a Mathlib gap: classical commutative-algebra content.

## Verification

- `lake build EtingofRepresentationTheory.Chapter5.FormalCharacterIso`
  (or the chosen file) succeeds.
- Full `lake build` succeeds.
- New theorem has zero sorries.
- `schurPoly_injective` should either become a corollary of the new
  result, or remain as-is (no refactor required).
