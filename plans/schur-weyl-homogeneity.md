## Current state

The proof of `iso_of_formalCharacter_eq_schurPoly`
(`FormalCharacterIso.lean:221`) requires first establishing that a
polynomial GL_N-rep with character equal to a Schur polynomial is
homogeneous of the right tensor degree. This is **Step A / sub-issue 1**
of the Schur-Weyl scoping plan in `progress/schur-weyl-scoping.md`
(closed issue #2440 / PR #2442).

The lemma is needed by later Schur-Weyl sub-issues (embedding into
`V^⊗n`, identifying abstract `L_i` with `SchurModule`, and the final
assembly). It is the shortest and lowest-risk of the six sub-issues.

## Deliverables

Add a lemma to an appropriate location in Chapter5 (likely
`FormalCharacterIso.lean` immediately before
`iso_of_formalCharacter_eq_schurPoly`, or a helper file if one is
preferred by the author of PR #2442):

```lean
/-- If a finite-dim polynomial GL_N-rep has formal character equal to
`schurPoly N lam` for an antitone partition `lam`, then every weight
`μ` of `M` has magnitude `|μ| = |lam|`. -/
lemma weight_magnitude_of_formalCharacter_eq_schurPoly
    (N : ℕ) (lam : Fin N → ℕ) (hlam : Antitone lam)
    (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (h : formalCharacter k N M = schurPoly N lam)
    (μ : Fin N → ℕ) (hμ : 0 < Module.finrank k (glWeightSpace k N M μ)) :
    ∑ i, μ i = ∑ i, lam i := sorry
```

**Proof outline** (see `progress/schur-weyl-scoping.md` §5 Step A):

1. `schurPoly` is a homogeneous polynomial of total degree `|lam| =
   ∑ lam i` — this is classical and should be derivable from the
   `schurPoly` definition plus the Vandermonde / alternant
   presentation. If not already available in-project, prove a
   stand-alone `schurPoly_isHomogeneous` lemma as a helper.
2. `formalCharacter k N M` is the generating function
   `∑_μ dim(M_μ) · x₁^{μ₁} · … · x_N^{μ_N}`
   (see `Theorem5_22_1.lean:494`). Its monomials occur exactly at
   weights `μ` of `M` with nonzero multiplicity. Equality with the
   homogeneous `schurPoly` forces all nonzero-dim weights to have the
   same magnitude `|lam|`.

A companion corollary `weight_magnitudes_equal_of_formalCharacter_eq_schurPoly`
(degree homogeneity of `M`) may naturally pair with this — optional.

## Context

- Scoping doc: `progress/schur-weyl-scoping.md`, Step A / sub-issue 1
  (lines 316–378 of that file).
- Source sorry: `EtingofRepresentationTheory/Chapter5/FormalCharacterIso.lean:221`
  (`iso_of_formalCharacter_eq_schurPoly`).
- Project infrastructure:
  - `schurPoly` (definition: `Chapter5/SchurPoly.lean` — search for it).
  - `formalCharacter` (`Chapter5/Theorem5_22_1.lean:494`).
  - `formalCharacter_coeff` (same file).
  - `schurPoly_injective` (`FormalCharacterIso.lean:72`) — analogue in
    stronger form.
- Not a Mathlib gap: this is all in-project infrastructure.

## Verification

- `lake build EtingofRepresentationTheory.Chapter5.FormalCharacterIso`
  succeeds (or the chosen helper file, if placed elsewhere).
- Full `lake build` succeeds.
- New lemma has zero sorries.
- Does not modify `iso_of_formalCharacter_eq_schurPoly` itself;
  closing that sorry is sub-issue 6 (not in scope here).
