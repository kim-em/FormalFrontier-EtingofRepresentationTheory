## Current state

`Theorem5_18_4_decomposition` (`Chapter5/Theorem5_18_4.lean:315`) gives
an abstract decomposition `V^⊗n ≃ ⊕_i S_i ⊗ L_i` with the summands
existentially produced. `Theorem5_18_4_partition_decomposition`
(line 340) attempts to index by `Nat.Partition n` but uses
`Classical.arbitrary`, making the indexing vacuous. **Schur-Weyl
sub-issue 3** from `progress/schur-weyl-scoping.md` (§5 Step C) asks
us to canonicalize the `L_i` as actual Schur modules.

This is the "conceptual crux" of the Schur-Weyl gap: it replaces the
unnamed `L_i` with explicit `SchurModule k N λ` objects, which is what
the final assembly sub-issues (#5, #6) need.

## Deliverables

Add to `EtingofRepresentationTheory/Chapter5/Theorem5_18_4.lean` (or a
neighbouring file) a refinement of `_partition_decomposition` that
canonically identifies the `L_i` with Schur modules:

```lean
/-- The `L_i` summands in `Theorem5_18_4_decomposition` (viewed as a
GL_N-rep decomposition of `V^⊗n`) are exactly the Schur modules
`SchurModule k N lam` for antitone `lam` with `|lam| = n` and at most
`N` nonzero parts. -/
theorem schurWeyl_gl_decomposition (N n : ℕ) :
    Nonempty (TensorPower k n (Fin N → k) ≃ₗ[k]
      ⨁ (lam : {lam : Fin N → ℕ // Antitone lam ∧ ∑ i, lam.val i = n}),
        Specht ℂ lam.val ⊗[ℂ] SchurModule k N lam.val) := sorry
```

Exact statement form is at the author's discretion — what matters is
that the GL_N-equivariant component of the decomposition is indexed by
antitone partitions and the summands are the concrete `SchurModule`
construction.

**Proof outline** (scoping doc §5 Step C):

1. Start from `Theorem5_18_4_decomposition` applied to `V = Fin N → k`.
2. Compute the formal character of each abstract `L_i` using
   character additivity: `character(V^⊗n) = Σ dim(S_i) · character(L_i)`.
3. Identify each `character(L_i)` as a Schur polynomial `schurPoly N lam`
   using Theorem 5.22.1 and the observation that each `L_i` is an
   irreducible polynomial GL_N-rep of degree `n`.
4. Use the (to-be-filed) sub-issue #4 result
   (`schurPoly_linearIndependent`) to conclude that the `L_i` are
   mutually non-isomorphic and exhaust the Schur modules of degree `n`.
5. Construct the canonical iso from `L_i` to `SchurModule k N lam` via
   either character-uniqueness (Schur's lemma + simple module
   classification) or by showing both are highest-weight modules for
   the same weight.

**Scope warning**: this may be large (1+ sessions). If you hit the
3-attempt threshold on any sub-step, decompose further with a
`Decomposed into #A, #B` breadcrumb before `coordination skip`.
Likely sub-splits: (i) character match of one `L_i` with one
`SchurModule`; (ii) assembly of the iso.

## Context

- Scoping doc: `progress/schur-weyl-scoping.md`, Step C / sub-issue 3
  (lines 316–378).
- Source sorry: `EtingofRepresentationTheory/Chapter5/FormalCharacterIso.lean:221`
  (`iso_of_formalCharacter_eq_schurPoly`).
- Project infrastructure available:
  - `Theorem5_18_4_decomposition` (`Theorem5_18_4.lean:315`) — abstract.
  - `Theorem5_18_4_partition_decomposition` (`Theorem5_18_4.lean:340`) —
    the re-indexed but vacuous version; this issue may replace or
    supersede it.
  - `SchurModule k N lam` (`Theorem5_22_1.lean:320`).
  - `formalCharacter_schurModule_eq_schurPoly` (`Theorem5_22_1.lean:2756`).
  - `schurPoly_injective` (`FormalCharacterIso.lean:72`).
- **Depends on**: sub-issue #4 (`schurPoly_linearIndependent`) filed
  alongside this. You may prove a local lemma while that issue is
  pending (use `sorry` as a stand-in and remove once #4 lands — track
  the dependency in your PR description).

## Verification

- `lake build EtingofRepresentationTheory.Chapter5.Theorem5_18_4`
  (or relevant file) succeeds.
- Full `lake build` succeeds.
- New theorem has zero sorries (modulo the #4 dependency noted above).
- Existing `Theorem5_18_4_partition_decomposition` either deleted
  (if fully superseded) or left as a corollary of the new result.
