## Current state

`Chapter5/FormalCharacterIso.lean` has had two recent self-contained
additions land **without a dedicated review issue**:

- **PR #2516** (`a0fc873`, closing #2492 — Schur-Weyl L_i part B,
  formalCharacter additivity). +146 lines. Introduces
  - `noncomputable def glWeightSpace_directSum_equiv` (line 517) — the
    linear equivalence
    `(weight space of directSum ρᵢ) ≃ ⨁ (weight space of ρᵢ)`
  - `theorem formalCharacter_directSum` (line 583) — additivity of the
    formal character over `Representation.directSum`
  - `theorem formalCharacter_eq_of_rep_iso` (line 633) — invariance under
    rep isomorphism

- **PR #2534** (`c8b7b74`, closing #2514 — Schur-Weyl L_i part B,
  trivial-tensor multiplicativity). +140 lines. Introduces
  - `theorem formalCharacter_trivialTensor` (line 653) — the formal
    character of a trivial-action tensor representation factors as
    `dim S · char L`

Both PRs are **fully closed** (their parent issues #2492 / #2514 are
closed). A third PR on the same file (#2542, partial on #2515 — character
identity skeleton) introduced sorry'd statements at lines 758 / 796 and
is **not** in scope for this audit; the file's two existing sorries
(line 399 in `iso_of_formalCharacter_eq_schurPoly`, line 774 in
`glTensorRep_equivariant_schurWeyl_decomposition`) are also out of scope
— they are owned by other open issues.

These additions are character-level building blocks that the Schur-Weyl
chain assembly (#2493 → #2482) will compose. Audit them before the chain
bottoms out so any structural finding propagates while the chain is still
blocked.

## Deliverables

Audit the additions from PRs #2516 + #2534 and post **one consolidated
review comment** answering all of the following.

### Q1 — `glWeightSpace_directSum_equiv` (PR #2516)

The construction realises a weight space of `Representation.directSum ρᵢ`
as the direct sum of the individual weight spaces.

- Is the construction definitionally correct? In particular, does it
  respect the `GL_N`-weight grading on each summand (i.e. it does not
  silently swap the role of `i` and the weight `μ`)?
- Are the hypotheses minimal — `[Fintype ι] [DecidableEq ι]
  [∀ i, Module.Finite k (M i)]` — or does the proof use anything stronger?
- Is there a simpler one-liner using existing Mathlib API
  (`Module.Submodule.equiv_directSum`-style)? If so, propose a follow-up
  cleanup; do not change the construction in this audit.

### Q2 — `formalCharacter_directSum` (PR #2516)

This is the headline lemma — additivity of `formalCharacter` over
`Representation.directSum`.

- Does the proof correctly route through `glWeightSpace_directSum_equiv`
  to extract the dimension identity
  `finrank (weightSpace μ (directSum ρᵢ)) = ∑ i, finrank (weightSpace μ ρᵢ)`?
- Is the cast to `ℚ` (the codomain of `formalCharacter`) handled cleanly?
  Are there hidden `Nat → Rat` coercions that should be `Nat.cast_sum`
  away from the `simp` set?
- Is there an unnecessary `[CharZero k]` or `[Field k]` hypothesis? The
  construction is purely linear-algebraic over a commutative ring with
  character-level rationality.

### Q3 — `formalCharacter_eq_of_rep_iso` (PR #2516)

A naturality lemma: equivalent representations have equal formal
characters.

- Does the proof use the *correct* notion of "rep isomorphism" — i.e.
  a `GL_N`-equivariant linear equivalence — and not just a linear
  equivalence forgetting the action?
- Is the statement in the most general form needed by downstream
  consumers (`#2482`, `#2493`)? If `glTensorRep_equivariant_schurWeyl_decomposition`
  produces a different shape of iso (e.g. via `FDRep` morphisms), is
  `formalCharacter_eq_of_rep_iso` directly applicable, or will the
  capstone need a small bridge lemma?

### Q4 — `formalCharacter_trivialTensor` (PR #2534)

The trivial-tensor multiplicativity lemma:
`char ((triv k G S) ⊗ L.ρ) = (dim S) • char L`.

- Is the lemma's assumption that `S` carries the *trivial* `G`-action
  used correctly throughout the proof? (No silent assumption that `S`
  is a non-trivial rep.)
- Does the `dim S • char L` conclusion match the form that
  `formalCharacter_tensorPower_eq_sum_character_L` (line 796, downstream)
  will need to compose with `formalCharacter_directSum` to produce
  `∑ᵢ dim(Sᵢ) · char(Lᵢ)`?
- Are there missed simp normal-form opportunities (e.g. `dim S` written
  as `Module.finrank k S` vs `FiniteDimensional.finrank k S`)? Flag any
  inconsistency between the two recent PRs.

## Context

- File under audit:
  - `EtingofRepresentationTheory/Chapter5/FormalCharacterIso.lean`
- Commits:
  - `a0fc873` (PR #2516, formalCharacter additivity)
  - `c8b7b74` (PR #2534, trivial-tensor multiplicativity)
- Out of scope (do **not** review in this audit):
  - PR #2542 (`586e666`) — partial, character-identity skeleton
  - Pre-existing sorries at lines 399, 774 (owned by #2483, #2542)
- Downstream consumers waiting on this:
  - #2493 (Schur-Weyl L_i part C, blocked on #2540)
  - #2482 (Schur-Weyl #5, blocked on #2493)
- Critical-path note: this audit is independent of the in-flight Wall 3
  PRs (#2541 / #2550) and the claimed bimodule decomposition (#2540), so
  it can run in parallel.

## Verification

- `lake build EtingofRepresentationTheory.Chapter5.FormalCharacterIso`
  succeeds (no behavior changes from this audit).
- One review comment posted on the issue answering Q1 / Q2 / Q3 / Q4.
- For each `PASS` answer: explicit confirmation.
- For each `FAIL` or follow-up finding: a separate `review-finding` issue
  filed (small, one-shot, not blocking this audit).
- Audit is `PASS` if all four deliverables stand up to scrutiny modulo
  any review-findings filed.
