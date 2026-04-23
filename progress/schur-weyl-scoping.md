# Scoping: Schur-Weyl / `iso_of_formalCharacter_eq_schurPoly`

**Issue**: https://github.com/FormalFrontier/Etingof-RepresentationTheory-draft1/issues/2440
**Session**: a3e2a585 (Opus 4.7, wave 55)
**Status**: research + decomposition only — **no proof attempt in this PR**.

---

## 1. Executive summary

`EtingofRepresentationTheory/Chapter5/FormalCharacterIso.lean:221` carries the
project's hardest non-framework-wall sorry:

```lean
theorem iso_of_formalCharacter_eq_schurPoly (N : ℕ) (lam : Fin N → ℕ)
    (hlam : Antitone lam)
    (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (h : formalCharacter k N M = schurPoly N lam)
    (h_dim : Module.finrank k M = Module.finrank k (SchurModule k N lam)) :
    Nonempty (M ≅ SchurModule k N lam) := sorry
```

The missing ingredient — exactly as the file's own proof sketch notes — is
**complete reducibility of polynomial GL_N-representations into Schur modules**
(Schur-Weyl duality, Etingof Theorem 5.23.2(i)).

The book's proof route (Etingof §5.23) routes Theorem 5.23.2(i) through
Theorem 5.18.4(iii) (Schur-Weyl decomposition of `V^⊗n`) — most of the
machinery of 5.18.4 is **already formalized** in this project (double
centralizer, semisimplicity of both images, abstract decomposition). The gap
is in **naming** the summands (identifying the abstract `L_i` from
`Theorem5_18_4_decomposition` with the concrete `SchurModule k N λ`) and in
**lifting** the tensor-power decomposition to an arbitrary polynomial rep.

This is not a Mathlib-level multi-month effort. It is an in-project
formalization task of medium size (≈ 4–6 sub-issues; rough total 3–5
worker-sessions of effort assuming each sub-issue holds up). The main risk
is that the abstract `L_i` supplied by `Theorem5_18_4_decomposition` are
existentially produced with `Classical.arbitrary` re-indexing, which may
force the identification step to be rebuilt from `Theorem5_18_1_decomposition`
directly rather than through `5_18_4_partition_decomposition`.

**Recommendation**: decompose into 6 sub-issues (below). Pursue them in
the order listed. Sub-issues 1–3 are parallel-safe; sub-issue 4 consumes
1 and 2; 5 consumes 3; 6 (the original sorry) consumes 4 and 5.

---

## 2. The current state of the sorry

### 2.1 What the signature says

- `k` is a field, algebraically closed, of characteristic zero (from the
  `variable` line).
- `M : FDRep k (GL_N k)` is a finite-dimensional `k`-linear representation.
- `formalCharacter k N M : MvPolynomial (Fin N) ℚ` is a generating
  function for the dimensions of the ℕ-valued weight spaces (defined in
  `Theorem5_22_1.lean:494`). The rationale for working over ℚ and only
  summing ℕ-indexed weights is that the weight lattice of polynomial
  representations is `ℕ^N ⊂ ℤ^N`; non-polynomial summands such as
  `det⁻¹` have no ℕ-valued weights and vanish under `formalCharacter`.
- `h_dim` is the polynomial-ness hypothesis in disguise: by
  `finrank_eq_sum_glWeightSpace` (same file, line 118–149) it is
  equivalent to "the ℕ-valued weight spaces span `M`".

### 2.2 Existing informal proof sketch (lines 215–220)

1. From `h` + `Theorem5_22_1` + `formalCharacter_coeff`: weight space
   dimensions of `M` match those of `SchurModule k N lam` at every
   ℕ-valued weight.
2. From `h_dim`: the ℕ-valued weight spaces span `M` (= `M` is polynomial).
3. **[sorry]** By GL_N-equivariant complete reducibility
   (Schur-Weyl): `M ≅ ⊕ nᵢ · L_{μᵢ}` with each `L_{μᵢ}` a Schur module.
4. Character additivity + `schurPoly_injective`:
   `ch(M) = Σ nᵢ · S_{μᵢ} = S_λ` forces `n_λ = 1`, other `nᵢ = 0`.
5. Therefore `M ≅ L_λ = SchurModule k N lam`.

Steps 1, 2, 4, 5 are in-project infrastructure already (below). Step 3
is the gap.

### 2.3 Character → homogeneity constraint

A useful observation not in the sketch: `schurPoly N lam` is
**homogeneous of degree `n := Σ lam`**, so `h` implies the formal
character of `M` has all monomials of degree `n`. Because
`formalCharacter M = Σ_{μ} (dim M_μ) x^μ`, every weight `μ` with
`M_μ ≠ 0` satisfies `|μ| = n`. In particular, `M` is supported in a
single tensor degree, which lets us embed `M` in `V^⊗n^⊕m` for some
multiplicity `m` — the route that connects back to Schur-Weyl for
`V^⊗n` (Sub-issue 2 below).

---

## 3. Book strategy: Etingof §5.22 + §5.23

### 3.1 What the book assumes

The book uses Schur-Weyl duality by name at
`blobs/Chapter5/Discussion_computing_characters_of_L_lambda.md` to compute
`Tr_{V^⊗n}(g^⊗n · s)` in two ways (giving Theorem 5.22.1, the Weyl
character formula). That computation only needs the abstract
`(S_n × GL(V))`-decomposition of `V^⊗n`, which the project already has
(§3.2 below).

The implicit use of Schur-Weyl for `iso_of_formalCharacter_eq_schurPoly`
is **stronger**: it identifies the abstract `L_λ` from the tensor-power
decomposition with a concrete Schur module, and it lifts the result from
`V^⊗n` to arbitrary polynomial reps. The book gives both steps in
Theorem 5.23.2(i) and its proof (blob
`Discussion_proof_of_Theorem5.23.2.md`):

> "Every element of `R` is a polynomial in `g_{ij}` times a nonpositive
> power of `det(g)`. Thus, `R` is a quotient of a direct sum of
> representations of the form `S^r(V ⊗ V^*) ⊗ (∧^N V^*)^{⊗s}`... So we
> may assume that `Y` is contained in a quotient of a (finite) direct sum
> of such representations. Thus, `Y` is contained in a direct sum of
> representations of the form `V^{⊗n} ⊗ (∧^N V^*)^{⊗s}`, and we are done."

For the **polynomial** case (no `det⁻¹`, i.e. no `∧^N V^*` summands), this
simplifies:

> Every polynomial rep `Y` of degree `≤ n` is a subrepresentation of some
> `(V^⊗n)^m`. Hence by Schur-Weyl applied to `(V^⊗n)^m`, `Y` is a direct
> sum of Schur modules.

Because our `M` is forced to be degree-exactly-`n` by the character
constraint (§2.3), the needed statement collapses further:

> **Key lemma**: every polynomial GL_N-rep of homogeneous degree `n`
> embeds as a direct summand of `(V^⊗n)^m` for some `m`, hence
> decomposes as a direct sum of Schur modules `L_λ` with `|λ| = n`.

This is the exact thing the sub-issue decomposition below targets.

### 3.2 Book items already formalized (status from items.json)

All of these are `sorry_free` in `progress/items.json`, though in one case
the status is misleading (Theorem5.23.2(i), see §4.4):

| Item                            | File                                           | Status     |
|---------------------------------|------------------------------------------------|------------|
| Definition 5.23.1 (algebraic)   | `Chapter5/Definition5_23_1.lean`              | statement-only |
| Theorem 5.18.1 (DCT)           | via `Theorem5_18_4.lean`                       | sorry-free |
| Theorem 5.18.4 (Schur-Weyl)    | `Chapter5/Theorem5_18_4.lean`                  | sorry-free |
| Theorem 5.22.1 (Weyl formula)  | `Chapter5/Theorem5_22_1.lean`                  | sorry-free |
| Proposition 5.22.2 (det twist) | `Chapter5/Proposition5_22_2.lean`              | depends on our sorry |
| Theorem 5.23.2(i) (complete red.) | `Chapter5/Theorem5_23_2.lean`                  | trivial cheat — see §4.4 |
| Theorem 5.23.2(ii) (Peter-Weyl) | `Chapter5/Theorem5_23_2.lean`                  | sorry-free stub |

---

## 4. Project infrastructure survey

### 4.1 In our favour

`EtingofRepresentationTheory/Chapter5/Theorem5_18_4.lean` already contains:

- `Theorem5_18_4_centralizers` (line 268): `symGroupImage = centralizer(diagonalActionImage)` and vice versa. Complete proof.
- `Theorem5_18_4_semisimple` (line 292): both images are semisimple rings. Complete proof.
- `Theorem5_18_4_decomposition` (line 315): `∃ ι, ∃ (S L : ι → Type), V^⊗n ≃ₗ ⊕_ι S_i ⊗ L_i`. Complete but **abstract** — the `L_i` are not identified with `SchurModule`.
- `Theorem5_18_4_partition_decomposition` (line 340): re-indexes by
  `Nat.Partition n` but via `Classical.arbitrary`, so the indexing is
  vacuous (every partition may or may not receive a component).

`EtingofRepresentationTheory/Chapter5/Theorem5_22_1.lean` already contains:

- `SchurModule k N lam` construction (line 320), an irreducible
  polynomial GL_N-rep with character `schurPoly N lam`.
- `formalCharacter_schurModule_eq_schurPoly` (line 2756): the Weyl
  character formula.
- `glWeightSpace_iSupIndep` etc.

`EtingofRepresentationTheory/Chapter5/FormalCharacterIso.lean` already contains:

- `schurPoly_injective` (line 72): equal Schur polynomials ⟹ equal antitone partitions.
- `glWeightSpace_iSupIndep` (line 92): weight spaces are sup-independent.
- `finrank_eq_sum_glWeightSpace` (line 118): polynomial reps
  `⟹ finrank = Σ finrank M_μ`.
- `finrank_eq_of_formalCharacter_eq` (line 154): equal characters
  (+ polynomial-ness) ⟹ equal finrank.

### 4.2 Mathlib dependencies in scope (GREEN — directly usable)

- `Mathlib/CategoryTheory/Preadditive/Schur.lean`: Schur's lemma
  (`isIso_of_hom_simple`, `finrank_hom_simple_simple`).
- `Mathlib/RingTheory/SimpleModule/Basic.lean`: `IsSimpleModule`,
  `IsSemisimpleModule`.
- `Mathlib/RingTheory/SimpleModule/Isotypic.lean`: isotypic
  components, decomposition via `iSupIndep` / `DirectSum`.
- `Mathlib/RepresentationTheory/Maschke.lean`: complete reducibility
  for finite groups (we use it on `S_n`).
- `Mathlib/RepresentationTheory/FDRep.lean`: the `FDRep k G` category.
- `Mathlib/RepresentationTheory/Irreducible.lean`: irreducibility ↔
  `IsSimpleModule k[G] ρ.asModule`.
- `Mathlib/LinearAlgebra/TensorPower/Basic.lean`: tensor power
  infrastructure.

### 4.3 Mathlib gaps (RED — would need to be built from scratch)

- **Schur-Weyl duality for `V^⊗n`** (as a named theorem): absent. We
  build our own in `Theorem5_18_4.lean` — already done at the abstract
  level.
- **GL_N complete reducibility**: absent. We build our own (§3.1).
- **Polynomial vs algebraic representation distinction**: the project
  has its own `IsAlgebraicRepresentation` (Definition 5.23.1) but there
  is no Mathlib counterpart.
- **Formal character = Schur polynomial comparison**: project-specific
  (handled by Theorem 5.22.1 already).

The scoping doc for issue #2440 explicitly noted that this sorry might
"genuinely require a multi-month subproject" if the Mathlib gaps were
deep. The surveys above show **they are not** — the project has already
done the hard Schur-Weyl work at `Theorem5_18_4_decomposition`.

### 4.4 Hazard: `Theorem5_23_2_i` is a cheat

`EtingofRepresentationTheory/Chapter5/Theorem5_23_2.lean:35` "proves"
Theorem 5.23.2(i) as `IsSemisimpleModule k Y`, which is trivially true
because `Y` is a module over a field, **not** because the GL_N action
has a semisimple representation structure. The comment on lines 42–45
explicitly admits this:

> "Every module over a field is semisimple... The representation-theoretic
> content (GL_n-equivariant decomposition into irreducible summands L_λ)
> is captured by the formal character theory in Theorem 5.22.1 rather
> than by this type-theoretic statement."

So in items.json this theorem is `sorry_free` but semantically the
representation-theoretic claim it was supposed to encode is not yet
formalized. **This sub-issue list should also fix that**: sub-issue 5
(equivariant semisimplicity) supersedes the current statement of
`Theorem5_23_2_i` with a stronger one (or posts a sibling theorem
`Theorem5_23_2_i_equivariant`).

---

## 5. Proposed proof decomposition

The target is a `decompose_polynomial_gl_rep` lemma:

```lean
theorem decompose_polynomial_gl_rep (N : ℕ)
    (M : FDRep k (GL_N k))
    (h_top : ⨆ (μ : Fin N →₀ ℕ), glWeightSpace k N M (fun i => μ i) = ⊤) :
    ∃ (m : Antitone (Fin N → ℕ) →₀ ℕ),
      Nonempty (M ≅ ⨁ (λ : {lam // Antitone lam}), (m λ) • SchurModule k N λ.val)
```

(Type-checking the RHS is tedious but the shape is clear.) From this,
`iso_of_formalCharacter_eq_schurPoly` follows by character comparison
(sub-issue 6).

The proof path uses:

**Step A — Degree reduction (sub-issue 1).** Force `M` to be supported
in a single tensor degree `n` by character homogeneity:
if `formalCharacter M = schurPoly N lam`, every weight `μ` of `M`
satisfies `|μ| = |lam| =: n`. This is a one-lemma item.

**Step B — Embedding in tensor powers (sub-issue 2).** Show that a
homogeneous degree-`n` polynomial GL_N-rep `M` is isomorphic to a direct
summand (equivalently, a subrep, in characteristic zero) of some
`(V^⊗n)^m`. The book's proof (Theorem 5.23.2) gives this via the
double-dual / matrix-coefficient embedding into `R` (the coordinate
ring) and truncation by homogeneity degree. A cleaner alternative in
characteristic zero: reproduce the classical construction of a
polynomial rep as the image of a GL_N-equivariant map from a
tensor-power sum (universal property of symmetric and alternating
powers in each irreducible's construction).

**Step C — Identifying the abstract `L_i`** (sub-issue 3). Establish
that the `L_i` produced by `Theorem5_18_4_decomposition` are (up to
iso) exactly the `SchurModule k N λ` for antitone `λ` of size `n` with
at most `N` nonzero parts. This requires:

- Each `SchurModule k N λ` appears as some `L_i`.
- Each nonzero `L_i` is some `SchurModule k N λ`.
- The association is bijective.

The book's proof (Theorem 5.22.1 discussion) does this via character
matching: the `L_i` are mutually nonisomorphic irreducible polynomial
GL_N-reps, and `SchurModule k N λ` are also mutually nonisomorphic
(their characters, the Schur polynomials, are linearly independent by
the strengthening of `schurPoly_injective`).

**Step D — Linear independence of Schur polynomials (sub-issue 4).**
Strengthen `schurPoly_injective` to: the Schur polynomials
`{S_λ : λ antitone, |λ| = n, length(λ) ≤ N}` are linearly independent in
`MvPolynomial (Fin N) ℚ`. This is needed in sub-issue 5 and 6 to
conclude multiplicity vectors are unique. Standard proof via the
Vandermonde identity (`schurPoly_mul_vandermonde`) reducing to
linear independence of alternants, which is classical.

**Step E — Equivariant semisimplicity (sub-issue 5).** The statement

```lean
theorem polynomial_gl_rep_isSemisimple (N : ℕ)
    (M : FDRep k (GL_N k))
    (h_top : ⨆ (μ : Fin N →₀ ℕ), glWeightSpace k N M (fun i => μ i) = ⊤) :
    IsSemisimple (category-theoretic sense)
```

is the GL_N-equivariant reformulation of "completely reducible". This
bundles sub-issues B + C: embed `M` in `(V^⊗n)^m` via Step B, apply
`Theorem5_18_4_decomposition` + `Theorem5_18_4_semisimple` to
`(V^⊗n)^m`, restrict the decomposition to `M`, and identify the
summands via Step C.

**Step F — Assembly (sub-issue 6).** With the decomposition from Step E
and linear independence from Step D, close the original sorry by
character matching (Step 4–5 of the existing informal sketch, which are
straightforward given the infrastructure).

---

## 6. Sub-issue list

Below, the titles are ready for `coordination plan --label feature`.
Each body would be expanded to the standard Current state / Deliverables
/ Context / Verification format before posting (this scoping doc is the
**plan** — a separate planner cycle posts the sub-issues, or this PR's
reviewer may request that the agent's planner pass do it).

### Sub-issue list

1. **`Schur-Weyl scoping: derive tensor-degree homogeneity from character = Schur polynomial`** — Prove: if `formalCharacter k N M = schurPoly N lam` with antitone `lam`, then every weight of `M` has magnitude `|lam|`. Depends on: `schurPoly_homogeneous` (sub-lemma — may already be in-project under a different name) and `formalCharacter_coeff`. Expected size: 1 worker-session.

2. **`Schur-Weyl scoping: embed homogeneous polynomial GL_N-rep into (V^⊗n)^m`** — Given a finite-dim polynomial GL_N-rep `M` with all weights at degree `n`, construct a GL_N-equivariant injection `M ↪ (V^⊗n)^m` for some `m`. Depends on: `IsAlgebraicRepresentation` (Definition 5.23.1) + basic algebraic-rep infrastructure. Likely the largest sub-issue — expected 1–2 worker-sessions.

3. **`Schur-Weyl scoping: identify Theorem5_18_4 L_i summands with SchurModule k N λ`** — Refine `Theorem5_18_4_decomposition` / `_partition_decomposition` to produce a canonical iso to `⊕_{λ antitone, |λ|=n, length≤N} (Specht_λ ⊗ SchurModule k N λ)`. Depends on: `Theorem5_18_4_partition_decomposition`, `schurModule_weight_eq_schurPoly_coeff` (Theorem 5.22.1 helper). Expected 1 worker-session.

4. **`Schur-Weyl scoping: linear independence of Schur polynomials`** — Strengthen `schurPoly_injective` to `LinearIndependent ℚ {schurPoly N lam : lam ∈ Antitone}` (suitably restricted to at-most-N-part partitions of a fixed size). Use `schurPoly_mul_vandermonde` + linear independence of alternants. Expected 1 worker-session.

5. **`Schur-Weyl scoping: polynomial GL_N-rep decomposes as direct sum of Schur modules`** — State and prove `decompose_polynomial_gl_rep` using sub-issues 2 + 3 (and therefore 1 transitively). This also fixes the `Theorem5_23_2_i` cheat (§4.4) by providing the representation-theoretic content. Expected 1–2 worker-sessions.

6. **`Schur-Weyl scoping: close iso_of_formalCharacter_eq_schurPoly (wraps sub-issues 1–5)`** — Close the original sorry at `FormalCharacterIso.lean:221` using sub-issues 4 + 5 and the existing infrastructure (informal Steps 1, 2, 4, 5 of the file's own sketch). Expected 0.5 worker-sessions given the preceding sub-issues.

### Dependency graph

```
┌────┐    ┌────┐    ┌────┐   ┌────┐
│ #1 │    │ #2 │    │ #3 │   │ #4 │
└─┬──┘    └─┬──┘    └─┬──┘   └─┬──┘
  │         │         │        │
  │         └────┬────┘        │
  │              ▼             │
  │          ┌────┐            │
  └────────► │ #5 │            │
             └─┬──┘            │
               │               │
               ▼               │
             ┌────┐            │
             │ #6 │ ◄──────────┘
             └────┘
```

- `#1`, `#2`, `#3`, `#4` have no prerequisites within this set and can
  be worked in parallel.
- `#5` consumes `#1`, `#2`, `#3` (and trivially `#2` consumes `#1` since
  the embedding uses homogeneity).
- `#6` consumes `#5` and `#4`.

Practically: `#1` and `#4` are short and can be first; `#2` is the
longest and should be started early; `#3` bridges the existing
`Theorem5_18_4` infrastructure to concrete Schur modules and is the
conceptual crux.

### Difficulty per sub-issue

| # | Estimated worker-sessions | Risk of wall           | Remarks                                          |
|---|---------------------------|------------------------|--------------------------------------------------|
| 1 | 0.5                       | low                    | Single fact about homogeneity of `schurPoly`.    |
| 2 | 1–2                       | **medium-high**        | Relies on degree-truncation inside algebraic reps; needs care with the double-dual embedding or a direct Schur-functor construction. |
| 3 | 1                         | low-medium             | Character comparison; existing infrastructure mostly suffices.  |
| 4 | 1                         | low                    | Classical alternant argument; mirrors `schurPoly_injective`.    |
| 5 | 1–2                       | medium                 | Assembly — depends heavily on the APIs exposed by `#2` and `#3`. |
| 6 | 0.5                       | low                    | A straightforward wrap once 4 + 5 exist.         |
| — | **5–8 total**             |                        |                                                  |

### Total effort estimate

**5–8 worker-sessions.** This is substantially less than the "multi-month
Mathlib subproject" feared by the scoping issue, because the hardest
pieces of Schur-Weyl are already done in this project. The risk concentrates
on sub-issue #2 — the embedding of a polynomial rep into a tensor power —
which is where the gap between "formal character equals a Schur polynomial"
and "actual subrep of V^⊗n" has to be closed. A fresh worker on #2 should
read the book's proof of Theorem 5.23.2 and Etingof's Definition 5.23.1
(algebraic representation) carefully, and may elect to prove the
homogeneous-polynomial case via the Schur functor construction rather than
matrix-coefficient coordinate ring truncation.

### Walls / known risks

- **Sub-issue 2 could wall** if the embedding into `(V^⊗n)^m` turns out
  to require more infrastructure than anticipated (e.g. if the
  coordinate-ring approach needs `GLCoordinateRing` properties the
  current file does not expose). Mitigation: the worker on #2 should
  stop and `coordination skip` after the standard 3-attempt threshold if
  the embedding lemma resists both the coordinate-ring and the Schur-functor
  approaches. No immediate Option B is known; skipping forces a
  re-planning cycle.

- **Sub-issue 3 could wall** if `Theorem5_18_4_partition_decomposition`'s
  use of `Classical.arbitrary` makes the summand identification
  unreachable. Mitigation: reuse `Theorem5_18_1_decomposition` (the
  upstream form) directly; the `partition_decomposition` is just a
  re-indexing and can be rebuilt non-trivially.

- **The `Theorem5_23_2_i` cheat** (§4.4) is a latent correctness issue.
  Sub-issue 5 should either supersede it with a stronger statement or
  open a separate issue to mark it for amendment. Recommend **strengthening
  the statement in place** as part of sub-issue 5's PR: change the
  signature of `Theorem5_23_2_i` to require the GL_n-equivariant
  decomposition into Schur modules, and update any callers (there
  should be few or none, since the current statement is vacuous).

---

## 7. Open questions / items for human review

- Is the scope of sub-issue 2 (embedding) too ambitious for one session?
  An alternative is to split it into "2a: matrix-coefficient / coordinate-ring
  approach" and "2b: apply to polynomial reps with character constraint".
  The scoping session recommends leaving this as a single issue and letting
  the worker decompose further via the standard Step-4b procedure if
  they judge so mid-session.

- Should sub-issue 5 include `Theorem5_23_2_i` replacement in the
  same PR, or open a sibling issue? The recommendation above is
  "same PR" because the current cheat is actively misleading and leaves
  the project less honest than it should be. But if the resulting PR
  grows too large, splitting into two is fine.

- The Peter-Weyl part Theorem 5.23.2(ii) is out of scope for this issue
  entirely — it would be a separate sub-issue (or sub-subproject)
  requiring the `GLCoordinateRing` infrastructure currently only
  scaffolded in `Theorem5_23_2.lean`.

---

## 8. No code changes in this PR

Per the issue scope: this PR creates only this scoping document. No
change to `FormalCharacterIso.lean`. No proof attempt. The next
planner cycle (or a manual planner invocation) should post sub-issues
1–6 based on §6. Proofs begin only when individual sub-issues are
claimed and worked.

This matches the issue-body deliverable: a concrete plan a follow-up
planner can act on, with a Mathlib survey, a book survey, a dependency
graph, difficulty estimates, and an actionable decomposition.
