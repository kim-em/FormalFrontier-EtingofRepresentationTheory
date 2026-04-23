# Ẽ₆ / Ẽ₇ / T(1,2,5) Indecomposability Framework Investigation

**Session:** `9981829f-5619-46b6-9594-6401b8fa2124` (meditate, issue #2430)
**Date:** 2026-04-23
**Status:** Framework is mathematically unsound. Explicit counter-examples
for both `etilde7Rep 1` and `t125Rep 1` constructed below.

## TL;DR

All three constructions (`etilde6v2Rep`, `etilde7Rep`, `t125Rep`) share the
same fatal design pattern: a single nilpotent twist `N` on one arm of an
affine-Dynkin quiver, hoping that "N ≠ 0" forces indecomposability.

**It doesn't.** The twist only hits the `⟨e₀, …, e_{m-1}⟩` sub-block of
its target, leaving the `e_m` direction uncoupled. That one direction is
enough to peel off a 1-dimensional complementary summand at the center,
giving a non-trivial decomposition for every `m ≥ 1`.

The explicit Ẽ₆ counter-example on #2417 already refuted
`etilde6v2Rep_isIndecomposable`. This note:

1. **Confirms** the same failure mode refutes `etilde7Rep 1` and
   `t125Rep 1` (explicit decompositions below).
2. **Explains** why `d5tildeRep_isIndecomposable` *does* work (γ is an
   iso between the two centers; there is no analogous bridge in Ẽ₆/₇/₈
   or T(p,q,r)).
3. **Compares** with the book: Etingof's infinite-type proof for affine
   Dynkin quivers (Problem 6.1.5 + Problem 6.1.2) is an *orbit-counting
   argument over the Tits form*, not an explicit-rep construction.
4. **Recommends** dropping explicit `etilde{6,7,8}Rep_isIndecomposable` /
   `t125Rep_isIndecomposable` in favor of either (a) the book's Tits-form
   argument or (b) a structurally stronger explicit construction with
   multiple coupling twists. Sketches both.

## 1. Counter-example for `etilde7Rep 1`

### Setup

For `m = 1`, `ℂ^{m+1} = ℂ²` with basis `e₀, e₁`.
`N : ℂ² → ℂ²` is nilpotent shift: `N e₀ = 0`, `N e₁ = e₀`.
So `N(ℂ²) = ⟨e₀⟩` (1-dim, missing the `e₁` direction).

Vertex dims:

| v | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 |
|---|---|---|---|---|---|---|---|---|
| dim | 8 | 4 | 6 | 4 | 2 | 6 | 4 | 2 |

Decompose `V(0) = ℂ⁸ = A ⊕ B ⊕ C ⊕ D` (each `ℂ²`).
Arrows (sink orientation, all into 0):

- `1→0`: `(p,q) ↦ (p+q, p, q, Nq)` (the only N-twisted map)
- `4→3→2→0`: `starEmbed1 ∘ embed2to3_AB ∘ embed3to4_ABC`
  sends `x ∈ V(4)` to `(x, 0, 0, 0) ∈ V(0)` (block A only)
- `7→6→5→0`: analogous chain, but with `embed3to4_ACD` at the end
  sends `y ∈ V(7)` via `V(5) = (A'', B'', C'')` to
  `(A'', 0, B'', C'') ∈ V(0)` — so arm 3 covers blocks A, C, D.

The critical observation: arm 1's image has

```
block D = Nq ∈ ⟨e₀⟩  (never reaches e₁)
```

### The decomposition

Set `W'` to be concentrated in the "missed" `e₁` direction of block D:

```
W'(5) = ⟨(0, 0, e₁)⟩  ⊂ V(5)        (1-dim, e₁ in the C''-block)
W'(0) = ⟨(0, 0, 0, e₁)⟩  ⊂ V(0)     (1-dim, e₁ in block D)
W'(v) = 0  for all other v
```

and `W` is the complement at every vertex:

```
W(0) = A + B + C + ⟨(0, 0, 0, e₀)⟩  (7-dim)
W(5) = {(A'', B'', C'') : C'' ∈ ⟨e₀⟩}  (5-dim)
W(v) = V(v)  for v ∈ {1, 2, 3, 4, 6, 7}
```

### Edge-by-edge verification (all arrows)

**For W:**

- `1→0`: `arm1((p,q)) = (p+q, p, q, Nq)`. Block D = `Nq ∈ ⟨e₀⟩`.
  So `arm1(V(1)) ⊆ A + B + C + ⟨block D · e₀⟩ = W(0)`. ✓
- `4→3`, `3→2`, `2→0`: all are first-block embeddings, images have
  block D = 0 ∈ `⟨e₀⟩`, so images land in `W(0)`. ✓
- `7→6`: `starEmbed1(V(7)) = (V(7), 0) ⊆ V(6) = W(6)`. ✓
- `6→5`: `embed2to3_AB(V(6)) = {(α'', β'', 0)}`, and `C'' = 0 ∈ ⟨e₀⟩`,
  so image is in `W(5)`. ✓
- `5→0`: `embed3to4_ACD(W(5)) = (A'', 0, B'', C'')` with
  `C'' ∈ ⟨e₀⟩`, so image is in `W(0)`. ✓

**For W':**

- `1→0`: `W'(1) = 0 → arm1(0) = 0 ⊆ W'(0)`. ✓
- All other edges into/out of vertices with `W'(v) = 0` are trivial. ✓
- `5→0`: `embed3to4_ACD((0, 0, λ e₁)) = (0, 0, 0, λ e₁) ∈ W'(0)`. ✓
- `6→5`: `W'(6) = 0 → 0 ⊆ W'(5)`. ✓

**Complementarity:** `W(v) ⊕ W'(v) = V(v)` at every vertex (dim sum
equals full dim; the `⟨e₀⟩`/`⟨e₁⟩` split of the relevant last block is
always a direct sum in `ℂ²`).

**Non-triviality:** `W'(0), W'(5) ≠ 0` and `W(v) ≠ 0` everywhere.

**Conclusion:** `etilde7Rep 1` is decomposable. Any attempt to prove
`etilde7Rep_isIndecomposable 1 (le_refl 1)` will fail. The sub-sorries
#2427, #2428 cannot be closed as stated.

## 2. Counter-example for `t125Rep 1`

### Setup

For T(1,2,5): 9 vertices. Null root
`δ = (6, 3, 4, 2, 5, 4, 3, 2, 1)` (per the file comment).
For `m = 1`, dim vector is `2δ = (12, 6, 8, 4, 10, 8, 6, 4, 2)`.

Decompose `V(0) = ℂ^{12} = A + B + C + D + E + F` (each `ℂ²`).
Arm 1 (`1→0`): `t125Arm1Embed((p,q,r)) = (p+q+r, p+q, p, q, r, Nr)`.
Block F = `Nr ∈ ⟨e₀⟩` — again, the N-twist misses the `e₁` direction.

Arm 3 chain (the long one, `8→7→6→5→4→0`) ends with
`embedSkipBlockB : ℂ^{5·(m+1)} → ℂ^{6·(m+1)}`,
`(a,b,c,d,e) ↦ (a, 0, b, c, d, e)`.
So the 5th block of `V(4)` maps onto block F of `V(0)`.

### The decomposition

```
W'(0) = ⟨(0, 0, 0, 0, 0, e₁)⟩            (1-dim)
W'(4) = {(0, 0, 0, 0, λ e₁) : λ ∈ ℂ}     (1-dim, e₁ in 5th block)
W'(v) = 0  for all other v

W(0) = (A + B + C + D + E) + ⟨(0,…,0,e₀)⟩ in block F  (11-dim)
W(4) = {(a, b, c, d, e) : e ∈ ⟨e₀⟩}      (9-dim)
W(v) = V(v)  for v ∈ {1, 2, 3, 5, 6, 7, 8}
```

### Verification

- `1→0`: `arm1((p,q,r))` has block F = `Nr ∈ ⟨e₀⟩ ⊆ W(0)`. ✓
- `3→2`, `2→0` (arm 2): first-block embeddings, images have block F = 0. ✓
- `8→7`, `7→6`, `6→5`, `5→4`: first-block embeddings along arm 3,
  all land within `V(·) = W(·)`. The image of `5→4` has 5th block
  `= 0 ∈ ⟨e₀⟩`, so `W(5) = V(5)` is compatible with `W(4)`'s constraint. ✓
- `4→0`: `embedSkipBlockB(a,b,c,d,e) = (a, 0, b, c, d, e)`. For
  `e ∈ ⟨e₀⟩` this is in `W(0)`; for `(0,0,0,0,λ e₁)` this is
  `(0, 0, 0, 0, 0, λ e₁) ∈ W'(0)`. ✓
- `W'`-side: `W'(5) = 0 → 0 ⊆ W'(4)`. ✓

**Non-triviality:** `W'(0), W'(4) ≠ 0` and `W(v) ≠ 0` everywhere. ✓

**Conclusion:** `t125Rep 1` is decomposable. Issue #2400 is unprovable
as stated.

## 3. Why `d5tildeRep` works but Ẽ₆/Ẽ₇/T(1,2,5) don't

### The d5tilde coupling `γ` is a bijection

D̃₅ has two centers (vertices 2 and 3), connected by

```
γ = [[I, I], [I, N]] : ℂ^{2(m+1)} → ℂ^{2(m+1)}
```

Its determinant is `det(N - I) = ±1` (since `N` is nilpotent, `I - N`
is unipotent, hence invertible). So `γ` is an **iso**. This forces
`W(2) ≅ W(3)` via `γ`, and any decomposition must respect this iso.
The four leaves are all tied together through this bridge.

### Ẽ₆/₇/T(p,q,r) have no such bridge

In all three constructions, the arms are **embeddings** (injective
but *not* surjective) from leaves into the center. The center vertex
receives from each arm independently, and nothing forces the arms'
decompositions to agree across the center.

The "shared block A" between arm 2 and arm 3 does provide some
coupling at dimension level, but the nilpotent twist on arm 1 only
covers the `⟨e₀⟩`-direction of one block, leaving the `e_m` direction
free to be peeled off.

### Summary table

| Feature | `d5tildeRep` | `etilde{6,7}Rep` / `t125Rep` |
|---------|-------------|------------------------------|
| Center-to-center bridge | `γ` (iso) | none |
| Arm maps | embeddings | embeddings |
| N-twist location | one arm | one arm |
| N-twist rank | m (out of m+1) | m (out of m+1) |
| "missing" e_m direction | covered by γ | **not covered** |
| Indecomposable for m ≥ 1? | ✓ | ✗ (counter-examples above) |

## 4. What the book actually does

Etingof **does not** construct explicit indecomposable representations
at dim vectors `n·δ` for affine Dynkin quivers. The proof of
"affine ⟹ infinite type" is via the Tits form (Problem 6.1.5):

1. Define the Tits form `q(x) = Σ x_i² − Σ b_{ij} x_i x_j` on dim
   vectors.
2. For a quiver with `n` vertices and dim vector `d`, the
   representation variety `Rep(Q, d)` has dimension
   `Σ b_{ij} d_i d_j` (sum over arrows).
3. `∏ GL_{d_i}` has dimension `Σ d_i²`. The orbit action has
   stabilizer at least `𝔾_m` (scalars). So the space of isomorphism
   classes has "at least" `Σ b_{ij} d_i d_j − Σ d_i² + 1 = −q(d) + 1`
   dimensions.
4. For affine Dynkin, `q(δ) = 0`, hence `q(n·δ) = 0` for all `n`.
   Orbit space has positive dim → **infinitely many orbits** →
   infinitely many isomorphism classes of reps at dim vector `n·δ`.
5. Each rep decomposes (uniquely, Krull–Schmidt) into indecomposables
   of total dim vector `n·δ`. Pigeonhole as `n → ∞` ⟹ infinitely
   many indecomposable isomorphism classes.

This is an **existence** proof; the indecomposables themselves are
never constructed. The current Lean framework tries to *construct*
them, which is a genuinely harder problem and — as the counter-examples
show — is not what the naive mixed-orientation + single-twist pattern
delivers.

## 5. Recommended framework(s)

### Option A: Book's orbit-counting argument (preferred)

Build the infrastructure that the book uses. Rough shape of a Lean
plan:

1. **Tits form**: `def tits (Q : Quiver) (d : V → ℤ) : ℤ := Σ d_v^2 − Σ_arrows d_{src} d_{tgt}`.
   Show `tits (affine Dynkin null root) = 0` for each affine case
   (Ã, D̃, Ẽ₆, Ẽ₇, Ẽ₈, T(p,q,r) with 1/(p+1)+1/(q+1)+1/(r+1) ≤ 1).
2. **Representation variety dim**:
   `dim Rep(Q, d) = Σ_arrows d_{src} d_{tgt}`.
3. **Orbit-counting lemma** (Problem 6.1.2 in the book): if a
   connected algebraic group `G` acts on a variety `V` with finitely
   many orbits, then `dim V ≤ dim G`. Contrapositive:
   `dim V > dim G ⟹ infinitely many orbits`.
4. **Finite type ⟹ finitely many iso classes per dim vector**: if Q is
   of finite type, there are only finitely many indecomposables, and
   each dim vector d has only finitely many (d_1 + … + d_n)! / ∏ d_i!
   many decomposition patterns (at most). So finitely many iso classes.
5. **Contradiction**: for affine Dynkin, `tits(n·δ) = 0`, so
   `dim Rep = dim G`, but stabilizer of scalars gives one extra dim,
   so `dim Rep = dim G − 1`… wait, sign convention. The orbit-space
   dim is `dim Rep − (dim G − 1) = −tits(d) + 1 = 1 > 0` at `d = n·δ`.
   So infinitely many orbits per `n·δ`; pigeonhole ⟹ infinitely many
   indecomposables.

**Lean cost estimate:** very large. Requires algebraic geometry
infrastructure (constructible sets, orbit maps, dimension of
quasi-projective varieties). Mathlib has parts of this. 6+ months of
effort.

### Option B: Stronger explicit construction

If we insist on the constructive path, we need to *fix* the current
representation definitions so that:

- the N-twist covers the `e_m` direction of every block of V(0), or
- there's a center-to-center bridge (iso) like γ in d5tildeRep.

Concretely, for Ẽ₆/₇/T(p,q,r) one could:

1. **Couple multiple arms to block D (or F)**: instead of only arm 1
   having an N-twist, make arm 3 also carry an independent nilpotent
   that covers the complementary direction. This makes the missing
   `e_m` direction in block D be non-trivially constrained.

2. **Add a "recoupling" arrow**: introduce a virtual "bridge" vertex
   between two center-like vertices and use a γ-style iso there.
   This effectively changes the quiver, which may not be allowed.

3. **Use a non-null-root dim vector**: e.g., a dim vector `(m+1) · δ`
   *except* one block increased by 1 (so dim vector is a positive
   root, not a null root). These are known to have unique
   indecomposables (Gabriel's theorem over finite type). But we
   need infinitely many, so this only gives one (or a few).

Option B feels like fighting the representation. The right Lean
story for affine Dynkin is probably Option A.

### Option C: Interim — use subgraph transfer for non-sporadic cases

For T(p,q,r) with arms longer than Ẽ₆, Ẽ₇, Ẽ₈, **some of these do
contain a smaller affine Dynkin as a subgraph** and can be reduced via
`subgraph_infinite_type_transfer` (line 910). But the "sporadic"
cases Ẽ₆, Ẽ₇, Ẽ₈ themselves cannot be reduced further — they are the
minimal forbidden shapes. For those, Option A or B is required.

## 6. Concrete next-issue plan

Recommended planner actions (in priority order):

### Short-term (unblock current PRs)

1. **Close as unprovable:** #2427, #2428 (Ẽ₇ sub-sorries) and #2400
   (T(1,2,5)). Reference this document. Add the explicit
   counter-examples as issue comments for the record.
2. **Close or rewrite:** #2394 (Ẽ₇ parent). Same reasoning.
3. **Revert or gut** the Ẽ₆v2 / Ẽ₇ / T(1,2,5) indecomposability
   attempts in `InfiniteTypeConstructions.lean`. Keep the quiver +
   dim-vector definitions; drop the `_isIndecomposable` theorems
   (replace with `sorry` and a comment pointing at #2430).

### Medium-term: pick a framework

4. **Create an issue: "Decide framework for affine Dynkin infinite
   type."** Human (Kim) picks Option A or Option B. This is a
   definition-level decision that agents should not make alone.

### Long-term (after framework decided)

5a. **Option A path** — create feature issues for Tits form, Rep
    variety dim, orbit-counting theorem, then the main
    `affine_dynkin_infinite_type` theorem.

5b. **Option B path** — create feature issues for the redesigned
    representations (multi-twist couplings, or γ-style bridges),
    one issue per affine type.

Either way, **do not create more "Ẽ_n sub-sorry" issues** against
the current definitions. They cannot be closed.

## 7. What the D̃_n work tells us

`d5tildeRep_isIndecomposable` (#closed) and `dTildeRep_isIndecomposable`
(#2431 refactor in flight) *are* structurally sound. The D̃_n
infrastructure can stay. The problem is specifically the E_n/T_{p,q,r}
constructions, which are modeled after D̃₅ but *without* the γ-iso
bridge — and that bridge is exactly what makes D̃₅ work.

## Appendix: verified counter-example for Ẽ₆v2 (recap of #2417)

For completeness, the Ẽ₆v2 counter-example (from session `d25b71e0`,
full verification on #2417):

- `W₁(2) = ⟨e₀⟩`, `W₁(4) = ℂ²`, `W₁(6) = ⟨e₁⟩`,
- `W₁(1) = ⟨e₀⟩ × ℂ²`, `W₁(5) = ⟨e₁⟩ × ⟨e₀⟩`,
- `W₁(3) = span(ε₀, ε₁, ε₂)`, `W₁(0) = span(α₀, β₀, β₁, γ₁)`,
- `W'₁` complementary at every vertex.

All six edge invariances verified by hand in the issue comment.

---

*Prepared by meditate session `9981829f-5619-46b6-9594-6401b8fa2124`
for #2430.*
