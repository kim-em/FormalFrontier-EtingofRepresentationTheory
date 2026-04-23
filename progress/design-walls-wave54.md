# Wave 54 — Design Walls Inbox

Three framework-level decisions are blocking further worker progress.
Each has been investigated to refutation or impossibility with the
current approach; each needs a planner or human to commit to one of
the listed options before any worker-fillable issue can be usefully
written.

This file is short on purpose. The detail is in the linked documents.

---

## Wall 1 — Ẽ_n / T(p,q,r) indecomposability framework

**Context.** `etilde6v2Rep_isIndecomposable`, `etilde7Rep_isIndecomposable`,
and `t125Rep_isIndecomposable` are all provably **false** for every m ≥ 1.
A single nilpotent twist on one arm only covers the `⟨e₀, …, e_{m-1}⟩`
sub-block of its target; the `e_m` direction is uncoupled, and can be
peeled off as a 1-dimensional complementary summand at the center.
Explicit counter-example decompositions for `etilde7Rep 1` and
`t125Rep 1` are constructed in the design doc. Ten sub-sorries in
`Chapter6/InfiniteTypeConstructions.lean` (lines 2380, 2397, 2400,
2425, 3001, 3004, 3038, 3477, 3480, 3502) cannot be closed as stated.

`d5tildeRep_isIndecomposable` escapes this because its center-to-center
bridge `γ` is an iso (nilpotent `I − N` is unipotent hence invertible),
not just an embedding. Ẽ/T have no analogous bridge.

**Full analysis.** `progress/indecomposability-framework-investigation.md`
(merged via #2432).

**Options.**

- **Option A — Book's Tits-form / orbit-counting argument.** Replace
  the explicit-construction strategy with the book's existence proof:
  define the Tits form; show `q(δ) = 0` for each affine Dynkin case;
  invoke the algebraic-group orbit-counting lemma (`dim V > dim G ⟹
  infinitely many orbits`) to conclude infinitely many indecomposables
  per `n·δ`. Requires substantial Lean algebraic-geometry infrastructure
  (orbit maps, dimension of quasi-projective varieties, constructible
  sets). Estimate: 6+ months.

- **Option B — Stronger explicit construction.** Redefine the Rep
  objects so that either (a) the N-twist covers the `e_m` direction of
  every block, or (b) there is a γ-style center-to-center iso
  bridging independent arms. Concrete sketches:
    1. Couple multiple arms to block D/F with independent nilpotents
       (Ẽ₇, T(1,2,5)).
    2. Add a virtual "recoupling" arrow (changes the quiver; may not
       match the book's setup).
    3. Use a non-null-root dim vector for the explicit case (only
       gives one indecomposable, insufficient on its own).
  Estimate: weeks for one case; the four `etilde{6,7,8}Rep` /
  `t125Rep` cases must each be reworked.

- **Option C — Interim subgraph transfer.** Several T(p,q,r) cases
  contain a smaller affine Dynkin as a subgraph and reduce via the
  existing `subgraph_infinite_type_transfer` (line 910). Does **not**
  close Ẽ₆, Ẽ₇, Ẽ₈ (the sporadic minimal forbidden shapes), but
  removes some T(p,q,r) cases from the explicit-construction burden.
  Useful as a partial step whichever of A/B is chosen.

**Blocks.** 10 Ch6 sorries. Downstream: Theorem 2.1.2 forward bridge
(1 Ch2 sorry).

---

## Wall 2 — `dTildeDim` vertex-type strategy

**Context.** `dTildeRep_isIndecomposable (k m : ℕ)` (line 2177) is the
only non-refuted Ch6 indecomposability item. The blocker is
Lean-level, not mathematical: `dTildeDim k m v` does not reduce by
`rfl`/`dsimp` at k-dependent vertices because the definition
case-splits on `v.val`'s position relative to `k + 6`. The case-split
style proof (copy the d5tilde pattern) needs `dTildeDim k m ⟨i, hi⟩`
to reduce to a concrete value like `m + 1` or `2(m+1)` in each branch,
which fails at vertices that are expressed in terms of `k` (e.g.
`⟨k + 3, _⟩`).

**Session analysis.** Session 0fa9a788 on closed issue #2431.

**Options.**

- **Option a — Custom inductive vertex type.** Replace `Fin (k + 6)`
  with a bespoke inductive `DTildeVertex k`  whose constructors directly
  name the left-tip, right-tip, arm, and center vertices. Each
  constructor has its own dimension via `dim (DTildeVertex k) → ℕ`
  defined by pattern matching. Reduces by `rfl` by design. Cost: a
  refactor of the dTilde section of `InfiniteTypeConstructions.lean`
  (several hundred lines), and a separate conversion step when
  interfacing with the `FinQuiverRep` ambient framework.

- **Option c — `finCongr` cast bridges.** Keep `Fin (k + 6)` but
  insert explicit `finCongr` casts where definitional reduction fails.
  Every `dTildeDim k m v = dim_value` step in the proof becomes a
  small lemma proved by cases / omega. Cost: verbose proof, but no
  refactor; the interface remains Fin-based. Risk: the number of cast
  bridges scales with proof length, and motive-not-type-correct errors
  appear whenever casts traverse dependent types.

- **Option b (implicit — "do nothing")**: abandon the dTilde explicit
  construction and reduce to the book's argument via Option A of Wall 1.
  Consistent with that choice; makes dTilde a special case of the
  general Tits-form machinery.

**Blocks.** 1 Ch6 sorry (dTilde indecomposability). If Wall 1 is
resolved via Option A, this wall becomes moot.

---

## Wall 3 — Garnir straightening induction measure

**Context.** `garnir_twisted_in_lower_span` (SpechtModuleBasis.lean:942)
and `garnir_straightening_step` are both **false** at λ=(2,2),
σ=swap(0,1): the theorem's claimed span is `{ψ_id}` in this case, but
ψ_σ = ψ_id − ψ_{swap(1,2)}, and `swap(1,2)` is not in the theorem's
allowed τ set. The outer Specht-basis theorem
`polytabloidTab_column_standard_in_span` is classically true (the
Specht module has the SYT basis), but the Garnir-based decomposition
currently in `SpechtModuleBasis.lean` loses essential ψ_τ terms at
lower-dominated tabloids and cannot close the sorry.

**Session analysis.** Session 9cfda69f on closed issue #2425;
progress entry `progress/20260423T112112Z_9cfda69f.md`.

**Options.**

- **Option 1 — Column-based induction (classical James Ch. 8 /
  Fulton Ch. 7).** Switch the induction measure from row-inversion
  count to the *column tableau's* inversion structure, traversing
  tabloid classes via column (not row) rearrangements. The classical
  straightening algorithm is stated this way; porting it should work.
  Cost: rewrite of `SpechtModuleBasis` inductive structure (~100 lines).

- **Option 2 — Broaden the allowed τ set.** Extend
  `garnir_straightening_step` to permit τ's whose tabloid is strictly
  dominated by σ's (rather than strictly row-inverted). Update the
  outer induction in `polytabloidTab_column_standard_in_span`
  correspondingly. Cost: moderate; re-verifies the counter-example but
  may open other edge cases.

- **Option 3 — Maximal-tabloid corner case.** Handle σ whose tabloid
  is maximal-but-row-inverted explicitly, by column-restandardizing
  σ (find q₀ ∈ ColumnSubgroup with q₀σ row-standard) rather than
  routing through the Garnir identity. Leaves the rest of the
  framework intact. Cost: a single lemma, easier than 1 or 2, but
  feels like a patch rather than a fix.

**Blocks.** 1 Ch5 sorry (`garnir_twisted_in_lower_span`). Downstream:
`polytabloidTab_column_standard_in_span` → Ch5 dimV_λ theorem. No
further downstream chain.

---

## Meta

None of these walls can be resolved by a worker agent. Each needs a
planner's (or human's) commitment to one of the listed options,
after which the worker queue can be reopened with concrete sub-issues.
Until then, the worker pool has nothing productive to do on the
framework-blocked items — work can only proceed on
`iso_of_formalCharacter_eq_schurPoly` (independent Mathlib-gap item,
hardest remaining sorry) or cleanup / infrastructure tasks.
