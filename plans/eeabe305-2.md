## Current state

`dTildeRep_isIndecomposable` (line 2177 of
`EtingofRepresentationTheory/Chapter6/InfiniteTypeConstructions.lean`,
D̃ₙ indecomposability) is blocked by a type-reduction problem in
`dTildeDim`. Analysis from session 18ffb36a-ca72-44fe-bfdb-3624130f782f
(posted on #2407, now closed) showed:

- `dTildeDim k m v = if 2 ≤ v.val ∧ v.val ≤ k+3 then 2*(m+1) else m+1`.
- For the k-dependent branch points `vk3 = ⟨k+3, _⟩`, `vk4 = ⟨k+4, _⟩`,
  `vk5 = ⟨k+5, _⟩`, the condition involves `Nat.decLe` on k-dependent
  values and does NOT reduce by `rfl`.
- The d5tilde template (`d5tildeRep_isIndecomposable`, lines 1569-1913)
  works because `d5tildeDim m ⟨3, _⟩` reduces to `2*(m+1)` by `rfl`.
- With the current `dTildeDim` definition, statements like
  `starEmbed1 m x + starEmbed2 m z ∈ W vk3` fail to typecheck without
  heavyweight cast bridges.

## Deliverables

1. **Refactor `dTildeDim`** (or the ambient representation definition
   `dTildeRepMap`) so that `(dTildeRep k m).obj v` reduces by `rfl`
   (or at worst by `dsimp`) to `Fin (2*(m+1)) → ℂ` at each of the
   branch-point vertices `⟨2, _⟩`, `⟨k+3, _⟩`, and to
   `Fin (m+1) → ℂ` at the leaf vertices `⟨0, _⟩`, `⟨1, _⟩`, `⟨k+4, _⟩`,
   `⟨k+5, _⟩`.

   Possible approaches:
   - Pattern-match on a structured view of `v` (e.g., a custom inductive
     covering "leaf-left / spine / branch / leaf-right" cases).
   - Replace the `if ... then ... else` with an explicit `match`
     expression that carries the relevant arithmetic conditions.
   - Add `@[simp]` `rfl`-equality lemmas for the branch-point cases
     that `dsimp only [...]` can apply to make types align.

2. **Verify that the d5tilde proof pattern ports cleanly**: state (but
   do NOT yet prove) `dTildeRep_isIndecomposable` in the same shape as
   `d5tildeRep_isIndecomposable` — i.e., the statements
   `starEmbed1 m x + starEmbed2 m z ∈ W vk3` etc. should typecheck
   after the refactor without cast gymnastics.

3. Keep the refactor scoped: do NOT attempt to prove
   `dTildeRep_isIndecomposable` in this PR. A follow-up issue will
   reference the d5tilde template once the scaffolding is in place.

## Context

- File: `EtingofRepresentationTheory/Chapter6/InfiniteTypeConstructions.lean`.
- Reference implementation: `d5tildeRep_isIndecomposable` (lines
  1569-1913) and `d5tildeDim`.
- Superseded issue: #2407 (closed, see its skip comment for the full
  analysis).
- This is a Stage 3.1 (definition) fix — the mathematical content of
  the representation is unchanged, only the Lean packaging.
- The path infrastructure `walk_to_nodup_path` and
  `dTilde_nodup_path_between` is already complete (#2384 merged) and
  is available for the downstream proof.

## Verification

- `lake build EtingofRepresentationTheory.Chapter6.InfiniteTypeConstructions`
  succeeds.
- In a scratch block at the bottom of the file (to be removed once the
  downstream proof lands), demonstrate that
  `example (k m : ℕ) (x : Fin (m+1) → ℂ) :
      x ∈ (⊥ : Submodule ℂ (Fin (2*(m+1)) → ℂ)) →
      x ∈ (⊥ : Submodule ℂ ((dTildeRep k m).obj ⟨2, by omega⟩)) := by
    intro h; exact h`
  (or equivalent, capturing that the types coincide by `rfl`/`dsimp`).
- No new sorries introduced; existing `dTildeRep_isIndecomposable`
  sorry at line 2177 may remain.
