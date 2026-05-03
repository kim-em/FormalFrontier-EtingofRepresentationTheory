## Current state

`EtingofRepresentationTheory/Chapter5/SpechtModuleBasis.lean` line
1681 (`garnir_twisted_in_lower_span`) is sorry'd. The original
Algorithm A outline (former #2648 / #2652) was shown to be unsound
because it required a col-std representative at the same tabloid as
each support element of `f_w(σ)` — and at λ = (2,2), the tabloid
`[{2,3} | {0,1}]` admits no col-std representative at all (parity
argument; see `progress/algorithm-A-redesign.md` §4).

The redesign (note §2 / §3) replaces the col-std existence sub-lemma
with a clean reduction:

```
twistedPolytabloid w σ ∈ L_σ
  ⇐ in_L_of_in_V_of_supp_bounded (R1)        — bridge V → L_σ
  ⇐ twistedPolytabloid_mem_V (this issue)    — Algorithm A core
```

The residual claim — `twistedPolytabloid w σ ∈ V` — is the
combinatorial heart of the proof. The redesign note's Strategy A
(per-q dispatch via column-restandardisation + IH on
`(srRank, rowInvCount')` lex) is the recommended attack.

## Deliverables

1. Add the new helper `twistedPolytabloid_mem_V` to
   `EtingofRepresentationTheory/Chapter5/SpechtModuleBasis.lean`,
   placed immediately before
   `garnir_twisted_in_lower_span` (line 1681):

   ```lean
   private theorem twistedPolytabloid_mem_V
       (σ : Equiv.Perm (Fin n)) (hcs : isColumnStandard' n la σ)
       (hrp : 0 < rowInvCount' (la := la) σ)
       (G : Finset (Fin n)) (w : Equiv.Perm (Fin n))
       (hw_supp : ∀ x, x ∉ G → w x = x)
       (hw_ne : w ≠ 1) (hw_col : w ∉ ColumnSubgroup n la)
       (hw_row : w ∉ RowSubgroup n la)
       (ih : ∀ τ', isColumnStandard' n la τ' →
             ((srRank la τ' < srRank la σ) ∨
              (srRank la τ' = srRank la σ ∧
               rowInvCount' (la := la) τ' < rowInvCount' (la := la) σ)) →
             generalizedPolytabloidTab (n := n) (la := la) τ' ∈ V) :
       twistedPolytabloid (la := la) w σ ∈ V
   ```

   (`V := Submodule.span ℂ (Set.range (fun T : StandardYoungTableau n la
      => polytabloidTab T))`. Match the exact spelling already in the
   file.)

2. Prove it via the per-q dispatch outlined in the redesign note
   §3.1:
   - Define `τ_q := garnirColReindex σ w q · (w · q⁻¹ · σ)` and the
     four regions `Q_low`, `Q_eq`, `Q_eq'`, `Q_high`.
   - On `Q_low ∪ Q_eq` use `ih` to land `ψ_{τ_q} ∈ V` and rewrite
     each `δ_{[w q⁻¹ σ]}` as `sign(γ_q) · ψ_{τ_q} − (residual)`.
   - Show the residual sums and the `Q_high` contribution sum
     vanish or land in `V`. The redesign note §3.1.2 outlines the
     sign-reversing involution to use for `Q_high`, modelled on
     `twistedPolytabloid_apply_of_not_dominates`
     (`SpechtModuleBasis.lean:1475`).
   - If `Q_eq'` turns out to be empty for "Neither" `w` (sub-claim
     §3.1.3), the dispatch simplifies; if not, route through
     §3.1.1.

3. Re-derive `garnir_twisted_in_lower_span` (line 1681) as a
   corollary by composing this helper with R1
   (`in_L_of_in_V_of_supp_bounded`) and the existing
   `twistedPolytabloid_support_bound`. The body of the now-sorry'd
   theorem becomes ~5 lines.

4. The packed-mutual-induction restructure of the surrounding three
   theorems (`garnir_twisted_in_lower_span`,
   `garnir_straightening_step`,
   `polytabloidTab_column_standard_in_span`) is also part of this
   issue: the IH for `polytabloidTab_column_standard_in_span` at
   strictly smaller `(srRank, rowInvCount')` is what feeds the `ih`
   parameter of `twistedPolytabloid_mem_V`. (This is the work
   originally scoped to #2649; the architectural restructure and
   the residual proof are inseparable under the new framework.)

## Context

- **Parent**: #2605 → meditate #2660 → redesign note
  `progress/algorithm-A-redesign.md`.
- **Depends on**: R1 (`in_L_of_in_V_of_supp_bounded` bridge —
  issue #2666). The packed-induction restructure that was
  originally scoped as #2649 has been folded into this issue,
  because under the new framework the architectural change and
  the residual proof are inseparable (sorry-shuffling them across
  two PRs would produce a fragile boundary). #2649 will be closed
  with a forward link.

## Depends on

- depends-on: #2666

## Strategy notes

- The redesign note's **Strategy A 3.1.2** (Q_high cancellation
  involution) is the most novel sub-step. If after a focused
  investigation the worker cannot construct the involution, do not
  burn the budget — abandon this issue with `coordination skip`
  and a comment requesting a follow-up `meditate(Ch5): Q_high
  cancellation involution` (this is R3 in §5.3 of the note).
- The redesign note explicitly rules out two failed approaches
  (§1.4) — workers should not retry "f_w(σ) = w · ψ_σ via
  S_n-invariance of V" (circular) or per-term polytabloid
  expansion (Q_high overflow obstruction).

## Verification

- `lake build EtingofRepresentationTheory.Chapter5.SpechtModuleBasis`
  succeeds with **zero** sorries in `garnir_twisted_in_lower_span`,
  `twistedPolytabloid_mem_V`, and any helper introduced.
- Full `lake build` succeeds.
- Sorry count drops by 1 (from 7 → 6) — the
  `garnir_twisted_in_lower_span` sorry at line 1681 is closed.
- The downstream consumers `garnir_straightening_step` (line 1654)
  and `polytabloidTab_column_standard_in_span` (line 2202) continue
  to type-check (they may need to be updated as part of the
  packed-induction restructure, but their public signatures are
  preserved).
- No new sorries are introduced anywhere.

