## Current state

`garnir_straightening_step` (line 982 of `SpechtModuleBasis.lean`) has a `sorry`
for the `k = 0` case of the Garnir reduction, introduced by PR #2415 during the
circularity fix of #2413.

The `k ≥ 1` case is fully proved: the Garnir identity gives
`k·ψ_σ + (-ψ_σ) + Σ_neither = 0`, and since `Σ_neither ∈ L` by
`garnir_twisted_in_lower_span`, we get `k·ψ_σ ∈ L` and divide by `k`.

The `k = 0` case is degenerate: `k = |G ∩ Q_λ| - 1 = 0` happens iff
`row(p₁) = 0` and `col(p₁)` has length 1. In this case the Garnir identity
only gives `0 = -Σ_neither ∈ L`, providing no information about `ψ_σ`.

## Deliverables

1. Fill the sorry at line 982 of `SpechtModuleBasis.lean` (`k = 0` branch of
   `garnir_straightening_step`).

   Proposed strategy (from #2413 body):
   - In the `k = 0` case, let `σ' := swap(p₁, p₂) · σ`.
   - Prove `σ'` is still column-standard: columns `col(p₁)` and `col(p₂)` are
     single cells, so the swap does not break column order.
   - Prove `rowInvCount'(σ') < rowInvCount'(σ)`: the swap removes the row
     inversion `(p₁, p₂)`.
   - Prove `ψ_σ = ψ_{σ'}`: because `swap(p₁, p₂) ∈ P_λ` (row-preserving —
     both are in row 0 in this case) and tabloids are `P_λ`-equivariant,
     `[swap(p₁, p₂) · q⁻¹ · σ] = [q⁻¹ · σ]` for every `q ∈ Q_λ`.
   - Conclude `ψ_σ = ψ_{σ'} ∈ L` via the induction hypothesis on `σ'`.

## Context

- File: `EtingofRepresentationTheory/Chapter5/SpechtModuleBasis.lean`, line 982
- The `k = 0` branch currently reads `by_cases hk_zero : k = 0` → `· sorry`.
- Helper lemmas that may be useful (check if already present or need to be
  added):
  - `twistedPolytabloid_row_eq` (already added by PR #2415) — shows
    `twistedPolytabloid w σ = ψ_σ` for `w ∈ RowSubgroup`.
  - A `ψ` equality via P-equivariance of tabloids: `[w · x] = [x]` for
    `w ∈ P_λ` (tabloids are `Quotient`s by `P_λ` action).
  - Column-standardness is preserved under swap of same-row single-cell
    columns.
- Callers of `garnir_straightening_step` are inside the induction in
  `straightening_theorem` (further down in the same file). The induction
  uses `rowInvCount'` as the well-founded measure, so appealing to
  `σ'` with strictly smaller `rowInvCount'` fits the same induction.
- Difficulty: 5-6. The strategy is clear; the work is mostly bookkeeping
  (column-standardness, inversion counting, tabloid equivariance).

## Verification

- `lake build EtingofRepresentationTheory.Chapter5.SpechtModuleBasis` succeeds.
- 1 sorry eliminated (line 982).
- No regressions: `lake build` succeeds for the full target.
