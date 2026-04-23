## Current state

`EtingofRepresentationTheory/Chapter5/SpechtModuleBasis.lean` has a
single `sorry` in `garnir_twisted_in_lower_span`. The statement was
framework-corrected in PR #2443 (flipping dominance direction) and is
now classically correct — it matches the James Ch. 7-8 / Fulton Ch. 7
Garnir-term dominance result.

The theorem states: for column-standard σ with positive row-inversion
count, and for any Garnir permutation w ∈ Neither (w ∉ ColumnSubgroup
and w ∉ RowSubgroup) supported on a Garnir set G,

```
twistedPolytabloid (w σ) ∈ Submodule.span ℂ { ψ_τ // τ col-std ∧
  (σ's tabloid strictly dominates τ's ∨
   (τ has same tabloid as σ ∧ rowInvCount' τ < rowInvCount' σ)) }
```

## ⚠️ Pre-implementation validation required — two approaches have been refuted

Before attempting a proof, **validate your strategy against the
counter-example** λ = (2,2), σ = swap(0,1), described in
`progress/20260423T112112Z_9cfda69f.md`.

Two decomposition routes have been tried and refuted:

1. **Per-term dominance** (#2425, closed): attempted to show each
   individual Garnir-sum term is dominated by σ's tabloid. Refuted.
2. **Per-term classification** (#2451, #2453, #2454, all closed):
   attempted to classify each col-restandardized Garnir term as either
   tabloidStrictDominates or same-tabloid-smaller-rowInv. Refuted by
   the triple (σ=swap(0,1), w=swap(1,2), q=swap(1,3)): the
   col-standardized τ = swap(2,3)·swap(0,1) has same tabloid as σ but
   rowInvCount' 2 > 1 = rowInvCount'(σ), violating both disjuncts.

Both refutations share a structural root: **Q·P·Q sandwich
conjugation** can map a Neither-permutation to a P_λ (row)
permutation, so per-term control of `w·q⁻¹` or `q₀·w·q⁻¹` cannot be
derived from `w ∉ P_λ`.

**The outer theorem is still true** — the Specht module has the SYT
basis (classical), and for the counter-example
ψ_σ = ψ_id − ψ_{swap(1,2)} sits in the broadened span (ψ_id via the
same-tabloid-rowInv< disjunct; ψ_{swap(1,2)} via σ-strictly-dominates).
The issue is not the statement but the proof strategy.

## Deliverables

**Prove `garnir_twisted_in_lower_span`** (close the sorry). Because
per-term decomposition has been refuted twice, **the recommended
approach is whole-sum cancellation**:

- Recognize `f_w(σ) = Σ_{q ∈ Q_λ} sign(q)·[w·q⁻¹·σ]` as a **conjugate
  polytabloid** over the subgroup `wQ_λw⁻¹`, or more precisely as a
  twisted polytabloid whose Q-subgroup is shifted by w.
- Use the sign-cancellation across all q simultaneously (James Ch. 7.2
  proof of the Garnir relation) rather than analyzing individual
  terms.
- The key identity to aim at: when w ∈ Neither is supported on a
  Garnir set G with |col(p₁) ∩ G| + |col(p₂) ∩ G| > (row count), the
  **full sum** kills by pigeonhole, giving a direct expression of f_w
  as a combination of `ψ_τ` for τ with tabloid strictly dominated by
  σ's, *plus* a residual row-subgroup correction that contributes
  same-tabloid-smaller-rowInv terms.

If you find yourself decomposing into per-term classifications, STOP:
that route is dead. Check the counter-example before coding.

## Verification

- `lake build EtingofRepresentationTheory.Chapter5.SpechtModuleBasis`
  succeeds with zero sorries in the target theorem.
- `lake build` full project succeeds.
- `finrank_spechtModule_eq_card_syt'` continues to compile.
- The counter-example λ = (2,2), σ = swap(0,1) produces both expansion
  terms (ψ_id and ψ_{swap(1,2)}) in the theorem's span via the
  broadened disjunction.

## Context / References

- File: `EtingofRepresentationTheory/Chapter5/SpechtModuleBasis.lean`
  (search for `garnir_twisted_in_lower_span`).
- Supporting infrastructure already present:
  - `exists_column_standard_mul` (line 269)
  - `generalizedPolytabloidTab_col_mul`
    (`EtingofRepresentationTheory/Chapter5/TabloidModule.lean:1104`)
  - `twistedPolytabloid`, `twistedPolytabloid_col_eq`,
    `twistedPolytabloid_row_eq`
  - `rowInvCount'_swap_lt`, `tabloidStrictDominates`
- Session analyses to read first:
  - `progress/20260423T112112Z_9cfda69f.md` — original counter-example
    for λ=(2,2), σ=swap(0,1).
  - `progress/20260423T133105Z_d3dde2a8.md` — direction-fix landed in
    PR #2443.
  - `progress/20260423T162323Z_84b86e57.md` — refutation of per-term
    classification (#2454 / #2451).
- Design wall: `progress/design-walls-wave54.md` Wall 3, Option 1.
- Closed refutation issues: #2425, #2451, #2453, #2454.

## Scope warning

This is the **entirety of Wall 3** (Garnir straightening). It is a
substantial mathematical result — multiple hundred lines of Lean is
plausible. Decomposition is encouraged, but **only along lines the
whole-sum strategy supports**. If you decompose, the sub-issues must
be validated against the λ=(2,2), σ=swap(0,1) counter-example before
dispatch. Leave a `Decomposed into #A, #B` breadcrumb before
`coordination skip` if you decompose.

Downstream: closing this sorry unblocks
`polytabloidTab_column_standard_in_span` →
`generalizedPolytabloidTab_mem_span_polytabloidTab` →
`finrank_spechtModule_le_card_syt` → `finrank_spechtModule_eq_card_syt'`
(Ch5 dim V_λ = |SYT(λ)| theorem).
