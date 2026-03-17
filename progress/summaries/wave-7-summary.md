# Stage 3.2 Seventh Proof Wave Summary

**Date:** 2026-03-17
**Scope:** All work since the sixth wave summary (#838, merged 2026-03-17T08:39Z)
**Status:** Stage 3.2 in progress — 178/583 items sorry_free (30.5%), 129 sorry occurrences across 54 files

## Executive Summary

The seventh wave landed 14 PRs, advancing sorry_free count from 176 to 178 (+2 items). This wave was dominated by **statement formalization** rather than proof completion — 7 PRs formalized new statements across Ch2, Ch5, Ch6, and Ch9, laying groundwork for future proof work. Key developments: Lemma 6.4.6 (root coordinates nonneg/nonpos) was proved sorry-free, Proposition 6.6.5 (indecomposable surjective at sinks) was formalized, and three Ch9 items gained real statements (Theorem 9.6.4, Corollary 9.7.3, Proposition 9.2.3). The meditate retrospective (#843) produced updated skills for helper lemma extraction, multi-PR proof chains, and chapter closure tactics. Aristotle results were polled and integrated (#858).

## Merged PRs (14)

### Proof Completions (1)

| PR | Title | Chapter | Key Result |
|----|-------|---------|------------|
| #859 | Prove Lemma 6.4.6 (root coordinates nonneg/nonpos) | Ch6 | Positive root coordinates are all ≥0 or all ≤0 — sorry-free |

### Statement Formalizations (7)

| PR | Title | Chapter |
|----|-------|---------|
| #849 | Theorem 2.1.1 statement (sl(2) irreps classification) | Ch2 |
| #850 | Proposition 2.7.1 (Weyl algebra basis) | Ch2 |
| #853 | Theorem 2.1.2 statement (Gabriel's theorem) | Ch2 |
| #852 | Proposition 5.14.1 (Kostka decomposition) | Ch5 |
| #862 | Proposition 6.6.5 (indecomposable surjective at sinks) | Ch6 |
| #860 | Theorem 9.6.4 + Corollary 9.7.3 (Morita equivalence) | Ch9 |
| #866 | Proposition 9.2.3 (projective cover hom multiplicity) | Ch9 |

### Scaffolding & Escalation (2)

| PR | Title | Chapter |
|----|-------|---------|
| #848 | Theorem 5.17.1 (hook length formula) — statement formalized, proof escalated to Aristotle | Ch5 |
| #851 | Scaffold reflection functor bodies (6.6.3, 6.6.4) | Ch6 |

### Combined / Multi-item PRs (1)

| PR | Title | Items |
|----|-------|-------|
| #861 | Corollary 5.12.4 statement + Proposition 2.7.1 Aristotle escalation | Ch5 + Ch2 |

### Reviews & Infrastructure (3)

| PR | Title | Type |
|----|-------|------|
| #843 | Meditate: Stage 3.2 hard-proof transition retrospective | Meditate |
| #854 | Document type-level if/else diamond in lean-formalization skill | Chore |
| #858 | Poll Aristotle results and integrate proofs (9.2.1, 5.12.2, 6.3.1) | Review |

## Sorry-Free Items by Chapter

| Chapter | Topic | Sorry-free | Formal Items | Formal % | Total | Overall % | Delta from Wave 6 |
|---------|-------|------------|-------------|----------|-------|-----------|-------------------|
| 2 | Basic notions | 39 | 42 | 92.9% | 117 | 33.3% | +0 |
| 3 | General results | 23 | 23 | **100%** | 58 | 39.7% | +0 |
| 4 | Characters | 21 | 21 | **100%** | 60 | 35.0% | +0 |
| 5 | Representations of S_n | 32 | 59 | 54.2% | 157 | 20.4% | +0 |
| 6 | Quiver representations | 15 | 33 | 45.5% | 64 | 23.4% | **+2** |
| 7 | Categories | 26 | 26 | **100%** | 59 | 44.1% | +0 |
| 8 | Abelian categories | 9 | 9 | **100%** | 24 | 37.5% | +0 |
| 9 | Finite dim. algebras | 13 | 18 | 72.2% | 35 | 37.1% | +0 |
| **Total** | | **178** | **231** | **77.1%** | **583** | **30.5%** | **+2** |

## Sorry Count Trend

| Wave | Date | Sorry-free | Sorries | Files w/sorry | Items/PR | PRs |
|------|------|-----------|---------|---------------|----------|-----|
| Wave 1 | 2026-03-16 | 132 | ~226 | ~90 | — | 32 |
| Wave 2 | 2026-03-16 | 147 | 193 | 79 | 0.5 | 27 |
| Wave 3 | 2026-03-17 | 157 | 166 | 72 | 0.8 | 13 |
| Wave 4 | 2026-03-17 | 167 | 150 | 67 | 1.0 | 10 |
| Wave 5 | 2026-03-17 | 170 | 141 | 64 | 0.2 | 14 |
| Wave 6 | 2026-03-17 | 176 | 129 | 56 | 0.6 | 10 |
| **Wave 7** | **2026-03-17** | **178** | **129** | **54** | **0.1** | **14** |

## Velocity Analysis

- **Items per PR**: 0.1 (2 items / 14 PRs) — lowest yet, reflecting the shift to statement formalization
- **Sorry reduction**: 0 sorries eliminated (129 → 129), -2 files (56 → 54)
- **Statement formalizations**: 7 PRs — largest statement formalization batch in any wave
- **New Aristotle submissions**: Theorem 5.17.1 (hook length formula), Proposition 2.7.1 (Weyl algebra basis)

Wave 7 represents a deliberate pivot toward **breadth over depth**: formalizing statements in Ch2, Ch5, Ch6, and Ch9 to create a larger frontier of provable items. The low items/PR ratio is expected — statement formalization doesn't increase sorry_free count but creates the preconditions for future proof work.

## Aristotle Pipeline Status

| Item | Status | Project ID | Notes |
|------|--------|-----------|-------|
| Chapter5/Theorem5.12.2 | attention_needed | 9ebaca73 | Failed: namespace/axiom issues. Needs manual intervention for young_symmetrizer_sq_ne_zero |
| Chapter5/Lemma5.15.3 | attention_needed | ca2097ca | **False statement** detected — sign convention in Cauchy determinant formula incorrect |
| Chapter5/Theorem5.17.1 | sent_to_aristotle | — | Hook length formula proof escalated this wave |
| Chapter2/Proposition2.7.1 | sent_to_aristotle | — | Weyl algebra basis escalated this wave |
| Chapter9/Theorem9.2.1 | sent_to_aristotle | — | Re-submitted with context files in wave 6 |

## Items.json Audit

Verified items against actual Lean file sorry counts:

| Item | items.json Status | Sorries in File | Assessment |
|------|------------------|-----------------|------------|
| Ch6/Lemma6.4.6 | sorry_free | 0 | ✅ Correct |
| Ch6/Proposition6.6.5 | statement_formalized | 4 | ✅ Correct (has sorry placeholders) |
| Ch9/Proposition9.2.3 | statement_formalized | 1 | ✅ Correct |
| Ch9/Theorem9.6.4 | statement_formalized | 1 | ✅ Correct |
| Ch5/Lemma5.15.3 | attention_needed | 1 | ✅ Correct (false statement found by Aristotle) |
| Ch5/Theorem5.12.2 | attention_needed | 3 | ✅ Correct (Aristotle failed on helper) |

No inconsistencies found in spot-checked items. All statuses match actual file state.

## Key Observations

1. **Statement formalization wave**: 7 of 14 PRs were statement formalizations — the largest such batch. This creates a broader frontier for future proof work.
2. **Ch9 advancing**: Three new statements formalized (9.2.3, 9.6.4, 9.7.3), pushing Ch9 toward completion (13/35 sorry_free, 18 formal).
3. **Ch6 infrastructure maturing**: Reflection functor bodies scaffolded (6.6.3, 6.6.4), Prop 6.6.5 formalized, Lemma 6.4.6 proved. The quiver representation chain is building toward Theorem 6.8.1 (Gabriel's theorem proof).
4. **Aristotle pipeline challenges**: Two items in `attention_needed` — one false statement (5.15.3), one tooling issue (5.12.2). These require manual intervention before re-submission.
5. **Four chapters remain at 100%**: Ch3, Ch4, Ch7, Ch8 — no regression.
6. **Skills updated**: Helper lemma extraction pattern, multi-PR proof chains, chapter closure tactics added to lean-formalization skill.

## Recommendations for Next Wave

1. **Prove newly-formalized statements**: Prioritize items that now have real statements but sorry proofs (Ch9 items, Ch6/Prop6.6.5)
2. **Fix Lemma 5.15.3 statement**: Aristotle found a counterexample — the Cauchy determinant sign convention needs correction before re-submission
3. **Ch2 completion push**: At 39/42 formal items sorry_free (92.9%), Ch2 is close to 100% formal completion — 3 items remain
4. **Poll Aristotle**: Check results for Theorem 5.17.1 and Proposition 2.7.1 submissions
