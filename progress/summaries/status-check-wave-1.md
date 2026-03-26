# Status Check Wave 1

**Date:** 2026-03-26
**Issue:** #1725
**Trigger:** 793+ PRs merged, first formal status check (overdue per PLAN.md)
**Baseline:** Wave 34 sorry landscape (44 sorrys / 22 files)

## Key Metrics

| Metric | Wave 34 | Now | Delta |
|--------|---------|-----|-------|
| Total sorrys | 44 | 43 | -1 |
| Files with sorry | 22 | 21 | -1 |
| Sorry-free files | 246/268 (91.8%) | 247/268 (92.2%) | +1 |
| Definition-level sorrys | ~8 (reported) | 10 | see below |

### Per-Chapter Breakdown

| Chapter | Sorrys | Files | Hardest item | Open issues |
|---------|--------|-------|--------------|-------------|
| Ch2 | 1 | 1 | Theorem2_1_2 (blocked on Ch6) | #1734 |
| Ch3 | 0 | 0 | - | - |
| Ch4 | 0 | 0 | - | - |
| Ch5 | 28 | 8 | Theorem5_23_2 (9, def-level) | #1717, #1721, #1722 |
| Ch6 | 10 | 8 | Corollary6_8_3 + CoxeterInfra chain | #1691, #1714, #1724, #1726 |
| Ch7 | 0 | 0 | - | - |
| Ch8 | 0 | 0 | - | - |
| Ch9 | 2 | 2 | Example9_4_4 (Hilbert syzygy) | #1729 |
| Infra | 2 | 2 | BasicAlgebraExistence | #1729 |

## 1. Definition-Level Sorry Regression Check

**10 definition-level sorrys found** (vs ~8 reported in wave 34):

| # | Definition | File:Line | Known? |
|---|-----------|-----------|--------|
| 1 | `kostkaNumber` | Proposition5_21_1:334 | Yes |
| 2 | `SchurModule` | Theorem5_22_1:38 | Yes (#1722) |
| 3 | `formalCharacter` | Theorem5_22_1:46 | Yes |
| 4 | `AlgIrrepGL` (type) | Theorem5_23_2:59 | Yes |
| 5 | `AlgIrrepGL.addCommGroup` | Theorem5_23_2:62 | Yes |
| 6 | `AlgIrrepGL.module` | Theorem5_23_2:65 | Yes |
| 7 | `AlgIrrepGL.finite` | Theorem5_23_2:68 | Yes |
| 8 | `AlgIrrepGLDual` (type) | Theorem5_23_2:73† | Yes |
| 9 | `AlgIrrepGLDual.addCommGroup` | Theorem5_23_2:76 | Yes |
| 10 | `AlgIrrepGLDual.module` | Theorem5_23_2:79 | Yes |
| 11 | `IsFiniteTypeQuiver` | Problem6_1_5_theorem:33 | Yes |

†Line 73 is the sorry'd proof of `AlgIrrepGLDual`; the type definition is at line 73 (`Type := sorry`).

**Verdict: No new definition-level sorry regressions.** The count difference from wave 34 (8 vs 10-11) is due to counting methodology (whether instances are counted separately from their parent type). All are known.

**Critical path:** SchurModule (#1722, actively claimed) blocks ~21 sorrys transitively. This is the single highest-ROI target.

## 2. Hardest Remaining Items

### Chapter 2
- **Theorem2_1_2** (1 sorry): Gabriel's theorem. Blocked on Chapter 6 chain. Not independently workable. Created #1734.

### Chapter 5
- **Theorem5_23_2** (9 sorrys, 5 def-level): Peter-Weyl for GL(V). Blocked on SchurModule + AlgIrrepGL construction. **Tier 4.**
- **Theorem5_27_1** (5 sorrys): Mackey machine. Requires Clifford theory ~500 lines. **Tier 3.** Created #1731.
- **Theorem5_18_4** (4 sorrys): Schur-Weyl centralizer/decomposition. Core sorry is `centralizer_symGroupImage_eq_diagonalActionImage`. **Tier 2-3.** Created #1733.
- **PowerSumCauchyBilinear** (2 sorrys): Cauchy bilinear identity. Active (#1714, #1721).
- **PolytabloidBasis** (2 sorrys): Linear independence + straightening. Active (#1717).

### Chapter 6
- **CoxeterInfrastructure** (1 sorry): `indecomposable_reduces_to_simpleRoot` — iterated reflection functor chain. **Tier 2.** Active (#1691).
- **Corollary6_8_3** (1 sorry): Uniqueness via reflection chain. Blocked on CoxeterInfra.
- **Corollary6_8_4** (1 sorry): Existence via reflection chain. Blocked on CoxeterInfra.
- **Proposition6_6_6** (2 sorrys): Instance diamonds. Active (#1724).
- **Proposition6_6_7** (1 sorry): Source case. Active (#1726).

### Chapter 9 + Infrastructure
- **Example9_4_4** (1 sorry): Hilbert syzygy theorem. **Tier 4.** Deep homological algebra.
- **MoritaStructural** (2 sorrys across Ch9+Infra): B ≅ eAe construction. **Tier 3.** Created #1729.
- **BasicAlgebraExistence** (1 sorry): Every algebra is Morita equivalent to basic. **Tier 3.**

## 3. Neglected Items

Files with sorrys that have had no PRs or issues in 5+ days (10+ waves):

| File | Last touched | Sorrys | Reason | New issue |
|------|-------------|--------|--------|-----------|
| Theorem2_1_2 | Mar 18 | 1 | Blocked on Ch6 | #1734 |
| Proposition5_21_1 | Mar 19 | 2 | kostkaNumber def-sorry + proof | - (blocked on SchurModule) |
| Proposition5_22_2 | Mar 18 | 1 | Blocked on SchurModule | - |
| Theorem5_22_1 | Mar 18 | 3 | SchurModule + formalCharacter def-sorrys | #1722 (active) |
| Theorem5_23_2 | Mar 18 | 9 | All blocked on SchurModule/AlgIrrepGL | - |
| Problem6_1_5_theorem | Mar 18 | 2 | IsFiniteTypeQuiver def-sorry + proof | - (blocked on Ch6 chain) |
| Theorem6_5_2 | Mar 18 | 1 | Full proof sorry, blocked on Ch6 chain | - |
| Example9_4_4 | Mar 17 | 1 | Hilbert syzygy — deep, Tier 4 | #1729 |

**Most neglected items are blocked on SchurModule or the Ch6 Gabriel chain** — this is expected. The items that are genuinely neglected AND workable are:
- MoritaStructural (2 sorrys) → #1729
- Theorem5_18_4 centralizer (4 sorrys, partially independent) → #1733
- Theorem5_27_1 Mackey (5 sorrys, fully independent) → #1731

## 4. Work Distribution

Last 50 merged PRs by chapter:

| Chapter | PRs | Has sorrys? | Assessment |
|---------|-----|-------------|------------|
| Ch2 | 2 | 1 sorry | Appropriate (blocked) |
| Ch5 | 13 | 28 sorrys | **Highest activity, highest sorry count** |
| Ch6 | 7 | 10 sorrys | Active, well-covered by open issues |
| Ch9 | 0 | 2 sorrys | **Neglected** → #1729 |
| Infra | 5 | 2 sorrys | Recent activity (Morita, FDRep bridge) |
| Other | 23 | - | Reviews, summaries, meditations, infrastructure |

**Flag:** Ch9 has had zero direct PRs in 50 waves despite having sorrys. The sorrys are genuinely hard (Tier 3-4) but at least MoritaStructural deserves an attempt.

## 5. Milestones Since Wave 34

- **Theorem5_15_1 → sorry-free** (PR #1719): Frobenius character formula complete
- **Theorem5_25_2 → sorry-free** (confirmed): GL₂(𝔽_q) principal series classification
- **Proposition6_6_6** reduced from 5→2 sorrys (PRs #1715, #1723)
- **double_counting Part A** proved (PR #1718)

## 6. Tier Classification (updated)

| Tier | Description | Count | Examples |
|------|-------------|-------|----------|
| 1 | Achievable (1-2 sessions) | 5 | PowerSumCauchyBilinear, PolytabloidBasis, Prop6_6_7 |
| 2 | Hard but tractable | 4 | Prop6_6_6, CoxeterInfra, Problem6_9_1, Theorem5_18_4 (centralizer) |
| 3 | Significant infrastructure needed | 8 | Theorem5_27_1, MoritaStructural, Theorem5_18_4 (decomposition) |
| 4 | Deep blockers / SchurModule-dependent | ~26 | Theorem5_23_2 (9), Theorem5_22_1 (3), Corollary6_8_3/4, Example9_4_4 |

## 7. New Issues Created

| Issue | Title | Label |
|-------|-------|-------|
| #1729 | Ch9 + Infrastructure neglected — 4 sorrys with 0 recent PRs | status-check |
| #1731 | Theorem5_27_1 (Mackey machine) — 5 sorrys, no open issue | status-check |
| #1733 | Theorem5_18_4 Schur-Weyl — 4 sorrys | status-check |
| #1734 | Theorem2_1_2 (Gabriel's theorem) — 1 sorry, blocked on Ch6 | status-check |

## 8. items.json Updates

- `Chapter5/Theorem5.15.1`: `proof_partial` → `sorry_free`
- `Chapter5/Theorem5.25.2`: `proof_partial` → `sorry_free`

## Recommendations

1. **Continue SchurModule construction** (#1722) — highest ROI, unblocks ~21 sorrys
2. **Complete Ch6 Gabriel chain**: CoxeterInfra → Corollary6_8_3/4 → Theorem6_5_2 → Theorem2_1_2
3. **Attempt MoritaStructural** (#1729) — 2 easy wins in neglected Ch9/Infra
4. **Theorem5_18_4 centralizer** (#1733) — independent of SchurModule, 4 sorrys
5. **Deprioritize Tier 4** items until SchurModule is resolved
