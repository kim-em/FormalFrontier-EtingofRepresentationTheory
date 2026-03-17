# Stage 3.2 Eighth Proof Wave Retrospective

**Date:** 2026-03-18
**Scope:** 22 merged PRs since meditate #843 (closed 2026-03-17T08:42Z), covering Waves 7-8
**Status:** Stage 3.2 in progress — 178/583 items sorry_free (30.5%), 119 sorry occurrences across 54 files

## Executive Summary

Since the last meditate, 22 PRs landed but only 4 new items became sorry_free (+4, from 174 to 178). This wave was dominated by **statement formalization and scaffolding** — 12 PRs formalized new statements or scaffolded definitions across Ch2, Ch5, Ch6, and Ch9. The remaining PRs were proof completions (3), infrastructure/skill updates (3), reviews (1), summaries (1), and duplicate/rebase fixes (2). The project has entered a **breadth-first expansion phase**, building a large frontier of provable items (46 items in the formalized-but-not-proved backlog) before the next proof wave.

Key developments: Theorem 5.12.2 distinct (Specht module non-isomorphism) was proved, the Ch6 reflection functor chain advanced significantly (6.6.3 mapLinear completed, 6.6.5 scaffolded with sourceMap, 6.6.8 formalized), and Lemma 6.4.6 (root coordinates) was proved sorry-free. Aristotle continues to have mixed results — 3 items in `attention_needed`, 4 items `sent_to_aristotle`.

## Quantitative Analysis

### Velocity Trend

| Metric | Wave 5 | Wave 6 | Wave 7 | Wave 8 (combined) | Trend |
|--------|--------|--------|--------|-------------------|-------|
| PRs merged | 33 | 25 | 14 | 22 | Stable at lower level |
| Items sorry_free gained | +7 | +8 | +2 | +4 | Decreasing |
| Sorry count | 141→129 | 129→129 | 129→129 | 129→119 | Finally declining again |
| Statement formalizations | 2 | 3 | 7 | 12 | Growing rapidly |
| Items/PR | 0.2 | 0.3 | 0.1 | 0.2 | Low — statement-heavy |

**Interpretation:** The project has shifted from "prove existing sorry'd items" to "formalize new statements to expand the frontier." The 12 statement formalizations create future proof opportunities but don't immediately increase the sorry_free count. The sorry count dropping from 129 to 119 indicates that some sorry-removal happened even as new sorry'd statements were added — a sign that both fronts are active.

### Chapter Completion Status

| Chapter | Sorry-free | Formal | Formal % | Total | Overall % | Delta |
|---------|-----------|--------|----------|-------|-----------|-------|
| 2 | 39 | 42 | 92.9% | 117 | 33.3% | +0 |
| 3 | 23 | 23 | **100%** | 58 | 39.7% | +0 |
| 4 | 21 | 21 | **100%** | 60 | 35.0% | +0 |
| 5 | 32 | 59 | 54.2% | 157 | 20.4% | +0 |
| 6 | 15 | 33 | 45.5% | 64 | 23.4% | **+2** |
| 7 | 26 | 26 | **100%** | 59 | 44.1% | +0 |
| 8 | 9 | 9 | **100%** | 24 | 37.5% | +0 |
| 9 | 13 | 18 | 72.2% | 35 | 37.1% | +0 |
| **Total** | **178** | **231** | **77.1%** | **583** | **30.5%** | **+4** |

**Note:** Ch6 gained +2 sorry_free items (Lemma 6.4.6, Definition 6.6.3 mapLinear). Ch5 gained Theorem 5.12.2 distinct but this was a new sorry_free item added to existing infrastructure. Four chapters remain at 100% (Ch3, Ch4, Ch7, Ch8).

### Sorry Count by Chapter

| Chapter | Sorries | Files w/sorry | Notes |
|---------|---------|---------------|-------|
| Ch2 | 5 | 3 | Near completion (3 formal items remain) |
| Ch3 | 0 | 0 | Complete |
| Ch4 | 0 | 0 | Complete |
| Ch5 | 62 | 27 | Largest backlog |
| Ch6 | 41 | 18 | Second largest; reflection functor chain advancing |
| Ch7 | 0 | 0 | Complete |
| Ch8 | 0 | 0 | Complete |
| Ch9 | 9 | 5 | Moderate; 4 new statements formalized this wave |

## Merged PRs (22)

### Proof Completions (3)

| PR | Title | Chapter | Impact |
|----|-------|---------|--------|
| #859 | Prove Lemma 6.4.6 (root coordinates nonneg/nonpos) | Ch6 | Sorry-free; +157 lines |
| #880 | Prove Theorem 5.12.2 distinct (Specht non-isomorphism) | Ch5 | Sorry-free; +200/-71 |
| #884 | Complete mapLinear for reflectionFunctorPlus (6.6.3) | Ch6 | Partial — fills mapLinear field |

### Statement Formalizations (12)

| PR | Title | Chapter |
|----|-------|---------|
| #848 | Theorem 5.17.1 (hook length formula) statement + Aristotle escalation | Ch5 |
| #849 | Theorem 2.1.1 (sl(2) irreps classification) | Ch2 |
| #850 | Proposition 2.7.1 (Weyl algebra basis) | Ch2 |
| #852 | Proposition 5.14.1 (Kostka decomposition) | Ch5 |
| #853 | Theorem 2.1.2 (Gabriel's theorem) | Ch2 |
| #860 | Theorem 9.6.4 + Corollary 9.7.3 (Morita equivalence) | Ch9 |
| #861 | Corollary 5.12.4 + Proposition 2.7.1 Aristotle escalation | Ch5+Ch2 |
| #862 | Proposition 6.6.5 (indecomposable surjective at sinks) | Ch6 |
| #866 | Proposition 9.2.3 (projective cover hom multiplicity) | Ch9 |
| #872 | Example 9.4.4 (Hilbert syzygy theorem) | Ch9 |
| #873/#874 | Proposition 6.6.8 (dimension vector reflection) | Ch6 |
| #875/#876 | Theorem 5.14.3 + 5.15.1 (character formulas) | Ch5 |

### Scaffolding (1)

| PR | Title | Chapter |
|----|-------|---------|
| #851 | Scaffold reflection functor bodies (6.6.3, 6.6.4) | Ch6 |

### Infrastructure / Refactoring (1)

| PR | Title |
|----|-------|
| #885 | Define sourceMap and scaffold Proposition 6.6.5 | Ch6 |

### Reviews & Meta (3)

| PR | Title | Type |
|----|-------|------|
| #854 | Document type-level if/else diamond | Chore (skill update) |
| #858 | Poll Aristotle results and integrate (9.2.1, 5.12.2, 6.3.1) | Review |
| #868 | Wave 7 progress summary | Summary |

### Duplicate/Rebase (2)

PRs #873/#874 and #875/#876 each had a rebase pair — the first PR was superseded by the second with conflict resolution.

## Pattern Analysis

### What Worked Well

#### 1. Breadth-First Statement Formalization (Strategic Investment)

12 of 22 PRs were statement formalizations — the largest such batch in the project's history. This created 12+ new provable items across 4 chapters, expanding the frontier for future proof waves. The backlog of formalized-but-not-proved items grew from ~34 to 46, creating a healthy pipeline of proof opportunities.

**Why this matters:** The "easy proof" era is over (Waves 1-4 captured those). Future proof work requires real mathematical statements as targets. This wave ensured proof agents won't run out of work.

#### 2. Ch6 Reflection Functor Chain Progress (End-to-End Advancement)

The Ch6 reflection functor chain (6.6.3 → 6.6.4 → 6.6.5 → 6.6.6 → 6.6.7 → 6.6.8) saw coordinated advancement across 6 PRs (#851, #862, #873/874, #884, #885). Key milestones:
- 6.6.3: mapLinear completed (PR #884)
- 6.6.4: bodies scaffolded (PR #851)
- 6.6.5: sourceMap defined and scaffolded (PR #885)
- 6.6.8: dimension vector reflection formalized (PR #874)

This is the first time the Ch6 pipeline has seen sustained multi-PR progress. The concrete construction approach (documented in Wave 5) continues to work.

#### 3. Theorem 5.12.2 Distinct (Clean Proof Pattern)

PR #880 proved the non-isomorphism of distinct Specht modules — a key result in the Specht module classification chain. The proof was self-contained (+200/-71 lines) and didn't require Aristotle escalation. This demonstrates that even in the "hard proof" phase, focused single-session proofs are possible for well-scoped theorems.

#### 4. Aristotle Result Polling (PR #858)

The review PR #858 polled Aristotle results for 3 items (9.2.1, 5.12.2, 6.3.1) and updated items.json accordingly. This housekeeping prevented stale state accumulation — a problem identified in the previous meditate.

### What Struggled

#### 1. Aristotle Pipeline Effectiveness (Low Success Rate)

Current Aristotle pipeline status:
- **sent_to_aristotle (4):** Ch2/Prop2.7.1, Ch5/Lemma5.15.3, Ch6/Prop6.6.5, Ch9/Thm9.2.1
- **attention_needed (3):** Ch5/Thm5.12.2 (import errors), Ch5/Thm5.17.1 (import errors), Ch6/Example6.3.1

**0 successful Aristotle integrations this wave.** Common failure modes:
- Import resolution failures (Aristotle can't resolve `EtingofRepresentationTheory.*` imports)
- Even with `--context-files`, the module prefix causes load failures
- The skill already documents the workaround (inline dependencies, use `--no-auto-add-imports --no-validate-lean-project`), but agents are still hitting issues

**Root cause:** The self-contained file preparation is error-prone. Each submission requires manually inlining all local dependencies and stripping local imports — a mechanical but tedious process that agents frequently get wrong.

**Recommendation:** Add a concrete checklist/template to the skill for Aristotle file preparation, with a worked example showing before/after transformation.

#### 2. Duplicate PRs from Rebase Conflicts (Wasted Effort)

Two PR pairs (#873/#874 and #875/#876) were duplicates — the first PR had merge conflicts resolved by creating a second. This represents 4 PRs for 2 logical changes, adding noise to the PR history and wasting CI cycles.

**Root cause:** Multiple agents working on adjacent files in Ch5 and Ch6 created merge conflicts. The current guidance says "salvage, don't restart" but agents are creating new PRs instead of rebasing the original.

**Recommendation:** Strengthen the "rebase existing PR" guidance. When a conflict is simple (< 5 files), rebase and force-push-with-lease rather than creating a new PR.

#### 3. Low Proof Throughput (4 items / 22 PRs = 18% proof rate)

Only 3 of 22 PRs were proof completions, yielding 4 sorry_free items. This is the lowest proof rate in the project's history. While the statement formalization investment is strategic, it means the sorry count is barely declining.

**Mitigation:** This is expected during a breadth-first phase. The next wave should pivot back to proof work, leveraging the expanded frontier. The 46-item backlog provides ample proof targets.

#### 4. FDRep Plumbing (Still Persistent, No New Progress)

The #1 infrastructure blocker for character theory remains unfixed. No new infrastructure or workaround patterns were developed this wave. The non-categorical workaround pattern from Wave 5 is still sufficient for most cases, but it limits progress on Ch5 items that genuinely need categorical structure.

**Status:** Accepted technical debt. A dedicated infrastructure session would be needed to fix this, and the ROI decreases as more workarounds exist.

### Statement vs Proof Ratio Assessment

| Metric | Value | Assessment |
|--------|-------|------------|
| Total formalized items | 231 | Growing (was 231 at start of wave — most new formalizations are statement-level) |
| Sorry-free items | 178 | 77.1% of formalized items |
| Scaffolded backlog | 31 | Stable |
| Statement-formalized backlog | 13 | Grew from ~6 |
| Proof-formalized (partial) | 2 | Ch6 definitions with partial proofs |

The backlog is healthy — 46 items in the pipeline is enough to keep 4-6 proof agents busy for the next wave without running out of targets. The ratio of statement formalizations to proofs should rebalance toward proofs in Wave 9.

### Chapter Closure Opportunities

| Chapter | Remaining | Items | Difficulty | Priority |
|---------|-----------|-------|------------|----------|
| Ch2 | 3 items | Thm 2.1.1, Thm 2.1.2, Prop 2.7.1 | Mixed (2.7.1 sent to Aristotle, 2.1.1/2.1.2 need infrastructure) | Medium — `needs_infrastructure` items may block |
| Ch9 | 5 items | 9.2.1, 9.2.3, 9.4.4, 9.6.4, 9.7.3 | Mixed (9.2.1 sent to Aristotle) | Medium |
| Ch5 | 27 items | Large backlog | Hard (combinatorial, character theory) | Low priority for closure, high priority for throughput |
| Ch6 | 18 items | Reflection functors, quiver theory | Medium-Hard | Medium — chain advancing |

**Near-term closure candidate:** None — Ch2 and Ch9 both have items blocked by Aristotle or infrastructure gaps. Focus should be on proof throughput across all chapters rather than targeted closure.

## Aristotle Effectiveness Analysis

### Submission History (All Waves)

| Item | Submissions | Result | Failure Mode |
|------|------------|--------|-------------|
| Ch9/Thm9.2.1 | 2+ | Still pending | Import errors, re-submitted with context |
| Ch5/Thm5.12.2 | 2+ | attention_needed | Import/axiom/namespace errors |
| Ch5/Thm5.17.1 | 1 | attention_needed | Import resolution failure |
| Ch5/Lemma5.15.3 | 2 | Re-submitted | Sign convention fixed, awaiting result |
| Ch6/Example6.3.1 | 1+ | attention_needed | Unknown |
| Ch2/Prop2.7.1 | 1 | Pending | Awaiting result |
| Ch6/Prop6.6.5 | 1 | Pending | Awaiting result |

**Success rate this wave:** 0/7 items resolved by Aristotle.
**Cumulative success rate:** Very low — most submissions fail at the import/load stage rather than at the proof stage.

**Assessment:** Aristotle is not currently a reliable proof pipeline for this project. The primary failure mode is import resolution, not proof difficulty. Until a more robust file preparation process is established, Aristotle should be treated as a "nice to have" rather than a critical path dependency.

**Recommendations:**
1. Create a dedicated `scripts/prepare-aristotle.sh` helper that automates the file preparation (strip local imports, inline dependencies, validate compilation)
2. Batch-test the preparation process on 2-3 items before submitting more
3. Don't block proof planning on Aristotle results — treat all `sent_to_aristotle` items as if they will fail

## Concrete Skill/Command Changes

### 1. lean-formalization/SKILL.md — Updates

- **Aristotle File Preparation Checklist**: Add step-by-step checklist with before/after example for creating self-contained submission files
- **Breadth-vs-Depth Phase Awareness**: Document the statement-formalization-then-proof cycle as a deliberate strategy, not a failure mode

### 2. parallel-agent-coordination/SKILL.md — Updates

- **Rebase vs New PR guidance**: Strengthen guidance to prefer rebasing over creating duplicate PRs for simple merge conflicts
- **Phase awareness for planners**: When backlog > 40 items, pivot planner issues toward proof work rather than more statement formalizations

## Recommendations for Wave 9

### Tier 1: Proof Throughput (Pivot Back to Proofs)
- The backlog has 46 items ready for proof work — focus the next wave on proofs, not more statement formalizations
- Target items with all dependencies sorry-free first (check `internal.json`)
- Ch6 items that recently had reflection functor infrastructure completed
- Ch9 items with newly formalized statements (9.2.3, 9.4.4, 9.6.4, 9.7.3)

### Tier 2: Aristotle Pipeline Fix
- Create `scripts/prepare-aristotle.sh` automation
- Re-submit items in `attention_needed` with properly prepared files
- If success rate doesn't improve, consider deprioritizing Aristotle entirely

### Tier 3: Ch2 Closure Attempt
- 3 remaining items — but 2 need infrastructure (sl(2) classification, Gabriel's theorem) and 1 is sent to Aristotle
- May need to accept that Ch2 formal completion requires quiver/Lie algebra infrastructure not yet in Mathlib

### Tier 4: Ch6 Reflection Functor Chain Completion
- Continue the 6.6.3→6.6.8 chain with proof work now that scaffolding is done
- The type-level if/else diamond workaround is documented — agents should use `sorry` for the affected fields and focus on the mathematical content

### Meta-Recommendation: Rebalance Statement/Proof Ratio
The project should enter a **proof-heavy phase** for Wave 9. The 46-item backlog provides ample targets. Planners should create mostly proof issues (80%+) and limit new statement formalizations to items that unblock proof chains.
