# Stage 3.2 Eighth Proof Wave Summary

**Date:** 2026-03-18
**Scope:** 14 merged PRs since the seventh wave summary (#867, closed 2026-03-17T09:32Z)
**Status:** Stage 3.2 in progress — 179/583 items sorry_free (30.7%), 119 sorry occurrences across 53 files

## Executive Summary

The eighth wave landed 14 PRs, advancing sorry_free count from 178 to 179 (+1 item: Corollary 5.12.4). This wave continued the breadth-first pattern from Wave 7 — 6 PRs formalized statements or scaffolded definitions, while infrastructure work (merge conflict resolution, Aristotle escalation, meditate retrospective) accounted for most of the remaining PRs. The Ch6 reflection functor chain advanced further with Proposition 6.6.6 and 6.6.7 statements formalized. The meditate retrospective (#893) recommended pivoting to proof-heavy Wave 9 to work down the 43-item backlog.

## Merged PRs (14)

### Proof Completions (1)

| PR | Title | Chapter | Impact |
|----|-------|---------|--------|
| #895 | Prove Corollary 5.12.4 (S_n irreps over Q) | Ch5 | +1 sorry_free item |

### Statement Formalizations (4)

| PR | Title | Chapter |
|----|-------|---------|
| #898 | Proposition 6.6.6 + 6.6.7 statements (reflection functor chain) | Ch6 |
| #872 | Example 9.4.4 statement (Hilbert syzygies theorem) | Ch9 |
| #874 | Proposition 6.6.8 statements (dimension vector reflection) | Ch6 |
| #876 | Theorem 5.14.3 + 5.15.1 statements (character formulas) | Ch5 |

### Scaffolding & Escalation (3)

| PR | Title | Chapter |
|----|-------|---------|
| #897 | Scaffold Proposition 9.2.3 proof structure | Ch9 |
| #896 | Escalate Theorem 2.1.1(ii) to Aristotle | Ch2 |
| #885 | Define sourceMap and scaffold Proposition 6.6.5 | Ch6 |

### Infrastructure (2)

| PR | Title | Chapter |
|----|-------|---------|
| #884 | Complete mapLinear for reflectionFunctorPlus (6.6.3) | Ch6 |
| #883 | Ch6 Example 6.3.1 work | Ch6 |

### Reviews & Meta (2)

| PR | Title | Type |
|----|-------|------|
| #893 | Meditate: Stage 3.2 wave 8 retrospective | Meditate |
| #894 | Review: triage and resolve merge-conflicting PRs | Review |

### Merge Conflict Resolution (2)

| PR | Title |
|----|-------|
| #903 | Resolve PR #895 merge conflicts (Corollary 5.12.4) |
| #873/#875 | Superseded PRs for 6.6.8 and 5.14.3+5.15.1 (conflict pairs) |

## Sorry-Free Items by Chapter

| Chapter | Topic | Sorry-free | Formal Items | Formal % | Total | Overall % | Delta from Wave 7 |
|---------|-------|------------|-------------|----------|-------|-----------|-------------------|
| 2 | Basic notions | 39 | 42 | 92.9% | 117 | 33.3% | +0 |
| 3 | General results | 23 | 23 | **100%** | 58 | 39.7% | +0 |
| 4 | Characters | 21 | 21 | **100%** | 60 | 35.0% | +0 |
| 5 | Representations of S_n | 33 | 59 | 55.9% | 157 | 21.0% | **+1** |
| 6 | Quiver representations | 15 | 33 | 45.5% | 64 | 23.4% | +0 |
| 7 | Categories | 26 | 26 | **100%** | 59 | 44.1% | +0 |
| 8 | Abelian categories | 9 | 9 | **100%** | 24 | 37.5% | +0 |
| 9 | Finite dim. algebras | 13 | 18 | 72.2% | 35 | 37.1% | +0 |
| **Total** | | **179** | **231** | **77.5%** | **583** | **30.7%** | **+1** |

## Sorry Count by Chapter

| Chapter | Sorries | Files w/sorry | Notes |
|---------|---------|---------------|-------|
| Ch2 | 5 | 3 | Near completion (3 formal items remain) |
| Ch3 | 0 | 0 | Complete |
| Ch4 | 0 | 0 | Complete |
| Ch5 | 61 | 26 | Largest backlog; 18 scaffolded + 5 statement_formalized |
| Ch6 | 40 | 18 | Second largest; reflection functor chain advancing |
| Ch7 | 0 | 0 | Complete |
| Ch8 | 0 | 0 | Complete |
| Ch9 | 11 | 5 | 2 sent_to_aristotle + 3 statement_formalized |

## Sorry Count Trend

| Wave | Date | Sorry-free | Sorries | Files w/sorry | Items/PR | PRs |
|------|------|-----------|---------|---------------|----------|-----|
| Wave 1 | 2026-03-16 | 132 | ~226 | ~90 | -- | 32 |
| Wave 2 | 2026-03-16 | 147 | 193 | 79 | 0.5 | 27 |
| Wave 3 | 2026-03-17 | 157 | 166 | 72 | 0.8 | 13 |
| Wave 4 | 2026-03-17 | 167 | 150 | 67 | 1.0 | 10 |
| Wave 5 | 2026-03-17 | 170 | 141 | 64 | 0.2 | 14 |
| Wave 6 | 2026-03-17 | 176 | 129 | 56 | 0.6 | 10 |
| Wave 7 | 2026-03-17 | 178 | 129 | 54 | 0.1 | 14 |
| **Wave 8** | **2026-03-18** | **179** | **119** | **53** | **0.07** | **14** |

## Velocity Analysis

- **Items per PR**: 0.07 (1 item / 14 PRs) — the lowest ratio yet, reflecting continued breadth-first investment
- **Sorry reduction**: 10 sorries eliminated (129 -> 119), likely from mapLinear completion and scaffolding cleanup
- **Sorry files**: -1 (54 -> 53)
- **Cumulative sorry_free gain since Wave 1**: +47 items (132 -> 179)

The sorry count decline from 129 to 119 despite only 1 new sorry_free item indicates that some existing files had internal sorry counts reduced (partial proof progress) without fully reaching sorry_free status.

## Backlog Analysis

### Current Backlog: 43 items (down from 46 in Wave 7)

| Status | Count | Description |
|--------|-------|-------------|
| scaffolded | 29 | Lean file exists with sorry stubs |
| statement_formalized | 12 | Real mathematical statements, sorry proofs |
| proof_formalized | 2 | Partial proofs (Ch6 definitions 6.6.3, 6.6.4) |

### Backlog by Chapter

| Chapter | Scaffolded | Statement | Proof | Total Backlog |
|---------|-----------|-----------|-------|---------------|
| Ch2 | 0 | 1 | 0 | 1 |
| Ch5 | 18 | 5 | 0 | 23 |
| Ch6 | 11 | 3 | 2 | 16 |
| Ch9 | 0 | 3 | 0 | 3 |

Ch5 has the largest backlog (23 items, 53% of all backlog). Ch6 is second (16 items, 37%). Together they account for 90% of remaining proof work.

## Aristotle Pipeline Status

| Item | Status | Notes |
|------|--------|-------|
| Chapter2/Theorem2.1.1 | sent_to_aristotle | Part (ii) escalated this wave (PR #896) |
| Chapter2/Proposition2.7.1 | sent_to_aristotle | Awaiting result |
| Chapter5/Theorem5.12.2 | attention_needed | Import/axiom errors |
| Chapter5/Lemma5.15.3 | sent_to_aristotle | Sign convention fixed, re-submitted |
| Chapter5/Theorem5.17.1 | attention_needed | Import resolution failure |
| Chapter6/Example6.3.1 | sent_to_aristotle | Awaiting result |
| Chapter6/Proposition6.6.5 | sent_to_aristotle | Awaiting result |
| Chapter9/Theorem9.2.1 | sent_to_aristotle | Re-submitted with context files |
| Chapter9/Proposition9.2.3 | sent_to_aristotle | Scaffolded this wave (PR #897) |

**9 items in the Aristotle pipeline** (7 sent_to_aristotle, 2 attention_needed). Cumulative success rate remains low. The meditate retrospective recommended treating Aristotle as a non-critical path dependency.

## Key Observations

1. **Proof throughput at historic low**: Only 1 sorry_free item gained across 14 PRs. The project has been in breadth-first mode for two consecutive waves (Waves 7-8). The 43-item backlog is well-stocked for a proof-focused pivot.

2. **Ch6 reflection functor chain nearly scaffolded**: The 6.6.3 -> 6.6.4 -> 6.6.5 -> 6.6.6 -> 6.6.7 -> 6.6.8 chain now has all statements formalized. The chain is ready for proof work, though the underlying type-level plumbing remains complex.

3. **Corollary 5.12.4 proved**: The sole proof completion this wave — S_n irreps over Q are absolutely irreducible. This required merge conflict resolution (#903) before landing.

4. **Merge conflicts consuming effort**: 2 of 14 PRs were merge conflict resolution (#894, #903). This overhead grows as more agents work on adjacent files.

5. **Four chapters remain at 100%**: Ch3, Ch4, Ch7, Ch8 — no regression across eight waves.

6. **No open PRs**: The PR queue is clear, indicating good merge discipline.

## Chapter Closure Assessment

| Chapter | Remaining Formal Items | Blockers | Priority |
|---------|----------------------|----------|----------|
| Ch2 | 3 (Thm 2.1.1, Thm 2.1.2, Prop 2.7.1) | 2 sent_to_aristotle, 1 statement_formalized (needs infrastructure) | Medium — depends on Aristotle results |
| Ch9 | 5 (9.2.1, 9.2.3, 9.4.4, 9.6.4, 9.7.3) | 2 sent_to_aristotle, 3 statement_formalized | Medium — good proof targets |
| Ch5 | 26 items | Mixed difficulty, 18 scaffolded | Low for closure, high for throughput |
| Ch6 | 18 items | Infrastructure complexity, 11 scaffolded | Medium — chain now ready |

**Nearest closure candidate**: Ch9 at 72.2% formal completion (13/18), but 2 items depend on Aristotle. Ch2 at 92.9% (39/42) has the highest formal % but its 3 remaining items are all hard.

## Recommendations for Wave 9

### Tier 1: Pivot to Proof Work (Critical)
- The backlog has 43 items ready for proof attempts. Wave 9 should be 80%+ proof issues.
- **Priority proof targets**:
  - Ch9 statement_formalized items (9.4.4, 9.6.4, 9.7.3) — well-scoped, dependencies met
  - Ch6 reflection functor proofs (6.6.6, 6.6.7, 6.6.8) — chain is ready
  - Ch5 items with all dependencies sorry_free

### Tier 2: Poll and Integrate Aristotle Results
- 7 items are sent_to_aristotle. Poll all of them.
- If any succeed, integrate immediately (+1 sorry_free each)
- If most fail, consider deprioritizing Aristotle and having agents prove directly

### Tier 3: Address attention_needed Items
- Ch5/Theorem5.12.2 and Ch5/Theorem5.17.1 have Aristotle submission failures
- Either fix submission files and retry, or attempt proofs directly

### Tier 4: Ch2 Closure Attempt
- Only viable if Aristotle returns results for Thm 2.1.1 and Prop 2.7.1
- Otherwise, may need to accept these as long-term sorry items requiring infrastructure not yet available in Mathlib
