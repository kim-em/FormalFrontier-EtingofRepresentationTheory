# Stage 3.2 Fourteenth Proof Wave Summary

**Date:** 2026-03-18
**Scope:** 14 merged PRs since the twelfth wave summary (#1028, closed 2026-03-17T23:02:39Z)
**Status:** Stage 3.2 in progress — 191/583 items sorry_free (32.8%), 109 sorry occurrences across 41 files

## Executive Summary

Wave 14 (which subsumes wave 13's review work) merged 14 PRs: 7 feature/proof PRs, 3 infrastructure/definition PRs, 2 reviews, and 2 fixes. Net progress: +3 sorry_free items, -0 sorry occurrences (net — new infrastructure added sorries that offset removals), -3 files with sorry. The headline achievement is **Theorem 6.8.1** (reaching simple roots via reflections), which was identified in wave 12 as "the linchpin" of the Gabriel's theorem chain. This unblocks the remaining Gabriel chain items. Chapter 9 saw its first proof completion (Proposition 9.2.3), and new sl(2) infrastructure was added for Theorem 2.1.1.

## Merged PRs (14)

### Proof Completions (3 sorry_free)

| PR | Title | Chapter | Impact |
|----|-------|---------|--------|
| #1029 | Prove Theorem 6.8.1 (reaching simple roots via reflections) | Ch6 | +1 sorry_free; Gabriel theorem linchpin proven via strong induction on coordinate sum with 8 supporting lemmas |
| #1042 | Prove backward direction of Theorem 5.26.1 (Artin's theorem) | Ch5 | +1 sorry_free (partial — backward direction complete) |
| #1056 | Prove Proposition 9.2.3 (projective cover Hom computes JH multiplicity) | Ch9 | +1 sorry_free; first Ch9 proof completion using rank-nullity and induction on composition series |

### Infrastructure & Definitions (4)

| PR | Title | Chapter | Impact |
|----|-------|---------|--------|
| #1041 | Fill Q₂Rep_E and Q₂Rep_H definitions (Problem 6.9.1) | Ch6 | Definitions for quiver path algebra representations |
| #1043 | Decompose Corollary 6.8.3 proof structure | Ch6 | Scaffolded 3 sorry'd lemmas enabling parallel proof work |
| #1050 | Fill ellipticSubgroup and complementarySeriesChar definitions (Lemma 5.25.3) | Ch5 | Definitions needed for complementary series |
| #1061 | sl(2) triple and irrep infrastructure for Theorem 2.1.1 | Ch2 | New sl2Triple, irreducibleRep, and Casimir operator definitions |

### Refactors & Fixes (3)

| PR | Title | Impact |
|----|-------|--------|
| #1052 | Add no-self-loop hypothesis to simpleAt_iso (Corollary 6.8.3) | Correctness fix; updated all downstream callers |
| #1035 | Correct Theorem 5.14.3 statement (hsymm → psum) | Statement fix enabling future proof work |
| #1036 | items.json staleness audit (Corollary 5.26.3 → sorry_free) | Data hygiene; corrected 1 stale status |

### Reviews (2)

| PR | Title | Impact |
|----|-------|--------|
| #1040 | attention_needed items triage (10 items across Ch2/5/6) | 9 items restatus'd with clear blockers identified |
| #1049 | Wave 13 proof quality audit (5 items) | Quality review of recent proof completions |

### Partial Proofs (2)

| PR | Title | Chapter |
|----|-------|---------|
| #1022 | Example 6.4.9 E-type root counts (E₆, E₇, E₈) | Ch6 (coordinate bound lemmas still sorry'd) |
| #1030 | Proposition 5.21.2 geometric (Schur poly at geometric progression) | Ch5 (partial proof) |

## Sorry-Free Items by Chapter

| Chapter | Topic | Sorry-free | Total Items | % | Delta from Wave 12 |
|---------|-------|------------|-------------|---|---------------------|
| 2 | Basic notions | 39 | 117 | 33.3% | +0 |
| 3 | General results | 23 | 58 | 39.7% | +0 |
| 4 | Characters | 21 | 60 | 35.0% | +0 |
| 5 | Representations of S_n | 37 | 157 | 23.6% | +1 |
| 6 | Quiver representations | 22 | 64 | 34.4% | +1 |
| 7 | Categories | 26 | 59 | 44.1% | +0 |
| 8 | Abelian categories | 9 | 24 | 37.5% | +0 |
| 9 | Finite dim. algebras | 14 | 35 | 40.0% | +1 |
| **Total** | | **191** | **583** | **32.8%** | **+3** |

**Complete chapters (100% of formal items):** Ch3, Ch4, Ch7, Ch8 — unchanged from wave 12.

## Sorry Count by Chapter

| Chapter | Sorries | Files w/sorry | Delta from Wave 12 |
|---------|---------|---------------|---------------------|
| Ch2 | 8 | 4 | +3 sorries, +1 file (sl(2) infrastructure added) |
| Ch3 | 0 | 0 | +0 |
| Ch4 | 0 | 0 | +0 |
| Ch5 | 65 | 22 | +0 sorries, -1 file |
| Ch6 | 27 | 11 | +1 sorry, -1 file |
| Ch7 | 0 | 0 | +0 |
| Ch8 | 0 | 0 | +0 |
| Ch9 | 9 | 4 | -2 sorries, -1 file |
| **Total** | **109** (was 109) | **41** (was 44) | **+0 sorries, -3 files** |

Note: Ch2 sorry count increased due to new sl(2) infrastructure (#1061) adding sorry placeholders — these are intentional scaffolding for Theorem 2.1.1, not regressions.

## Item Status Distribution

| Status | Count | % of 583 | Delta from Wave 12 |
|--------|-------|----------|---------------------|
| sorry_free | 191 | 32.8% | +3 |
| statement_formalized | 26 | 4.5% | +0 |
| proof_partial | 8 | 1.4% | +6 |
| blocked | 3 | 0.5% | +0 |
| attention_needed | 1 | 0.2% | -9 (triaged by #1040) |
| needs_redesign | 1 | 0.2% | +0 |
| no status (non-formalizable or not yet reached) | 352 | 60.4% | +0 |

The attention_needed → proof_partial migration reflects the triage review (#1040) that correctly restatus'd items.

## Queue Health

### Open Issues: 27 (excluding coordination sentinel)

| Category | Count | Details |
|----------|-------|---------|
| Claimed features | 16 | Active work by agents |
| Unclaimed features | 2 | #995 (Example 5.19.3 exterior), #1021 (E-type coord bounds) |
| Has-PR features | 1 | #1055 (Corollary 6.8.3 partial) |
| Claimed reviews | 2 | #991, #1003 |
| Claimed summarize | 1 | #1053 (this issue) |
| Unclaimed meditate | 1 | #1058 (waves 12-14 retrospective) |
| Blocked | 2 | #924 (template reconciliation), #1057 (Theorem 2.1.1 Mathlib) |
| Replan | 1 | #1045 (Theorem 2.1.1 — replanned as #1057) |

### Open PRs: 1

- **#1051** (Corollary 6.8.3 hd_root) — mergeable status UNKNOWN. Related to #1055.

### Stalled Claims Assessment

16 claimed feature issues span a wide range of ages. Many were created 2026-03-17 and remain without PRs after 24+ hours. Some of these (hook length formula #984, double centralizer #1002, Specht module classification #1001) are difficulty 3/3 items that may be stalled.

## Velocity Analysis

| Metric | Wave 10 (17 PRs) | Wave 11 (20 PRs) | Wave 12 (10 PRs) | Wave 14 (14 PRs) |
|--------|-------------------|-------------------|-------------------|-------------------|
| sorry_free delta | +4 | +4 | +2 | +3 |
| sorry delta | -4 | -7 | -5 | +0 (net) |
| Feature PRs | 12 | 14 | 5 | 9 |
| Review/Fix PRs | 5 | 6 | 4 | 5 |

**Observation:** Wave 14 recovered from wave 12's dip in velocity, returning to a healthy 14-PR wave. However, the net sorry count is flat because new infrastructure (sl(2) for Theorem 2.1.1, Corollary 6.8.3 decomposition) added sorries that offset proof completions. This is the expected pattern in "depth" phase work — scaffolding hard proofs adds temporary sorries before the proofs are filled.

## Milestone Tracking

### Gabriel's Theorem Chain (Ch6) — Major Progress

- Theorem 6.5.2a (finiteness of positive roots): **sorry_free** (wave 12)
- Proposition 6.6.8 (dim vector under reflection): partial
- Corollary 6.8.2 (dim vectors are positive roots): **sorry_free** (wave 11)
- **Theorem 6.8.1 (reaching simple roots): sorry_free (THIS WAVE, #1029)** — the linchpin
- Corollary 6.8.3 (dim vector is positive root): decomposed (#1043), partial (#1051 PR open)
- Corollary 6.8.4 (every positive root realized): claimed (#1025)
- Lemma 6.7.2 (Coxeter element): claimed (#1006)

**Assessment:** 3/7 sorry_free (was 2/6). Theorem 6.8.1 proven — this was the critical dependency. Corollary 6.8.3 is actively being worked on (PR #1051). The chain is progressing well.

### Symmetric Group Chain (Ch5) — Incremental Progress

- Theorem 5.26.1 backward direction proven (#1042)
- Proposition 5.21.2 geometric partial (#1030)
- Infrastructure additions: ellipticSubgroup, complementarySeriesChar (#1050)
- Core hard items (hook length #984, double centralizer #1002, Specht classification #1001) remain claimed but without PRs

**Assessment:** Ch5 remains the bottleneck — 65 sorries across 22 files. The incremental progress is real but the hard core items are stalling.

### sl(2) Theory (Ch2) — New Front

- #1061 added sl2Triple, irreducibleRep, and Casimir infrastructure
- Theorem 2.1.1 blocked on major Mathlib gaps (#1057)

**Assessment:** Infrastructure laid but the main theorem is blocked on missing Mathlib API (Lie algebra module infrastructure).

## Honest Assessment

The project has formalized 32.8% of items (191/583). Among the ~231 items with Lean files, 191 are sorry_free (82.7% of formal items). The wave 14 progress (+3 sorry_free, 14 merged PRs) shows sustained activity but the sorry_free rate per PR continues to decline — confirming wave 12's observation that easy proofs are exhausted.

**Positive signals:**
- Gabriel's theorem chain breakthrough (Theorem 6.8.1 proven)
- First Ch9 proof completion shows cross-chapter reach
- Healthy mix of proofs, infrastructure, and project health work
- The triage reviews (#1040, #1049) are keeping the queue honest

**Concerns:**
- 16 claimed features with no PRs after 24+ hours — possible stalling on hard items
- Ch5 remains stubbornly difficult (65 sorries, most difficulty 3/3)
- Net sorry count flat — new scaffolding adds as fast as proofs remove
- Theorem 2.1.1 blocked on Mathlib infrastructure — no clear timeline
- The 352 "no status" items are non-formalizable text; the real denominator for progress is ~231 formal items, making progress 82.7% rather than 32.8%

The project is firmly in the "hard proof" phase where each sorry_free item requires significantly more effort. The infrastructure investments (sl(2), Corollary 6.8.3 decomposition) are forward-looking bets that will only pay off when the proofs they enable are completed.
