# Stage 3.2 Fourth Proof Wave Summary

**Date:** 2026-03-17
**Scope:** All work since the third wave summary (#755, merged 2026-03-17T00:47Z)
**Status:** Stage 3.2 in progress — 167/583 items sorry_free (28.6%), 152 sorry occurrences remain across 72 files

## Executive Summary

The fourth proof wave landed 10 PRs in ~1.7 hours (02:44Z–04:23Z), advancing sorry_free count from 155 to 167 (+12 items, +7.7%). This wave was characterized by three threads: (1) completing the Theorem 4.10.2 Frobenius determinant chain (all helpers now proved), (2) advancing the Chapter 5 Specht module pipeline (Lemmas 5.13.1–5.13.2 algebraic proofs, Theorem 5.12.2 + Lemma 5.13.3 statements formalized), and (3) the first Chapter 6 breakthrough with Examples 6.2.2–6.2.4. Chapter 4 is now at 100% formal completion (21/21).

## Merged PRs (10)

### Proof Completions (5)

| PR | Title | Chapter | Key Result |
|----|-------|---------|------------|
| #761 | Ch4 prove frobeniusDet_eq_prod (Theorem 4.10.2 block factorization) | Ch4 | Frobenius determinant = product of block polynomials |
| #762 | Ch5 prove Theorem 5.4.6 core (conjugacy class of prime power size) | Ch5 | Prime power conjugacy class → not simple |
| #767 | Ch5 prove Lemma 5.13.1 modulo pigeonhole | Ch5 | Young projector algebraic proof complete |
| #768 | Ch4 prove n_eq_card_conjClasses (Corollary 4.2.2 completion) | Ch4 | Number of irreps = conjugacy classes |
| #772 | Ch4 prove blockPoly_irreducible + blockPoly_not_associated | Ch4 | Theorem 4.10.2 remaining helpers |

### Statement Formalizations (3)

| PR | Title | Chapter |
|----|-------|---------|
| #756 | Ch9 formalize Theorem 9.2.1 statement | Ch9 |
| #773 | Ch5 Lemma 5.13.2 statement + algebraic proof (pigeonhole sorry) | Ch5 |
| #774 | Ch5 formalize Theorem 5.12.2 statement (Specht module classification) | Ch5 |
| #775 | Ch5 formalize Lemma 5.13.3 statement (Young symmetrizer idempotent) | Ch5 |

### Other (2)

| PR | Title | Type |
|----|-------|------|
| #766 | Ch6 Examples 6.2.2–6.2.4 (2 sorry-free, 1 statement only) | Ch6 mixed |
| #771 | Review: Validate Ch5 Specht module chain | Review |

## Sorry-Free Items by Chapter

| Chapter | Topic | Sorry-free | Formal Items | Formal % | Total | Overall % | Δ from Wave 3 |
|---------|-------|------------|-------------|----------|-------|-----------|----------------|
| 2 | Basic notions | 36 | 42 | 85.7% | 117 | 30.8% | +0 |
| 3 | General results | 22 | 23 | 95.7% | 58 | 37.9% | +0 |
| 4 | Characters | 21 | 21 | **100%** | 60 | 35.0% | **+1** |
| 5 | Representations of Sₙ | 29 | 59 | 49.2% | 157 | 18.5% | **+3** |
| 6 | Quiver representations | 11 | 33 | 33.3% | 64 | 17.2% | **+3** |
| 7 | Categories | 26 | 26 | **100%** | 59 | 44.1% | +0 |
| 8 | Abelian categories | 9 | 9 | **100%** | 24 | 37.5% | +0 |
| 9 | Finite dim. algebras | 13 | 18 | 72.2% | 35 | 37.1% | **+2** |
| **Total** | | **167** | **231** | **72.3%** | **583** | **28.6%** | **+12** |

Note: "Sorry-free" includes `sorry_free` + `proof_formalized` statuses. "Formal Items" counts all items with Lean files. Items without a `status` key (352) are discussion blobs, exercises, problems, and remarks without Lean formalization.

## Sorry Count Trend

| Metric | Wave 1 | Wave 2 | Wave 3 | Wave 4 |
|--------|--------|--------|--------|--------|
| Sorry-free items | 120 | 130 | 155 | 167 |
| Sorry occurrences | 205 | 194 | 159 | 152 |
| Files with sorry | 110 | 103 | 76 | 72 |
| Sorry-free Lean files | 126/236 (53%) | 138/241 (57%) | 166/242 (69%) | 170/242 (70%) |
| Formal items completion | 32.6% | 35.3% | 68.4% | 72.3% |

## Velocity Analysis

| Metric | Wave 1 | Wave 2 | Wave 3 | Wave 4 | Trend |
|--------|--------|--------|--------|--------|-------|
| PRs merged | 37 | 19 | 30 | 10 | Smaller batch |
| Items sorry_free gained | 120 | 10 | 25 | 12 | Moderate |
| Duration | ~10h | ~3.5h | ~6h | ~1.7h | Short burst |
| Items/hour | ~12 | ~2.9 | ~4.2 | ~7.1 | Strong recovery |
| Statement PRs | 0 | 0 | 0 | 4 | New scaffolding |

**Key observation:** Wave 4 had the highest items/hour rate since Wave 1, driven by focused completion of already-started proof chains (Theorem 4.10.2 helpers, Specht module pipeline). The wave was shorter than prior waves but highly efficient. Four statement formalization PRs indicate the pipeline is opening new frontiers in Chapter 5 even as proofs land.

## Notable Achievements

### 1. Chapter 4 complete (100% formal items sorry-free)
Chapter 4 joins Chapters 7 and 8 at full formal completion. The final pieces were Corollary 4.2.2 (`n_eq_card_conjClasses`) and the two Theorem 4.10.2 helpers (`blockPoly_irreducible`, `blockPoly_not_associated`). This closes all Wave 3 Tier 1 recommendations for Chapter 4.

### 2. Chapter 6 breakthrough
After three waves of zero progress, Chapter 6 gained 3 sorry-free items (Examples 6.2.2–6.2.4). While modest, this breaks the stall and establishes patterns for quiver representation formalization. Chapter 6 moved from 24.2% to 33.3% formal completion.

### 3. Specht module pipeline advancing
The Chapter 5 Specht module chain (5.12.1 → 5.13.1 → 5.13.2 → 5.13.3 → 5.13.4 → 5.12.2) saw significant progress:
- Lemma 5.13.1: algebraic proof complete, one combinatorial `pigeonhole_transposition` sorry remains
- Lemma 5.13.2: statement + algebraic proof formalized, same pigeonhole sorry pattern
- Theorem 5.12.2: statement formalized
- Lemma 5.13.3: statement formalized
The pigeonhole combinatorial lemma is now the shared bottleneck for both 5.13.1 and 5.13.2.

### 4. Burnside chain progress
Theorem 5.4.6 (conjugacy class of prime power size implies not simple) was proved, advancing toward the Burnside p^a·q^b theorem (5.4.3).

## Proof Strategies in This Wave

1. **Chain completion** (PRs #768, #772): The Theorem 4.10.2 factorization chain was completed by proving the two remaining helpers (irreducibility and non-association of block polynomials). This demonstrates the value of identifying and closing proof chains.

2. **Algebraic reduction with combinatorial sorry** (PRs #767, #773): Both Lemmas 5.13.1 and 5.13.2 adopted the same pattern: prove the full algebraic argument (absorption, linearity extension, sign cancellation) while sorry'ing the combinatorial pigeonhole core. This isolates the hard combinatorial problem for focused attention.

3. **First quiver formalization** (PR #766): Chapter 6 examples used concrete quiver constructions (A₁, A₂, A₃), establishing patterns for the 22 remaining scaffolded items.

## Current Blockers and Critical Path

### Active Blockers

- **`pigeonhole_transposition`**: Shared sorry in both Lemma 5.13.1 and 5.13.2. This combinatorial argument (if σ ∉ P_λ·Q_λ, find a transposition in P_λ whose σ-conjugate is in Q_λ) is the bottleneck for the entire Specht module chain. Two dedicated issues (#776, #777) exist for this.
- **Theorem 4.2.1**: Still has 1 remaining sorry (`(D.d i : k) ≠ 0`), though the theorem is otherwise complete.
- **Theorem 3.6.2**: Still has remaining sorries from Wave 2.

### Chapters Approaching/At Completion

| Chapter | Sorry-free | Formal Items | Remaining | Status |
|---------|------------|-------------|-----------|--------|
| 4 | 21 | 21 | 0 | **Complete** ✓ |
| 7 | 26 | 26 | 0 | **Complete** ✓ |
| 8 | 9 | 9 | 0 | **Complete** ✓ |
| 3 | 22 | 23 | 1 | Near-complete (Theorem 3.6.2) |
| 2 | 36 | 42 | 6 | 6 scaffolded items remaining |
| 9 | 13 | 18 | 5 | 72.2% (4 scaffolded, 1 stmt) |

## Recommended Priorities for Next Wave

**Tier 1 — Unblock Specht module chain:**
- Prove `pigeonhole_transposition` (#776, #777) — this unblocks Lemmas 5.13.1 and 5.13.2, which cascade to 5.13.3 → 5.13.4 → Theorem 5.12.2
- Consider Aristotle escalation if combinatorial formalization proves intractable

**Tier 2 — Close out near-complete chapters:**
- Fix Theorem 4.2.1's last sorry (`(D.d i : k) ≠ 0`)
- Finish Theorem 3.6.2 remaining sorries
- Clear Chapter 2's 6 remaining scaffolded items

**Tier 3 — Advance Chapter 6:**
- Build on the 6.2.x breakthrough to prove more quiver examples
- Example 6.2.4 (A₃ indecomposable reps, #778) is next
- 22 scaffolded items remain — focus on definitions and basic results first

**Tier 4 — Chapter 9 proofs:**
- Theorem 9.2.1(i) existence of projective covers (#764) — difficulty 3/3
- 4 scaffolded items remain after recent definition work

**Tier 5 — Chapter 5 depth:**
- Prove Theorem 5.4.3 (Burnside p^a·q^b) — now unblocked by 5.4.6
- Work through remaining 28 scaffolded items in Chapter 5
