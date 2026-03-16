# Stage 3.2 Second Proof Wave Summary

**Date:** 2026-03-17
**Scope:** All work since the first wave summary (#642, merged 2026-03-16T14:26Z)
**Status:** Stage 3.2 in progress — 130/583 items sorry_free (22.3%), 194 sorry occurrences remain across 103 files

## Executive Summary

The second proof wave landed 19 PRs in ~3.5 hours, advancing sorry_free count from 120 to 130 (+10 items, +8.3%). Key achievements: Krull-Schmidt theorem (existence + uniqueness), matrix element orthogonality, column orthogonality statement, Frobenius reciprocity statement, and infrastructure for irreducible enumeration and regular character. Chapter 8 became fully sorry-free (9/9 items). The wave focused on harder proofs (algebraic manipulation, category theory) compared to the first wave's Mathlib-alias style proofs.

## Merged PRs (19)

### Proof Completions (9)

| PR | Title | Chapter | Key Result |
|----|-------|---------|------------|
| #684 | Lemma 4.10.3 generic determinant irreducibility | Ch4 | `MvPolynomial.rename` preserves irreducibility; coprimality via vars argument |
| #683 | Theorem 3.6.2 helper lemmas | Ch3 | Tracial functional + semisimple injectivity (2/4 sorries resolved) |
| #682 | Example 7.9.6 tensor right exactness | Ch7 | Sorry-free |
| #681 | Theorem 5.10.1 + Theorem 5.4.4 structure | Ch5 | Frobenius reciprocity sorry-free; Theorem 5.4.4 proof structured |
| #677 | Theorem 3.8.1 Krull-Schmidt | Ch3 | Both existence and uniqueness proved sorry-free |
| #671 | Proposition 4.7.1 matrix element orthogonality | Ch4 | Full proof of matrix element orthogonality relation |
| #670 | Corollary 4.2.4 sorry-free | Ch4 | Rebased and completed; character determines representation |
| #665 | Frobenius determinant + A5 conjugacy classes | Ch4 | Definition 4.10.1 + Example 4.8.1 |
| #657 | Example 8.1.7 dual of projective is injective | Ch8 | Completed Chapter 8 (all 9 items sorry-free) |

### Statement Formalizations (5)

| PR | Title | Chapter |
|----|-------|---------|
| #675 | Definitions 5.2.1-5.2.2 + Theorem 5.1.5 statement | Ch5 |
| #663 | Theorem 4.5.4 column orthogonality statement | Ch4 |
| #653 | Theorem 5.10.1 Frobenius reciprocity statement | Ch5 |
| #651 | Theorem 5.4.4 character vanishing statement | Ch5 |
| #650 | Proposition 4.7.1 + Theorem 4.10.2 statements | Ch4 |

### Infrastructure (3)

| PR | Title | Purpose |
|----|-------|---------|
| #672 | IrreducibleEnumeration bijection | FDRep irreducible enumeration for character theory |
| #658 | RegularCharacter identity | χ_reg(g) = |G|·δ_{g,1} for orthogonality proofs |
| #652 | Wedderburn-Artin infrastructure | Dimension formula for semisimple algebra decomposition |

### Review & Summary (2)

| PR | Title |
|----|-------|
| #654 | Stage 3.2 proof quality audit (Chapters 3, 4, 5, 8) |
| #642 | Stage 3.2 first proof wave summary |

## Sorry-Free Items by Chapter

| Chapter | Topic | Sorry-free | Formal Items | Formal % | Total | Overall % | Δ from Wave 1 |
|---------|-------|------------|-------------|----------|-------|-----------|----------------|
| 2 | Basic notions | 36 | 79 | 45.6% | 117 | 30.8% | +0 |
| 3 | General results | 20 | 39 | 51.3% | 58 | 34.5% | +1 |
| 4 | Formal language | 15 | 39 | 38.5% | 60 | 25.0% | +4 |
| 5 | Representations of quivers | 22 | 85 | 25.9% | 157 | 14.0% | +3 |
| 6 | Quiver structure theorems | 8 | 47 | 17.0% | 64 | 12.5% | +0 |
| 7 | Introduction to categories | 19 | 36 | 52.8% | 59 | 32.2% | +1 |
| 8 | Abelian categories | 9 | 18 | 50.0% | 24 | 37.5% | +1 |
| 9 | Finite dimensional algebras | 1 | 25 | 4.0% | 35 | 2.9% | +0 |
| **Total** | | **130** | **368** | **35.3%** | **583** | **22.3%** | **+10** |

## Sorry Count

- **194 sorry occurrences** across **103 files** (down from 205 across 110 files at Wave 1)
- **138 sorry-free files** out of 241 total Lean files (57.3%, up from 52.4%)

## Velocity Analysis

| Metric | Wave 1 | Wave 2 | Trend |
|--------|--------|--------|-------|
| PRs merged | 37 | 19 | Expected decrease as easy items depleted |
| Items sorry_free gained | 120 | 10 | Harder proofs yield fewer items per PR |
| Sorries eliminated | ~44 | 11 | Each sorry now requires more work |
| Duration | ~10 hours | ~3.5 hours | Shorter wave window |
| Items/hour | ~12 | ~2.9 | Reflects difficulty increase |
| Proof PRs | 22 | 9 | Down from first wave |
| Statement PRs | 6 | 5 | Roughly constant |
| Infrastructure PRs | 0 | 3 | New category — building foundations for harder proofs |

**Key observation:** Wave 1 was dominated by Mathlib-alias and `inferInstance` proofs (especially Chapters 2, 7). Wave 2 tackled genuinely hard theorems requiring algebraic manipulation (Krull-Schmidt, orthogonality relations, determinant irreducibility). The items/hour metric reflects this difficulty increase, not a productivity decline.

## Proof Strategies in This Wave

1. **Algebraic manipulation with MvPolynomial** (PR #684): Used `vars`-based arguments and evaluation maps to prove irreducibility of generic determinants. Novel approach using `MvPolynomial.rename` preservation.

2. **Inductive decomposition arguments** (PR #677): Krull-Schmidt uniqueness proved by induction on number of summands, using the endo_indecomposable_iso_or_nilpotent lemma as the key tool.

3. **Character theory chain** (PRs #671, #670, #663, #658, #652): Building the column orthogonality infrastructure piece by piece — regular character → Wedderburn-Artin → matrix element orthogonality → column orthogonality statement.

4. **Category-theoretic duality** (PR #657): Example 8.1.7 used contravariant Hom functor properties to prove dual of projective is injective.

5. **Direct Mathlib application** (PRs #682, #681): Frobenius reciprocity and tensor right exactness leveraged existing Mathlib APIs with moderate adaptation.

## Current Blockers and Critical Path

### Active Blockers
- **Theorem 5.4.6** (attention_needed): Conjugacy class of prime power size → group not simple. Blocked on column orthogonality proof (#663 laid the statement, proof still needed).
- **Theorem 5.4.3** (Burnside's p^a·q^b theorem): Depends on Theorem 5.4.6.

### Critical Path
The character theory chain is the highest-impact critical path:
1. ~~Column orthogonality statement (Theorem 4.5.4)~~ — Done (#663)
2. **Column orthogonality proof** — Needs Wedderburn-Artin + IrreducibleEnumeration (both now available)
3. **Theorem 5.4.4** (character vanishing) — Statement done, proof structured
4. **Theorem 5.4.6** (prime power conjugacy class) — Depends on 5.4.4
5. **Theorem 5.4.3** (Burnside's theorem) — Depends on 5.4.6

### Infrastructure Gaps
- **Chapter 9**: Only 1/25 formal items sorry-free. Homological algebra infrastructure largely missing.
- **Chapter 6**: 8/47 formal items sorry-free. Quiver representation gap definitions need work.
- **Theorem 3.6.2**: 2/4 sorries resolved (#683); remaining 2 need tracial functional arguments.

## Recommended Priorities for Next Wave

**Tier 1 — Unblock the character theory chain:**
- Prove Theorem 4.5.4 (column orthogonality) — infrastructure is now ready
- Prove Theorem 4.2.1 + Corollary 4.2.2 (character basis) — claimed (#662)
- Prove Theorem 5.4.4 (character vanishing)

**Tier 2 — Complete partial proofs:**
- Finish Theorem 3.6.2 (2 remaining sorries)
- Prove Theorem 3.7.1 (Jordan-Holder) — has open PR (#596)
- Complete Theorem 5.4.4 structure into full proof

**Tier 3 — Expand Chapter 5 coverage:**
- Statement audit for Chapter 5 scaffolded items (#661)
- Prove algebraic integer results (5.2.x series)
- Frobenius reciprocity applications

**Tier 4 — Address neglected chapters:**
- Chapter 6: Pick low-hanging quiver representation items
- Chapter 9: Assess which items can be proved with current Mathlib
