# Stage 3.2 Third Proof Wave Summary

**Date:** 2026-03-17
**Scope:** All work since the second wave summary (#690, merged 2026-03-16T18:23Z)
**Status:** Stage 3.2 in progress — 155/583 items sorry_free (26.6%), 159 sorry occurrences remain across 76 files

## Executive Summary

The third proof wave landed 30 PRs in ~6 hours, advancing sorry_free count from 130 to 155 (+25 items, +19.2%). The wave was characterized by three parallel threads: (1) completing the character theory infrastructure chain (column orthogonality, characters spanning class functions, number of irreps = conjugacy classes), (2) major expansion of Chapter 9 homological algebra definitions (+10 sorry_free items, from 1 to 11), and (3) completing Chapter 7 (all 26 formal items sorry-free). Chapter 8 remains fully complete. The project has crossed the 25% sorry_free threshold.

## Merged PRs (30)

### Proof Completions (12)

| PR | Title | Chapter | Key Result |
|----|-------|---------|------------|
| #695 | Theorem 5.4.4 helper lemmas (eigenvalue decomposition) | Ch5 | Algebraic integer eigenvalue + character divisibility |
| #698 | Theorem 4.5.4 column orthogonality | Ch4 | Full column orthogonality proof using Wedderburn-Artin |
| #704 | Theorem 4.10.2 Frobenius determinant factorization | Ch4 | Determinant factored via irreducible characters |
| #705 | Theorem 3.10.2(ii) tensor product irreducible classification | Ch3 | Classification of irreducible tensor products |
| #713 | Theorem 4.2.1 characters span class functions | Ch4 | Characters span (1 sorry remains: dimension ≠ 0) |
| #715 | Theorem 3.8.1 Krull-Schmidt uniqueness final step | Ch3 | Completed uniqueness via complement isomorphism |
| #716 | Theorem 5.1.5 Frobenius-Schur involution count | Ch5 | Sorry-free |
| #721 | Theorem 5.4.4 character_div_dim_isIntegral | Ch5 | Non-categorical Schur approach |
| #722 | Corollary 4.2.2 number of irreps = conjugacy classes | Ch4 | Consequence of 4.2.1 |
| #729 | Proposition 9.1.1(i) idempotent lifting | Ch9 | Existence of lifted idempotents |
| #730 | Example 7.3.2 + Example 7.5.3 (completing Ch7) | Ch7 | Double dual + forgetful representable |
| #738 | Proposition 9.1.1(ii) conjugacy of lifted idempotents | Ch9 | Conjugation via 1+I units |

### Statement Formalizations & Definitions (11)

| PR | Title | Chapter |
|----|-------|---------|
| #697 | Example 7.8.3 (split exact) + Definition 7.9.4 (semisimple category) | Ch7 |
| #699 | Example 7.3.2 + Example 7.5.3 | Ch7 |
| #709 | Example 7.6.3, Definition 7.8.6, Example 7.9.2 | Ch7 |
| #714 | Definition 5.12.1 Young tableaux + symmetrizers | Ch5 |
| #726 | Example 4.8.1 (Q₈) + Example 4.9.1 (S₃) character computations | Ch4 |
| #735 | Lemma 5.13.4 idempotent module hom isomorphism | Ch5 |
| #741 | Definition 9.2.2 (projective cover) + Definition 9.3.1 (Cartan matrix) | Ch9 |
| #742 | Definition 9.7.1 (Morita equivalence) + Definition 9.7.2 (basic algebra) | Ch9 |
| #746 | Definition 9.4.1 (projective dimension) + Definition 9.4.3 (homological dimension) | Ch9 |
| #747 | Lemma 5.13.1 statement + helper lemmas (Young projector) | Ch5 |
| #748 | Definition 9.6.1 (finite abelian category) + Definition 9.6.2 (progenerator) | Ch9 |

### Infrastructure (4)

| PR | Title | Purpose |
|----|-------|---------|
| #696 | columnFDRep simplicity + Theorem 4.2.1 completeness infra | Wedderburn-FDRep bridge |
| #734 | columnFDRep_surjective + d_eq_finrank | Dimension formula for character theory |
| #749 | sum_dim_character_eq_zero (regular character decomposition) | Regular character infrastructure |
| #751 | Definition 9.5.1 (blocks) + Example 9.5.2 | Block theory foundations |

### Review & Meditate (3)

| PR | Title |
|----|-------|
| #720 | Stage 3.2 second proof wave retrospective |
| #750 | Validate Ch9 definitions 9.2.2, 9.3.1, 9.7.1, 9.7.2 |
| #690 | Stage 3.2 second proof wave summary |

## Sorry-Free Items by Chapter

| Chapter | Topic | Sorry-free | Formal Items | Formal % | Total | Overall % | Δ from Wave 2 |
|---------|-------|------------|-------------|----------|-------|-----------|----------------|
| 2 | Basic notions | 36 | 42 | 85.7% | 117 | 30.8% | +0 |
| 3 | General results | 22 | 23 | 95.7% | 58 | 37.9% | +2 |
| 4 | Characters | 20 | 21 | 95.2% | 60 | 33.3% | +5 |
| 5 | Representations of Sₙ | 26 | 59 | 44.1% | 157 | 16.6% | +4 |
| 6 | Quiver representations | 8 | 33 | 24.2% | 64 | 12.5% | +0 |
| 7 | Categories | 26 | 26 | **100%** | 59 | 44.1% | +7 |
| 8 | Abelian categories | 9 | 9 | **100%** | 24 | 37.5% | +0 |
| 9 | Finite dim. algebras | 11 | 18 | 61.1% | 35 | 31.4% | +10 |
| **Total** | | **158** | **231** | **68.4%** | **583** | **26.6%** | **+28** |

Note: "Sorry-free" includes `sorry_free` + `proof_formalized` statuses. "Formal Items" counts all items with Lean files (sorry_free + scaffolded + proof_formalized + statement_formalized + attention_needed). Items without a `status` key (352) are discussion blobs, exercises, problems, and remarks without Lean formalization.

## Sorry Count Trend

| Metric | Wave 1 | Wave 2 | Wave 3 |
|--------|--------|--------|--------|
| Sorry-free items | 120 | 130 | 155 |
| Sorry occurrences | 205 | 194 | 159 |
| Files with sorry | 110 | 103 | 76 |
| Sorry-free Lean files | 126/236 (53%) | 138/241 (57%) | 166/242 (69%) |
| Formal items completion | 32.6% | 35.3% | 68.4% |

## Velocity Analysis

| Metric | Wave 1 | Wave 2 | Wave 3 | Trend |
|--------|--------|--------|--------|-------|
| PRs merged | 37 | 19 | 30 | Rebound — more parallel agents |
| Items sorry_free gained | 120 | 10 | 25 | Improved over Wave 2 |
| Duration | ~10h | ~3.5h | ~6h | Moderate |
| Items/hour | ~12 | ~2.9 | ~4.2 | Stabilizing |
| Infrastructure PRs | 0 | 3 | 4 | Continuing investment |
| Ch9 definition PRs | 0 | 0 | 6 | New frontier opened |

**Key observation:** Wave 3 recovered velocity compared to Wave 2, driven by three factors: (1) infrastructure from Wave 2 (Wedderburn-Artin, IrreducibleEnumeration, regular character) paid off in character theory proofs, (2) Chapter 9 definition work was high-throughput (many items per PR), and (3) completing Chapter 7 resolved several straightforward categorical items. The character theory chain is now mostly proved, unblocking downstream Burnside-type results.

## Proof Strategies in This Wave

1. **Character theory chain completion** (PRs #698, #713, #722, #721, #749): The column orthogonality → characters span → irrep count chain is now almost fully proved. Key technique: building on `IrreducibleEnumeration` bijection and `RegularCharacter` decomposition from Wave 2 infrastructure.

2. **Non-categorical Schur lemma** (PR #721): For `character_div_dim_isIntegral`, bypassed the categorical Schur's lemma (FDRep plumbing issues) by using a direct algebraic argument with eigenvalues of central elements.

3. **Idempotent algebra** (PRs #729, #738): Proposition 9.1.1 proved via explicit unit construction `u = 1 + (2e₂-1)(e₁-e₂)` rather than induction on nilpotency degree — simpler and avoids quotient ring manipulation.

4. **Young tableaux formalization** (PRs #714, #735, #747): Decomposed Young symmetrizer into `RowSymmetrizer` and `ColumnAntisymmetrizer`, enabling modular proofs. Helper lemmas used `Fintype.sum_equiv` with `Equiv.mulLeft`/`mulRight`.

5. **Chapter completion sprints** (PRs #697, #699, #709, #730): Batched remaining Chapter 7 items into focused PRs, achieving 100% formal completion.

## Current Blockers and Critical Path

### Active Blockers

- **Theorem 4.2.1** has 1 remaining sorry: `(D.d i : k) ≠ 0` (dimension of simple module is nonzero as field element). Needs Frobenius dimension divisibility theorem or characteristic-zero argument.
- **Theorem 5.4.6** (conjugacy class of prime power size → not simple): Depends on Theorem 5.4.4 (now partially proved) and column orthogonality (now proved).
- **Lemma 5.13.1** main proof: Young projector linear functional requires deep combinatorial argument (row/column decomposition of permutations).

### Completed Critical Path Items
The character theory chain from Wave 2's recommendations is now substantially resolved:
- ✅ Column orthogonality proof (Theorem 4.5.4) — PR #698
- ✅ Characters span class functions (Theorem 4.2.1) — PR #713 (1 sorry)
- ✅ Number of irreps = conjugacy classes (Corollary 4.2.2) — PR #722
- ✅ character_div_dim_isIntegral (Theorem 5.4.4 partial) — PR #721

### Infrastructure Gaps
- **Chapter 6**: 0 items gained this wave. 25 scaffolded items untouched. Quiver representation theory needs dedicated attention.
- **Chapter 5**: Largest chapter (157 items), only 26 sorry_free (16.6%). 31 scaffolded items awaiting proofs. The Young symmetrizer work (5.12–5.13) is progressing but deep.
- **Theorem 3.6.2**: Still 2/4 sorries unresolved from Wave 2.

## Chapters Approaching Completion

| Chapter | Sorry-free | Formal Items | Remaining | Status |
|---------|------------|-------------|-----------|--------|
| 7 | 26 | 26 | 0 | **Complete** ✓ |
| 8 | 9 | 9 | 0 | **Complete** ✓ |
| 3 | 22 | 23 | 1 | Near-complete (Theorem 3.6.2 last sorry) |
| 4 | 20 | 21 | 1 | Near-complete (Theorem 4.2.1 last sorry) |
| 2 | 36 | 42 | 6 | 6 scaffolded items remaining |

## Recommended Priorities for Next Wave

**Tier 1 — Close out near-complete chapters:**
- Fix Theorem 4.2.1's last sorry (`(D.d i : k) ≠ 0`) — possibly via `Nat.cast_ne_zero` + `finrank_pos`
- Finish Theorem 3.6.2 remaining 2 sorries (tracial functional arguments)
- Clear Chapter 2's 6 remaining scaffolded items (Theorem 2.3.7, 2.6.3, etc.)

**Tier 2 — Advance Burnside chain:**
- Prove Theorem 5.4.6 (prime power conjugacy class → not simple) — prerequisites now available
- Prove Theorem 5.4.3 (Burnside's p^a·q^b theorem) — depends on 5.4.6
- Complete Theorem 5.4.4 remaining sorries

**Tier 3 — Chapter 5 depth:**
- Prove Lemma 5.13.1 main theorem (Young projector) — consider Aristotle escalation
- Work through scaffolded Propositions 5.3.x, 5.5.x series
- Frobenius reciprocity applications

**Tier 4 — Unblock Chapter 6:**
- Chapter 6 has had 0 progress across all 3 waves. 25 scaffolded items need proofs.
- Start with definitions and basic quiver path algebra results
- Assess which items can leverage existing Mathlib `Quiver` API

**Tier 5 — Chapter 9 proofs:**
- Definitions are now well-scaffolded (11/18 formal items sorry_free)
- Remaining 7 scaffolded items are theorems/propositions requiring proofs
- Prioritize Theorem 9.6.4 (finite abelian categories ≃ module categories) as the capstone result
