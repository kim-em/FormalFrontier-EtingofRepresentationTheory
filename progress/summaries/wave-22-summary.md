# Stage 3.2 Twenty-Second Proof Wave Summary

**Date:** 2026-03-20
**Scope:** 46 merged PRs since wave 21 summary (#1291, closed 2026-03-20T00:05:40Z)
**Status:** Stage 3.2 in progress — 202/583 items sorry_free (34.6%), ~87 sorry occurrences across 30 files

## Executive Summary

Wave 22 was the largest single wave yet with 46 merged PRs: 32 feature/proof PRs, 5 refactors/infrastructure, 4 fixes, 3 reviews/chores, and 2 progress docs. Net progress: sorry count dropped from 94 to ~87 (net -7) while files with sorries decreased from 32 to 30. Key achievements: **GL2ConjugacyClasses.lean completely sorry-free** (card_isElliptic proved via bijection), **GNW Property 1 proved** (hook quotient identity restructured), **Theorem 5.27.1 dual action and stabilizer** proved, **Young's Rule character identity** proved (`youngsRule_character`), **Dynkin classification** major sorry reduction (path_walk_construction, no_cycle, arm_length_solutions all proved), **Proposition 6.6.6** first-isomorphism helpers proved, and **Corollary 6.8.4** reduced from 3 to 1 sorry.

## Merged PRs (46)

### Proof Completions (files/items flipped to sorry_free or major milestones)

| PR | Title | Chapter | Impact |
|----|-------|---------|--------|
| #1422 | GL2.card_isElliptic (q²(q-1)²/2) | Ch5 | **GL2ConjugacyClasses.lean 0 sorries** — bijection to F×F×F*×nonsquares |
| #1396 | GNW Property 1 + hook quotient restructure | Ch5 | Key step in FRT hook-length formula |
| #1412 | Theorem5_27_1 semidirect product irrep | Ch5 | Dual action + stabilizer constructions proved |
| #1341 | Young's Rule character identity | Ch5 | `youngsRule_character` + isotypic trace formula, closes #1289 |
| #1342 | Dn_count — D_n root count n*(n-1) | Ch6 | Root counting complete |
| #1361 | coeff_symmetric_eq_coeff_partition | Ch5 | Frobenius coefficient sorry removed |
| #1337 | syt_branching_rule proved | Ch5 | FRT branching bijection |
| #1340 | hrank i=j case (E₁₁ rank 1) | Ch9 | Theorem 9.2.1 helper |

### Major Partial Proofs (sorry reduction or infrastructure)

| PR | Title | Chapter | Impact |
|----|-------|---------|--------|
| #1420 | path_walk_construction remaining sorries | Ch6 | Connectivity + embedding for Dynkin A_n |
| #1416 | arm_length_solutions + n=0 case | Ch6 | Dynkin classification forward direction |
| #1404 | no_cycle_in_dynkin + dynkin_edge_count | Ch6 | 2 key structural lemmas proved |
| #1405 | path_walk_construction key lemmas | Ch6 | Walk construction infrastructure |
| #1377 | path_walk_construction key lemmas | Ch6 | Walk construction (earlier batch) |
| #1397 | Corollary6_8_4 sorry reduction (3→1) | Ch6 | Proved reversedAtVertex_isOrientationOf, closes #1382 |
| #1415 | Problem6_9_1 nilpotent restructure | Ch6 | ker_sum isolated as sole sorry |
| #1329 | Proposition 6.6.6 first-isomorphism helpers | Ch6 | Surjectivity + kernel proved |
| #1358 | Proposition 6.6.7 hU₁/hU₂ subrep cases | Ch6 | reflFunctorPlus helpers |
| #1339 | Dynkin structural lemmas (degree≤3, no cycle) | Ch6 | Reduces sorries 7→5 |
| #1372 | dynkin_no_cycle full proof | Ch6 | All-ones vector on cycle gives B=0 |
| #1359 | path_iso_An + branch_classification | Ch6 | Dynkin forward direction structure |
| #1348 | Corollary 6.8.4 inductive step | Ch6 | Strong induction decomposition |
| #1326 | GL₂ sum_split + card_isScalar (#1296) | Ch5 | Conjugacy class partition assembly |
| #1347 | Lemma 5.25.3 inner product + char orthogonality | Ch5 | #1297 character values |
| #1393 | elliptic_contribution for Lemma 5.25.3 | Ch5 | Elliptic conjugacy class contribution |
| #1388 | card_disc_eq_zero + card_isParabolic | Ch5 | GL₂ cardinality helpers |
| #1418 | GL2 conjugacy class cardinalities | Ch5 | Partial #1354 |
| #1378 | Character value lemmas for elliptic elements | Ch5 | #1367 |
| #1362 | charW₁ split semisimple, disc conjugation | Ch5 | #1297 helpers |
| #1363 | ellipticSubgroup_disc — K elements | Ch5 | Scalar/elliptic classification |
| #1335 | spechtModule_noniso + exhaust_simples | Ch5 | Partial #1289 |
| #1338 | polytabloid linear independence framework | Ch5 | #1275 infrastructure |
| #1357 | polytabloid basis (independence + straightening) | Ch5 | Polytabloid framework |
| #1330 | hook quotient identity infrastructure | Ch5 | FRT helpers |
| #1395 | hookWalkWeight WF recursion | Ch5 | Hook walk definition |
| #1387 | hook walk infrastructure | Ch5 | Hook quotient identity prep |
| #1352 | trace_isotypic_eq_mult_trace | Ch5 | 1/2 sorries resolved |
| #1356 | sum_shifted_sub_permExponent | Ch5 | Partial coeff_symmetric |
| #1389 | sign convention fix for alternating_kostka | Ch5 | Closes #1364 |
| #1368 | Frobenius character formula sign fix | Ch5 | Closes #1364 |

### Refactors, Fixes, Reviews (11)

| PR | Title | Impact |
|----|-------|--------|
| #1365 | refactor: split Theorem5_12_2.lean into 3 sub-files | Code organization |
| #1360 | refactor: split Example6_4_9.lean into sub-files by Dynkin type | Code organization |
| #1379 | refactor: replace broad import Mathlib with specific imports (#1313) | Build performance |
| #1413 | fix: Example6_4_9_An.lean and _Dn.lean compile | Build fix |
| #1370 | fix: remove duplicate cartanMatrix_isSymm | Build fix |
| #1410 | Fix broken PRs: close #1394, rebase #1396 and #1375 | PR maintenance |
| #1334 | review: wave 22 quality check (4 files) | Quality review |
| #1411 | chore: wave 20 skill review | Skill updates |
| #1325 | sytBranchingEquiv construction | Infrastructure (partial right_inv sorry) |

## Sorry Counts by Chapter

| Chapter | Files with sorry | Total sorries | Delta from Wave 21 |
|---------|-----------------|---------------|---------------------|
| 2 | 2 | 3 | +0 |
| 3 | 0 | 0 | +0 |
| 4 | 0 | 0 | +0 |
| 5 | 15 | 43 | -7 (GL2 done, FRT progress, sign fixes) |
| 6 | 10 | 33 | +1 (Dynkin progress offset by new scaffolds) |
| 7 | 0 | 0 | +0 |
| 8 | 0 | 0 | +0 |
| 9 | 3 | 8 | -1 (hrank i=j proved) |
| **Total** | **30** | **~87** | **-7** |

Four chapters remain at 100% formal completion: Ch3, Ch4, Ch7, Ch8.

## Sorry-Free Items by Chapter

| Chapter | Topic | Sorry-free | Total Items | % | Delta from Wave 21 |
|---------|-------|------------|-------------|---|---------------------|
| 2 | Basic notions | 40 | 117 | 34.2% | +0 |
| 3 | General results | 23 | 58 | 39.7% | +0 |
| 4 | Characters | 21 | 60 | 35.0% | +0 |
| 5 | Symmetric group reps | 45 | 157 | 28.7% | +1 |
| 6 | Quiver representations | 23 | 64 | 35.9% | +0 |
| 7 | Category O | 26 | 59 | 44.1% | +0 |
| 8 | Infinite-dim reps | 9 | 24 | 37.5% | +0 |
| 9 | Finite-dim algebras | 15 | 35 | 42.9% | +0 |
| **Total** | | **202** | **583** | **34.6%** | **+1** |

Note: items.json may not fully reflect wave 22 completions. Several files that became sorry-free (GL2ConjugacyClasses.lean) need items.json updates.

## Active Work Fronts

### Ch5: Frame-Robinson-Thrall Hook Length Formula
- Base case: **proved**
- Inductive step: proved modulo sub-lemmas
  - `syt_branching_rule`: **proved** (#1337)
  - `hook_quotient_identity`: GNW Property 1 proved (#1396); column identity still open (#1385)
  - `hookWalkWeight`: defined with WF recursion (#1395)

### Ch5: GL₂(𝔽_q) Representations
- GL2ConjugacyClasses.lean: **0 sorries** (card_isElliptic proved #1422)
- Lemma 5.25.3: 3 sorries remain (innerProduct assembly, character orthogonality)
- Theorem 5.25.2: 7 sorries (representation definitions + classification)
- Theorem 5.27.1: 1 sorry (main theorem statement)

### Ch5: Schur-Weyl Duality
- Theorem 5.18.1: 2 sorries
- Theorem 5.18.4: 3 sorries
- Theorem 5.22.1 (Schur module): 3 sorries (definition placeholders)

### Ch5: Frobenius Character Formula
- Sign convention fixed (#1368, #1389)
- alternating_kostka_eq_delta: restructured, still 1+ sorries
- Theorem 5.15.1: 3 sorries

### Ch6: Dynkin Classification
- Forward direction: major progress — path_walk_construction, no_cycle, arm_length_solutions all proved
- 1 sorry remains in Theorem_Dynkin_classification.lean
- Corollary 6.8.3: 3 sorries (reflection reduce + Tits form)
- Corollary 6.8.4: 1 sorry (reflection functor chain step)

### Ch6: Quiver Representation Machinery
- Proposition 6.6.6: 4 sorries (first-isomorphism details)
- Proposition 6.6.7: 3 sorries (reflFunctorMinus blocked)
- Problem 6.9.1: 1 sorry (ker_sum_le_one — Jordan chain needed)

### Ch6: Example 6.4.9 (Root Counting)
- Example6_4_9_Dn.lean: 14 sorries — largest single file
- Example6_4_9_An.lean: 4 sorries

### Ch9: Finite-Dimensional Algebras
- Theorem 9.2.1: 4 sorries (block-module correspondence)
- Corollary 9.7.3: 3 sorries (basic algebra)
- Example 9.4.4: 1 sorry (homological dimension)

## Velocity Analysis

| Metric | Wave 19 (39 PRs) | Wave 21 (24 PRs) | Wave 22 (46 PRs) |
|--------|-------------------|-------------------|-------------------|
| sorry_free delta | +4 | +5 | **+1** (items.json stale) |
| sorry delta | 0 | +10 | **-7** |
| Feature PRs | 21 | 16 | **32** |
| Review/Fix PRs | 11 | 5 | **11** |
| Files w/sorry | 34 | 32 | **30** |

## Honest Assessment

Wave 22 was the highest-throughput wave yet (46 PRs), and importantly reversed the sorry count trend: net -7 sorries (94→87) after wave 21's +10 increase. The sorry_free item count barely moved (+1) because items.json updates lag behind actual file completions.

**Positive signals:**
- **Sorry count declining** — first net decrease in recent waves, suggesting scaffold-filling is catching up
- **GL2ConjugacyClasses.lean fully proved** — all 4 conjugacy class cardinalities
- **Dynkin classification nearly complete** — only 1 sorry in forward direction theorem
- **GNW Property 1 proved** — major FRT milestone
- **Young's Rule character identity proved** — key symmetric group result
- **46 PRs merged** — highest single-wave throughput

**Concerns:**
- **Example6_4_9_Dn.lean has 14 sorries** — largest single-file concentration, needs dedicated attention
- **items.json is stale** — sorry_free count (202) doesn't reflect actual completions
- **Ch5 still dominates** — 43/87 sorries (49%), concentrated in Schur-Weyl and GL₂ representations
- **Theorem 5.22.1/5.23.2** contain definition-level sorries (SchurModule, AlgIrrepGL) that block downstream work
- **Proposition 6.6.7** blocked on reflFunctorMinus definition, which cascades to Corollary 6.8.3/6.8.4

**Recommendations for next wave:**
1. **Update items.json** — reflect actual sorry_free status for recently completed files
2. **Attack Example6_4_9_Dn.lean** (14 sorries) — highest concentration, likely many are routine
3. **Complete Lemma 5.25.3** (#1298) — assembly of innerProduct_sum_eq_card from existing infrastructure
4. **Complete hook quotient identity** (#1385) — the column identity is the last piece for FRT
5. **Prove Corollary6_8_3 helpers** (#1381) — reflection reduce + Tits form bound
6. **Address definition-level sorries** in Theorem 5.22.1 (SchurModule) — blocks Ch5 downstream items
