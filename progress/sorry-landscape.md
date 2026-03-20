# Sorry Landscape Analysis — Wave 24

Generated 2026-03-20 by meditate session (issue #1474).

## Summary

**84 sorries** across 29 files. Down from 91 at wave 23 (7 eliminated).

| Tier | Count | % | Description |
|------|-------|---|-------------|
| Tier 1 — Achievable | 8 | 10% | Standard math, Mathlib APIs exist, needs effort |
| Tier 2 — Hard but tractable | 14 | 17% | Non-trivial proofs, novel approaches needed |
| Tier 3 — Blocked on infrastructure | ~50 | 60% | Missing Mathlib or project infrastructure |
| Unclassified / mixed | ~12 | 14% | Arithmetic or partial-progress items |

## Chapter Breakdown

| Chapter | Sorries | Files | Notes |
|---------|---------|-------|-------|
| Ch2 | 3 | 2 | Burnside, Schur |
| Ch5 | 45 | 14 | SchurModule, polytabloids, Mackey machine |
| Ch6 | 27 | 10 | Reflection functors, Dynkin, Gabriel |
| Ch9 | 9 | 3 | Krull-Schmidt, projective covers |

Ch3, Ch4, Ch7, Ch8 are 100% sorry-free.

## Tier 1 — Achievable (8 sorries)

These can be closed with standard techniques in 1-2 agent sessions each.

### Example6_4_9_Dn — 7 sorries
**File:** `Chapter6/Example6_4_9_Dn.lean`
**Nature:** Arithmetic root-counting for D_n Dynkin diagrams. Explicit finite computations (cardinality of positive roots, verification of root system properties).
**Approach:** `decide`, `omega`, `norm_num`, explicit `Fin` enumeration. Similar patterns already succeeded for A_n root counting.

### Problem6_9_1 `ker_sum_le_one` — 1 sorry
**File:** `Chapter6/Problem6_9_1.lean` (line ~573)
**Nature:** If ρ is indecomposable Q₂-rep with AB nilpotent and both dims > 0, then dim(ker A) + dim(ker B) ≤ 1.
**Approach:** The proof infrastructure (ker_sum_ge_one, ker_A_sub_range_B, ker_B_sub_range_A) is already built. Needs rank-nullity argument showing dim(ker A) = 1 forces dim(ker B) ≤ 0 (contradiction with hypothesis) or both = 1 then decomposability contradiction. Tractable but requires ~100 lines of careful linear algebra.

## Tier 2 — Hard but Tractable (14 sorries)

Each requires significant effort but has a clear mathematical path.

### Theorem5_15_1 — rearrangement inequality completion (~2 sorries)
**File:** `Chapter5/Theorem5_15_1.lean`
**Nature:** Remaining cases of rearrangement inequality for symmetric group representations.
**Approach:** Structure already proved; needs case completion.

### Theorem5_18_1 — Schur-Weyl dimension formula (~2 sorries)
**File:** `Chapter5/Theorem5_18_1.lean`
**Nature:** Dimension formula relating symmetric group and GL representations.
**Approach:** Requires connecting polytabloid basis cardinality to dimension. Hard but well-specified.

### Proposition5_19_1 — character formula (~1 sorry)
**File:** `Chapter5/Proposition5_19_1.lean`
**Nature:** Character computation for specific representations.
**Approach:** Needs careful Mathlib character API usage.

### Proposition5_21_1 — decomposition (~2 sorries)
**File:** `Chapter5/Proposition5_21_1.lean`
**Nature:** Decomposition of tensor product representations.

### Lemma5_25_3 — hook quotient identity (~2 sorries)
**File:** `Chapter5/Lemma5_25_3.lean`
**Nature:** Combinatorial identity for hook lengths. Decomposed into sub-issues (#1383-#1386).
**Approach:** Sub-issues are well-specified; needs patient combinatorial work.

### FRTHelpers — Frobenius reciprocity (~2 sorries)
**File:** `Chapter5/FRTHelpers.lean`
**Nature:** Helper lemmas for Frobenius reciprocity theorem.

### Theorem_Dynkin_classification — (~1 sorry)
**File:** `Chapter6/Theorem_Dynkin_classification.lean`
**Nature:** Completing the Dynkin classification proof.
**Approach:** Skeleton exists; needs case completion for exceptional types.

### PolytabloidBasis — (~2 sorries)
**File:** `Chapter5/PolytabloidBasis.lean`
**Nature:** Proving polytabloids form a basis for Specht modules.

## Tier 3 — Blocked on Infrastructure (~50 sorries)

These require major infrastructure that doesn't exist in Mathlib or this project.

### Blocker Cluster 1: Schur Modules & Characters (Ch5, ~15 sorries)
**Files:** AlgIrrepGL, SchurModule-related files
**Missing:** `SchurModule k N lam` is sorry'd as `sorry : FDRep k (GL (Fin N) k)`. Every downstream proof (Peter-Weyl for GL(V), Frobenius formula, character orthogonality for GL) is blocked.
**Unblocking path:** Define SchurModule concretely via polytabloid quotient of tensor power, prove it carries a GL action. Estimated: 500+ lines.

### Blocker Cluster 2: Schur-Weyl Duality (Ch5, ~8 sorries)
**Files:** Theorem5_18_1, related
**Missing:** The double centralizer theorem for S_n acting on V^⊗n vs GL(V) acting on V^⊗n. Requires both SchurModule and the centralizer algebra identification.
**Unblocking path:** After SchurModule exists, prove the image of k[S_n] in End(V^⊗n) equals the centralizer of GL(V). Estimated: 300+ lines.

### Blocker Cluster 3: Gabriel's Theorem (Ch6, ~10 sorries)
**Files:** Theorem6_6_2, Proposition6_6_6, Proposition6_6_7, Corollary6_6_8
**Missing:** Reflection functor round-trip isomorphism (F⁻F⁺V ≅ V) blocked by Decidable.casesOn opacity. Gabriel's theorem (quiver has finitely many indecomposables iff underlying graph is Dynkin) depends on this.
**Unblocking path:** Refactor `reversedArrow_eq_ne` in Definition6_6_3.lean to use `cast` instead of `match`. Estimated: 200+ lines of refactoring.

### Blocker Cluster 4: Krull-Schmidt Theorem (Ch9, ~9 sorries)
**Files:** Theorem9_2_1 (parts ii, iii), related
**Missing:** Unique decomposition into indecomposables. Not in Mathlib. Part (i) is fully proved, but parts (ii) "A = ⊕ dim(M_i) P_i" and (iii) "any indecomposable projective ≅ some P_i" both require Krull-Schmidt.
**Unblocking path:** Prove Krull-Schmidt for Artinian modules with local endomorphism rings. Estimated: 400+ lines.

### Blocker Cluster 5: Mackey Machine (Ch5, ~5 sorries)
**Files:** Theorem5_27_1
**Missing:** Semidirect product orbit method for constructing irreducible representations. Requires Clifford theory (restriction to normal subgroup, orbit stabilizer).
**Unblocking path:** Build Clifford theory infrastructure from scratch. Estimated: 500+ lines.

### Blocker Cluster 6: Complete Reducibility Extensions (Ch2, ~3 sorries)
**Files:** Burnside theorem, Schur's lemma extensions
**Missing:** Certain extensions of complete reducibility results.

## Strategic Recommendations

1. **Highest ROI:** Tier 1 sorries (8 total). The D_n root counting (7 sorries) is purely mechanical and could be knocked out in a single session. Problem6_9_1 needs careful but straightforward linear algebra.

2. **Biggest unblock:** Refactoring Definition6_6_3.lean to eliminate Decidable.casesOn opacity would unblock ~10 Tier 3 sorries in the Gabriel's theorem cluster. This is the single highest-leverage infrastructure change.

3. **SchurModule is the mega-blocker:** ~23 sorries (27% of all remaining) are transitively blocked on a concrete SchurModule definition. This is the project's critical path but requires the most new infrastructure.

4. **Krull-Schmidt is self-contained:** The 9 Ch9 sorries could be unblocked by proving Krull-Schmidt independently. This is a well-defined project (~400 lines) with no dependencies on other blockers.

5. **Velocity is declining** as expected — remaining items are genuinely harder. The project should prioritize Tier 1 and the Definition6_6_3 refactor before attempting Tier 3 blockers.
