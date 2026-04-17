# Meditate Wave 49: Endgame Strategy Review

Generated 2026-04-17 (issue #2366). Covers 48+ commits since wave 48 meditate.

## 1. Current Sorry Inventory (Post-Wave 52)

**16 sorry sites** across 4 files (down from 17 at wave 52 landscape).

Since the wave 52 landscape was written, PRs #2385/#2386/#2387 closed the
tree_two_leaf_posdef and D-type leaf posdef sorries (−4), but PR #2381/#2382
added path infrastructure sorries (+3). The etilde7 proof was decomposed
from 1 monolithic sorry into 4 sub-sorries.

### InfiniteTypeConstructions.lean — 12 sorries

**Indecomposability (7 sorries, 4 theorems):**
| Line | Sorry | Context |
|------|-------|---------|
| 2177 | `dTildeRep_isIndecomposable` | D̃_n, monolithic, no structural framework |
| 2332 | `etilde6v2Rep_isIndecomposable` | Ẽ₆, monolithic, edge orientation fixed (ef3e868) |
| 2748 | etilde7 hN₁ | W₁(4) closed under nilpotent shift |
| 2751 | etilde7 hN₂ | W₂(4) closed under nilpotent shift |
| 2785 | etilde7 hbot0 | W(0) = ⊥ from propagation |
| 2792 | etilde7 propagation | W(0) = ⊥ → all W(v) = ⊥ |
| 3008 | `t125Rep_isIndecomposable` | T(1,2,5), monolithic, no structural framework |

**Path infrastructure (3 sorries):**
| Line | Sorry | Context |
|------|-------|---------|
| 7968 | `dTilde_nodup_path_between` | Construct explicit paths in D̃_n |
| 7990 | `walk_to_nodup_path` | Trim walk to Nodup path (generic) |
| 8106+8109 | walk length bounds | Walk length ≥ 2 and Nodup path length ≥ 3 |

**D̃ embedding (1 sorry):**
| Line | Sorry | Context |
|------|-------|---------|
| 8215 | non_adjacent_branches D̃ embedding | Full embedding φ + edge preservation |

**Closed since landscape:** tree_two_leaf_posdef (h_bound, h_strict), D-type leaf posdef (a₂, a₃), ADE posdef (all 4: T(1,4,2), T(1,3,2), T(1,2,4), T(1,2,3)).

### SpechtModuleBasis.lean — 1 sorry
- Line 670: `garnir_twisted_in_lower_span` (straightening heart, difficulty 8)

### FormalCharacterIso.lean — 1 sorry
- Line 221: `iso_of_formalCharacter_eq_schurPoly` (GL_N complete reducibility, difficulty 9)

### Theorem2_1_2.lean — 2 sorries
- Line 171: Forward bridge (`not_posdef_not_HasFiniteRepresentationType`)
- Line 210: Backward bridge (`isDynkinDiagram_HasFiniteRepresentationType`)

## 2. Sorry Clustering and Strategy Assessment

### Cluster A: Indecomposability (7 sorries across 4 theorems)

**Current approach:** Each indecomposability theorem follows the pattern:
1. Assume complementary invariant decomposition W₁ ⊕ W₂
2. Propagate constraints through the quiver arms
3. Show nilpotent shift invariance at a leaf vertex
4. Apply `nilpotent_invariant_compl_trivial` to conclude W₁ or W₂ = ⊥
5. Propagate back to all vertices

**Assessment: The current approach IS correct, but unified infrastructure is needed.**

The etilde7 structural framework (PR #2367) is the most advanced — it's decomposed
into 4 sub-sorries with detailed proof sketches. The hN₁/hN₂ sub-sorries (nilpotent
invariance at leaf) are the mathematical core. Once solved for Ẽ₇, the same technique
should apply to Ẽ₆ and T(1,2,5).

**Null root approach assessment:** Null roots appear only in comments as documentation
for dimension vectors. There's no formal null root infrastructure. While a null root
eigenvector approach (showing adjacency matrix has null eigenvector with all-nonzero
components) is mathematically valid, it would require:
- Formalizing the Tits form / adjacency matrix at the representation level
- Relating representation-level indecomposability to matrix eigenvalues
- This is a NEW proof technique not following the book

**Recommendation: Do NOT pursue the null root approach.** The existing
`nilpotent_invariant_compl_trivial` approach follows the book and has a complete
working example (`cycleRep_isIndecomposable`). The bottleneck is the propagation
arguments, not the overall strategy. Focus on:

1. **Close etilde7 first** — it has the most infrastructure (4 sub-sorries with
   proof sketches, structural framework complete)
2. **Extract shared helpers** from etilde7 for reuse in etilde6v2 and t125
3. **dTildeRep_isIndecomposable last** — D̃_n has parametric k, making it harder

**Priority ranking within cluster:**
1. etilde7 hN₁ + hN₂ (the mathematical core — once solved, hbot0 and propagation follow)
2. etilde6v2 (same technique, simpler graph)
3. t125 (same technique, 9 vertices)
4. dTilde (parametric, hardest)

### Cluster B: Path Infrastructure (3-4 sorries)

These are NEW since wave 52, added by PR #2381/#2382 for the non_adjacent_branches
proof. They are graph theory infrastructure, not representation theory.

**Assessment: These are difficulty 4-5 and highly tractable.**

- `walk_to_nodup_path` is a standard graph theory lemma (strong induction on walk length)
- `dTilde_nodup_path_between` is explicit path construction in a well-understood graph
- The walk length bounds are trivial once the above are proved

Issue #2384 is claimed for this work. This is the right priority — clearing path
infrastructure unblocks the D̃ embedding sorry (line 8215).

### Cluster C: D̃ Embedding (1 sorry)

Line 8215 constructs an explicit D̃_n subgraph embedding in a tree with two
non-adjacent branch points. Blocked on path infrastructure (#2384). Once paths
exist, this is a construction + verification task (difficulty 5-6).

### Cluster D: Ch5 Sorries (2 sorries)

**garnir_twisted_in_lower_span (difficulty 8):** Infrastructure is COMPLETE.
`garnir_polytabloid_identity` is fully proved, `twistedPolytabloid_col_eq` proved,
row inversion counting formalized. What remains is the combinatorial management
of restandardization + row inversion counting. This is the most "infrastructure-
complete" hard sorry — a focused agent session could close it.

**iso_of_formalCharacter_eq_schurPoly (difficulty 9):** Requires GL_N complete
reducibility (Schur-Weyl duality), which is almost certainly NOT in Mathlib. The
supporting lemmas are all proved (schurPoly_injective, finrank equality, weight
space independence), but the core result requires deep representation theory.

**Recommendation:** `garnir_twisted_in_lower_span` should be prioritized — it's
closer to completion. `iso_of_formalCharacter_eq_schurPoly` may need to be
deferred or worked around (e.g., adding complete reducibility as an axiom/sorry'd
lemma that's clearly identified as a Mathlib gap).

### Cluster E: Ch2 Bridges (2 sorries)

**Forward bridge (difficulty 6-7):** Needs field-generic infinite type constructions.
FieldGenericInfiniteType.lean has cycle case done; star and extended Dynkin need
field-generic versions. Partially blocked on Cluster A completion.

**Backward bridge (difficulty 8-9):** Fully independent — needs only Theorem 6.5.2(a-c)
and positive root enumeration. Heavy infrastructure bridging between Chapter 6 and
Chapter 2 type definitions.

**Recommendation:** The backward bridge is the better target — it's fully independent
of all other clusters. The forward bridge should wait until more indecomposability
proofs are closed and can be refactored to field-generic.

## 3. Recommended Approach Changes

### Change 1: Focus on etilde7 sub-sorries, not monolithic proofs

The decomposition of etilde7 into 4 sub-sorries was the right move. The other
indecomposability theorems (etilde6v2, t125, dTilde) should be similarly decomposed
before attempting proofs. This allows:
- Multiple agents to work on sub-sorries in parallel
- Clear scope for each work item
- Shared helper extraction

**Action:** Create issues to decompose etilde6v2 and t125 into sub-sorries
following the etilde7 pattern.

### Change 2: Prioritize path infrastructure (#2384)

The 3-4 path infrastructure sorries gate both the D̃ embedding and potentially
future graph lemmas. These are standard results, not research-level proofs.
They should be highest priority after currently claimed work.

### Change 3: Accept iso_of_formalCharacter_eq_schurPoly as a Mathlib gap

Complete reducibility of polynomial GL_N representations is a major theorem
that's not in Mathlib. Rather than spending agent sessions attempting it,
mark it explicitly as a Mathlib dependency and move on. This doesn't affect
the book formalization's core value — 582/583 items are sorry-free.

### Change 4: Close stale/done issues

Issues #2341 (done), #2347 (done), #2361 (done via #2385), #2362 (done via #2387),
#2325 (partially done, needs replan) should be cleaned up.

## 4. Tractability Assessment

### Achievable (difficulty ≤ 6, clear path):
- Path infrastructure (#2384): 3-4 sorries, claimed, in progress
- D̃ embedding (line 8215): 1 sorry, after path infra
- etilde7 propagation (line 2792): injectivity chain, straightforward after hbot0

### Hard but viable (difficulty 7-8, established technique):
- etilde7 hN₁ + hN₂ (lines 2748-2751): nilpotent invariance at leaf
- etilde7 hbot0 (line 2785): center propagation
- etilde6v2 (line 2332): same technique as etilde7, simpler
- garnir_twisted_in_lower_span (line 670): infrastructure complete
- Forward bridge (line 171): after field-generic refactor

### Very hard (difficulty 8-9, unclear path):
- t125 (line 3008): same technique, but 9 vertices
- dTilde (line 2177): parametric k, most general case
- Backward bridge (line 210): heavy bridging infrastructure
- iso_of_formalCharacter_eq_schurPoly (line 221): Mathlib gap

## 5. Recommended Work Priority

1. **Merge nothing** — no open PRs currently
2. **Close stale issues** (#2341, #2347, #2361, #2362)
3. **Let #2384 complete** (path infrastructure, already claimed)
4. **Work #2379** (etilde6v2 indecomposability) — issue exists, unclaimed
5. **Work #2380** (garnir_twisted_in_lower_span) — issue exists, unclaimed
6. **Decompose etilde7 sub-sorries** into separate issues for parallel work
7. **Backward bridge** (#2256) — independent, can start anytime

## 6. Skill Update Recommendations

### lean-formalization SKILL.md

Add to Known Dead-Ends:
- `iso_of_formalCharacter_eq_schurPoly` requires GL_N complete reducibility
  (Schur-Weyl duality), which is not in Mathlib. Mark as Mathlib dependency.

Add to patterns:
- **Indecomposability proof pattern:** Reference `cycleRep_isIndecomposable` (lines
  304-372) as the template. Key steps: (1) show nontrivial, (2) propagate invariance
  through arms, (3) apply `nilpotent_invariant_compl_trivial` at leaf, (4) propagate
  ⊥ back. For extended Dynkin types, the nilpotent enters at one arm and must be
  shown to propagate to the leaf where the complement argument fires.

## 7. Trajectory Update

| Wave | Sorries | Files | Items sorry-free | Date |
|------|---------|-------|------------------|------|
| 48 | 8 | 6 | 581/583 (99.7%) | 2026-04-11 |
| 49 | 10 | 6 | 581/583 (99.7%) | 2026-04-12 |
| 50 | 13 | 5 | 581/583 (99.7%) | 2026-04-13 |
| 51 | 21 | 5 | 582/583 (99.8%) | 2026-04-17 |
| 52 | 17 | 4 | 582/583 (99.8%) | 2026-04-17 |
| **53** | **16** | **4** | **582/583 (99.8%)** | **2026-04-17** |

**Best-case trajectory (if all tractable sorries close):**
- After path infra + D̃ embedding: 16 → 11 (−5)
- After etilde7: 11 → 7 (−4)
- After etilde6v2: 7 → 6 (−1)
- After garnir: 6 → 5 (−1)
- Hard residual: 5 sorries (t125, dTilde, iso, forward bridge, backward bridge)

**Realistic end state:** 5-8 sorries, concentrated in the hardest proofs.
