---
name: lean-formalization
description: Use when working on Phase 3 formalization — translating mathematical text into Lean 4 statements and proofs, or filling sorry placeholders.
allowed-tools: Read, Edit, Write, Bash, Glob, Grep
---

# Lean Formalization Skill

Patterns for formalizing mathematics textbooks into Lean 4 with Mathlib. Derived from Phase 2 analysis of 583 items across 10 chapters of Etingof's Representation Theory.

## Session Setup

Before the first `lake build` or `lake env lean` in any session:
```bash
lake exe cache get
```
This downloads pre-built Mathlib oleans. Skipping it triggers a full Mathlib rebuild (1800+ jobs).

## Pre-Flight Checklist (Before Starting Any Proof)

Run this checklist before writing a single tactic. Skipping it has caused agents to waste entire context windows on dead-ends.

1. **Check Known Dead-Ends.** Scan the "Known Dead-Ends" section below. If your proof requires any of these patterns, sorry it immediately and move on:
   - ExteriorAlgebra ↔ PiTensorProduct bridging
   - `if`-branching `obj` fields in QuiverRepresentation-like structures
   - `Decidable.casesOn` **composition** (double round-trip) in `reflectionFunctorPlus`/`Minus` proofs — the composition F⁻(F⁺(V)) creates types Lean can't reduce through. **Note:** Individual arrow-level helper lemmas (e.g., `reversedArrow_ne_ne_is_cast`, `reversedArrow_ne_ne_twice`) ARE provable using `eqRec_heq_self` and `Subsingleton.elim` patterns (see HEq section below). The dead-end is the full Sigma-level round-trip, not individual components.
   - `reflFunctorPlus_mapLinear_ne_ne` / `reflFunctorMinus_mapLinear_ne_ne` API (missing; needed for reflection functor naturality in the ne/ne case)
   - ~~Definition-level `sorry : Type` for `AlgIrrepGL`~~ — **RESOLVED** (Wave 35): SchurModule constructed in PR #1740, AlgIrrepGL instances via `show ... from inferInstance` in PR #1752. Some downstream definition sorrys remain (`formalCharacter`, `kostkaNumber`).
   - Nilpotent operator structure theorem (cyclic decomposition / Jordan chains) — not in Mathlib, blocks Problem6_9_1. Would require ~100-200 line development.
   - Clifford theory (semidirect product orbit method) — blocks Mackey machine (Theorem5_27_1). Would require ~500 lines of new theory.
   - `Submodule.map` of complementary submodules through non-injective maps — does NOT preserve complementarity. Problem6_9_1 IsCompl conditions hit this fundamental gap.
   - `Lemma5_13_3` (Young symmetrizer idempotency) over general fields — currently only works over ℂ. Blocks the trace-based approach to Weyl character formula.
   - Corner ring Morita equivalence (`eAe` Morita equivalent to `A` for full idempotent `e`) — not in Mathlib, ~200-300 lines. Blocks BasicAlgebraExistence.
   - `basic_morita_algEquiv` (basic + Morita equivalent ⟹ isomorphic) — fundamental circularity: all non-circular approaches require Krull-Schmidt theorem or progenerator theory, neither in Mathlib.
   - Right-multiplication dominance for polytabloids — `column_perm_dominance` proves LEFT multiplication dominance, but linear independence needs RIGHT multiplication. Left permutes positions, right permutes entries — fundamentally different. Blocks `polytabloid_linearIndependent'`.
   - Non-commutative `TensorProduct` — Mathlib requires `CommSemiring`. Balanced tensor product `A ⊗_{eAe} N` must be built as a manual quotient (~100 lines boilerplate). Blocks corner ring Morita equivalence and BasicAlgebraExistence.

2. **Search for existing definitions and infrastructure.** Before defining any concept or building any equivalence/isomorphism, search the codebase:
   ```bash
   grep -r "def.*YourConceptName\|abbrev.*YourConceptName" EtingofRepresentationTheory/
   ```
   Duplicate definitions across chapters create incompatibility bugs that require manual refactoring later (e.g., duplicate `inducedCharacter'` in Ch5, duplicate `IsIndecomposable` in Ch2/Ch6). **Also search for infrastructure you might need** — PRs #1682, #1685, #1690 independently built the same GL₂(𝔽_q) BorelSubgroup equivalence because agents didn't check what already existed. Before building group/subgroup equivalences, coset decompositions, or character computation helpers, search for them first.

3. **Verify the statement.** Cross-reference the Lean statement against the book's text. Missing hypotheses (algebraic closure, field characteristic, orientation constraints) are a recurring source of wasted proof attempts. If the proof fails at a fundamental level after 1 attempt, suspect a statement bug before trying alternative tactics.

4. **Estimate your context budget.** Difficulty 3/3 proofs consume 60-80% of a context window on average. If you're already past the midpoint of your session, consider claiming an easier item instead. Partial progress on a hard proof with no commit is worth zero — a completed easy proof is worth one sorry removed.

5. **Check dependency readiness.** Verify that imports compile and key helper lemmas are sorry-free (or that sorry'd helpers won't block your proof). Use `lake build <module>` for the specific file.

6. **Code the framework before deep analysis.** When a proof has an obvious high-level structure (e.g., "use Schur's lemma + nonvanishing"), code that framework with sorry placeholders within the first 15 minutes. Don't spend the majority of your session analyzing whether the hard step is provable before writing any Lean. The framework commit has value even if the hard sorry remains — it reduces the problem for future agents. Deep mathematical analysis should happen AFTER the framework compiles, focused on the specific sorry goals.

## Translation Pipeline

Formalizing an item follows three stages: **translate**, **scaffold**, **prove**.

### 1. Translate: Natural Language to Formal Statement

Read the item's blob text and its `.refs.md` file (Mathlib coverage + external sources). Then:

1. **Identify the Mathlib types.** Check `.refs.md` for exact/partial matches. For exact matches, use the Mathlib declaration directly. For partial matches, read the Mathlib source to understand the gap.
2. **State the theorem/definition.** Write the Lean signature with `sorry` as body. Include a docstring with the book's natural language statement.
3. **Check it compiles.** Run `lake env lean <file>` — fix import and type errors before proceeding.

**Common pitfalls:**
- Don't invent type classes. If Mathlib doesn't have a concept, use a `structure` or `def` with explicit fields.
- Don't use `True` as a placeholder for propositions — it compiles but hides the real requirement.
- Check that universe levels are consistent. Representation theory often needs `Type*` not `Type`.
- **WF-recursive definitions** (`termination_by`): Don't use `rw [f]` or `simp [f]` to unfold — they fail on WF-recursive functions. Instead, prove a separate `have` using `unfold f` (works inside `conv` blocks), or extract a standalone unfolding lemma.

### 2. Scaffold: Set Up the Proof Structure

Before attempting the proof:

1. **Read the book's proof sketch.** Identify the key steps and what facts they use.
2. **Check dependencies.** All items this proof depends on should be sorry-free (or admitted for now). If not, either work on those first or use `admit` temporarily.
3. **Outline the proof.** Use `sorry` for each major step:

```lean
theorem foo : statement := by
  -- Step 1: reduce to case X
  sorry
  -- Step 2: apply theorem Y
  sorry
  -- Step 3: algebraic manipulation
  sorry
```

### 3. Prove: Fill In Sorries One at a Time

Follow the global CLAUDE.md proof rules strictly:

1. **One tactic at a time.** Write one tactic, check diagnostics.
2. **Use `done` to see remaining goals.** Don't guess what the goal state is.
3. **Error priority:** syntax > type > unsolved goals > warnings.
4. **Stop at first error.** Don't continue writing tactics after an error.
5. **Hardest case first.** For case splits, sorry the easy cases and focus on the hard one.

### Private Abbreviation Gotcha

Multiple files define `private abbrev GL2 = ...` / `private abbrev GL2' = ...` for the same underlying type. When using lemmas across files, `rw`/`simp`/`show` may fail because the elaborator sees different abbreviation names. Workarounds:
- Use `have h := lemma_from_other_file ...` then `rw [h]` (let unification handle it)
- Use `change` instead of `show` when the target uses a different abbreviation
- For sorry'd lemmas that need `[Fintype F] [DecidableEq F]` instances (needed by callers and the sorry body): wrap in a `section` with `set_option linter.unusedFintypeInType false` / `set_option linter.unusedDecidableInType false`. The `set_option ... in` syntax doesn't work before `private`.

### Tactic Selection Guide

| Goal Shape | Try First | Then Try |
|-----------|-----------|----------|
| `⊢ a = b` (algebraic) | `ring`, `field_simp; ring` | `simp`, manual `rw` |
| `⊢ a = b` (categorical) | `simp [CategoryTheory...]` | `ext`, `aesop_cat` |
| `⊢ P ∧ Q` | `exact ⟨..., ...⟩` or `constructor` | split into subgoals |
| `⊢ ∃ x, P x` | `exact ⟨witness, proof⟩` | `use witness` |
| `⊢ P → Q` | `intro h` | `fun h => ...` |
| `⊢ ∀ x, P x` | `intro x` | lambda |
| Finite group theory | `decide` (small groups) | case analysis |
| Linear algebra | `ext`, `simp [LinearMap...]` | `apply LinearMap.ext` |
| Module homomorphisms | `ext`, `simp` | manual composition |

### Dependent Pi Types and Pi.single

When working with `Pi.single` for dependent function types (e.g., `∀ i, Matrix (Fin (d i)) (Fin (d i)) k`), standard lemmas like `Pi.single_eq_same`, `Pi.single_add` do NOT work with `simp` because types differ across indices.

**Working pattern** — unfold to `Function.update` and manipulate `dite`:
```lean
ext t r s  -- go all the way to scalar level
simp only [Pi.single, Function.update, dite_apply, Pi.zero_apply, ...]
split
· next h => subst h; rfl  -- or simp
· simp  -- the ¬(i = t) case gives 0
```

Key insight: `ext t` alone leaves dependent casts (`⋯ ▸ x`). Go deeper with `ext t r s` to reach scalar goals where `subst` eliminates the cast.

### Representation Theory Patterns

This book covers:
- **Chapters 1-3:** Basic algebra (associative algebras, quivers, Lie algebras)
- **Chapters 4-6:** Representation theory fundamentals (representations, characters, tensor products)
- **Chapters 7-10:** Advanced topics (structure theorems, categories, Hopf algebras)

**Key Mathlib imports for this book:**
```
Mathlib.Algebra.Algebra.Basic
Mathlib.RingTheory.TensorProduct.Basic
Mathlib.Representation.Basic
Mathlib.Algebra.Lie.Basic
Mathlib.Algebra.Category.ModuleCat.Basic
Mathlib.LinearAlgebra.TensorProduct.Basic
Mathlib.GroupTheory.GroupAction.Basic
```

**When Mathlib doesn't have it:** This is the most important work in the project — prove it here. Check the `.refs.md` file for the item. If coverage is "gap", build the definition and proof from scratch. These are the highest-priority items, not items to defer. If the book proves the result (or assigns it as an exercise with hints), follow the book's approach. If it's genuinely external mathematics, prove it anyway — that's what this project is for.

## Scaffolding Anti-Patterns

These patterns were discovered during Chapter 2 and 7-8 reviews. Avoid them in all scaffolding work.

### Never sorry a Type

```lean
-- BAD: sorry'd type breaks all downstream usage
noncomputable def Etingof.PathAlgebra ... : Type* := sorry

-- GOOD: define carrier concretely, sorry the algebraic instances
def Etingof.PathAlgebra ... := FreeModule k (Quiver.Path ...)
instance : Algebra k (Etingof.PathAlgebra ...) := sorry
```

A sorry producing `Type*` gives `sorryAx Type*` — no instances can be built on it. Define the carrier type concretely and sorry the structure instances.

### Don't alias only the carrier type

```lean
-- BAD: misses the Lie module structure (the actual content of the definition)
abbrev Etingof.LieTensorProduct ... := TensorProduct k V W

-- GOOD: alias and import the relevant instance
import Mathlib.Algebra.Lie.TensorProduct
abbrev Etingof.LieTensorProduct ... := TensorProduct k V W
-- The Lie module instance is provided by the import
```

When a definition is about *structure on a type*, the alias must capture the structure, not just the carrier.

### Don't scaffold definitions as theorems

```lean
-- BAD: book definition scaffolded as theorem
theorem Etingof.Definition_8_2_3 : (sorry : Prop) := sorry

-- GOOD: use def/abbrev for definitions
noncomputable def Etingof.TorFunctor ... := sorry
```

Use `def`/`abbrev`/`noncomputable def` for definitions, `theorem`/`lemma` for propositions.

### Don't write tautological examples

```lean
-- BAD: proves nothing
example (A : Type*) [Ring A] : (1 : A) = 1 := rfl

-- GOOD: demonstrate actual properties
example (A : Type*) [Ring A] (a : A) : 1 * a = a := one_mul a
```

### Verify blob content before scaffolding

If a blob file is empty, flag it rather than scaffolding from the title alone. Title-only scaffolding produces low-quality formalizations.

### Use minimal imports

Prefer the most specific Mathlib module. Don't import `Mathlib.LinearAlgebra.DirectSum.Finite` when `Mathlib.Algebra.Module.Prod` suffices.

### Match Mathlib's generality for type class assumptions

If Mathlib uses `[Semiring R]`, don't restrict to `[CommRing R]`. Use the same or a compatible assumption. Within a chapter, be consistent — don't use `[CommRing R]` in one definition and `[Ring R]` in the adjacent one.

## Scaffolding Review Checklist

When reviewing scaffolded files, check each item against this list:

1. **Compilation**: `lake build <module>` passes with only expected sorry warnings
2. **Lean↔Blob↔items.json alignment**: every items.json entry has a .lean file and a blob file, no orphans
3. **Mathlib alias correctness**: `#check` the referenced declaration, verify it exists and is non-deprecated
4. **Type class consistency**: assumptions match Mathlib's (or are intentionally more specific with documented rationale)
5. **Anti-pattern scan**: no sorry'd types, no carrier-only aliases, no definitions-as-theorems, no tautological examples
6. **Import minimality**: imports are the most specific Mathlib module needed
7. **Doc-string quality**: matches the blob text, identifies Mathlib correspondence
8. **Gap definitions**: carrier type is concrete (not sorry'd), instances are sorry'd

Write findings to `reviews/<chapter>-scaffolding-review.md` with per-file scores and systematic pattern analysis.

## Quality Checks

Before submitting a PR for a formalized item:

1. **`lake env lean <file>` passes** — no errors
2. **No `sorry` remaining** in the target item (sorry in dependencies is OK)
3. **No `admit`** anywhere in committed code
4. **Docstring present** with book's natural language statement
5. **Imports are minimal** — only import what's actually used
6. **No duplicate declarations** — search for the declaration name across all files before adding. Duplicate names (even private ones) cause CI failures when files are compiled together. PRs #1655, #1657 were CI fixes for this exact issue.
7. **Heartbeat budget** — if your proof uses heavy `decide`, `omega`, or trace computations, test with the CI heartbeat limit. Use `set_option maxHeartbeats N in` to increase locally if needed. Guidelines:
   - **≤ 400000**: Normal, no annotation needed
   - **400000–800000**: Acceptable for trace/character computations over finite groups. Add a comment explaining why.
   - **800000–1600000**: Borderline. Acceptable only for GL₂(𝔽_q) trace computations or similar unavoidable large finite sums. Must have a comment. Consider whether `simp` can be replaced with targeted `rw` to reduce heartbeats.
   - **> 1600000**: Refactor the proof. Extract helper lemmas, precompute intermediate results, or use `native_decide` for finite checks.

## Issue Sizing for Formalization

Based on Phase 2 experience with issue sizing:

- **Definitions:** 1-3 per issue (fast, low risk)
- **Easy theorems** (direct application of Mathlib): 2-5 per issue
- **Medium theorems** (multi-step proofs): 1-2 per issue
- **Hard theorems**: 1 per issue
- **Never mix difficulty levels** in one issue — a hard theorem blocks the easy ones

## Proven Proof Strategies

Patterns that have succeeded in this project, derived from 110+ merged proof PRs (through wave 20).

### Mathlib Alias Pattern (Chapter 2)

When a book definition matches a Mathlib concept exactly, use a simple alias:

```lean
/-- Definition 2.1.1: An associative algebra over k. -/
abbrev Etingof.Algebra (k : Type*) [CommRing k] (A : Type*) := Algebra k A
```

This pattern covered 19/25 Chapter 2 definitions. Check `.refs.md` — if coverage is "exact match", alias first, prove later. Don't build custom definitions when Mathlib already has the concept.

### Type Class Instance Examples

For "example" items that demonstrate a type satisfies a definition, use `inferInstance`:

```lean
/-- Example 2.2.1: M_n(k) is an algebra. -/
instance : Algebra k (Matrix (Fin n) (Fin n) k) := inferInstance
```

This compiles cleanly when Mathlib already provides the instance. Check with `#check` first.

### Norm-Based Contradiction (Analysis Proofs)

For proofs requiring algebraic integer arguments (e.g., Lemma 5.4.5):
1. Use `Algebra.norm` to map from the algebraic number to a rational integer
2. Establish `|Norm(α)| ≥ 1` (since α is a nonzero algebraic integer, its norm is a nonzero integer)
3. Establish `|Norm(α)| < 1` via triangle inequality and `norm_sum_lt_of_strictConvexSpace`
4. Derive contradiction

This two-step norm approach works whenever you need to show an algebraic quantity equals zero or a root of unity.

### `sorry : Prop` for Unprovable Statements

When Mathlib lacks the types to express a theorem's statement at all (not just the proof), use:

```lean
/-- Theorem X.Y.Z: [natural language statement].
    Statement requires infrastructure not yet in Mathlib. -/
theorem theorem_X_Y_Z : (sorry : Prop) := sorry
```

This is sanctioned for items where the *statement itself* cannot be formalized (e.g., Gabriel's theorem needing quiver representation types, sl(2) classification). These items cannot be proved until infrastructure is built. Track them with status `needs_infrastructure` in items.json.

**Never use `True` as a placeholder** — it compiles silently and hides the gap.

### Multipart Theorem Strategy

When a theorem has multiple parts (e.g., existence + uniqueness, or (i)+(ii)+(iii)), prove them independently and leave unsolved parts as `sorry`:

```lean
theorem foo : Part1 ∧ Part2 ∧ Part3 := by
  refine ⟨?_, ?_, ?_⟩
  · -- Part 1: proved
    exact proof1
  · -- Part 2: hardest, work on this first
    sorry
  · -- Part 3: easy, fill in after Part 2
    sorry
```

**Always work on the hardest part first.** If Part 2 fails, all effort on Parts 1 and 3 is wasted. Commit partial proofs — they document exactly what's missing and unblock downstream work that doesn't need the sorry'd parts.

This pattern succeeded for Theorem 3.10.2 (part i proved, part ii sorry'd), Theorem 5.4.4 (main structure done, one ingredient sorry'd), and IrreducibleEnumeration (injectivity + simplicity proved, surjectivity sorry'd).

### Character Orthogonality for Span/Independence (Wave 30)

When proving that a set of characters spans or is linearly independent, use inner product orthogonality:

```lean
-- Prove ℚ-span via orthogonality + induction
have h_orth := FDRep.char_orthonormal
-- Use span_induction to reduce to showing each basis element is in the span
apply Submodule.span_induction ...
```

**Key APIs:** `FDRep.char_orthonormal`, `ClassFunction.inner_eq_zero_of_ne`, `Submodule.exists_le_ker_of_notMem`.

**Evidence:** This proved Theorem5_26_1 (Artin's theorem) completely — both `class_fun_vanishes_on_subgroup_of_orthogonal` and `artin_Q_span_of_induced_chars` used character inner products. Also proved the character orthogonality lemma for `principalSeries_simple_of_ne`.

**Pattern:** For any "show X is in the span of Y" problem in representation theory, first check if orthogonality gives you a clean proof. It usually does.

### IsSplitMono + Cokernel for Representation Decomposition (Wave 30)

When proving a representation decomposes as a direct sum V ≅ A ⊕ B:

1. Construct a nonzero mono `f : A ⟶ V` (e.g., an embedding)
2. Apply Maschke's theorem to get `IsSplitMono f`
3. Use `binaryBiconeOfIsSplitMonoOfCokernel` to get V ≅ A ⊞ cokernel(f)
4. Identify cokernel(f) ≅ B (often via dimension counting)

```lean
-- Step 1: Get IsSplitMono from Maschke
have hsm : IsSplitMono detCharEmbedding := Abelian.IsSplitMono_of_mono _
-- Step 2: Build biproduct via cokernel
exact binaryBiconeOfIsSplitMonoOfCokernel detCharEmbedding
```

**Evidence:** This approach is set up for `principalSeries_decomp` (V(μ,μ) ≅ ℂ_μ ⊕ W_μ). The infrastructure lemmas (detChar_simple, detCharEmbedding_mono, detCharEmbedding_ne_zero) proved in PRs #1624, #1658 feed directly into this pattern.

### Dimension Contradiction Pattern (Wave 30)

For proving properties by contradiction using `Module.finrank`:

```lean
-- Show two finite-rank subspaces can't both fit
have h1 : Module.finrank k S₁ ≥ 1 := ...
have h2 : Module.finrank k S₂ ≥ 1 := ...
have h3 : Module.finrank k V = Module.finrank k S₁ + Module.finrank k S₂ := ...
-- Derive contradiction from dimension inequality
omega
```

**Evidence:** Proved nilpotent_nontrivial_decomp (d=1 contradiction in PR #1628, subrepresentation arguments in PR #1632). Also used in decomp_of_ker_sum_ge_two dimension argument (PR #1633).

### Graph Isomorphism for Classification Proofs (Wave 30)

For Dynkin-type classification proofs requiring graph isomorphisms between combinatorially-defined graphs:

```lean
-- Build explicit bijection via path permutation
def tree_branch_iso : G₁ ≃g G₂ where
  toEquiv := pathPermutation ...  -- permute vertices along a canonical path
  map_rel_iff' := ...
```

**Evidence:** PR #1634 used `tree_branch_iso` to prove all 4 arm cases (D_n, E₆, E₇, E₈) in `branch_classification`, reducing Theorem_Dynkin_classification from 6 sorries to 0. The key insight: express graph isomorphisms as path permutations with optional reversal.

### FDRep Categorical Plumbing

Working with `FDRep` (finite-dimensional representations as a category) requires navigating multiple abstraction layers. This is the #1 blocker in Chapters 4-5.

**The problem:** Book proofs work with concrete linear maps `V →ₗ[k] V`, but Mathlib's FDRep uses categorical morphisms. Converting requires unwrapping 3 levels: `Action.Hom → FGModuleCat.Hom → ModuleCat.Hom → LinearMap`.

**Pattern 1: Reflect through a full+faithful functor**

When you need to prove a property about FDRep objects (like simplicity), prove it for the underlying module and reflect through the functor:

```lean
-- Prove simplicity for the concrete module first
have h : IsSimpleModule k M := Matrix.instIsSimpleModule ...
-- Reflect to FDRep via full+faithful functor
exact Simple.of_full_faithful_preservesMono FDRep.forget₂ h
```

This avoids working inside the categorical abstraction entirely.

**Pattern 2: Use Representation directly instead of FDRep**

For character theory, prefer `Representation k G V` (which gives you `V →ₗ[k] V` directly) over `FDRep k G` (which wraps in a category). Most character computations don't need the categorical structure.

**Pattern 3: Avoid `.hom.hom` chains**

If your proof requires distributing `.hom.hom` over `Finset.sum` or similar, you're fighting the abstraction. Instead:
- Define a helper that states the result directly on `LinearMap`
- Or use `Representation.averageMap` which already works at the LinearMap level

**When stuck on FDRep plumbing after 2 attempts:** Sorry the categorical step with a comment explaining what's needed, and file an issue. Don't spend an entire session on unwrapping functors.

### Bezout Reduction for Integrality

When proving `IsIntegral ℤ (a / b)` where `a` and `b` are related by coprimality:

1. Find `m, n` with `m * b + n * a = 1` via `Nat.Coprime` and `Nat.gcd_eq_gcd_ab`
2. Rewrite `a / b = m * (stuff₁) + n * (stuff₂)` where both summands are provably integral
3. Apply `IsIntegral.add` and `IsIntegral.mul`

This avoids dependent type issues from rewriting `a/b` directly. Used successfully in Theorem 5.4.4.

### Full+Faithful Functor Reflection for Simplicity

To prove an FDRep is simple:
1. Prove `IsSimpleModule k M` for the underlying module (often via `Matrix.instIsSimpleModule`)
2. Lift through `IsSimpleModule.compHom` if needed (for algebra homomorphisms)
3. Reflect to categorical `Simple` via `Simple.of_full_faithful_preservesMono`

This chain: concrete simplicity → algebra hom transfer → functor reflection was the successful pattern for IrreducibleEnumeration (#678).

### Permutation Matrix Arguments

For character identities involving the regular representation (e.g., χ_reg(g) = 0 for g ≠ 1):
- Express the representation matrix as a permutation matrix of left-multiplication
- Show the permutation has no fixed points when g ≠ 1
- Conclude the trace (= character value) is zero

This is more concrete than abstract character theory and avoids FDRep entirely.

### Jacobson Radical for Injectivity

To prove a ring homomorphism from a semisimple ring is injective:
1. Show every element of the kernel acts as zero on all simple modules
2. Therefore the kernel element is in every maximal left ideal
3. The intersection of all maximal left ideals is the Jacobson radical
4. For semisimple rings, Jacobson radical = ⊥
5. Hence kernel = ⊥, so the map is injective

**Lean tip:** May need explicit universe parameters (`.{v}`) to make the Jacobson radical API work with the correct universe level.

## Mathlib Gap Handling

When you discover a Mathlib API gap during formalization, follow this escalation ladder:

### Level 1: Local Workaround (< 30 min)
If you can define the missing concept locally in ≤ 20 lines and it unblocks the proof:
```lean
-- Local definition until Mathlib adds IsIndecomposable
def IsIndecomposable (M : Type*) [AddCommMonoid M] [Module R M] : Prop :=
  ¬IsZero M ∧ ∀ N₁ N₂ : Submodule R M, N₁ ⊓ N₂ = ⊥ → N₁ ⊔ N₂ = ⊤ → N₁ = ⊥ ∨ N₂ = ⊥
```

### Level 2: `sorry` the Gap, File an Issue (> 30 min)
If building the infrastructure would take > 30 min:
1. Use `sorry` for the missing fact
2. Add a comment: `-- Requires [description], not in Mathlib as of v4.28`
3. File a GitHub issue with label `needs-mathlib-api` describing exactly what's needed
4. Move on to the next item

### Level 3: Infrastructure Issue (Blocks Multiple Items)
If the same gap blocks 3+ items (e.g., column orthogonality blocking all character theory):
1. File a detailed GitHub issue documenting:
   - What's missing (with mathematical description)
   - Which items are blocked
   - Whether Mathlib has partial coverage (e.g., row orthogonality exists but not column)
   - Estimated effort to build locally
2. Mark all blocked items as `needs_infrastructure` in items.json
3. Don't attempt to build major infrastructure during a proof session — that's a separate planned issue

### Known Gaps in This Project

| Gap | What Exists | What's Missing | Blocks | Status |
|-----|------------|----------------|--------|--------|
| Column orthogonality | `FDRep.char_orthonormal` (row) | `∑_V χ_V(g) · χ_V(h⁻¹) = \|C_G(g)\| · δ` | Thm 5.4.6, Burnside | Issue #633 |
| Regular rep decomposition | `FDRep`, `Simple` | `k[G] ≅ ⊕ dim(V_i) · V_i` | Thm 5.4.6 | Issue #643 |
| Simple module classification | `Simple` predicate | Every simple FDRep ≅ some columnFDRep | IrrepEnum surjectivity | Issue #655 |
| FDRep ↔ LinearMap plumbing | `.hom` unwrapping | Distributing `.hom.hom` over sums, Schur at LinearMap level | Prop 5.3.2 | Workaround: non-categorical pattern |
| Quiver representations | `Quiver`, `PathAlgebra` | `QuiverRepresentation`, hom, subobjects | Ch6 items | Workaround: concrete constructions |
| Pigeonhole transposition | `Finset` API | Row/column counting for Young tableaux | Lemmas 5.13.1, 5.13.2 | Issues #776, #777 |
| Non-commutative TensorProduct | `TensorProduct` (CommSemiring only) | Balanced tensor product `A ⊗_{eAe} N` for non-commutative rings | BasicAlgebraExistence, MoritaStructural | Manual quotient construction needed |
| Krull-Schmidt theorem | None | Unique decomposition of modules into indecomposables | basic_morita_algEquiv (#1877) | Not in Mathlib, blocks Morita isomorphism |
| Clifford theory | None | Semidirect product orbit method, coset representations | Theorem5_27_1 (Mackey machine) | ~500 lines new theory needed |
| Right-multiplication dominance | Left-mult dominance proved | Right `σ · e_T` ≠ left `σ · e_T` for polytabloids | PolytabloidBasis (#1884) | Fundamentally different from left case |

## Proof Chain Completion Strategy

When multiple sorry'd items exist, **prioritize completing already-started chains** over beginning new proofs. A "chain" is a sequence of items where proving one unblocks the next.

**Why this works:** Chain completion has the highest ROI per agent-hour. Completing one helper lemma can cascade to chapter-level completion. In Wave 4, focusing on the Theorem 4.10.2 chain (2 helper lemmas) completed all of Chapter 4.

**How to identify chains:**
1. Look for items whose dependencies are all sorry-free except one
2. Look for chapters near 100% — one or two proofs may close them out
3. Check if a sorry'd helper lemma is used by 2+ other proofs

**Priority order for proof selection:**
1. Chain-completing proofs (unblock downstream items)
2. Chapter-completing proofs (achieve 100% for a chapter)
3. Infrastructure proofs (unblock 3+ items across chapters)
4. Standalone proofs (no downstream dependents)

## Quiver Representation Patterns

Chapter 6 quiver representations use concrete finite-dimensional constructions rather than abstract quiver theory. This approach was discovered in Wave 4 (Examples 6.2.2-6.2.4) after three waves of zero progress with abstract approaches.

### Concrete Construction Pattern

For quiver representations with vertices V₁, ..., Vₙ and arrows between them:

```lean
-- Represent each vertex space as Fin d →₀ k (or Fin d → k)
-- Represent each arrow as a concrete LinearMap between vertex spaces
structure D₄Rep (k : Type*) [Field k] where
  V  : Type* -- central vertex
  V₁ : Type* -- arm vertices
  V₂ : Type*
  V₃ : Type*
  A₁ : V₁ →ₗ[k] V  -- arrow maps
  A₂ : V₂ →ₗ[k] V
  A₃ : V₃ →ₗ[k] V
```

**Key insight:** Work with explicit `LinearMap`s between finite-dimensional spaces, not abstract `QuiverRepresentation` types. Mathlib's quiver infrastructure is insufficient for the proofs we need, but the concrete linear algebra API is rich.

### Indecomposability via Kernel Splitting

For classifying indecomposable representations:
1. Check kernels of arrow maps — if `ker Aᵢ ≠ ⊥`, split off the kernel as a direct summand
2. This reduces to the "all injective" case, which is the hard subspace-configuration problem
3. For the injective case, use `Submodule.IsCompl` and `Module.finrank` to classify

### Dimension Vector Pattern

Track dimension vectors `(dim V, dim V₁, ..., dim Vₙ)` as the primary classification tool. Indecomposability constraints on dimension vectors are often finite and enumerable.

## Combinatorial Counting Arguments

Pigeonhole-style counting arguments (e.g., "by counting, some row must have two elements mapping to the same column") are a persistent difficulty in Lean formalization. The mathematical intuition is simple but the formal proof requires careful API navigation.

### Recommended Approach

1. **State the counting lemma separately** — don't inline pigeonhole arguments in larger proofs
2. **Use `Finset.exists_ne_map_eq_of_card_lt`** (pigeonhole principle) when available
3. **For partition-based counting:** Express the constraint as a `Finpartition` or use `Finset.sum_card_fiberwise_eq_card` to relate partition sizes to totals
4. **For injection-based arguments:** Use `Fintype.card_lt_of_injective_of_not_surjective` or `Function.Injective.card_le`

### When Stuck on Combinatorial Proofs

After 2 serious attempts:
1. Sorry the combinatorial core with a precise comment describing the counting argument
2. Complete the algebraic frame around it (this is valuable and independently reviewable)
3. File an issue with status `attention_needed`

This "algebraic frame + combinatorial sorry" pattern was successfully used in Lemmas 5.13.1 and 5.13.2 (Young symmetrizer proofs).

## Non-Categorical Workaround Pattern

When a proof requires FDRep categorical machinery that's blocked by `.hom` plumbing, try reformulating the argument to avoid categories entirely.

**Example (Theorem 5.4.4, PR #721):** Instead of using the categorical Schur's lemma via FDRep:
- Used eigenvalues of central elements acting on simple modules
- Proved `character_div_dim_isIntegral` via direct algebraic argument
- Completely bypassed FDRep plumbing

**When to try this:**
- The proof fundamentally needs a fact about linear maps (traces, eigenvalues, determinants)
- The categorical formulation adds structure you don't actually need
- You've spent > 30 min fighting `.hom` unwrapping

**How to find the workaround:**
1. Write out the mathematical argument in terms of linear maps and matrices
2. Check if Mathlib has the needed lemmas at the `LinearMap` / `Matrix` level
3. If yes, build the proof there — it's usually cleaner than the categorical version

## Helper Lemma Extraction Pattern

When a proof is too complex for a single session, extract helper lemmas into separate declarations. This pattern was critical for Theorem 4.10.2 (block polynomial irreducibility) and the Young symmetrizer chain (5.13.1-5.13.4).

### When to Extract

- A proof attempt reveals a non-trivial subgoal that's independently meaningful
- The same fact is needed by 2+ proofs (e.g., `pigeonhole_transposition` used by both 5.13.1 and 5.13.2)
- A proof exceeds ~50 lines of tactics — break it up

### How to Extract

1. **State the helper as a separate `lemma`** in the same file, above the main theorem
2. **Use `sorry` for the helper's proof** — this lets you test the main theorem's proof structure immediately
3. **Commit the main theorem using the sorry'd helper** — this is valuable progress even if the helper is hard
4. **Work on the helper separately**

```lean
-- Helper extracted from complex proof
lemma helper_fact (n : ℕ) (h : n > 0) : some_property n := sorry

-- Main theorem uses the helper
theorem main_result : conclusion := by
  have h := helper_fact n hn
  exact ...
```

### Multi-PR Proof Chains

Complex theorems may span multiple PRs. This is expected and desirable:
- **PR 1**: State theorem + helpers, prove the algebraic frame, sorry the hard core
- **PR 2**: Prove helper lemmas
- **PR 3**: Close the last sorry

Each PR must compile. Label intermediate PRs with the item ID so reviewers can track the chain.

## Chapter Closure Tactics

When a chapter is within 1-3 items of 100% completion, prioritize closing it. Chapter closures have outsized value:
- Psychological milestone for the project
- Eliminates an entire category from the work queue
- Proves the formalization approach works end-to-end for that chapter

**Identifying closure candidates:**
1. Check `items.json` for chapters with high completion percentage
2. Look for items where all dependencies are sorry-free
3. Prefer the easiest remaining item to close the chapter first

**Evidence:** Ch3 closed via Jordan-Hölder (#831), Ch4 via block polynomial (#812). Both were chain-completion efforts that required focused multi-session work but had outsized impact on project morale and metrics.

## Endgame Priorities (Wave 40, 2026-03-28)

With **29 sorries** across 20 files, the remaining work is concentrated in hard items. All definition-level sorries are resolved (verified by scan on 2026-03-28). Easy wins are exhausted — future progress is slower per sorry.

**Trajectory:** 66 sorries (wave 28, Mar 22) → 33 (wave 37) → 27 (wave 38) → 29 (wave 40, Mar 28). Note: sorry count can increase when decomposition adds new sub-goals.

**Recently completed (Waves 38-40, PRs #1824–#1897):**
- Hilbert syzygy lower bound: Shapiro's lemma proved from scratch (#1870, #1880), Ext^n result (#1887)
- Hilbert syzygy upper bound: Koszul SES infrastructure + extendScalars preserves projective dim (#1897)
- Morita/corner ring: exists_full_idempotent_basic_corner fullness proved (#1881)
- Weyl character formula: trace formula sub-lemmas decomposed (#1883)
- Peter-Weyl: directSum_rank_ge_aleph0 proved (#1896, pending CI)
- Polytabloid: false theorem (tabloid expansion) identified and fixed (#1888)
- Determinant identity: det_clearedDenomMatrix_eq proved (#1845)

**Dependency DAG — strategic priority order:**

```
Proposition6_6_6_source (1 sorry) ← KEYSTONE: unblocks ~11 downstream
├─→ Corollary6_8_3 (1) → Problem6_1_5_theorem (1) → Theorem_Dynkin_classification (1)
├─→ Corollary6_8_4 (1)
└─→ Theorem2_1_2 (1)

Theorem5_22_1 (3 sorrys) ← unblocks character formula completion
├─→ Theorem5_23_2 (1)
└─→ Proposition5_22_2 (1)

CoxeterInfrastructure (2 sorrys) ← enables Corollary6_8_3 inductive step

Theorem5_27_1 (3 sorrys) [Independent — Mackey machine]
PolytabloidBasis (3 sorrys) + TabloidModule (3 sorrys) [Isolated cluster]
BasicAlgebraExistence (2 sorrys) → MoritaStructural (1)
Problem6_9_1 (2 sorrys) [Isolated]
Example9_4_4 (2 sorrys) [Isolated]
Theorem2_1_2 (1 sorry) [Blocked on Gabriel chain]
```

**Priority tiers:**

**Tier 1 — Highest strategic value:**
- Proposition6_6_6_source (1 sorry) — reflection functor naturality. Unblocks 5+ downstream theorems with 11+ sorrys total. Very hard (dependent type rewriting).
- Theorem5_22_1 (3 sorrys) — Cauchy identity / Vandermonde. Unblocks character formula completion (2 downstream).

**Tier 2 — Hard but tractable:**
- CoxeterInfrastructure (2 sorrys) — type-changing quiver iteration
- Problem6_9_1 (2 sorrys) — IsCompl conditions for projected subspaces
- Theorem5_27_1 (3 sorrys) — Mackey machine (needs Clifford theory ~500 lines)

**Tier 3 — Significant infrastructure:**
- BasicAlgebraExistence (2 sorrys) — corner ring Morita equivalence (~200-300 lines), non-commutative tensor products
- MoritaStructural (1 sorry) — basic_morita_algEquiv has fundamental circularity; all non-circular approaches require Krull-Schmidt or progenerator theory
- Example9_4_4 (2 sorrys) — Koszul SES exactness for polynomial rings

**Tier 4 — Isolated / lower priority:**
- PolytabloidBasis (3 sorrys) + TabloidModule (3 sorrys) — right-multiplication dominance needed (left was proved, right is fundamentally different)
- Theorem2_1_2 (1 sorry) — blocked on full Gabriel chain

**Key endgame insights:**
1. **All definitions are constructed.** Every remaining sorry is a pure proof obligation.
2. **Decomposition is the dominant value-creation pattern.** Converting a monolithic sorry into structured sub-goals (with 60-80% proved) is often the best outcome for a single session.
3. **Approach cycling is expensive.** After 3 genuinely different approaches, document and move on.
4. **Decidable.casesOn patterns are well-documented** (see sections below). Read before attempting Ch6 work.
5. **False theorems can hide in conjugation/action directions.** Verify statement correctness with concrete examples.
6. **Missing infrastructure is the primary blocker**, not tactic difficulty. Remaining sorrys need new mathematical developments (Clifford theory, Morita, tensor algebra isomorphisms).
7. **Circular dependencies between sorry'd theorems** exist (e.g., Prop 5.22.2 needs Thm 5.22.1). When both ends of a circle have sorrys, focus on the one with fewer prerequisites.
8. **Non-commutative tensor products are a recurring wall.** Mathlib's `TensorProduct` requires `CommSemiring`. Morita theory needs `A ⊗_{eAe} N` over non-commutative corner rings. Multiple agents have hit this — see "Non-Commutative Ring Workarounds" below.
9. **Multi-PR iteration is normal for hard items.** Complex theorems (Hilbert syzygy, Morita) routinely require 2-4 PRs: restructure → build infrastructure → prove. Plan for this.

## Non-Commutative Ring Workarounds

Mathlib's `TensorProduct` requires `CommSemiring`. Multiple agents across 4+ sessions have hit this wall when working on Morita theory and corner rings. Here are the known workarounds:

### The Problem
`TensorProduct R M N` requires `[CommSemiring R]`. But Morita equivalence needs `A ⊗_{eAe} N` where `eAe` is a corner ring (non-commutative in general).

### Workaround 1: Balanced Tensor Product as Quotient
Construct `A ⊗_{eAe} N` as a quotient of `A ⊗_k N` by the balanced submodule:
```lean
-- The balanced submodule: generated by (a · r) ⊗ n - a ⊗ (r · n) for r ∈ eAe
def balancedSubmodule : Submodule k (TensorProduct k A N) := ...
def BalancedTensorProduct := (TensorProduct k A N) ⧸ balancedSubmodule
```
This construction appeared in BasicAlgebraExistence and was used in 3+ sessions.

### Workaround 2: Use `isUnit_of_sub_one_mem_jacobson_bot` alternatives
The `isUnit_of_sub_one_mem_jacobson_bot` API requires `CommRing`. For non-commutative rings, use `IsNilpotent.isUnit_one_sub` instead (only requires `Ring`).

### Workaround 3: Avoid `linarith`/`linear_combination` over non-commutative rings
These tactics need `CommSemiring`. Use manual algebra (`calc` blocks with `mul_assoc`, `mul_comm` where applicable, or `ring_nf` after establishing commutativity of specific elements).

### Status
Non-commutative tensor products remain the hardest infrastructure gap. No clean resolution exists in Mathlib. The balanced quotient approach works but requires ~100 lines of boilerplate per use site.

## Type-Level If/Else Diamond Issue

When defining a structure whose `obj` field branches on vertex equality (e.g., `if v = i then T₁ else T₂`), Lean's typeclass system creates a diamond:

**The problem:** Structure fields like `[instAddCommMonoid : ∀ v, AddCommMonoid (obj v)]` and `[instModule : ∀ v, Module k (obj v)]` are filled sequentially. After `instAddCommMonoid` is filled (e.g., via `split; infer_instance`), it becomes opaque. The `instModule` field's type depends on `instAddCommMonoid`, but the opaque term prevents `split` from decomposing the `if` inside it.

**What doesn't work:**
- `split <;> infer_instance` for the Module field (can't split opaque match)
- `by_cases h; subst h; simp; infer_instance` (simp can't reduce `if` with opaque Decidable)
- `convert inferInstance` (leaves unsolvable HEq goals between opaque and concrete instances)
- Helper instances `iteAddCommMonoid`/`iteModule` (Module's AddCommMonoid dependency doesn't match)
- Sharing a `let`-bound `Decidable` value (doesn't reduce at type level)

**Current workaround:** Sorry the `instModule` field and the `mapLinear` field. The `obj` field (the mathematical content) and `instAddCommMonoid` can be concrete. This is acceptable per issue guidelines ("specific field obligations sorry'd").

**Potential solutions for a future refactor:**
1. Change `QuiverRepresentation` to not use `[...]` instance fields — use explicit bundled instances instead
2. Use `@[reducible]` on the obj definition so the `if` reduces
3. Define the representation for each case separately and combine using `Sigma`/`Sum`

This affects: Definition 6.6.3 (F⁺ᵢ), Definition 6.6.4 (F⁻ᵢ), and any future definition that branches `obj` on a proposition.

## Fintype Instance Mismatch in Sum Comparisons

When comparing two `Finset.sum` expressions over `Finset.univ` for a subtype (e.g., `↑(RowSubgroup n la)`), the `Fintype` instances may differ if one comes from a local `haveI : DecidablePred ... := Classical.decPred _` at the proof level and the other from a `haveI` inside the original definition. This makes the two `Finset.univ` propositionally but not definitionally equal.

**Symptoms:** `rfl` fails, `Finset.sum_congr rfl` fails, `congr 1; funext` fails, all with messages about `Finset.univ` not being definitionally equal.

**Fix:** Use `convert rfl using N` (typically `N = 2`) to handle the instance mismatch automatically via `Subsingleton (Fintype α)`. Then close remaining subgoals (e.g., summand equality) with `ext` + `simp`/`rw`.

```lean
-- Two sums that are "the same" but have different Fintype instances
-- ∑ x ∈ @Finset.univ _ inst₁, f x = ∑ x ∈ @Finset.univ _ inst₂, g x
convert rfl using 2
-- Remaining goal: f = g (pointwise)
ext ⟨σ, hσ⟩
simp [...]
```

**Preferred fix:** Add `open scoped Classical` at the section level (before any definitions that use `haveI : DecidablePred ... := Classical.decPred _`). This ensures all `DecidablePred` instances come from the same source, avoiding the mismatch entirely. This is better than `convert rfl` because it prevents the issue rather than patching it.

**Alternative:** Prove equality via `Finsupp.ext` (coefficient-wise) to sidestep sum comparison entirely.

## MonoidAlgebra Coefficient Computation

`MonoidAlgebra k G` is a `def` (not `abbrev`) alias for `G →₀ k`. This means `simp_rw` and `simp only` cannot see through it to apply `Finsupp` lemmas like `Finsupp.smul_apply`, `Finsupp.single_apply`, etc.

**Symptom:** `simp_rw [Finsupp.smul_apply, Finsupp.single_apply]` makes no progress on a goal involving `MonoidAlgebra` terms.

**Fix:** Use `Finset.sum_congr rfl` with `change` to coerce the term to `Finsupp` before `rw`:
```lean
rw [Finset.sum_congr rfl (fun i _ => show _ = _ from by
  change (c • (Finsupp.single g (1 : k))) σ = _
  rw [Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply])]
```

**Key lemmas for MonoidAlgebra coefficients:**
- `MonoidAlgebra.single_mul_apply`: `(single g r * x) h = r * x (g⁻¹ * h)` (for groups)
- `MonoidAlgebra.mul_single_apply`: `(x * single g r) h = x (h * g⁻¹) * r` (for groups)
- `Finsupp.finset_sum_apply`: `(∑ i ∈ S, f i) a = ∑ i ∈ S, f i a`
- `Finsupp.smul_apply`: `(b • v) a = b • v a` (definitional, but needs coercion via `change`)

## Trace-Based Proof Pattern

When a proof involves showing a group algebra element is nonzero, or bounding the dimension of a representation, try using traces of left-multiplication operators.

**Pattern (Young symmetrizer squared nonzero, Theorem 5.12.2):**
1. Prove `trace_lmul_monoidAlgebra`: `Tr(L_a) = |G| · a(1)` for any group algebra element `a`
2. Show that if `c² = 0` then `L_c` is nilpotent, hence `Tr(L_c) = 0`
3. But `Tr(L_c) = |G| · c(id) = n! ≠ 0` in characteristic zero
4. Contradiction

**When to use:** Whenever the mathematical argument involves "evaluate at the identity element" or "take the trace of left multiplication". This is cleaner than trying to work with the group algebra directly because traces are computed via `LinearMap.trace`.

**Key Mathlib APIs:** `LinearMap.trace`, `MonoidAlgebra.lmul`, `IsNilpotent`, `LinearMap.trace_eq_zero_of_isNilpotent`

## Reynolds Operator / Symmetrization Pattern

For proofs involving invariant subspaces under group actions (e.g., `V^G ≅ Sym^n V`):

1. Construct the symmetrization/averaging map: `symSum(x) = Σ_{σ ∈ G} σ · x`
2. Show `symSum` factors through the quotient (e.g., `SymmetricPower.mk`) via `AddCon.addConGen_le`
3. For injectivity on invariants: `symSum(x) = |G| · x` when `x` is invariant, so if images agree, `|G| · (a - b) = 0`, giving `a = b` by `CharZero`
4. For surjectivity: use `(|G|)⁻¹ · symSum(lift(y))` as preimage

**Key insight:** The Reynolds operator `R = (1/|G|) Σ_σ σ` is an idempotent projection onto invariants. Most invariant-subspace identifications reduce to showing `R` factors through the target construction.

## `decide` for Concrete Finite Computations

For theorems about specific small finite structures (e.g., D₄ quiver with 4 vertices):

```lean
-- Example 6.8.5: concrete D₄ reflection functor computations
example : reflectionResult₁ = expected₁ := by decide
```

**When to use:** The statement involves only `Fin n` for small `n`, concrete matrices, or specific permutations. If `decide` doesn't terminate in reasonable time (< 30s), fall back to `native_decide` or manual proof.

**Caution:** `decide` only works when all types are decidable and small. It won't work for general `n` or abstract algebraic structures.

## Strong Induction on Coordinate Sums (Root System Pattern)

For proofs involving positive roots or dimension vectors where the claim is "every element can be reached from simple elements via reflections":

1. **Induct on `∑ dᵢ`** (the coordinate sum of the dimension vector)
2. **Base case:** When `∑ dᵢ` is minimal (e.g., a simple root `eᵢ`), the claim holds trivially
3. **Inductive step:** Find a "good vertex" `k₀` where `(B·d)_{k₀} > 0` (positive entry in Cartan matrix product)
4. **Key lemma:** If no good vertex exists, construct `d' = d - e_{k₀}` and show `B(d', d') ≤ 0`, contradicting positive-definiteness

**Implementation pattern:** Build helper lemmas systematically:
- Cartan matrix symmetry (`cartanMatrix_symm`)
- Simple reflection properties (`simpleReflection_preserves_bilinearForm`)
- `exists_good_vertex` (by contradiction using positive-definiteness)
- Main induction with `Nat.strongRecOn` or `WellFoundedRelation`

This pattern proved Theorem 6.8.1 (reaching simple roots via reflections) — the linchpin of Gabriel's theorem. It's applicable to any root-system argument requiring structural induction.

## Rank-Nullity for Non-Commutative Hom Spaces

For proofs about `Hom_A(P, M)` where `A` is a non-commutative algebra:

1. Use `LinearMap.finrank_range_add_finrank_ker` for Hom additivity on short exact sequences
2. Use `Submodule.comapSubtypeEquivOfLe` for relating submodule preimages
3. For composition factor simplicity: `covBy_iff_quot_is_simple`

**Key workaround:** `LinearEquiv.congrRight` requires commutativity. For non-commutative algebras, manually construct k-linear equivalences on Hom spaces instead. This was the successful pattern for Proposition 9.2.3.

## Partial Proof Publication Pattern

When a theorem has conceptually independent parts (e.g., symmetric power + exterior power):

1. **Split the theorem** into independent sub-declarations
2. **Prove the tractable part** completely (sorry-free)
3. **Sorry the hard part** with an explicit issue filed
4. **Submit as `proof_partial`** in items.json

This is strictly better than leaving the entire theorem sorry'd. Downstream work that only needs the proved part can proceed. Example: Example 5.19.3 symmetric power was proved completely while the exterior power part (blocked by the ExteriorAlgebra/PiTensorProduct coercion gap) was sorry'd with an issue.

## Verify Statement Correctness Before Proving (Convention Check)

**Before attempting any proof involving Mathlib conventions** (signs, orderings, normalizations), verify the statement is correct with a small concrete example.

**The problem:** Convention mismatches between the book and Mathlib silently make statements unprovable. These appear as "unprovable goals" rather than type errors. Agents spend entire sessions trying proof strategies before discovering the statement itself is wrong.

**Known convention differences:**
- `vandermondePoly` uses `∏_{i<j}(x_j - x_i)` (Mathlib) vs the book's `∏_{i<j}(x_i - x_j)`, differing by `Equiv.Perm.sign(Fin.revPerm)`
- Alternating sum conventions may differ in sign
- Partition/Young diagram indexing conventions may differ

**Verification pattern:**
```lean
-- Before proving: test with n=2 or smallest non-trivial case
#eval do
  let lhs := <your_LHS_computed_for_n_2>
  let rhs := <your_RHS_computed_for_n_2>
  return (lhs == rhs)  -- should be true!
```

If the concrete example fails, the statement has a convention bug. Fix the statement before attempting the proof. This check takes 5 minutes and can save an entire session.

## Dependent Type Rewriting Patterns

Direct `rw` on dependent types is a recurring friction point. These patterns work:

### Pattern 1: `congrArg` with `Fin.ext` (for Fin-indexed access)
When you need to rewrite a `Fin` value inside a dependent context (e.g., cycle access, list indexing):
```lean
-- Instead of: rw [some_fin_equality]  -- fails with "motive is not type correct"
-- Use:
exact congrArg cycle.get (Fin.ext (by omega))
```

### Pattern 2: `suffices ∀ s, ...` (generalize-then-instantiate)
When rewriting a term `b` that appears in dependent types like `hab : a ≤ b`:
```lean
suffices ∀ s, statement_about s by
  convert this ?_ <;> exact the_specific_equality
intro s
-- Now prove for arbitrary s (no dependent type issues)
```

### Pattern 3: `show`/`change` for `Fin.cons` goals
`Fin.cons_zero`/`Fin.cons_succ` don't match literal `(0, _)`/`(n+1, _)` syntactically:
```lean
-- Instead of relying on simp to reduce Fin.cons:
show <explicit_expected_form>  -- or use `change`
-- Then apply the appropriate lemma
```

### Pattern 4: `convert rfl using N` for Fintype instance mismatches
When two `Finset.univ` expressions use different `Fintype` instances:
```lean
convert rfl using 2  -- handles instance mismatch via Subsingleton
```

### Pattern 5: `unfold + match` for `Decidable.casesOn` composition
When two functions both use `match inst a b, inst c d with ...` on the same decidable instances,
their composition should reduce to identity. Standard tactics (`rw`, `simp`, `▸`, `split`, `cases`)
ALL fail because the scrutinee is an opaque application. Use `match` in the proof itself:
```lean
-- After unfolding both function definitions:
unfold foo bar
simp only [id]  -- remove @id wrappers from `change`/`unfold` in tactic definitions
revert e  -- revert the variable so its type enters the goal
exact match inst a b, inst c d with
| .isFalse h, _ => fun _ => (absurd rfl h).elim  -- vacuous
| .isTrue _, .isTrue h => fun _ => (absurd h hne).elim  -- vacuous
| .isTrue _, .isFalse _ => fun _ => rfl  -- both matches reduce to id
```
**Limitation**: This works for arrow-level (homogeneous) equalities but NOT for Sigma-level
equalities where the Sigma TYPE itself contains `Decidable.casesOn`. For Sigma-level round-trips,
define both conversion directions in the SAME file as the type definition, or use `Equiv.ofBijective`.

**Stop after 3 failed approaches** — if `match`-based proof doesn't work, the issue is structural
(needs upstream definition changes), not tactical.

## Issue Description Feasibility Check

**Issue descriptions sometimes contain mathematically incorrect proof strategies.** Before committing to a proof approach described in an issue:

1. **Spend 10 minutes verifying feasibility** — check whether the described approach actually works mathematically
2. **Look for hidden complexity** — "the terms vanish individually" may only be true in special cases
3. **Test with small examples** — if the strategy says "by counting" or "by cancellation", check on a 2×2 or 3×3 case

**Evidence:** The alternating Kostka delta identity issue claimed "all non-rev terms vanish individually" — true only for λ=ν, not in general. The hook quotient identity was estimated at difficulty 2/3 but required 3 fundamentally different approaches before being decomposed into 4 sub-issues.

## Statement Correctness: Common Missing Hypotheses

Multiple sessions were wasted proving statements that turned out to be false due to missing hypotheses. Check for these **before** attempting the proof:

| Missing Hypothesis | Symptom | Example |
|-------------------|---------|---------|
| `[IsAlgClosed k]` | Classification/uniqueness fails | Corollary9_7_3 needed algebraic closure for basic algebra existence |
| `[IsBasicAlgebra A]` | Morita equivalence `B ≅ eAe` fails without basic assumption | MoritaStructural was false without this |
| `[CharZero k]` | Averaging/Reynolds operator arguments fail | Theorem5_18_4 `symGroupImage_faithful` needed char 0 |
| `Module.Finite k V` | Finite-dimensionality needed for rank-nullity | MoritaStructural needed explicit finiteness |
| Orientation constraints | Sink/source confusion in quiver proofs | Prop6_6_6 sink vs source cases |

**Pattern:** If a proof fails at a fundamental level (not a tactic issue but a mathematical impossibility) after 1 serious attempt, **suspect a statement bug**. Check the book's hypotheses carefully before trying more proof strategies.

## Sorry-to-Helper Extraction Pattern (Endgame)

The dominant value-creation pattern in the endgame. Instead of trying to prove a hard sorry directly, extract it into a well-documented helper lemma.

**When to use:** Any sorry that has resisted 2+ attempts, or any theorem with 3+ sorries where the proof structure is unclear.

**Pattern:**
```lean
-- BEFORE: monolithic sorry
theorem main_result : conclusion := by sorry

-- AFTER: structured proof with isolated helper sorries
private lemma helper_1 : intermediate_fact_1 := sorry
private lemma helper_2 : intermediate_fact_2 := sorry

theorem main_result : conclusion := by
  have h1 := helper_1
  have h2 := helper_2
  exact final_combination h1 h2
```

**Why this is high-value:**
1. The main theorem file now has a complete proof term — only helpers are sorry'd
2. Each helper sorry is independently claimable by a future agent
3. The proof structure documents exactly what's needed, reducing onboarding time
4. Partial progress is visible and committable

**Evidence (waves 25-27):**
- Theorem5_25_2: parts 1, 2, 3a proved; sorry isolated in 6 helpers (#1545, #1562)
- Theorem5_26_1: forward direction decomposed into helper lemmas (#1568, #1569)
- Theorem9_2_1: sorry decomposed into targeted sub-goals (#1567)
- Corollary9_7_3: sorry pushed to infrastructure files (#1560)

**Infrastructure absorption pattern:** When helper lemmas are reusable across theorems, extract them into dedicated infrastructure files (e.g., `Infrastructure/BasicAlgebraExistence.lean`, `Infrastructure/MoritaStructural.lean`). This cleanly separates mathematical infrastructure from theorem proofs.

## MonoidAlgebra.lift Pattern for Group Algebra Homomorphisms

When constructing algebra homomorphisms out of `MonoidAlgebra k G`, use `MonoidAlgebra.lift`:

```lean
-- MonoidAlgebra.lift : (G →* A) → (MonoidAlgebra k G →ₐ[k] A)
-- Given a group hom f : G →* A, lift it to an algebra hom
def myAlgHom : MonoidAlgebra k G →ₐ[k] A :=
  MonoidAlgebra.lift k G A f
```

**Key insight:** Don't try to define algebra homs on `MonoidAlgebra` by working with `Finsupp` directly. `MonoidAlgebra.lift` is the universal property and handles all the algebraic structure automatically.

**Companion pattern:** Use `Finsupp.induction_linear` (cases: zero, add, single) instead of `Finsupp.induction` when proving properties of `MonoidAlgebra` elements. The `induction_linear` variant is easier because it doesn't require tracking a `not_mem_support` hypothesis.

## HEq and eqRec Patterns for Dependent Type Transport

When working with dependent types where direct `rw` fails (common in reflection functor proofs):

### Pattern: `eqRec_heq_self` with field projection motive

When you need to show that transporting a value along a proof and then projecting a field gives the same result:

```lean
-- When goal involves: (Eq.rec x proof).field = x.field
-- Use eqRec_heq_self to get HEq between the transported and original value
have : HEq (Eq.rec x proof) x := eqRec_heq_self proof x
-- Then use field projection congruence
exact heq_of_field_projection this
```

### Pattern: `Subsingleton.elim` for Decidable proof irrelevance

When two `Decidable` instances block definitional equality:

```lean
-- When inst₁ inst₂ : Decidable P appear in the goal and prevent reduction
have : inst₁ = inst₂ := Subsingleton.elim _ _
subst this  -- Now only one instance, and dif_pos/dif_neg can reduce
```

This was critical for the `reversedArrow_ne_ne_twice` proof in Prop6_6_6 (#1561).

If the issue's strategy doesn't work after verification, **update the issue comment** with your findings before trying alternative approaches. This saves the next agent from repeating your investigation.

## Module Instance Agreement Pattern

When two `Module R M` instances exist on the same type (e.g., one from `Representation.asModule` and one from `Submodule.module`), direct `rfl` or `congr` fails because the instances are constructed differently.

**Pattern: Prove pointwise agreement via algebra induction**

```lean
-- Two Module (MonoidAlgebra ℂ G) M instances that act identically
-- inst₁ comes from Representation.asModule, inst₂ from Submodule.module
-- They agree on all elements but are not definitionally equal

-- Step 1: Prove the SMul actions agree on generators
have smul_agree : ∀ (g : G) (m : M), @SMul.smul _ _ inst₁.toSMul (single g 1) m
    = @SMul.smul _ _ inst₂.toSMul (single g 1) m := by
  intro g m; simp [...]

-- Step 2: Lift to all MonoidAlgebra elements via induction
have : inst₁ = inst₂ := by
  ext a m
  induction a using MonoidAlgebra.induction_on with
  | single g r => simp [smul_agree g m, ...]
  | zero => simp
  | add x y hx hy => simp [add_smul, hx, hy]
```

**When to use:** Module instance diamonds from `FDRep`/`Representation.asModule` vs. submodule inheritance. This was critical for the FDRep bridge (#1601) — `spechtModuleFDRep_simple` required proving `IsSimpleModule` transfers across instance-incompatible equivalences.

**Companion:** Use `Finsupp.induction_linear` instead of `MonoidAlgebra.induction_on` when working with Finsupp directly (cases: zero, add, single — no `not_mem_support` hypothesis needed).

## FDRep Morphism Extensionality Patterns

FDRep morphisms are `Action.Hom` wrapping `FGModuleCat.Hom` wrapping `ModuleCat.Hom` wrapping `LinearMap`. Proving `f = g` for FDRep morphisms requires decomposing through all layers.

**Pattern 1: Standalone lemma proofs** (f ≫ g = 0, f ≫ g = 𝟙, etc.)
```lean
apply Action.Hom.ext
simp only [Action.comp_hom, Action.zero_hom]  -- or Action.id_hom
apply FGModuleCat.hom_ext
ext c
-- Now at LinearMap level. Use `show` to set the expected form.
show <expected_pointwise_equality>
```

Key lemmas: `Action.comp_hom`, `Action.zero_hom`, `Action.id_hom` (from `Mathlib.CategoryTheory.Action.Basic` and `Limits`).

**Pattern 2: Term-mode** (useful in `exact` or `refine`)
```lean
exact Action.Hom.ext (FGModuleCat.hom_ext (LinearMap.ext (fun x => ...)))
```

**Pattern 3: Inside `where` clause `comm` proofs**
The `comm` field is already at FGModuleCat level. Use:
```lean
comm g := by
  apply FGModuleCat.hom_ext; ext ⟨f, hf⟩
  -- For subtypes: apply Subtype.ext; funext g
  show <expected_pointwise_form>
  ...
```

**WARNING**: With high `maxHeartbeats`, Lean may eagerly reduce definitions, causing `show`/`change` to fail because the normal form differs from the expected mathematical form. If `show` fails, try `sorry` and revisit with lower heartbeats or restructured definitions.

**Evidence:** Discovered during principalSeries_decomp (#1647, #1674) — ~15 build iterations were spent fighting FDRep morphism equality before these patterns were identified.

## PID Structure Theorem Bridge Pattern

When using Mathlib's `Module.torsion_by_prime_power_decomposition` to decompose a module over a PID (e.g., ℂ[X]-modules for nilpotent operators), the output is a `DirectSum` of quotient modules `ℂ[X] ⧸ Ideal.span {X^nᵢ}`. Bridging this to concrete vector subspaces requires careful infrastructure.

**Pattern:**

```lean
-- Step 1: Get the PID decomposition
-- The polynomial ring ℂ[X] is a PID (EuclideanDomain → PrincipalIdealRing)
-- T : V →ₗ[ℂ] V nilpotent gives a ℂ[X]-module structure on V via X ↦ T

-- Step 2: Map quotient modules to kernel spaces
-- Key fact: ℂ[X] ⧸ Ideal.span {X^n} ≅ ker(T^n) / ker(T^(n-1)) as ℂ-vector spaces
-- This requires:
private lemma quotient_poly_dim (n : ℕ) :
    Module.finrank ℂ (Polynomial ℂ ⧸ Ideal.span {X ^ n}) = n := sorry

-- Step 3: Track dimensions through the decomposition
-- dim(ker T^k on ℂ[X]/(X^n)) = min(k, n)
-- This determines the Jordan block structure
```

**Key difficulties:**
- The `Module.torsion_by_prime_power_decomposition` API produces existential types (primes, exponents) that need careful handling with `Exists.choose`
- ℂ[X]-module structure on V must be constructed explicitly from the linear map T
- Dimension tracking through quotients requires `Module.finrank` lemmas for polynomial quotient rings

**Evidence:** Problem6_9_1 Case 2b (#1617) — proved 4/5 nilpotent decomp cases using this bridge. The remaining case (2b-ii) is blocked on the kernel dimension computation.

## Type Class Shadowing for Instance Pollution

When a typeclass instance leaks through from an outer scope and interferes with proof goals, use `letI` to shadow it with the correct instance.

**Pattern:**
```lean
-- Problem: `inst✝ : Quiver Q` in context is wrong/opaque, preventing reduction
-- Solution: Shadow it with the concrete instance you want
letI : Quiver Q := concreteQuiverInstance
-- Now tactics see the concrete instance, not the opaque one
```

**When to use:** Proposition6_6_6 hdim proof (#1598) needed this to shadow a `Quiver` instance that was preventing `simp` from reducing. Also useful when `inferInstance` finds the wrong instance in the presence of multiple candidates.

**Caution:** Only shadow when you're sure the shadowed instance agrees with the one you're replacing — otherwise proofs may become inconsistent.

## Inductive Construction on Finite Sets (Finset.strongInduction)

For existence proofs that build a structure incrementally on a finite set (e.g., constructing orderings, colorings, assignments), use `Finset.strongInduction` or equivalent well-founded recursion on `Finset.card`.

**Pattern:**
```lean
-- Construct an admissible ordering of vertices by repeatedly finding local sinks
-- At each step, remove a local sink from the remaining set and recurse

theorem exists_ordering : ∃ (l : List V), l.Nodup ∧ l.toFinset = Finset.univ ∧ P l := by
  -- Use strong induction on |remaining vertices|
  suffices ∀ (S : Finset V), ∃ (l : List V), l.Nodup ∧ l.toFinset = S ∧ P' S l from
    this Finset.univ
  intro S
  induction S using Finset.strongInduction with
  | ind S ih =>
    -- Find an element to remove (e.g., a local sink)
    obtain ⟨v, hv, hprop⟩ := exists_special_element S hS
    -- Recurse on S \ {v}
    obtain ⟨l, hl⟩ := ih (S.erase v) (Finset.erase_ssubset hv)
    exact ⟨v :: l, ...⟩
```

**Evidence:** admissibleOrdering_exists (#1613) — constructed admissible orderings for Dynkin quivers by iteratively removing local sinks, proved via `Finset.strongInduction`. Helper lemmas for sink existence were proved separately using a counting argument on forward/backward edge pairs.

**Key helper pattern:** When the "special element" existence requires a counting/pigeonhole argument, prove it as a separate lemma first. The inductive construction is cleaner when the "find next element" step is a black box.

## Decidable.casesOn Workaround Patterns (Quiver Reflection Functors)

The `reflectionFunctorPlus`/`Minus` definitions use `Decidable.casesOn` via `if h : v = i then ... else ...`. Outside these definitions, Lean cannot reduce through `Decidable.rec`, causing type mismatches. Three workaround variants exist, discovered across PRs #1723, #1735, #1739, #1760:

### Variant A: Revert-Unfold-Rewrite-Intro (most common)

Used 6+ times across Proposition6_6_7 and Proposition6_6_6. The canonical pattern for ne/ne cases:

```lean
-- Fix the decidable instances to their known values
have h_da : DecidableEq Q a' i = .isFalse ha' := by
  cases DecidableEq Q a' i with | isTrue h => exact absurd h ha' | isFalse _ => rfl
have h_db : DecidableEq Q b' i = .isFalse hb' := by
  cases DecidableEq Q b' i with | isTrue h => exact absurd h hb' | isFalse _ => rfl
-- Revert ALL dependent variables
revert hw w e' hsubrep Sb Sa
-- Unfold the definitions containing Decidable.casesOn
unfold reflFunctorMinus_equivAt_ne reflectionFunctorMinus reversedAtVertex ReversedAtVertexHom
simp only []
-- Rewrite with the fixed decidable values
rw [h_da, h_db]
simp only []
-- Re-introduce the variables
intro Sa Sb hsubrep e' w hw
```

### Variant B: Refine-Match (for definitions)

Preferred when defining equivs at specific vertices:

```lean
refine match inst_dec i i with
| .isFalse h => absurd rfl h
| .isTrue _ => ?_
```

Avoids `Eq.mpr` wrappers from `rw` that block downstream computation.

### Variant C: Two-variable fix (for naturality proofs)

When both equality and inequality branches need fixing simultaneously:

```lean
have h_ii : inst_dec i i = .isTrue rfl := by match ...
have h_bi : inst_dec b i = .isFalse hb := by match ...
```

### Key Insight: Avoid `= 0` with Decidable dependency

When `0 : F(rho).obj i` has `Decidable.rec` in its type, prove `f x = mkQ(0)` (where `0 : DirectSum` has no Decidable dependency) then use `map_zero`.

## Instance Construction via `show ... from inferInstance`

When a definition is a type alias (e.g., `AlgIrrepGL` wrapping `SchurModuleSubmodule`), derive instances by showing they follow from the underlying type:

```lean
noncomputable instance AlgIrrepGL.addCommGroup : AddCommGroup (AlgIrrepGL n lam k) :=
  show AddCommGroup (SchurModuleSubmodule k n lam.toNatWeight) from inferInstance
```

Works for `AddCommGroup`, `Module k`, `Module.Finite k`. Discovered in PR #1752. More reliable than `@inferInstance` or manual instance construction.

## Tabloid and Young Tableau Infrastructure Patterns

### Quotient type via Setoid (PR #1754)

```lean
-- TabloidSetoid: two fillings are equivalent if row assignments agree up to permutation
instance : Setoid (Filling n la) where
  r f g := ∃ σ ∈ RowSubgroup n la, σ • f = g
  iseqv := ⟨fun _ => ⟨1, one_mem _, one_smul _ _⟩,
            fun ⟨σ, h, e⟩ => ⟨σ⁻¹, inv_mem h, by rw [← e]; group⟩,
            fun ⟨σ, h1, e1⟩ ⟨τ, h2, e2⟩ => ⟨τ * σ, mul_mem h2 h1, by rw [← e2, ← e1]; group⟩⟩
```

### Fintype for quotient types

```lean
noncomputable instance : Fintype (Tabloid n la) := by
  haveI : DecidableRel (TabloidSetoid n la).r := Classical.decRel _
  unfold Tabloid
  exact Quotient.fintype (TabloidSetoid n la)
```

Must provide `DecidableRel` via `Classical.decRel` before `Quotient.fintype` works.

### False theorem discovery pattern (PRs #1769, #1771)

`RelColumnSubgroup_ne_tabloid` was initially stated with wrong conjugation direction (`σ_T Q_λ σ_T⁻¹` vs `σ_T⁻¹ Q_λ σ_T`). A concrete counterexample for partition (2,2) was found. **Always verify conjugation/action direction with a small example before proving.**

## Orbit-Stabilizer via Burnside's Lemma (PR #1755)

For counting arguments involving group orbits on combinatorial structures:

1. `FiberPerm h ≅ stabilizer h` via `Equiv.subtypeEquiv`
2. Sigma swap `(Σ h, stab h) ≅ (Σ σ, fixedBy σ)` via `Equiv.subtypeProdEquivSigmaSubtype` + `Equiv.prodComm`
3. Burnside: `MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group`
4. Orbit classification: `Equiv.ofBijective` with `Quotient.lift` on fiber sizes

Use `Equiv.ofFiberEquiv` to show structures with the same fiber sizes are in the same orbit — leverages `Fintype.equivOfCardEq` per fiber.

## Simp Lemma Instability Across Lean/Mathlib Versions

`simp` arguments that work locally may stop working after Lean/Mathlib version bumps (PR #1767 was entirely a CI fix for this). Common culprits:
- `LinearEquiv.refl_apply`, `LinearEquiv.coe_toLinearMap` — may be removed from simp set
- `Submodule.coe_mk` — behavior changes across versions

**Mitigation:** After CI failure on `simp` calls, try removing specific simp lemmas rather than adding new ones. Use `simp?` to find the current minimal simp set.

## Known Dead-Ends (Don't Waste Context Windows)

These are proof approaches that multiple agents have attempted and failed. Don't retry them without new Mathlib infrastructure.

### ExteriorAlgebra / PiTensorProduct Coercion Gap

**Problem:** Proving `∧^n V ≅ (V⊗ⁿ)^{Alt}` (the alternating subspace of the tensor power is the exterior power) requires bridging two incompatible Mathlib constructions:
- `exteriorPower n V` is a `Submodule` of `ExteriorAlgebra V` (built on `CliffordAlgebra`)
- The alternating subspace lives in `PiTensorProduct` (or `TensorProduct`)

**What fails:**
- `exteriorPower.linearMap_ext` creates `compAlternatingMap` goals with `↑` coercions that `simp` cannot resolve
- `Fintype.sum_equiv` gets type mismatches when goals are wrapped in `compMultilinearMap`
- `congr 1` strips one coercion layer but leaves incompatible goal forms

**Status:** 3+ agents have attempted this (Example 5.19.3 exterior part). All failed. **Sorry and move on.** This requires new Mathlib bridging infrastructure between `ExteriorAlgebra` and `PiTensorProduct`.

### Dependent Type Issues with `if`-branching `obj` Fields

**Problem:** When a `QuiverRepresentation`-like structure has `obj v := if v = i then T₁ else T₂`, filling `Module` instance fields fails because the `AddCommMonoid` instance becomes opaque after filling.

**Status:** Documented in detail above (Type-Level If/Else Diamond Issue). The workaround is to sorry the `instModule` field. Don't attempt to solve the diamond — it requires a structural refactor.

### Decidable.casesOn Opacity in reflectionFunctorPlus Proofs

**Problem:** `reflectionFunctorPlus` (Definition 6.6.3) defines vertex objects and maps using `Decidable.casesOn` on the `DecidableEq` instance. Any proof that needs to relate the F⁺ maps to the underlying representation maps requires reducing this `casesOn`, but:
- `rw`/`simp` with `inst a i = .isFalse ha` fails: "motive is not type correct"
- `generalize` on `inst a i` fails: "result is not type correct"
- Term-mode `match` on `inst a i` resolves the outer match but does NOT substitute `inst a i` in the inner goal (non-dependent motive inferred)
- `exact rfl` fails: types are not definitionally equal across the casesOn boundary

**Affected items:** Prop 6.6.7 (all sink-case sorry's), Prop 6.6.6 (equivAt lemmas), any proof composing reflection functor maps.

**What to do — depends on which vertices are involved:**
- **Both vertices ≠ i (ne_ne case):** SOLVABLE. Use `.trans` composition of equivAt_ne equivs instead of monolithic equivAt_ne_sink/source. Then apply API lemmas (`reflFunctorMinus_mapLinear_ne_ne`, `reflFunctorPlus_mapLinear_ne_ne`, `reversedArrow_ne_ne_twice`) via `rw`. See Proposition6_6_6_sink ne_ne case for the working pattern.
- **One vertex = i (ne_eq or eq_ne case):** BLOCKED. The `(reflectionFunctor...).obj i` type is opaque — API lemma statements can't even typecheck because Lean can't see through `Decidable.casesOn` to recognize it as a quotient/kernel. **Sorry immediately.** The fix requires refactoring `reflectionFunctorPlus`/`Minus` to avoid `Decidable.casesOn`.

**Workaround for API lemma application:** When proofs have local `let instR := reversedAtVertex Q i` bindings, Lean's type class synthesis finds `instR` for `[Quiver Q]` instead of the registered `inst`, causing "synthesized type class instance is not definitionally equal" errors when applying API lemmas. **Fix**: Extract the computation as a separate top-level theorem (outside the proof) where `instR` doesn't exist as a local binding. Use explicit `@`-prefixed terms with `Etingof.reversedAtVertex Q _ inst i` to control instance resolution. See `Φ_comp_source_eq_zero` in Proposition6_6_6.lean and `reflFunctorPlus_mapLinear_eq_ne` in Definition6_6_3.lean for examples of this pattern.

## Common Failure Modes

### Explicit Bijection Construction (Counting Proofs)

When proving cardinality results or counting arguments, prefer explicit bijection constructions over abstract reasoning:

1. Define the forward map explicitly
2. Define the inverse map explicitly
3. Prove round-trip properties

This pattern proved GL2 conjugacy class cardinalities (disc=0 split into g01=0 and g01≠0 cases) and the `invColorEquivMC` equivalence (σ-invariant colorings ↔ monochromatic colorings). It works well because Lean's `Equiv` API is rich and `simp` handles most round-trip goals.

**Avoid `Finset.univ.image f` + `Finset.card_image_of_injective` for cardinality proofs.**
This approach requires `DecidableEq` on the codomain, causes elaboration issues with
`fin_cases` (producing unreduced `σ ^ ↑((fun i ↦ i) ⟨0, ⋯⟩)` terms), and anonymous
constructor matching in `Finset.mem_image` existentials is fragile. Instead use
`Fintype.card_congr` with an explicit `Equiv`, or `Finset.card_union_of_disjoint`.

### Well-Founded Recursion on Natural Measures

For recursive definitions where termination isn't structural:

1. Identify a natural `ℕ`-valued measure that strictly decreases
2. Prove the decrease lemmas as separate helper lemmas first
3. Define the function using `WellFoundedRelation` or `termination_by`

This pattern defined the hook walk weight function with termination via strictly decreasing hook length. Prove the decrease lemmas before attempting the definition — interleaving them causes elaboration issues.

### Fin.cons + Equiv.ofBijective for Explicit Equivalences

When constructing an equivalence between a finite type and `Fin n` (e.g., for counting conjugacy classes, enumerating roots):

1. Build the forward map inductively using `Fin.cons` to handle each case
2. Prove injectivity by case analysis on each pair
3. Prove surjectivity by showing the image covers all elements
4. Combine via `Equiv.ofBijective`

```lean
-- Example: equivalence between conjugacy class representatives and Fin 4
def classEquiv : Fin 4 → ConjClass G :=
  Fin.cons scalar (Fin.cons splitSS (Fin.cons parabolic (Fin.cons elliptic Fin.elim0)))

theorem classEquiv_bijective : Function.Bijective classEquiv := by
  refine ⟨fun i j h => ?_, fun c => ?_⟩
  · fin_cases i <;> fin_cases j <;> simp_all [classEquiv]
  · obtain ⟨g, rfl⟩ := c.exists_rep
    -- case analysis on g to find preimage
    sorry

noncomputable def classFinEquiv : ConjClass G ≃ Fin 4 :=
  (Equiv.ofBijective classEquiv classEquiv_bijective).symm
```

This pattern proved GL₂(𝔽_q) conjugacy class cardinalities and `SimpleGraph.Connected.induce_compl_singleton_of_degree_eq_one`. It works well because `fin_cases` handles all pairs for injectivity automatically.

### Bridge to Mathlib's Native Abstractions

When the project uses a custom representation (e.g., list-based paths, adjacency matrices) but Mathlib has richer API for a different representation (e.g., `SimpleGraph`):

1. Build a conversion function to Mathlib's type
2. Prove key properties transfer across the conversion
3. Use Mathlib's existing API on the converted representation

This proved `dynkin_edge_count` by converting adjacency matrices to `SimpleGraph` and leveraging Mathlib's connected graph theory.

## Issue Feasibility Triage (Before Committing to Work)

Before spending a full session on an issue, spend 10-15 minutes on feasibility triage:

### Step 1: Check sorry count and location
```bash
grep -n "sorry" <target-file>.lean | head -20
```
Count the sorries. If the issue claims "1 sorry remains" but the file has 5, the issue is stale.

### Step 2: Identify the mathematical core
Read the blob (`blobs/<Chapter>/<Item>.md`) and identify what mathematical result is needed. Ask:
- Is this a computation (finite cases, arithmetic)? → Likely Tier 1
- Does it need a named theorem not in Mathlib (Krull-Schmidt, Schur-Weyl)? → Likely Tier 3
- Is it standard algebra/linear algebra with Mathlib API? → Likely Tier 1-2

### Step 3: Check for known dead-ends
Search the "Known Dead-Ends" section above. If the proof touches `Decidable.casesOn` in Ch6, `ExteriorAlgebra ↔ PiTensorProduct`, or `SchurModule`, it's blocked.

### Step 4: Verify infrastructure exists
For each dependency the proof needs:
```bash
grep -rn "theorem <dep_name>\|def <dep_name>" EtingofRepresentationTheory/
```
If a dependency is sorry'd, that's OK (sorry acts as axiom). But if a dependency doesn't exist at all, you need to build it — factor that into your time estimate.

### Step 5: Skip or decompose if needed
- If blocked → `coordination skip <N> "reason"` immediately
- If too large → decompose into sub-issues (see agent-worker-flow Step 4b)
- If feasible → proceed with confidence

**Common triage mistakes:**
- Spending 2 hours before realizing a theorem needs Krull-Schmidt
- Not checking if the issue's sorry count matches reality (other agents may have merged changes)
- Assuming a "1 sorry" issue is easy — the sorry may hide a 200-line proof

## Common Failure Modes

From Phase 2 review patterns and Stage 3.2 proof experience (110+ merged PRs through wave 20):

1. **Wrong Mathlib declaration name.** Always `#check` the declaration before using it.
2. **Fabricated references.** If `.refs.md` cites a Mathlib declaration, verify it exists.
3. **Scope mismatch.** The book may state a theorem for a specific case (e.g., finite-dimensional) but Mathlib has it more generally. Use the general version.
4. **Missing instances.** Representation theory needs many type class instances. If Lean can't find one, check if Mathlib has it under a different name or if you need to `open` a namespace.
5. **Hidden hypotheses in book statements.** The book may omit hypotheses that are implicit in context (e.g., algebraic closure, field characteristic). Discovered examples: Theorem 3.10.2 needed `[IsAlgClosed k]`, Example 8.1.7 needed `Field k` not `CommRing R`. When a proof attempt fails at a fundamental level, check whether the statement needs additional hypotheses.
6. **Status tracking lag.** After proving a theorem, update `items.json` immediately in the same commit. Audits have found items marked `scaffolded` that were actually `sorry_free`. Always update proactively — manual tracking in `progress/items.json` is the only status tracking mechanism.
7. **FDRep abstraction fighting.** If your proof requires distributing `.hom.hom` over sums or otherwise unwrapping 3+ layers of categorical abstraction, you're fighting the wrong abstraction. See the FDRep Categorical Plumbing patterns above for alternatives.
8. **Universe level mismatches.** Representation theory proofs sometimes need explicit universe annotations (`.{v}`) especially when working with Jacobson radical or maximal ideal APIs. If type unification fails mysteriously, try adding explicit universe parameters.
9. **Sinking entire context windows on known dead-ends.** Before starting a proof, check the "Known Dead-Ends" section above. If the proof requires bridging `ExteriorAlgebra` ↔ `PiTensorProduct` or resolving the `if`-branching diamond, sorry it immediately and move on. Multiple agents have confirmed these are blocked on missing infrastructure.
10. **Opaque placeholder accumulation.** Defining key structures as `sorry : FDRep k G` (e.g., `SchurModule k N lam`) creates downstream dependency chains that block entire proof clusters. When you must sorry a definition, prefer making the carrier type concrete and sorry-ing only specific operations/instances (see "Never sorry a Type" above). Each opaque placeholder blocks all items that depend on it.
11. **Convention mismatch between book and Mathlib.** Sign conventions, ordering conventions, and normalization conventions can silently make statements unprovable. See "Verify Statement Correctness Before Proving" section above. The vandermondePoly sign mismatch wasted multiple agent sessions before being discovered via a concrete n=2 counterexample.
12. **Issue description proof strategies are sometimes wrong.** The proof approach described in an issue body may be mathematically incorrect or only work for special cases. Always spend 10 minutes verifying the described approach before committing to it. See "Issue Description Feasibility Check" section above.
13. **Namespace dot-notation mismatch.** Most Lean files in this project wrap code in `namespace Etingof` (and `noncomputable section`). If you define `def YoungDiagram.foo` inside `namespace Etingof`, the full name is `Etingof.YoungDiagram.foo` — dot notation `μ.foo` (where `μ : YoungDiagram`) will NOT find it. **Symptoms:** The definition silently fails to register (no error reported) and downstream references get "Invalid field" errors. **Fix:** Close the namespace before defining `YoungDiagram.*` declarations that need dot-notation access, then reopen it. Remember to also close/reopen any `noncomputable section`.


### Tactic Gotchas with `rw`, `omega`, and `nsmul`

1. **`rw [← Finset.sum_filter]` fails on lambda matching.** `rw` does strict term matching and often can't unify `fun x => if x ∈ S then f x else 0` with `Finset.sum_filter`'s pattern. Use `simp only [← Finset.sum_filter]` instead — `simp` is more flexible with lambda matching.

2. **`omega` can't see through `Fin` equalities.** After `Fin.val_eq_of_eq`, omega may not recognize the resulting Nat equality. Fix: use `simp only [Fin.mk.injEq] at h` to normalize `⟨a, _⟩ = ⟨b, _⟩` into `a = b` before calling `omega`.

3. **`omega` can't handle `min`/`if` from `List.length_take`.** `List.length_take` gives `(l.take n).length = min n l.length`, and `min` unfolds to `if n ≤ l.length then n else l.length`. omega can't simplify `if`. Fix: extract the bound you need with `lt_of_lt_of_le h (min_le_left a b)` or `min_le_right`.

4. **`nsmul_eq_mul` produces `↑n * x` not `n * x`.** Converting `n • x` (where `n : ℕ`, `x : ℤ`) via `nsmul_eq_mul` gives `↑n * x` with a Nat cast. `linarith` can't equate `↑2 * x` with `(2 : ℤ) * x`. Add `push_cast` after `nsmul_eq_mul` to normalize.

5. **`linarith` requires a linear order — use `linear_combination` over ℂ.** `linarith` only works on linearly ordered types (ℝ, ℤ, ℕ, etc.). For goals over ℂ like `a + b = 0 → a = -b`, use `linear_combination h` instead. The `linear_combination` tactic works over any commutative ring.

## Breadth-vs-Depth Phase Awareness

The project alternates between **breadth phases** (statement formalization) and **depth phases** (proof completion). Recognizing which phase you're in prevents misallocating effort.

### Breadth Phase (Statement Formalization)
- **Trigger:** Proof backlog < 30 items, or agents are running out of proof targets
- **Focus:** Formalize new theorem/definition statements across multiple chapters
- **Expected metrics:** Low items/PR ratio, sorry count may increase (new sorry'd statements added)
- **This is not a failure mode** — it's strategic investment in the proof pipeline

### Depth Phase (Proof Completion)
- **Trigger:** Proof backlog > 40 items, or enough targets exist across 3+ chapters
- **Focus:** Prove sorry'd items, prioritizing chain completion and chapter closures
- **Expected metrics:** Higher items/PR ratio, sorry count declining
- **Planners should create 80%+ proof issues** during this phase

### Current Status (as of Wave 40, 2026-03-28)
The project has 29 sorries across 20 files (down from 66 at wave 28). Sorry-free rate: 249/271 files (91.9%). This is deep in a **depth phase** — all remaining work is proof completion on hard items. Statement formalization is complete.

**Chapter status (Wave 40):** Ch3, Ch4, Ch7, Ch8 are 100% sorry-free. Ch2 has 1 sorry (Theorem2_1_2). Ch5 has 14 sorries across 7 files. Ch6 has 9 sorries across 7 files. Ch9 has 3 sorries across 3 files. Infrastructure has 2 sorries across 1 file.

**Major milestones since wave 33:**
- **All definition-level sorries resolved** (wave 37) — every mathematical object is constructed
- **SchurModule constructed** (PR #1740) — the mega-blocker is resolved
- **Shapiro's lemma proved from scratch** (#1870, #1880) — was missing from Mathlib, built locally
- **Hilbert syzygy theorem infrastructure** (#1897) — extendScalars preserves projective dimension, Koszul SES setup
- **Peter-Weyl decomposition** (#1896) — directSum_rank_ge_aleph0 via infinite linear independence
- **Morita idempotent fullness** (#1881) — exists_full_idempotent_basic_corner fullness step proved
- **Weyl character trace formula** (#1883) — decomposed into sub-lemmas
- **False polytabloid expansion identified** (#1888) — tabloid expansion convention was wrong
- **Proposition6_6_7 sorry-free** (#1800) — Decidable.casesOn workarounds succeeded
- **Determinant identity** (#1845) — det_clearedDenomMatrix_eq proved (V_x * V_y)

**Major blocker clusters (updated wave 40):**
1. **Gabriel's theorem chain** (~5+ files, 11+ downstream sorries): Prop6_6_6_source (1 sorry) is the keystone — unblocks Corollary6_8_3, 6_8_4, Problem6_1_5_theorem, Theorem_Dynkin_classification
2. **Character formula chain** (5 sorries): Theorem5_22_1 (3) → Theorem5_23_2 (1) + Proposition5_22_2 (1)
3. **Mackey machine / Clifford theory** (3 sorries): Theorem5_27_1 — needs ~500 lines new theory
4. **Morita/Basic algebra** (3 sorries): Non-commutative tensor products + circularity in basic_morita_algEquiv
5. **Polytabloid basis** (6 sorries across 2 files): right-multiplication dominance needed (left proved, right fundamentally different)

**Velocity trend:** 66 → 43 → 36 → 27 → 29 sorries over waves 28-40. Rate decelerating as remaining items are increasingly hard. Sorry count increased from 27 to 29 due to decomposition adding structured sub-goals (net positive: better scoped work items).

**Key velocity insight:** Difficulty 3/3 items have a ~30% single-session success rate — agents should budget accordingly and commit partial progress early. **Agents that don't commit intermediate work produce zero value** — stale claims continue to be a recurring problem.

## `simp` Doesn't See Through Local `let` Bindings

When `simp` fails to make progress on a goal involving a term bound by a local `let`:

**The problem:** `simp` and `simp_rw` do not beta-reduce through local `let` bindings. If you have:
```lean
let f := DirectSum.component R i
-- Goal: ... f (Finset.sum ...) ...
simp [DirectSum.component.of]  -- makes no progress!
```

**Workaround 1: Use `rw` before `simp`**
```lean
rw [DFinsupp.finset_sum_apply]  -- expand the sum application first
simp_rw [show f x = ... from rfl]  -- then rewrite with explicit `show`
```

**Workaround 2: Use `change` to eliminate the `let`**
```lean
change <explicit_form_without_let>
simp [...]  -- now simp can see the structure
```

**Workaround 3: Use `dsimp only` to reduce `let` bindings**
```lean
dsimp only []  -- reduces let-bindings in the goal
simp [...]  -- now works
```

**Evidence:** Discovered independently in Proposition6_6_7 (#1800) and Problem6_9_1 (#1807). The `DFinsupp.finset_sum_apply` + `show` pattern was the successful resolution in both cases.

## Decidable Instance Mismatch Patterns (Comprehensive)

Decidable instance mismatches are a recurring friction point across the project. They arise when `classical` decidability and concrete `DecidableEq`/`DecidablePred` instances coexist, creating terms that look identical but are not definitionally equal.

### Symptom Recognition

- `rfl` fails on two expressions that are "obviously equal"
- `rw` fails with "motive is not type correct" on a Decidable-dependent term
- Two `Finset.univ` expressions have different `Fintype` instances
- `if`/`dite` expressions don't reduce under `simp` because the `Decidable` instance is opaque

### Strategy 1: `open scoped Classical` (Prevention)

Add at the section level, **before** any definitions that use `haveI : DecidablePred ... := Classical.decPred _`:
```lean
open scoped Classical
```
This ensures all `DecidablePred` instances come from the same source. **Best approach** — prevents the problem rather than patching it.

### Strategy 2: `convert rfl using N` (Patching)

When two sums over `Finset.univ` differ only in their `Fintype` instance:
```lean
convert rfl using 2  -- handles via Subsingleton (Fintype α)
```

### Strategy 3: `trans` + separate goals

When `rw` fails due to a dependent Decidable in the motive, split into two steps:
```lean
-- Instead of: rw [h]  -- fails with "motive is not type correct"
calc lhs = middle := by <prove_without_h>
       _ = rhs := by <prove_using_h>
```

### Strategy 4: `Subsingleton.elim` for proof irrelevance

When two `Decidable` instances block definitional equality:
```lean
have : inst₁ = inst₂ := Subsingleton.elim _ _
subst this  -- now only one instance exists
```

### Strategy 5: Avoid `set` for local definitions

The `set x := expr` tactic introduces a local definition that can capture the "wrong" Decidable instance. Prefer `have` or `let` with explicit type annotations instead.

**Evidence:** Decidable mismatches appeared in Theorem5_27_1 (sessions #5, #15), Proposition6_6_7 (#1800), and Proposition6_6_6_source (#1821). Strategy 1 (`open scoped Classical`) is the most reliable prevention.

## Universe Pinning Strategy

When universe level errors or mismatches arise (common in representation theory where multiple universe levels interact):

**Pattern:** Change from `Type*` to explicit `universe u v` declarations:
```lean
universe u v

theorem my_theorem
    (k : Type u) [Field k]
    (V : Type v) [AddCommGroup V] [Module k V] :
    ... := by
  ...
```

**When to use:**
- `universe polymorphism` errors
- Sigma types with universe-level mismatches
- `MoritaEquivalent`, `FDRep`, or other constructions that require universe alignment
- `SchurModule`, `AlgIrrepGL`, or similar constructions that mix multiple universe-polymorphic types

**Evidence:** Universe pinning resolved issues in Theorem5_18_4 (SchurModule universe annotations), IsFiniteTypeQuiver (pinned to `Type` to avoid universe mismatch), and BasicAlgebraExistence (explicit `Type u` throughout).

## Section Variable Auto-Inclusion Gotcha

Lean 4 section variables declared with `variable (h : P)` are only auto-included
in declarations where they appear **syntactically** in the type or proof body.
Dot notation like `h.eq` may not trigger auto-inclusion — Lean's variable scanner
doesn't always resolve dot notation to find the underlying variable.

**Symptom**: "Unknown identifier `h.eq`" or "Unknown identifier `h`" inside a
proof in a `section` block, even though `h` is declared as a `variable`.

**Fix**: Add `include h` after the `variable` declaration to force inclusion in
all subsequent declarations in the section:
```lean
section Foo
variable {e : A} (he : IsIdempotentElem e)
include he  -- forces he into all declarations in this section

lemma bar ... := by
  ... he.eq ...  -- works now
end Foo
```

**Alternative**: Explicitly add the parameter to each declaration (the pattern
used in this project's `cornerSubmodule_left_mul` etc.).

## When to Decompose vs. Attempt Directly

**Decompose immediately** when:
- The sorry has resisted 2+ attempts by prior agents (check issue comments)
- The proof has 3+ conceptually independent sub-goals
- You estimate the proof at 100+ lines of tactics
- The file is 500+ lines and you need to understand most of it
- You're past the midpoint of your context window

**Attempt directly** when:
- The sorry is in a Tier 1 (achievable) category
- A clear tactic sequence is visible after reading the book's proof
- The file is short (<200 lines) and self-contained
- No prior agent has attempted this sorry

**The decomposition output pattern:**
```lean
-- BEFORE: monolithic sorry
theorem hard_theorem : conclusion := by sorry

-- AFTER: structured proof with isolated helper sorries
private lemma step1 : ... := sorry  -- clear, independently claimable
private lemma step2 : ... := sorry  -- clear, independently claimable

theorem hard_theorem : conclusion := by
  have h1 := step1
  have h2 := step2
  exact final_combination h1 h2
```

**Value assessment:** A session that decomposes a monolithic sorry into 5 sub-goals and proves 3 of them is MORE valuable than a session that attempts the monolithic sorry directly and fails. Decomposition creates independently claimable work items and documents the proof strategy.

**Evidence:** Problem6_9_1 was decomposed from 1 sorry into 8 sub-goals, 6 proved (#1807). Theorem5_22_1 was decomposed into coefficient extraction + core identity (#1806). BasicAlgebraExistence was split into 2 targeted helpers (#1803). All three patterns created visible, committable progress.
