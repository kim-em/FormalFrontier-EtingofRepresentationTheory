---
name: lean-formalization
description: Use when working on Phase 3 formalization — translating mathematical text into Lean 4 statements and proofs, filling sorry placeholders, or escalating to Aristotle.
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

**When Mathlib doesn't have it:** Check the `.refs.md` file for the item. If coverage is "gap", you need to build the definition from scratch. State it clearly, add a comment `-- not in Mathlib as of v4.28`, and use sorry for the proof.

## Aristotle Escalation

### When to Escalate

Escalate after **2-3 serious attempts** (not 2-3 minor variations of the same approach). A "serious attempt" means:
- You identified the mathematical strategy
- You got partway through (some subgoals resolved)
- You hit a specific blocker (missing lemma, type mismatch, tactic timeout)

### How to Escalate

1. **Prepare file.** Copy the item's `.lean` file. Keep exactly one `sorry` (the target). Change all other `sorry` to `admit`.
2. **Gather context.** Collect sorry-free local `.lean` files from the import chain. Skip Mathlib imports.
3. **Submit.**
   ```bash
   aristotle prove-from-file item_pending.lean --no-wait \
     --no-auto-add-imports --context-files dep1.lean dep2.lean
   ```
4. **Record in items.json.** Set status to `sent_to_aristotle` with the project ID.
5. **Delete temp file.** Never commit files with `admit`.

**CRITICAL: `--context-files` is mandatory for this project.** Every Lean file imports
`EtingofRepresentationTheory.*` modules, which Aristotle cannot resolve on its own.
Without `--context-files`, Aristotle returns "unknown module prefix" and produces no proof.
Step 2 is NOT optional — if no sorry-free context files exist yet, you must still provide
the imported files (with their sorries changed to `admit`) as context.

### After Aristotle Returns

- **Success:** Verify with `lake env lean`, copy proof, update status to `sorry_free`.
- **False statement:** Mark `attention_needed`, post GitHub issue with counterexample.
- **Failure/timeout:** Mark `attention_needed`, move on to next item.

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

## Issue Sizing for Formalization

Based on Phase 2 experience with issue sizing:

- **Definitions:** 1-3 per issue (fast, low risk)
- **Easy theorems** (direct application of Mathlib): 2-5 per issue
- **Medium theorems** (multi-step proofs): 1-2 per issue
- **Hard theorems** (may need Aristotle): 1 per issue
- **Never mix difficulty levels** in one issue — a hard theorem blocks the easy ones

## Proven Proof Strategies

Patterns that have succeeded in this project, derived from 50+ merged proof PRs.

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

## When Aristotle Is Unavailable

If `aristotle` is not on PATH or fails to connect, don't waste time debugging it. Instead:

1. Attempt the proof yourself (2-3 serious tries)
2. If stuck, `sorry` the proof with a comment: `-- Escalate to Aristotle when available`
3. Set items.json status to `attention_needed` (not `sent_to_aristotle`)
4. Move on to the next item — don't block your entire session on one proof

Aristotle availability varies by machine. Recording the need for escalation ensures a future session on a properly configured machine can pick it up.

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
3. Escalate to Aristotle if available — combinatorial lemmas are good Aristotle candidates
4. If Aristotle unavailable, file an issue with status `attention_needed`

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
4. **Work on the helper separately** (or escalate to Aristotle)

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
- **PR 2**: Prove helper lemmas (or receive Aristotle results)
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

## Common Failure Modes

From Phase 2 review patterns and Stage 3.2 proof experience (50+ merged PRs):

1. **Wrong Mathlib declaration name.** Always `#check` the declaration before using it.
2. **Fabricated references.** If `.refs.md` cites a Mathlib declaration, verify it exists.
3. **Scope mismatch.** The book may state a theorem for a specific case (e.g., finite-dimensional) but Mathlib has it more generally. Use the general version.
4. **Missing instances.** Representation theory needs many type class instances. If Lean can't find one, check if Mathlib has it under a different name or if you need to `open` a namespace.
5. **Hidden hypotheses in book statements.** The book may omit hypotheses that are implicit in context (e.g., algebraic closure, field characteristic). Discovered examples: Theorem 3.10.2 needed `[IsAlgClosed k]`, Example 8.1.7 needed `Field k` not `CommRing R`. When a proof attempt fails at a fundamental level, check whether the statement needs additional hypotheses.
6. **Status tracking lag.** After proving a theorem, update `items.json` immediately in the same commit. Audits have found items marked `scaffolded` that were actually `sorry_free`. Automated sorry detection (via LeanArchitect) is more reliable than manual tracking, but agents should still update proactively.
7. **FDRep abstraction fighting.** If your proof requires distributing `.hom.hom` over sums or otherwise unwrapping 3+ layers of categorical abstraction, you're fighting the wrong abstraction. See the FDRep Categorical Plumbing patterns above for alternatives.
8. **Universe level mismatches.** Representation theory proofs sometimes need explicit universe annotations (`.{v}`) especially when working with Jacobson radical or maximal ideal APIs. If type unification fails mysteriously, try adding explicit universe parameters.
