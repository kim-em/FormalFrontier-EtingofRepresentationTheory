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

Patterns that have succeeded in this project, derived from 30+ merged proof PRs.

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

| Gap | What Exists | What's Missing | Blocks |
|-----|------------|----------------|--------|
| Column orthogonality | `FDRep.char_orthonormal` (row) | `∑_V χ_V(g) · χ_V(h⁻¹) = \|C_G(g)\| · δ` | Thm 5.4.6, Burnside |
| Regular rep decomposition | `FDRep`, `Simple` | `k[G] ≅ ⊕ dim(V_i) · V_i` | Thm 5.4.6 |
| Quiver representations | `Quiver`, `PathAlgebra` | `QuiverRepresentation`, hom, subobjects | Ch7 items |
| Finite simple object enumeration | `Simple` predicate | Enumerating all simples in `FDRep` | Character table results |

## When Aristotle Is Unavailable

If `aristotle` is not on PATH or fails to connect, don't waste time debugging it. Instead:

1. Attempt the proof yourself (2-3 serious tries)
2. If stuck, `sorry` the proof with a comment: `-- Escalate to Aristotle when available`
3. Set items.json status to `attention_needed` (not `sent_to_aristotle`)
4. Move on to the next item — don't block your entire session on one proof

Aristotle availability varies by machine. Recording the need for escalation ensures a future session on a properly configured machine can pick it up.

## Common Failure Modes

From Phase 2 review patterns (50% attribution error rate in Stage 2.4 Part 1):

1. **Wrong Mathlib declaration name.** Always `#check` the declaration before using it.
2. **Fabricated references.** If `.refs.md` cites a Mathlib declaration, verify it exists.
3. **Scope mismatch.** The book may state a theorem for a specific case (e.g., finite-dimensional) but Mathlib has it more generally. Use the general version.
4. **Missing instances.** Representation theory needs many type class instances. If Lean can't find one, check if Mathlib has it under a different name or if you need to `open` a namespace.
