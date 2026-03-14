# FormalFrontier Formalization Plan

This document describes the pipeline for formalizing a mathematics textbook into Lean 4 with Mathlib. Work through the stages in order. Record progress in `PROGRESS.md` (stage-level) and `progress/items.json` (item-level). Do not modify this file for progress tracking.

## Phase 1: Source Preparation

### Stage 1.1: Page Extraction

Split the source PDF (`source/original.pdf`) into individual page files.

```bash
mkdir -p pdf/raw-pages
pdfseparate source/original.pdf pdf/raw-pages/%d.pdf
```

**Output:** `pdf/raw-pages/1.pdf`, `pdf/raw-pages/2.pdf`, ...

**Verify:** The number of files in `pdf/raw-pages/` matches the page count of the original PDF.

### Stage 1.2: Frontmatter Detection

Analyze the first ~20 pages and the last ~10 pages to determine:
- Where "page 1" of the book actually starts (after title page, copyright, table of contents, preface, etc.)
- Where the backmatter begins (appendices, bibliography, index)

Rename pages into `pdf/pages/` so that:
- `pdf/pages/1.pdf` corresponds to the book's actual page 1
- Frontmatter pages become `pdf/pages/frontmatter-1.pdf`, `pdf/pages/frontmatter-2.pdf`, ...
- Backmatter pages become `pdf/pages/backmatter-1.pdf`, `pdf/pages/backmatter-2.pdf`, ...

**Output:** `pdf/pages/` directory with correctly numbered pages.

**Verify:** Spot-check that page numbering matches the book's internal page numbers (printed on the pages themselves).

### Stage 1.3: Page Transcription

Convert each page to markdown with LaTeX math notation.

For each page in `pdf/pages/`, read the PDF and write it out as markdown. Maintain a rolling context of the book's topic and notation conventions to ensure consistency.

**Output:** `pages/1.md`, `pages/2.md`, ..., `pages/frontmatter-1.md`, etc.

**Validation:** Consider round-tripping: render the markdown back to a visual format and compare with the original page. Flag pages where the transcription looks poor.

**Verify:** One `.md` file per page in `pdf/pages/`.

### Stage 1.4: Structure Analysis

Identify every piece of content in the book and assign it to a blob. The goal is **complete, gap-free coverage**: every character of the transcribed text belongs to exactly one blob.

#### What to identify

**Formally numbered items:**
- Theorems, lemmas, propositions, corollaries
- Definitions
- Examples, exercises
- Remarks, notes

**Unstructured text** (equally important — these are first-class items):
- Chapter introductions
- Discussion paragraphs between numbered items
- Motivating text, informal explanations
- Notation conventions, historical notes
- Preface, foreword

#### Identifier scheme

- Numbered items: `Chapter3/Theorem3.1`, `Chapter3/Definition3.2`
- Discussion text between items: `Chapter3/Discussion_after_3.2` (covering all text from after Definition 3.2 until the next numbered item)
- Chapter introductions (text before the first numbered item): `Chapter3/Introduction`
- Frontmatter blobs: `Frontmatter/Preface`, `Frontmatter/Notation`, `Frontmatter/TableOfContents`
- Backmatter blobs: `Backmatter/Bibliography`, `Backmatter/Index`

#### Output format

Write `items.json` with an array of items, each having:
```json
{
  "id": "Chapter3/Theorem3.1",
  "type": "theorem",
  "title": "Bolzano-Weierstrass Theorem",
  "start_page": 45,
  "end_page": 46,
  "start_line": 12,
  "end_line": 3
}
```

Where `start_line` and `end_line` refer to line numbers within the page markdown files.

Types: `theorem`, `lemma`, `proposition`, `corollary`, `definition`, `example`, `exercise`, `remark`, `discussion`, `introduction`, `preface`, `notation`, `bibliography`, `index`

**Contiguity check:** Run a check to verify that:
1. Every line of every page markdown file belongs to exactly one blob
2. There are no gaps between consecutive blobs
3. There are no overlaps
4. The blobs, when concatenated in order, reproduce the complete text

**Verify:** `items.json` exists and passes the contiguity check.

### Stage 1.5: Blob Extraction

Split the page-level markdown into per-blob files, one file per item in `items.json`.

**Output:** `blobs/Chapter1/Definition1.1.md`, `blobs/Chapter1/Discussion_after_1.1.md`, ...

**Verify:**
- One blob file per item in `items.json`
- Concatenating all blob files in order reproduces the complete transcribed text

### Stage 1.6: Indexing (optional)

Build one-line summaries for each blob, useful for quick reference and RAG.

**Output:** `index/summaries.json`

This stage is optional. Agents can also just read blob files directly.

---

## Phase 2: Dependency Mapping

### Stage 2.1: Internal Dependency Analysis

Read the text linearly, noting every internal reference:

- **Explicit references:** "by Lemma 5.6.7", "from Theorem 2.3", "as defined in Definition 1.4"
- **Structural declarations:** "This chapter depends only on Chapters 1 and 2", "We assume familiarity with Chapter 3"
- **Implicit dependencies:** Uses a concept or definition from earlier without citing it

**Initial assumption:** Each item depends on everything that comes before it in the book, unless the text clearly states otherwise (e.g., "this chapter is independent of chapters 4-6"). This is conservative and correct. We will trim dependencies later in Stage 3.4 once we have actual proofs.

**Output:** `dependencies/internal.json` — a mapping from each item ID to a list of item IDs it depends on.

**Verify:** Every reference target exists in `items.json`.

### Stage 2.2: External Dependency Analysis

Identify mathematical concepts, definitions, and results that the book assumes but does not prove.

Categorize each:
- **Undergraduate prerequisites:** Linear algebra, basic analysis, group theory basics, etc.
- **Results from other books:** Specific theorems cited from external sources
- **Folklore/well-known facts:** Results stated without proof and without citation

**Output:** `dependencies/external.json` — a list of external dependencies, each with a description, the items that need it, and the category.

### Stage 2.3: Blueprint Assembly

Combine `items.json`, `dependencies/internal.json`, and `dependencies/external.json` into a preliminary blueprint.

This is a DAG of what needs to be formalized and in what order. Because we conservatively assumed sequential dependencies, the initial DAG will be nearly linear. That is fine — it will be refined in Stage 3.4.

#### Blueprint tooling

The blueprint uses a hybrid of two tools:

- **leanblueprint** (https://github.com/PatrickMassot/leanblueprint): The rendering substrate. Produces an interactive HTML website with a dependency DAG and a PDF document. Uses LaTeX source with special macros (`\uses{}`, `\lean{}`, `\leanok`). This handles **all** blueprint nodes — both formal declarations and non-formal content (discussion blobs, introductions, external dependencies).
- **LeanArchitect** (https://github.com/hanwenzhu/LeanArchitect, using https://github.com/kim-em/LeanArchitect/tree/blueprint-all until https://github.com/hanwenzhu/LeanArchitect/pull/8 is merged): Complements leanblueprint for Lean-backed nodes. Run externally with `extract_blueprint --all` against the project's compiled `.olean` files — no `require`, `import`, or attributes needed in the Lean source. Automatically infers dependencies between formal declarations and tracks formalization status via sorry detection. Provides JSON export for agent consumption.

The split: leanblueprint owns the full DAG (formal + non-formal nodes). LeanArchitect automates the Lean-backed portion (theorems, definitions, lemmas), eliminating manual `\leanok` and `\uses{}` maintenance for those nodes. Non-formal nodes (discussion, introductions, external dependencies) use leanblueprint's LaTeX macros directly. The Lean source files are completely free of blueprint annotations.

#### Steps

1. Set up leanblueprint scaffolding in `blueprint/` (use `leanblueprint new` or copy from a template).
2. Generate LaTeX blueprint nodes from `items.json` and dependency data. Each item becomes a LaTeX environment with `\label{}` and `\uses{}` annotations.
3. Non-formalizable items (discussion, introduction, etc.) are included as LaTeX nodes for completeness — they appear in the DAG but don't need Lean declarations.
4. Run `leanblueprint web` to generate the HTML dependency graph.

The initial blueprint is purely LaTeX-based. LeanArchitect integration happens after Stage 3.2 when Lean scaffolding is compiled — run `extract_blueprint --all --json` against the `.olean` files to get the dependency graph and formalization status.

**Output:** `blueprint/` directory with leanblueprint LaTeX source files.

**Verify:** `leanblueprint web` succeeds and produces a valid dependency graph.

### Stage 2.4: Research — Mathlib Coverage

For each external dependency and each item, search Mathlib for relevant material.

- Is this definition already in Mathlib? Under what name?
- Is this theorem already proved? At what generality?
- What's the closest Mathlib result, even if not an exact match?

**Output:** `research/mathlib-coverage.json` — mapping items and external deps to Mathlib declarations (with `#check` names).

### Stage 2.5: Research — External Sources

For items and dependencies not covered by Mathlib:

- Other FormalFrontier artifacts that cover this material
- External Lean libraries
- Natural language sources with detailed proofs (useful for formalization agents)

**Output:** `research/external-sources.json`

### Stage 2.6: Readiness Report

Prepare a human-readable report summarizing:

- Which items are ready to formalize (all dependencies satisfied by Mathlib or already formalized items)
- Which items are blocked and on what
- Suggested formalization order
- Any concerns about definitions, generality, or missing infrastructure

**Output:** `READINESS.md`

**This is a human review checkpoint.** Orchestrators should pause here and wait for a human to review the readiness report and give approval before proceeding to formalization.

### Stage 2.7: Reference Attachment

For each blob that has external dependencies or Mathlib matches, create a companion reference file.

These files are read by formalization agents when they work on the corresponding item, giving them immediate access to relevant Mathlib names, similar theorems, and context.

**Output:** `blobs/Chapter1/Theorem1.2.refs.md` alongside each blob that has references.

---

## Phase 3: Formalization

### Stage 3.1: Lean Project Setup

Create a Lean 4 project with Mathlib as a dependency. The `blueprint/` directory should already exist from Stage 2.3. LeanArchitect is **not** a dependency of the Lean project — it runs externally against the compiled `.olean` files.

**Output:** `lean/` directory containing:
- `lakefile.toml` with Mathlib dependency
- `lean-toolchain` matching Mathlib's toolchain
- `.gitignore` for build artifacts

**Verify:** `cd lean && lake build` succeeds (empty project, just checking Mathlib dependency works).

### Stage 3.2: Lean Scaffolding

Create `.lean` files for each formalizable item (theorems, definitions, lemmas — not discussion blobs).

Set up the import chain:
- Root file: `lean/{Title}.lean` importing all chapter files
- Chapter files: `lean/{Title}/Chapter1.lean` importing all items in the chapter
- Item files: `lean/{Title}/Chapter1/Theorem1_1.lean` with a sorry'd statement

Each item file should contain:
- A sorry'd `theorem` or `def` statement based on the blob's content
- A doc-string with the natural language statement from the book
- Appropriate Mathlib imports

No blueprint-specific annotations are needed — LeanArchitect runs externally with `--all` to extract the blueprint from the compiled `.olean` files.

Example:
```lean
/-- **Bolzano-Weierstrass Theorem.** Every bounded sequence in ℝ has a convergent subsequence. -/
theorem bolzano_weierstrass {s : ℕ → ℝ} (hb : Bornology.IsBounded (Set.range s)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ L, Filter.Tendsto (s ∘ φ) Filter.atTop (nhds L) := by
  sorry
```

Once scaffolding is complete, run `extract_blueprint single --all --json` against each module's `.olean` to get the blueprint JSON, and `leanblueprint web` to update the HTML dependency graph.

**Output:** `lean/{Title}/Chapter1/Theorem1_1.lean`, etc.

**Verify:** `cd lean && lake build` succeeds (everything compiles with sorries).

### Stage 3.3: Formalization Work Loop

Orchestrate agents to formalize items, respecting the dependency DAG from the blueprint. Uses a tiered strategy: Claude agents first, with escalation to Aristotle (an automated theorem prover) for difficult proofs.

#### Agent workflow

Each agent is assigned a task (an item or small group of related items). The agent either:
1. **Submits a PR** that fully or partially resolves the task
2. **Escalates by posting an issue** documenting the blockers

#### Task selection

Agents query the blueprint to find ready work:
1. Run `extract_blueprint single --all --json` against each module to get the current dependency graph and formalization status.
2. Find nodes that still contain `sorry` but whose dependency nodes are all sorry-free.
3. These are the items ready for formalization — pick one and work on it.

Status updates are automatic: when an agent removes a `sorry`, the next extraction reflects the new status. No annotations needed in the Lean source. Non-formal nodes (discussion, external dependencies) are tracked via leanblueprint's LaTeX macros and `progress/items.json`.

#### Tiered proving strategy

Use a tiered approach to maximize throughput:

1. **Claude first** — Claude agents attempt initial formalization: statement formalization, straightforward proofs, and definition translation. Most textbook items should be attempted by Claude first.

2. **Escalate to Aristotle** — When a Claude agent fails to prove a theorem after 2-3 serious attempts, escalate to Aristotle. Record the escalation in `progress/items.json` by setting `"escalated_to_aristotle": true`.

3. **Aristotle batch pass** — After Stage 3.2 scaffolding is complete, submit all sorry'd theorems to Aristotle as a batch. This runs concurrently with Claude agents working on other items. Any theorems Aristotle solves reduce the workload for Claude.

#### Aristotle integration

Aristotle is an automated theorem proving service that can fill `sorry` placeholders in Lean files. It is especially effective for standard mathematical proofs that follow well-known patterns.

##### Submitting to Aristotle

For each item to submit:

1. **Prepare the file.** Create a temporary copy of the item's Lean file. The file must contain exactly one `sorry` (the target theorem). Change all other `sorry` occurrences to `admit`.

2. **Gather context.** Collect sorry-free local Lean files that this item depends on (from the import chain). Skip Mathlib imports — Aristotle has Mathlib built in. If no local files are sorry-free yet (e.g., during the initial batch pass after Stage 3.2), submit with no context files. Pass context via `--context-files`.

3. **Submit.**
   ```bash
   aristotle prove-from-file item_pending.lean --no-wait \
     --no-auto-add-imports --context-files dep1.lean dep2.lean
   ```

4. **Record the project ID.** Aristotle returns a UUID. Store it in `progress/items.json`:
   ```json
   {
     "Chapter1/Theorem1.1": {
       "status": "sent_to_aristotle",
       "aristotle_id": "uuid-here",
       "last_updated": "2026-03-20"
     }
   }
   ```

5. **Clean up.** Delete the temporary file. Never commit files with `admit`.

##### Monitoring and retrieval

- **Poll every 5 minutes** for completion using the `aristotlelib` Python API.
- **Respect the concurrency limit:** Aristotle allows at most 5 concurrent projects. Queue excess items and submit as slots free up.
- **Deduplication:** Before submitting, check that the item is not already in `sent_to_aristotle` status. Only one submission per item at a time.
- When a project completes, download the result to a temporary file for verification.

##### Incorporating results

When Aristotle returns a result:

1. **Verify it compiles** against the local toolchain: copy the proof into the item's Lean file (under `lean/{Title}/...`) and run `lake build` for that module.
2. **If it compiles clean:** Update status to `sorry_free` (if the item has no remaining sorries) or `proof_formalized`. Submit a PR.
3. **If Aristotle reports the theorem is false:** Mark the item as `attention_needed`. Post a GitHub issue describing the counterexample Aristotle found. The formalized statement (from Stage 3.2) needs revision.
4. **If it fails to compile** (toolchain version mismatch): Mark the item as `attention_needed` for manual review.

##### Aristotle item statuses

Items going through Aristotle use these statuses in `progress/items.json`:

`statement_formalized` → `sent_to_aristotle` → `sorry_free` (success) or `attention_needed` (failure)

#### Dependency tracking

- Use `- [ ] depends on #X` comments in issues
- Use a `blocked` label for items waiting on dependencies
- Agents should not work on items whose dependencies aren't yet formalized (unless they are willing to sorry the dependencies and work top-down)

#### Triage

Specialized triage agents should periodically review open issues for:
- Definition correctness problems (wrong definition, insufficient generality)
- Missing low-level API lemmas needed across multiple items
- Dependency ordering mistakes
- Opportunities for useful tactics or metaprograms
- Aristotle results that need attention (false statements, version mismatches)

#### Formalization guidance

- **Push sorries earlier:** Work top-down. State the theorem, sorry the proof, then work on filling in the sorry. Don't waste time on helper lemmas until you know they're needed.
- **Spec-driven development:** Use sorry placeholders with comments explaining what's needed, not `True` or other cheats.
- **Pre-formalization:** For complex items, first translate the natural language blob into a pedantic, detailed version with careful references to every fact used, before attempting formalization.

### Stage 3.4: Dependency Trimming (post-formalization)

Once items have sorry-free proofs, analyze actual dependencies using both LeanArchitect's inference (for formal declarations) and manual review (for non-formal nodes).

For Lean-backed nodes, LeanArchitect automatically infers dependencies from proof terms — compare these against the conservative initial dependencies. For non-formal nodes (discussion blobs, external dependencies), review whether the initial dependency assumptions were accurate.

Compare the inferred/reviewed dependencies against `dependencies/internal.json`:
- Which initial dependencies turned out to be unnecessary?
- Are there unexpected dependencies that weren't in the original analysis?
- Does the actual dependency structure reveal anything interesting about the book's organization?

This is when we learn the true dependency structure of the book, which may differ significantly from the conservative initial assumption.

**Output:** Updated `dependencies/internal.json` and blueprint reflecting actual dependencies.

---

## Progress Tracking

### Stage-level progress: `PROGRESS.md`

Orchestrators update `PROGRESS.md` as stages are completed. Format:

```markdown
## Stage 1.1: Page Extraction
**Status:** Complete
**Date:** 2026-03-15
**Notes:** 342 pages extracted.

## Stage 1.2: Frontmatter Detection
**Status:** Complete
**Date:** 2026-03-15
**Notes:** Page 1 starts at raw page 13. Backmatter from page 298.
```

### Item-level progress: `progress/items.json`

Item statuses flow through:
`identified` → `extracted` → `statement_formalized` → `proof_formalized` → `sorry_free` → `dependency_trimmed`

Items escalated to Aristotle use: `statement_formalized` → `sent_to_aristotle` → `sorry_free` (success) or `attention_needed` (failure)

```json
{
  "Chapter1/Theorem1.1": {
    "status": "sorry_free",
    "last_updated": "2026-03-20",
    "pr": "#42",
    "notes": ""
  },
  "Chapter2/Theorem2.3": {
    "status": "sent_to_aristotle",
    "last_updated": "2026-03-21",
    "aristotle_id": "a1b2c3d4-e5f6-7890-abcd-ef1234567890",
    "escalated_to_aristotle": true,
    "notes": "Claude failed after 3 attempts, escalated"
  }
}
```

### Rules

- **Do NOT modify PLAN.md** for progress tracking. This document is the reference plan.
- Stage-level progress goes in `PROGRESS.md`.
- Item-level progress goes in `progress/items.json`.
- Blockers and discussion go in GitHub issues.
