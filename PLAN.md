# FormalFrontier Formalization Plan

This document describes the pipeline for formalizing a mathematics textbook into Lean 4 with Mathlib. Work through the stages in order. Record progress in per-turn files in `progress/` and item-level status in `progress/items.json`. Do not modify this file for progress tracking.

## Phase 1: Source Preparation

### Stage 1.1: Page Extraction

Split the source PDF (`source/original.pdf`) into individual page files.

```bash
mkdir -p pdf/raw-pages
pdfseparate source/original.pdf pdf/raw-pages/%d.pdf
```

**Output:** `pdf/raw-pages/1.pdf`, `pdf/raw-pages/2.pdf`, ...

**Verify:** The number of files in `pdf/raw-pages/` matches the page count of the original PDF.

### Stage 1.2: Start Lean Build

The Lean project was created at the repo root by `ff init` using `lake init <ProjectName> math`, where `<ProjectName>` is the repository name with the `FormalFrontier-` prefix stripped (e.g., `FormalFrontier-Rudin` → `Rudin`). Start downloading Mathlib now so it is ready by the time formalization begins.

```bash
lake build
```

This takes ~30 minutes the first time (Mathlib download and build). Start it in the background and proceed with the remaining Phase 1 stages. Having the Lean project available early allows agents to test Lean snippets while transcribing and analyzing structure.

**Output:** `.lake/` with compiled Mathlib artifacts.

**Verify:** `lake build` exits successfully.

### Stage 1.3: Frontmatter Detection

This is a **lightweight pass**. Start by examining the first ~20 pages and the last ~10 pages of `pdf/raw-pages/` — that is usually sufficient. If a book has an unusually long preface, TOC, or index, look at a few more pages until the boundary is clear. You do not need to read the entire book.

Determine:
- Where "page 1" of the book actually starts (after title page, copyright, table of contents, preface, etc.)
- Where the backmatter begins (appendices, bibliography, index)

Copy pages into `pdf/pages/` with the appropriate names. (`pdf/raw-pages/` is the untouched extraction output and must not be modified; `pdf/pages/` is the canonical input for all subsequent stages.)
- `pdf/pages/1.pdf` corresponds to the book's actual page 1
- Frontmatter pages become `pdf/pages/frontmatter-1.pdf`, `pdf/pages/frontmatter-2.pdf`, ...
- Backmatter pages become `pdf/pages/backmatter-1.pdf`, `pdf/pages/backmatter-2.pdf`, ...

**All pages are included** — frontmatter, main content, and backmatter all get entries in `pdf/pages/`. Nothing is discarded.

After copying, write `pdf/pages/mapping.json` recording the raw-page → logical-page correspondence. This is the authoritative record of the frontmatter boundary decision; subsequent stages that need to map between raw and logical page numbers must read this file rather than reverse-engineering it from filenames.

Format:
```json
{
  "frontmatter_raw_pages": [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12],
  "backmatter_raw_pages": [298, 299, 300, 301, 302, 303, 304, 305, 306, 307, 308, 309, 310, 311, 312],
  "mapping": {
    "1": "frontmatter-1",
    "2": "frontmatter-2",
    "13": "1",
    "14": "2",
    "298": "backmatter-1",
    "299": "backmatter-2"
  }
}
```

Keys in `"mapping"` are raw page numbers (as strings); values are logical page names (matching the filenames in `pdf/pages/` without the `.pdf` extension). Every raw page appears exactly once as a key; every logical page name appears exactly once as a value; and the set of values corresponds exactly to the filenames present in `pdf/pages/`. `"frontmatter_raw_pages"` and `"backmatter_raw_pages"` are convenience lists for quick range queries; use `[]` for either when the book has no frontmatter or no backmatter.

**Output:** `pdf/pages/` directory with all pages from `pdf/raw-pages/`, copied and renamed. `pdf/pages/mapping.json` recording the raw-page → logical-page correspondence.

**Verify:**
- Spot-check that page numbering matches the book's internal page numbers (printed on the pages themselves).
- Every file in `pdf/raw-pages/` maps to exactly one file in `pdf/pages/` — no raw page is missing and no extra files are present.
- `pdf/pages/mapping.json` exists and accounts for every raw page number.

> **Do not begin Stage 1.4 until this stage is complete and `pdf/pages/` is fully populated.** Stage 1.4 reads exclusively from `pdf/pages/` — never from `pdf/raw-pages/`. If you are uncertain about frontmatter boundaries after examining the boundary pages, make your best determination; do not defer this decision into the transcription loop.

### Stage 1.4: Page Transcription

Convert each page to markdown with LaTeX math notation.

Transcribe **all** pages — frontmatter, main content, and backmatter — every file in `pdf/pages/` gets a corresponding `.md` file. Read exclusively from `pdf/pages/` — never from `pdf/raw-pages/`. To look up which raw page corresponds to a given logical page (or vice versa), read `pdf/pages/mapping.json`.

#### Setup

Create one GitHub issue per page in this repo. Use `gh label create transcription --color 0075ca --description "Page transcription work item"` first (ignore error if it already exists). Each issue should:

- Title: `Transcribe page N` for main-content pages; `Transcribe frontmatter-N` or `Transcribe backmatter-N` for frontmatter/backmatter pages
- Body: list the specific input file(s) (e.g., `pdf/pages/42.pdf` or `pdf/pages/frontmatter-3.pdf`), expected output file(s) (e.g., `pages/42.md` or `pages/frontmatter-3.md`), and a dependency on the previous page's issue: `- [ ] depends on #(previous issue number)`
- Label: `transcription`

The dependency chain enforces linear processing so each agent can read the previously transcribed page for context. The first page's issue (frontmatter-1, or page 1 if there is no frontmatter) has no dependency. Order issues following the logical order already established in `pdf/pages/mapping.json`.

After creating all issues, verify that every file in `pdf/pages/` is covered by exactly one issue and there are no gaps.

This gives each transcription agent a single, well-scoped task and makes progress visible at page granularity. Partial failures are isolated — a missing page 47 doesn't block the rest.

#### Shared notation conventions

Create `pages/CONVENTIONS.md` before agents start work. Initially it may be sparse (just the book title and subject area). Each transcription agent must:

1. Read `pages/CONVENTIONS.md` before transcribing
2. After transcribing, update `pages/CONVENTIONS.md` with any notation or formatting conventions they established (e.g., how inline math is delimited, how theorem environments are marked up, abbreviations used)

This file is the shared context that keeps transcriptions consistent across parallel agents. Commit it alongside the page `.md` file.

#### Agent workflow

Each agent assigned to a transcription issue:

1. Reads `pages/CONVENTIONS.md` for established conventions
2. Reads the previously transcribed `.md` file (if any) for style and formatting context
3. Reads the specified PDF page(s) from `pdf/pages/`
4. Writes the corresponding `.md` file(s) with LaTeX math notation, consistent with preceding pages
5. Updates `pages/CONVENTIONS.md` with any new conventions introduced
6. Commits directly to the default branch with `Fixes #N` in the commit message (which auto-closes the issue on push)

**Output:** `pages/1.md`, `pages/2.md`, ..., `pages/frontmatter-1.md`, `pages/backmatter-1.md`, etc. Plus `pages/CONVENTIONS.md`.

**Validation:** Consider round-tripping: render the markdown back to a visual format and compare with the original page. Flag pages where the transcription looks poor.

**Verify:** One `.md` file per page in `pdf/pages/`. All transcription issues are closed.

### Stage 1.5: Structure Analysis

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
  "start_page": "45",
  "end_page": "46",
  "start_line": 12,
  "end_line": 3
}
```

Where `start_line` and `end_line` refer to line numbers within the page markdown files. `start_page` and `end_page` are logical page names (strings matching the `pdf/pages/` filenames without the `.pdf` extension, e.g. `"45"`, `"frontmatter-3"`, `"backmatter-1"`).

Types: `theorem`, `lemma`, `proposition`, `corollary`, `definition`, `example`, `exercise`, `remark`, `discussion`, `introduction`, `preface`, `notation`, `bibliography`, `index`

**Contiguity check:** Run a check to verify that:
1. Every line of every page markdown file belongs to exactly one blob
2. There are no gaps between consecutive blobs
3. There are no overlaps
4. The blobs, when concatenated in order, reproduce the complete text

**Verify:** `items.json` exists and passes the contiguity check.

### Stage 1.6: Blob Extraction

Split the page-level markdown into per-blob files, one file per item in `items.json`.

**Output:** `blobs/Chapter1/Definition1.1.md`, `blobs/Chapter1/Discussion_after_1.1.md`, ...

**Verify:**
- One blob file per item in `items.json`
- Concatenating all blob files in order reproduces the complete transcribed text

### Stage 1.7: Indexing (optional)

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

**Initial assumption:** List only **direct** dependencies — do not store transitive closure. The conservative default is a **linear chain**: each item directly depends only on its immediate predecessor in book order. For example, if items are A, B, C in order: B depends on `["A"]` and C depends on `["B"]` — not `["A", "B"]`. If the text explicitly states independence (e.g., "this chapter does not use Chapter 3"), trim accordingly. We will replace this chain with actual direct dependencies in Stage 3.3.

**File size check:** `internal.json` should have approximately N entries of 0–1 elements each (for N items). If entries grow with item count (e.g., item 100 has 99 entries), you have stored transitive closure — regenerate with direct dependencies only.

**Output:** `dependencies/internal.json` — a mapping from each item ID to a list of item IDs it **directly** depends on.

**Verify:** Every reference target exists in `items.json`.

### Stage 2.2: External Dependency Analysis

Identify mathematical concepts, definitions, and results that the book assumes but does not prove.

Categorize each:
- **Undergraduate prerequisites:** Linear algebra, basic analysis, group theory basics, etc.
- **Results from other books:** Specific theorems cited from external sources
- **Folklore/well-known facts:** Results stated without proof and without citation

**Output:** `dependencies/external.json` — a list of external dependencies, each with a description, the items that need it, and the category.

### Stage 2.3: Research — Mathlib Coverage

For each external dependency and each item, search Mathlib for relevant material.

- Is this definition already in Mathlib? Under what name?
- Is this theorem already proved? At what generality?
- What's the closest Mathlib result, even if not an exact match?

**Output:** `research/mathlib-coverage.json` — mapping items and external deps to Mathlib declarations (with `#check` names).

### Stage 2.4: Research — External Sources

For items and dependencies not covered by Mathlib:

- Other FormalFrontier artifacts that cover this material
- External Lean libraries
- Natural language sources with detailed proofs (useful for formalization agents)

**Output:** `research/external-sources.json`

### Stage 2.5: Readiness Report

Prepare a human-readable report summarizing:

- Which items are ready to formalize (all dependencies satisfied by Mathlib or already formalized items)
- Which items are blocked and on what
- Suggested formalization order
- Any concerns about definitions, generality, or missing infrastructure

**Output:** `READINESS.md`

**Note:** This report is informational — do not pause for human review. Write the report and immediately continue to Stage 2.6.

### Stage 2.6: Reference Attachment

For each blob that has external dependencies or Mathlib matches, create a companion reference file.

These files are read by formalization agents when they work on the corresponding item, giving them immediate access to relevant Mathlib names, similar theorems, and context.

**Output:** `blobs/Chapter1/Theorem1.2.refs.md` alongside each blob that has references.

---

## Phase 3: Formalization

### Stage 3.1: Lean Scaffolding

The Lean project was created at the repo root by `ff init` in Stage 1.2 and Mathlib was built then. Create `.lean` files for each formalizable item (theorems, definitions, lemmas — not discussion blobs).

Set up the import chain:
- Root file: `{Title}.lean` importing all chapter files
- Chapter files: `{Title}/Chapter1.lean` importing all items in the chapter
- Item files: `{Title}/Chapter1/Theorem1_1.lean` with a sorry'd statement

Each item file should contain:
- A sorry'd `theorem` or `def` statement based on the blob's content
- A doc-string with the natural language statement from the book
- Appropriate Mathlib imports

Example:
```lean
/-- **Bolzano-Weierstrass Theorem.** Every bounded sequence in ℝ has a convergent subsequence. -/
theorem bolzano_weierstrass {s : ℕ → ℝ} (hb : Bornology.IsBounded (Set.range s)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ L, Filter.Tendsto (s ∘ φ) Filter.atTop (nhds L) := by
  sorry
```

**Output:** `{Title}/Chapter1/Theorem1_1.lean`, etc.

**Verify:** `lake build` succeeds (everything compiles with sorries).

### Stage 3.2: Formalization Work Loop

Orchestrate agents to formalize items, respecting the dependency DAG.

#### PR lifecycle

PRs must be merged to `main` without human intervention to avoid blocking downstream agents. Every PR should have auto-merge enabled at creation time:

```bash
gh pr create --title "Formalize <ItemID>" --body "..."
PR_NUM=$(gh pr view --json number --jq .number)
gh pr merge "$PR_NUM" --auto --squash
```

At the **start of every planning cycle**, before selecting new work, merge all PRs that are mergeable and have no failing CI checks:

```bash
gh pr list --state open \
  --json number,mergeable,statusCheckRollup \
  --jq '.[] | select(
    .mergeable == "MERGEABLE" and
    (.statusCheckRollup | all(.conclusion != "FAILURE" and .conclusion != "CANCELLED"))
  ) | .number' \
| xargs -I{} gh pr merge {} --squash --delete-branch
```

#### Agent workflow

Each agent is assigned a task (an item or small group of related items). The agent either:
1. **Submits a PR** that fully or partially resolves the task (with auto-merge enabled)
2. **Escalates by posting an issue** documenting the blockers

#### Task selection

Agents query `progress/items.json` and the dependency DAG to find ready work:
1. Find items that still contain `sorry` but whose dependency items are all sorry-free.
2. These are the items ready for formalization — pick one and work on it.

Status updates are tracked in `progress/items.json`. Non-formal nodes (discussion, external dependencies) are also tracked there.

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

#### Formalization guidance

- **Push sorries earlier:** Work top-down. State the theorem, sorry the proof, then work on filling in the sorry. Don't waste time on helper lemmas until you know they're needed.
- **Spec-driven development:** Use sorry placeholders with comments explaining what's needed, not `True` or other cheats.
- **Pre-formalization:** For complex items, first translate the natural language blob into a pedantic, detailed version with careful references to every fact used, before attempting formalization.

### Stage 3.3: Dependency Trimming (post-formalization)

Once items have sorry-free proofs, analyze actual dependencies by reviewing the proof terms and imports.

Compare the actual dependencies against `dependencies/internal.json`:
- Which initial dependencies turned out to be unnecessary?
- Are there unexpected dependencies that weren't in the original analysis?
- Does the actual dependency structure reveal anything interesting about the book's organization?

This is when we learn the true dependency structure of the book, which may differ significantly from the conservative initial assumption.

**Output:** Updated `dependencies/internal.json` reflecting actual dependencies.

### Stage 3.5: Upstreaming Analysis

Identify formalized results that may be worth contributing to Mathlib or related libraries.
The output is a non-binding `UPSTREAMING.md` report — no actual upstreaming happens here.

#### Criteria

Include only results with **proofs genuinely new to Mathlib**. Exclude:
- Items whose proof is a one-line call to an existing Mathlib declaration (pure wrappers)
- Items that combine two or three Mathlib facts with trivial glue
- Items where the proof quality, generality, or formulation is not at Mathlib level

#### Phase 1: Lightweight triage

Scan all sorry-free, proof-polished items. For each, make an initial judgment:

- **Reject immediately** if the proof in the Lean file is a one-liner delegating to a named
  Mathlib theorem — it's already in Mathlib.
- **Keep as candidate** if the proof is substantive and the result feels absent from Mathlib's
  API.

Record the initial candidate list with a brief justification for each entry.

#### Phase 2: Deep Mathlib research

For each candidate, search the **local Mathlib source** (`.lake/packages/mathlib/`) for
closely related results — do not rely on web searches or AI knowledge of Mathlib, which
may be out of date. Open one GitHub issue per candidate to track the research and verdict.

For each candidate, determine:
1. Is the result already in Mathlib, possibly under a different name or with different type
   class assumptions? (Check related files carefully — not just exact name matches.)
2. Is there a close relative in Mathlib such that the candidate is just a straightforward
   corollary or type-class variant?
3. Is the proof approach genuinely new, or does it reconstruct something Mathlib already
   proves elsewhere?

Based on the research, assign one of three verdicts:

- **Reject — insufficient interest:** The result is too narrow, the proof quality doesn't
  meet Mathlib standards, or it's not a good fit.
- **Reject — already in Mathlib:** Found an equivalent result. Create a GitHub issue to
  refactor the proof to use the Mathlib declaration directly, and update the item's
  `progress/items.json` status to `mathlib_covered`.
- **Include in UPSTREAMING.md:** Genuinely new to Mathlib, correct, and at appropriate
  generality and quality.

#### Phase 3: Write UPSTREAMING.md

Write `UPSTREAMING.md` at the repository root with the following structure:

```markdown
# Upstreaming Candidates

These are suggestions only — no actual upstreaming has occurred.

## Included

### <Item ID> — `theorem_name`

**File:** `path/to/Item.lean`

**Statement:** (the Lean statement)

**Why it's new:** What was searched, what was found, why this is absent.

**Suggested home:** Which Mathlib file/module it belongs in.

## Excluded

### <Item ID> — reason

One-line reason (already in Mathlib as `FooBar.baz`, too narrow, etc.).
```

#### Output

- `UPSTREAMING.md` at the repository root
- GitHub issues for any items whose proofs should be refactored to use Mathlib directly
- `progress/items.json` updated with `"upstreaming_status"` field:
  - `"candidate"` — included in UPSTREAMING.md
  - `"mathlib_covered"` — already in Mathlib, refactor issue opened
  - `"rejected"` — not a candidate

**Verify:** `UPSTREAMING.md` exists. Every proof-polished item has an `upstreaming_status`
in `progress/items.json`.

---

## Progress Tracking

### Per-turn progress files: `progress/YYYY-MM-DDTHH-MM-SSZ.md`

At the end of every agent turn, write a timestamped progress file in `progress/`. Use the current UTC time for the filename (e.g., `progress/2026-03-15T14-30-00Z.md`). This gives a full audit trail of what each agent did and decided, and reliably onboards the next agent.

Template:
```markdown
## Accomplished
<!-- What was done this turn -->

## Current frontier
<!-- Where work stopped -->

## Overall project progress
<!-- High-level status (which stages are complete, how many items are formalized, etc.) -->

## Next step
<!-- Concrete recommendation for the next agent -->

## Blockers
<!-- Anything blocking forward progress; empty if none -->
```

The most recent file in `progress/` (sorted alphabetically, since filenames are ISO 8601 timestamps) is the canonical handoff document for the next agent. **Always read it at the start of a turn** before checking `PLAN.md` for stage details. If `progress/` contains only `progress/0000-init.md` (or no handoff file at all), the repo is freshly initialized — proceed with Stage 1.1.

Commits made during a turn should mention the corresponding progress file in the commit message (e.g., `See progress/2026-03-15T14-30-00Z.md`).

### Stage-level summary: `PROGRESS.md` (optional)

`PROGRESS.md` may be maintained as a human-facing summary of stage completion. It is not the primary source of truth — the per-turn files are. If kept, format:

```markdown
## Stage 1.1: Page Extraction
**Status:** Complete
**Date:** 2026-03-15
**Notes:** 342 pages extracted.

## Stage 1.2: Start Lean Build
**Status:** Complete
**Date:** 2026-03-15
**Notes:** Mathlib downloaded and built successfully.

## Stage 1.3: Frontmatter Detection
**Status:** Complete
**Date:** 2026-03-15
**Notes:** Page 1 starts at raw page 13. Backmatter from raw page 298. See `pdf/pages/mapping.json` for the full raw-page → logical-page mapping.
```

### Item-level progress: `progress/items.json`

Item statuses flow through:
`identified` → `extracted` → `statement_formalized` → `proof_formalized` → `sorry_free` → `dependency_trimmed`

```json
{
  "Chapter1/Theorem1.1": {
    "status": "sorry_free",
    "last_updated": "2026-03-20",
    "pr": "#42",
    "notes": ""
  }
}
```

### Rules

- **Do NOT modify PLAN.md** for progress tracking. This document is the reference plan.
- Per-turn handoff notes go in `progress/YYYY-MM-DDTHH-MM-SSZ.md` (write one at the end of every turn).
- Stage-level summary may be kept in `PROGRESS.md` (optional, human-facing).
- Item-level progress goes in `progress/items.json`.
- Blockers and discussion go in GitHub issues.
