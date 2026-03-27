# FormalFrontier Formalization Plan

This document describes the pipeline for formalizing a mathematics textbook into Lean 4 with Mathlib. Work through the stages in order. Record progress in per-turn files in `progress/` and item-level status in `progress/items.json`. Do not modify this file for progress tracking.

**Two item files — don't confuse them:**
- **`items.json`** (repo root) — The **catalog**: every item's ID, type, title, page range, and line range. Created in Stage 1.6 (Structure Analysis). Read-only after creation (except to fix errors found by the contiguity check).
- **`progress/items.json`** — The **workflow status tracker**: which pipeline stage each item has reached, when it was last updated, which PR touched it. Updated throughout Phases 2–3 as items progress.

### Project Dependencies (check `lakefile.toml`)

**At the start of every session**, read `lakefile.toml` and check for `[[require]]` entries beyond Mathlib. These are **sibling formalization projects** — typically earlier lectures, chapters, or volumes in the same series — whose definitions and theorems are available for import.

For each non-Mathlib `[[require]]` entry:

1. **Browse its source code.** After `lake exe cache get` downloads dependencies, find the package under `.lake/packages/<package-name>/`. Read its Lean source files to understand what definitions, theorems, and instances it provides.
2. **Import from it preferentially.** If a concept needed by this project is already formalized in a required package, import and use it — do not re-formalize it. This applies to definitions, theorems, type class instances, and notation.
3. **Treat it like Mathlib.** Required packages are first-class dependencies, just like Mathlib. Use `recall` for definitions/theorems that exist there, `example` for instances, and build on their API.

If `lakefile.toml` has no non-Mathlib requires, skip this section — the project is self-contained.

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
lake exe cache get &&  lake build
```

### Stage 1.3: Frontmatter Detection

Start by examining the first ~20 pages and the last ~10 pages of `pdf/raw-pages/` — that is usually sufficient. If a book has an unusually long preface, TOC, or index, look at a few more pages until the boundary is clear. You do not need to read the entire book.

Determine:
- Where "page 1" of the book actually starts (after title page, copyright, table of contents, preface, etc.)
- Where the backmatter begins (appendices, bibliography, index)

Copy pages into `pdf/pages/` with the appropriate names. (`pdf/raw-pages/` is the untouched extraction output and must not be modified; `pdf/pages/` is the canonical input for all subsequent stages.)
- `pdf/pages/1.pdf` corresponds to the book's actual page 1
- Frontmatter pages become `pdf/pages/frontmatter-1.pdf`, `pdf/pages/frontmatter-2.pdf`, ...
- Backmatter pages become `pdf/pages/backmatter-1.pdf`, `pdf/pages/backmatter-2.pdf`, ...

**All pages are included** — frontmatter, main content, and backmatter all get entries in `pdf/pages/`. Nothing is discarded.

After copying, write `pdf/pages/mapping.json` recording the raw-page → logical-page correspondence. 

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

Create one GitHub issue per page, so that separate agents handle each page. Use `gh label create transcription --color 0075ca --description "Page transcription work item"` first (ignore error if it already exists). Each issue should:

- Title: `Transcribe page N` for main-content pages; `Transcribe frontmatter-N` or `Transcribe backmatter-N` for frontmatter/backmatter pages
- Body: list the specific input file(s) (e.g., `pdf/pages/42.pdf` or `pdf/pages/frontmatter-3.pdf`), expected output file(s) (e.g., `pages/42.md` or `pages/frontmatter-3.md`), and a dependency on the previous page's issue: `- [ ] depends on #(previous issue number)`
- Label: `transcription`

The dependency chain enforces linear processing so each agent can read the previously transcribed page for context. The first page's issue (frontmatter-1, or page 1 if there is no frontmatter) has no dependency. Order issues following the logical order already established in `pdf/pages/mapping.json`.

Skip the `- [ ] depends on` every 10 pages or so: this will lose some contextual information during the transcription, but allow parallelism.

After creating all issues, verify that every file in `pdf/pages/` is covered by exactly one issue and there are no gaps.

This gives each transcription agent a single, well-scoped task and makes progress visible at page granularity. Partial failures are isolated — a missing page 47 doesn't block the rest.

#### Shared notation conventions

Create `pages/CONVENTIONS.md` before agents start work. Initially it may be sparse (just the book title and subject area). This file is the shared context that keeps transcriptions consistent across parallel agents. 

#### Agent workflow

Each agent assigned to a transcription issue:

1. Reads `pages/CONVENTIONS.md` for established conventions
2. Reads the previously transcribed `.md` file (if any) for style and formatting context
3. Reads the specified PDF page(s) from `pdf/pages/`
4. Writes the corresponding `.md` file(s) with LaTeX math notation, consistent with preceding pages
5. Updates `pages/CONVENTIONS.md` with any new conventions introduced
6. Commits with `Fixes #N` in the commit message (which auto-closes the issue on push)

**Output:** `pages/1.md`, `pages/2.md`, ..., `pages/frontmatter-1.md`, `pages/backmatter-1.md`, etc. Plus `pages/CONVENTIONS.md`.

### Stage 1.5: Transcription Validation

Create issues, assigning 10 pages per issue, and instruct the handling agents to validate that the relevant `pages/*.md` files exist, and are accurate transcriptions of the corresponding pdfs.

Note that this stage may begin before the transcription stage is complete: once batches of pages have been transcribed they can be sent to validation.

### Stage 1.6: Structure Analysis

Create issues, assigning 10 pages per issue, and instruct the handling agents to perform structure analysis of the markdown files for those pages, including looking at any items that start on their final assigned page but continue onto the next page.

Note that this stage can overlap with the transcription validation stage. Once a batch of pages (and the subsequent page, in case of items continuing over pages) has been validated, it can be sent for analysis.

Identify every piece of content in the book and assign it to a blob. The goal is **complete, gap-free coverage**: every character of the transcribed text belongs to exactly one blob.

#### What to identify

**Formally numbered items:**
- Theorems, lemmas, propositions, corollaries
- Proofs of theorems, lemmas, and propositions
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

All item identifiers use the format `{CC}_{NN}_{Type}`, where `{CC}` is the zero-padded chapter number, `{NN}` is the zero-padded item number within the chapter, and `{Type}` is the item kind (e.g., `Theorem`, `Definition`, `Lemma`, `Corollary`, `Discussion`). For some textbooks, it may be appropriate to have three or even four levels of numbers.

The same underscore-separated format is used consistently across all contexts:

| Context | Format | Example |
|---------|--------|---------|
| items.json ID | `Chapter{N}/{CC}_{NN}_{Type}` | `Chapter1/01_02_Definition` |
| Blob filename | `blobs/Chapter{N}/{CC}_{NN}_{Type}.md` | `blobs/Chapter1/01_02_Definition.md` |
| Blob reference | `blobs/Chapter{N}/{CC}_{NN}_{Type}.refs.md` | `blobs/Chapter1/01_02_Definition.refs.md` |
| Lean filename | `{Title}/Chapter{N}/{CC}_{NN}_{Type}.lean` | `Rudin/Chapter1/01_02_Definition.lean` |
| Lean module | `{Title}.Chapter{N}.{CC}_{NN}_{Type}` | `Rudin.Chapter1.01_02_Definition` |

Special items:
- Discussion text between items: `Chapter3/03_02a_Discussion` (letter suffix sorts between `03_02_Definition` and `03_03_Theorem`)
- Chapter introductions (text before the first numbered item): `Chapter3/03_00_Introduction`
- Frontmatter blobs: `Frontmatter/Preface`, `Frontmatter/Notation`, `Frontmatter/TableOfContents`
- Backmatter blobs: `Backmatter/Bibliography`, `Backmatter/Index`

The zero-padded prefix ensures files sort in presentation order rather than grouping by type (which would put all Corollaries before all Definitions, etc.).

> **Lean module names:** Lean 4 accepts module names starting with digits (e.g., `import Rudin.Chapter1.01_02_Definition` works without escaping).

#### Output format

Write `items.json` with an array of items, each having:
```json
{
  "id": "Chapter3/03_01_Theorem",
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

Once all the agents performing structure analysis have merged their PRs, run a **contiguity check** to verify that:
1. Every line of every page markdown file belongs to exactly one blob
2. There are no gaps between consecutive blobs
3. There are no overlaps
4. The blobs, when concatenated in order, reproduce the complete text

If the contiguity check finds problems, either fix them directly or create issues to re-extract the affected items.

### Stage 1.7: Blob Extraction

Create issues to split the page-level markdown into per-blob files based on `items.json`. Aim for roughly 50 blobs per issue; for short chapters, combine several into one issue.

This stage can overlap with Stage 1.6: once a batch of items has passed structure analysis, its blobs can be extracted without waiting for other batches. The contiguity check (above) runs after all items are done and may generate follow-up issues.

**Output:** `blobs/Chapter1/01_01_Definition.md`, `blobs/Chapter1/01_01a_Discussion.md`, ...

**Verify:**
- One blob file per item in `items.json`
- Concatenating all blob files in order reproduces the complete transcribed text

---

## Phase 2: Dependency Mapping

### Stage 2.1: Internal Dependency Analysis

Create issues, each covering roughly 50 blobs. Each agent reads its assigned blobs and notes every internal reference:

- **Explicit references:** "by Lemma 5.6.7", "from Theorem 2.3", "as defined in Definition 1.4"
- **Structural declarations:** "This chapter depends only on Chapters 1 and 2", "We assume familiarity with Chapter 3"
- **Implicit dependencies:** Uses a concept or definition from earlier without citing it

This stage can begin as soon as blobs are extracted (Stage 1.7) for the relevant items. Stages 2.1 and 2.2 can run in parallel on the same batch since they read the same blobs for different purposes.

**Initial assumption:** List only **direct** dependencies — do not store transitive closure. The conservative default is a **linear chain**: each item directly depends only on its immediate predecessor in book order. For example, if items are A, B, C in order: B depends on `["A"]` and C depends on `["B"]` — not `["A", "B"]`. If the text explicitly states independence (e.g., "this chapter does not use Chapter 3"), trim accordingly. We will replace this chain with actual direct dependencies in Stage 3.4.

**File size check:** `internal.json` should have approximately N entries of 0–5 elements each (for N items). If entries grow with item count (e.g., item 100 has 99 entries), you have stored transitive closure — regenerate with direct dependencies only.

**Output:** `dependencies/internal.json` — a mapping from each item ID to a list of item IDs it **directly** depends on.

**Verify:** Every reference target exists in `items.json`.

### Stage 2.2: External Dependency Analysis

Create issues, each covering roughly 50 blobs (matching the Stage 2.1 batches). Each agent identifies mathematical concepts, definitions, and results that its batch assumes but does not prove.

Runs in parallel with Stage 2.1 (same batch can have both agents working simultaneously).

Categorize each:
- **Undergraduate prerequisites:** Linear algebra, basic analysis, group theory basics, etc.
- **Results from other books:** Specific theorems cited from external sources
- **Folklore/well-known facts:** Results stated without proof and without citation

**Output:** `dependencies/external.json` — a list of external dependencies, each with a description, the items that need it, and the category.

### Stage 2.3: Research — Mathlib Coverage

Create issues, each covering roughly 50 blobs. Each agent searches Mathlib for relevant material covering its batch's items and external dependencies.

Can begin as soon as the corresponding Stage 2.1 and 2.2 issues are merged. Stages 2.3 and 2.4 can run in parallel on the same batch.

- Is this definition already in Mathlib? Under what name?
- Is this theorem already proved? At what generality?
- What's the closest Mathlib result, even if not an exact match?

**Output:** `research/mathlib-coverage.json` — mapping items and external deps to Mathlib declarations (with `#check` names).

### Stage 2.4: Research — External Sources

Create issues, each covering roughly 50 blobs. For items and dependencies not covered by Mathlib, each agent searches for:

- **Required packages first.** Check `lakefile.toml` for non-Mathlib `[[require]]` entries. These are the highest-priority external sources — browse their Lean source under `.lake/packages/` to catalog every definition, theorem, and instance they provide. Map each to the items in this project that can use it.
- Other FormalFrontier artifacts that cover this material
- External Lean libraries
- Natural language sources with detailed proofs (useful for formalization agents)

Runs in parallel with Stage 2.3.

**Output:** `research/external-sources.json` — must include an entry for each required package with a full inventory of what it provides and which items benefit.

### Stage 2.5: Formalization Planning Report

Single-agent task. Requires all of Stages 2.1–2.4 to be complete. Prepare a human-readable report summarizing:

- **Suggested formalization order** — which items to tackle first, based on dependencies and difficulty
- **Dependency gaps** — items whose dependencies are not yet in Mathlib or earlier in the book, where we will need to do extra work to build the necessary infrastructure
- **Hardest items** — items that will require the most effort (e.g., developing significant new theory, complex constructions, or proofs that rely on material not covered by existing libraries)

**Output:** `PLANNING.md`

**Note:** This report is informational — do not pause for human review.

### Stage 2.6: Reference Attachment

Create issues, each covering roughly 50 blobs. For each blob that has external dependencies or Mathlib matches, create a companion reference file.

Can begin as soon as the corresponding Stages 2.3 and 2.4 issues are merged — does not need to wait for the planning report (Stage 2.5).

These files are read by formalization agents when they work on the corresponding item, giving them immediate access to relevant Mathlib names, similar theorems, and context.

**Output:** `blobs/Chapter1/01_02_Theorem.refs.md` alongside each blob that has references.

---

## Phase 3: Formalization

Phase 3 is where the bulk of the project happens: every formalizable item needs a Lean file with correct definitions and eventually a complete proof. Each stage is parallelized **per item** via GitHub issues and PRs — one issue per item, one agent per item. Stages can overlap: an item can progress through scaffolding, review, and proof work while other items are still in earlier stages.

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

### Stage 3.1: Lean Scaffolding

The Lean project was created at the repo root by `ff init` in Stage 1.2 and Mathlib was built then. Create `.lean` files for each formalizable item — theorems, definitions, lemmas, and any discussion blob that contains formalizable mathematical claims (characterizations, constructions, non-trivial verifications, named concepts). Discussion blobs that are purely motivational, historical, or set up notation already handled elsewhere can be skipped, but the decision must be explicit: update `progress/items.json` with status `non_formalizable` and a `reason` field.

Scaffolding can begin per-item as soon as that item's Stage 2.6 (reference attachment) is merged — it does not need to wait for all of Phase 2 to complete.

#### Setup

The orchestrating agent creates the file structure and then creates issues for worker agents:

1. Create the skeleton: root file `{Title}.lean` importing all chapter files, chapter files `{Title}/Chapter1.lean` importing all items in the chapter. Commit this to `main`.
2. Create `gh label create scaffolding --color 1d76db` (ignore error if exists).
3. **Assess discussion blobs.** For each discussion-type item in `items.json`, read the blob and determine whether it contains formalizable mathematical claims (characterizations, constructions, named concepts, non-trivial verifications). The assessor must list every candidate mathematical claim in the blob and classify each as formalizable or not, with a reason for each exclusion. If any claim is formalizable, the blob gets a scaffolding issue like any other item. If no claim is formalizable, update `progress/items.json` with status `non_formalizable` and a `reason` field that includes the enumerated claims and why each was excluded. `non_formalizable` assessments are subject to Stage 3.2 review — a reviewer must verify the claim enumeration is complete and the exclusion reasons are sound.
4. Create one issue per item (including discussion items assessed as formalizable in step 3):
   - Title: `Scaffold <ItemID>`
   - Body: link to the blob file, the item's entry in `research/mathlib-coverage.json` and `research/external-sources.json`
   - Label: `scaffolding`

#### Agent workflow

Each agent assigned to a scaffolding issue:
1. Reads the blob file for its item
2. Reads `research/mathlib-coverage.json` and `research/external-sources.json` for Mathlib API references and other background
3. **Checks required packages.** For each non-Mathlib `[[require]]` in `lakefile.toml`, search `.lake/packages/<name>/` for definitions and theorems relevant to this item. If a concept is already formalized there, use `recall` or import it directly — do not re-define it.
4. Creates the `.lean` file following the conventions below
5. Submits a PR with auto-merge enabled (see PR lifecycle above)

#### Import chain

Each item gets its own file:
- Root file: `{Title}.lean` importing all chapter files
- Chapter files: `{Title}/Chapter1.lean` importing all items in the chapter
- Item files: `{Title}/Chapter1/01_01_Theorem.lean`

Lean filenames use the same `{CC}_{NN}_{Type}` convention as item IDs (see Identifier scheme in Stage 1.6).

#### Definitions vs. theorems: the critical distinction

**Definitions (`def`, `noncomputable def`, `instance`, `abbrev`) must have real bodies — never `sorry`.** A sorry'd definition spoils all subsequent scaffolding. 

**Only theorem/lemma proofs may use `sorry`.** Propositional subterms within a definition (e.g., a proof obligation in a `where` clause or `Subgroup.mk`) may also use `sorry`, since the *data* part of the definition is still constructed. 

Bad (definition-level sorry — the object does not exist):
```lean
noncomputable def myMetricSpace (X : Type*) : MetricSpace X := sorry
```

Good (definition with proof obligation sorry'd — all the data is provided):
```lean
def evenIntegers : AddSubgroup ℤ where
  carrier := {n | 2 ∣ n}
  add_mem' := sorry  -- data is constructed, only proofs deferred
  zero_mem' := sorry
  neg_mem' := sorry
```

Good (theorem-level sorry — the statement is meaningful, proof deferred):
```lean
/-- **Bolzano-Weierstrass.** Every bounded sequence in ℝ has a convergent subsequence. -/
theorem bolzano_weierstrass {s : ℕ → ℝ} (hb : Bornology.IsBounded (Set.range s)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ L, Filter.Tendsto (s ∘ φ) Filter.atTop (nhds L) := by
  sorry
```

Writing definitions is the hardest part of scaffolding. If a definition requires significant research into the API of Mathlib or another library, or careful mathematical design, that work must happen here — not be deferred with a `sorry`.

#### Items already in Mathlib: use `recall` and `example`, not wrapper definitions

Many textbook items (definitions, theorems, examples) correspond directly to existing Mathlib declarations. **Do not create wrapper definitions or synonym theorems for these.** Instead, use Mathlib's `recall` command (from `Mathlib.Tactic.Recall`) to document the correspondence, and `example` to demonstrate instances.

`recall` redeclares an existing Mathlib definition for expository purposes. It verifies the name and type match the original, without creating a new declaration or polluting the namespace.

**For definitions that exist in Mathlib** — use `recall` with a doc-comment explaining the textbook correspondence:
```lean
import Mathlib.Tactic.Recall
import Mathlib.RingTheory.LocalRing.Basic

/-- **Definition 1.12.** A *local ring* is a nontrivial ring where `a + b = 1` implies
`a` or `b` is a unit. -/
recall IsLocalRing (R : Type*) [Semiring R] : Prop
```

**For theorems that exist in Mathlib** — use `recall` to show the statement:
```lean
/-- **Theorem 1.8** (Ostrowski). Every nontrivial absolute value on `ℚ` is equivalent
to the real absolute value or to a `p`-adic absolute value for a unique prime `p`. -/
recall Rat.AbsoluteValue.equiv_real_or_padic (f : AbsoluteValue ℚ ℝ)
    (hf : f.IsNontrivial) :
    f.IsEquiv Rat.AbsoluteValue.real ∨
    ∃! p : ℕ, ∃ _ : Fact p.Prime, f.IsEquiv (Rat.AbsoluteValue.padic p)
```

**For results that follow from Mathlib's instance system** — use `example`:
```lean
/-- **Proposition 1.22.** `ℤ` is integrally closed. -/
example : IsIntegrallyClosed ℤ := inferInstance
```

`recall` can include the full signature or just the name (`recall IsLocalRing`). Include the signature when it's pedagogically helpful — it shows the reader exactly what Mathlib provides. You can also use `recall? IsLocalRing`, which will provide a "Try this:" suggestion showing a `recall` suggestion with the full correct type. Using `example` is also a reasonable alternative to `recall`, if you have a good reason for writing the signature differently.

Bad (creates a useless synonym that clutters the namespace):
```lean
def IsLocalRing' (A : Type*) [CommRing A] : Prop := IsLocalRing A

theorem ostrowski (f : AbsoluteValue ℚ ℝ) (hf : f.IsNontrivial) :=
  Rat.AbsoluteValue.equiv_real_or_padic f hf
```

The module docstring (`/-! ... -/`) should still explain the textbook item, its mathematical content, and the Mathlib correspondence. The `recall`/`example` then serves as the machine-checked evidence that the correspondence is correct.

> **`recall` covers a single Mathlib declaration, not an entire blob.** If a blob introduces concept X and Mathlib has `X` under name `Y`, then `recall Y` covers that ONE claim. But if the blob also defines concept Z, states theorem W, and constructs object Q, those need separate Lean declarations. Read the blob sentence by sentence — each mathematical claim needs its own line item in the .lean file.
>
> **Watch for non-trivial equivalences.** If the textbook defines concept X one way and Mathlib defines it a different (equivalent) way, the equivalence itself is a mathematical claim that should be formalized as a `theorem`, not silently glossed over by the `recall`. Example: the textbook defines a DVR as "the valuation ring of a discrete valuation on Frac(A)" while Mathlib defines it as "a local PID that is not a field" — the equivalence is a substantive theorem that must appear in the .lean file.
>
> **Use your own definitions.** If you define a concept from the book (e.g., `AbsoluteValue.AreEquivalent`), you must use that definition in subsequent results that refer to it. Do not define the book's version and then silently switch to a different Mathlib notion (e.g., `IsEquiv`) in later theorems. Either use the book's definition and prove the equivalence, or don't define it at all.
>
> **Formal statements must match the book.** When formalizing a theorem statement, each condition must correspond to what the book actually says — do not substitute a logically equivalent but differently-phrased condition without an explicit bridging lemma. If the book says "regular noetherian local ring of dimension one", the Lean statement must express regularity and dimension one, not silently replace them with a different equivalent characterization.
>
> **Use consistent representations.** When the book poses mathematically analogous problems (e.g., "show ℤ[√5] is not integrally closed" and "show (1+√7)/2 is not integral over ℤ"), use the same Lean representation for both (e.g., both as `Zsqrtd`, or both as subrings of ℝ). Inconsistent choices make the formalization harder to read and maintain.

Each item file should contain:
- A doc-string with the natural language statement from the book
- Appropriate imports from earlier items or library dependencies
- For definitions already in Mathlib: `recall` with a doc-comment (no new definitions)
- For theorems already in Mathlib: `recall` with a doc-comment (no wrapper theorems)
- For instances already in Mathlib: `example ... := inferInstance`
- For definitions not in Mathlib: a full construction (proof obligations within the definition may use `sorry`). Auxiliary definitions may be needed, which should happen during scaffolding.
- For theorems/lemmas not in Mathlib: a sorry'd proof with the precise Lean statement

#### Coverage completeness (mandatory)

**Every new mathematical claim in the blob must have a corresponding Lean declaration in the .lean file.** A single `recall` does not "cover" a blob that contains five distinct concepts. Read the blob sentence by sentence and ensure each claim is addressed:

- Defines a new mathematical object → needs a `def`, `recall`, or `example`
- States a new mathematical fact (theorem, lemma, characterization, equivalence) → needs a `theorem`, `lemma`, `recall`, or `example`
- Constructs a mathematical object from another (e.g., "defining |x|_v := c^{v(x)} yields a nonarchimedean absolute value") → needs a `def` + `theorem`
- Introduces a named concept not already formalized (e.g., "value group", "discrete valuation") → needs a `def`, `abbrev`, or `recall`

A "claim" is a sentence that introduces a new concept, statement, construction, or equivalence — not a restatement of something already established. Claims already formalized in an earlier item's .lean file can be satisfied by importing that item and adding a comment citing the declaration, rather than duplicating it locally.

If a claim cannot be formalized yet (e.g., requires infrastructure not currently available), add a `-- TODO: <claim from blob>` comment in the .lean file **and** create a GitHub issue for it. The item's status remains `needs_definition` until all TODO comments are resolved — visible incompleteness is better than silent omission, but it does not pass scaffolding review.

**Example — bad vs. good coverage for a definition blob with ~8 claims:**

Bad (3 recalls for a blob defining valuations, value groups, discrete valuations, valuation rings, DVRs, and the construction of absolute values from valuations):
```lean
recall AddValuation ...
recall IsDiscreteValuationRing ...
recall ValuationRing ...
```

Good (every claim in the blob is addressed):
```lean
-- Valuation as group homomorphism with ultrametric inequality
recall Valuation (k : Type*) [DivisionRing k] (Γ₀ : Type*) ...

-- Value group: image of valuation in the target group
recall Valuation.ValueGroup ...   -- or def if not in Mathlib

-- Discrete valuation: value group isomorphic to ℤ
def IsDiscreteValuation ... -- or recall if in Mathlib

-- Construction: valuation → nonarchimedean absolute value via c^{v(x)}
noncomputable def Valuation.toAbsoluteValue ... := ...
theorem Valuation.toAbsoluteValue_isNonarchimedean ...

-- Valuation ring
recall ValuationRing ...

-- DVR: integral domain that is valuation ring of discrete valuation on Frac(A)
recall IsDiscreteValuationRing ...
-- Note: Mathlib defines DVR as local PID + not a field;
-- equivalence with "valuation ring of a discrete valuation" is:
recall DiscreteValuationRing.TFAE ...  -- or theorem if not in Mathlib
```

**Output:** `{Title}/Chapter1/01_01_Theorem.lean`, etc.

**Verify:** `lake build` succeeds (everything compiles with sorries).

### Stage 3.2: Scaffolding Review

Before beginning proof work (Stage 3.3) on an item, a separate verification issue must be created so a different agent can review the scaffolding skeptically. This gate helps prevent mis-formalizations and definition-level sorries.

Can begin per-item as soon as that item's scaffolding (Stage 3.1) is merged.

The review agent should update `progress/items.json` with the status transition, and submits a PR with any fixes. The review must perform an explicit **coverage audit**, included in the PR body as a checklist:

1. **Enumerate claims:** List every new mathematical claim in the blob — definitions, theorems, constructions, characterizations, named concepts. A "claim" is a sentence that introduces a new concept, statement, construction, or equivalence not already formalized in an earlier item. Mere restatements of earlier definitions or informal motivational sentences are not claims.
2. **Map to Lean:** For each claim, identify which Lean declaration in the .lean file addresses it. A claim formalized in an earlier item's .lean file can be satisfied by importing that item and citing the declaration — no local duplication needed.
3. **Flag gaps:** Any claim without a corresponding Lean declaration is a coverage gap. The review **fails** if any gap exists. Every gap must be resolved by adding a Lean declaration. If a claim cannot be formalized yet, the item remains at `needs_definition` with a GitHub issue — `-- TODO` comments are acceptable as markers but do not satisfy the coverage audit.
4. **Check non-trivial equivalences:** Whenever the textbook wording and the recalled Mathlib declaration are not definitionally equal (after unfolding notation), the .lean file must contain an explicit bridging `theorem` or a review note explaining why no bridge is needed (e.g., the definitions unfold to the same thing).
5. **Check definition integrity:** No *data* is sorried, only proof obligations.

The coverage audit checklist must appear in the review PR body so it is permanently visible, not performed only mentally.

The agent may create new issues if problems with the data scaffolding are discovered: sometimes getting definition right can be difficult, and may require large excursions to set up preliminary material, which may even not be explained in the book, or available in Mathlib. Do the research, and get it done anyway!

#### Status transitions

After Stage 3.2 review:
- Items that pass → status `definition_verified` (for both definitions and theorems)
- Items that fail → status `needs_definition`, with a GitHub issue created

### Stage 3.3: Formalization Work Loop

Orchestrate agents to formalize items, one issue per item. Proof work on an item can begin as soon as it passes scaffolding review (Stage 3.2).

#### Formalization guidance

- **Read the book's proof first (mandatory).** Before attempting any proof, read the blob file (`blobs/<Chapter>/<Item>.md`) for the theorem you're proving. Remember that the proof itself is likely to be in separate blob from the statement. The book contains the proof strategy — follow it. Do not invent your own proof approach from mathematical knowledge. The book's approach is chosen to build on earlier results in the book, which are the results available to you.
- **Follow the book's dependency chain.** If the book says "the result follows from Lemma X.Y.Z", find that lemma in the project and use it in your proof — even if it still has a `sorry`. A sorry'd dependency is not a blocker. Never conclude that a proof is "blocked on missing Mathlib infrastructure" when the book's proof uses an earlier result from the same book.
- **"Not in Mathlib" is not a blocker.** This project exists to formalize what isn't in Mathlib. If the book's proof requires a result that isn't in Mathlib, check whether it's an earlier item in the book (it usually is). If it genuinely requires external mathematics not covered by the book or Mathlib, prove it here — that's just more work, not a blocker. If you exhaust the book's own proof path and Mathlib, then create research issuess to read the informal literature and begin formalizing the missing material too.
- **Push sorries earlier:** Work top-down. If the proof of a theorem is currently `sorry`, you can replace this with the intended structure of the proof, even if some subsidiary steps are still `sorry` for now. Don't waste time on proving helper lemmas until you know they're needed, because you've used them in high level proofs later.
- **Spec-driven development:** Use sorry placeholders with comments explaining what's needed, not `True` or other cheats.
- **Pre-formalization:** For complex items, first translate the natural language blob into a pedantic, detailed version with careful references to every fact used, before attempting formalization.

#### Agent workflow

Each agent is assigned a task (an item or small group of related items). The agent either:
1. **Submits a PR** that fully or partially resolves the task (with auto-merge enabled)
2. **Escalates by posting multiple issues** documenting a proposed decomposition into more manageable tasks. These may include doing further research, either within the book (for more proof details, or prerequisites earlier in the book), or in Mathlib, or other informal or formal sources.

#### Task selection

Once Stage 3.2 is complete, all statements and definitions are verified. Agents should prioritize the hardest, most impactful items, not items with the easiest dependency graphs.

Task selection criteria (in priority order):
1. Items that unblock the most downstream work (high fan-out in the dependency DAG)
2. Items assessed as mathematically hardest (from health check or summarize reports)

Status updates are tracked in `progress/items.json`. Non-formal nodes (discussion, external dependencies) are also tracked there.

#### Escalation policy: the `blocked` label

**`blocked` means blocked on another issue in *this* repository** — never on missing
external infrastructure. This project is responsible for formalizing the book in full.

Before applying `blocked`:
1. **Read the book's proof** in the blob file (`blobs/<Chapter>/<Item>.md`). Identify
   which earlier results the proof cites — these are your actual dependencies. Check
   whether those earlier items exist in the project and whether they have sorries.
2. **Decompose** the problem into sub-tasks matching the book's proof structure, create
   issues for each, link with `- [ ] depends on #X`, then mark the original blocked on
   those issues.
3. **If you can't decompose**, research the informal literature first (textbooks,
   surveys, lecture notes) to find a proof strategy, then decompose.
4. **If a result isn't in Mathlib**, prove it here — that's just more work, not a blocker.
   The book's proof almost certainly uses results from earlier in the book. Check there
   first.

#### Triage

Specialized triage agents should periodically review open issues for:
- Definition correctness problems (wrong definition, insufficient generality)
- Missing low-level API lemmas needed across multiple items
- Dependency ordering mistakes
- Opportunities for useful tactics or metaprograms

#### Periodic status check (every 50 merged PRs)

After every 50 merged PRs, a review agent must perform a status check. This prevents the work loop from drifting — agents have tendency to pick the easy work and defer the hardest parts. Status checks that identify remaining work without producing GitHub issues are wasted — the issues are the primary deliverable, not the report.

The status check must:

1. **Scan for definition-level sorries (regression check).** Re-run the Stage 3.2 scaffolding check. New definition-level sorries can be introduced during proof work when agents create helper definitions with sorry bodies. Any found must become issues — these are the highest priority, since they make downstream theorem statements vacuous.

2. **Identify the hardest remaining items.** This is a mathematical assessment, not just a sorry count. For each chapter with remaining work, identify the items that are hardest to complete, considering:
   - Mathematical depth and complexity (e.g., developing significant theory vs a routine calculation)
   - Dependency chains (items that unblock many others)
   - Whether the book's proof strategy requires infrastructure not in Mathlib
   For each, create or update a GitHub issue with a difficulty assessment, a decomposition into sub-tasks, and concrete next steps.

3. **Identify neglected items.** List all items with remaining sorries that have had zero PRs and zero issues across recent waves. For each, determine why and create an issue if none exists.

4. **Check work distribution.** Count PRs per chapter over recent waves. If any chapter with remaining sorries has received disproportionately little attention, flag it and create targeted issues for its hardest items.

5. **Update `progress/items.json`** to reflect the current state, especially items whose status has changed but weren't updated.

6. **Create actionable issues.** Every finding from steps 1-4 that doesn't already have a GitHub issue must result in a new issue. Before creating an issue, search open issues for the item ID to avoid duplicates.

**Counting PRs:** Count merged PRs since the last status-check issue was closed. Use `gh pr list --state merged` with a date filter based on the close date of the last `status-check` labeled issue.

**Output:**
- `progress/summaries/status-check-wave-N.md` with the analysis
- GitHub issues for every actionable finding (labeled `status-check`)

**The status check is mandatory, not optional.** A planner must schedule it. If no status check has been performed after 50 PRs, the next planner must schedule one before creating new proof work items.

### Stage 3.4: Dependency Trimming (post-formalization)

Create one issue per item. Once an item has a sorry-free proof, analyze its actual dependencies by reviewing the proof terms and imports.

Can begin per-item as soon as the item is sorry-free — does not need to wait for all formalization to complete. Overlaps with the Stage 3.3 work loop on other items.

Compare the actual dependencies against `dependencies/internal.json`:
- Which initial dependencies turned out to be unnecessary?
- Are there unexpected dependencies that weren't in the original analysis?
- Does the actual dependency structure reveal anything interesting about the book's organization?

This is when we learn the true dependency structure of the book, which may differ significantly from the conservative initial assumption.

**Output:** Updated `dependencies/internal.json` reflecting actual dependencies.

### Stage 3.5: Proof Polishing

Polish sorry-free proofs to Mathlib quality standards. This is a cleanup pass — the proofs work, but may be verbose, use suboptimal tactics, or not follow Mathlib conventions.

Can begin per-item as soon as that item's dependency trimming (Stage 3.4) is complete.

#### Setup

Create `gh label create proof-polish --color c5def5` (ignore error if exists). Create one issue per item:
- Title: `Polish <ItemID>`
- Label: `proof-polish`

#### Agent workflow

Each agent assigned to a proof-polish issue:

1. Reviews the sorry-free proof
2. Applies cleanup:
   - Combine redundant steps (`rw [a]; rw [b]` → `rw [a, b]`)
   - Replace verbose tactic sequences with more powerful single tactics where appropriate
   - Remove unnecessary intermediate steps (test by deleting and checking if the proof still works)
   - Ensure `simp` calls use minimal lemma sets where practical
   - Follow Mathlib naming conventions and style
3. Verifies the polished proof still compiles
4. Submits a PR with auto-merge enabled

#### Status transitions

After polishing: items move from `dependency_trimmed` → `proof_polished` in `progress/items.json`.

**Output:** Polished `.lean` files. Updated `progress/items.json`.

**Verify:** All previously sorry-free items have status `proof_polished`. `lake build` succeeds.

### Stage 3.6: Upstreaming Analysis

Identify formalized results that may be worth contributing to Mathlib. The output is a non-binding `UPSTREAMING.md` report — no actual upstreaming happens here.

Can begin per-item as soon as that item's proof is polished (Stage 3.5). Create one issue per item for the triage and research below.

#### Phase 1: Lightweight triage

Scan all proof-polished items. Reject immediately if the proof is a one-liner delegating to a named Mathlib theorem, or trivial glue between two or three existing Mathlib facts. Keep as candidate if the proof is substantive and the result appears absent from Mathlib's API.

#### Phase 2: Deep Mathlib research

For each candidate, search the **local Mathlib source** (`.lake/packages/mathlib/`) for closely related results — do not rely on web searches or AI knowledge of Mathlib, which may be out of date. Check for equivalent results under different names, close relatives that make the candidate a straightforward corollary, and proof approaches that reconstruct something Mathlib already proves elsewhere. Open one GitHub issue per candidate to track the research.

Assign one of three verdicts:

- **Reject — already in Mathlib:** Create a GitHub issue to refactor the proof to use the Mathlib declaration directly, and set `upstreaming_status` to `mathlib_covered`.
- **Reject — insufficient interest:** Too narrow, not at Mathlib quality/generality, or not a good fit.
- **Refactor - we can write a better proof based on our research**.
- **Include in UPSTREAMING.md:** Genuinely new to Mathlib, correct, and at appropriate generality.

#### Output

Write `UPSTREAMING.md` at the repository root. For each included candidate: the item ID, Lean declaration name, file path, Lean statement, why it's new (what was searched, what was found), and suggested Mathlib module. For excluded items: one-line reason each.

Update `progress/items.json` with `"upstreaming_status"`: `"candidate"`, `"mathlib_covered"`, or `"rejected"`.

**Verify:** `UPSTREAMING.md` exists. Every proof-polished item has an `upstreaming_status` in `progress/items.json`.

---

## Progress Tracking

### Per-turn progress files: `progress/YYYY-MM-DDTHH-MM-SSZ.md`

At the end of every agent turn, write a timestamped progress file in `progress/`. Use the current UTC time for the filename (e.g., `progress/2026-03-15T14-30-00Z.md`). This gives a full audit trail of what each agent did and decided, and reliably onboards subsequent agents.

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

`PROGRESS.md` may be maintained as a human-facing summary of stage completion. It is not the primary source of truth — the per-turn files are. 

```markdown
## Stage 1.1: Page Extraction
**Status:** Complete
**Date:** 2026-03-15 12:34
**Notes:** 342 pages extracted.

## Stage 1.2: Start Lean Build
**Status:** Complete
**Date:** 2026-03-15 15:43
**Notes:** Mathlib downloaded and built successfully.

## Stage 1.3: Frontmatter Detection
**Status:** Complete
**Date:** 2026-03-15 21:21
**Notes:** Page 1 starts at raw page 13. Backmatter from raw page 298. See `pdf/pages/mapping.json` for the full raw-page → logical-page mapping.
```

### Item-level progress: `progress/items.json`

Item statuses flow through:
`identified` → `extracted` → `scaffolded` → `definition_verified` → `proof_formalized` → `sorry_free` → `dependency_trimmed` → `proof_polished`

Each status is set by a specific stage:

| Status | Set by | Trigger |
|--------|--------|---------|
| `identified` | Stage 1.6 | Item added to `items.json` |
| `extracted` | Stage 1.7 | Blob file created |
| `scaffolded` | Stage 3.1 | `.lean` file created and compiles |
| `definition_verified` | Stage 3.2 | Scaffolding review passes |
| `proof_formalized` | Stage 3.3 | Proof work submitted (may still contain sorries) |
| `sorry_free` | Stage 3.3 | All sorries removed from the item's `.lean` file |
| `dependency_trimmed` | Stage 3.4 | Actual dependencies analyzed and recorded |
| `proof_polished` | Stage 3.5 | Proof cleaned up to Mathlib quality |

Special statuses (set during review):
- `needs_definition` — the item has a definition-level sorry or coverage gap that must be resolved before downstream theorems are meaningful
- `attention_needed` — requires specialized agent attention (e.g., wrong statement, repeated failures)
- `non_formalizable` — discussion blob assessed as containing no formalizable claims (must include enumerated claims and exclusion reasons; subject to Stage 3.2 review; terminal status if review confirms)

```json
{
  "Chapter1/01_01_Theorem": {
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
