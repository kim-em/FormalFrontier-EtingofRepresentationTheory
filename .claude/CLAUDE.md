# FormalFrontier Book Formalization Harness

This repository is a formalization of a mathematics textbook using the FormalFrontier pipeline.

## How to Work

1. Read the most recent file in `progress/` (sorted alphabetically) — this is your onboarding document
2. Read `PLAN.md` for the full pipeline description and stage details
3. Work on the next incomplete stage
4. For item-level progress, update `progress/items.json`
5. At the end of every turn, write `progress/<UTC-timestamp>.md` with Accomplished, Current frontier, Overall project progress, Next step, and Blockers

## Key Principles

### Top-Down Development
Push sorries earlier. State the theorem first, sorry the proof, then fill in. Don't waste time on helper lemmas until you know they're needed by the main result.

### Spec-Driven Development
Use `sorry` placeholders with comments explaining what's needed. Never use `True` as a placeholder for propositions — it hides the actual requirements and will need a full refactor to fix.

### Discussion Blobs Are First-Class
During structure analysis (Stage 1.5), unstructured text between numbered items must be identified and tracked just like theorems and definitions. These discussion paragraphs carry context that proofs depend on. Every byte of the book must belong to exactly one blob.

### Conservative Dependencies
Store only **direct** dependencies. The conservative default is a linear chain: each item depends only on its immediate predecessor. Never store transitive closure — that creates an O(N²) file with no useful information. We trim to actual direct dependencies later (Stage 3.3) once proofs exist.

## When Stuck

- **3 failed proof attempts**: escalate the proof to Aristotle (see below), then if that also fails, document in a GitHub issue and move on
- **3 failed attempts on a non-proof sub-task** (definitions, statement formalization): skip it, document in a GitHub issue, move on (Aristotle only handles proofs)
- **Dependency blocked:** Post an issue with `- [ ] depends on #X` and add the `blocked` label
- **Definition seems wrong:** Post an issue describing the problem — don't silently work around bad definitions
- **Missing Mathlib API:** Post an issue describing what's needed; another agent or human can add it
- **Ordering mistake in the plan:** Report it — request a replan rather than hacking around it

## Aristotle Escalation

Aristotle is an automated theorem prover. Escalate to it when Claude can't prove a theorem after 2-3 serious attempts.

### When to use Aristotle

- A proof is beyond Claude's ability after multiple attempts
- Standard mathematical proofs (calculus, algebra, analysis) that follow well-known patterns
- Batch proving: after Stage 3.1 scaffolding, submit all sorry'd theorems

### When NOT to use Aristotle

- Statement formalization (translating definitions/theorem statements from natural language) — Claude handles this
- When the formalized statement might be wrong — fix the statement first
- For discussion blobs or non-theorem items

### Handoff protocol

1. Create a temporary copy of the item's Lean file (preserving all imports, namespaces, notation). Keep exactly one `sorry` (the target proof); change all others to `admit`.
2. Gather context files: sorry-free local Lean files from the import chain (skip Mathlib imports). If no local files are sorry-free yet, submit with no context files.
3. Submit: `aristotle prove-from-file item_pending.lean --no-wait --no-auto-add-imports --context-files ...`
4. Record the project ID in `progress/items.json` with status `sent_to_aristotle`
5. Delete the temp file — never commit `admit`

**Deduplication:** Before submitting, check that the item is not already in `sent_to_aristotle` status. Only one submission per item at a time.

### After Aristotle returns

- **Success:** Verify the proof compiles (`lake env lean`), copy into the item's Lean file, update status to `sorry_free` (if all sorries resolved) or `proof_formalized`
- **False statement:** Mark `attention_needed`, post a GitHub issue with the counterexample — the formalized statement needs fixing
- **Failure/timeout/version mismatch:** Mark `attention_needed`, move on

## Blueprint Tooling

The blueprint uses a hybrid of **leanblueprint** (rendering, full DAG) and **LeanArchitect** (external extraction).

- **leanblueprint** owns the complete dependency graph — formal declarations and non-formal content (discussion, introductions, external deps)
- **LeanArchitect** runs externally with `extract_blueprint --all` against compiled `.olean` files — automates dependency inference and sorry detection. No `require`, `import`, or attributes needed in the Lean source.
- Non-formal nodes use leanblueprint's LaTeX macros (`\uses{}`, `\leanok`) directly

### Querying the blueprint

From the `lean/` directory, after `lake build`:

```bash
# Extract JSON for a single module
lake env /path/to/LeanArchitect/.lake/build/bin/extract_blueprint \
  single --all --json --build .lake/build MyProject.Chapter1.Theorem1
```

The `lake env` wrapper sets `LEAN_PATH` so the extractor can find `.olean` files. LeanArchitect is built separately — it is NOT a dependency of this project.

- `leanblueprint web` — visual HTML dependency graph for all nodes

### Finding ready work

Query the extracted JSON for nodes where:
- The node still contains `sorry` (not yet proved)
- All dependency nodes are sorry-free (prerequisites are done)

These nodes are ready for formalization. Status updates are automatic — removing a `sorry` and recompiling updates the extraction output.

## PR Workflow

### Submitting PRs

When you complete work on a formalization item, create a PR and immediately enable auto-merge so it merges to `main` without human intervention once CI passes:

```bash
gh pr create --title "Formalize <ItemID>" --body "..."
PR_NUM=$(gh pr view --json number --jq .number)
gh pr merge "$PR_NUM" --auto --squash
```

### Merging ready PRs (start of every planning cycle)

**Before selecting new work**, merge all open PRs that are mergeable and have no failing CI checks. This unblocks downstream agents waiting on `main`.

```bash
gh pr list --state open \
  --json number,mergeable,statusCheckRollup \
  --jq '.[] | select(
    .mergeable == "MERGEABLE" and
    (.statusCheckRollup | all(.conclusion != "FAILURE" and .conclusion != "CANCELLED"))
  ) | .number' \
| xargs -I{} gh pr merge {} --squash --delete-branch
```

Never skip this step. Downstream agents are blocked on `main` until merged PRs land.

## Progress Tracking

- **Per-turn handoff files:** `progress/YYYY-MM-DDTHH-MM-SSZ.md` (UTC timestamp)
- Stage-level summary: `PROGRESS.md` (optional, human-facing)
- Item-level: `progress/items.json`
- Blueprint status: automatic via LeanArchitect (sorry detection)
- Do NOT modify `PLAN.md` — it is the reference plan
- Blockers and discussion: GitHub issues

### Writing a progress file (mandatory at end of every turn)

At the end of every turn, before handing off, write `progress/<UTC-timestamp>.md` using this template:

```markdown
## Accomplished
<!-- What was done this turn -->

## Current frontier
<!-- Where work stopped -->

## Overall project progress
<!-- High-level status (which stages are complete, how many items formalized, etc.) -->

## Next step
<!-- Concrete recommendation for the next agent -->

## Blockers
<!-- Anything blocking forward progress; empty if none -->
```

Use the current UTC time as the filename (e.g., `progress/2026-03-15T14-30-00Z.md`). Any commits made during the turn should mention the progress file in the commit message.

### Starting a turn (mandatory)

At the start of every turn, read the most recent file in `progress/` (sorted alphabetically = chronologically). This is your primary onboarding document. Then read `PLAN.md` for stage details as needed. If `progress/` contains only `progress/0000-init.md` (or no handoff file), the repo is freshly initialized — proceed with Stage 1.1.

**Before the first `lake build` of any session**, always run:
```bash
lake exe cache get
```
This downloads pre-built Mathlib oleans and avoids a full rebuild (1800+ jobs). Skipping this wastes significant time and compute.
