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

### Definitions Must Be Constructed
**Never sorry the body of a `def`, `noncomputable def`, `instance`, or `abbrev`.** A sorry'd definition means the mathematical object does not exist — any theorem referencing it is vacuous. Proof obligations *within* a definition (e.g., `where` clauses) may use sorry, but the data itself must be real. See Stage 3.1 in PLAN.md for details and examples.

### Discussion Blobs Are First-Class
During structure analysis (Stage 1.5), unstructured text between numbered items must be identified and tracked just like theorems and definitions. These discussion paragraphs carry context that proofs depend on. Every byte of the book must belong to exactly one blob.

### Conservative Dependencies
Store only **direct** dependencies. The conservative default is a linear chain: each item depends only on its immediate predecessor. Never store transitive closure — that creates an O(N²) file with no useful information. We trim to actual direct dependencies later (Stage 3.4) once proofs exist.

## When Stuck

### Read the book first (mandatory)

**Before attempting any proof**, read the blob file for the item (`blobs/<Chapter>/<Item>.md`). The book contains the proof strategy — follow it. Do not invent your own proof approach from mathematical knowledge.

If the book's proof says "by Lemma X.Y.Z" or "the result follows from [earlier result]":
1. Find that earlier result in the project (search `blobs/` and the Lean files)
2. Use it in your proof — even if it still has a `sorry`. A sorry'd dependency is not a blocker.

**Never say "not in Mathlib" without first checking the book.** The book's proofs build on earlier results in the book. Those results are what you should be using — not searching Mathlib for advanced infrastructure like Schur functors or Schur-Weyl duality when the book uses an elementary lemma from the previous page.

### Escalation ladder

- **3 failed attempts on any sub-task** (proof, definition construction, statement formalization): document in a GitHub issue and move on
- **Dependency blocked:** Post an issue with `- [ ] depends on #X` and add the `blocked` label — but only for *definition-level* blockers, never for proof-level sorries
- **Definition seems wrong:** Post an issue describing the problem — don't silently work around bad definitions
- **Definition-level sorry found:** This is highest priority. The mathematical object must be constructed — see "Definitions Must Be Constructed" above. Create an issue and fix it before proving downstream theorems.
- **Missing Mathlib API:** First check whether the missing result is an earlier item in the book. If it is, that's a dependency, not a missing Mathlib API. If genuinely missing from Mathlib, **prove it here** — that's the highest-priority work, not a reason to defer. This project exists to formalize what isn't in Mathlib.
- **Ordering mistake in the plan:** Report it — request a replan rather than hacking around it

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
