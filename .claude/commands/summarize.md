# Execute a Summarize Work Item

You are a **summarize** session. Your job is to produce an accurate summary of
project progress that honestly identifies both achievements and limitations.

**First, read the `agent-worker-flow` skill** for the standard
claim/branch/verify/publish workflow. This document only covers what is specific
to summarize sessions.

## Claiming Your Issue

Use `coordination list-unclaimed --label summarize` to find work for this session type.

## The Summary Task

### Step 1: Read the project specification

Find and read the top-level specification/roadmap document to understand the
project's intended goals. This is the ground truth against which you measure progress.

### Step 2: Read the current progress document

Understand what the project currently claims to have achieved.

### Step 3: Survey recent work

- Read the last 15 entries in `progress/` (sorted by filename, most recent last)
- Fetch titles of PRs merged since the last `summarize` issue was closed

### Step 4: Inspect the codebase

- List source files and read their module-level docstrings
- Read key top-level declarations/signatures (not full implementations)
- Record current quality metrics as described in the project's CLAUDE.md

### Step 5: Produce an updated progress document

Write an updated progress document that:

- **Accurately reflects** current quality metrics and phase
- **Describes the architecture structurally** (layers, relationships)
- **Identifies flaws and limitations honestly** (scope restrictions,
  remaining work, gaps between goals and achievements)
- **Is honest in its framing** — don't overstate what has been achieved

## Sorry Counting

Lean files contain `sorry` in both code and comments/docstrings. To get accurate
counts, you must distinguish actual `sorry` tactics/terms from comment mentions
like "sorry'd", "currently sorry", etc.

**Recommended approach:** Use grep to find all `sorry` mentions, then manually
verify any file where the count differs from the previous wave. Common false
positives:
- `sorry'd` in docstrings and block comments (`/- ... -/`)
- `"sorry"` in string literals or comment text like "1 sorry in ..."
- Inline comments after code: `-- ... sorry ...`

A simple first pass: `grep -rn '\bsorry\b' --include='*.lean'`, then for each
file, inspect the matching lines to separate code sorries from comment mentions.
Don't trust automated filtering alone — wave-over-wave deltas catch errors.

## Constraints

- Do NOT modify any code or implementation files
- Commit ONLY the progress document changes
- The progress entry should note what changed and why

## Reflect

Run `/reflect` before finishing.
