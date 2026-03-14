# FormalFrontier Book Formalization Harness

This repository is a formalization of a mathematics textbook using the FormalFrontier pipeline.

## How to Work

1. Read `PLAN.md` for the full pipeline description
2. Check `PROGRESS.md` to see what stages are complete
3. Work on the next incomplete stage
4. After completing a stage, update `PROGRESS.md` with status, date, and notes
5. For item-level progress, update `progress/items.json`

## Key Principles

### Top-Down Development
Push sorries earlier. State the theorem first, sorry the proof, then fill in. Don't waste time on helper lemmas until you know they're needed by the main result.

### Spec-Driven Development
Use `sorry` placeholders with comments explaining what's needed. Never use `True` as a placeholder for propositions — it hides the actual requirements and will need a full refactor to fix.

### Discussion Blobs Are First-Class
During structure analysis (Stage 1.4), unstructured text between numbered items must be identified and tracked just like theorems and definitions. These discussion paragraphs carry context that proofs depend on. Every byte of the book must belong to exactly one blob.

### Conservative Dependencies
Initially assume each item depends on everything before it. This is safe. We trim to actual dependencies later (Stage 3.4) once proofs exist.

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
- Batch proving: after Stage 3.2 scaffolding, submit all sorry'd theorems

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

## Progress Tracking

- Stage-level: `PROGRESS.md`
- Item-level: `progress/items.json`
- Blueprint status: automatic via LeanArchitect (sorry detection)
- Do NOT modify `PLAN.md` — it is the reference plan
- Blockers and discussion: GitHub issues
