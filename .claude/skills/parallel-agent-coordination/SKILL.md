# Parallel Agent Coordination Skill

Patterns for effective multi-agent work on FormalFrontier book repositories. Derived from Phases 1-2 experience (5+ concurrent agents, 140+ PRs, 578 items).

## Issue Design

### Match Dependencies to Actual Coupling

Don't use linear dependency chains for inherently parallel work. Each issue's dependencies should reflect genuine data dependencies, not just ordering in the source material.

**Parallel-safe work** (minimal dependencies):
- Page transcription (each page is independent)
- Structure analysis of separate chapters
- Formalization of items whose dependencies are already sorry-free

**Genuinely sequential work** (needs real dependencies):
- Multi-page proofs (page N+1 continues page N's proof)
- Items that reference definitions from earlier items
- Tooling that must exist before downstream work can begin

### Keep Issues Granular But Not Atomic

Too granular (1 page per issue): high coordination overhead, lots of claim/skip/release cycles.
Too coarse (1 chapter per issue): blocks parallelism, only one agent per chapter.

**Sweet spot:** Group 3-10 related items per issue. For transcription, group by chapter section. For formalization, group by dependency cluster.

## Branch and PR Hygiene

### Short-Lived Branches

Keep branches alive for hours, not days. The more concurrent agents, the faster `main` moves, and the faster branches go stale.

**Pattern:**
1. Claim issue(s)
2. Do the work (30 min - 2 hours)
3. Create PR, enable auto-merge
4. Start next batch on a fresh branch from updated `main`

### Check Before You Claim

Before starting work on any item, verify it hasn't already been completed:

```bash
# For transcription
git show main:pages/N.md 2>/dev/null && echo "Already done"

# For formalization
git show main:lean/MyProject/Chapter1/Item42.lean 2>/dev/null && echo "Already done"
```

### Salvage, Don't Restart

When a PR has merge conflicts, salvage the content rather than redoing the work:
1. Check out the conflicted branch
2. Extract the new files/changes
3. Apply them to a fresh branch from `main`
4. Close the old PR, create a new one

## Progress File Protocol

### Always Write a Progress File

Even for short turns, write `progress/<timestamp>.md`. The next agent depends on this for onboarding. Include:
- What was accomplished (specific pages/items)
- Where work stopped
- Overall project progress (percentage)
- Concrete next step
- Blockers

### Read Before You Write

Always read the most recent progress file before starting. It may contain warnings about stale issues, broken CI, or other traps.

## Stale State Management

Stale claims, labels, and branches accumulate when agents crash or PRs are abandoned. Check for and clean these up at the start of planning sessions.

### Stale Claims

Issues with `claimed` label but no PR after several hours are stale. Use `coordination release-stale-claims` to release them (default 4h threshold). Planners should check for stale claims during orientation.

### Stale `has-pr` Labels

If a PR was closed without merging, the issue may still have `has-pr` (excluding it from `list-unclaimed`). Fix by removing the label and adding `replan`:
```bash
gh issue edit N --remove-label has-pr --add-label replan
```

### Dead Branches

Branches from abandoned PRs create merge conflict risk. After closing a PR, delete its remote branch:
```bash
gh pr close N --delete-branch
```

### Pre-Flight Before PR Creation

Before creating a PR, verify you haven't accidentally modified protected files:
```bash
git diff --name-only main..HEAD | grep -E '^(\.claude/CLAUDE\.md|PLAN\.md)$'
```
If this outputs anything, remove those changes before pushing.

## Coordination Anti-Patterns

1. **Claiming an issue without checking `main`** — wastes a turn discovering it's already done
2. **Skipping without releasing** — blocks other agents from the issue
3. **Rebasing a branch with 20+ commits** — creates massive conflict potential; squash or fresh-branch instead
4. **Working on tooling during a parallelizable phase** — tooling should be done in a dedicated turn before parallel work begins
5. **Not enabling auto-merge** — forces manual merge, blocking downstream agents
6. **Deferring cross-validation** — gaps between chapters were discovered late in Phase 1 because cross-validation was reactive, not planned upfront
7. **Not cleaning stale state** — stale claims and labels silently block work items from the queue

## Phase Transitions

When the project transitions between phases (e.g., Phase 1 Source Preparation to Phase 2 Dependency Mapping), the work patterns change fundamentally. Key considerations:

### Different Skill Requirements

- **Phase 1 (transcription/structure)**: Mechanical work, high parallelism, low cognitive load per item
- **Phase 2 (dependency analysis)**: Reading comprehension, mathematical reasoning, lower parallelism
- **Phase 3 (formalization)**: Lean proof writing, Aristotle escalation, dependency-ordered work

### Tooling Gates

Before starting content work in a new phase, verify that:
1. Validation tooling exists and is tested (see `validation-first` skill)
2. The previous phase's outputs are complete and validated
3. Any CLI workarounds are documented (e.g., leanblueprint needing `lean/` as cwd)

### Issue Sizing Shifts

Issue granularity should match the phase:
- **Phase 1**: 5-15 pages per issue (transcription), 1 chapter per issue (structure analysis)
- **Phase 2**: 1 chapter per issue (dependency analysis), 1 issue for cross-chapter validation
- **Phase 3**: 1-5 items per issue (formalization), grouped by dependency cluster and difficulty

## Phase 3: Formalization-Specific Coordination

### Dependency DAG Traversal

Phase 3 work must respect the dependency DAG — you can't formalize an item until its dependencies are sorry-free.

**Finding ready work:**
1. Query `progress/items.json` for items with status `statement_formalized`
2. Check each item's dependencies in `dependencies/internal.json`
3. An item is "ready" when all its direct dependencies have status `sorry_free`
4. Prefer items with many dependents (unblocks more downstream work)

**Planners should:**
- Group ready items by dependency cluster (items that share dependencies)
- Never plan work on items whose dependencies aren't sorry-free
- Front-load foundational definitions (Chapter 1-2) — everything depends on them
- Track the formalization frontier: the boundary between sorry-free and sorry'd items

### Aristotle Coordination

Aristotle adds a new dimension to coordination: async proof attempts running in parallel with Claude agents.

**Constraints:**
- Max 5 concurrent Aristotle projects
- Deduplication: check `sent_to_aristotle` status before submitting
- One submission per item at a time

**Planner patterns:**
- After Stage 3.1 scaffolding, plan an "Aristotle batch submission" issue
- Plan periodic "Aristotle result harvesting" issues to check and incorporate results
- Don't plan Claude work on items already sent to Aristotle (wait for result)

**Worker patterns:**
- Before starting an item, check if Aristotle already solved it
- If you escalate to Aristotle mid-work, commit what you have, mark the PR partial
- Record the Aristotle project ID in `progress/items.json` immediately

### Merge Order Matters

In formalization, merge order affects what's available to downstream agents:
- Definition PRs should merge before theorem PRs that use them
- If two PRs touch the same import chain, they will conflict
- Enable auto-merge and keep PRs small (1-5 items) to minimize conflicts

### Formalization Anti-Patterns

1. **Working on items with unmet dependencies** — wastes time, proof will need to change when dependencies are formalized
2. **Submitting the same theorem to both Claude and Aristotle simultaneously** — wasteful duplication
3. **Large PRs touching many items** — high conflict risk with parallel agents
4. **Changing definition signatures after dependents exist** — cascading breakage across all agents
5. **Not checking `.refs.md` before starting** — may miss that Mathlib already has the result
