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

## Coordination Anti-Patterns

1. **Claiming an issue without checking `main`** — wastes a turn discovering it's already done
2. **Skipping without releasing** — blocks other agents from the issue
3. **Rebasing a branch with 20+ commits** — creates massive conflict potential; squash or fresh-branch instead
4. **Working on tooling during a parallelizable phase** — tooling should be done in a dedicated turn before parallel work begins
5. **Not enabling auto-merge** — forces manual merge, blocking downstream agents
6. **Deferring cross-validation** — gaps between chapters were discovered late in Phase 1 because cross-validation was reactive, not planned upfront

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
- **Phase 3**: 3-10 items per issue (formalization), grouped by dependency cluster
