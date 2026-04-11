# Parallel Agent Coordination Skill

Patterns for effective multi-agent work on FormalFrontier book repositories. Derived from Phases 1-3 experience (5+ concurrent agents, 200+ PRs, 583 items, 20 proof waves).

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
git show main:MyProject/Chapter1/Item42.lean 2>/dev/null && echo "Already done"
```

### Salvage, Don't Restart

When a PR has merge conflicts, salvage the content rather than redoing the work:
1. Check out the conflicted branch
2. Extract the new files/changes
3. Apply them to a fresh branch from `main`
4. Close the old PR, create a new one

**Prefer rebasing over creating duplicate PRs.** When the conflict is simple (< 5 files
changed, conflicts in non-overlapping sections), rebase the existing branch:
```bash
git fetch origin main
git rebase origin/main
# resolve conflicts
git push --force-with-lease
```
Creating a new PR for a simple rebase wastes CI cycles and adds noise to the PR history.
Only create a new PR when the conflicts are extensive or the original branch is badly diverged.

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

## CI Triage Checklist

CI failures on PRs fall into two categories: **infrastructure** (runner-side) and **code** (your changes). Misdiagnosing infrastructure failures as code issues wastes entire sessions. Multiple sessions in waves 45-47 were spent re-diagnosing the same infrastructure failures.

### Quick Diagnosis (< 2 minutes)

1. **Check the CI conclusion.** `CANCELLED` almost always means infrastructure (runner OOM, disconnected, timeout). `FAILURE` could be either.
2. **Read the build log tail.** Infrastructure failures show messages like:
   - "The runner has received a shutdown signal"
   - "Communication with the server was lost"
   - "The operation was canceled"
   - "Runner.Worker"
   - No error output at all (job killed before producing output)
3. **Check if other PRs have the same failure.** If 3+ PRs all fail with CANCELLED at the same time, it's infrastructure.

### Infrastructure Failure → Re-trigger

```bash
# Re-trigger CI by pushing an empty commit (if no other changes to push)
gh pr view N --json headRefName --jq .headRefName | xargs -I{} git push origin {}
# Or via the API:
gh api repos/OWNER/REPO/actions/runs/RUN_ID/rerun -X POST
```

**Don't create "fix CI" issues for infrastructure failures.** Just re-trigger and move on.

### Code Failure → Diagnose

If the build log shows actual Lean errors (type mismatches, unknown identifiers, unsolved goals):
1. Check if the error is on a file you changed
2. Check if main has been updated since your branch diverged (rebase may be needed)
3. Read the specific error message — don't just re-trigger and hope

### Batch Re-trigger Pattern

When multiple PRs have infrastructure failures (common after runner pool issues):
```bash
for pr in 2175 2191 2198 2200 2208; do
  echo "Re-triggering #$pr"
  gh pr view $pr --json headRefName --jq .headRefName | xargs -I{} git push origin {}
done
```

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
- **Phase 3 (formalization)**: Lean proof writing, dependency-ordered work

### Tooling Gates

Before starting content work in a new phase, verify that:
1. Validation tooling exists and is tested (see `validation-first` skill)
2. The previous phase's outputs are complete and validated
3. Any CLI workarounds are documented

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

### Merge Order Matters

In formalization, merge order affects what's available to downstream agents:
- Definition PRs should merge before theorem PRs that use them
- If two PRs touch the same import chain, they will conflict
- Enable auto-merge and keep PRs small (1-5 items) to minimize conflicts

### Formalization Anti-Patterns

1. **Working on items with unmet dependencies** — wastes time, proof will need to change when dependencies are formalized
2. **Large PRs touching many items** — high conflict risk with parallel agents
3. **Changing definition signatures after dependents exist** — cascading breakage across all agents
4. **Not checking `.refs.md` before starting** — may miss that Mathlib already has the result

## Lessons from Stage 3.2 Proof Waves (200+ PRs, 20 waves)

### Cross-Validation Must Be Planned Upfront

Chapter 5 had 9 missing pages (pp. 111-114, 116-118, 120, 134) discovered only during cross-chapter validation, not during original structure analysis. This cascaded to block items.json assembly and all of Phase 2.

**Rule:** Plan cross-validation as a dedicated issue *before* finishing a stage, not as an afterthought. Each stage's planner should create a cross-validation issue that runs after all chapter-level work is done but before the stage is declared complete.

### READINESS.md Must Incorporate Review Findings

The Phase 2 readiness report missed findings from 6 completed reviews: 50% external dep attribution errors, ~6% Mathlib naming errors, fabricated sources, and 9 excluded external deps. The report was accurate about what it *counted* but silent about known *quality issues*.

**Rule:** Readiness/summary reports must explicitly list open review findings and their severity. A report that omits known issues is worse than no report — it creates false confidence.

### Stale Label Cleanup Protocol

11 stale claims and 3 stale `has-pr` labels accumulated during the proof wave, silently blocking work items. Causes: agent crashes, PRs closed without merging, branches abandoned.

**Rule:** Planners must run this pre-flight at the start of every planning cycle:
```bash
# Release stale claims (no PR after 4h)
coordination release-stale-claims

# Check for has-pr labels on closed/merged PRs
gh issue list --state open --label has-pr \
  --json number --jq '.[].number' | while read n; do
  pr_state=$(gh pr list --search "closes #$n" --json state --jq '.[0].state // "NONE"')
  if [[ "$pr_state" == "CLOSED" || "$pr_state" == "NONE" ]]; then
    echo "Issue #$n has stale has-pr label"
    gh issue edit "$n" --remove-label has-pr --add-label replan
  fi
done
```

### Proof Difficulty Triage for Planners

When creating proof issues, planners should classify items by expected tractability based on wave 9-11 experience:

**High success rate (create these freely):**
- Dimension counting / rank-nullity arguments
- Concrete finite computations (`decide`-able)
- Direct Mathlib API applications (alias + `inferInstance`)
- Trace-based arguments (group algebra elements)
- Symmetrization / Reynolds operator arguments in characteristic zero
- Strong induction on coordinate sums / dimension vectors (root system proofs)
- Bilinear form preservation via `ring` + linearity lemmas

**Medium success rate (1 per issue, budget full context window):**
- Multi-step algebraic proofs requiring 3+ Mathlib lemmas
- Inductive arguments on natural numbers or partitions
- Proofs requiring `Finset.sum` manipulation and reindexing

- Non-commutative Hom space arguments (require manual k-linear equivalences)

**Low success rate (flag in issue, expect sorry):**
- Anything involving `ExteriorAlgebra` ↔ `PiTensorProduct` bridging
- Proofs requiring `QuiverRepresentation` infrastructure beyond concrete constructions
- Deep symmetric function theory (hook length formula, RSK correspondence)
- Dependent type issues with `if`-branching in structure fields
- Items depending on opaque `sorry : FDRep` placeholders (SchurModule, orbit method)


**Planner action:** For low-success items, set difficulty to 3/3 and include an explicit note: "This may require sorry. Budget the full context window for a single attempt. If blocked after 2 serious attempts, sorry and move on."

### Proof Batch Sizing

From 30 PRs across 4 concurrent agents:
- **Optimal:** 1-3 items per proof PR (fast review, low conflict risk)
- **Definitions/aliases:** 3-8 per PR (mechanical, rarely conflict)
- **Infrastructure items:** 1 per PR (high complexity, needs careful review)

Mixing difficulty levels in one issue causes the hard item to block all easy ones. Never combine a hard theorem with straightforward proofs.

### Housekeeping Cadence

Regular housekeeping prevents accumulation of stale state. Planners should create review-type issues for these tasks periodically:

**Every 10-15 merged PRs:**
- **items.json staleness audit**: Compare items.json status with actual sorry counts in Lean files. Fix any discrepancies.
- **Stale PR triage**: Review open PRs with failing CI or merge conflicts. Close dead PRs, replan if needed.

**Every 25 merged PRs (meditate trigger):**
- **Skill and command refresh**: The meditate session handles this automatically.

**Why this matters:** In Wave 5-6, items.json drift caused agents to skip ready work or duplicate effort. PR #824 (stale PR triage) was a reactive fix. Proactive housekeeping prevents these issues.

**Planner implementation:** When the planner sees that 10+ PRs have merged since the last review issue, create a review issue with deliverables covering the housekeeping tasks above. This is separate from the summarize trigger (which focuses on progress reporting, not cleanup).

### Breadth-Depth Phase Balancing for Planners

The project alternates between statement formalization (breadth) and proof completion (depth). Planners should monitor the backlog size to decide which type of issues to create:

- **Backlog < 30 items:** Create more statement formalization issues (breadth phase)
- **Backlog 30-40 items:** Balanced mix of statement and proof issues
- **Backlog > 40 items:** Create 80%+ proof issues (depth phase)

Check the backlog with:
```bash
python3 -c "
import json
with open('progress/items.json') as f:
    items = json.load(f)
backlog = sum(1 for i in items if i.get('status') in ['statement_formalized', 'scaffolded', 'proof_formalized'])
print(f'Proof backlog: {backlog} items')
"
```

**As of Wave 43 (2026-04-04):** 579/583 items sorry-free (99.3%), **13 sorries** across 10 files. Ch3, Ch4, Ch7, Ch8 are 100% sorry-free. Ch2 has 1 sorry (Theorem2_1_2). Ch5 has 5 sorries (PolytabloidBasis 3, TabloidModule 1, Theorem5_22_1 1). Ch6 has 5 sorries (CoxeterInfrastructure 1, Corollary6_8_4 1, Problem6_1_5_theorem 1, Problem6_9_1 1, Theorem6_5_2 1). Ch9 has 2 sorries (MoritaStructural 2). Statement formalization is complete.

**Wave 40-43 trajectory (14 PRs, #2047–#2092):** Largest single-wave reduction in project history (−12 sorries, −4 files in Wave 43). Mackey Machine cluster fully eliminated without Clifford theory. Weyl Character cluster nearly eliminated (1 sorry, PR #2081 pending). Corollary6_8_3 fully proved. MoritaStructural reduced 4→2.

**Endgame characteristics (Wave 43+):** Remaining sorries in 4 clusters:
- **Cluster A: Polytabloid Basis (4 sorries):** Design blocker — `columnInvCount'` metric provably insufficient for multi-column Garnir. Needs architectural rethink (dominance ordering or new metric).
- **Cluster B: Weyl Character (1 sorry):** PR #2081 pending CI. If merged, cluster eliminated.
- **Cluster D: Gabriel Chain (5 sorries):** CoxeterInfrastructure universe blocker prevents Corollary6_8_4. Three other sorries are independent and tractable.
- **Cluster E: Morita (2 sorries):** Needs progenerator theory or composition series infrastructure.
- **Primary value-creation patterns:** Decomposition into sub-sorries, bypass approaches (simpler than estimated), and element-level instance bridging. Single-sorry items remain highest-ROI targets.

### Disk Space and Worktree Management (Wave 41)

**Problem:** 45 concurrent worktrees consumed 156GB, leaving only 214MB free. Agents could not run `lake build` or `lake exe cache get`.

**Prevention:**
- Monitor disk usage before creating worktrees: `df -h /`
- If < 5GB free, truncate `.lake/build/ir` and `.lake/build/lib` in idle worktrees
- Cap concurrent worktrees at ~30 for this project
- Rely on CI for verification when local builds are impossible

### CI-Stale PRs: Merge Promptly (Waves 42-43)

**Problem:** PRs #2047, #2049 had cancelled CI for ~5 hours. PR #2081 had cancelled CI at the end of Wave 43. Delays cascade — downstream agents can't merge their work until upstream PRs land on `main`.

**Rule:** After creating a PR with auto-merge:
1. Check CI status after 30 minutes
2. If CI is cancelled or stalled, re-trigger manually: `gh run rerun <run-id>`
3. If CI fails, investigate immediately — don't leave it for the next agent
4. Never leave a session with a pending CI-stale PR without noting it in the progress file

### Stalling Detection and Response

**Pattern (waves 12-17):** Stale claims are a recurring problem — 16 in waves 12-14, 13 more in wave 17 (total 29 stale claims across 6 waves). Root cause: agents work for hours on difficulty 2-3 proofs, hit dead-ends, and terminate without committing any intermediate progress.

**Planner response when stalling is detected:**
1. Run `coordination release-stale-claims` more aggressively (reduce threshold to 2h for hard items)
2. Check if stalled items share a common blocker (e.g., opaque SchurModule placeholder blocking a cluster)
3. If a common blocker exists, create an infrastructure issue to resolve it before re-planning the blocked items
4. Reclassify stalled items: bump difficulty rating, add "This stalled in a previous attempt" to the issue body
5. Consider splitting stalled items into smaller sub-issues (e.g., "prove part (i) only" instead of full theorem)
6. For items that stalled twice: escalate to difficulty 3/3 and add "2 prior failed attempts" to the issue body. These may need a fundamentally different approach or new Mathlib infrastructure.

### PR Supersession Tracking

**Problem (waves 12-14):** PR #926 (Definition 6.6.4) was closed as "superseded" by the owner, but no replacement PR was created. Agent 6416121a wasted a turn discovering the closure, and the definition had to be re-implemented independently.

**Rule:** When closing a PR as superseded:
1. Comment on the closed PR linking to the replacement (or noting it needs one)
2. If no replacement exists yet, create a new feature issue for the item
3. Remove `has-pr` label from the associated issue and add `replan`

**Planner check:** During orientation, scan for recently closed PRs without replacement:
```bash
gh pr list --state closed --limit 20 --json number,title,closedAt,body \
  --jq '.[] | select(.closedAt > "2026-03-17") | "\(.number) \(.title)"'
```

### Stale Issue Detection (Waves 18-20)

**Problem:** Planners create issues for work that was already completed by a recently merged PR. In wave 20, issue #1247 (`invColorEquivMC`) was created even though PR #1216 had already proved it.

**Rule:** Before creating a proof issue, verify the sorry still exists:
```bash
# Check if the file still has sorry at the claimed line
grep -n "sorry" EtingofRepresentationTheory/Chapter5/TargetFile.lean
```

**Worker-side defense:** At the start of any feature session, verify the target sorry still exists before investing time. If the issue is already resolved, close it with a comment referencing the PR that resolved it, then pick the next issue.

### Decomposition as Primary Value Creation (Waves 18-20)

**Pattern:** Top-down decomposition sessions produce the highest value per agent-hour at this stage of the project. With ~70 remaining sorries, many are hard (difficulty 2-3). Sessions that decompose 1 hard sorry into 3-4 well-specified smaller sorries are more valuable than sessions that attempt and fail the hard sorry.

**Evidence:**
- Lemma 5.25.3: 1 sorry → 4 character value sorries (each independently provable)
- Hook quotient identity: 1 issue → 4 sub-issues with clear dependency chain (#1383-#1386)
- Polytabloid basis: 1 sorry → framework + 2 documented sorries

**Planner action:** For difficulty 3/3 items, consider creating a "decomposition" issue (label: feature) before creating a "prove" issue. The decomposition issue's deliverable is a framework commit with well-specified sub-sorries, not a full proof.

### File Collision Mitigation

**Problem (waves 18-20):** Multiple agents working on the same file (especially `Theorem5_15_1.lean` and Chapter 5 files) creates significant rebase overhead. One session was entirely spent fixing 3 broken PRs.

**Mitigation for planners:**
- Label each proof issue with the primary file it touches
- Avoid creating 2+ concurrent issues for the same file
- If concurrent work on the same file is unavoidable, ensure the issues target different functions/theorems with no shared helper lemmas

**Mitigation for workers:**
- Commit and push early — the first-to-merge agent wins, and the other must rebase
- If you see another open PR touching your file, coordinate by commenting on the PR

### Infrastructure Deduplication

**Problem (waves 31-33):** PRs #1682, #1685, #1690 independently built the same GL₂(𝔽_q) BorelSubgroup ≃ F_q × F_q* equivalence. Three agents each spent time constructing equivalent infrastructure because none checked what already existed in other files or recent PRs.

**Mitigation for planners:**
- When creating issues that need group/subgroup equivalences, character computation helpers, or coset decompositions, explicitly note in the issue body which existing infrastructure to reuse
- If multiple issues touch the same algebraic structure, create a shared infrastructure issue first

**Mitigation for workers:**
- Before building any equivalence, isomorphism, or computation helper, search the codebase: `grep -r "def.*BorelEquiv\|Equiv.*Borel\|BorelSubgroup" EtingofRepresentationTheory/`
- Check recent PRs (last 2 weeks) for infrastructure that may not yet be on main
- If you build infrastructure that could be reused, put it in a shared file or the chapter's infrastructure file, not inline in a theorem file
