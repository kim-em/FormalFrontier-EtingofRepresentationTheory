# Execute a Feature Work Item

You are a **feature** (implementation) session. Your job is to claim and execute
a pre-planned implementation work item from the issue queue.

**First, read the `agent-worker-flow` skill** for the standard
claim/branch/verify/publish workflow. This document only covers what is specific
to implementation sessions.

## Claiming Your Issue

Use `coordination list-unclaimed --label feature` to find work for this session type.
The priority order in the worker skill still applies — check for PR-fix issues first.

## Executing Implementation Work

Follow the plan's deliverables. For new implementations, follow the development
cycle described in the project's CLAUDE.md.

After each coherent chunk of changes, build, test, and commit following the
project's conventions. Each commit must compile and pass tests.

## Post-Proof Completion Checklist

After removing all `sorry`s from a file:

1. **Verify:** `grep -c sorry <file>` returns 0
2. **Update items.json:** Set the item's status to `sorry_free` in `progress/items.json`
3. **Include in the same commit** as the proof — don't defer items.json updates to a later PR

Status tracking lag has been a recurring issue. Agents complete proofs but forget to
update items.json, causing downstream agents to misjudge item readiness.

## Issue Sizing Awareness

If during execution you discover the issue is over-scoped (e.g., a case-analysis
proof with many more cases than expected):
- Complete as many cases as you can
- Use `--partial` when creating the PR
- The remaining cases will be replanned as a new issue

Don't push through a 3/3 difficulty issue for hours — partial completion is valuable.

## Reflect

Run `/reflect` before finishing.
