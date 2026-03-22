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

Follow the plan's deliverables. For proof work items, follow the pre-flight
checklist in the `lean-formalization` skill before starting.

After each coherent chunk of changes, build, test, and commit following the
project's conventions. Each commit must compile and pass tests.

**Endgame strategy:** If stuck after 2 serious attempts on a sorry, extract it
into a well-documented helper lemma and commit the structured proof. This is
high-value work — see "Sorry-to-Helper Extraction Pattern" in the
lean-formalization skill.

## Reflect

Run `/reflect` before finishing.
