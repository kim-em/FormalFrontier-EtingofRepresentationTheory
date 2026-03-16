---
name: validation-first
description: Use when planning a new pipeline stage or creating work items for parallel execution. Ensures validation tooling exists before content work begins.
allowed-tools: Read, Edit, Bash, Glob, Grep, Write
---

# Validation-First Development Pattern

Build validation tooling **before** starting content work for any pipeline stage. This pattern proved highly effective in Phase 1 and should be replicated for all subsequent phases.

## The Pattern

For each pipeline stage:

1. **Create schema** — Define the JSON schema for the stage's output format
2. **Build validator** — Write a validation script that checks output against the schema
3. **Test validator** — Run against edge cases (empty input, malformed data, boundary conditions)
4. **Then start content work** — With validation in place, errors are caught immediately

## Why This Works

- **Catch errors early**: Agents working in parallel all validate against the same schema
- **Consistent output**: No format drift between agents or sessions
- **Fast feedback**: Validation runs in seconds, much faster than manual review
- **Enables parallel work**: Multiple agents can work independently because the validator ensures compatibility

## Phase 1 Evidence

This pattern was used successfully for:
- `scripts/items_schema.json` + `validate_items.py` — caught gaps/overlaps in structure analysis
- `scripts/dependencies_schema.json` + `validate_dependencies.py` — 14 edge cases tested before any dependency work
- `scripts/external_deps_schema.json` + `validate_external_deps.py` — ready before external dep analysis

All validation tooling was created in dedicated issues (#414, #451, #459) before the content work issues were created. This sequencing is intentional.

## Anti-Pattern: Validation After the Fact

Don't create content first and validate later. When validation is deferred:
- Format inconsistencies accumulate across agents
- Rework is needed to fix format issues in already-completed content
- Cross-validation catches problems too late (e.g., Chapter 5 gap discovery)

## Cross-Validation

After individual content work is complete, run a **cross-validation** pass that checks consistency across all outputs:
- Do all chapter structures together cover all pages?
- Do all internal dependencies reference items that exist?
- Are there any orphaned items or dangling references?

Cross-validation should be a separate issue, not an afterthought. Plan for it explicitly.

## Phase 3: Formalization Verification Patterns

Formalization adds a new dimension to validation — the Lean compiler itself is the ultimate validator.

### Compilation as Validation

Unlike Phases 1-2 (JSON schemas, text validation), Phase 3 has `lake build` as the ground truth:
- **No sorry = proved.** The compiler guarantees correctness.
- **sorry = placeholder.** Compiles but isn't done.
- **admit = dangerous.** Never commit — only use in temporary Aristotle submission files.

### Automated Status Tracking

LeanArchitect's `extract_blueprint` automatically detects sorry status from compiled `.olean` files. No manual status tracking needed for formal declarations — just compile and extract.

For non-formal items (discussion blobs, external dependencies), status is tracked manually in `progress/items.json`.

### Validation Tooling for Stage 3.1 (Scaffolding)

Before starting content work, create:
1. **Compilation check script** — runs `lake build` and reports files with errors
2. **Sorry counter** — counts remaining sorries across all item files
3. **Dependency readiness checker** — given an item, checks if all dependencies are sorry-free

### Review Patterns for Formalized Proofs

When reviewing a formalization PR:
1. **Does it compile?** (`lake env lean <file>` — the minimum bar)
2. **Does the statement match the book?** Compare docstring against blob text
3. **Is the proof reasonable?** Overly long proofs or `native_decide` on large terms may indicate wrong approach
4. **Are imports minimal?** Unnecessary imports slow compilation
5. **Any `sorry` or `admit` remaining?** Search the diff

## Planning Heuristic

When a planner creates issues for a new stage:
1. First issue: create schema + validation tooling
2. Second issue: create any helper scripts (generators, assemblers)
3. Remaining issues: content work (can be parallelized)
4. Final issue: cross-validation

The tooling issues should be dependencies of the content work issues.
