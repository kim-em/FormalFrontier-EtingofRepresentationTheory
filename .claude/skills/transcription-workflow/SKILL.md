# Transcription Workflow Skill

Lessons learned from the Stage 1.4 transcription phase (~140 PRs, 235 pages, 5+ concurrent agents).

## Parallel Work Coordination

### Linear Dependencies Are Too Conservative for Transcription

The initial setup created a linear dependency chain (each page depends on the previous). This caused excessive skip/reclaim cycles — agents would claim an issue, discover its dependency was still open, skip it, and try the next one.

**Better approach for transcription:** Pages are largely independent. Dependencies should only exist for genuinely coupled content (e.g., a proof spanning two pages). Most pages can be transcribed in any order. Reserve linear dependencies for stages where ordering matters (like structure analysis).

**Observed impact:** Issues #255, #256, #259, #262 each had 3-6 coordination comments showing claim → skip → release → reclaim cycles. This is pure overhead.

### Batch PRs Are More Efficient Than Single-Page PRs

The most productive sessions batched 8-17 pages per PR (e.g., PR #360 with 17 pages, PR #400 with 8 pages). Single-page PRs have high coordination overhead relative to the work done.

**Recommendation:** For transcription-like work, batch 5-15 items per PR when they share a logical group (same chapter, same type of content). The PR description should list all pages for traceability.

### Merge Conflicts from Stale Branches

Several PRs (#335, #342, #343) became stale and developed conflicts across 15-20 files. Agents had to salvage content from conflicted PRs rather than merging normally.

**Prevention:** Keep branches short-lived. Rebase frequently if the branch will live more than an hour. For transcription, push and merge each batch before starting the next.

## Transcription Quality Patterns

### Consistent High Quality

Out of 60+ pages validated, only 1 correction was needed (a duplicate running header on page 95). The CONVENTIONS.md file was effective at maintaining consistency across agents.

**Key factors:**
- Clear conventions document created early
- PDF source available for verification
- Structured format (math notation, theorem environments) is unambiguous

### Convention Adherence Was Strong

All sampled pages correctly used:
- `$...$` for inline math, `$$...$$` for display math
- `##` for section headers with book numbering
- Bold labels + italic statements for theorems
- `**Proof.**` ... `$\square$` pattern
- Bold citation numbers `[**47**]`

### Empty/Blank Pages Handled Correctly

Blank pages (e.g., page 42, frontmatter-2, frontmatter-8) received empty `.md` files as specified. No confusion about this convention.

## Common Pitfalls

### Duplicate Running Headers

The one recurring quality issue: some pages included the running header (chapter/section title at page top) as content. Running headers should be omitted — they're navigation aids, not content.

### Stale `has-pr` Labels

When PRs were closed without merging (due to conflicts), their `has-pr` labels remained on the issue, blocking other agents from claiming. Manual label cleanup was needed.

**Recommendation:** The coordination tooling should automatically remove `has-pr` when a PR is closed without merging.

### Claiming Already-Completed Work

Some agents claimed issues for pages that were already on `main` (e.g., issue #91 for page 56). This happened when the issue hadn't been closed after the page was merged via a batch PR.

**Prevention:** Before starting transcription, check if the page file already exists on `main`: `git show main:pages/N.md 2>/dev/null`

## Performance Observations

### Throughput

- **Peak day:** ~50 pages transcribed across 3-4 concurrent agents
- **Average per agent turn:** 3-8 pages (text-heavy pages faster, math-heavy pages slower)
- **Total duration:** ~2 days for 235 pages with 3-5 concurrent agents

### Page Complexity Variance

- **Text/narrative pages** (historical interludes, introductions): fastest, ~2 min each
- **Theorem-dense pages** (definitions, proofs): moderate, ~3-5 min each
- **Table/diagram pages** (character tables, Dynkin diagrams): slowest, ~5-10 min each
- **Blank pages:** trivial

## Applicability to Later Stages

These patterns should inform Stage 1.5 (Structure Analysis) planning:

1. **Reduce artificial dependencies** — only add real ones
2. **Batch work by chapter** — the chapter_map.json enables this
3. **Validate early and often** — the contiguity checker catches gaps/overlaps
4. **Keep CONVENTIONS.md updated** — it was the single most effective quality tool
