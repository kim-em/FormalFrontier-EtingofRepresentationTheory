# Formalization Progress

Progress is recorded here as stages from PLAN.md are completed.

## Stage 1.1: Page Extraction
- **Status:** Complete
- **Date:** 2026-03-14
- **Notes:** 235 pages extracted from `source/original.pdf` into `pdf/raw-pages/`.

## Stage 1.2: Lean Build
- **Status:** Complete
- **Date:** 2026-03-15
- **Notes:** Lean project initialized, Mathlib built. CI workflow active on PRs.

## Stage 1.3: Frontmatter Detection
- **Status:** Complete
- **Date:** 2026-03-15
- **Notes:** 8 frontmatter pages, 227 main content pages (1–227). Mapping in `pdf/pages/mapping.json`.

## Stage 1.4: Page Transcription
- **Status:** Complete
- **Date:** 2026-03-16
- **Notes:** All 235 pages transcribed (8 frontmatter + 227 main content). 235 `.md` files in `pages/`. Spurious PDF running headers cleaned up across all pages. Quality spot-check passed on 10-page sample.

## Stage 1.5: Structure Analysis
- **Status:** Complete
- **Date:** 2026-03-16
- **Notes:** All 10 chapters structured. 583 items identified across frontmatter, 9 chapters, and backmatter. Contiguity validation passed. `items.json` assembled.

## Stage 1.6: Blob Extraction
- **Status:** Complete
- **Date:** 2026-03-16
- **Notes:** 583 blob files extracted. 1:1 correspondence validated — no gaps, overlaps, or orphans.

## Stage 2.1: Internal Dependency Analysis
- **Status:** Complete
- **Date:** 2026-03-16
- **Notes:** 583 internal dependency entries (conservative: each item depends on all predecessors). Accuracy validated — 100% correct on spot check.

## Stage 2.2: External Dependency Analysis
- **Status:** Complete
- **Date:** 2026-03-16
- **Notes:** 58 external dependencies identified (33 undergrad prerequisites, 15 external results, 10 folklore). 163/583 items (28%) reference external deps. Descriptions accurate; item attribution ~50% error rate (to be fixed in Stage 3.3).

## Stage 2.3: Blueprint Assembly
- **Status:** Complete
- **Date:** 2026-03-16
- **Notes:** 583-item leanblueprint DAG generated. HTML blueprint builds via plastex. All items and dependency edges validated.

## Stage 2.4: Mathlib Coverage Research
- **Status:** Complete
- **Date:** 2026-03-16
- **Notes:** External deps: 34 exact (59%), 15 partial (26%), 9 missing (16%). Book definitions (83 total): 46 exact (55%), 21 partial (25%), 16 gap (19%). 4 wrong Mathlib names corrected during review.

## Stage 2.5: External Sources Research
- **Status:** Complete
- **Date:** 2026-03-16
- **Notes:** All 52 gap/partial items have identified external sources (87 entries, 66 high-usefulness). Primary formal source: MathComp. No uncovered gaps.

## Stage 2.6: Readiness Report
- **Status:** Complete
- **Date:** 2026-03-16
- **Notes:** Readiness report compiled (#498). Reviewed and validated (#512). Risk assessments calibrated for all chapters.

## Stage 2.7: Reference Attachment
- **Status:** Complete
- **Date:** 2026-03-16
- **Notes:** Stage 2.7 tooling built (#505). .refs.md companion files generated for all items (#515). Output reviewed and validated (#529).

## Stage 3.1: Scaffolding
- **Status:** Complete
- **Date:** 2026-03-16
- **Notes:** All 8 chapters (2–9) scaffolded: 231 Lean files, ~249 sorry placeholders. Module structure established (#535). Chapter 2 reviewed (#539). Remaining chapter reviews pending (#531, #541, #542, #543). Three scaffolding patterns: Mathlib alias, custom definition, sorry'd statement.

## Stage 3.2: Proof Filling
- **Status:** In progress
- **Date started:** 2026-03-16
- **Latest update:** 2026-03-20 (wave 23 summary, updated)
- **Notes:** 205/583 items sorry_free in items.json (35.2%). 84 sorry occurrences across 29 files. ~340 PRs merged across twenty-three proof waves. Four chapters at 100% formal completion: Ch3, Ch4, Ch7, Ch8. Wave 23 (15 PRs) consolidated wave 22's gains: Example6_4_9_An.lean became sorry-free (root classification proved), Proposition 6.6.6 reduced from ~12 to 4 sorries (reflection functor round-trip), Lemma 5.25.3 down to 1 sorry (charVα₁_parabolic proved), GL2 conjugacy class work completed, and a full feasibility audit classified all sorries. Remaining work concentrated in Ch5 (45 sorries across 15 files) and Ch6 (27 sorries across 9 files). 10 issues actively claimed with work in progress. See `progress/summaries/wave-23-summary.md` for full details.
