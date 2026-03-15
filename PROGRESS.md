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
- **Status:** In progress — **9 of 10 chapters complete (422 items identified)**
- **Last updated:** 2026-03-16
- **Notes:**
  - Complete: Frontmatter (4 items), Chapter 1 (3), Chapter 2 (113), Chapter 3 (58), Chapter 4 (60), Chapter 6 (64), Chapter 7 (59), Chapter 8 (24), Chapter 9 (35), Backmatter (2)
  - Remaining: Chapter 5 (#429, in progress)
  - Validation tooling created: contiguity checker + JSON schema (#414)
  - Cross-chapter validation passed (#444)
  - Items.json assembly (#441) blocked on Chapter 5 completion

## Stage 1.6: Blob Extraction
- **Status:** Not started
- **Notes:** Blocked on items.json assembly (#441), which depends on Chapter 5 structure analysis (#429).
