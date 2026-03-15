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
- **Status:** In progress — **153 of 235 pages transcribed (65.1%)**
- **Last updated:** 2026-03-15
- **Notes:**
  - Pages 31–110: **complete** (80/80, batch PR #10)
  - Pages 111–160: 33/50 (66%)
  - Pages 161–227: 40/67 (60%)
  - Frontmatter: 0/8 (not started)
  - Pages 1–30: 0/30 (not started)
  - 235 per-page issues created; 75 closed via individual PRs
  - 82 merged PRs total across ~26 hours
  - Largest gap: pages 180–193 (14 contiguous unclaimed pages)
  - 5 open PRs (2 mergeable, 3 conflicting)
