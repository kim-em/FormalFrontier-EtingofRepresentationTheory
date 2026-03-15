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
- **Status:** In progress — **175 of 227 main-content pages transcribed (77.1%)**
- **Last updated:** 2026-03-16
- **Notes:**
  - Pages 31–110: **complete** (80/80)
  - Pages 111–160: 39/50 (78%) — missing 111–118, 120–121, 134
  - Pages 161–227: 56/67 (84%) — missing 161–162, 164, 204, 216–221, 227
  - Pages 1–30: 0/30 (not started)
  - Frontmatter: 0/8 (not started)
  - 108 merged PRs total across ~36 hours of project lifetime
  - 24 PRs merged since last checkpoint: 8 new transcriptions, 15 validations (13 no-changes, 2 minor corrections)
  - 2 open PRs (both mergeable)
  - Remaining gaps: pages 1–30 (early chapters), scattered mid/late pages
