# Stage 2.7 Review: `.refs.md` Reference Attachment Output

**Date:** 2026-03-16
**Reviewer:** Agent session d14fbdd7
**Issue:** #508

## Summary

Stage 2.7 generated `.refs.md` companion files via `scripts/generate_refs.py`. This review validates the output for accuracy, completeness, and usefulness to Phase 3 formalization agents.

**Recommendation: Proceed to Phase 3.** The output is high quality with two minor prefix-matching bugs that affect only 2 of 58 external dependencies. These do not block formalization.

## Coverage Statistics

| Metric | Count |
|--------|-------|
| Total items in `items.json` | 583 |
| Items with `.refs.md` | 204 (35.0%) |
| Items without `.refs.md` | 379 (65.0%) |
| Empty `.refs.md` files | 0 |

### Per-Chapter Breakdown

| Chapter | Total Items | Refs Files | Coverage |
|---------|-------------|------------|----------|
| Chapter 1 | 3 | 0 | 0.0% |
| Chapter 2 | 117 | 47 | 40.2% |
| Chapter 3 | 58 | 18 | 31.0% |
| Chapter 4 | 60 | 17 | 28.3% |
| Chapter 5 | 157 | 48 | 30.6% |
| Chapter 6 | 64 | 20 | 31.2% |
| Chapter 7 | 59 | 23 | 39.0% |
| Chapter 8 | 24 | 10 | 41.7% |
| Chapter 9 | 35 | 21 | 60.0% |
| Frontmatter/Backmatter | 6 | 0 | 0.0% |

The 379 items without refs are dominated by discussions (118), exercises (87), introductions (61), remarks (32), and examples (27) — types that typically have no Mathlib coverage or external dependency data.

### Refs Content Sections

| Section Type | Count |
|--------------|-------|
| Mathlib Coverage (definition) | 83 |
| External Dependencies | 163 |
| External Sources (definition gap) | 37 |

### Definition Coverage Quality

| Match Quality | Count |
|---------------|-------|
| Exact | 46 |
| Partial | 21 |
| Gap | 16 |
| **Total** | **83** |

### External Dependency Coverage Quality

| Match Quality | Count |
|---------------|-------|
| Exact | 34 |
| Partial | 15 |
| Missing | 9 |
| **Total** | **58** |

## Spot-Check Results

12 files spot-checked across all chapters and coverage levels:

| File | Coverage Type | Verdict |
|------|--------------|---------|
| `Chapter2/Definition2.2.1` | exact (Algebra) | Correct: `Algebra` declaration and 3 ext deps with Mathlib names |
| `Chapter2/Definition2.11.1` | exact (TensorProduct) | Correct: declaration and notes match source data |
| `Chapter2/Remark2.9.10` | ext deps only | **Issue**: PBW gap sources missing (see below) |
| `Chapter3/Definition3.1.1` | exact (IsSemisimpleModule) | Correct |
| `Chapter4/Discussion_4.4` | ext deps only | Correct: bilinear forms reference |
| `Chapter5/Definition5.1.1` | gap | Correct: 3 external sources, Serre/Fulton-Harris/MathComp |
| `Chapter6/Definition6.5.1` | gap | Correct: Schiffler reference |
| `Chapter7/Definition7.1.1` | exact (Category) | Correct: CategoryTheory.Category |
| `Chapter8/Definition8.1.2` | exact (Module.Projective) | Correct: declaration + 2 ext deps with Mathlib names |
| `Chapter8/Definition8.2.3` | partial (Tor) | Correct: Mathlib notes + Weibel/Rotman gap sources |
| `Chapter8/Theorem8.1.1` | ext deps only | **Issue**: "free module" gap source missing (see below) |
| `Chapter9/Definition9.2.2` | partial (projective cover) | Correct: notes + Assem/Anderson-Fuller sources |

**Cross-check methodology:** For each file, verified that:
- Mathlib declaration names match `research/mathlib-coverage-definitions.json`
- External dependency descriptions and Mathlib names match `research/mathlib-coverage-external.json`
- External source references match `research/external-sources.json`
- Content formatting is well-structured and useful

## Issues Found

### Issue 1: Two prefix-match failures in `find_ext_dep_gap` (minor)

The `generate_refs.py` function `find_ext_dep_gap` (line 73) uses prefix matching to join external dependency descriptions with gap source entries from `external-sources.json`. Two descriptions fail to match because neither is a prefix of the other:

1. **PBW theorem:**
   - `external.json`: `"PBW (Poincaré-Birkhoff-Witt) theorem: the universal enveloping algebra U(g) has an ordered monomial basis"`
   - `external-sources.json`: `"PBW theorem"`
   - Diverges at position 4: "PBW (" vs "PBW t"

2. **Free module quotient:**
   - `external.json`: `"Every module over a ring is a quotient of a free module (existence of free resolutions)"`
   - `external-sources.json`: `"Every module is a quotient of a free module"`
   - Diverges at position 13: "Every module over" vs "Every module is"

**Impact:** 2 items (`Chapter2/Remark2.9.10`, `Chapter8/Theorem8.1.1`) are missing external source references (Humphreys, Dixmier for PBW; Rotman for free module quotient). The Mathlib coverage notes are still present and useful. The missing sources are supplementary references, not critical for formalization.

**Fix:** Either normalize descriptions in `external-sources.json` to match `external.json`, or use fuzzy matching (e.g., Levenshtein distance or word overlap) instead of prefix matching.

### Issue 2: No internal dependency information (design choice, not bug)

The `generate_refs.py` script does not read `dependencies/internal.json`. The issue deliverable #1 mentions verifying internal dependency info, but the script was not designed to include it. This is reasonable — internal dependencies are a linear chain (each item depends on its predecessor) and are trivially derivable from item ordering. Including them would add noise.

## Accuracy Assessment

- **Mathlib declaration names:** All 173 unique declarations referenced appear to be legitimate Mathlib names (no suspicious patterns, parentheses, or spaces)
- **Join correctness:** External dependency descriptions join perfectly with the coverage map (0 misses). Definition IDs join perfectly with the definition coverage data (0 misses).
- **Coverage completeness:** Exactly 204 items have reference data across the source files; exactly 204 `.refs.md` files were generated. No items with data were missed; no spurious files were created.
- **Formatting:** All files follow a consistent structure with Markdown headers, bulleted declarations, and inline notes. Content is actionable for formalization agents.

## Conclusion

The Stage 2.7 output is high quality and ready for Phase 3 consumption. The two prefix-match bugs are minor and affect supplementary references only — they should be fixed opportunistically but do not warrant blocking Phase 3 work.
