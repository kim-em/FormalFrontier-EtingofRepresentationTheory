# Review: Readiness Report (Stage 2.6)

**Issue:** #494
**Reviewed artifact:** `READINESS.md` (merged via #484)
**Date:** 2026-03-16

## 1. Statistical Accuracy

### Verified correct

| Statistic | Report value | JSON source value | Status |
|-----------|-------------|-------------------|--------|
| Total items | 583 | `items.json`: 583 | PASS |
| Formal items | 230 | Counted from `items.json` | PASS |
| Book definitions total | 83 | `mathlib-coverage-definitions.json` metadata | PASS |
| Def exact match | 46 (55%) | 46 (55.4%) | PASS |
| Def partial | 21 (25%) | 21 (25.3%) | PASS |
| Def gap | 16 (20%) | 16 (19.3%) | PASS |
| External deps total | 58 | `mathlib-coverage-external.json`: 58 | PASS |
| Ext exact | 34 (59%) | 34 (58.6%) | PASS |
| Ext partial | 15 (26%) | 15 (25.9%) | PASS |
| Ext missing | 9 (15%) | 9 (15.5%) | PASS |
| External source refs | 87 total (79 NL, 7 formal, 1 Lean) | `external-sources.json`: 79 natural_language, 7 other_formal, 1 lean_library | PASS |
| Items researched | 52 | `external-sources.json` metadata: 52 | PASS |
| Proof targets | 104 | 44 thm + 25 prop + 19 lem + 16 cor = 104 | PASS |
| Chapter-level item counts | All match | Counted from `items.json` item IDs | PASS |
| Per-chapter definition coverage | All match | `mathlib-coverage-definitions.json` | PASS |

### Error found

| Statistic | Report value | Actual value | Severity |
|-----------|-------------|--------------|----------|
| Internal dependency edges | 169,653 | **582** (linear chain) | **HIGH** |

**Explanation:** PR #504 regenerated `dependencies/internal.json` as a linear chain (each item depends only on its immediate predecessor), replacing the old transitive closure. The readiness report still cites the old transitive closure figure of 169,653 edges. The actual edge count is 582.

## 2. Formalization Order Validity

The suggested formalization order (Waves 1-5) follows a reasonable prioritization by Mathlib coverage strength. However:

### Items spot-checked (8 items)

All 8 items checked have their dependencies satisfied in the linear chain DAG:

- `Chapter2/Definition2.2.1` (Associative algebra, exact) — depends only on preceding discussion
- `Chapter2/Definition2.3.1` (Representation, exact) — depends on Definition2.2.6
- `Chapter3/Theorem3.2.2` (Maschke's theorem) — depends on Corollary3.2.1
- `Chapter3/Definition3.5.1` (Characters, exact) — depends on introduction text
- `Chapter4/Definition4.6.1` (Induced rep, partial) — depends on introduction text
- `Chapter4/Theorem4.10.2` (Frobenius determinant) — depends on preceding discussion
- `Chapter7/Definition7.1.1` (Lie algebra, exact) — depends on Ch7 introduction
- `Chapter7/Definition7.8.1` (UEA, exact) — depends on Ch7.8 introduction

### Issue: parallel waves contradict the dependency DAG

The report suggests Wave 2 can run "Chapters 4, 7 in parallel" and Wave 4 can run "Chapters 5-6" together. But the current linear chain DAG has Ch7 depending (transitively) on all of Ch4, 5, and 6. The formalization order as written is only valid if dependency trimming (Phase 3.3) is performed first to remove false dependencies.

The report does note that "the formalization order follows the book's linear order" and that dependency trimming happens in Phase 3.3, but the Wave 2/4 parallelism suggestions are presented without this caveat. This could confuse agents that check the DAG before starting work.

**Recommendation:** Add a note to the formalization order section stating that parallel waves require dependency trimming first, and that agents must follow the linear book order until Phase 3.3 completes.

## 3. Incorporation of Review Findings

**Verdict: FAIL — No review findings are incorporated into READINESS.md.**

The following issues found in completed reviews are not mentioned anywhere in the report:

### From `reviews/dependency-accuracy.md`

- **50% item-attribution error rate in external dependencies** (4 of 8 items checked had wrong item IDs). The external dependency descriptions are accurate but the item IDs they reference are wrong. This is the single most significant quality issue found in Phase 2.
- Wedderburn-Artin theorem may not be a true external dependency (the book proves it internally).

### From `reviews/mathlib-coverage-definitions-review.md`

- **5 of 83 entries (~6%) reference non-existent or incorrectly-named Mathlib declarations**: `Indecomposable`, `UnitaryGroup`, `Tor`, `PreservesFiniteLimits`, `IsGenerator`
- **3 entries have misclassified coverage levels** (e.g., marked "exact" when partial, or vice versa)
- Overall accuracy is ~88%, not 100% as the statistics imply

### From `reviews/external-sources-review.md`

- **2 fabricated MathComp references** for Frobenius-Schur indicator (`cfun_indicator` is a class function indicator, not Frobenius-Schur)
- **9 external dependencies with zero Mathlib coverage were excluded** from the external sources research — these are the items that most need external source references, yet they have none
- The "100% of gap/partial items have external sources" claim in progress summaries is inaccurate because it excludes the 9 missing external deps

### Missing from all reviews but relevant

The report presents coverage percentages at face value. A human reviewer seeing "55% exact match" and "59% exact match" should know that:
- ~6% of "exact match" definitions may reference wrong Mathlib declarations
- ~50% of external dependency item attributions are wrong (though descriptions are correct)
- External source research has a systematic gap for the 9 hardest items

## 4. Overall Assessment

### What the report does well

- Accurate aggregate statistics (item counts, coverage percentages match source data exactly)
- Clear chapter-by-chapter readiness tiers with actionable prioritization
- Comprehensive Tier 1/2/3 definition breakdown
- Realistic identification of high-risk chapters (5, 6, 9)
- Useful estimated scope table

### What needs correction

1. **[HIGH] Edge count error:** Change "169,653 edges" to "582 edges (linear chain)" and note that the conservative approach means each item depends only on its immediate predecessor
2. **[HIGH] Missing data quality caveats:** Add a section (or subsection of Risk Areas) documenting known data quality issues from reviews:
   - 50% item-attribution error rate in external dependencies
   - ~6% declaration naming errors in Mathlib coverage data
   - 2 fabricated formal system references
   - 9 external dependencies excluded from sources research
3. **[MEDIUM] Formalization order caveat:** Note that parallel waves are aspirational and require dependency trimming first; agents must follow linear order until Phase 3.3
4. **[LOW] Coverage accuracy disclaimer:** Note that the 55%/59% exact-match figures are approximate due to known ~6% declaration error rate in the definitions data

### Recommendation

The report is suitable for human review **with corrections**. The core recommendation (proceed to Phase 3, start with Chapters 2-3) is sound regardless of the data quality issues. However, the human reviewer needs to see the known quality limitations to make an informed decision. The omission of all review findings is the most significant gap — a readiness report that doesn't acknowledge known issues undermines trust in the Phase 2 research process.

**Corrections needed before human approval:**
1. Fix the edge count (169,653 → 582)
2. Add a "Known Data Quality Issues" subsection incorporating review findings
3. Add a caveat to the parallel waves suggestion
