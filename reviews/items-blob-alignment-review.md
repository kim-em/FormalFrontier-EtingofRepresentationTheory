# Items.json ↔ Blob Directory ↔ Lean Files Alignment Review

**Date**: 2026-03-16
**Issue**: #532

## 1. Cross-Validation: items.json ↔ Blob Directory

**Result: Perfect alignment.**

- `items.json` contains 583 items
- `blobs/` contains exactly 583 `.md` files (excluding `.refs.md` companions)
- Every item ID in `items.json` maps to `blobs/<item_id>.md` — zero orphaned blobs, zero missing blobs
- Chapters covered: 1–9 plus Frontmatter and Backmatter

## 2. Formal Item Counts vs. Scaffolding Issues

### Summary of formal items per chapter

| Chapter | Total formal | Definitions | Theorems | Propositions | Lemmas | Corollaries | Examples |
|---------|-------------|-------------|----------|--------------|--------|-------------|----------|
| 2       | 42          | 25          | 2        | 3            | 0      | 2           | 10       |
| 3       | 23          | 5           | 7        | 4            | 3      | 2           | 2        |
| 4       | 21          | 2           | 7        | 2            | 1      | 2           | 7        |
| 5       | 59          | 10          | 20       | 10           | 11     | 5           | 3        |
| 6       | 32          | 12          | 4        | 4            | 3      | 3           | 6        |
| 7       | 26          | 13          | 0        | 0            | 1      | 0           | 12       |
| 8       | 9           | 6           | 2        | 0            | 0      | 0           | 1        |
| 9       | 18          | 10          | 2        | 2            | 0      | 2           | 2        |

### Comparison with scaffolding issue titles

| Issue | Title claim | Actual count | Match? |
|-------|-----------|--------------|--------|
| #516  | Chapter 3 (23 items) | 23 | ✅ |
| #517  | Chapter 7 (26 items) | 26 | ✅ |
| #518  | Chapter 8 (9 items)  | 9  | ✅ |
| #519  | Chapter 2 non-defs (17 items) | 17 | ✅ |
| #520  | Chapter 4 (21 items) | 21 | ✅ |
| #521  | Chapter 9 (18 items) | 18 | ✅ |
| #523  | Chapter 5, 5.1–5.9 (24 items) | 24 | ✅ |
| #524  | Chapter 5, 5.10–5.18 (20 items) | 20 | ✅ |
| #525  | Chapter 5, 5.19–5.27 (15 items) | 15 | ✅ |
| #526  | Chapter 6, 6.1–6.5 (16 items) | **17** | ❌ |
| #527  | Chapter 6, 6.6–6.8 (16 items) | **15** | ❌ |

### Chapter 6 Discrepancy Details

**Root cause**: `Chapter6/Theorem_Dynkin_classification` has no section number in its item ID. It appears on page 150, which is in section 6.1 (between `Definition6.1.4` and `Problem6.1.3`). The planner likely split items by regex on section numbers, missing this item entirely from the 6.1–6.5 group and compensating by inflating the 6.6–6.8 count.

**Actual Sections 6.1–6.5 (17 items)**:
- 7 definitions, 5 examples, 2 lemmas, 3 theorems (including `Theorem_Dynkin_classification` and `Problem6.1.5_theorem`)

**Actual Sections 6.6–6.8 (15 items)**:
- 5 definitions, 1 example, 4 propositions, 1 lemma, 1 theorem, 3 corollaries

**Issue #526 body claims**: 7 defs + 3 examples + 3 propositions + 2 theorems + 1 lemma = 16
- Actual: 7 defs + 5 examples + 0 propositions + 3 theorems + 2 lemmas = 17
- Type breakdown is wrong in multiple categories

**Issue #527 body claims**: 5 defs + 3 examples + 2 theorems + 2 propositions + 2 corollaries + 1 lemma + 1 additional = 16
- Actual: 5 defs + 1 example + 1 theorem + 4 propositions + 3 corollaries + 1 lemma = 15
- Type breakdown is wrong in multiple categories

**Impact**: Agents working on #526 will discover 17 items instead of expected 16 and may not scaffold `Theorem_Dynkin_classification` if they only look for section-numbered items. Agents working on #527 will find only 15 items instead of 16 and may waste time searching for a non-existent 16th item.

**Recommendation**: Update issue #526 to 17 items (adding `Theorem_Dynkin_classification` explicitly) and issue #527 to 15 items, with corrected type breakdowns.

## 3. Chapter 2 Lean-File-to-Blob Alignment

**Result: Perfect alignment.**

All 25 `.lean` files in `EtingofRepresentationTheory/Chapter2/` map 1:1 to the 25 Chapter 2 definition blobs in `blobs/Chapter2/`:

| Lean file | Blob file | Match |
|-----------|-----------|-------|
| `Definition2_2_1.lean` | `blobs/Chapter2/Definition2.2.1.md` | ✅ |
| `Definition2_2_2.lean` | `blobs/Chapter2/Definition2.2.2.md` | ✅ |
| `Definition2_2_5.lean` | `blobs/Chapter2/Definition2.2.5.md` | ✅ |
| `Definition2_2_6.lean` | `blobs/Chapter2/Definition2.2.6.md` | ✅ |
| `Definition2_3_1.lean` | `blobs/Chapter2/Definition2.3.1.md` | ✅ |
| `Definition2_3_4.lean` | `blobs/Chapter2/Definition2.3.4.md` | ✅ |
| `Definition2_3_5.lean` | `blobs/Chapter2/Definition2.3.5.md` | ✅ |
| `Definition2_3_6.lean` | `blobs/Chapter2/Definition2.3.6.md` | ✅ |
| `Definition2_3_7.lean` | `blobs/Chapter2/Definition2.3.7.md` | ✅ |
| `Definition2_3_8.lean` | `blobs/Chapter2/Definition2.3.8.md` | ✅ |
| `Definition2_7_3.lean` | `blobs/Chapter2/Definition2.7.3.md` | ✅ |
| `Definition2_8_1.lean` | `blobs/Chapter2/Definition2.8.1.md` | ✅ |
| `Definition2_8_3.lean` | `blobs/Chapter2/Definition2.8.3.md` | ✅ |
| `Definition2_8_4.lean` | `blobs/Chapter2/Definition2.8.4.md` | ✅ |
| `Definition2_8_8.lean` | `blobs/Chapter2/Definition2.8.8.md` | ✅ |
| `Definition2_8_9.lean` | `blobs/Chapter2/Definition2.8.9.md` | ✅ |
| `Definition2_8_10.lean` | `blobs/Chapter2/Definition2.8.10.md` | ✅ |
| `Definition2_9_1.lean` | `blobs/Chapter2/Definition2.9.1.md` | ✅ |
| `Definition2_9_6.lean` | `blobs/Chapter2/Definition2.9.6.md` | ✅ |
| `Definition2_9_7.lean` | `blobs/Chapter2/Definition2.9.7.md` | ✅ |
| `Definition2_9_9.lean` | `blobs/Chapter2/Definition2.9.9.md` | ✅ |
| `Definition2_11_1.lean` | `blobs/Chapter2/Definition2.11.1.md` | ✅ |
| `Definition2_12_1.lean` | `blobs/Chapter2/Definition2.12.1.md` | ✅ |
| `Definition2_14_1.lean` | `blobs/Chapter2/Definition2.14.1.md` | ✅ |
| `Definition2_14_2.lean` | `blobs/Chapter2/Definition2.14.2.md` | ✅ |

**Naming convention**: Dots in item IDs become underscores in Lean filenames; title suffixes (e.g., `_Algebra`) are dropped. This is consistent across all 25 files.

**Doc-string content**: Spot-checked `Definition2_2_1.lean` — the doc-string reproduces the blob's natural language statement accurately.

## Conclusions

1. **items.json ↔ blobs**: No issues. Perfect 1:1 correspondence across all 583 items.
2. **Formal counts**: 9 of 11 scaffolding issues have correct counts. **Issues #526 and #527 have wrong counts and type breakdowns** due to `Theorem_Dynkin_classification` having no section number in its ID.
3. **Chapter 2 Lean ↔ blobs**: No issues. All 25 files correctly correspond to their blobs with consistent naming.

### Action Items

- **Update #526**: Change title to "(17 items)", fix type breakdown in body, explicitly list `Theorem_Dynkin_classification`
- **Update #527**: Change title to "(15 items)", fix type breakdown in body
