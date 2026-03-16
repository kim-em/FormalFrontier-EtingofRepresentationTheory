# Internal Dependencies (Stage 2.1)

Conservative dependency baseline for Etingof's *Introduction to Representation Theory*.

## Method

Each item depends on all items that precede it in book order (the conservative default from PLAN.md Stage 2.1). The book's chapter organization description (blob `Chapter1/Discussion_BookOrganization`) was reviewed for explicit chapter-independence declarations but **none were found** — the text describes a linear progression through topics with no statements about chapters being independently readable or skippable.

Therefore, the full conservative baseline is used without chapter-level trimming.

## Summary Statistics

| Metric | Value |
|--------|-------|
| Total items | 578 |
| Total dependency edges | 166,753 |
| Edges removed by trimming | 0 |
| Items with 0 dependencies | 1 (Frontmatter/TitlePage) |
| Max dependencies (single item) | 577 (Backmatter/MathematicalReferences) |

## Per-Chapter Item Counts

| Chapter | Items |
|---------|-------|
| Frontmatter | 4 |
| Chapter 1 | 3 |
| Chapter 2 | 117 |
| Chapter 3 | 58 |
| Chapter 4 | 60 |
| Chapter 5 | 152 |
| Chapter 6 | 64 |
| Chapter 7 | 59 |
| Chapter 8 | 24 |
| Chapter 9 | 35 |
| Backmatter | 2 |

## Chapter Dependency Matrix (Conservative)

Every chapter depends on all preceding chapters:

| Chapter | Depends On |
|---------|-----------|
| Frontmatter | — |
| Chapter 1 | Frontmatter |
| Chapter 2 | Frontmatter, Ch 1 |
| Chapter 3 | Frontmatter, Ch 1–2 |
| Chapter 4 | Frontmatter, Ch 1–3 |
| Chapter 5 | Frontmatter, Ch 1–4 |
| Chapter 6 | Frontmatter, Ch 1–5 |
| Chapter 7 | Frontmatter, Ch 1–6 |
| Chapter 8 | Frontmatter, Ch 1–7 |
| Chapter 9 | Frontmatter, Ch 1–8 |
| Backmatter | All |

## Items with Most Dependencies

| Item | Dependencies |
|------|-------------|
| Backmatter/MathematicalReferences | 577 |
| Backmatter/ReferencesHistorical | 576 |
| Chapter9/Corollary9.7.3 | 575 |
| Chapter9/Definition9.7.2 | 574 |
| Chapter9/Discussion_after_Definition9.7.1 | 573 |

## Chapter-Independence Analysis

The chapter organization description in `blobs/Chapter1/Discussion_BookOrganization.md` describes each chapter's content but does not declare any chapters as independent or skippable. Notable observations:

- Chapters 2–5 form a clear linear progression on finite group representations
- Chapter 5 explicitly "continues" from Chapter 4
- Chapters 6–9 introduce new topics (quivers, categories, homological algebra, finite dimensional algebras) but the text does not state they can be read independently of earlier chapters
- The conservative baseline is therefore appropriate; actual dependency trimming will occur in Stage 3.3 once proofs exist

## Files

- `internal.json` — Full dependency map (578 entries)
- `README.md` — This file

## Validation

```bash
python3 scripts/validate_dependencies.py
```
