# items.json Status Audit

**Date:** 2026-03-16
**Issue:** #604

## Status Counts: Before and After

| Status | Before | After | Delta |
|--------|--------|-------|-------|
| `missing` | 442 | 352 | -90 |
| `scaffolded` | 117 | 118 | +1 |
| `sorry_free` | 21 | 110 | +89 |
| `statement_formalized` | 3 | 3 | 0 |
| **Total** | **583** | **583** | **0** |

**New field: `needs_statement`:** 83 items flagged (items with `(sorry : Prop)` placeholder propositions)

## Methodology

For each item in `progress/items.json`:

1. **Derived Lean file path** from item ID: `Chapter2/Theorem2.1.1` -> `EtingofRepresentationTheory/Chapter2/Theorem2_1_1.lean`
2. **Checked file existence** and counted `sorry` keywords
3. **Detected `(sorry : Prop)` placeholders** — these indicate the statement itself needs formalization
4. **Detected `True` placeholders** — checked both `theorem foo : True` (statement-level) and `(h : True)` (hypothesis-level)

## Items Changed to `sorry_free`

### From `scaffolded` (38 items)

| Chapter | Items |
|---------|-------|
| Ch2 | Proposition2.2.3, Example2.2.4, Example2.3.3, Example2.3.14_continued, Example2.8.2, Example2.9.2, Example2.9.2_continued, Example2.9.8, Example2.9.12, Example2.9.13 |
| Ch4 | Definition4.6.1, Theorem4.6.2, Theorem4.6.3 |
| Ch6 | Definition6.4.1, Definition6.4.3, Definition6.4.5, Definition6.4.7, Definition6.4.10, Definition6.5.1, Definition6.6.1, Definition6.7.1 |
| Ch7 | Definition7.1.1, Example7.1.3, Definition7.1.4, Example7.1.5, Example7.1.6, Definition7.2.1, Example7.2.2, Definition7.3.1, Definition7.4.1, Definition7.6.1, Definition7.7.1, Example7.7.2, Definition7.8.1, Definition7.8.2, Definition7.9.1, Definition7.9.3 |
| Ch9 | Definition9.1.2 |

### From `missing` (51 items — files existed but were untracked)

| Chapter | Items |
|---------|-------|
| Ch2 | Definition2.2.1, Definition2.2.2, Definition2.2.5, Definition2.2.6, Definition2.3.1, Definition2.3.4, Definition2.3.5, Definition2.3.6, Definition2.3.7, Definition2.3.8, Definition2.7.3, Definition2.8.1, Definition2.8.3, Definition2.8.8, Definition2.8.10, Definition2.9.1, Definition2.9.6, Definition2.9.7, Definition2.9.9, Definition2.11.1, Definition2.12.1, Definition2.14.1, Definition2.14.2 |
| Ch3 | Definition3.1.1, Proposition3.1.4, Lemma3.1.6, Definition3.3.2, Definition3.4.1, Definition3.5.1, Proposition3.5.2, Definition3.5.7 |
| Ch5 | Definition5.1.1, Example5.1.3, Definition5.1.4, Corollary5.1.6, Theorem5.3.1, Proposition5.3.2, Theorem5.4.4, Lemma5.4.7, Theorem5.6.1, Definition5.7.1, Lemma5.7.2, Definition5.8.1, Theorem5.9.1, Example5.12.3 |
| Ch8 | Definition8.1.2, Definition8.1.6, Definition8.1.8, Definition8.2.1, Definition8.2.3, Definition8.2.4 |

## Items Changed to `scaffolded` (from `missing`)

### With sorry (19 items — proper statements, proofs needed)

| Chapter | Items | Sorry count |
|---------|-------|-------------|
| Ch2 | Definition2.8.4, Definition2.8.9 | 2 each |
| Ch3 | Theorem3.3.1, Theorem3.5.4, Corollary3.5.5, Theorem3.6.2, Theorem3.7.1, Theorem3.8.1, Theorem3.10.2 | 1-2 each |
| Ch5 | Theorem5.1.5, Definition5.2.1, Definition5.2.2, Proposition5.2.3, Lemma5.2.6, Theorem5.4.3, Lemma5.4.5, Theorem5.4.6, Definition5.12.1, Definition5.14.2 | 1-4 each |

### With `needs_statement` (20 items — `(sorry : Prop)` placeholder)

- Ch5: Theorem5.10.1, Theorem5.12.2, Corollary5.12.4, Lemma5.13.1-4, Proposition5.14.1, Theorem5.14.3, Theorem5.15.1, Lemma5.15.3, Corollary5.15.4, Theorem5.17.1, Theorem5.18.1-4
- Ch8: Theorem8.1.1, Theorem8.1.5, Example8.1.7

## Items Flagged with `needs_statement` (83 total)

These items have `(sorry : Prop)` as their proposition placeholder — the statement itself needs formalization before proof work can begin.

| Chapter | Count | Items |
|---------|-------|-------|
| Ch2 | 4 | Theorem2.1.1, Theorem2.1.2, Example2.3.14, Proposition2.7.1 |
| Ch5 | 28 | Proposition5.19.1, Corollary5.19.2, Example5.19.3, Proposition5.21.1-2, Theorem5.22.1, Proposition5.22.2, Theorem5.23.2, Proposition5.25.1, Theorem5.25.2, Lemma5.25.3, Theorem5.26.1, Corollary5.26.3, Theorem5.27.1, Theorem5.10.1, Theorem5.12.2, Corollary5.12.4, Lemma5.13.1-4, Proposition5.14.1, Theorem5.14.3, Theorem5.15.1, Lemma5.15.3, Corollary5.15.4, Theorem5.17.1, Theorem5.18.1-4 |
| Ch6 | 17 | Theorem_Dynkin_classification, Problem6.1.5_theorem, Example6.2.2-4, Example6.3.1, Lemma6.4.2, Example6.4.9, Theorem6.5.2, Proposition6.6.5-8, Lemma6.7.2, Theorem6.8.1, Corollary6.8.2-4, Example6.8.5, Problem6.9.1 |
| Ch7 | 6 | Example7.3.2, Example7.5.3, Example7.6.3, Example7.8.3, Definition7.8.6, Example7.9.2, Example7.9.5, Example7.9.6 |
| Ch8 | 3 | Theorem8.1.1, Theorem8.1.5, Example8.1.7 |
| Ch9 | 17 | Proposition9.1.1, Corollary9.1.3, Theorem9.2.1, Definition9.2.2, Proposition9.2.3, Definition9.3.1, Definition9.4.1, Definition9.4.3, Example9.4.4, Definition9.5.1, Example9.5.2, Definition9.6.1-2, Theorem9.6.4, Definition9.7.1-2, Corollary9.7.3 |

## True Placeholder Detection

**Statement-level `True` placeholders:** 0 items found (none use `theorem foo : True`)

**Hypothesis-level `True` placeholders:** 2 items (both already `sorry_free`, flagged with `has_true_hypothesis`):
- `Chapter5/Theorem5_4_4.lean` — `(h_coprime : True)` placeholder for gcd condition
- `Chapter5/Corollary5_1_6.lean` — `(h_all_real : True)` placeholder for "all FS indicators = 1"

These items compile and have no `sorry`, but their hypotheses are weaker than the textbook states. They should eventually be strengthened.

## Anomalies

1. **Theorem4.6.2 and Theorem4.6.3 now sorry_free**: These were listed in issue #607 as needing statement formalization, but the current files contain complete definitions/theorems with no sorry. The issue may be stale.

2. **Large gap in Chapter 5 numbering**: Items 5.10 through 5.18 are mostly scaffolded with `(sorry : Prop)` placeholders, suggesting a batch scaffolding pass that created files without proper statements.

3. **352 items still `missing`**: Most are discussion blobs, frontmatter, introductions, and non-formalizable content (exercises, remarks) that don't have corresponding Lean files. This is expected — not all textbook items map to Lean code.
