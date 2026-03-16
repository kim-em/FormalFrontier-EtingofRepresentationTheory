# Dependency Analysis Accuracy Review

Issue: #473

## Methodology

- **Internal dependencies**: Spot-checked 10 items spanning 5 types (theorem, definition, exercise, discussion, lemma/proposition) across 5 chapters (2, 3, 4, 5, 6, 7). For each, read the blob content, identified explicit and implicit references, and compared against dependencies in `dependencies/internal.json`.
- **External dependencies**: Spot-checked 8 of 58 entries spanning all 3 categories (4 external_result, 2 folklore, 2 undergraduate_prerequisite). For each, read 2 listed item blobs to verify the dependency is actually needed, and assessed categorization.

## Internal Dependency Findings

### Items reviewed

| Item | Type | Chapter | Listed Deps | Explicit Refs in Blob | False Negatives? |
|------|------|---------|-------------|----------------------|-----------------|
| Chapter3/Theorem3.3.1 | theorem | 3 | 138 | None (self-contained statement) | None |
| Chapter5/Theorem5.4.4 | theorem | 5 | 272 | None | None |
| Chapter2/Definition2.3.1 | definition | 2 | 23 | None | None |
| Chapter7/Definition7.1.1 | definition | 7 | 460 | None (fresh concept) | None |
| Chapter4/Exercise4.3.1 | exercise | 4 | 197 | Q_8 (from Example4.3_Q8, captured) | None |
| Chapter6/Problem6.1.2 | exercise | 6 | 397 | "Problem 6.1.1" (captured) | None |
| Chapter2/Discussion_2.6 | discussion | 2 | 53 | Implicit: free algebra (captured) | None |
| Chapter5/Discussion_Young_projectors | discussion | 5 | 307 | P_lambda, Q_lambda from Def 5.12.1 (captured) | None |
| Chapter3/Lemma3.1.6 | lemma | 3 | 132 | "Schur's lemma" = Ch2/Prop2.3.9 (captured) | None |
| Chapter5/Proposition5.19.1 | proposition | 5 | 350 | "Lemma 5.18.3" (captured) | None |

### Internal dependency assessment

**No false negatives found.** All explicit textual references and implicit semantic dependencies are captured by the conservative "all prior items" approach.

**False positives are heavy** as expected. For example:
- Chapter7/Definition7.1.1 (category definition) lists 460 dependencies but is mathematically self-contained
- Chapter6/Problem6.1.2 lists 397 dependencies but explicitly references only Problem 6.1.1

This is the intended behavior of the conservative baseline. Trimming to actual dependencies happens in Stage 3.3 after proofs exist.

**Cross-chapter references**: Found one explicit case (Lemma 3.1.6 referencing Schur's lemma from Chapter 2). The conservative approach correctly captures all cross-chapter references since it includes all prior chapters.

## External Dependency Findings

### Items reviewed

| # | Dependency | Category | Items Verified | Result |
|---|-----------|----------|---------------|--------|
| 1 | Zorn's lemma | external_result | Lemma3.1.6, Prop3.1.4 | Lemma3.1.6 confirmed; Prop3.1.4 indirect (via Problem 2.3.15) |
| 2 | Wedderburn-Artin theorem | external_result | Thm3.5.4, Cor3.5.5 | **Issue**: Book proves this as Thm3.5.4 — may not be external |
| 3 | Frobenius reciprocity | external_result | Def5.8.1, Thm5.9.1 | **Issue**: Def5.8.1 doesn't use it; Introduction_5.11 does but isn't listed |
| 4 | Vandermonde determinant | folklore | Thm5.15.1, Thm5.22.1 | Both confirmed |
| 5 | Properties of the trace | folklore | Def4.6.1, Thm3.6.2 | **Issue**: Def4.6.1 is about unitary reps, not trace |
| 6 | Tensor product of vector spaces | undergraduate_prerequisite | Def2.11.1, Def7.1.1 | **Issue**: Def7.1.1 (category def) doesn't use tensor products |
| 7 | Symmetric group | undergraduate_prerequisite | Introduction_5.11, Thm5.12.2 | Both confirmed |
| 8 | Nakayama's lemma | external_result | Introduction_9.2, Prop9.2.3 | Neither item visibly invokes Nakayama's lemma directly |

### Issues found (4 of 8 have problems)

**Major issue:**
- **Wedderburn-Artin theorem** listed as `external_result`, but the book proves it as Theorem 3.5.4 (derived from the density theorem). It should either be removed from external dependencies or reclassified — it is an internal result, not an external one.

**Moderate issues (incorrect item attribution):**
- **Frobenius reciprocity**: Definition5.8.1 (definition of induced representations) does not depend on Frobenius reciprocity. Introduction_5.11 explicitly uses it ("Using the Frobenius reciprocity, we obtain...") but is not listed.
- **Properties of the trace**: Definition4.6.1 is about unitary representations, not trace properties. Likely a copy-paste error from the "characters" dependency.
- **Tensor product**: Definition7.1.1 (definition of a category) has no connection to tensor products. Incorrect item attribution.

**Minor issues:**
- **Zorn's lemma**: Proposition3.1.4's dependency is indirect (through Problem 2.3.15, which may use Zorn's lemma for existence of irreducible subrepresentations).
- **Nakayama's lemma**: Neither checked item explicitly invokes it. The attribution may be at the section level (projective covers in 9.2) rather than specific items.

### Categorization assessment

Categories are generally reasonable:
- `external_result` entries are correctly identified as named theorems (with the Wedderburn-Artin exception above)
- `folklore` entries (Vandermonde, trace properties) are well-known facts used without proof — appropriate
- `undergraduate_prerequisite` entries (tensor products, symmetric groups) are standard prerequisite material — appropriate

The boundary between `folklore` and `undergraduate_prerequisite` is sometimes blurry (e.g., trace properties could be either), but this does not affect downstream use.

## Overall Assessment

### Internal dependencies: RELIABLE

The conservative "all prior items" baseline is correctly implemented. Zero false negatives across 10 spot-checks. The massive false positive rate (items listing hundreds of unnecessary dependencies) is by design and will be trimmed in Stage 3.3.

**Recommendation: Good to proceed.** Internal dependency data is safe for blueprint assembly (Stage 2.3) and formalization ordering.

### External dependencies: MOSTLY RELIABLE, with targeted fixes needed

Descriptions are accurate. Categorizations are mostly correct. However, **item-level attribution has errors in 4 of 8 checked entries** (50% error rate on item lists). These errors are:
- Wrong items listed (4 cases)
- Missing items that should be listed (1 case)
- One entry (Wedderburn-Artin) that may not be an external dependency at all

**Recommendation: Good enough to proceed**, but the Mathlib coverage research (issues #472, #474) should be aware that item attributions in external.json may be imprecise. The dependency descriptions themselves are accurate and sufficient for Mathlib lookups. Item-level attribution errors can be corrected during Stage 3.3 dependency trimming.

### Summary

| Aspect | Accuracy | Verdict |
|--------|----------|---------|
| Internal deps — false negatives | 0/10 items | Proceed |
| Internal deps — conservative baseline | Correctly applied | Proceed |
| External deps — descriptions | 8/8 accurate | Proceed |
| External deps — categorization | 7/8 correct (Wedderburn-Artin questionable) | Proceed with note |
| External deps — item attribution | 4/8 have errors | Proceed; fix in Stage 3.3 |
