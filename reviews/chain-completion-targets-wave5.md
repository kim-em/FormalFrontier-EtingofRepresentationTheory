# Chain-Completion Targets — Wave 5

Date: 2026-03-17
Basis: items.json audit (165/583 sorry_free = 28.3%, after fixing 2 stale entries)

## Top 5 Recommended Targets

### 1. Chapter 5 / Lemma 5.13.1 + Lemma 5.13.2 (1 sorry each)

Both are `proof_formalized` with exactly 1 sorry remaining. Issues already exist:
- #776 (Lemma 5.13.1 pigeonhole_transposition)
- #777 (Lemma 5.13.2 pigeonhole_transposition)

Completing both unlocks Lemma 5.13.3 (also 1 sorry, `statement_formalized`) which
chains into the sorry_free Lemma 5.13.4. This is a 3-item chain completion in the
Specht module section.

**ROI: High** — 3 items potentially sorry_free from 3 single-sorry proofs.

### 2. Chapter 9 / Example 9.5.2 (2 sorries)

Already `proof_formalized` with issue #791 planned. Adjacent to sorry_free
Definition 9.5.1. Completing it would bring Chapter 9's sorry_free count to 13/35.

**ROI: Medium-high** — active work, 2 sorries, extends a sorry_free chain.

### 3. Chapter 5 / Theorem 5.4.6 (4 sorries)

`proof_formalized` with issues #789 and #790 covering the 4 helper lemmas
(scalar_contradicts_simplicity, nontrivial_irrep_dim_ge_two, character_isIntegral,
trivialFDRep_simple). Adjacent to sorry_free Lemma 5.4.7 downstream.

**ROI: Medium** — 4 sorries is more work but issues are already planned and split.

### 4. Chapter 6 / Lemma 6.4.6 (1 sorry, scaffolded)

Sandwiched between sorry_free Definition 6.4.5 and Definition 6.4.7. Completing it
extends a sorry_free chain in the root systems section. No existing issue — **needs
a new issue created**.

**ROI: Medium** — single sorry, chain-extending, but no issue yet. Chapter 6 is at
11/64 sorry_free so every completion helps.

### 5. Chapter 2 / Example 2.3.14 (1 sorry, scaffolded)

Adjacent to sorry_free Example 2.3.14_continued. Chapter 2 is at 36/117 sorry_free.
No existing issue — **needs a new issue created**.

**ROI: Medium-low** — easy single sorry but doesn't unblock much downstream.

## Already-Planned Items (no new issues needed)

| Item | Sorries | Issue |
|------|---------|-------|
| Ch4/Theorem4.10.2 | 2 | #784 |
| Ch5/Theorem5.4.6 | 4 | #789, #790 |
| Ch5/Lemma5.13.1 | 1 | #776 |
| Ch5/Lemma5.13.2 | 1 | #777 |
| Ch6/Example6.3.1 | remaining sorry | #785 |
| Ch9/Theorem9.2.1 | sorry | #764 |
| Ch9/Example9.5.2 | 2 | #791 |
| Ch3/Theorem3.7.1 | 1 | #596 |

## New Issues Recommended

1. **Ch6/Lemma6.4.6** — prove root coefficients are all nonneg or all nonpos (1 sorry, chain-extending)
2. **Ch2/Example2.3.14** — prove irreducible/indecomposable reps of k and k[x] (1 sorry, chain-extending)
3. **Ch9/Proposition9.2.3** — prove Hom from projective cover computes JH multiplicity (1 sorry, extends from Definition 9.2.2)

## Status Summary After Audit

- 165/583 items sorry_free (28.3%) — up from 163 after fixing 2 stale entries
- 5 items proof_formalized (all verified to still contain sorry)
- 4 items statement_formalized (verified)
- 59 items scaffolded (all verified, files exist)
- 352 items not yet started
- Stale entries fixed: Chapter3/Theorem3.10.2, Chapter4/Corollary4.2.2 (both upgraded to sorry_free)
