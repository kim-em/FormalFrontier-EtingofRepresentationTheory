# Review: Chapter 5 Scaffolding — Cross-Section Consistency

**Issue:** #542
**Date:** 2026-03-16
**Scope:** 59 `.lean` files in `EtingofRepresentationTheory/Chapter5/`
Split across three scaffolding batches:
- Batch 1 (#523): Sections 5.1–5.9 (24 items)
- Batch 2 (#524): Sections 5.10–5.18 (20 items)
- Batch 3 (#525): Sections 5.19–5.27 (15 items)

## 1. Critical Finding: `True` Placeholder Abuse

**11 of 59 files use `True` as their theorem conclusion.** This violates the project's
explicit rule: "Never use `True` as a placeholder for propositions — it hides the actual
requirements and will need a full refactor to fix."

All 11 are in **Batch 1** (sections 5.1–5.9). Batches 2 and 3 correctly use
`(sorry : Prop) := by sorry` throughout.

Affected files:
| File | What should be stated |
|------|----------------------|
| Example5_1_3 (×2) | S₃ representations are real type; Q₈ reps are quaternionic type |
| Theorem5_3_1 | dim(V) divides \|G\| for irreducible V |
| Proposition5_3_2 | \|C\|·χ(C)/dim(V) is an algebraic integer |
| Theorem5_4_4 | Conjugacy class of prime power size implies normal subgroup |
| Theorem5_6_1 | Character of tensor product is product of characters |
| Lemma5_7_2 | Inner product of virtual characters equals multiplicity sum |
| Definition5_8_1 | Frobenius-Schur indicator theorem (should be a theorem not definition) |
| Theorem5_9_1 | Induced representation properties |
| Corollary5_1_6 | Number of real/complex/quaternionic irreps formula |
| Lemma5_4_7 | Every row of character table has a nonzero entry at prime-power conjugacy class |

**Impact:** These 11 files will all need refactoring before Stage 3.2 proof work can begin.
This is the most significant cross-section divergence: Batch 1 used `True` while
Batches 2 and 3 consistently used the correct `(sorry : Prop)` pattern.

## 2. Cross-Section Consistency Analysis

### 2.1 Import Patterns — CONSISTENT ✓

All 59 files use `import Mathlib` exclusively. No selective imports, no variation.

### 2.2 Namespace Structure — CONSISTENT ✓

All declarations use the `Etingof.*` prefix (e.g., `Etingof.Theorem5_10_1`,
`Etingof.StandardYoungTableau`). No namespace blocks, no variation.

### 2.3 Doc-String Format — CONSISTENT ✓

All 59 files follow the same template:
1. `/-! # [Type] [Number]: [Title]` module doc with mathematical description
2. `## Mathlib correspondence` section documenting alignment with Mathlib
3. Per-declaration `/-- ... (Etingof [ItemID]) --/` doc comment

No variation across batches.

### 2.4 Sorry Pattern — DIVERGENT ⚠

| Pattern | Batch 1 | Batch 2 | Batch 3 |
|---------|---------|---------|---------|
| `(sorry : Prop) := by sorry` | 13 files | 19 files | 15 files |
| `True := by trivial` | 11 files | 1 file | 0 files |
| Definition with `sorry` body | — | — | — |

Batch 2's single `True` instance is Example5_12_3 (2 theorems). All other Batch 2
and all Batch 3 files use the correct pattern.

### 2.5 Type Class Assumptions — CONSISTENT within domains ✓

Three coherent patterns emerge, used consistently across all batches:

**Finite group representations:**
```lean
{G : Type*} [Group G] [Fintype G]
{V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
```

**Symmetric group / partition theory:**
```lean
(n : ℕ) (la : Nat.Partition n)
```

**GL(V) / Schur-Weyl:**
```lean
{k : Type*} [Field k] [IsAlgClosed k]
{V : Type*} [AddCommGroup V] [Module k V] [Module.Finite k V]
```

Minor inconsistency: `DecidableEq G` is sometimes included, sometimes not, even for
similar statements. Not blocking, but could cause issues when composing results.

### 2.6 Naming Conventions — CONSISTENT ✓

All use `Etingof.[Type][Section]_[Number]` format. Multi-part results use suffixes
(`_algebraic`, `_integer`, `_vanishing`, `_diagonal`, `_i`, `_ii`). No conflicts.

### 2.7 No Duplicate or Conflicting Definitions ✓

All 73 declarations (59 files, some with multiple declarations) have unique names.
No two files define the same concept differently.

## 3. Spot-Check Results (15 items)

### Batch 1 (5 items)

| File | Verdict | Notes |
|------|---------|-------|
| Definition5_1_1 | ✓ Good | Proper inductive type + two Prop definitions with real math |
| Proposition5_2_3 | ✓ Good | Clean ↔ statement with Matrix.charpoly, proper sorry |
| Theorem5_4_3 | ✓ Good | Burnside's theorem stated correctly with IsSolvable |
| Theorem5_3_1 | ✗ True placeholder | Should state `finrank ℂ V ∣ Fintype.card G` |
| Definition5_7_1 | ✓ Good | Well-structured VirtualRepresentation with finite support |

### Batch 2 (5 items)

| File | Verdict | Notes |
|------|---------|-------|
| Theorem5_10_1 | ✓ Good | Frobenius reciprocity with proper representation params |
| Definition5_12_1 | ✓ Good | 4 definitions (StandardYoungTableau, RowSubgroup, etc.) all sorry'd correctly |
| Theorem5_15_1 | ✓ Good | Frobenius character formula, clean (sorry : Prop) |
| Lemma5_13_2 | ⚠ Minor | `(hlt : sorry)` in assumptions — unusual but not incorrect |
| Example5_12_3 | ✗ True placeholder | Both trivial/sign Specht module examples use True |

### Batch 3 (5 items)

| File | Verdict | Notes |
|------|---------|-------|
| Proposition5_19_1 | ✓ Good | GL(V) centralizer algebra, clean scaffolding |
| Theorem5_22_1 | ✓ Good | Weyl character formula with proper type classes |
| Definition5_23_1 | ✓ Good | IsAlgebraicRepresentation Prop definition, acknowledged TODO |
| Theorem5_25_2 | ✓ Good | Principal series with let bindings, clean |
| Theorem5_26_1 | ✓ Good | Artin's theorem with Set (Subgroup G), clean |

### Summary: 12/15 pass, 2 True placeholder issues, 1 minor

## 4. Additional Observations

### 4.1 Definition5_8_1 is Miscategorized

`Definition5_8_1.lean` contains a `theorem` (about the Frobenius-Schur indicator),
not a definition. The definition of the indicator is in `Definition5_1_4.lean`.
This file should be renamed or restructured.

### 4.2 Lemma5_13_2 Uses Sorry in Hypothesis

```lean
(hlt : sorry) -- la > mu in dominance order
```

This is a valid scaffolding approach (the dominance order isn't defined yet), but it's
unique across all 59 files. Other files with missing prerequisites use comment-only
descriptions. Low priority.

### 4.3 Multi-Part Results Handling

Files with multiple sub-results are consistent across batches:
- Batch 1: Proposition5_2_3 (`_algebraic`, `_integer`), Definition5_2_1 (`_algebraic_number`, `_algebraic_integer`)
- Batch 2: Theorem5_18_1 (`_double_centralizer`, `_commutant_semisimple`, `_decomposition`)
- Batch 3: Proposition5_21_2 (`_geometric`, `_dimension`), Theorem5_23_2 (`_i`, `_ii`)

Suffix convention is consistent.

## 5. Recommendations

### Before Stage 3.2 (blocking)

1. **Replace all 11+2 `True` placeholders** with `(sorry : Prop) := by sorry` or
   (preferably) actual mathematical statements. Priority files:
   - Theorem5_3_1 (dimension divisibility — fundamental result)
   - Proposition5_3_2 (algebraic integer property — used by Theorem5_3_1)
   - Theorem5_4_4 (conjugacy class theorem — used by Burnside)
   - Theorem5_6_1 (tensor product characters — foundational)

### Nice to have (non-blocking)

2. Add `DecidableEq` consistently to all finite group statements that may need it
3. Rename Definition5_8_1 → Theorem5_8_1 (or restructure)
4. Resolve Lemma5_13_2's `(hlt : sorry)` pattern to match the project standard

## 6. Conclusion

**Cross-section consistency is strong in structure but divergent in sorry patterns.**
Batches 2 and 3 are nearly identical in style and quality. Batch 1 has the majority
of issues, with 11 files using `True` placeholders. The structural consistency
(imports, namespaces, doc-strings, naming) is excellent across all three batches,
indicating the workers followed the same template but Batch 1 made different choices
about placeholder statements.

The 13 `True` placeholder files are the only blocking issue for Stage 3.2. All other
findings are minor or stylistic.
