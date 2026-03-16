# Review: Chapter 2 Definition Scaffolding Quality and Patterns

**Issue:** #528
**Date:** 2026-03-16
**Scope:** 25 definition `.lean` files in `EtingofRepresentationTheory/Chapter2/`

## 1. Build Verification

`lake build` completes successfully (1825 jobs). Only two warnings, both expected `sorry` warnings:

- `Definition2_8_4.lean:21` — `PathAlgebra` (gap definition, not in Mathlib)
- `Definition2_8_9.lean:17` — `QuiverRepresentation.directSum` (gap definition, not in Mathlib)

**No type errors, import failures, or namespace issues.** ✓

## 2. Lean↔Blob↔items.json Alignment

All 25 items.json definition entries have:
- A corresponding `.lean` file (dots→underscores naming: `Definition2.3.1` → `Definition2_3_1.lean`) ✓
- A corresponding blob file in `blobs/Chapter2/` ✓
- No orphan Lean files or blob files ✓

## 3. Per-File Spot-Check (10 files + 1 bonus)

### Definition2_2_1 — Associative Algebra (exact-match) ✓
- `abbrev Etingof.AssociativeAlgebra ... := Algebra k A`
- Mathlib alias correct. Doc-string matches blob. Import minimal.
- **Score: 5/5**

### Definition2_2_2 — Unit in an Associative Algebra (exact-match) ⚠
- `example (A : Type*) [Ring A] : (1 : A) = 1 := rfl`
- Doc-string correctly explains units are built into `Ring`.
- **Issue:** The `example` is a tautology (`1 = 1` by `rfl`). It does not demonstrate the unit laws (`one_mul`, `mul_one`). Better as either `example (A : Type*) [Ring A] (a : A) : 1 * a = a := one_mul a` or as a doc-only file.
- **Score: 3/5**

### Definition2_3_1 — Representation / Left A-module (exact-match) ✓
- `abbrev Etingof.Representation ... := Module A V`
- Correct Mathlib concept. Loses the field `k` parameter but that's fine — `Module A V` is the right abstraction.
- **Score: 4/5**

### Definition2_3_5 — Irreducible (Simple) Representation (exact-match) ✓
- `abbrev Etingof.IrreducibleRepresentation ... := IsSimpleModule A V`
- Perfect match. Import `Mathlib.RingTheory.SimpleModule.Basic` is correct.
- **Score: 5/5**

### Definition2_3_7 — Direct Sum of Representations (exact-match) ⚠
- `abbrev Etingof.DirectSumRepresentation ... := V1 × V2`
- Using product type for binary direct sum is standard Mathlib practice.
- **Issue:** Import `Mathlib.LinearAlgebra.DirectSum.Finite` is heavier than needed; `Mathlib.Algebra.Module.Prod` would suffice.
- **Score: 4/5**

### Definition2_3_8 — Indecomposable Representation (gap) ✓
- Custom `Prop` definition: `Nontrivial V ∧ ∀ (W1 W2 : Submodule A V), IsCompl W1 W2 → W1 = ⊥ ∨ W2 = ⊥`
- **Uses proper `Prop`, not `True`.** Mathematically correct formalization.
- **Score: 5/5**

### Definition2_7_3 — Faithful Representation (exact-match) ✓
- `abbrev Etingof.FaithfulRepresentation ... := FaithfulSMul A V`
- Correct. Minimal import.
- **Score: 5/5**

### Definition2_8_4 — Path Algebra (gap, sorry'd) ⚠⚠
- `noncomputable def Etingof.PathAlgebra ... : Type* := sorry`
- **Critical issue:** The return type is `Type*` with body `sorry`. This produces `sorryAx Type*` — a sorry'd *type*. No algebra instances can be built on it. Downstream code cannot use `PathAlgebra` in any meaningful way.
- **Correct approach:** Define the carrier type concretely (e.g., as a free module on `Quiver.Path`) and sorry the `Algebra` instance.
- **Score: 2/5**

### Definition2_8_9 — Direct Sum of Quiver Representations (gap, sorry'd) ⚠
- `noncomputable def Etingof.QuiverRepresentation.directSum ... := sorry`
- **Issue:** The blob file `blobs/Chapter2/Definition2.8.9.md` is empty (blank). The Lean doc-string was written from the items.json title alone, without source text to verify against.
- The sorry'd definition itself is reasonable for a gap item (returns a `QuiverRepresentation`, not a `Type*`).
- **Score: 3/5**

### Definition2_9_1 — Lie Algebra (exact-match) ✓
- `abbrev Etingof.LieAlgebraDef ... := LieAlgebra k L`
- Correct. Uses `[CommRing k]` (more general than Etingof's field, which is fine).
- **Score: 5/5**

### Definition2_12_1 — Symmetric/Exterior/Universal Enveloping Algebras (exact-match) ✓
- Three `abbrev`s in one file for the three parts of the definition. All correct Mathlib aliases.
- **Score: 5/5**

### Definition2_14_1 — Tensor Product of Lie Algebra Representations (partial-match) ⚠
- `abbrev Etingof.LieTensorProduct ... := TensorProduct k V W`
- **Issue:** Aliases only the carrier type, not the Lie module structure. The definition in Etingof is specifically about the *Lie action* (Leibniz rule), not just the vector space. The doc-string even mentions `Mathlib.Algebra.Lie.TensorProduct` may have the instance, but this import is absent.
- **Score: 3/5**

## 4. Systematic Patterns

### Good patterns
- **Consistent `Etingof.*` namespace** across all files
- **`abbrev` for Mathlib aliases, `def`/`structure` for custom definitions** — correct transparency distinction
- **Module doc-strings** include both mathematical definition and Mathlib correspondence
- **Naming convention** is consistent: blob dots→underscores for Lean filenames
- **Type class choices** are reasonable throughout

### Bad patterns

1. **Type-valued `sorry` (Definition2_8_4):** A `sorry` producing `Type*` is worse than useless — downstream definitions cannot build on it. This pattern must not propagate.

2. **Carrier-only aliases (Definition2_14_1):** Aliasing `TensorProduct k V W` without the Lie module instance misses the mathematical content of the definition. When a definition is about *structure on a type*, the alias should capture the structure.

3. **Tautological example (Definition2_2_2):** `(1 : A) = 1` by `rfl` demonstrates nothing. "Built-in" concepts need a more meaningful formalization or should be doc-only.

4. **Empty blob undetected (Definition2_8_9):** The blob is blank but was scaffolded anyway. The pipeline should flag empty blobs as blocking rather than proceeding with title-only scaffolding.

5. **Import weight varies:** Some files use heavier imports than necessary (e.g., `DirectSum.Finite` when only `Module.Prod` is needed). Minor but worth standardizing.

## 5. Recommendations for Subsequent Scaffolding

1. **Never `sorry` a `Type*`.** For gap definitions, define the carrier type concretely and `sorry` the algebraic instances. A sorry'd type breaks all downstream usage.

2. **For "built-in" concepts**, either demonstrate the actual properties (`one_mul`, `mul_one`) or make the file doc-only with no Lean code. Tautologies add noise.

3. **For definitions about structure on types**, import and reference the relevant instance, not just the carrier. If the instance doesn't exist, note it explicitly as a gap.

4. **Verify blob content before scaffolding.** If a blob is empty, flag it rather than proceeding from the title alone.

5. **Use minimal imports.** Prefer the most specific Mathlib module that provides what's needed.

6. **The quiver-related custom structures (QuiverRepresentation, QuiverSubrepresentation) are well-designed** and should serve as a good pattern for similar constructions in later chapters.
