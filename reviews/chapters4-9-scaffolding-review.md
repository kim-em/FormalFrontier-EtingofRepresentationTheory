# Review: Chapters 4+9 Scaffolding — Definition and Theorem Quality

**Issue:** #541
**Date:** 2026-03-16
**Scope:** 21 files in Chapter 4, 18 files in Chapter 9 (39 total)

## 1. Build Verification

`lake build EtingofRepresentationTheory.Chapter4 EtingofRepresentationTheory.Chapter9` completes successfully (8066 jobs). All warnings are expected `sorry` declarations and unused-hypothesis linter warnings. No type errors or import failures. **+**

### Linter warnings (non-sorry)

| File | Warning | Severity |
|------|---------|----------|
| Theorem4_1_1 | `[DecidableEq G]` unused in `sum_of_squares` | Low |
| Proposition4_1_2 | `[DecidableEq G]` unused | Low |
| Theorem4_2_1 | `[DecidableEq G]` unused | Low |
| Corollary4_2_2 | `[DecidableEq G]` unused | Low |
| Corollary4_2_4 | Two unused hypotheses | Low |
| Example4_3_FiniteAbelianGroups | Two unused hypotheses | Low |
| Theorem4_5_1 | Unused variables `V`, `W`; two unused hypotheses | Medium |
| Theorem4_5_4 | Line exceeds 100 chars; two unused hypotheses | Low |
| Theorem4_6_2 | Unused variable `V` (both parts); unused hypotheses | Medium |
| Theorem4_6_3 | Unused variable `hunit` | Medium |
| Proposition4_7_1 | Two unused hypotheses | Low |
| Theorem4_10_2 | Two unused hypotheses | Low |

The unused-variable warnings on `V`, `W`, and `hunit` are direct consequences of the `True` placeholder anti-pattern (see below). Chapter 9 has only `sorry` warnings.

## 2. Chapter 4 — `True` Placeholder Anti-Pattern (Critical)

**12 instances across 10 files** use `True` as the theorem statement type, violating the project rule in CLAUDE.md: "Never use `True` as a placeholder for propositions."

| File | Declaration | Notes |
|------|-------------|-------|
| Theorem4_1_1 | `Theorem4_1_1_sum_of_squares` | Sum-of-squares formula; could use concrete `Fintype.card` equality |
| Theorem4_2_1 | `Theorem4_2_1` | Characters form basis; could state `Fintype.card (ConjClasses G) = ...` |
| Corollary4_2_2 | `Corollary4_2_2` | Irred count = conj class count; same as above |
| Theorem4_5_1 | `Theorem4_5_1` | First orthogonality; Mathlib has `FDRep.character` inner product |
| Theorem4_5_4 | `Theorem4_5_4` | Second orthogonality; could use character sum formula |
| Theorem4_6_2 | `Theorem4_6_2_existence` | Unitarizability; could use `Etingof.UnitaryRepresentation` from Def 4.6.1 |
| Theorem4_6_2 | `Theorem4_6_2_uniqueness` | Uniqueness of unitary structure |
| Theorem4_6_3 | `Theorem4_6_3` | Unitary reps are semisimple; could state `IsSemisimpleModule` |
| Proposition4_7_1 | `Proposition4_7_1` | Matrix element orthogonality |
| Example4_8_1 | `Example4_8_1_Q8_char_id` | Q8 character identity |
| Example4_9_1 | `Example4_9_1_S3_tensor` | Tensor product decomposition |
| Theorem4_10_2 | `Theorem4_10_2` | Frobenius determinant; should reference `Etingof.FrobeniusDeterminant` |

**Impact:** These files declare hypotheses (`V`, `W`, `hunit`, `[DecidableEq G]`, etc.) that are unused because the conclusion is `True`. This hides the actual mathematical content, generates linter warnings, and will require a full rewrite at Stage 3.2. The correct pattern is `(sorry : Prop) := sorry` (as used in Chapter 9) or a real but sorry'd statement.

## 3. Chapter 4 — Well-Formed Files (9 files)

These files have proper type signatures and are ready for Stage 3.2 proof work:

| File | Declaration | Quality |
|------|-------------|---------|
| Theorem4_1_1 | `Theorem4_1_1_semisimple` | Good: `IsSemisimpleRing (MonoidAlgebra k G)` with `IsUnit` hypothesis |
| Proposition4_1_2 | `Proposition4_1_2` | Good: converse of Maschke, properly stated |
| Example4_1_3 | `Example4_1_3` | Good: uses `Multiplicative (ZMod p)` correctly |
| Corollary4_2_4 | `Corollary4_2_4` | Good: uses `FDRep ℂ G` and `FDRep.character` |
| Example4_3_S3 | Two concrete theorems | Good: decidable `Fintype.card` equalities |
| Example4_3_Q8 | Two concrete theorems | Good: `QuaternionGroup 2` for Q8 |
| Example4_3_S4 | Two concrete theorems | Good: `Equiv.Perm (Fin 4)` for S4 |
| Definition4_6_1 | `UnitaryRepresentation` structure | Good: well-typed with `InnerProductSpace` |
| Definition4_10_1 | `FrobeniusDeterminant` | Good: `MvPolynomial G k` return type |
| Lemma4_10_3 | Generic det irreducibility | Excellent: `Irreducible (Matrix.det ...)` fully formalized |
| Example4_8_1 | `Example4_8_1_A5_conj_classes` | Good: concrete `Fintype.card (ConjClasses ...)` |

## 4. Chapter 4 — Conceptual Error

**Example4_3_FiniteAbelianGroups.lean**: The hypothesis `hirr : IsSimpleModule k V` asserts that `V` is a simple *k-module*, not a simple *G-representation*. Over an algebraically closed field, every simple k-module is 1-dimensional by Schur's lemma — the theorem is vacuously true without any assumption on G.

The intended statement requires irreducibility as a G-representation:
- Either `IsSimpleModule (MonoidAlgebra k G) V` (with appropriate module instance), or
- An explicit hypothesis that `V` has no proper G-invariant subspaces

**Priority: High** — this is a mathematically wrong formalization.

## 5. Chapter 4 — Doc-string Inaccuracy

**Theorem4_1_1.lean**: The doc-string claims "Mathlib has `MonoidAlgebra.instIsSemisimpleRing`". Mathlib's actual semisimplicity instance is on `AddMonoidAlgebra`, not `MonoidAlgebra`, and uses `[NeZero (Nat.card G : k)]` as a typeclass rather than `IsUnit (Fintype.card G : k)` as a hypothesis. The scaffold's formulation using `IsUnit` is reasonable as a standalone statement, but the doc-string should reflect the actual Mathlib API.

## 6. Chapter 9 — Overview

Chapter 9 uses the `(sorry : Prop) := sorry` pattern consistently (17 out of 18 scaffolded items). This is the correct placeholder pattern. The one exception is Definition9_1_2, which is a proper Mathlib alias.

### Mathlib Alias (1 file)

| File | Alias Target | Correct? |
|------|-------------|----------|
| Definition9_1_2 | `CompleteOrthogonalIdempotents` | Yes |

Import `Mathlib.RingTheory.Idempotents` is correct. Minor: `[DecidableEq i]` is carried but not strictly needed by the structure itself.

### Placeholder Definitions (9 files)

All 9 definition files use `def ... : (sorry : Prop) := sorry`, which erases the target type entirely. This is acceptable at scaffolding stage but means every definition will need a complete type rewrite at Stage 3.2.

| File | Declaration | Target Type (from doc-string) |
|------|-------------|-------------------------------|
| Definition9_2_2 | `ProjectiveCover` | Structure: `(R : Type*) [Ring R] (P M : ModuleCat R)` |
| Definition9_3_1 | `CartanMatrix` | `Matrix i i N` indexed by simple modules |
| Definition9_4_1 | `projectiveDimension` | `N` or `WithTop N` |
| Definition9_4_3 | `homologicalDimension` | Supremum over modules of projective dimension |
| Definition9_5_1 | `Block` | Partition of simple modules by Ext-linkage |
| Definition9_6_1 | `FiniteAbelianCategory` | `Prop` on `(C : Type*) [Category C] [Abelian C]` |
| Definition9_6_2 | `Progenerator` | `Prop` on an object of a category |
| Definition9_7_1 | `MoritaEquivalent` | `Prop` on two rings |
| Definition9_7_2 | `BasicAlgebra` | `Prop` on a ring (quotient by Jacobson radical is commutative) |

### Placeholder Theorems/Propositions (7 files)

All use `theorem ... : (sorry : Prop) := sorry`. Acceptable for scaffolding.

## 7. Chapter 9 — Issues

### 7a. Incorrect Mathlib Reference: `CategoryTheory.IsGenerator` (Definition9_6_2)

The doc-string states: "Mathlib has `CategoryTheory.Projective` and `CategoryTheory.IsGenerator` separately."

**`CategoryTheory.IsGenerator` does not exist in Mathlib.** The `Generator/Basic.lean` module defines `IsSeparator`, `IsCoseparator`, `IsDetector`, and `IsCodetector` — but not `IsGenerator`. The correct analogue for a projective generator is `CategoryTheory.IsSeparator` (or possibly `IsDetector`).

**Priority: High** — this will send Stage 3.2 workers looking for a non-existent declaration.

### 7b. Incorrect Mathlib Name: `Ideal.jacobson` (Definition9_7_2)

The doc-string says "Uses the Jacobson radical `Ideal.jacobson`." The file imports `Mathlib.RingTheory.Jacobson.Radical`, which defines `Ring.jacobson : Ideal R` (the Jacobson radical of a ring). The correct Mathlib name is `Ring.jacobson`, not `Ideal.jacobson`. (`Ideal.jacobson` exists in `Mathlib.RingTheory.Jacobson.Ideal` but is the Jacobson radical of a specific ideal, not of the ring.)

**Priority: Low** — minor name confusion, but could cause import issues during formalization.

### 7c. Overstatement: Krull-Schmidt "partially in Mathlib" (Theorem9_2_1)

The doc-string says "Uses Krull-Schmidt theorem (partially in Mathlib)." The project's own READINESS report lists Krull-Schmidt as a **missing external dependency** (not in Mathlib). The doc-string should say "not in Mathlib" or "not yet in Mathlib."

**Priority: Low** — misleading but not blocking.

### 7d. Heavy Import (Definition9_5_1)

`import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic` is one of the heaviest imports in Mathlib and is not needed for a placeholder definition. A lighter import (e.g., `Mathlib.Algebra.Homology.ShortComplex.Basic`) or just `import Mathlib` would suffice at scaffolding stage.

**Priority: Low** — no functional impact; the build still succeeds.

## 8. Cross-Chapter Patterns

### Good Patterns
- All files compile without errors
- Doc-strings consistently describe mathematical content, proof strategies, and Mathlib correspondence
- Correct use of Mathlib types: `FDRep`, `MonoidAlgebra`, `ConjClasses`, `QuaternionGroup`, `alternatingGroup`, `CompleteOrthogonalIdempotents`, `Representation`
- Concrete numeric examples (S3, Q8, S4, A5) use decidable equalities — good for `decide` proofs
- `noncomputable` markers used where appropriate (Definition9_4_1, Definition9_4_3, Definition4_10_1)

### Bad Patterns
- **Chapter 4**: `True` placeholder used in 12/21 declarations (57%). This is the dominant quality issue.
- **Chapter 9**: All definitions use `(sorry : Prop)` which erases type information. Acceptable for scaffolding but means every definition needs a full rewrite.
- **Both chapters**: Several doc-strings reference Mathlib declarations that don't exist or use wrong names.

## 9. Summary and Recommendations

### Must-fix before Stage 3.2 proof work

1. **Replace all `True` placeholders in Chapter 4** with either real (sorry'd) statements or `(sorry : Prop)` at minimum. The `True` pattern generates spurious linter warnings and hides mathematical content.

2. **Fix `Example4_3_FiniteAbelianGroups`** — change `IsSimpleModule k V` to `IsSimpleModule (MonoidAlgebra k G) V` or equivalent representation-theoretic simplicity.

3. **Fix Definition9_6_2 doc-string** — replace `CategoryTheory.IsGenerator` with `CategoryTheory.IsSeparator` (the actual Mathlib declaration).

### Should-fix (lower priority)

4. Fix `Theorem4_1_1` doc-string re: `MonoidAlgebra.instIsSemisimpleRing`
5. Fix `Definition9_7_2` doc-string: `Ideal.jacobson` → `Ring.jacobson`
6. Fix `Theorem9_2_1` doc-string: Krull-Schmidt is not in Mathlib
7. Remove unused `[DecidableEq G]` hypotheses from Chapter 4 files (or defer to proof stage)
