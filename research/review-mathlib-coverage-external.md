# Review: Mathlib Coverage for External Dependencies (Stage 2.4 part 1)

**Reviewer**: agent/2accde71
**Date**: 2026-03-16
**Source file**: `research/mathlib-coverage-external.json`
**Method**: `#check` verification of claimed Mathlib declarations against Mathlib v4.28.0

## Summary

Spot-checked 25+ declarations across 15 entries spanning all coverage levels (exact, partial, missing). **Overall quality is good** — coverage classifications are mostly correct, but there are **4 incorrect Mathlib declaration names** and **1 misnamed concept** that should be corrected before downstream stages rely on this data.

## Declaration Existence Verification

### Verified as correct (declarations exist with expected types)

| Entry | Claimed Name | Status |
|-------|-------------|--------|
| Rank-nullity | `LinearMap.rank_range_add_rank_ker` | **Exists** — returns `Module.rank` equation |
| Matrix trace | `Matrix.trace_mul_comm` | **Exists** — `(A * B).trace = (B * A).trace` |
| Group algebra | `MonoidAlgebra` | **Exists** — `(R : Type) → Type → [Semiring R] → Type` |
| Nakayama's lemma | `Submodule.eq_bot_of_le_smul_of_le_jacobson_bot` | **Exists** — correct statement |
| Vandermonde | `Matrix.det_vandermonde` | **Exists** — correct formula |
| Abelian decomposition | `Module.equiv_directSum_of_isTorsion` | **Exists** — for PID, torsion modules |
| Character | `FDRep.character` | **Exists** — `FDRep k G → G → k` |
| Power sums | `MvPolynomial.psum` | **Exists** — `σ → R → [CommSemiring R] → [Fintype σ] → ℕ → MvPolynomial σ R` |
| Representation linHom | `Representation.linHom` | **Exists** — `Representation k G V → Representation k G W → Representation k G (V →ₗ[k] W)` |
| Bilinear forms | `LinearMap.BilinForm` | **Exists** — type alias |
| Dual spaces | `Module.evalEquiv` | **Exists** — requires `Module.IsReflexive` |
| Quadratic forms | `QuadraticMap.PosDef` | **Exists** |
| Topological groups | `IsTopologicalGroup` | **Exists** — `Prop` predicate |
| Lie algebras | `LieAlgebra.Orthogonal.so`, `LieAlgebra.SpecialLinear.sl` | **Both exist** — as `LieSubalgebra R (Matrix n n R)` |
| Universal enveloping | `UniversalEnvelopingAlgebra` | **Exists** |
| Jordan-Hölder | `CompositionSeries`, `JordanHolderLattice` | **Both exist** |
| Semisimplicity | `IsSemisimpleRing`, `IsArtinianRing` | **Both exist** |
| Ext functors | `Ext` | **Exists** — as `ℕ → Functor Cᵒᵖ (Functor C (ModuleCat R))` |
| Graph theory | `SimpleGraph.IsTree` | **Exists** |
| Zorn's lemma | `zorn_le` | **Exists** — for `Preorder` |
| Permutations | `Equiv.Perm.cycleType` | **Exists** — returns `Multiset ℕ` |
| Finite field card | `FiniteField.card` | **Exists** — `∃ n, Nat.Prime p ∧ card K = p ^ n` |
| GaloisField | `GaloisField` | **Exists** — `(p : ℕ) → [Fact (Nat.Prime p)] → ℕ → Type` |
| Legendre symbol | `legendreSym` | **Exists** (but wrong name in JSON — see below) |

### Declarations that do NOT exist (errors found)

| Entry | Claimed Name | Actual Status | Correct Name |
|-------|-------------|---------------|-------------|
| Finite fields (entry 23) | `FiniteField` | **Does not exist** as a standalone type | Not a type; `FiniteField.card` exists as a lemma but `FiniteField` is not a class/structure |
| Finite fields (entry 23) | `ZMod.legendreSym` | **Does not exist** | Correct name is `legendreSym` (top-level, not in `ZMod` namespace) |
| Exact sequences (entry 27) | `CategoryTheory.Functor.PreservesFiniteLimits` | **Does not exist** | Correct name is `CategoryTheory.Limits.PreservesFiniteLimits` |
| Natural transformations (entry 48) | `CategoryTheory.Functor.Representable` | **Does not exist** | Correct name is `CategoryTheory.Functor.RepresentableBy` (a structure, not a class) |

## Coverage Classification Assessment

### Correctly classified entries (sampled)

- **Exact matches** (Fields, Vector spaces, Linear maps, Matrix algebra, Group algebra, Nakayama, Vandermonde, Zorn, etc.): All correctly classified. The Mathlib types genuinely match the described mathematical concepts.

- **Partial matches** (Finite abelian groups, Jordan-Hölder, Wedderburn-Artin, Characters, Idempotents, PBW): Appropriately labeled. The partial classification correctly identifies that infrastructure exists but the specific theorem statement is missing.

- **Missing entries** (Dynkin diagrams, Gabriel's theorem, Schur-Weyl, Frobenius reciprocity, Mackey, Schur orthogonality, Hochschild cohomology, deformation theory): Correctly classified as absent from Mathlib.

### Questionable classification

- **Frobenius reciprocity** (entry 41): Classified as `missing`, but the `mathlib_names` field lists `Representation.linHom` and `Representation.ofMulAction`, both of which **do exist**. The classification is correct in that Frobenius reciprocity itself is absent, but the presence of existing names in the `mathlib_names` field for a `missing` entry is potentially confusing for downstream consumers. The notes clarify this correctly.

- **Schur orthogonality** (entry 42): Classified as `missing` with `mathlib_names` listing `FDRep.character` and `Representation`, both of which exist. Same pattern as above — infrastructure present but the specific theorem absent.

### Note on `CharacterModule`

The finite abelian groups entry (entry 9) lists `CharacterModule` — this exists as a type alias for `AddChar A (Multiplicative ℤ)`. This is correctly noted but is distinct from representation-theoretic characters.

## Systematic Issues

1. **4 wrong declaration names**: `FiniteField`, `ZMod.legendreSym`, `CategoryTheory.Functor.PreservesFiniteLimits`, `CategoryTheory.Functor.Representable` — these need correction so downstream tools can use the names programmatically.

2. **Pattern: `missing` entries listing existing partial infrastructure in `mathlib_names`**: Entries 41 (Frobenius) and 42 (Schur orthogonality) are classified `missing` but list names that exist. This is technically accurate (the theorem is missing, the infrastructure isn't) but could confuse automated consumers. Suggest using a separate `infrastructure_names` field or documenting this pattern.

3. **No `ContinuousMonoidHom` verification**: The topological groups entry (entry 20) claims `ContinuousMonoidHom` exists. This was not verified in this review. The related `IsTopologicalGroup` was verified.

## Recommendations

1. **Fix the 4 wrong names** before Stage 2.5/2.6 consume this file
2. **Add a note in the summary** about the pattern where `missing` entries can still have valid `mathlib_names` (for infrastructure)
3. **Overall quality is sufficient** for downstream stages — the coverage level classifications are accurate even where individual declaration names are wrong

## Verdict

**Acceptable with corrections.** The coverage research correctly identifies what Mathlib has and doesn't have for this book's external dependencies. The 4 name errors are minor (they don't change any coverage classification) but should be fixed for data integrity.
