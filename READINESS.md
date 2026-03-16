# Readiness Report — Etingof, Introduction to Representation Theory

**Generated:** 2026-03-16 (Stage 2.6)
**Status:** Awaiting human review before Phase 3 formalization begins.

---

## Executive Summary

The book contains **583 items** across 11 chapters. Of these, **230 are formal items** (definitions, theorems, propositions, lemmas, corollaries, examples) that require Lean formalization. The remaining 353 are non-formal (discussion, introductions, remarks, exercises).

Mathlib coverage is strong for foundational material: **55% of definitions** have exact Mathlib matches, and **59% of external dependencies** are fully covered. The main gaps cluster in Chapters 5 (symmetric group representations), 6 (quiver representations), and 9 (homological algebra of categories). Chapters 2–4 and 7–8 are largely ready to formalize with existing Mathlib infrastructure.

**Recommendation:** Proceed to Phase 3. Begin with Chapters 2–3 (strongest Mathlib coverage), then Chapter 4 and 7, while building gap definitions for Chapters 5–6 and 9 in parallel.

---

## 1. Coverage Summary

### 1.1 Book Definitions (83 total)

| Coverage Level | Count | Percentage | Meaning |
|---------------|-------|------------|---------|
| Exact match   | 46    | 55%        | Direct Mathlib counterpart exists |
| Partial       | 21    | 25%        | Foundation exists, needs adaptation |
| Gap           | 16    | 20%        | Must be built from scratch |

### 1.2 External Dependencies (58 total)

| Coverage Level | Count | Percentage | Meaning |
|---------------|-------|------------|---------|
| Exact match   | 34    | 59%        | Fully available in Mathlib |
| Partial       | 15    | 26%        | Infrastructure exists, connecting lemmas needed |
| Missing       | 9     | 15%        | Not in Mathlib at all |

### 1.3 External Sources for Gaps

Of the 52 items with gap/partial Mathlib coverage:
- **79 natural language references** identified (textbooks, monographs)
- **7 other formal system references** (MathComp/UniMath in Coq)
- **1 Lean library reference** (non-Mathlib)

Key reference texts: Serre (Linear Representations), Fulton & Harris (Representation Theory), Schiffler (Quiver Representations), Humphreys (Lie Algebras), Assem–Simson–Skowroński (Associative Algebras), Weibel (Homological Algebra).

---

## 2. Chapter-by-Chapter Readiness

| Chapter | Items | Formal | Defs | Proofs | Examples | Exercises | Def Coverage |
|---------|-------|--------|------|--------|----------|-----------|--------------|
| Frontmatter | 4 | 0 | 0 | 0 | 0 | 0 | — |
| Ch 1 | 3 | 0 | 0 | 0 | 0 | 0 | — |
| **Ch 2** | **117** | **42** | **25** | **7** | **10** | **26** | **19 exact, 6 partial, 0 gap** |
| **Ch 3** | **58** | **23** | **5** | **16** | **2** | **11** | **4 exact, 1 partial, 0 gap** |
| **Ch 4** | **60** | **21** | **2** | **12** | **7** | **15** | **0 exact, 1 partial, 1 gap** |
| Ch 5 | 157 | 59 | 10 | 46 | 3 | 17 | 4 exact, 1 partial, 5 gap |
| Ch 6 | 64 | 32 | 12 | 14 | 6 | 11 | 2 exact, 5 partial, 5 gap |
| **Ch 7** | **59** | **26** | **13** | **1** | **12** | **6** | **12 exact, 1 partial, 0 gap** |
| **Ch 8** | **24** | **9** | **6** | **2** | **1** | **9** | **5 exact, 1 partial, 0 gap** |
| Ch 9 | 35 | 18 | 10 | 6 | 2 | 7 | 0 exact, 5 partial, 5 gap |
| Backmatter | 2 | 0 | 0 | 0 | 0 | 0 | — |

**Bold** chapters have zero or one definition gap — these are ready to formalize.

### Readiness Assessment by Chapter

- **Chapters 2–3** ✅ Ready. All definitions have exact or partial Mathlib matches. Strong Mathlib infrastructure for algebras, representations, modules, Schur's lemma, Maschke's theorem.
- **Chapter 4** ✅ Mostly ready. 1 gap definition (Frobenius determinant). 12 proof targets; character theory and induced representations are partially covered.
- **Chapter 7** ✅ Ready. 12/13 definitions have exact matches (Lie algebras, universal enveloping algebras, sl(2) representations). Only semisimple abelian category needs adaptation.
- **Chapter 8** ✅ Ready. 5/6 definitions exact. Tor functors need adaptation but Mathlib's homological algebra infrastructure is strong.
- **Chapter 5** ⚠️ Moderate risk. 5 gap definitions (Frobenius-Schur indicator, virtual representations, Kostka numbers, algebraic representations of GL(V), real/quaternionic types). 46 proof targets — the largest chapter.
- **Chapter 6** ⚠️ High risk. 5 gap definitions (dimension vectors, sinks/sources, reflection functors). 5 partial definitions (Dynkin diagrams, roots, simple roots). Gabriel's theorem is a missing external dependency.
- **Chapter 9** ⚠️ High risk. 5 gap definitions (Cartan matrix, projective dimension, blocks, basic algebras). 5 partial definitions (Morita equivalence, projective covers, idempotents). Hochschild cohomology and deformation theory are missing external deps.

---

## 3. Readiness Tiers

### Tier 1 — Ready to Formalize (46 definitions with exact Mathlib match)

These definitions map directly to existing Mathlib declarations. Formalization involves writing thin wrappers or type aliases. Chapters 2, 3, 7, and 8 are almost entirely in this tier.

Key exact-match definitions include: `Algebra`, `Module`, `Representation`, `CategoryTheory.SimpleObject`, `LieAlgebra`, `UniversalEnvelopingAlgebra`, `TensorProduct`, `Quiver`, `CategoryTheory.Functor`.

### Tier 2 — Needs Adaptation (21 definitions with partial match)

Mathlib has the foundations, but the book's specific formulation needs work. Examples:
- Indecomposable representation (Mathlib has `Indecomposable` for objects, needs specialization)
- Quiver representation (Mathlib has `Quiver` but representation functor needs construction)
- Path algebra (Mathlib has `Quiver.PathAlgebra` concept but API may need extension)
- Dynkin diagrams, root systems (Mathlib has partial infrastructure)
- Morita equivalence (Mathlib has equivalence of categories, needs algebraic Morita theory)

### Tier 3 — Build from Scratch (16 definitions)

No Mathlib counterpart. Must be defined fresh in Lean:

| Definition | Chapter | Complexity |
|-----------|---------|------------|
| Frobenius determinant | Ch 4 | Low — matrix determinant over group algebra |
| Real/quaternionic type | Ch 5 | Medium — classification of irreps by Schur indicator |
| Frobenius-Schur indicator | Ch 5 | Medium — sum of character values on squares |
| Virtual representation | Ch 5 | Low — Grothendieck group element |
| Kostka numbers | Ch 5 | Medium — combinatorial, depends on Young tableaux |
| Algebraic representation of GL(V) | Ch 5 | Medium — polynomial maps condition |
| Dimension vector | Ch 6 | Low — function from vertices to ℕ |
| Sink and source | Ch 6 | Low — combinatorial property of quiver vertex |
| Reversed quiver at vertex | Ch 6 | Low — local edge reversal |
| Reflection functor F⁺ | Ch 6 | High — functor between representation categories |
| Reflection functor F⁻ | Ch 6 | High — dual of F⁺ |
| Cartan matrix (algebra) | Ch 9 | Medium — matrix of composition multiplicities |
| Projective dimension | Ch 9 | Medium — length of projective resolution |
| Homological dimension | Ch 9 | Medium — supremum of projective dimensions |
| Blocks | Ch 9 | Medium — equivalence classes of linked simple modules |
| Basic algebra | Ch 9 | Medium — no repeated simple modules in socle |

---

## 4. Risk Areas

### 4.1 Missing External Dependencies (9 items, not in Mathlib)

These are major theorems the book relies on that have no Mathlib formalization:

1. **Dynkin diagram classification** — Required for Chapter 6. Complete classification of positive-definite Cartan matrices.
2. **Gabriel's theorem** — Central to Chapter 6. Connects quiver representation type to Dynkin diagrams.
3. **Krull-Schmidt theorem** — Used across multiple chapters for unique decomposition of modules.
4. **Schur-Weyl duality** — Required for Chapter 5 symmetric group theory.
5. **Frobenius reciprocity** — Core result for Chapter 4 induced representations.
6. **Mackey's theorem** — Intertwining number formula, Chapter 4.
7. **Generalized Schur orthogonality** — Character theory foundation, Chapters 3–4.
8. **Deformation theory of algebras** — Chapter 9 topic.
9. **Hochschild cohomology** — Chapter 9 topic.

**Mitigation:** Items 1–7 can potentially be proved in the project (they are classical results with known proofs). Items 8–9 are the subject matter of Chapter 9 and must be developed as part of the formalization.

### 4.2 Chapter 5 Volume

Chapter 5 has **157 items** (27% of the book) and **46 proof targets** (44% of all proofs). It covers symmetric group representations, Young tableaux, Schur-Weyl duality — all areas with significant Mathlib gaps. This chapter will likely require the most effort.

### 4.3 Dependency Chain Depth

The internal dependency graph is conservative (each item depends on all preceding items), producing **169,653 edges**. This will be trimmed to actual dependencies during Phase 3.3. Until then, the formalization order follows the book's linear order, which is safe but may miss opportunities for parallelism.

---

## 5. Suggested Formalization Order

Based on dependency structure, Mathlib coverage, and proof target density:

### Phase 3.1 — Scaffolding (all chapters)
Create Lean module structure and file stubs for all 583 items.

### Phase 3.2 — Definitions and Statements

**Wave 1: Chapters 2–3** (30 definitions, 23 proofs)
- Strongest Mathlib coverage (all definitions exact or partial)
- Foundational: algebras, representations, modules, Schur's lemma, Maschke's theorem, density theorem
- Unblocks all later chapters

**Wave 2: Chapters 4, 7** (15 definitions, 13 proofs)
- Chapter 4: Character theory, orthogonality, induced representations (1 gap definition)
- Chapter 7: Lie algebras, universal enveloping algebra, sl(2) representations (0 gap definitions)
- Can proceed in parallel

**Wave 3: Chapter 8** (6 definitions, 2 proofs)
- Homological algebra applications — short chapter, strong Mathlib coverage
- Depends on Chapter 7

**Wave 4: Chapters 5–6** (22 definitions, 60 proofs)
- Chapter 5: Symmetric groups, Young tableaux — largest proof load, most gaps
- Chapter 6: Quiver representations, Gabriel's theorem — most novel definitions
- Start gap definitions early; proofs after Waves 1–2 establish foundations

**Wave 5: Chapter 9** (10 definitions, 6 proofs)
- Categories, homological dimension, deformation theory
- Most dependent on earlier material; formalize last

### Phase 3.3 — Dependency Trimming
After proofs exist, replace conservative dependencies with actual `import`/`uses` edges.

---

## 6. Estimated Scope

| Category | Count | Notes |
|----------|-------|-------|
| Lean files to create | ~230 | One per formal item |
| Definitions to formalize | 83 | 46 exact, 21 partial, 16 gap |
| Proof targets | 104 | Theorems + propositions + lemmas + corollaries |
| Examples to formalize | 43 | Concrete computations |
| Exercises (optional) | 102 | Not required for main formalization |
| New Mathlib-gap definitions | 16 | Must be built from scratch |
| Missing external theorems | 9 | Major results to prove or axiomatize |
| External source references | 87 | Available for guidance on gaps |

### Effort Distribution Estimate

- **Low effort** (exact Mathlib match): ~46 definitions + their dependent theorems — mostly wiring
- **Medium effort** (partial match + adaptation): ~21 definitions + gap-filling proofs
- **High effort** (from scratch): ~16 definitions + 9 missing external theorems + Chapter 5/6 proof load

---

## 7. Data Sources

This report synthesizes the following Phase 2 outputs:

| File | Description | Items |
|------|-------------|-------|
| `progress/items.json` | All book items with types and locations | 583 |
| `dependencies/internal.json` | Conservative internal dependency graph | 169,653 edges |
| `dependencies/external.json` | External dependency classification | 58 deps |
| `research/mathlib-coverage-external.json` | Mathlib coverage for external deps | 58 items |
| `research/mathlib-coverage-definitions.json` | Mathlib coverage for book definitions | 83 items |
| `research/external-sources.json` | Non-Mathlib sources for gaps | 52 items, 87 citations |
| `blueprint/src/content.tex` | Assembled leanblueprint DAG | 583 nodes |

---

*This is a human review checkpoint. Phase 3 formalization should not begin until this report is reviewed and approved.*
