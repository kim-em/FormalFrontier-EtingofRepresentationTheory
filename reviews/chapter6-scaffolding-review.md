# Chapter 6 Scaffolding Review: Gap and Partial Definition Quality

**Date**: 2026-03-16
**Reviewer**: Agent (issue #543)
**Scope**: All 33 Chapter 6 Lean files (12 definitions, 3 lemmas, 4 theorems, 4 propositions, 3 corollaries, 5 examples, 2 problems)

## Build Status

All 33 files compile successfully. Only `sorry` warnings — no type errors, no missing imports.

---

## Gap Definitions (5 items)

### Definition6_5_1 — Dimension Vector ✅ GOOD

```lean
noncomputable def Etingof.dimensionVector {V : Type*} [Fintype V] (k : Type*)
    [Field k] (spaces : V → Type*)
    [∀ v, AddCommGroup (spaces v)] [∀ v, Module k (spaces v)]
    [∀ v, FiniteDimensional k (spaces v)] :
    V → ℕ :=
  fun v => Module.finrank k (spaces v)
```

**Verdict**: Correct and complete. Uses `Module.finrank` which is the standard Mathlib API for finite-dimensional rank. The parameterization over an arbitrary vertex type `V` with `[Fintype V]` is appropriate and more general than the book's `Fin n` vertices.

**Minor suggestion**: Consider adding `(Q : Quiver V)` or similar context to tie this to quiver representations rather than being a standalone function on indexed spaces.

### Definition6_6_1 — Sink and Source ✅ GOOD (with note)

```lean
def Etingof.IsSink (V : Type*) [Quiver V] (i : V) : Prop :=
  ∀ (j : V), IsEmpty (i ⟶ j)

def Etingof.IsSource (V : Type*) [Quiver V] (i : V) : Prop :=
  ∀ (j : V), IsEmpty (j ⟶ i)
```

**Verdict**: Mathematically correct. The `∀ j` quantifier includes `j = i`, which means sinks/sources implicitly have no self-loops. This matches the book's context (simple quivers), but should be documented.

**Note**: The book says "all edges connected to i point towards it" for a sink. The formalization captures the correct notion — a sink has no outgoing arrows (including to itself).

### Definition6_6_2 — Reversed Quiver at a Vertex ⚠️ NEEDS REWORK

```lean
noncomputable def Etingof.reversedAtVertex
    (V : Type*) [DecidableEq V] [Quiver V] (i : V) : Quiver V :=
  sorry
```

**Issues**:
1. **Return type is problematic**: Returns `Quiver V`, but `V` already has a `[Quiver V]` instance. In Lean 4, creating a new `Quiver` instance on the same type causes instance conflicts. The standard pattern would be to define a new type wrapper (e.g., `ReversedAt V i`) or use `@[local instance]`.
2. **Body is `sorry`**: Expected at scaffolding stage, but the definition body should be fillable. The logic is: for arrows between `a` and `b`, if exactly one of `{a, b}` equals `i`, reverse the arrow; otherwise keep it.

**Recommendation**: Define a type synonym `abbrev ReversedAtVertex (V : Type*) (i : V) := V` and put the new `Quiver` instance on that type. This avoids instance conflicts.

### Definition6_6_3 — Reflection Functor F⁺ᵢ ⚠️ NEEDS REDESIGN

```lean
noncomputable def Etingof.reflectionFunctorPlus
    (V : Type*) [Quiver V] [DecidableEq V] (i : V) :
    sorry := -- TODO: needs Rep Q and Rep Q̄ᵢ types
  sorry
```

**Issues**:
1. **Type is `sorry`**: This is not a valid scaffolding — the entire type signature is undefined. The `sorry` in the type position means Lean treats the output type as `False`-like, making this definitionally unsound.
2. **Missing infrastructure**: Needs quiver representation types. The correct signature would be a functor from `Rep k Q` to `Rep k Q̄ᵢ`, but this requires:
   - A formalization of quiver representations (as functors from path category to `ModuleCat k`)
   - The reversed quiver `Q̄ᵢ` from Definition 6.6.2
   - Direct sums and kernels in `ModuleCat k`

**Recommendation**: For Stage 3.1 scaffolding, the minimum viable signature would be:
```lean
-- Placeholder: state the type as a proposition about existence
-- until quiver representation infrastructure is built
noncomputable def Etingof.reflectionFunctorPlus
    (V : Type*) [Quiver V] [DecidableEq V] (i : V)
    (hi : Etingof.IsSink V i) :
    sorry := sorry  -- blocked on quiver rep infrastructure
```
Even this is not ideal. Consider leaving a structured `sorry` with a clear comment about what the actual type should be, or define it as a `structure` with fields corresponding to the functor's data.

### Definition6_6_4 — Reflection Functor F⁻ᵢ ⚠️ NEEDS REDESIGN

Same issues as Definition6_6_3. The `sorry := sorry` pattern with undefined type needs the same redesign.

---

## Partial-Match Definitions (7 items)

### Definition6_1_4 — Dynkin Diagram ⚠️ BODY SORRY, SIGNATURE OK

```lean
def Etingof.IsDynkinDiagram (n : ℕ) (adj : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  sorry
```

**Verdict**: Signature is reasonable — a predicate on adjacency matrices. The body needs to assert positive-definiteness of the associated quadratic form.

**Issue**: Should reference `Etingof.cartanMatrix` from Definition6_4_1 instead of needing to recompute `2·Id - adj` internally. Currently there's no import of Definition6_4_1.

**Suggestion**: Fill body as:
```lean
  ∀ x : Fin n → ℤ, x ≠ 0 → 0 < dotProduct x ((Etingof.cartanMatrix n adj).mulVec x)
```

### Definition6_4_1 — Cartan Matrix ✅ GOOD

```lean
def Etingof.cartanMatrix (n : ℕ) (adj : Matrix (Fin n) (Fin n) ℤ) :
    Matrix (Fin n) (Fin n) ℤ :=
  2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj
```

**Verdict**: Correct and complete. `2 • 1 - adj` correctly computes `2·Id - R`.

### Definition6_4_3 — Root ✅ GOOD (minor issue)

```lean
def Etingof.IsRoot (n : ℕ) (adj : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → ℤ) : Prop :=
  x ≠ 0 ∧ dotProduct x ((2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).mulVec x) = 2
```

**Verdict**: Mathematically correct. The condition `xᵀAx = 2` for `A = 2Id - R` is the right characterization.

**Minor issue**: Inlines the Cartan matrix formula instead of using `Etingof.cartanMatrix`. Should be:
```lean
  x ≠ 0 ∧ dotProduct x ((Etingof.cartanMatrix n adj).mulVec x) = 2
```

### Definition6_4_5 — Simple Roots ✅ GOOD

```lean
def Etingof.simpleRoot (n : ℕ) (i : Fin n) : Fin n → ℤ :=
  Pi.single i 1
```

**Verdict**: Perfect. `Pi.single i 1` is the idiomatic Mathlib way to express standard basis vectors.

### Definition6_4_7 — Positive and Negative Roots ✅ GOOD

```lean
def Etingof.IsPositiveRoot (n : ℕ) (adj : ...) (x : Fin n → ℤ) : Prop :=
  Etingof.IsRoot n adj x ∧ ∀ i, 0 ≤ x i

def Etingof.IsNegativeRoot (n : ℕ) (adj : ...) (x : Fin n → ℤ) : Prop :=
  Etingof.IsRoot n adj x ∧ ∀ i, x i ≤ 0
```

**Verdict**: Correct. Properly composes with `IsRoot` and uses the coordinate characterization from the book. This file correctly imports `Definition6_4_3`.

### Definition6_4_10 — Reflections ✅ GOOD

```lean
def Etingof.rootReflection (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ) (α : Fin n → ℤ)
    (v : Fin n → ℤ) : Fin n → ℤ :=
  v - (dotProduct v (A.mulVec α)) • α

def Etingof.simpleReflection (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) :
    (Fin n → ℤ) → (Fin n → ℤ) :=
  Etingof.rootReflection n A (Pi.single i 1)
```

**Verdict**: Correct. The formula `v - B(v,α)·α` matches the book exactly. The simple reflection correctly specializes to `α = αᵢ = Pi.single i 1`.

**Note**: Takes `A` as the full Cartan matrix, not the adjacency matrix. Callers must pass `cartanMatrix n adj`. This is a reasonable design choice — it decouples the reflection from the graph.

### Definition6_7_1 — Coxeter Element ✅ GOOD

```lean
noncomputable def Etingof.coxeterElement
    (n : ℕ) (W : Type*) [Group W] (s : Fin n → W) : W :=
  (List.ofFn s).prod
```

**Verdict**: Correct. The product of group elements indexed by `Fin n` via `List.ofFn` followed by `.prod` is clean and correct.

**Note**: Parameterized over an abstract group `W` rather than tying to a specific Weyl/Coxeter group. This is a reasonable generic definition but means the connection to simple reflections must be established at use sites.

---

## Theorem/Proposition/Lemma Files (14 items)

All 14 theorem-like files use the scaffolding pattern `(sorry : Prop) := sorry` for statements that require infrastructure not yet built, or proper typed statements with `sorry` proofs for statements that can be formalized now.

### Well-typed statements (2 files):

- **Lemma6_4_6**: Properly typed with `(∀ i, 0 ≤ x i) ∨ (∀ i, x i ≤ 0)`. References `Etingof.IsRoot`. Ready for proof work.
- **Example6_4_9_An**: Partially typed (has `(sorry : Prop)` but the right shape).

### Fully sorry'd statements (12 files):

These all use `(sorry : Prop) := sorry`, meaning neither the statement nor proof is formalized:
- Theorem_Dynkin_classification, Theorem6_5_2 (Gabriel's), Theorem6_8_1, Problem6_1_5_theorem
- Lemma6_4_2 (parts 1 and 2), Lemma6_7_2
- Proposition6_6_5 (parts 1 and 2), Proposition6_6_6 (parts 1 and 2), Proposition6_6_7, Proposition6_6_8 (parts 1 and 2)
- Corollary6_8_2, Corollary6_8_3, Corollary6_8_4
- Examples 6_2_2, 6_2_3, 6_2_4, 6_3_1, 6_8_5
- Problem6_9_1

**This is expected for Stage 3.1 scaffolding** — these require quiver representation infrastructure that doesn't exist yet.

---

## Cross-Cutting Issues

### 1. Cartan matrix inlining (Medium priority)

`Definition6_4_3` (IsRoot) inlines the Cartan matrix formula `2 • 1 - adj` instead of referencing `Etingof.cartanMatrix`. Similarly, `Definition6_1_4` (IsDynkinDiagram) will need to reference it but doesn't import it. This creates maintenance risk — if the Cartan matrix definition changes, these would be inconsistent.

**Recommendation**: Before Stage 3.2, refactor `IsRoot` to use `cartanMatrix`:
```lean
import EtingofRepresentationTheory.Chapter6.Definition6_4_1
-- ...
  x ≠ 0 ∧ dotProduct x ((Etingof.cartanMatrix n adj).mulVec x) = 2
```

### 2. Quiver representation infrastructure gap (High priority)

The biggest blocker for Stage 3.2 in Chapter 6 is the absence of a quiver representation type. Definitions 6.6.2-6.6.4 and Propositions 6.6.5-6.6.8 all need:
- A type for representations of a quiver (functor from path category to ModuleCat)
- Indecomposability predicate
- Direct sum of representations
- Morphisms between representations

This should be established as shared infrastructure before any proof work in Sections 6.6-6.8.

### 3. `sorry := sorry` pattern (Medium priority)

Definitions 6.6.3 and 6.6.4 use `sorry` as both the type and body (`sorry := sorry`). This compiles but is semantically worse than a properly-typed `sorry` — it provides no information about what the definition should look like. Before Stage 3.2, these should be upgraded to at least have a comment-documented type signature.

### 4. Import consistency

Most files import `Mathlib` directly. Two files use specific imports:
- `Definition6_4_7` imports `Definition6_4_3`
- `Lemma6_4_6` imports `Definition6_4_3`

This is the right pattern — specific imports are better than blanket `import Mathlib`. The remaining files should adopt specific imports as definitions are filled in.

---

## Summary

| Category | Count | Status |
|----------|-------|--------|
| Gap definitions — complete | 2 | ✅ Definition6_5_1, Definition6_6_1 |
| Gap definitions — sorry body only | 1 | ⚠️ Definition6_6_2 (needs type redesign) |
| Gap definitions — sorry type+body | 2 | ⚠️ Definition6_6_3, Definition6_6_4 (need infrastructure) |
| Partial definitions — complete | 5 | ✅ 6_4_1, 6_4_3, 6_4_5, 6_4_7, 6_4_10 |
| Partial definitions — sorry body | 1 | ⚠️ Definition6_1_4 (needs positive-definiteness) |
| Partial definitions — complete (generic) | 1 | ✅ Definition6_7_1 |
| Theorems/lemmas — properly typed | 1 | ✅ Lemma6_4_6 |
| Theorems/lemmas — fully sorry'd | 13+ | Expected for Stage 3.1 |

**Overall assessment**: The Section 6.4 definitions (Cartan matrix, roots, reflections) are **well-formalized** and ready for proof work. The Section 6.6 definitions (reversed quiver, reflection functors) are **blocked** on quiver representation infrastructure and need architectural rework before Stage 3.2. The Section 6.5 (dimension vector) and 6.6.1 (sink/source) definitions are clean.

## Recommendations for Stage 3.2

1. **Start proof work in Section 6.4** — Lemma 6.4.2 and Lemma 6.4.6 have the infrastructure they need and can be proved now.
2. **Build quiver representation infrastructure** — Create a shared module defining `QuiverRep k V` before attempting Section 6.6 proofs.
3. **Refactor Cartan matrix references** — Make `IsRoot` and `IsDynkinDiagram` use `cartanMatrix` instead of inlining.
4. **Redesign `reversedAtVertex`** — Use a type synonym to avoid instance conflicts.
5. **Upgrade reflection functor types** — At minimum, document the intended type signatures for F⁺ and F⁻.
