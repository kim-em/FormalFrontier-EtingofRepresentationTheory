# Review: Chapter 3 Scaffolding — Theorem Statement Quality

**Issue:** #530
**Date:** 2026-03-16
**Scope:** 23 `.lean` files in `EtingofRepresentationTheory/Chapter3/`
(5 definitions, 7 theorems, 4 propositions, 3 lemmas, 2 corollaries, 2 examples)

## 1. Critical Finding: `True` Placeholder Abuse

**8 of 23 files use `True` as their theorem conclusion.** This violates the project's
explicit rule: "Never use `True` as a placeholder for propositions — it hides the actual
requirements and will need a full refactor to fix."

Affected files:
| File | What should be stated |
|------|----------------------|
| Theorem3_2_2 | Part (ii): surjectivity of ⊕ᵢ ρᵢ : A → ⊕ᵢ End(Vᵢ) |
| Theorem3_3_1 | Every irreducible rep of ⊕ᵢ Matₐᵢ(k) is isomorphic to k^{dᵢ} |
| Theorem3_5_4 | A/Rad(A) ≅ ⊕ᵢ End(Vᵢ), finitely many irreducibles |
| Theorem3_6_2 | Parts (i) and (ii): linear independence / basis of characters |
| Theorem3_8_1 | Unique decomposition into indecomposable summands |
| Theorem3_10_2 | Parts (i) and (ii): tensor products of irreducibles |
| Corollary3_5_5 | ∑ᵢ (dim Vᵢ)² ≤ dim A |
| Example3_5_6 | Both parts: concrete radical computations |

**Impact:** These files will all need refactoring before Stage 3.2 proof work can begin.
The `True` placeholder provides zero specification — a `sorry`'d proof of `True` compiles
but carries no mathematical content.

**Correct pattern (used in Ch2):**
```lean
-- Good: sorry'd proof of actual statement
def Etingof.PathAlgebra ... : Type* := sorry

-- Bad: sorry'd proof of True
theorem Etingof.density_theorem_part2 ... : True := by sorry
```

## 2. Missing `.refs.md` Files

7 of 23 items lack reference companion files:

- `Corollary3.2.1.refs.md`
- `Example3.1.2.refs.md`
- `Example3.5.6.refs.md`
- `Lemma3.8.2.refs.md`
- `Theorem3.7.1.refs.md`
- `Theorem3.8.1.refs.md`
- `Theorem3.10.2.refs.md`

These were likely missed during Stage 2.7 reference attachment. Without `.refs.md` files,
workers lack Mathlib API guidance when filling proofs.

## 3. Per-File Findings

### Definitions (5 files) — Overall: Good

| File | Match Type | Score | Notes |
|------|-----------|-------|-------|
| Definition3_1_1 | Exact | 5/5 | `IsSemisimpleModule` — clean alias |
| Definition3_3_2 | Exact | 4/5 | `Module.Dual` — uses `CommSemiring` instead of `Field` |
| Definition3_4_1 | Partial | 5/5 | `RelSeries` for filtrations — correct |
| Definition3_5_1 | Exact | 5/5 | `Ideal.jacobson ⊥` — perfect |
| Definition3_5_7 | Exact | 5/5 | `IsSemisimpleRing` — clean alias |

**Definition3_3_2 minor issue:** Uses `[CommSemiring k]` where `[Field k]` matches the
stated context. Not wrong, but overgeneral relative to the blob.

### Theorems (7 files) — Overall: Poor

| File | Has Real Statement | Score | Key Issue |
|------|-------------------|-------|-----------|
| Theorem3_2_2 | Part (i) yes, part (ii) `True` | 2/5 | Missing density theorem conclusion |
| Theorem3_3_1 | No — `True` | 1/5 | Entire statement is `True` |
| Theorem3_5_4 | No — `True` | 1/5 | Missing A/Rad(A) isomorphism |
| Theorem3_6_2 | No — both `True` | 1/5 | Missing character independence |
| Theorem3_7_1 | Partial | 3/5 | Only length equality, missing factor permutation |
| Theorem3_8_1 | No — `True` | 1/5 | Missing Krull-Schmidt uniqueness |
| Theorem3_10_2 | No — both `True` | 1/5 | Missing tensor product irreducibility |

**Theorem3_7_1** is the best of the theorems — it avoids `True` and states `s₁.length = s₂.length`,
but still misses the composition factor permutation and doesn't encode irreducibility of
successive quotients in the hypotheses.

### Propositions (4 files) — Overall: Mixed

| File | Score | Key Issue |
|------|-------|-----------|
| Proposition3_1_4 | 3/5 | Weakened: only states "sub of semisimple is semisimple", missing multiplicity structure |
| Proposition3_5_2 | 2/5 | Trivially proves `.carrier.Nonempty` instead of actual content (ideal property is definitional) |
| Proposition3_5_3 | 4/5 | Good: nilpotent ≤ radical and radical is nilpotent, both well-formalized |
| Proposition3_5_8 | 3/5 | Only captures (1)↔(5) of 5-way equivalence |

**Proposition3_5_2** is especially problematic: the theorem proves `(Ideal.jacobson ⊥).carrier.Nonempty`
(trivially: 0 is in every ideal). The blob says "Rad(A) is a two-sided ideal" — which is
already true by type in Mathlib. This should either be a doc-only file or formalize
a non-trivial consequence.

### Lemmas (3 files) — Overall: Good

| File | Score | Key Issue |
|------|-------|-----------|
| Lemma3_1_6 | 5/5 | Splitting property well-formalized with `Disjoint`/`⊔ = ⊤` |
| Lemma3_4_2 | 5/5 | Composition series existence via `CompositionSeries` |
| Lemma3_8_2 | 4/5 | Good: bijective ∨ nilpotent, missing `.refs.md` |

### Corollaries (2 files) — Mixed

| File | Score | Key Issue |
|------|-------|-----------|
| Corollary3_2_1 | 4/5 | Good interpolation property, missing `.refs.md` |
| Corollary3_5_5 | 1/5 | `True` placeholder — should state ∑ (dim Vᵢ)² ≤ dim A |

### Examples (2 files) — Mixed

| File | Score | Key Issue |
|------|-------|-----------|
| Example3_1_2 | 4/5 | Good: End(V) semisimple, missing `.refs.md` |
| Example3_5_6 | 1/5 | Both parts use `True` — should state concrete radicals |

## 4. Comparison with Chapter 2 Review

| Metric | Chapter 2 | Chapter 3 |
|--------|-----------|-----------|
| Total files | 25 | 23 |
| `True` placeholders | 0 | **8** |
| Missing `.refs.md` | 0 | **7** |
| Average score | ~4.3/5 | ~2.9/5 |
| Build passes | ✓ | ✓ |
| Doc-strings match blobs | ✓ | ✓ (mostly) |

**Chapter 2 had no `True` placeholders** — even gap definitions used `sorry` on actual
types/structures. Chapter 3 regressed significantly on this metric.

**Chapter 2 had complete `.refs.md` coverage.** Chapter 3 is missing 7 files (30%).

**Pattern divergence:** Chapter 2 definitions used `abbrev ... :=` consistently. Chapter 3
definitions follow this pattern, but theorems diverge from the project norm by using
`True` instead of `sorry`'d real statements.

## 5. Recommendations

### Blocking (must fix before Stage 3.2):

1. **Replace all 8 `True` placeholders** with actual mathematical statements (even
   if sorry'd). Each theorem conclusion should express the real type-level content.
   This is the highest-priority fix.

2. **Fix Proposition3_5_2** — either make it doc-only or formalize a non-trivial
   consequence (e.g., that `Ideal.jacobson ⊥` annihilates all simple modules).

### Non-blocking (should fix, but won't block proofs):

3. **Generate missing `.refs.md` files** for the 7 items lacking them. Re-run
   Stage 2.7 reference attachment for these items.

4. **Definition3_3_2:** Consider tightening `CommSemiring` to `Field` for
   consistency with the source text.

5. **Proposition3_5_8:** Consider expanding to capture all 5 equivalences,
   not just (1)↔(5).

6. **Theorem3_7_1:** Add composition factor permutation to the conclusion;
   encode irreducibility of successive quotients in the hypotheses.

## 6. Verification Checklist

- [x] All 23 Chapter 3 `.lean` files individually checked
- [x] Doc-strings compared against blob content
- [x] Mathlib imports verified against `.refs.md` (where available)
- [x] Type signatures assessed for formalization quality
- [x] Comparison with Chapter 2 patterns documented
- [x] No modifications to `PLAN.md` or `.claude/CLAUDE.md`
