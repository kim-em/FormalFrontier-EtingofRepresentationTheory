# Review: Chapter 5 Scaffolding Statement Quality Audit

**Issue:** #661
**Date:** 2026-03-17
**Scope:** 34 items in `scaffolded` status across Chapter 5

## Summary

| Classification | Count | Description |
|----------------|-------|-------------|
| Well-formed definition | 3 | Correct type signature, `sorry` body only |
| Well-formed theorem | 1 | Proper proposition, `sorry` proof only |
| Sorry placeholder | 28 | Statement is `(sorry : Prop)` — needs full formalization |
| Broken | 2 | `sorry` in hypothesis types AND statement |
| **Total** | **34** | |

**Key finding:** 88% of scaffolded Chapter 5 items (30/34) have no real Lean statement — the proposition itself is `sorry`. Only 4 items have well-formed type signatures ready for proof work. This means Chapter 5 requires extensive **statement formalization** before proof filling can proceed.

## Per-Item Classification

### Well-formed definitions (3) — ready for body implementation

| Item | Type | Assessment |
|------|------|------------|
| Definition5_12_1 | `def` | Defines StandardYoungTableau, RowSubgroup, ColumnSubgroup, YoungSymmetrizer with correct return types (`Type`, `Subgroup`, `MonoidAlgebra`). Sorry only in bodies. |
| Definition5_14_2 | `def` | Defines KostkaNumber as `ℕ := sorry`. Correct type, needs body. |
| Definition5_23_1 | `def` | Defines IsAlgebraicRepresentation as `Prop := sorry`. Correct type signature with proper parameters (field, n, module, representation map). |

### Well-formed theorem (1) — ready for proof work

| Item | Statement | Assessment |
|------|-----------|------------|
| Theorem5_4_3 | `IsSolvable G` | Burnside's theorem. Proper statement with Group, Fintype, prime hypotheses. Ready for proof. |

### Sorry placeholders (28) — need statement formalization

All use the pattern `(sorry : Prop) := by sorry` — the proposition is literally `sorry`.

#### Section 5.4: Burnside's theorem area (1 item)
- **Theorem5_4_3** is well-formed (see above), but no other 5.4.x items are scaffolded

#### Section 5.12–5.13: Symmetric group / Young tableaux (7 items)
| Item | Textbook content | Notes |
|------|-----------------|-------|
| Corollary5_12_4 | Irreps of S_n realized over ℚ | Depends on Specht module theory |
| Theorem5_12_2 | Specht modules V_λ = ℂ[S_n]·c_λ are irreducible & distinct | Central theorem for symmetric group reps |
| Lemma5_13_1 | a_λ·x·b_λ = ℓ_λ(x)·c_λ for linear functional ℓ_λ | Young projector scalar multiple |
| Lemma5_13_3 | c_λ² proportional to c_λ (quasi-idempotent) | Young symmetrizer property |
| Lemma5_13_4 | Hom_A(Ae, M) ≅ eM for idempotent e | General algebra fact; good parameters already |

#### Section 5.14–5.15: Kostka numbers / Cauchy identity (5 items)
| Item | Textbook content | Notes |
|------|-----------------|-------|
| Proposition5_14_1 | Hom(U_λ, V_μ) = 0 for μ < λ; dim Hom(U_λ, V_λ) = 1 | Two sub-theorems |
| Theorem5_14_3 | Character formula via power sums | Symmetric functions |
| Theorem5_15_1 | Frobenius character formula | Major result |
| Corollary5_15_4 | Cauchy identity for formal power series | |
| Lemma5_15_3 | Cauchy determinant identity | |

#### Section 5.17–5.19: Schur-Weyl duality (8 items)
| Item | Textbook content | Notes |
|------|-----------------|-------|
| Theorem5_17_1 | Hook length formula | Combinatorial formula for dim(V_λ) |
| Theorem5_18_1 | Double centralizer theorem (3 parts) | Major structural result |
| Theorem5_18_2 | Centralizer = universal enveloping algebra image | |
| Lemma5_18_3 | Symmetric power generation (2 parts) | |
| Theorem5_18_4 | Schur-Weyl duality (3 parts) | Central theorem |
| Proposition5_19_1 | GL(V) spans centralizer algebra | |
| Corollary5_19_2 | Schur-Weyl decomposition V⊗ⁿ ≅ ⊕ Vλ ⊗ Lλ | |
| Example5_19_3 | Schur functors for symmetric/exterior powers (2 parts) | |

#### Section 5.21–5.23: GL(V) representations (5 items)
| Item | Textbook content | Notes |
|------|-----------------|-------|
| Proposition5_21_1 | Character expansion in Schur polynomials | |
| Proposition5_21_2 | Schur polynomial properties (2 parts) | |
| Theorem5_22_1 | Weyl character formula | Major result |
| Proposition5_22_2 | Twisting by determinant | |
| Theorem5_23_2 | Complete reducibility + Peter-Weyl for GL(V) (2 parts) | |

#### Section 5.25–5.27: Finite group constructions (5 items)
| Item | Textbook content | Notes |
|------|-----------------|-------|
| Proposition5_25_1 | Commutator subgroup of GL₂(𝔽_q) | |
| Theorem5_25_2 | Principal series representations | |
| Lemma5_25_3 | Complementary series character properties | |
| Corollary5_26_3 | Irreducible characters as ℚ-linear combinations of induced | |
| Theorem5_26_1 | Artin's theorem | |
| Theorem5_27_1 | Representations of semidirect products | |

### Broken statements (2) — need hypothesis AND statement formalization

| Item | Issue | Assessment |
|------|-------|------------|
| Lemma5_13_2 | `(hlt : sorry)` in hypothesis | Needs dominance order on partitions formalized for the hypothesis, plus statement |
| Proposition5_14_1 (vanishing) | `(hlt : sorry)` in hypothesis | Same: needs dominance order for μ < λ hypothesis, plus statement |

Both require a formalization of the dominance order on `Nat.Partition` before they can be properly stated.

## Priority Recommendations

### Batch 1: Foundations (definitions + general algebra)
**Recommended first.** These have minimal external dependencies and unblock later work.

1. **Definition5_12_1** — Already well-formed. Fill in StandardYoungTableau, Row/ColumnSubgroup, YoungSymmetrizer bodies. This is the foundation for ALL section 5.12–5.15 work.
2. **Definition5_14_2** — Already well-formed. KostkaNumber body (cardinality of semistandard tableaux).
3. **Definition5_23_1** — Already well-formed. IsAlgebraicRepresentation body.
4. **Lemma5_13_4** — Formalize statement for Hom_A(Ae,M) ≅ eM. General algebra, independent of Young tableaux specifics.

### Batch 2: Burnside + early symmetric group
**High value: Burnside's theorem is a famous result.**

5. **Theorem5_4_3** — Already well-formed. Prove Burnside's theorem (IsSolvable G). Dependencies: Theorem5_4_6 (attention_needed) may be a blocker.
6. **Theorem5_12_2** — Formalize Specht module irreducibility statement. Central to section 5.12–5.15.
7. **Lemma5_13_1** — Formalize Young projector linear functional statement. Depends on Definition5_12_1.
8. **Lemma5_13_3** — Formalize Young symmetrizer quasi-idempotent statement. Depends on Definition5_12_1.

### Batch 3: Dominance order infrastructure
**Unblocks broken statements and Kostka theory.**

9. Define dominance order on `Nat.Partition` (needed for Lemma5_13_2 and Proposition5_14_1).
10. **Lemma5_13_2** — Fix broken hypothesis and formalize statement.
11. **Proposition5_14_1** — Fix broken hypothesis and formalize both sub-theorems.
12. **Theorem5_14_3** — Formalize character formula statement.

### Batch 4: Schur-Weyl duality cluster
**Complex but mathematically central. Tackle after Batches 1–3.**

13. **Theorem5_18_1** — Double centralizer theorem (3 parts).
14. **Theorem5_18_4** — Schur-Weyl duality (3 parts).
15. **Corollary5_19_2** — Schur-Weyl decomposition.

### Batch 5: Advanced topics (defer)
**These are deep results requiring significant infrastructure.**

- Theorem5_15_1 (Frobenius character formula)
- Theorem5_17_1 (Hook length formula)
- Theorem5_22_1 (Weyl character formula)
- Theorem5_23_2 (Complete reducibility for GL(V))
- Section 5.25–5.27 items (finite field constructions)

## Items to flag as `attention_needed`

None beyond the existing Theorem5_4_6. The broken statements (Lemma5_13_2, Proposition5_14_1) need work but are not "attention needed" — they just need the dominance order infrastructure built.

## Context: Chapter 5 vs other chapters

Chapter 5 has the most remaining scaffolded work of any chapter. For comparison:
- 22 items sorry_free (mostly sections 5.1–5.9)
- 34 items scaffolded (sections 5.12–5.27)
- 98 items not yet started
- 1 statement_formalized (Theorem5.1.5)
- 1 proof_formalized (Theorem5.4.4)
- 1 attention_needed (Theorem5.4.6)

The sorry-free items cluster in sections 5.1–5.9 (early, simpler results). Sections 5.12+ represent increasingly advanced material (symmetric group representations, Schur-Weyl duality, GL(V) theory) that requires substantial Mathlib infrastructure not yet available.
