# Review: Ch5 Specht Module Chain (Definitions 5.12.1, Lemmas 5.13.1–5.13.4, Theorem 5.12.2)

Date: 2026-03-17
Reviewer: agent/bca06107

## Scope

Reviewed the Young symmetrizer / Specht module chain:
- `Definition5_12_1.lean` — Young symmetrizer definitions
- `Lemma5_13_1.lean` — absorption lemmas + main sandwich lemma
- `Lemma5_13_2.lean` — vanishing for distinct partitions
- `Lemma5_13_3.lean` — idempotent proportionality
- `Lemma5_13_4.lean` — Hom via idempotents
- `Theorem5_12_2.lean` — classification of irreps of S_n

## Deliverable 1: Definition 5.12.1 — Young Symmetrizer Definitions

### Validated ✓

**`rowOfPos` / `colOfPos`**: Correctly compute row and column indices for the canonical (left-to-right, top-to-bottom) filling of the Young diagram. Verified manually for partition (3,2) of 5:
- Positions 0,1,2 → row 0; positions 3,4 → row 1
- Position 0 → col 0, position 1 → col 1, position 2 → col 2, position 3 → col 0, position 4 → col 1

These are marked `private`, which is appropriate since downstream code only interacts through `RowSubgroup`/`ColumnSubgroup`.

**`Nat.Partition.sortedParts`**: Sorts the multiset of parts descending into a deterministic list. Correct.

**`StandardYoungTableau`**: Defined as a bijection from cells to `Fin n` that is row-increasing and column-increasing. Mathematically correct. Note: this type is not used by the downstream chain (the symmetrizer construction doesn't depend on a specific standard tableau choice).

**`RowSubgroup` / `ColumnSubgroup`**: Defined as permutations preserving row/column assignments under the canonical filling. Subgroup axioms (one_mem', mul_mem', inv_mem') are proved correctly. The key property P_λ ∩ Q_λ = {id} follows from the fact that the only permutation preserving both rows and columns in the canonical filling is the identity.

**`RowSymmetrizer`**: a_λ = Σ_{g ∈ P_λ} g in `MonoidAlgebra ℂ (Equiv.Perm (Fin n))`. Correct.

**`ColumnAntisymmetrizer`**: b_λ = Σ_{g ∈ Q_λ} sign(g) · g. The sign cast chain `ℤˣ → ℤ → ℂ` is correct. Each term is `sign(g) • of(g)`.

**`YoungSymmetrizer`**: c_λ = a_λ · b_λ. Correct — multiplication in `MonoidAlgebra` corresponds to convolution, so this is the right definition.

### Design choice: canonical vs tableau-parametrized

The code defines everything relative to the canonical filling (identity tableau). This is a valid mathematical choice: different standard tableaux of the same shape give conjugate symmetrizers, so the resulting Specht modules are isomorphic. The code avoids carrying a tableau parameter, which simplifies the API. No issues.

### Types and compatibility

The definitions are all over `MonoidAlgebra ℂ (Equiv.Perm (Fin n))` with partition parameter `la : Nat.Partition n`. Types are consistent across all files that import this module.

## Deliverable 2: Lemma 5.13.1 Helpers — Absorption Lemmas

### Validated ✓

All four absorption lemmas are sorry-free and mathematically correct:

1. **`RowSymmetrizer_mul_of_row`** (a_λ · of(p) = a_λ for p ∈ P_λ): Right multiplication by a subgroup element permutes the summands. Uses `Fintype.sum_equiv (Equiv.mulRight ⟨p, hp⟩)`. ✓

2. **`of_row_mul_RowSymmetrizer`** (of(p) · a_λ = a_λ for p ∈ P_λ): Left multiplication version. Uses `Equiv.mulLeft`. ✓

3. **`of_col_mul_ColumnAntisymmetrizer`** (of(q) · b_λ = sign(q) · b_λ for q ∈ Q_λ): Left absorption with sign. The key step uses sign(q)² = 1 to rearrange sign(q) · sign(q·g) = sign(g). ✓

4. **`ColumnAntisymmetrizer_mul_of_col`** (b_λ · of(q) = sign(q) · b_λ for q ∈ Q_λ): Right absorption with sign. Uses `linear_combination` for the sign rearrangement. ✓

**Orientation correctness**: Left vs right absorption is correct for both row and column subgroups. The row symmetrizer absorbs without sign change (because it sums all elements without signs). The column antisymmetrizer absorbs with sign (because sign(pq) = sign(p) · sign(q)).

### Helper lemmas for Lemma 5.13.1

5. **`sandwich_mem`** (sorry-free): For σ = p·q with p ∈ P_λ, q ∈ Q_λ, proves a_λ · of(σ) · b_λ = sign(q) · c_λ. Uses the absorption lemmas correctly. ✓

6. **`sandwich_not_mem`** (sorry-free): For σ ∉ P_λ · Q_λ, proves a_λ · of(σ) · b_λ = 0 via a sign-reversing involution argument. The proof:
   - Uses `pigeonhole_transposition` to find a transposition t ∈ P_λ with t' = σ⁻¹tσ ∈ Q_λ
   - Shows sign(t') = -1 (conjugation preserves sign)
   - Deduces y = -y, hence y = 0
   The logic is correct. ✓

7. **`pigeonhole_transposition`** (**sorry**): The combinatorial core — if σ ∉ P_λ · Q_λ, find a row transposition whose conjugate is a column transposition. This is the standard pigeonhole argument and is the only remaining sorry in the chain.

### Main Lemma 5.13.1

The main theorem constructs the linear functional ℓ via `Finsupp.lsum` and verifies by induction on `Finsupp.induction_linear`. The proof structure is clean and correct modulo the `pigeonhole_transposition` sorry. ✓

### Refactoring opportunity

The `hsqq` computation (sign(q)² = 1 in ℂ) is duplicated verbatim between `of_col_mul_ColumnAntisymmetrizer` (lines 58–64) and `ColumnAntisymmetrizer_mul_of_col` (lines 82–88). This should be extracted to a shared lemma, e.g.:

```lean
private lemma sign_sq_eq_one (q : Equiv.Perm (Fin n)) :
    ((↑(↑(Equiv.Perm.sign q) : ℤ) : ℂ)) * ((↑(↑(Equiv.Perm.sign q) : ℤ) : ℂ)) = 1
```

This is minor — the proofs work correctly as-is.

## Deliverable 3: Theorem 5.12.2 Statement

### Issues Found ✗

**CRITICAL: Both parts use `(sorry : Prop) := sorry` placeholders.** The statements are not formalized at all:

```lean
theorem Etingof.Theorem5_12_2_irreducible (n : ℕ) (la : Nat.Partition n) :
    (sorry : Prop) := by sorry

theorem Etingof.Theorem5_12_2_classification (n : ℕ) :
    (sorry : Prop) := by sorry
```

This means:
- The return type is `sorry : Prop`, which Lean treats as an axiom — it provides no specification
- The "4 sorries" are: 2 in the types + 2 in the proofs
- No agent can prove these until the types are replaced with real mathematical statements

**Recommended formalization for `Theorem5_12_2_irreducible`**:

The statement should express that V_λ = ℂ[S_n] · c_λ is an irreducible left module. This requires:
- Defining the Specht module as a `Submodule` or `Module` over `MonoidAlgebra ℂ (Equiv.Perm (Fin n))`
- Stating `IsSimpleModule` on that module

**Recommended formalization for `Theorem5_12_2_classification`**:
- For distinct partitions λ ≠ μ, V_λ ≇ V_μ (non-isomorphism)
- Every simple module over ℂ[S_n] is isomorphic to some V_λ

This statement formalization is a prerequisite for any proof work and should be prioritized.

## Additional Files Reviewed

### Lemma 5.13.2 (vanishing for distinct partitions)

**Status**: `(sorry : Prop) := sorry` with `hlt : sorry` hypothesis. Not formalized. The dominance/lexicographic order on partitions needs to be defined or imported. This is a harder formalization task because it requires relating the ordering to the pigeonhole combinatorics.

### Lemma 5.13.3 (idempotent proportionality)

**Status**: `(sorry : Prop) := sorry`. Not formalized. The statement requires expressing c_λ² = scalar · c_λ, which depends on Lemma 5.13.1 (to get c_λ² = a_λ · (b_λ · a_λ) · b_λ = ℓ(b_λ · a_λ) · c_λ).

### Lemma 5.13.4 (Hom via idempotents)

**Status**: Sorry-free ✓. Both statement and proof are complete. The equivalence `Hom_A(Ae, M) ≃ eM` is correctly formalized using `Submodule.span A ({e})` for the left ideal Ae. The proof constructs the forward map (evaluation at e) and inverse map (left multiplication), verifying both compositions. Clean and correct.

## Summary

| Item | Status | Notes |
|------|--------|-------|
| Definition 5.12.1 | ✓ Sorry-free | All definitions correct and well-typed |
| Lemma 5.13.1 helpers (4 absorption lemmas) | ✓ Sorry-free | Mathematically correct, minor sign duplication |
| Lemma 5.13.1 main | ⚠ 1 sorry | `pigeonhole_transposition` is the only gap |
| Lemma 5.13.2 | ✗ Not formalized | `(sorry : Prop)` placeholder |
| Lemma 5.13.3 | ✗ Not formalized | `(sorry : Prop)` placeholder |
| Lemma 5.13.4 | ✓ Sorry-free | Complete and correct |
| Theorem 5.12.2 | ✗ Not formalized | `(sorry : Prop)` placeholders in both parts |

## Recommendations

1. **Priority 1**: Formalize the statement of Theorem 5.12.2. This requires defining the Specht module V_λ as a concrete module and expressing irreducibility + classification. Without this, no proof work can begin.

2. **Priority 2**: Formalize Lemma 5.13.3 statement (c_λ² = scalar · c_λ). This can use Lemma 5.13.1 directly.

3. **Priority 3**: Prove `pigeonhole_transposition` (the last sorry in Lemma 5.13.1). This is a combinatorial argument about Young diagrams.

4. **Low priority**: Extract the duplicated `hsqq` sign computation into a shared lemma.
