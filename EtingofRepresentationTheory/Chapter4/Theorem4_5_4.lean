import Mathlib
import EtingofRepresentationTheory.Infrastructure.IrreducibleEnumeration
import EtingofRepresentationTheory.Infrastructure.RegularCharacter

/-!
# Theorem 4.5.4: Second Orthogonality Relation (Column Orthogonality)

For g, h ∈ G, the column orthogonality of characters states:
$$\sum_{V} \chi_V(g) \cdot \chi_V(h^{-1})
= \begin{cases} |Z_G(g)| & g \sim h \\ 0 & \text{otherwise}\end{cases}$$

where the sum runs over irreducible representations V.

## Proof strategy

The proof computes tr(T) where T(x) = gxh⁻¹ on k[G] in two ways:

1. **Basis computation**: tr(T) counts fixed points
   `{x : gxh⁻¹ = x}`, bijects with `Z_G(g)` when `g ~ h`.

2. **Decomposition via Wedderburn-Artin**: Using
   `k[G] ≅ ⊕ Mat_{d_i}(k)`, the trace decomposes as
   `∑_i tr(ρ_i(g)) · tr(ρ_i(h⁻¹)) = ∑_i χ_i(g) · χ_i(h⁻¹)`.

Both computations are connected via `D.iso` and
`AlgEquiv.linearEquivConj_mulLeftRight` (trace is invariant under
algebra isomorphism).

## Mathlib correspondence

Column (second) orthogonality, not in Mathlib as of v4.28.
Row (first) orthogonality is `FDRep.char_orthonormal`.
-/

open CategoryTheory

universe u

variable {G : Type u} [Group G] [Fintype G]

/-! ### Group-theoretic lemmas on conjugation fixed points -/

section ConjugatorCounting

/-- Equivalence between `Z_G(g)` and `{x | x * g * x⁻¹ = h}` via
left multiplication by a conjugator `c` with `c * g * c⁻¹ = h`. -/
noncomputable def conjugatorEquiv (g h c : G)
    (hc : c * g * c⁻¹ = h) :
    ↥(Subgroup.centralizer ({g} : Set G)) ≃
      {x : G // x * g * x⁻¹ = h} where
  toFun z := ⟨c * z.1, by
    have hz := z.2
    rw [Subgroup.mem_centralizer_iff] at hz
    have hzg : z.1 * g * z.1⁻¹ = g := by
      have := (hz g (Set.mem_singleton g)).symm
      rw [mul_inv_eq_iff_eq_mul, this]
    calc c * z.1 * g * (c * z.1)⁻¹
        = c * (z.1 * g * z.1⁻¹) * c⁻¹ := by group
      _ = c * g * c⁻¹ := by rw [hzg]
      _ = h := hc⟩
  invFun x := ⟨c⁻¹ * x.1, by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    have hx := x.2
    have key : (c⁻¹ * x.1) * g * (c⁻¹ * x.1)⁻¹ = g := by
      calc _ = c⁻¹ * (x.1 * g * x.1⁻¹) * c := by group
        _ = c⁻¹ * h * c := by rw [hx]
        _ = c⁻¹ * (c * g * c⁻¹) * c := by rw [hc]
        _ = g := by group
    calc g * (c⁻¹ * x.1)
        = (c⁻¹ * x.1) * g * (c⁻¹ * x.1)⁻¹ * (c⁻¹ * x.1) := by
          rw [key]
      _ = (c⁻¹ * x.1) * g := by group⟩
  left_inv z := by ext; simp
  right_inv x := by ext; simp

open scoped Classical in
/-- The set `{x : G | x * g * x⁻¹ = h}` is empty when `g` and `h`
are not conjugate. -/
theorem conjugators_empty_of_not_isConj (g h : G)
    (hnh : ¬IsConj g h) :
    Finset.filter (fun x => x * g * x⁻¹ = h)
      Finset.univ = ∅ := by
  rw [Finset.filter_eq_empty_iff]
  intro x _ heq
  exact hnh (isConj_iff.mpr ⟨x, heq⟩)

open scoped Classical in
/-- When `g ~ h`, `|{x : G | x * g * x⁻¹ = h}| = |Z_G(g)|`. -/
theorem card_conjugators_eq_of_isConj (g h : G)
    (hgh : IsConj g h) :
    (Finset.filter (fun x => x * g * x⁻¹ = h)
      Finset.univ).card =
      Fintype.card
        ↥(Subgroup.centralizer ({g} : Set G)) := by
  obtain ⟨c, hc⟩ := isConj_iff.mp hgh
  rw [← Fintype.card_subtype]
  exact Fintype.card_congr
    (conjugatorEquiv g h c hc).symm

open scoped Classical in
/-- `|{x ∈ G | x * g * x⁻¹ = h}| = |Z_G(g)|` if `g ~ h`, else `0`.
-/
theorem card_conjugators (g h : G) :
    (Finset.filter (fun x => x * g * x⁻¹ = h)
      Finset.univ).card =
      if IsConj g h
        then Fintype.card
          ↥(Subgroup.centralizer ({g} : Set G))
        else 0 := by
  split
  · exact card_conjugators_eq_of_isConj g h ‹_›
  · simp [conjugators_empty_of_not_isConj g h ‹_›]

open Classical in
/-- The fixed point set `{x : gxh⁻¹ = x}` has the same cardinality as
the conjugator set `{y : ygy⁻¹ = h}`, via the bijection `x ↦ x⁻¹`.

`gxh⁻¹ = x ↔ x⁻¹gx = h ↔ x⁻¹g(x⁻¹)⁻¹ = h`, so `x⁻¹` lies in the
conjugator set. -/
theorem card_fixedPoints_eq_card_conjugators (g h : G) :
    (Finset.filter (fun x : G => g * x * h⁻¹ = x) Finset.univ).card =
    (Finset.filter (fun x : G => x * g * x⁻¹ = h) Finset.univ).card := by
  classical
  rw [show (Finset.filter (fun x : G => g * x * h⁻¹ = x) Finset.univ) =
    (Finset.filter (fun x : G => x * g * x⁻¹ = h) Finset.univ).map
      ⟨fun x => x⁻¹, inv_injective⟩ from ?_]
  · rw [Finset.card_map]
  · ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Function.Embedding.coeFn_mk]
    constructor
    · intro hx
      -- hx : g * x * h⁻¹ = x
      -- Need: ∃ a, a * g * a⁻¹ = h ∧ a⁻¹ = x
      refine ⟨x⁻¹, ?_, inv_inv x⟩
      rw [inv_inv]
      have h1 : g * x = x * h := by
        calc g * x = g * x * h⁻¹ * h := by group
          _ = x * h := by rw [hx]; group
      calc x⁻¹ * g * x = x⁻¹ * (x * h) := by rw [mul_assoc, h1]
        _ = h := by rw [← mul_assoc, inv_mul_cancel, one_mul]
    · intro ⟨a, ha, hax⟩
      -- ha : a * g * a⁻¹ = h, hax : a⁻¹ = x
      rw [← hax]
      -- Goal: g * a⁻¹ * h⁻¹ = a⁻¹
      rw [← ha]
      group

end ConjugatorCounting

/-! ### Trace of two-sided multiplication on the group algebra -/

variable {k : Type u} [Field k] [IsAlgClosed k]

section ColumnOrthogonality

open Classical

variable [NeZero (Nat.card G : k)]

/-- The character of `D.columnFDRep i` at `g` equals the matrix trace of the
i-th Wedderburn-Artin block evaluated at `MonoidAlgebra.of k G g`.

Follows because `columnRep i g = mulVecLin(M)` where `M = D.iso(of g)_i`,
and `trace(mulVecLin M) = Matrix.trace M` (via `Matrix.trace_toLin'_eq`). -/
lemma IrrepDecomp.columnFDRep_character
    (D : IrrepDecomp k G) (i : Fin D.n) (g : G) :
    (D.columnFDRep i).character g =
      Matrix.trace (D.iso (MonoidAlgebra.of k G g) i) := by
  show LinearMap.trace k _ (Matrix.mulVecLin (D.projRingHom i (MonoidAlgebra.of k G g))) = _
  rw [← Matrix.toLin'_apply']
  rw [Matrix.trace_toLin'_eq]
  rfl

/-- The trace of `x ↦ a * x * b` on `MonoidAlgebra k G`, transported via
the Wedderburn-Artin isomorphism, equals the sum of products of matrix
traces on each block.

**Key ideas:**
- `LinearMap.trace_conj'` + `AlgEquiv.linearEquivConj_mulLeftRight`:
  trace is invariant under algebra isomorphism
- `mulLeftRight` on a pi ring acts componentwise
- Trace of `A ↦ M * A * N` on `Mat_n(k)` equals `tr(M) * tr(N)`
  (from `LinearMap.trace_tensorProduct'` via `Mat_n ≅ k^n ⊗ (k^n)*`) -/
lemma trace_mulLeftRight_eq_sum_matrix_traces
    (D : IrrepDecomp k G) (a b : MonoidAlgebra k G) :
    LinearMap.trace k (MonoidAlgebra k G)
      (LinearMap.mulLeftRight k (a, b)) =
    ∑ i : Fin D.n,
      Matrix.trace (D.iso a i) * Matrix.trace (D.iso b i) := by
  sorry

/-- The trace of `x ↦ g * x * h⁻¹` on `MonoidAlgebra k G` equals the
conjugator count: `|Z_G(g)|` if `g ~ h`, else `0`.

Computed on the standard Finsupp basis: the diagonal entry at `x` is
`δ(g*x*h⁻¹, x)`, and the sum counts the fixed point set `{x : g*x*h⁻¹ = x}`,
which bijects with the conjugator set `{y : y*g*y⁻¹ = h}` via `y = x⁻¹`. -/
theorem trace_mulLeftRight_monoidAlgebra (g h : G) :
    LinearMap.trace k (MonoidAlgebra k G)
      (LinearMap.mulLeftRight k
        (MonoidAlgebra.of k G g, MonoidAlgebra.of k G h⁻¹)) =
      if IsConj g h
        then (Fintype.card ↥(Subgroup.centralizer ({g} : Set G)) : k)
        else 0 := by
  let b := MonoidAlgebra.basis G k
  rw [LinearMap.trace_eq_matrix_trace k b]
  simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply,
    LinearMap.mulLeftRight_apply, MonoidAlgebra.of_apply]
  conv_lhs =>
    arg 2; ext x
    rw [show b x = MonoidAlgebra.single x 1 from by simp [b, MonoidAlgebra.basis]; rfl]
    rw [MonoidAlgebra.single_mul_single, MonoidAlgebra.single_mul_single, one_mul, mul_one]
    rw [show b.repr (MonoidAlgebra.single (g * x * h⁻¹) 1) x =
        if g * x * h⁻¹ = x then 1 else 0 from by
      show (LinearEquiv.refl k (G →₀ k) (Finsupp.single (g * x * h⁻¹) 1)) x = _
      simp [Finsupp.single_apply]]
  trans ↑(∑ x : G, if g * x * h⁻¹ = x then (1 : ℕ) else 0)
  · push_cast; rfl
  rw [Finset.sum_boole (fun x => g * x * h⁻¹ = x) Finset.univ,
    card_fixedPoints_eq_card_conjugators g h, card_conjugators g h]
  split <;> simp

/-- Column orthogonality for the canonical Wedderburn column representations:
`∑_i χ_{col_i}(g) · χ_{col_i}(h⁻¹) = |Z_G(g)| if g ~ h, else 0`.

Combines `columnFDRep_character` and `trace_mulLeftRight_eq_sum_matrix_traces`
with `trace_mulLeftRight_monoidAlgebra`. -/
theorem column_orthogonality_wedderburn
    (D : IrrepDecomp k G) (g h : G) :
    ∑ i : Fin D.n,
      (D.columnFDRep i).character g * (D.columnFDRep i).character h⁻¹ =
      if IsConj g h
        then (Fintype.card ↥(Subgroup.centralizer ({g} : Set G)) : k)
        else 0 := by
  simp_rw [D.columnFDRep_character]
  have key := trace_mulLeftRight_eq_sum_matrix_traces D
    (MonoidAlgebra.of k G g) (MonoidAlgebra.of k G h⁻¹)
  rw [← key]
  exact trace_mulLeftRight_monoidAlgebra g h

/-- Any two complete systems of non-isomorphic irreducible representations
indexed by `Fin n` give the same sum of products of characters. -/
theorem sum_character_prod_eq_of_complete
    {n : ℕ} (V W : Fin n → FDRep k G)
    (hV : ∀ i, Simple (V i))
    (hVinj : ∀ i j, Nonempty ((V i) ≅ (V j)) → i = j)
    (hVsurj : ∀ (U : FDRep k G), Simple U → ∃ i, Nonempty (U ≅ V i))
    (hW : ∀ i, Simple (W i))
    (hWinj : ∀ i j, Nonempty ((W i) ≅ (W j)) → i = j)
    (hWsurj : ∀ (U : FDRep k G), Simple U → ∃ i, Nonempty (U ≅ W i))
    (g h : G) :
    ∑ i, (V i).character g * (V i).character h =
    ∑ i, (W i).character g * (W i).character h := by
  sorry

/-- `D.columnFDRep` forms a complete system of non-isomorphic irreducible
representations. -/
theorem IrrepDecomp.columnFDRep_is_complete
    (D : IrrepDecomp k G) :
    (∀ i, Simple (D.columnFDRep i)) ∧
    (∀ i j, Nonempty ((D.columnFDRep i) ≅ (D.columnFDRep j)) → i = j) ∧
    (∀ (W : FDRep k G), Simple W → ∃ i, Nonempty (W ≅ D.columnFDRep i)) := by
  sorry

end ColumnOrthogonality

/-! ### Main theorem -/

open scoped Classical in
/-- **Column orthogonality of characters** (Etingof Theorem 4.5.4).

For `g, h ∈ G`, `∑_V χ_V(g) · χ_V(h⁻¹)` over irreducible
representations equals `|Z_G(g)|` when `g ~ h`, else `0`.

The proof proceeds in three steps:
1. **Basis computation**: `tr(x ↦ gxh⁻¹)` on `k[G]` counts fixed
   points, giving the conjugator count (`trace_mulLeftRight_monoidAlgebra`).
2. **Wedderburn computation**: The same trace, computed via the
   Wedderburn-Artin isomorphism, gives `∑_i χ_i(g) · χ_i(h⁻¹)` for
   the column representations (`column_orthogonality_wedderburn`).
3. **Transfer**: Any complete system of irreducibles gives the same
   character sum (`sum_character_prod_eq_of_complete`). -/
theorem Etingof.Theorem4_5_4
    [NeZero (Nat.card G : k)]
    (D : IrrepDecomp k G) (V : Fin D.n → FDRep k G)
    (hV : ∀ i, Simple (V i))
    (hinj : ∀ i j, Nonempty ((V i) ≅ (V j)) → i = j)
    (hsurj : ∀ (W : FDRep k G), Simple W →
      ∃ i, Nonempty (W ≅ V i))
    (g h : G) :
    ∑ i : Fin D.n,
      (V i).character g * (V i).character h⁻¹ =
      if IsConj g h
        then (Fintype.card
          ↥(Subgroup.centralizer ({g} : Set G)) : k)
        else 0 := by
  classical
  obtain ⟨hcS, hcI, hcSurj⟩ := D.columnFDRep_is_complete
  rw [sum_character_prod_eq_of_complete V D.columnFDRep
    hV hinj hsurj hcS hcI hcSurj g h⁻¹]
  exact column_orthogonality_wedderburn D g h
