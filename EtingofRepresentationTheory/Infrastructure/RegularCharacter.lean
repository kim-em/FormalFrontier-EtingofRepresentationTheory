import Mathlib
import EtingofRepresentationTheory.Infrastructure.IrreducibleEnumeration

/-!
# Regular Representation Character Identity

For a finite group G over ℂ (or any algebraically closed field of good characteristic),
the character of the regular representation satisfies:

* `χ_reg(1) = |G|`
* `χ_reg(g) = 0` for `g ≠ 1`

These are computed as traces of the left-multiplication action on `G →₀ k`.

## References

- Etingof, *Introduction to Representation Theory*, Section 4.4
-/

open Representation CategoryTheory

universe u

variable {k G : Type u} [Field k] [Group G]

/-! ### Character of the regular representation -/

/-- The character of the regular representation at the identity is `|G|`. -/
theorem regularCharacter_one [Fintype G] :
    LinearMap.trace k (G →₀ k) ((Representation.ofMulAction k G G) 1) =
      (Fintype.card G : k) := by
  rw [map_one, LinearMap.trace_one]
  simp

/-- The character of the regular representation at `g ≠ 1` is `0`. -/
theorem regularCharacter_ne_one [Finite G] (g : G) (hg : g ≠ 1) :
    LinearMap.trace k (G →₀ k) ((Representation.ofMulAction k G G) g) = 0 := by
  classical
  cases nonempty_fintype G
  have key : ∀ h : G, ofMulAction k G G g (Finsupp.single h 1) h = 0 := by
    intro h
    rw [ofMulAction_apply, Finsupp.single_apply, if_neg]
    intro heq
    rw [smul_eq_mul] at heq
    -- heq : h = g⁻¹ * h, need g = 1
    exact hg (inv_eq_one.mp (mul_right_cancel (show g⁻¹ * h = 1 * h by rw [one_mul, ← heq])))
  rw [LinearMap.trace_eq_matrix_trace k (Finsupp.basisSingleOne (ι := G) (R := k))]
  simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply]
  apply Finset.sum_eq_zero
  intro h _
  convert key h using 1

open scoped Classical in
/-- Combined form: `χ_reg(g)` equals `|G|` if `g = 1` and `0` otherwise. -/
theorem regularCharacter_eq [Fintype G] (g : G) :
    LinearMap.trace k (G →₀ k) ((Representation.ofMulAction k G G) g) =
      if g = 1 then (Fintype.card G : k) else 0 := by
  split
  · subst_vars; exact regularCharacter_one
  · exact regularCharacter_ne_one g ‹_›

/-! ### Sum-of-dimensions character identity

For `g ≠ 1`, the decomposition of the regular representation into irreducibles gives:
`∑_i dim(V_i) · χ_{V_i}(g) = 0`

The proof strategy:
1. The regular representation `ofMulAction g` equals left multiplication by `of g`
2. Under the Wedderburn isomorphism, trace decomposes as `∑_i d_i * Matrix.trace(m_i)`
3. Each `Matrix.trace(m_i)` equals the character of the i-th column representation
4. A bijection argument relates arbitrary enumeration `V` to `columnFDRep`
-/

/-! #### Helper lemmas for the trace decomposition -/

private lemma stdBasis_repr_apply' [IsAlgClosed k] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) k) (ij : Fin n × Fin n) :
    (Matrix.stdBasis k (Fin n) (Fin n)).repr A ij = A ij.1 ij.2 := by
  simp [Matrix.stdBasis]

/-- The regular representation at `g` equals left multiplication by `of g` on `k[G]`. -/
private lemma ofMulAction_eq_mulLeft (g : G) :
    (Representation.ofMulAction k G G g : (G →₀ k) →ₗ[k] (G →₀ k)) =
      LinearMap.mulLeft k (MonoidAlgebra.of k G g) := by
  apply Finsupp.lhom_ext'
  intro h
  ext c
  simp only [ofMulAction_single, LinearMap.mulLeft_apply, MonoidAlgebra.of_apply,
    LinearMap.comp_apply, Finsupp.lsingle_apply, smul_eq_mul]
  congr 1
  rw [MonoidAlgebra.single_mul_single, one_mul]

/-- Trace of left multiplication is preserved by algebra isomorphisms. -/
private lemma trace_mulLeft_algEquiv [IsAlgClosed k]
    {A B : Type u} [Ring A] [Ring B] [Algebra k A] [Algebra k B]
    [Module.Free k A] [Module.Finite k A] [Module.Free k B] [Module.Finite k B]
    (φ : A ≃ₐ[k] B) (a : A) :
    LinearMap.trace k A (LinearMap.mulLeft k a) =
      LinearMap.trace k B (LinearMap.mulLeft k (φ a)) := by
  have h : φ.toLinearEquiv.conj (LinearMap.mulLeft k a) = LinearMap.mulLeft k (φ a) := by
    ext x; simp [LinearEquiv.conj_apply, LinearMap.mulLeft_apply, map_mul]
  rw [← h]; exact (LinearMap.trace_conj' (LinearMap.mulLeft k a) φ.toLinearEquiv).symm

/-- Trace of left multiplication on a matrix algebra equals `n * Matrix.trace M`. -/
private lemma trace_mulLeft_matrix [IsAlgClosed k] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) k) :
    LinearMap.trace k (Matrix (Fin n) (Fin n) k) (LinearMap.mulLeft k M) =
      (n : k) * Matrix.trace M := by
  rw [LinearMap.trace_eq_matrix_trace k (Matrix.stdBasis k (Fin n) (Fin n))]
  simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply,
    LinearMap.mulLeft_apply, stdBasis_repr_apply']
  have key : ∀ x : Fin n × Fin n,
      (M * (Matrix.stdBasis k (Fin n) (Fin n)) x) x.1 x.2 = M x.1 x.1 := by
    intro ⟨a, b⟩; rw [Matrix.stdBasis_eq_single, Matrix.mul_single_apply_same, mul_one]
  simp_rw [key]
  rw [show ∑ x : Fin n × Fin n, M x.1 x.1 = ∑ a : Fin n, ∑ _ : Fin n, M a a from by
    rw [← Finset.sum_product']; rfl]
  simp [Finset.sum_const, Finset.mul_sum]

/-- Trace of componentwise left multiplication on a product of matrix algebras
decomposes as the sum of block traces: `∑_i d_i * Matrix.trace(m_i)`. -/
private lemma trace_mulLeft_pi [IsAlgClosed k] {N : ℕ} {d : Fin N → ℕ}
    (a : ∀ i : Fin N, Matrix (Fin (d i)) (Fin (d i)) k) :
    LinearMap.trace k _ (LinearMap.mulLeft k a) =
      ∑ i, (d i : k) * Matrix.trace (a i) := by
  let B := Pi.basis (fun i => Matrix.stdBasis k (Fin (d i)) (Fin (d i)))
  rw [LinearMap.trace_eq_matrix_trace k B]
  simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply,
    LinearMap.mulLeft_apply]
  have key : ∀ x : Σ i, Fin (d i) × Fin (d i),
      B.repr (a * B x) x = a x.1 x.2.1 x.2.1 := by
    intro ⟨i, a', b'⟩
    rw [Pi.basis_repr, stdBasis_repr_apply', Pi.basis_apply]
    simp [Pi.mul_apply, Matrix.stdBasis_eq_single,
      Matrix.mul_single_apply_same, mul_one]
  simp_rw [key]
  simp only [Fintype.sum_sigma]
  congr 1; ext i
  rw [show ∑ x : Fin (d i) × Fin (d i), a i x.1 x.1 =
    ∑ a' : Fin (d i), ∑ _ : Fin (d i), a i a' a' from by
    rw [← Finset.sum_product']; rfl]
  simp [Finset.sum_const, Finset.mul_sum]

/-- Character of column FDRep equals the matrix trace of the projection. -/
private lemma columnFDRep_character_eq [Fintype G] [IsAlgClosed k] [NeZero (Nat.card G : k)]
    (D : IrrepDecomp k G) (i : Fin D.n) (g : G) :
    (D.columnFDRep i).character g =
      Matrix.trace (D.projRingHom i (MonoidAlgebra.of k G g)) := by
  show LinearMap.trace k (Fin (D.d i) → k) (Matrix.mulVecLin _) = _
  rw [← Matrix.toLin'_apply']; exact Matrix.trace_toLin'_eq _

/-! #### Main theorem -/

/-- For `g ≠ 1`, the sum `∑_i dim(V_i) · χ_{V_i}(g) = 0` over all irreducible
representations. This follows from the decomposition of the regular representation
into irreducibles combined with `regularCharacter_ne_one`. -/
theorem sum_dim_character_eq_zero [Fintype G] [IsAlgClosed k] [NeZero (Nat.card G : k)]
    (D : IrrepDecomp k G) (V : Fin D.n → FDRep k G)
    (hV : ∀ i, Simple (V i))
    (hinj : ∀ i j, Nonempty ((V i) ≅ (V j)) → i = j)
    (g : G) (hg : g ≠ 1) :
    ∑ i, (Module.finrank k (V i) : k) * (V i).character g = 0 := by
  -- For each j, find τ j with V j ≅ columnFDRep (τ j)
  choose τ hτ using fun j => D.columnFDRep_surjective (V j) (hV j)
  have hτ_inj : Function.Injective τ := by
    intro j₁ j₂ h
    exact hinj j₁ j₂ ⟨(hτ j₁).some ≪≫ (h ▸ (hτ j₂).some.symm)⟩
  have hτ_bij : Function.Bijective τ := Finite.injective_iff_bijective.mp hτ_inj
  -- ∑_i d_i * (columnFDRep i).character g = 0 via trace decomposition
  have h_col : ∑ i, (D.d i : k) * (D.columnFDRep i).character g = 0 := by
    simp_rw [columnFDRep_character_eq D _ g]
    have h1 : LinearMap.trace k (MonoidAlgebra k G) (LinearMap.mulLeft k (MonoidAlgebra.of k G g)) = 0 := by
      have := regularCharacter_ne_one (k := k) g hg
      rwa [ofMulAction_eq_mulLeft] at this
    rw [trace_mulLeft_algEquiv D.iso, trace_mulLeft_pi] at h1
    exact h1
  -- finrank(V j) = D.d(τ j) and char(V j) = char(columnFDRep(τ j))
  have hfr : ∀ j, Module.finrank k (V j) = D.d (τ j) := by
    intro j; rw [← D.finrank_columnFDRep (τ j)]
    exact LinearEquiv.finrank_eq (FDRep.isoToLinearEquiv (hτ j).some)
  have hchar : ∀ j, (V j).character g = (D.columnFDRep (τ j)).character g := by
    intro j; exact congr_fun (FDRep.char_iso (hτ j).some) g
  -- Rewrite and reindex by τ
  conv_lhs => arg 2; ext j; rw [hfr j, hchar j]
  let τ_equiv := Equiv.ofBijective τ hτ_bij
  rw [show ∑ j, (D.d (τ j) : k) * (D.columnFDRep (τ j)).character g =
    ∑ i, (D.d i : k) * (D.columnFDRep i).character g from
    Finset.sum_equiv τ_equiv (fun _ => by simp) (fun _ _ => rfl)]
  exact h_col

/-! ### Dimension nonzero in k

In a Wedderburn decomposition `k[G] ≅ ∏ Mat(d_i, k)`, each block dimension `d_i`
is nonzero when cast to `k` (assuming `char(k) ∤ |G|`). This follows from the
nondegeneracy of the identity-coefficient functional on `k[G]`.
-/

/-- The "regular trace" of `γ ∈ k[G]` — the trace of left multiplication by `γ` —
equals `|G| * γ(1)`, where `γ(1)` is the coefficient of the identity element. -/
private theorem regTrace_eq_card_mul [Fintype G]
    (γ : MonoidAlgebra k G) :
    LinearMap.trace k (MonoidAlgebra k G) (LinearMap.mulLeft k γ) =
      (Fintype.card G : k) * γ 1 := by
  classical
  -- Both sides are linear in γ; suffices to check on basis {single g 1}.
  -- Use the existing regularCharacter_eq which computes trace of ofMulAction.
  -- Both sides are linear in γ. Define the two linear maps and show they agree on basis.
  -- LHS: γ ↦ trace(mulLeft γ), which is (trace ∘ₗ lmul).toLinearMap
  -- RHS: γ ↦ |G| * γ(1) = |G| • lapply 1
  suffices h_eq :
      (LinearMap.trace k (MonoidAlgebra k G)).comp
        (Algebra.lmul k (MonoidAlgebra k G)).toLinearMap =
      (Fintype.card G : k) • (Finsupp.lapply (1 : G) : MonoidAlgebra k G →ₗ[k] k) by
    exact LinearMap.ext_iff.mp h_eq γ
  apply (Finsupp.basisSingleOne (ι := G) (R := k)).ext
  intro g
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    LinearMap.smul_apply, smul_eq_mul, Finsupp.lapply_apply]
  -- LHS: trace(lmul(single g 1)) = trace(mulLeft(single g 1))
  change LinearMap.trace k (MonoidAlgebra k G) (LinearMap.mulLeft k _) = _
  have := regularCharacter_eq (k := k) g
  rw [ofMulAction_eq_mulLeft] at this
  simp only [Finsupp.coe_basisSingleOne, Finsupp.single_apply]
  convert this using 1
  split_ifs <;> ring

/-- In a Wedderburn decomposition of `k[G]`, each block dimension `d_i` is nonzero in `k`.
This is proved via the nondegeneracy of the coefficient-at-identity form on `k[G]`:
if `d_i = 0` in `k`, the central idempotent for block `i` would be annihilated by
all elements under this form, contradicting its nonzero-ness. -/
theorem IrrepDecomp.d_cast_ne_zero [Fintype G] [IsAlgClosed k]
    [Invertible (Fintype.card G : k)] [NeZero (Nat.card G : k)]
    (D : IrrepDecomp k G) (i : Fin D.n) :
    (D.d i : k) ≠ 0 := by
  classical
  intro hd_zero
  -- Central idempotent for block i
  set e : MonoidAlgebra k G := D.iso.symm (Pi.single i 1) with he_def
  -- e ≠ 0
  have he_ne : e ≠ 0 := by
    intro h
    have h1 : Pi.single i (1 : Matrix (Fin (D.d i)) (Fin (D.d i)) k) = 0 :=
      D.iso.symm.injective (h.trans (map_zero _).symm)
    haveI := D.d_pos i
    haveI : Nonempty (Fin (D.d i)) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne _)⟩⟩
    exact one_ne_zero ((Pi.single_eq_same i 1).symm.trans (congr_fun h1 i))
  -- For any β, compute regTrace(e * β) two ways to show (e * β)(1) = 0.
  have he_ann : ∀ β : MonoidAlgebra k G, (e * β) 1 = 0 := by
    intro β
    -- Way 1: via Wedderburn decomposition
    have hiso : D.iso (e * β) = Pi.single i (D.projRingHom i β) := by
      show D.iso (D.iso.symm (Pi.single i 1) * β) = _
      rw [map_mul, AlgEquiv.apply_symm_apply]
      funext j
      simp only [Pi.mul_apply]
      by_cases hj : j = i
      · subst hj
        rw [Pi.single_eq_same, Pi.single_eq_same, one_mul]
        rfl
      · rw [Pi.single_eq_of_ne hj, Pi.single_eq_of_ne hj, zero_mul]
    have hrt_wd : LinearMap.trace k (MonoidAlgebra k G) (LinearMap.mulLeft k (e * β)) =
        (D.d i : k) * Matrix.trace (D.projRingHom i β) := by
      conv_lhs => rw [trace_mulLeft_algEquiv D.iso (e * β)]
      rw [trace_mulLeft_pi]
      -- Goal: ∑ j, d_j * tr(D.iso(e*β) j) = d_i * tr(π_i(β))
      have h_zero : ∀ j, j ≠ i → (D.iso (e * β)) j = 0 := fun j hj => by
        rw [hiso]; exact Pi.single_eq_of_ne hj _
      have h_same : (D.iso (e * β)) i = D.projRingHom i β := by
        rw [hiso]; exact Pi.single_eq_same i _
      rw [Finset.sum_eq_single i
        (fun j _ hj => by rw [h_zero j hj]; simp)
        (fun h => absurd (Finset.mem_univ i) h), h_same]
    -- Way 2: via regular character formula
    have hrt_reg := regTrace_eq_card_mul (e * β)
    -- Combine: |G| * (e*β)(1) = d_i * tr(π_i(β)) = 0
    rw [hrt_wd, hd_zero, zero_mul] at hrt_reg
    exact (mul_eq_zero.mp hrt_reg.symm).resolve_left (Invertible.ne_zero _)
  -- Contradiction: e ≠ 0 means ∃ g with e(g) ≠ 0
  obtain ⟨g, hg⟩ := Finsupp.support_nonempty_iff.mpr he_ne
  rw [Finsupp.mem_support_iff] at hg
  -- But (e * single g⁻¹ 1)(1) = e(g) ≠ 0
  have : (e * MonoidAlgebra.single g⁻¹ (1 : k)) (1 : G) = e g := by
    rw [MonoidAlgebra.mul_single_apply, inv_inv, one_mul, mul_one]
  exact hg (this ▸ he_ann _)
