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
    (hsurj : ∀ (W : FDRep k G), Simple W → ∃ i, Nonempty (W ≅ V i))
    (g : G) (hg : g ≠ 1) :
    ∑ i, (D.d i : k) * (V i).character g = 0 := by
  -- Step 1: For each j, find τ j with V j ≅ columnFDRep (τ j)
  choose τ hτ using fun j => D.columnFDRep_surjective (V j) (hV j)
  -- τ is injective: if τ j₁ = τ j₂, then columnFDRep(τ j₁) = columnFDRep(τ j₂),
  -- so V j₁ ≅ V j₂, giving j₁ = j₂ by hinj
  have hτ_inj : Function.Injective τ := by
    intro j₁ j₂ h
    exact hinj j₁ j₂ ⟨(hτ j₁).some ≪≫ (h ▸ (hτ j₂).some.symm)⟩
  have hτ_bij : Function.Bijective τ := Finite.injective_iff_bijective.mp hτ_inj
  -- Step 2: Prove ∑_i d_i * (columnFDRep i).character g = 0 via trace decomposition
  have h_col : ∑ i, (D.d i : k) * (D.columnFDRep i).character g = 0 := by
    simp_rw [columnFDRep_character_eq D _ g]
    have h1 : LinearMap.trace k (MonoidAlgebra k G) (LinearMap.mulLeft k (MonoidAlgebra.of k G g)) = 0 := by
      have := regularCharacter_ne_one (k := k) g hg
      rwa [ofMulAction_eq_mulLeft] at this
    rw [trace_mulLeft_algEquiv D.iso, trace_mulLeft_pi] at h1
    exact h1
  -- Step 3: Relate V version to column version
  -- (V j).character = (columnFDRep (τ j)).character by char_iso
  have hchar : ∀ j, (V j).character g = (D.columnFDRep (τ j)).character g := by
    intro j; exact congr_fun (FDRep.char_iso (hτ j).some) g
  -- D.d j = D.d (τ j) via d_eq_finrank + finrank preserved by iso
  have hd : ∀ j, (D.d j : k) = (D.d (τ j) : k) := by
    intro j
    have hfr := D.d_eq_finrank V hV hinj hsurj
    congr 1; rw [hfr j, ← D.finrank_columnFDRep (τ j)]
    exact LinearEquiv.finrank_eq (FDRep.isoToLinearEquiv (hτ j).some)
  -- Rewrite each term and reindex
  conv_lhs => arg 2; ext j; rw [hchar j, hd j]
  -- Now goal: ∑ j, d_{τ j} * (columnFDRep (τ j)).char g = 0
  -- Reindex: ∑ j, f (τ j) = ∑ i, f i since τ is a bijection
  let τ_equiv := Equiv.ofBijective τ hτ_bij
  have : ∑ j, (D.d (τ j) : k) * (D.columnFDRep (τ j)).character g =
    ∑ i, (D.d i : k) * (D.columnFDRep i).character g :=
    Finset.sum_equiv τ_equiv (fun _ => by simp) (fun _ _ => rfl)
  rw [this]; exact h_col
