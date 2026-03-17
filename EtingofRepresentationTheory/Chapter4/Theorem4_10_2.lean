import Mathlib
import EtingofRepresentationTheory.Chapter4.Definition4_10_1
import EtingofRepresentationTheory.Infrastructure.IrreducibleEnumeration
import EtingofRepresentationTheory.Chapter4.Lemma4_10_3

/-!
# Theorem 4.10.2: Factorization of the Frobenius Determinant

The Frobenius determinant factors as:
$$\det X_G = \prod_{j=1}^{r} P_j(\mathbf{x})^{\deg P_j}$$
where P₁, …, Pᵣ are pairwise non-proportional irreducible polynomials over ℂ,
and r is the number of conjugacy classes (= number of irreducible representations).

The factor Pⱼ corresponds to the j-th irreducible representation Vⱼ of G, with
deg Pⱼ = dim Vⱼ. The proof uses the Artin–Wedderburn decomposition of ℂ[G] and
the multiplicativity of determinants.

## Mathlib correspondence

Not in Mathlib. This is Frobenius's original factorization theorem connecting the
group determinant to representation theory.
-/

universe u

open MvPolynomial Matrix Finset

variable {k G : Type u} [Field k] [IsAlgClosed k] [Group G] [Fintype G] [DecidableEq G]

/-! ### Block polynomial definition -/

/-- The block polynomial for the i-th Wedderburn component: the determinant of
the matrix ∑_g x_g · ρ_i(g), where ρ_i is the i-th irreducible representation.
This is a polynomial of degree d_i in the variables {x_g : g ∈ G}. -/
noncomputable def IrrepDecomp.blockPoly [NeZero (Nat.card G : k)]
    (D : IrrepDecomp k G) (i : Fin D.n) : MvPolynomial G k :=
  det (of fun (a b : Fin (D.d i)) =>
    ∑ g : G, C (D.projRingHom i (MonoidAlgebra.of k G g) a b) * X g)

/-! ### Helper lemmas for the factorization proof -/

section NormHelpers

variable (R : Type*) [CommRing R]

/-- The algebra norm of an element in a product of algebras equals the product of
the norms of the components. Uses the fact that left multiplication is block diagonal
in the product basis. -/
private lemma Algebra.norm_pi {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ι → Type*} [∀ i, Ring (A i)] [∀ i, Algebra R (A i)]
    [∀ i, Module.Free R (A i)] [∀ i, Module.Finite R (A i)]
    (x : ∀ i, A i) :
    Algebra.norm R x = ∏ i, Algebra.norm R (x i) := by
  -- Induction on ι via Fintype.induction_empty_option
  apply Fintype.induction_empty_option
    (P := fun (ι : Type _) [Fintype ι] => ∀ (A : ι → Type _) [∀ i, Ring (A i)] [∀ i, Algebra R (A i)]
        [∀ i, Module.Free R (A i)] [∀ i, Module.Finite R (A i)] (x : ∀ i, A i),
        Algebra.norm R x = ∏ i, Algebra.norm R (x i))
  · -- of_equiv case
    intro α β hβ e IH A hRingA hAlgA hFreeA hFiniteA x
    let eA : (∀ i : α, A (e i)) ≃ₐ[R] (∀ i : β, A i) := AlgEquiv.piCongrLeft R A e
    have hkey : Algebra.norm R (eA.symm x) = Algebra.norm R x :=
      Algebra.norm_eq_of_algEquiv eA.symm x
    have hval : eA.symm x = fun i => x (e i) := by
      ext i
      rw [show (eA.symm x) i = ((Equiv.piCongrLeft (fun j => A j) e).symm x) i from rfl]
      rw [Equiv.piCongrLeft_symm_apply]
    rw [← hkey, hval]
    letI : Fintype α := Fintype.ofEquiv β e.symm
    rw [IH (A := fun i => A (e i)) (x := fun i => x (e i))]
    exact Fintype.prod_equiv e (fun i => Algebra.norm R (x (e i)))
      (fun i => Algebra.norm R (x i)) (fun i => rfl)
  · -- h_empty case: PEmpty
    intro A _ _ _ _ x
    simp only [Fintype.prod_empty]
    have hx : x = 1 := by ext i; exact PEmpty.elim i
    rw [hx, map_one]
  · -- h_option case: Option ι'
    intro ι' _ IH A _ _ _ _ x
    haveI : DecidableEq ι' := Classical.decEq ι'
    -- Build AlgEquiv for (∀ i : Option ι', A i) ≃ₐ[R] A none × (∀ i, A (some i))
    let e : (∀ i : Option ι', A i) ≃ₐ[R] A none × (∀ i, A (some i)) :=
      { RingEquiv.piOptionEquivProd with
        commutes' := fun r => by
          ext i
          · simp [RingEquiv.piOptionEquivProd, Equiv.piOptionEquivProd]
          · simp [RingEquiv.piOptionEquivProd, Equiv.piOptionEquivProd] }
    have hstep : Algebra.norm R (e x) = Algebra.norm R x := Algebra.norm_eq_of_algEquiv e x
    have IHsome := IH (A := fun i => A (some i))
    -- norm of a product ring is the product of norms (for specific pair type)
    have norm_pair : Algebra.norm R (e x) = Algebra.norm R (e x).1 * Algebra.norm R (e x).2 := by
      simp only [Algebra.norm_apply]
      rw [show Algebra.lmul R (A none × (∀ i, A (some i))) (e x) =
          LinearMap.prodMap (Algebra.lmul R (A none) (e x).1)
            (Algebra.lmul R (∀ i, A (some i)) (e x).2) from ?hlmul]
      · exact LinearMap.det_prodMap _ _
      case hlmul =>
        apply LinearMap.ext; intro ⟨a, b⟩
        simp only [Algebra.coe_lmul_eq_mul, LinearMap.prodMap_apply]; rfl
    rw [← hstep]
    rw [norm_pair]
    simp only [show (e x).1 = x none from rfl, show (e x).2 = fun i => x (some i) from rfl]
    rw [IHsome, Fintype.prod_option]

/-- The algebra norm of a matrix `M : Matrix (Fin n) (Fin n) R` (viewed as an element
of the matrix algebra over R) equals `det(M) ^ n`. Left multiplication by M on Mat(n,R)
acts as M on each column independently, giving `M ⊗ₖ 1` whose determinant is `det(M)^n`. -/
private lemma Algebra.norm_matrix {n : ℕ} [NeZero n]
    (M : Matrix (Fin n) (Fin n) R) :
    Algebra.norm R M = M.det ^ n := by
  open Kronecker in
  rw [Algebra.norm_eq_matrix_det (Matrix.stdBasis R (Fin n) (Fin n))]
  have hkron : Algebra.leftMulMatrix (Matrix.stdBasis R (Fin n) (Fin n)) M =
      M ⊗ₖ (1 : Matrix (Fin n) (Fin n) R) := by
    ext ⟨i₁, j₁⟩ ⟨i₂, j₂⟩
    simp only [Algebra.leftMulMatrix_eq_repr_mul, Matrix.kroneckerMap_apply, Matrix.one_apply,
               Matrix.stdBasis_eq_single]
    have hmul : M * Matrix.single i₂ j₂ (1 : R) =
        Matrix.of (fun r c => M r i₂ * if c = j₂ then 1 else 0) := by
      ext r c
      simp only [Matrix.mul_apply, Matrix.single_apply, Matrix.of_apply, mul_ite, mul_one, mul_zero]
      rw [Finset.sum_eq_single i₂]
      · simp [eq_comm]
      · intro k _ hk; simp [Ne.symm hk]
      · simp
    rw [hmul]
    simp [Matrix.stdBasis, Equiv.sigmaEquivProd_symm_apply, Pi.basis_repr, Pi.basisFun_repr,
          Matrix.ofLinearEquiv]
  open Kronecker in
  rw [hkron, Matrix.det_kronecker, Matrix.det_one, Fintype.card_fin, one_pow, mul_one]

end NormHelpers

/-! ### Helper lemmas for factorization proof -/

/-- The left multiplication matrix of `a : MonoidAlgebra k G` in the Finsupp basis
has `(g, h)` entry `a (g * h⁻¹)`. -/
private lemma leftMulMatrix_monoidAlgebra_entry
    (a : MonoidAlgebra k G) (g h : G) :
    Algebra.leftMulMatrix (Finsupp.basisSingleOne (R := k)) a g h =
      a (g * h⁻¹) := by
  simp only [Algebra.leftMulMatrix_eq_repr_mul, Finsupp.basisSingleOne_repr,
    Finsupp.coe_basisSingleOne]
  exact (a.mul_single_apply_aux
    (fun m' _ => eq_mul_inv_iff_mul_eq.symm)).trans (mul_one _)

/-- The projection ring homomorphism commutes with scalar multiplication. -/
private lemma IrrepDecomp.projRingHom_smul' [NeZero (Nat.card G : k)]
    (D : IrrepDecomp k G) (i : Fin D.n)
    (r : k) (a : MonoidAlgebra k G) :
    D.projRingHom i (r • a) = r • D.projRingHom i a := by
  simp [IrrepDecomp.projRingHom]

/-- The Frobenius determinant equals the product of block polynomials raised to their
respective dimensions. -/
private lemma IrrepDecomp.frobeniusDet_eq_prod [NeZero (Nat.card G : k)]
    (D : IrrepDecomp k G) :
    Etingof.FrobeniusDeterminant k G = ∏ i : Fin D.n, D.blockPoly i ^ D.d i := by
  -- Use funext: reduce to showing equality for all evaluations σ : G → k
  haveI : Infinite k := IsAlgClosed.instInfinite
  apply MvPolynomial.funext
  intro σ
  -- Define the group algebra element corresponding to σ
  set a : MonoidAlgebra k G := ∑ s : G, σ s • MonoidAlgebra.of k G s with ha_def
  -- Evaluate LHS: det of group matrix
  have hLHS : MvPolynomial.eval σ (Etingof.FrobeniusDeterminant k G) =
      (Matrix.of fun g h : G => σ (g * h⁻¹)).det := by
    unfold Etingof.FrobeniusDeterminant
    rw [RingHom.map_det]
    congr 1; ext g h; simp [Matrix.map, Matrix.of_apply, MvPolynomial.eval_X]
  -- Evaluate RHS: product of block determinants
  have hRHS : MvPolynomial.eval σ (∏ i : Fin D.n, D.blockPoly i ^ D.d i) =
      ∏ i : Fin D.n, (MvPolynomial.eval σ (D.blockPoly i)) ^ D.d i := by
    rw [map_prod]; congr 1; ext i; rw [map_pow]
  -- Each blockPoly evaluates to det of projRingHom i a
  have hblock_eq : ∀ i : Fin D.n, MvPolynomial.eval σ (D.blockPoly i) =
      (D.projRingHom i a).det := by
    intro i
    unfold IrrepDecomp.blockPoly
    rw [RingHom.map_det]
    congr 1
    funext r c
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, of_apply, map_sum, map_mul,
      MvPolynomial.eval_C, MvPolynomial.eval_X]
    rw [ha_def, map_sum]
    simp only [D.projRingHom_smul' i, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl; intro g _; ring
  -- The LHS matrix det equals Algebra.norm k a
  have hLHS_eq : (Matrix.of fun g h : G => σ (g * h⁻¹)).det = Algebra.norm k a := by
    rw [Algebra.norm_eq_matrix_det (Finsupp.basisSingleOne (R := k))]
    congr 1
    funext g h
    rw [of_apply, leftMulMatrix_monoidAlgebra_entry]
    change σ (g * h⁻¹) = (∑ s : G, σ s • MonoidAlgebra.of k G s : MonoidAlgebra k G) (g * h⁻¹)
    rw [Finsupp.finset_sum_apply]
    simp [MonoidAlgebra.of_apply, Finsupp.smul_apply, Finsupp.single_apply]
  -- Chain the equalities
  rw [hLHS, hRHS]
  simp_rw [hblock_eq]
  rw [hLHS_eq]
  -- Now: Algebra.norm k a = ∏ i, (projRingHom i a).det ^ d i
  rw [show Algebra.norm k a = Algebra.norm k (D.iso a) from
    (Algebra.norm_eq_of_algEquiv D.iso a).symm]
  rw [Algebra.norm_pi k]
  congr 1; ext i
  haveI := D.d_pos i
  rw [Algebra.norm_matrix k]
  -- D.iso a i = projRingHom i a: handled by congr
  congr 2

/-! ### Generic determinant irreducibility over k -/

section GenericDet

variable {k' : Type*} [Field k'] {σ : Type*} [DecidableEq σ]

/-- vars(a) ⊆ vars(a * b) when both nonzero, in a polynomial ring over a domain. -/
private lemma vars_sub_mul_left {a b : MvPolynomial σ k'} (ha : a ≠ 0) (hb : b ≠ 0) :
    a.vars ⊆ (a * b).vars := by
  intro x hx
  simp only [MvPolynomial.vars_def] at hx ⊢
  rw [Multiset.mem_toFinset] at hx ⊢
  rw [← Multiset.count_pos] at hx ⊢
  rw [← MvPolynomial.degreeOf_def] at hx ⊢
  have := MvPolynomial.degreeOf_mul_eq ha hb (n := x)
  omega

/-- Injective rename preserves irreducibility over any field. -/
private lemma rename_irred {τ : Type*} [DecidableEq τ]
    {f : σ → τ} (hf : Function.Injective f)
    {p : MvPolynomial σ k'} (hp : Irreducible p) :
    Irreducible (MvPolynomial.rename f p) := by
  constructor
  · intro h
    exact hp.1 ((MvPolynomial.killCompl_rename_app hf p) ▸
      h.map (MvPolynomial.killCompl hf).toRingHom)
  · intro a b hab
    have hne : MvPolynomial.rename f p ≠ 0 :=
      (MvPolynomial.rename_injective f hf).ne hp.ne_zero
    have ha : a ≠ 0 := left_ne_zero_of_mul (hab ▸ hne)
    have hb : b ≠ 0 := right_ne_zero_of_mul (hab ▸ hne)
    have hvars_rfp : ∀ x ∈ (MvPolynomial.rename f p).vars, x ∈ Set.range f := by
      intro x hx; obtain ⟨y, _, rfl⟩ := MvPolynomial.mem_vars_rename f p hx
      exact Set.mem_range_self y
    have hvars_a : ↑a.vars ⊆ Set.range f := by
      intro x hx; exact hvars_rfp x (hab ▸ vars_sub_mul_left ha hb hx)
    have hvars_b : ↑b.vars ⊆ Set.range f := by
      intro x hx; exact hvars_rfp x (hab ▸ mul_comm a b ▸ vars_sub_mul_left hb ha hx)
    obtain ⟨a', rfl⟩ := MvPolynomial.exists_rename_eq_of_vars_subset_range a f hf hvars_a
    obtain ⟨b', rfl⟩ := MvPolynomial.exists_rename_eq_of_vars_subset_range b f hf hvars_b
    rw [← map_mul] at hab
    have hab' : p = a' * b' := (MvPolynomial.rename_injective f hf) hab
    exact (hp.isUnit_or_isUnit hab').imp
      (·.map (MvPolynomial.rename f).toRingHom) (·.map (MvPolynomial.rename f).toRingHom)

end GenericDet

/-- The generic determinant is irreducible over any field.
This is a generalization of `Etingof.Lemma4_10_3` from ℂ to an arbitrary field. -/
private lemma genDet_irreducible (k' : Type*) [Field k'] (n : ℕ) (hn : 0 < n) :
    Irreducible (det (mvPolynomialX (Fin n) (Fin n) k')) := by
  induction n with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero =>
      have hdet : det (mvPolynomialX (Fin 1) (Fin 1) k') = MvPolynomial.X ((0 : Fin 1), (0 : Fin 1)) := by
        rw [det_fin_one]; rfl
      rw [hdet]
      exact MvPolynomial.irreducible_of_totalDegree_eq_one
        (MvPolynomial.totalDegree_X _)
        (fun x hx => isUnit_of_dvd_one (by
          have := hx (Finsupp.single ((0 : Fin 1), (0 : Fin 1)) 1)
          rwa [MvPolynomial.coeff_X] at this))
    | succ n =>
      have ih' := ih (by omega)
      -- Abbreviations for the generic matrix and its submatrices
      set M := mvPolynomialX (Fin (n + 2)) (Fin (n + 2)) k' with hM_def
      -- Submatrix identities: minor_{0,c} = rename of smaller det
      have hsub_rename : ∀ c : Fin (n + 2),
          det (M.submatrix Fin.succ (Fin.succAbove c)) =
          MvPolynomial.rename (Prod.map Fin.succ (Fin.succAbove c))
            (det (mvPolynomialX (Fin (n + 1)) (Fin (n + 1)) k')) := by
        intro c; rw [AlgHom.map_det]; congr 1; funext i j
        simp only [submatrix_apply, AlgHom.mapMatrix_apply, Matrix.map_apply,
          hM_def, mvPolynomialX_apply, MvPolynomial.rename_X, Prod.map]
      -- Variables in submatrix minors have first component ≥ 1
      have hsub_vars : ∀ c : Fin (n + 2), ∀ v ∈
          (det (M.submatrix Fin.succ (Fin.succAbove c))).vars, v.1 ≠ 0 := by
        intro c v hv; rw [hsub_rename c] at hv
        obtain ⟨⟨a, b⟩, _, hab⟩ := MvPolynomial.mem_vars_rename _ _ hv
        exact hab ▸ Fin.succ_ne_zero a
      -- Minor_{0,0} ≠ 0
      have hf_ne : det (M.submatrix Fin.succ (Fin.succAbove 0)) ≠ 0 := by
        rw [hsub_rename 0]
        exact (MvPolynomial.rename_injective _
          (Prod.map_injective.mpr ⟨Fin.succ_injective _, Fin.succAbove_right_injective⟩)).ne
          (det_mvPolynomialX_ne_zero (Fin (n + 1)) k')
      -- (0,0) ∉ vars(minor_{0,0})
      have hf_vars : ((0 : Fin (n + 2)), (0 : Fin (n + 2))) ∉
          (det (M.submatrix Fin.succ (Fin.succAbove 0))).vars := by
        intro h; exact absurd rfl (hsub_vars 0 _ h)
      -- (0,0) ∉ vars(rest of cofactor expansion)
      have hg_vars : ((0 : Fin (n + 2)), (0 : Fin (n + 2))) ∉
          (∑ j : Fin (n + 1),
            (-1 : MvPolynomial (Fin (n + 2) × Fin (n + 2)) k') ^ ((j : ℕ) + 1) *
            MvPolynomial.X ((0 : Fin (n + 2)), j.succ) *
            det (M.submatrix Fin.succ (Fin.succAbove j.succ))).vars := by
        intro h
        have h' := MvPolynomial.vars_sum_subset (Finset.univ) _ h
        simp only [Finset.mem_biUnion, Finset.mem_univ, true_and] at h'
        obtain ⟨j, hj⟩ := h'
        have hj' := MvPolynomial.vars_mul _ _ hj
        simp only [Finset.mem_union] at hj'
        rcases hj' with hj' | hj'
        · have hj'' := MvPolynomial.vars_mul _ _ hj'
          simp only [Finset.mem_union] at hj''
          rcases hj'' with hj'' | hj''
          · exact absurd (MvPolynomial.vars_pow _ _ hj'') (by simp)
          · rw [MvPolynomial.vars_X] at hj''
            simp only [Finset.mem_singleton] at hj''
            exact absurd (congr_arg Prod.snd hj'').symm (Fin.succ_ne_zero j)
        · exact absurd rfl (hsub_vars j.succ _ hj')
      -- Minor_{0,0} is irreducible
      have hf_irr : Irreducible (det (M.submatrix Fin.succ (Fin.succAbove 0))) := by
        rw [hsub_rename 0]; simp only [Fin.succAbove_zero]
        exact rename_irred (Prod.map_injective.mpr
          ⟨Fin.succ_injective _, Fin.succ_injective _⟩) ih'
      -- Minor_{0,1} is irreducible
      have hf1_irr : Irreducible (det (M.submatrix Fin.succ
          (Fin.succAbove (1 : Fin (n + 2))))) := by
        rw [hsub_rename 1]
        exact rename_irred (Prod.map_injective.mpr
          ⟨Fin.succ_injective _, Fin.succAbove_right_injective⟩) ih'
      -- IsRelPrime(minor_{0,0}, rest) via evaluation argument
      have hrel : IsRelPrime
          (det (M.submatrix Fin.succ (Fin.succAbove 0)))
          (∑ j : Fin (n + 1),
            (-1 : MvPolynomial (Fin (n + 2) × Fin (n + 2)) k') ^ ((j : ℕ) + 1) *
            MvPolynomial.X ((0 : Fin (n + 2)), j.succ) *
            det (M.submatrix Fin.succ (Fin.succAbove j.succ))) := by
        rw [hf_irr.isRelPrime_iff_not_dvd]
        -- Define evaluation: X(0,1)→1, X(0,j)→0 for j≠1, X(i,j)→X(i,j) for i≥1
        let φ : (Fin (n + 2) × Fin (n + 2)) → MvPolynomial (Fin (n + 2) × Fin (n + 2)) k' :=
          fun v => if v.1 = 0 then (if v.2 = 1 then 1 else 0) else MvPolynomial.X v
        have aeval_X_id : ∀ (p : MvPolynomial (Fin (n + 2) × Fin (n + 2)) k'),
            MvPolynomial.aeval (MvPolynomial.X : _ → MvPolynomial (Fin (n + 2) × Fin (n + 2)) k') p = p := by
          have : MvPolynomial.aeval (MvPolynomial.X : _ → MvPolynomial (Fin (n + 2) × Fin (n + 2)) k') =
              AlgHom.id k' _ := by ext i; simp
          intro p; rw [this]; simp
        -- φ fixes any submatrix minor (no row-0 variables)
        have hφ_fix : ∀ (c : Fin (n + 2)),
            MvPolynomial.aeval φ (det (M.submatrix Fin.succ (Fin.succAbove c))) =
            det (M.submatrix Fin.succ (Fin.succAbove c)) := by
          intro c
          have hφ_eq : ∀ v ∈ (det (M.submatrix Fin.succ (Fin.succAbove c))).vars,
              φ v = MvPolynomial.X v := by
            intro v hv; simp only [φ, if_neg (hsub_vars c v hv)]
          rw [show MvPolynomial.aeval φ (det (M.submatrix Fin.succ (Fin.succAbove c))) =
            MvPolynomial.aeval MvPolynomial.X (det (M.submatrix Fin.succ (Fin.succAbove c))) from
            MvPolynomial.eval₂Hom_congr' rfl (fun i hi _ => hφ_eq i hi) rfl]
          exact aeval_X_id _
        -- φ(X(0, j.succ)) = 1 if j = 0, else 0
        have hφ_X : ∀ j : Fin (n + 1),
            φ ((0 : Fin (n + 2)), j.succ) = if j = 0 then 1 else 0 := by
          intro j; simp only [φ, ite_true]
          rcases Decidable.eq_or_ne j 0 with rfl | hj
          · simp [show Fin.succ (0 : Fin (n + 1)) = (1 : Fin (n + 2)) from rfl]
          · simp [show Fin.succ j ≠ (1 : Fin (n + 2)) from by
              rwa [show (1 : Fin (n + 2)) = Fin.succ 0 from rfl, Ne, Fin.succ_inj], hj]
        -- Suppose minor_{0,0} | rest
        intro ⟨q, hq⟩
        -- Apply aeval φ: φ(rest) = -minor_{0,1}
        have hφ_rest : MvPolynomial.aeval φ (∑ j : Fin (n + 1),
            (-1 : MvPolynomial (Fin (n + 2) × Fin (n + 2)) k') ^ ((j : ℕ) + 1) *
            MvPolynomial.X ((0 : Fin (n + 2)), j.succ) *
            det (M.submatrix Fin.succ (Fin.succAbove j.succ))) =
            -det (M.submatrix Fin.succ (Fin.succAbove (1 : Fin (n + 2)))) := by
          simp only [map_sum, map_mul, map_pow, map_neg, map_one, MvPolynomial.aeval_X,
            hφ_fix, hφ_X]; rw [Fin.sum_univ_succ]; simp
        -- So minor_{0,0} | minor_{0,1}
        have hdvd : det (M.submatrix Fin.succ (Fin.succAbove 0)) ∣
            det (M.submatrix Fin.succ (Fin.succAbove 1)) := by
          have h1 : MvPolynomial.aeval φ (det (M.submatrix Fin.succ (Fin.succAbove 0))) ∣
              MvPolynomial.aeval φ (∑ j : Fin (n + 1),
                (-1 : MvPolynomial (Fin (n + 2) × Fin (n + 2)) k') ^ ((j : ℕ) + 1) *
                MvPolynomial.X ((0 : Fin (n + 2)), j.succ) *
                det (M.submatrix Fin.succ (Fin.succAbove j.succ))) :=
            (MvPolynomial.aeval φ).toRingHom.map_dvd ⟨q, hq⟩
          rw [hφ_fix 0, hφ_rest] at h1; exact dvd_neg.mp h1
        -- Both irreducible, so associated
        have hassoc := hf_irr.associated_of_dvd hf1_irr hdvd
        obtain ⟨u, hu⟩ := hassoc
        -- Variable (1,1) is in vars(minor_{0,0}) but not vars(minor_{0,1})
        have hmem : ((1 : Fin (n + 2)), (1 : Fin (n + 2))) ∈
            (det (M.submatrix Fin.succ (Fin.succAbove 0))).vars := by
          by_contra habs
          let g₁ : Fin (n + 2) × Fin (n + 2) → k' := fun ⟨i, j⟩ => if i = j then 1 else 0
          let g₂ : Fin (n + 2) × Fin (n + 2) → k' := Function.update g₁ (1, 1) 0
          have hag : ∀ i ∈ (det (M.submatrix Fin.succ (Fin.succAbove 0))).vars,
              g₁ i = g₂ i := by
            intro i hi; exact (Function.update_of_ne (ne_of_mem_of_not_mem hi habs) _ _).symm
          have heq : MvPolynomial.eval g₁ (det (M.submatrix Fin.succ (Fin.succAbove 0))) =
              MvPolynomial.eval g₂ (det (M.submatrix Fin.succ (Fin.succAbove 0))) :=
            MvPolynomial.eval₂Hom_congr' rfl (fun i hi _ => hag i hi) rfl
          have hev1 : MvPolynomial.eval g₁
              (det (M.submatrix Fin.succ (Fin.succAbove 0))) = 1 := by
            rw [show MvPolynomial.eval g₁ (det (M.submatrix Fin.succ (Fin.succAbove 0))) =
              det ((MvPolynomial.eval g₁).mapMatrix
                (M.submatrix Fin.succ (Fin.succAbove 0))) from RingHom.map_det _ _]
            have : (MvPolynomial.eval g₁).mapMatrix
                (M.submatrix Fin.succ (Fin.succAbove 0)) =
                (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k') := by
              ext i j
              simp only [RingHom.mapMatrix_apply, Matrix.map_apply, submatrix_apply,
                hM_def, mvPolynomialX_apply, MvPolynomial.eval_X, Fin.succAbove_zero, one_apply]
              simp only [g₁, Fin.succ_inj]
            rw [this, det_one]
          have hev0 : MvPolynomial.eval g₂
              (det (M.submatrix Fin.succ (Fin.succAbove 0))) = 0 := by
            rw [show MvPolynomial.eval g₂ (det (M.submatrix Fin.succ (Fin.succAbove 0))) =
              det ((MvPolynomial.eval g₂).mapMatrix
                (M.submatrix Fin.succ (Fin.succAbove 0))) from RingHom.map_det _ _]
            apply det_eq_zero_of_row_eq_zero (0 : Fin (n + 1))
            intro j
            simp only [RingHom.mapMatrix_apply, Matrix.map_apply, submatrix_apply,
              hM_def, mvPolynomialX_apply, MvPolynomial.eval_X, Fin.succAbove_zero]
            simp only [g₂, g₁, Function.update_apply, Prod.mk.injEq]
            by_cases hj : j = 0
            · subst hj; simp [hM_def]
            · have hjs1 : ¬(j.succ : Fin (n + 2)) = (1 : Fin (n + 2)) := by
                intro h; exact hj (Fin.succ_injective _ h)
              simp [Fin.succ_ne_zero, hjs1, show (Fin.succ (0 : Fin (n + 1)) : Fin (n + 2)) =
                (1 : Fin (n + 2)) from rfl, Ne.symm (show ¬j.succ = (1 : Fin (n + 2)) from hjs1)]
          exact absurd (hev1.symm.trans (heq.trans hev0)) one_ne_zero
        have hnotmem : ((1 : Fin (n + 2)), (1 : Fin (n + 2))) ∉
            (det (M.submatrix Fin.succ (Fin.succAbove (1 : Fin (n + 2))))).vars := by
          rw [hsub_rename 1]; intro h
          obtain ⟨⟨a, b⟩, _, hab⟩ := MvPolynomial.mem_vars_rename _ _ h
          simp only [Prod.map, Prod.mk.injEq] at hab
          exact absurd hab.2 (Fin.succAbove_ne 1 b)
        exact hnotmem (hu ▸ vars_sub_mul_left hf_irr.ne_zero (Units.ne_zero u) hmem)
      -- Cofactor expansion: det = minor_{0,0} * X(0,0) + rest
      have heq : det M =
          det (M.submatrix Fin.succ (Fin.succAbove 0)) *
          MvPolynomial.X ((0 : Fin (n + 2)), (0 : Fin (n + 2))) +
          (∑ j : Fin (n + 1),
            (-1 : MvPolynomial (Fin (n + 2) × Fin (n + 2)) k') ^ ((j : ℕ) + 1) *
            MvPolynomial.X ((0 : Fin (n + 2)), j.succ) *
            det (M.submatrix Fin.succ (Fin.succAbove j.succ))) := by
        rw [det_succ_row_zero, Fin.sum_univ_succ]
        simp only [hM_def, Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero, mvPolynomialX_apply,
          Fin.val_succ]
        ring
      rw [heq]
      exact MvPolynomial.irreducible_mul_X_add _ _ _ hf_ne hf_vars hg_vars hrel

/-- The total degree of the i-th block polynomial equals d_i. Each entry of the
representation matrix is a linear polynomial in the x_g, so det has degree ≤ d_i.
For ≥ d_i, evaluation at x₁=t, xg=0 gives det(tI)=t^{d_i}. -/
private lemma IrrepDecomp.blockPoly_totalDegree [NeZero (Nat.card G : k)]
    (D : IrrepDecomp k G) (i : Fin D.n) :
    (D.blockPoly i).totalDegree = D.d i := by
  apply le_antisymm
  · -- ≤ d_i: det of matrix with degree-1 entries
    unfold blockPoly
    let M := of fun (a b : Fin (D.d i)) =>
      ∑ g : G, C (D.projRingHom i (MonoidAlgebra.of k G g) a b) * X g
    show (det M).totalDegree ≤ D.d i
    rw [det_apply]
    apply (totalDegree_finset_sum _ _).trans
    apply Finset.sup_le
    intro σ _
    have hsmul : (Equiv.Perm.sign σ • ∏ a, M (σ a) a).totalDegree =
        (∏ a, M (σ a) a).totalDegree := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
      · simp [h]
      · simp [h, totalDegree_neg]
    rw [hsmul]
    calc (∏ a, M (σ a) a).totalDegree
        ≤ ∑ a, (M (σ a) a).totalDegree := totalDegree_finset_prod _ _
      _ ≤ ∑ _a : Fin (D.d i), 1 := by
          apply Finset.sum_le_sum; intro a _
          show (∑ g : G, C (D.projRingHom i (MonoidAlgebra.of k G g) (σ a) a) *
            X g).totalDegree ≤ 1
          apply (totalDegree_finset_sum _ _).trans
          apply Finset.sup_le; intro g _
          calc MvPolynomial.totalDegree (C _ * X g)
              ≤ MvPolynomial.totalDegree (C _) +
                MvPolynomial.totalDegree (X g) := totalDegree_mul _ _
            _ = 0 + 1 := by rw [totalDegree_C, totalDegree_X]
            _ = 1 := by ring
      _ = D.d i := by simp
  · -- ≥ d_i: blockPoly is homogeneous of degree d_i and nonzero
    -- Step 1: each entry is homogeneous of degree 1
    have hentry : ∀ (a b : Fin (D.d i)),
        (∑ g : G, C (D.projRingHom i (MonoidAlgebra.of k G g) a b) *
          X g).IsHomogeneous 1 :=
      fun a b => IsHomogeneous.sum _ _ _ fun g _ =>
        (MvPolynomial.isHomogeneous_C (σ := G)
          (D.projRingHom i (MonoidAlgebra.of k G g) a b)).mul
          (MvPolynomial.isHomogeneous_X (R := k) g)
    -- Step 2: blockPoly is homogeneous of degree d_i
    have hhom : (D.blockPoly i).IsHomogeneous (D.d i) := by
      unfold blockPoly; rw [det_apply]
      apply IsHomogeneous.sum; intro σ _
      have hprod : IsHomogeneous (∏ a : Fin (D.d i),
          of (fun a b => ∑ g : G,
            C (D.projRingHom i (MonoidAlgebra.of k G g) a b) * X g)
          (σ a) a) (∑ _a : Fin (D.d i), 1) := by
        apply IsHomogeneous.prod; intro a _
        exact hentry (σ a) a
      simp only [Finset.sum_const, Finset.card_fin, smul_eq_mul, mul_one] at hprod
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
      · rw [h, one_smul]; exact hprod
      · simp only [h, Units.smul_def] at *
        rw [show ((-1 : ℤˣ) : ℤ) = -1 from rfl, neg_one_zsmul]
        exact (homogeneousSubmodule G k (D.d i)).neg_mem hprod
    -- Step 3: blockPoly is nonzero (eval at x₁=1, rest=0 gives det(I)=1)
    have hne : D.blockPoly i ≠ 0 := by
      intro h
      have heval : MvPolynomial.eval
          (fun g => if g = (1 : G) then (1 : k) else 0) (D.blockPoly i) = 1 := by
        unfold blockPoly
        rw [show MvPolynomial.eval _ (det _) = det
          ((MvPolynomial.eval _).mapMatrix _) from RingHom.map_det _ _]
        have hmat : (MvPolynomial.eval
            (fun g => if g = (1 : G) then (1 : k) else 0)).mapMatrix
            (of fun a b => ∑ g : G,
              C (D.projRingHom i (MonoidAlgebra.of k G g) a b) * X g) =
            (1 : Matrix (Fin (D.d i)) (Fin (D.d i)) k) := by
          ext a b
          simp only [RingHom.mapMatrix_apply, Matrix.map_apply, of_apply,
            map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X,
            one_apply]
          simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
            Finset.mem_univ, ite_true]
          have : D.projRingHom i (MonoidAlgebra.of k G 1) = 1 := by
            have h1 : MonoidAlgebra.of k G (1 : G) = 1 := map_one _
            rw [h1, map_one]
          rw [this]; simp [one_apply]
        rw [hmat, det_one]
      rw [h, map_zero] at heval; exact one_ne_zero heval.symm
    -- Step 4: combine
    exact (hhom.totalDegree hne).symm.le

/-- Each block polynomial is irreducible. The proof uses the fact that the generic
determinant is irreducible over k, and the block polynomial is obtained from it
via a surjective linear substitution (from the Wedderburn projection).

The key idea: construct a retraction ψ such that aeval ψ ∘ aeval φ = id (from
surjectivity of projRingHom), then use totalDegree additivity in domains to show
that any factor of blockPoly that maps to a unit under ψ must itself be a unit. -/
private lemma IrrepDecomp.blockPoly_irreducible [NeZero (Nat.card G : k)]
    (D : IrrepDecomp k G) (i : Fin D.n) :
    Irreducible (D.blockPoly i) := by
  /- Proof sketch: The generic determinant det(X_{a,b}) is irreducible (genDet_irreducible).
     blockPoly i = aeval φ (det(X)) where φ maps (a,b) to ∑_g c_{g,a,b} · X_g.
     From surjectivity of projRingHom, we construct a retraction ψ with aeval ψ ∘ aeval φ = id.
     Then any factorization blockPoly = a * b maps via ψ to a factorization of det(X),
     and the degree bound from ψ forces one factor to be constant, hence a unit. -/
  sorry

/-- Block polynomials for different Wedderburn components are not associated.
If d_i ≠ d_j, they have different total degrees. If d_i = d_j, they involve
different linear combinations of variables (by the injectivity of column FDReps). -/
private lemma IrrepDecomp.blockPoly_not_associated [NeZero (Nat.card G : k)]
    (D : IrrepDecomp k G) (i j : Fin D.n) (hij : i ≠ j) :
    ¬Associated (D.blockPoly i) (D.blockPoly j) := by
  intro ⟨u, hu⟩
  -- Define the central idempotent e_i and evaluate blockPolys at its coefficients
  set e := D.iso.symm (Pi.single i (1 : Matrix (Fin (D.d i)) (Fin (D.d i)) k)) with he_def
  set σ : G → k := fun g => e g with hσ_def
  -- The group algebra element reconstructed from σ equals e
  have ha_eq : ∑ g : G, σ g • MonoidAlgebra.of k G g = e := by
    conv_rhs => rw [← Finsupp.univ_sum_single e]
    congr 1; ext g
    simp [hσ_def, MonoidAlgebra.of_apply, Finsupp.smul_single', mul_one]
  -- Evaluate blockPoly at σ: eval σ (blockPoly l) = det(projRingHom l (e))
  have heval_eq : ∀ l : Fin D.n, MvPolynomial.eval σ (D.blockPoly l) =
      (D.projRingHom l e).det := by
    intro l
    unfold IrrepDecomp.blockPoly
    rw [RingHom.map_det]
    congr 1; ext r c
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, map_sum, map_mul,
      MvPolynomial.eval_C, MvPolynomial.eval_X]
    conv_rhs => rw [show e = ∑ s : G, σ s • MonoidAlgebra.of k G s from ha_eq.symm]
    simp only [map_sum, D.projRingHom_smul' l, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    congr 1; ext g; ring
  -- projRingHom i e = 1 (identity matrix)
  have hei : D.projRingHom i e = 1 := by
    simp [he_def, IrrepDecomp.projRingHom, Pi.evalRingHom, Pi.single, Function.update]
  -- projRingHom j e = 0 (zero matrix, since j ≠ i)
  have hej : D.projRingHom j e = 0 := by
    simp [he_def, IrrepDecomp.projRingHom, Pi.evalRingHom, Pi.single, Function.update,
      Ne.symm hij]
  -- eval σ (blockPoly i) = 1
  have heval_i : MvPolynomial.eval σ (D.blockPoly i) = 1 := by
    rw [heval_eq, hei, det_one]
  -- eval σ (blockPoly j) = 0
  have heval_j : MvPolynomial.eval σ (D.blockPoly j) = 0 := by
    rw [heval_eq, hej]
    haveI := D.d_pos j
    haveI : Nonempty (Fin (D.d j)) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne _)⟩⟩
    exact Matrix.det_zero ‹_›
  -- From hu: blockPoly i * ↑u = blockPoly j, apply eval σ
  have heval_u : MvPolynomial.eval σ (↑u : MvPolynomial G k) = 0 := by
    have h := congr_arg (MvPolynomial.eval σ) hu
    simp only [map_mul, heval_i, heval_j, one_mul] at h
    exact h
  -- But u is a unit, so eval σ maps it to a unit in k, which can't be zero
  exact (u.isUnit.map (MvPolynomial.eval σ).toMonoidHom).ne_zero heval_u

/-- The number of Wedderburn-Artin components equals the number of conjugacy classes.
Proof: dim center(k[G]) = |ConjClasses G| (class functions) and
dim center(∏ Mat(d_i,k)) = n (scalar matrices), and the Wedderburn iso preserves centers. -/
private lemma IrrepDecomp.n_eq_card_conjClasses [NeZero (Nat.card G : k)]
    (D : IrrepDecomp k G) :
    D.n = Fintype.card (ConjClasses G) := by
  -- Step 1: dim center(k[G]) = |ConjClasses G|
  have h_center_kG : Module.finrank k ↥(Subalgebra.center k (MonoidAlgebra k G)) =
      Fintype.card (ConjClasses G) := by
    -- Center elements have conjugation-invariant coefficients, giving a linear
    -- equivalence with functions ConjClasses G → k
    have center_conj_inv : ∀ {a : MonoidAlgebra k G},
        a ∈ Subalgebra.center k (MonoidAlgebra k G) → ∀ g h : G, a (g * h * g⁻¹) = a h := by
      intro a ha g h
      rw [Subalgebra.mem_center_iff] at ha
      have key := congr_fun (congr_arg (⇑) (ha (MonoidAlgebra.of k G g))) (g * h)
      simp only [MonoidAlgebra.of, MonoidHom.coe_mk, OneHom.coe_mk,
        MonoidAlgebra.single_mul_apply, MonoidAlgebra.mul_single_apply,
        one_mul, mul_one, inv_mul_cancel_left] at key
      exact key.symm
    have conj_inv_center : ∀ (a : MonoidAlgebra k G),
        (∀ g h : G, a (g * h * g⁻¹) = a h) → a ∈ Subalgebra.center k (MonoidAlgebra k G) := by
      intro a ha
      rw [Subalgebra.mem_center_iff]; intro b
      induction b using MonoidAlgebra.induction_on with
      | hM g =>
        ext x
        simp only [MonoidAlgebra.of_apply, MonoidAlgebra.single_mul_apply,
          MonoidAlgebra.mul_single_apply, one_mul, mul_one]
        have h1 := ha g⁻¹ (x * g⁻¹)
        simp only [inv_inv, mul_assoc, inv_mul_cancel, mul_one] at h1
        exact h1
      | hadd b₁ b₂ hb₁ hb₂ => rw [mul_add, add_mul, hb₁, hb₂]
      | hsmul r b hb => rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, hb]
    let fwd : ↥(Subalgebra.center k (MonoidAlgebra k G)) →ₗ[k] (ConjClasses G → k) :=
      { toFun := fun a C => (a : MonoidAlgebra k G) (Quotient.out C)
        map_add' := fun _ _ => funext fun _ => Finsupp.add_apply _ _ _
        map_smul' := fun _ _ => funext fun _ => Finsupp.smul_apply _ _ _ }
    let bwd : (ConjClasses G → k) →ₗ[k] ↥(Subalgebra.center k (MonoidAlgebra k G)) :=
      { toFun := fun f => ⟨Finsupp.onFinset Finset.univ
            (fun g => f (ConjClasses.mk g)) (fun _ _ => Finset.mem_univ _),
          conj_inv_center _ (fun g h => by
            simp only [Finsupp.onFinset_apply]; congr 1
            rw [ConjClasses.mk_eq_mk_iff_isConj]
            exact isConj_iff.mpr ⟨g⁻¹, by group⟩)⟩
        map_add' := fun f₁ f₂ => Subtype.ext (Finsupp.ext fun g => by
          simp [Finsupp.onFinset_apply])
        map_smul' := fun r f => Subtype.ext (Finsupp.ext fun g => by
          simp [Finsupp.onFinset_apply]) }
    have hfb : ∀ f, fwd (bwd f) = f := fun f => funext fun C => by
      simp only [fwd, bwd, LinearMap.coe_mk, AddHom.coe_mk, Finsupp.onFinset_apply]
      congr 1; exact Quotient.out_eq C
    have hbf : ∀ a : ↥(Subalgebra.center k (MonoidAlgebra k G)), bwd (fwd a) = a :=
      fun ⟨a, ha⟩ => by
      ext g
      simp only [fwd, bwd, LinearMap.coe_mk, AddHom.coe_mk, Finsupp.onFinset_apply]
      have hconj : IsConj (Quotient.out (ConjClasses.mk g) : G) g := by
        have h := Quotient.out_eq (ConjClasses.mk g)
        rw [ConjClasses.quotient_mk_eq_mk] at h
        exact ConjClasses.mk_eq_mk_iff_isConj.mp h
      obtain ⟨c, hc⟩ := isConj_iff.mp hconj
      rw [show a (Quotient.out (ConjClasses.mk g)) =
          a (c * Quotient.out (ConjClasses.mk g) * c⁻¹) from
        (center_conj_inv ha c _).symm, hc]
    have e : ↥(Subalgebra.center k (MonoidAlgebra k G)) ≃ₗ[k] (ConjClasses G → k) :=
      { fwd with invFun := bwd, left_inv := hbf, right_inv := hfb }
    have : Module.finrank k (ConjClasses G → k) = Fintype.card (ConjClasses G) :=
      Module.finrank_fintype_fun_eq_card k
    linarith [e.finrank_eq]
  -- Step 2: dim center(∏ Mat(d_i, k)) = n
  have h_center_pi : Module.finrank k ↥(Subalgebra.center k
      (∀ i : Fin D.n, Matrix (Fin (D.d i)) (Fin (D.d i)) k)) = D.n := by
    let PiMat := (∀ i : Fin D.n, Matrix (Fin (D.d i)) (Fin (D.d i)) k)
    let fwd : ↥(Subalgebra.center k PiMat) →ₗ[k] (Fin D.n → k) :=
      { toFun := fun a i =>
          haveI := D.d_pos i
          (a : PiMat) i ⟨0, Nat.pos_of_ne_zero (NeZero.ne _)⟩
            ⟨0, Nat.pos_of_ne_zero (NeZero.ne _)⟩
        map_add' := fun _ _ => funext fun _ => rfl
        map_smul' := fun _ _ => funext fun _ => rfl }
    let bwd_fun : (Fin D.n → k) → PiMat :=
      fun c i => c i • (1 : Matrix (Fin (D.d i)) (Fin (D.d i)) k)
    have bwd_mem : ∀ c, bwd_fun c ∈ Subalgebra.center k PiMat := fun c => by
      rw [Subalgebra.mem_center_iff]; intro N; ext i : 1
      change N i * (c i • 1) = (c i • 1) * N i
      rw [mul_smul_comm, smul_mul_assoc, mul_one, one_mul]
    let bwd : (Fin D.n → k) →ₗ[k] ↥(Subalgebra.center k PiMat) :=
      { toFun := fun c => ⟨bwd_fun c, bwd_mem c⟩
        map_add' := fun c₁ c₂ => by
          apply Subtype.ext; funext i
          change (c₁ i + c₂ i) • (1 : Matrix _ _ k) = _
          rw [add_smul]; rfl
        map_smul' := fun r c => by
          apply Subtype.ext; funext i
          show (r * c i) • (1 : Matrix _ _ k) = (r • fun i => c i • (1 : Matrix _ _ k)) i
          simp [Pi.smul_apply, smul_smul] }
    have hfb : ∀ c, fwd (bwd c) = c := fun c => funext fun i => by
      simp only [fwd, bwd, bwd_fun, LinearMap.coe_mk, AddHom.coe_mk]
      simp [Matrix.smul_apply]
    have hbf : ∀ x : ↥(Subalgebra.center k PiMat), bwd (fwd x) = x := fun ⟨f, hf⟩ => by
      apply Subtype.ext; ext i a b
      simp only [fwd, bwd, bwd_fun, LinearMap.coe_mk, AddHom.coe_mk]
      have hfc : f i ∈ Subalgebra.center k (Matrix (Fin (D.d i)) (Fin (D.d i)) k) := by
        rw [Subalgebra.mem_center_iff]; intro M
        have hf' : ∀ b : PiMat, b * f = f * b := Subalgebra.mem_center_iff.mp hf
        have h := hf' (Pi.single (M := fun j => Matrix (Fin (D.d j)) (Fin (D.d j)) k) i M)
        have lhs : (Pi.single (M := fun j => Matrix (Fin (D.d j)) (Fin (D.d j)) k) i M * f) i =
            M * f i := by rw [Pi.mul_apply, Pi.single_eq_same]
        have rhs : (f * Pi.single (M := fun j => Matrix (Fin (D.d j)) (Fin (D.d j)) k) i M) i =
            f i * M := by rw [Pi.mul_apply, Pi.single_eq_same]
        rw [show M * f i = (Pi.single (M := fun j => Matrix (Fin (D.d j)) (Fin (D.d j)) k) i M * f) i
          from lhs.symm, h, rhs]
      rw [Algebra.IsCentral.center_eq_bot] at hfc
      rw [Algebra.mem_bot] at hfc
      obtain ⟨c, hc⟩ := Set.mem_range.mp hfc
      have hfi : f i = c • (1 : Matrix (Fin (D.d i)) (Fin (D.d i)) k) := by
        rw [← hc, Algebra.algebraMap_eq_smul_one]
      rw [hfi]; simp [Matrix.smul_apply, Matrix.one_apply]
    have e : ↥(Subalgebra.center k PiMat) ≃ₗ[k] (Fin D.n → k) :=
      { fwd with invFun := bwd, left_inv := hbf, right_inv := hfb }
    have : Module.finrank k (Fin D.n → k) = D.n := by
      rw [Module.finrank_fintype_fun_eq_card k, Fintype.card_fin]
    linarith [e.finrank_eq]
  -- Step 3: AlgEquiv preserves center finrank
  have h_iso : Module.finrank k ↥(Subalgebra.center k (MonoidAlgebra k G)) =
      Module.finrank k ↥(Subalgebra.center k
        (∀ i : Fin D.n, Matrix (Fin (D.d i)) (Fin (D.d i)) k)) := by
    let e_center : ↥(Subalgebra.center k (MonoidAlgebra k G)) ≃ₗ[k]
        ↥(Subalgebra.center k (∀ i : Fin D.n, Matrix (Fin (D.d i)) (Fin (D.d i)) k)) :=
      { toFun := fun ⟨a, ha⟩ => ⟨D.iso a, by
          rw [Subalgebra.mem_center_iff] at ha ⊢
          intro b; obtain ⟨a', rfl⟩ := D.iso.surjective b
          simp [← map_mul, ha a']⟩
        invFun := fun ⟨b, hb⟩ => ⟨D.iso.symm b, by
          rw [Subalgebra.mem_center_iff] at hb ⊢
          intro a; apply D.iso.injective
          simp [map_mul, hb (D.iso a)]⟩
        left_inv := by intro ⟨a, _⟩; ext; simp
        right_inv := by intro ⟨b, _⟩; ext; simp
        map_add' := by intro ⟨a, _⟩ ⟨b, _⟩; ext; simp [map_add]
        map_smul' := by
          intro r ⟨a, _⟩; apply Subtype.ext
          show D.iso (r • a) = r • D.iso a
          rw [map_smul] }
    exact e_center.finrank_eq
  -- Combine
  linarith

/-! ### Main theorem -/

/-- The Frobenius determinant factors into r pairwise non-associated irreducible polynomials,
each raised to the power of its total degree, where r equals the number of conjugacy classes.
Specifically, det(X_G) = ∏_{j=1}^{r} P_j^(deg P_j), where the P_j are irreducible and
pairwise non-proportional, and the total degree satisfies Σ (deg P_j)² = |G|.
(Etingof Theorem 4.10.2) -/
theorem Etingof.Theorem4_10_2
    (k : Type u) (G : Type u) [Field k] [IsAlgClosed k]
    [Group G] [Fintype G] [DecidableEq G]
    [Invertible (Fintype.card G : k)] :
    ∃ (r : ℕ) (P : Fin r → MvPolynomial G k),
      (∀ j, Irreducible (P j)) ∧
      (∀ i j, i ≠ j → ¬Associated (P i) (P j)) ∧
      Etingof.FrobeniusDeterminant k G = ∏ j : Fin r, P j ^ (P j).totalDegree ∧
      r = Fintype.card (ConjClasses G) := by
  -- Derive NeZero from Invertible
  haveI : NeZero (Nat.card G : k) := by
    refine ⟨?_⟩
    have h : (Nat.card G : k) = (Fintype.card G : k) := by
      simp only [Nat.card_eq_fintype_card]
    rw [h]; exact (isUnit_of_invertible _).ne_zero
  -- Get the Wedderburn-Artin decomposition
  let D := IrrepDecomp.mk' (k := k) (G := G)
  -- Provide witnesses and proofs
  refine ⟨D.n, D.blockPoly, D.blockPoly_irreducible, D.blockPoly_not_associated,
    ?_, D.n_eq_card_conjClasses⟩
  -- Show: FrobeniusDeterminant = ∏ blockPoly ^ totalDegree
  conv_lhs => rw [D.frobeniusDet_eq_prod]
  congr 1; ext i
  rw [D.blockPoly_totalDegree i]
