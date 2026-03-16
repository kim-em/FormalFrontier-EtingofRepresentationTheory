import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Algebra.Algebra.Tower
import Mathlib.LinearAlgebra.TensorProduct.Basis
import EtingofRepresentationTheory.Chapter3.Theorem3_2_2

/-!
# Theorem 3.10.2: Irreducible Representations of Tensor Products of Algebras

(i) Let V be an irreducible finite dimensional representation of A and let W be an
    irreducible finite dimensional representation of B. Then V ⊗ W is an irreducible
    representation of A ⊗ B.

(ii) Any irreducible finite dimensional representation M of A ⊗ B has the form (i) for
     unique V and W.

The (A ⊗_k B)-module structure on V ⊗_k W is given by (a ⊗ b) • (v ⊗ w) = (a • v) ⊗ (b • w).
Irreducibility is stated as: the only k-submodules of V ⊗ W invariant under all such
actions are {0} and the whole space.

Note: These results require k to be algebraically closed (as assumed throughout Etingof's
textbook). Without algebraic closure, the tensor product of irreducible representations
need not be irreducible (e.g., ℂ ⊗_ℝ ℂ ≅ ℂ × ℂ as ℂ ⊗ ℂ-modules).
-/

section Part1

open scoped TensorProduct

variable {k : Type*} {V W : Type*}
  [Field k]
  [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  [AddCommGroup W] [Module k W] [FiniteDimensional k W]

omit [FiniteDimensional k V] [FiniteDimensional k W] in
/-- For linear functionals φ : V →ₗ k, ψ : W →ₗ k and vectors v₀ : V, w₀ : W,
applying TensorProduct.map (φ.smulRight v₀) (ψ.smulRight w₀) to t yields
(bilinear contraction of t by φ,ψ) • (v₀ ⊗ w₀). -/
private theorem map_smulRight_smulRight_eq
    (φ : V →ₗ[k] k) (ψ : W →ₗ[k] k) (v₀ : V) (w₀ : W) (t : V ⊗[k] W) :
    TensorProduct.map (φ.smulRight v₀) (ψ.smulRight w₀) t =
      TensorProduct.lid k k (TensorProduct.map φ ψ t) • (v₀ ⊗ₜ[k] w₀) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    simp only [TensorProduct.map_tmul, LinearMap.smulRight_apply, TensorProduct.lid_tmul,
      smul_eq_mul, TensorProduct.smul_tmul_smul]
  | add x y hx hy =>
    simp only [map_add, hx, hy, add_smul]

/-- If U is a nonzero k-submodule of V ⊗ W stable under all TensorProduct.map f g,
then every pure tensor v ⊗ w is in U. -/
private theorem pure_tensors_mem_of_stable
    (U : Submodule k (V ⊗[k] W))
    (hU_end : ∀ (f : Module.End k V) (g : Module.End k W) (x : V ⊗[k] W),
        x ∈ U → TensorProduct.map f g x ∈ U)
    {u : V ⊗[k] W} (hu : u ∈ U) (hu_ne : u ≠ 0)
    (v : V) (w : W) : v ⊗ₜ[k] w ∈ U := by
  classical
  -- Decompose u using a basis of V to find φ, ψ with nonzero contraction.
  let bV := Module.finBasis k V
  let coeffs := TensorProduct.equivFinsuppOfBasisLeft bV u
  -- u ≠ 0 implies the decomposition has a nonzero W-coefficient
  have hcoeffs_ne : coeffs ≠ 0 := by
    intro h
    apply hu_ne
    have : u = (TensorProduct.equivFinsuppOfBasisLeft bV).symm coeffs :=
      ((TensorProduct.equivFinsuppOfBasisLeft bV).symm_apply_apply u).symm
    rw [this, h, map_zero]
  obtain ⟨i₀, hi₀⟩ := Finsupp.ne_iff.mp hcoeffs_ne
  simp only [Finsupp.zero_apply] at hi₀
  -- w₀ is the nonzero W-coefficient at index i₀
  set w₀ := coeffs i₀ with hw₀_def
  -- Choose φ = bV.coord i₀ and find ψ with ψ(w₀) ≠ 0
  let bW := Module.finBasis k W
  have hw₀_ne : w₀ ≠ 0 := hi₀
  have hrepr_ne : bW.repr w₀ ≠ 0 :=
    fun h => hw₀_ne (bW.repr.injective (show _ = _ by simp [h]))
  obtain ⟨j₀, hj₀⟩ := Finsupp.ne_iff.mp hrepr_ne
  simp only [Finsupp.zero_apply] at hj₀
  -- The bilinear contraction c = ψ(w₀) ≠ 0
  -- where φ = bV.coord i₀, ψ = bW.coord j₀
  -- Use the general formula: map (φ.smulRight v) (ψ.smulRight w) u = c • (v ⊗ w)
  have h_mem : TensorProduct.map ((bV.coord i₀).smulRight v) ((bW.coord j₀).smulRight w) u ∈ U :=
    hU_end _ _ u hu
  rw [map_smulRight_smulRight_eq] at h_mem
  -- The contraction TensorProduct.lid k k (TensorProduct.map (bV.coord i₀) (bW.coord j₀) u)
  -- equals ψ(w₀) ≠ 0
  set c := TensorProduct.lid k k (TensorProduct.map (bV.coord i₀) (bW.coord j₀) u)
  -- Show c ≠ 0
  have hc_ne : c ≠ 0 := by
    -- Show c = (bW.coord j₀)(w₀) = (bW.repr w₀) j₀ ≠ 0
    suffices hc_eq : c = (bW.repr w₀) j₀ by rw [hc_eq]; exact hj₀
    -- Rewrite u via the basis decomposition
    have hu_decomp : u = (TensorProduct.equivFinsuppOfBasisLeft bV).symm coeffs :=
      ((TensorProduct.equivFinsuppOfBasisLeft bV).symm_apply_apply u).symm
    -- c is defined as lid (map φ ψ u); compute by rewriting u
    show TensorProduct.lid k k (TensorProduct.map (bV.coord i₀) (bW.coord j₀) u) = _
    rw [hu_decomp, TensorProduct.equivFinsuppOfBasisLeft_symm_apply]
    -- Distribute linear maps over the Finsupp sum
    rw [Finsupp.sum]
    simp only [map_sum, TensorProduct.map_tmul, TensorProduct.lid_tmul,
      Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
    -- The sum collapses to the i₀ term
    rw [Finset.sum_eq_single i₀]
    · simp [hw₀_def]
    · intro i _ hi; simp [hi]
    · intro h; exact absurd (Finsupp.mem_support_iff.mpr hi₀) h
  -- Since c ≠ 0 and c • (v ⊗ w) ∈ U, deduce v ⊗ w ∈ U
  have := U.smul_mem c⁻¹ h_mem
  rwa [inv_smul_smul₀ hc_ne] at this

end Part1

open TensorProduct in
/-- The tensor product of irreducible representations is irreducible over the tensor
product of algebras: the only k-submodules of V ⊗ W closed under the action
(a ⊗ b) • (v ⊗ w) = (a • v) ⊗ (b • w) for all a ∈ A, b ∈ B are {0} and V ⊗ W.
Etingof Theorem 3.10.2(i).

Proof: By the density theorem, A → End_k(V) and B → End_k(W) are surjective.
So U is stable under TensorProduct.map f g for all f ∈ End(V), g ∈ End(W).
Pick nonzero u ∈ U, decompose using a basis of V, and use a rank-1 projection
to extract a nonzero pure tensor. Then the A- and B-actions generate all of V ⊗ W. -/
theorem Etingof.tensor_product_irreducible (k : Type*) (A B V W : Type*)
    [Field k] [IsAlgClosed k]
    [Ring A] [Algebra k A] [FiniteDimensional k A]
    [Ring B] [Algebra k B] [FiniteDimensional k B]
    [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
    [AddCommGroup W] [Module k W] [Module B W] [IsScalarTower k B W]
    [FiniteDimensional k V] [FiniteDimensional k W]
    [IsSimpleModule A V] [IsSimpleModule B W] :
    ∀ (U : Submodule k (V ⊗[k] W)),
      (∀ (a : A) (b : B) (x : V ⊗[k] W), x ∈ U →
        TensorProduct.map ((Algebra.lsmul k k V : A →ₐ[k] Module.End k V) a)
          ((Algebra.lsmul k k W : B →ₐ[k] Module.End k W) b) x ∈ U) →
      U = ⊥ ∨ U = ⊤ := by
  intro U hU
  by_cases hbot : U = ⊥
  · exact Or.inl hbot
  · right
    obtain ⟨u, hu, hu_ne⟩ := U.ne_bot_iff.mp hbot
    -- Density theorem: A → End(V) and B → End(W) are surjective
    have hdens_A := Etingof.density_theorem_part1 k A V
    have hdens_B := Etingof.density_theorem_part1 k B W
    -- U is stable under TensorProduct.map f g for all f : End V, g : End W
    have hU_end : ∀ (f : Module.End k V) (g : Module.End k W) (x : V ⊗[k] W),
        x ∈ U → TensorProduct.map f g x ∈ U := by
      intro f g x hx
      obtain ⟨a, ha⟩ := hdens_A f
      obtain ⟨b, hb⟩ := hdens_B g
      rw [← ha, ← hb]
      exact hU a b x hx
    -- Every element is in U (since every pure tensor is)
    rw [eq_top_iff]
    intro x _
    -- x is in the span of pure tensors
    have := span_tmul_eq_top k V W
    rw [eq_top_iff] at this
    have hx := this (Submodule.mem_top : x ∈ ⊤)
    -- It suffices to show every pure tensor is in U
    refine Submodule.span_le.mpr ?_ hx
    intro t ht
    obtain ⟨v, w, rfl⟩ := ht
    exact pure_tensors_mem_of_stable U hU_end hu hu_ne v w

open TensorProduct in
/-- Every irreducible representation of A ⊗ B arises as V ⊗ W for unique irreducible
representations V of A and W of B. Specifically, given any finite-dimensional
k-vector space M with commuting A and B actions that is irreducible (no proper nonzero
invariant k-submodules), M ≅ V ⊗ W for some irreducible V of A and W of B.
Etingof Theorem 3.10.2(ii). -/
theorem Etingof.tensor_product_irreducible_classification (k : Type*) (A B M : Type*)
    [Field k] [IsAlgClosed k]
    [Ring A] [Algebra k A] [FiniteDimensional k A]
    [Ring B] [Algebra k B] [FiniteDimensional k B]
    [AddCommGroup M] [Module k M] [FiniteDimensional k M]
    [Module A M] [IsScalarTower k A M]
    [Module B M] [IsScalarTower k B M]
    [SMulCommClass A B M]
    (hM : ∀ (U : Submodule k M),
      (∀ (a : A) (x : M), x ∈ U → a • x ∈ U) →
      (∀ (b : B) (x : M), x ∈ U → b • x ∈ U) →
      U = ⊥ ∨ U = ⊤) :
    ∃ (V W : Type*) (_ : AddCommGroup V) (_ : Module k V) (_ : Module A V)
      (_ : IsScalarTower k A V) (_ : FiniteDimensional k V) (_ : IsSimpleModule A V)
      (_ : AddCommGroup W) (_ : Module k W) (_ : Module B W)
      (_ : IsScalarTower k B W) (_ : FiniteDimensional k W) (_ : IsSimpleModule B W),
      Nonempty (M ≃ₗ[k] V ⊗[k] W) := by
  sorry
