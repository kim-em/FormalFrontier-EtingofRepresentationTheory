import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import EtingofRepresentationTheory.Chapter3.Theorem3_2_2

/-!
# Theorem 3.6.2: Linear Independence of Characters

(i) Characters of (distinct) irreducible finite dimensional representations of A are
    linearly independent.

(ii) If A is a finite dimensional semisimple algebra, then these characters form a basis
     of (A/[A,A])*.

The proof of (i) uses the density theorem: the surjectivity of the combined representation
map ensures that traces of distinct irreducibles can be independently varied.

The proof of (ii) shows that [Mat_d(k), Mat_d(k)] = sl_d(k) (traceless matrices),
so A/[A,A] ≅ k^r for semisimple A = ⊕ Mat_{dᵢ}(k), and r linearly independent
characters on an r-dimensional space form a basis.
-/

open Module in
/-- The character of a finite-dimensional module V over a k-algebra A, defined as
the trace of the action map: χ_V(a) = tr(ρ_V(a)). -/
noncomputable def Etingof.character (k : Type*) (A : Type*) (V : Type*)
    [CommRing k] [Ring A] [Algebra k A]
    [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
    [Free k V] [Module.Finite k V] :
    Dual k A :=
  (LinearMap.trace k V).comp (Algebra.lsmul k k V : A →ₐ[k] End k V).toLinearMap

open Module in
/-- Characters of distinct irreducible representations are linearly independent.
Etingof Theorem 3.6.2(i). -/
theorem Etingof.characters_linearly_independent (k : Type*) (A : Type*)
    [Field k] [IsAlgClosed k] [Ring A] [Algebra k A] [FiniteDimensional k A]
    {ι : Type*} [Fintype ι]
    (V : ι → Type*) [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
    [∀ i, Module A (V i)] [∀ i, IsScalarTower k A (V i)]
    [∀ i, FiniteDimensional k (V i)] [∀ i, IsSimpleModule A (V i)]
    (h_noniso : ∀ i j, i ≠ j → IsEmpty (V i ≃ₗ[A] V j)) :
    LinearIndependent k (fun i => Etingof.character k A (V i)) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have hga : ∀ a : A, ∑ j, g j * Etingof.character k A (V j) a = 0 := by
    intro a
    have := LinearMap.congr_fun hg a
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, LinearMap.zero_apply] at this
    exact this
  have hsurj := Etingof.density_theorem_part2 k A ι V h_noniso
  classical
  haveI : Nontrivial (V i) := IsSimpleModule.nontrivial A (V i)
  let b := Module.Free.chooseBasis k (V i)
  have hne_idx : Nonempty (Module.Free.ChooseBasisIndex k (V i)) := by
    rw [← not_isEmpty_iff]
    intro h
    have : finrank k (V i) = 0 := by simp [finrank_eq_card_chooseBasisIndex, Fintype.card_eq_zero]
    have : 0 < finrank k (V i) := Module.finrank_pos
    omega
  let idx := hne_idx.some
  let target : ∀ j, Module.End k (V j) := fun j =>
    if h : j = i then h ▸ (dualTensorHom k (V i) (V i) (b.coord idx ⊗ₜ[k] b idx)) else 0
  obtain ⟨a, ha⟩ := hsurj target
  have h0 := hga a
  have hρ : ∀ j, (Algebra.lsmul k k (V j) : A →ₐ[k] Module.End k (V j)) a = target j := by
    intro j; exact congr_fun ha j
  simp only [Etingof.character, LinearMap.comp_apply, AlgHom.toLinearMap_apply] at h0
  have htarget_ne : ∀ j, j ≠ i → target j = 0 := by
    intro j hj; simp [target, hj]
  have htarget_eq : target i = dualTensorHom k (V i) (V i) (b.coord idx ⊗ₜ[k] b idx) := by
    simp [target]
  have htr_target_i : LinearMap.trace k (V i) (target i) = 1 := by
    rw [htarget_eq, LinearMap.trace_eq_contract_apply]
    simp [contractLeft, Basis.coord]
  have htr_ne : ∀ j, j ≠ i → LinearMap.trace k (V j) (target j) = 0 := by
    intro j hj; rw [htarget_ne j hj, map_zero]
  have hsum : ∑ j, g j * LinearMap.trace k (V j) (target j) =
      g i * LinearMap.trace k (V i) (target i) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    rw [Finset.sum_eq_zero (fun j hj => by rw [htr_ne j (Finset.ne_of_mem_erase hj), mul_zero])]
    ring
  have h0' : ∑ j, g j * LinearMap.trace k (V j) (target j) = 0 := by
    have : ∀ j, LinearMap.trace k (V j) ((Algebra.lsmul k k (V j) : A →ₐ[k] _) a) =
        LinearMap.trace k (V j) (target j) := fun j => congrArg _ (hρ j)
    simp only [this] at h0; exact h0
  rw [hsum, htr_target_i, mul_one] at h0'
  exact h0'

/-! ### Helper lemmas for Theorem 3.6.2(ii) -/

section helpers

open Module

/-- A tracial linear functional on End(V) (satisfying g(xy) = g(yx)) is a scalar multiple
of the trace. Proof: off-diagonal matrix units have zero value under tracial functionals,
and all diagonal entries are equal (matrix unit argument). -/
private lemma tracial_of_end_eq_scalar_trace {k V : Type*}
    [Field k] [AddCommGroup V] [Module k V] [Free k V] [Module.Finite k V]
    (g : End k V →ₗ[k] k) (hg : ∀ x y : End k V, g (x * y) = g (y * x)) :
    ∃ c : k, g = c • LinearMap.trace k V := by
  sorry

/-- For semisimple A with complete set of irreducibles, the combined representation map
A → ∏ End(Vᵢ) is injective. The kernel annihilates every simple module, hence every
submodule of the semisimple left regular representation, hence is zero. -/
private lemma rep_map_injective_of_semisimple {k : Type*} {A : Type*}
    [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]
    [IsSemisimpleRing A]
    {ι : Type*} [Fintype ι]
    (V : ι → Type*) [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
    [∀ i, Module A (V i)] [∀ i, IsScalarTower k A (V i)]
    [∀ i, FiniteDimensional k (V i)] [∀ i, IsSimpleModule A (V i)]
    (h_complete : ∀ (W : Type*) [AddCommGroup W] [Module k W] [Module A W]
      [IsScalarTower k A W] [FiniteDimensional k W] [IsSimpleModule A W],
      ∃ i, Nonempty (W ≃ₗ[A] V i)) :
    Function.Injective
      (fun a i => (Algebra.lsmul k k (V i) : A →ₐ[k] End k (V i)) a :
        A → ∀ i, End k (V i)) := by
  intro a₁ a₂ h
  by_contra hne
  have hb : a₁ - a₂ ≠ 0 := sub_ne_zero.mpr hne
  set b := a₁ - a₂ with hb_def
  -- b acts as zero on each V_i
  have hb_act : ∀ i (v : V i), b • v = 0 := by
    intro i v
    have hi := congr_fun h i  -- ρᵢ(a₁) = ρᵢ(a₂)
    have hv := LinearMap.congr_fun hi v  -- a₁ • v = a₂ • v
    show (a₁ - a₂) • v = 0
    rw [sub_smul]
    exact sub_eq_zero.mpr hv
  -- The left ideal A·b is nonzero (since 1 * b = b ≠ 0)
  -- A is semisimple ⟹ A·b contains a simple submodule S
  -- S ≅ V_j for some j (by h_complete)
  -- b acts on S by left multiplication: for s ∈ S, b • s = b * s
  -- Through S ≅ V_j, b acts as 0 ⟹ b * s = 0 for all s ∈ S
  -- In particular, Ab is in the kernel of left multiplication by b
  -- Repeating: every simple submodule of A is annihilated by b
  -- Since sSup{simples} = ⊤ (semisimple), b * x = 0 for all x ∈ A
  -- Taking x = 1: b = 0, contradiction
  sorry

end helpers

open Module in
/-- For a semisimple algebra, characters of irreducibles span the space of tracial
linear functionals (those f with f(ab) = f(ba)), hence form a basis of (A/[A,A])*.
Combined with part (i), this gives a basis.
Etingof Theorem 3.6.2(ii). -/
theorem Etingof.characters_basis_semisimple (k : Type*) (A : Type*)
    [Field k] [IsAlgClosed k] [Ring A] [Algebra k A] [FiniteDimensional k A]
    [IsSemisimpleRing A]
    {ι : Type*} [Fintype ι]
    (V : ι → Type*) [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
    [∀ i, Module A (V i)] [∀ i, IsScalarTower k A (V i)]
    [∀ i, FiniteDimensional k (V i)] [∀ i, IsSimpleModule A (V i)]
    (h_noniso : ∀ i j, i ≠ j → IsEmpty (V i ≃ₗ[A] V j))
    (h_complete : ∀ (W : Type*) [AddCommGroup W] [Module k W] [Module A W]
      [IsScalarTower k A W] [FiniteDimensional k W] [IsSimpleModule A W],
      ∃ i, Nonempty (W ≃ₗ[A] V i)) :
    ∀ f : Dual k A, (∀ a b : A, f (a * b) = f (b * a)) →
      f ∈ Submodule.span k (Set.range (fun i => Etingof.character k A (V i))) := by
  intro f hf
  classical
  -- The representation map ρ : A → ∏ End(Vᵢ) is bijective
  have hρ_surj := Etingof.density_theorem_part2 k A ι V h_noniso
  have hρ_inj := rep_map_injective_of_semisimple V h_complete
  let ρ : A →ₗ[k] ∀ i, Module.End k (V i) :=
    { toFun := fun a i => (Algebra.lsmul k k (V i) : A →ₐ[k] _) a,
      map_add' := fun a b => funext fun i => map_add _ a b,
      map_smul' := fun c a => funext fun i => map_smul _ c a }
  let ρ_equiv : A ≃ₗ[k] (∀ i, Module.End k (V i)) := LinearEquiv.ofBijective ρ ⟨hρ_inj, hρ_surj⟩
  -- Transfer f to ∏ End(Vᵢ) via ρ⁻¹
  let g : (∀ i, Module.End k (V i)) →ₗ[k] k := f.comp ρ_equiv.symm.toLinearMap
  -- ρ preserves multiplication (it's an algebra homomorphism componentwise)
  have hρ_mul : ∀ a b : A, ρ (a * b) = ρ a * ρ b :=
    fun a b => funext fun i => map_mul (Algebra.lsmul k k (V i) : A →ₐ[k] _) a b
  -- ρ⁻¹ also preserves multiplication
  have hρ_symm_mul : ∀ x y, ρ_equiv.symm (x * y) = ρ_equiv.symm x * ρ_equiv.symm y := by
    intro x y
    apply ρ_equiv.injective
    rw [LinearEquiv.apply_symm_apply]
    show x * y = ρ_equiv (ρ_equiv.symm x * ρ_equiv.symm y)
    change x * y = ρ (ρ_equiv.symm x * ρ_equiv.symm y)
    rw [hρ_mul]
    show x * y = ρ (ρ_equiv.symm x) * ρ (ρ_equiv.symm y)
    change x * y = ρ_equiv (ρ_equiv.symm x) * ρ_equiv (ρ_equiv.symm y)
    simp [LinearEquiv.apply_symm_apply]
  -- g is tracial
  have hg_tracial : ∀ (x y : ∀ i, Module.End k (V i)), g (x * y) = g (y * x) := by
    intro x y
    show f (ρ_equiv.symm (x * y)) = f (ρ_equiv.symm (y * x))
    rw [hρ_symm_mul, hρ_symm_mul, hf]
  -- Per-component functionals gᵢ
  let g_comp : ∀ i, Module.End k (V i) →ₗ[k] k := fun i =>
    g.comp (LinearMap.single (R := k) (fun i => Module.End k (V i)) i)
  -- Each gᵢ is tracial
  have hg_comp_tr : ∀ i (x y : Module.End k (V i)),
      g_comp i (x * y) = g_comp i (y * x) := by
    intro i x y
    show g (Pi.single i (x * y)) = g (Pi.single i (y * x))
    have hpi_mul : ∀ (a b : Module.End k (V i)),
        (Pi.single i a : ∀ j, Module.End k (V j)) * Pi.single i b = Pi.single i (a * b) := by
      intro a b; ext j
      simp only [Pi.mul_apply, Pi.single_apply]
      by_cases hj : j = i
      · subst hj; simp
      · simp [hj, zero_mul]
    rw [← hpi_mul, ← hpi_mul, hg_tracial]
  -- By the matrix unit argument, each gᵢ = cᵢ • trace
  choose c hc using fun i => tracial_of_end_eq_scalar_trace (g_comp i) (hg_comp_tr i)
  -- f = ∑ cᵢ χᵢ, so f ∈ span{χᵢ}
  rw [Submodule.mem_span_range_iff_exists_fun]
  refine ⟨c, ?_⟩
  ext a
  -- f(a) = g(ρ(a)) since g = f ∘ ρ⁻¹
  have hfa : f a = g (ρ a) := by
    show f a = f (ρ_equiv.symm (ρ_equiv a))
    simp
  -- g(e) = ∑ gᵢ(eᵢ) by decomposing e into Pi.single components
  have hg_sum : ∀ (e : ∀ i, Module.End k (V i)), g e = ∑ i, g_comp i (e i) := by
    intro e
    have : e = ∑ i : ι, Pi.single i (e i) := by
      ext j; simp [Finset.sum_apply, Pi.single_apply, Finset.sum_ite_eq']
    conv_lhs => rw [this]
    simp [map_sum, g_comp]
  -- Combine: f(a) = ∑ cᵢ tr(ρᵢ(a)) = ∑ cᵢ χᵢ(a)
  -- Goal: f a = (∑ i, c i • character k A (V i)) a
  -- RHS: ∑ i, (c i • character k A (V i)) a = ∑ i, c i * character(a)
  rw [hfa, hg_sum]
  -- Goal: (∑ i, c i • character k A (V i)) a = ∑ i, g_comp i (ρ a i)
  simp only [LinearMap.coeFn_sum, Finset.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Etingof.character, LinearMap.comp_apply, AlgHom.toLinearMap_apply]
  rw [hc i]
  rfl
