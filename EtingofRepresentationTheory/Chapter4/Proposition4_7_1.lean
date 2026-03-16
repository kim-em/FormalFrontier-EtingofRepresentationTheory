import Mathlib

/-!
# Proposition 4.7.1: Orthogonality of Matrix Elements

Let V, W be nonisomorphic irreducible representations of G with orthonormal bases.
Define matrix elements t^V_{ij}(g) = ⟨v_i, ρ_V(g) v_j⟩.

(i) Matrix elements of nonisomorphic irreducible representations are orthogonal:
  (t^V_{ij}, t^W_{kl}) = 0 for V ≇ W.

(ii) (t^V_{ij}, t^V_{i'j'}) = δ_{ii'} δ_{jj'} / dim(V).

In particular, the matrix elements of all irreducible representations form an orthogonal
basis of the space of functions F(G, ℂ) (Peter–Weyl for finite groups).

## Mathlib correspondence

This extends the character orthogonality (Theorem 4.5.1) to matrix elements.
Not directly in Mathlib.
-/

open FDRep CategoryTheory Representation

universe u

section SchurAverage

variable {k G : Type u} [Field k] [Group G] [Fintype G]
  [Invertible (Fintype.card G : k)]

/-- The averaged map T_f = ⅟|G| • Σ_g ρ_V(g) ∘ f ∘ ρ_W(g⁻¹) for a linear map f : W → V.
This is the projection of f into the space of G-equivariant maps Hom_G(W, V). -/
noncomputable def averagedLinHom (V W : FDRep k G) (f : (↑W : Type u) →ₗ[k] ↑V) :
    (↑W : Type u) →ₗ[k] ↑V :=
  ⅟(Fintype.card G : k) • ∑ g : G, (V.ρ g).comp (f.comp (W.ρ g⁻¹))

/-- averagedLinHom equals the averageMap on the linHom representation. -/
theorem averagedLinHom_eq_averageMap (V W : FDRep k G) (f : (↑W : Type u) →ₗ[k] ↑V) :
    averagedLinHom V W f = Representation.averageMap (Representation.linHom W.ρ V.ρ) f := by
  simp only [averagedLinHom, Representation.averageMap, GroupAlgebra.average,
    map_smul, map_sum]
  congr 1; ext g : 1
  simp [Representation.linHom_apply]

/-- The averaged map lies in the invariant subspace. -/
theorem averagedLinHom_mem_invariants (V W : FDRep k G)
    (f : (↑W : Type u) →ₗ[k] ↑V) :
    averagedLinHom V W f ∈ (Representation.linHom W.ρ V.ρ).invariants := by
  rw [averagedLinHom_eq_averageMap]
  exact Representation.averageMap_invariant _ _

/-- For non-isomorphic simple representations, the averaged map is zero. -/
theorem averagedLinHom_eq_zero [IsAlgClosed k]
    (V W : FDRep k G) [Simple V] [Simple W]
    (hVW : IsEmpty (V ≅ W))
    (f : (↑W : Type u) →ₗ[k] ↑V) :
    averagedLinHom V W f = 0 := by
  have hmem := averagedLinHom_mem_invariants V W f
  have hbot : (Representation.linHom W.ρ V.ρ).invariants = ⊥ := by
    rw [← Submodule.finrank_eq_zero]
    rw [LinearEquiv.finrank_eq
      (Representation.linHom.invariantsEquivFDRepHom W V)]
    exact CategoryTheory.finrank_hom_simple_simple_eq_zero_of_not_iso k
      fun i => hVW.false i.symm
  rw [hbot] at hmem
  exact hmem

/-- The sum ⅟|G| • Σ_g (M_V(g))_{ij} * (M_W(g⁻¹))_{pq} equals the (i,q) entry of
the averaged map T with the elementary map f sending basis vector p to basis vector j. -/
private theorem sum_eq_averagedLinHom_entry
    (V W : FDRep k G)
    {nV nW : ℕ}
    (bV : Module.Basis (Fin nV) k ↑V) (bW : Module.Basis (Fin nW) k ↑W)
    (i j : Fin nV) (p q : Fin nW) :
    ⅟(Fintype.card G : k) • ∑ g : G,
      (LinearMap.toMatrix bV bV (V.ρ g)) i j *
      (LinearMap.toMatrix bW bW (W.ρ g⁻¹)) p q =
    (bV.repr (averagedLinHom V W ((bW.coord p).smulRight (bV j)) (bW q))) i := by
  set f : (↑W : Type u) →ₗ[k] (↑V : Type u) := (bW.coord p).smulRight (bV j)
  simp_rw [LinearMap.toMatrix_apply]
  have step : ∀ g : G,
      (bV.repr (V.ρ g (bV j))) i * (bW.repr (W.ρ g⁻¹ (bW q))) p =
      (bV.repr ((V.ρ g).comp (f.comp (W.ρ g⁻¹)) (bW q))) i := by
    intro g
    simp [f, LinearMap.smulRight_apply, Module.Basis.coord_apply,
      LinearMap.comp_apply, map_smul, mul_comm]
  simp_rw [step]
  symm
  simp only [averagedLinHom, LinearMap.smul_apply, LinearMap.sum_apply,
    LinearMap.comp_apply, map_smul, map_sum, Finsupp.smul_apply,
    Finsupp.finset_sum_apply]

end SchurAverage

/-- Matrix element orthogonality, part (i): for nonisomorphic irreducible representations
V, W, the inner product of any pair of matrix coefficients is zero.
(1/|G|) Σ_g (ρ_V(g))_{ij} (ρ_W(g⁻¹))_{pq} = 0 when V ≇ W.
(Etingof Proposition 4.7.1(i)) -/
theorem Etingof.Proposition4_7_1_i
    {k G : Type u} [Field k] [IsAlgClosed k] [Group G] [Fintype G]
    [Invertible (Fintype.card G : k)]
    (V W : FDRep k G) [Simple V] [Simple W]
    (hVW : IsEmpty (V ≅ W))
    {nV nW : ℕ}
    (bV : Module.Basis (Fin nV) k V) (bW : Module.Basis (Fin nW) k W)
    (i j : Fin nV) (p q : Fin nW) :
    ⅟(Fintype.card G : k) • ∑ g : G,
      (LinearMap.toMatrix bV bV (V.ρ g)) i j *
      (LinearMap.toMatrix bW bW (W.ρ g⁻¹)) p q = 0 := by
  rw [sum_eq_averagedLinHom_entry V W bV bW i j p q]
  rw [averagedLinHom_eq_zero V W hVW]
  simp

/-- Matrix element orthogonality, part (ii): for an irreducible representation V,
(1/|G|) Σ_g (ρ(g))_{ij} (ρ(g⁻¹))_{pq} = δ_{iq} δ_{jp} / dim(V).
(Etingof Proposition 4.7.1(ii)) -/
theorem Etingof.Proposition4_7_1_ii
    {k G : Type u} [Field k] [IsAlgClosed k] [Group G] [Fintype G]
    [Invertible (Fintype.card G : k)]
    (V : FDRep k G) [Simple V]
    [Invertible (Module.finrank k (↑V : Type u) : k)]
    {n : ℕ}
    (b : Module.Basis (Fin n) k V)
    (i j p q : Fin n) :
    ⅟(Fintype.card G : k) • ∑ g : G,
      (LinearMap.toMatrix b b (V.ρ g)) i j *
      (LinearMap.toMatrix b b (V.ρ g⁻¹)) p q =
    if i = q ∧ j = p then (⅟(Module.finrank k (↑V : Type u) : k) : k) else 0 := by
  set f : (↑V : Type u) →ₗ[k] (↑V : Type u) := (b.coord p).smulRight (b j)
  -- Step 1: Reduce to the averaged map entry
  rw [sum_eq_averagedLinHom_entry V V b b i j p q]
  -- Step 2: The invariant space of linHom V.ρ V.ρ is 1-dimensional
  have hmem := averagedLinHom_mem_invariants V V f
  have h1dim : Module.finrank k (Representation.linHom V.ρ V.ρ).invariants = 1 := by
    rw [LinearEquiv.finrank_eq (Representation.linHom.invariantsEquivFDRepHom V V)]
    exact CategoryTheory.finrank_endomorphism_simple_eq_one k V
  -- LinearMap.id is in invariants (it commutes with all ρ(g))
  have hid_mem : LinearMap.id ∈ (Representation.linHom V.ρ V.ρ).invariants := by
    intro g; ext v
    simp only [Representation.linHom_apply, LinearMap.comp_apply, LinearMap.id_apply]
    change (V.ρ g * V.ρ g⁻¹) v = v
    rw [← map_mul, mul_inv_cancel, map_one]; rfl
  -- id ≠ 0 in the invariant space (since trace(id) = dim V ≠ 0)
  have hdim_ne : (Module.finrank k (↑V : Type u) : k) ≠ 0 :=
    isUnit_of_invertible _ |>.ne_zero
  have hid_ne : (⟨LinearMap.id, hid_mem⟩ : (Representation.linHom V.ρ V.ρ).invariants) ≠ 0 := by
    simp only [ne_eq, Subtype.ext_iff, Submodule.coe_zero]
    intro h
    have : (Module.finrank k (↑V : Type u) : k) = 0 := by
      rw [← LinearMap.trace_id (R := k) (M := (↑V : Type u)), h, map_zero]
    exact hdim_ne this
  -- Step 3: Every element of the 1-dim space is a scalar multiple of id
  obtain ⟨c, hc⟩ := ((finrank_eq_one_iff_of_nonzero'
    (⟨LinearMap.id, hid_mem⟩ : (Representation.linHom V.ρ V.ρ).invariants) hid_ne).mp h1dim)
    ⟨averagedLinHom V V f, hmem⟩
  -- hc : c • ⟨id, ...⟩ = ⟨averagedLinHom V V f, ...⟩
  have hT_eq : averagedLinHom V V f = c • LinearMap.id := by
    have := congr_arg Subtype.val hc
    simpa using this.symm
  -- Step 4: Compute c via trace
  -- First, trace(T) = trace(f) by cyclic property
  have htrace_T : LinearMap.trace k ↑V (averagedLinHom V V f) =
      LinearMap.trace k ↑V f := by
    simp only [averagedLinHom, map_smul, map_sum]
    have trace_conj : ∀ g : G,
        LinearMap.trace k ↑V ((V.ρ g).comp (f.comp (V.ρ g⁻¹))) =
        LinearMap.trace k ↑V f := by
      intro g
      have : (V.ρ g).comp (f.comp (V.ρ g⁻¹)) = V.ρ g * f * V.ρ g⁻¹ := rfl
      rw [this, LinearMap.trace_mul_cycle]
      rw [show V.ρ g⁻¹ * V.ρ g * f = f from by
        rw [← map_mul, inv_mul_cancel, map_one, one_mul]]
    simp_rw [trace_conj, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, smul_eq_mul, ← mul_assoc, invOf_mul_self, one_mul]
  -- trace(f) = δ_{jp} (trace of rank-1 map)
  have htrace_f : LinearMap.trace k ↑V f = if j = p then 1 else 0 := by
    simp only [f, LinearMap.trace_smulRight, Module.Basis.coord_apply,
      Module.Basis.repr_self, Finsupp.single_apply]
  -- trace(c • id) = c * dim(V) = trace(f) = δ_{jp}
  have hc_val : c = if j = p then ⅟(Module.finrank k (↑V : Type u) : k) else 0 := by
    have htr : (Module.finrank k (↑V : Type u) : k) * c =
        if j = p then 1 else 0 := by
      have : LinearMap.trace k ↑V (c • LinearMap.id) =
          if j = p then 1 else 0 := by
        rw [← hT_eq, htrace_T, htrace_f]
      rw [map_smul, LinearMap.trace_id, smul_eq_mul, mul_comm] at this
      exact this
    split_ifs with hjp
    · rw [if_pos hjp] at htr
      rw [eq_comm]
      exact invOf_eq_right_inv htr
    · rw [if_neg hjp] at htr
      exact (mul_eq_zero.mp htr).resolve_left hdim_ne
  -- Step 5: Extract the matrix entry
  rw [hT_eq]
  simp only [LinearMap.smul_apply, LinearMap.id_apply, map_smul,
    Finsupp.smul_apply, Module.Basis.repr_self, Finsupp.single_apply, hc_val]
  split_ifs <;> simp_all
