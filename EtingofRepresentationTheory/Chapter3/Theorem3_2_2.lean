import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RepresentationTheory.AlgebraRepresentation.Basic

/-!
# Theorem 3.2.2: The Density Theorem

(i) Let V be an irreducible finite dimensional representation of A over an algebraically
closed field k. Then the map ρ : A → End V is surjective.

(ii) Let V = V₁ ⊕ ⋯ ⊕ Vᵣ, where Vᵢ are irreducible pairwise nonisomorphic finite
dimensional representations of A. Then the map ⊕ᵢ ρᵢ : A → ⊕ᵢ End(Vᵢ) is surjective.
-/

open Module in
/-- The density theorem, part (i): For an irreducible finite dimensional representation
over an algebraically closed field, the representation map A → End(V) is surjective.
Etingof Theorem 3.2.2(i). -/
theorem Etingof.density_theorem_part1 (k : Type*) (A : Type*) (V : Type*)
    [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
    [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
    [FiniteDimensional k V] [IsSimpleModule A V] :
    Function.Surjective (Algebra.lsmul k k V : A →ₐ[k] End k V) := by
  intro f
  -- By Schur's lemma over algebraically closed k, End_A(V) ≅ k
  have hbij := IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed (A := A) (V := V) k
  -- Every k-linear endomorphism is End_A(V)-linear since End_A(V) = k
  have g_smul : ∀ (c : End A V) (v : V), f (c • v) = c • f v := by
    intro c v
    obtain ⟨t, ht⟩ := hbij.2 c
    have hc : ∀ w, c w = t • w := fun w => by simp [← ht]
    simp only [End.smul_def, hc, map_smul]
  -- Lift f to an End_A(V)-linear endomorphism
  let g : End (End A V) V :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := g_smul }
  -- V is finite over End_A(V) since End_A(V) = k and V is finite-dimensional over k
  haveI : Module.Finite (End A V) V :=
    Module.Finite.of_restrictScalars_finite k (End A V) V
  -- Apply the Jacobson density theorem
  obtain ⟨a, ha⟩ := Module.Finite.toModuleEnd_moduleEnd_surjective (R := A) (M := V) g
  -- Both Algebra.lsmul and toModuleEnd send a to (v ↦ a • v)
  exact ⟨a, LinearMap.ext fun v => show a • v = f v from congr($(ha) v)⟩

/-- The density theorem, part (ii): For a direct sum of pairwise nonisomorphic irreducible
representations, the combined representation map is surjective.
Etingof Theorem 3.2.2(ii). -/
theorem Etingof.density_theorem_part2 (k : Type*) (A : Type*) (ι : Type*)
    [Field k] [IsAlgClosed k] [Ring A] [Algebra k A] [Fintype ι]
    (V : ι → Type*) [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
    [∀ i, Module A (V i)] [∀ i, IsScalarTower k A (V i)]
    [∀ i, FiniteDimensional k (V i)] [∀ i, IsSimpleModule A (V i)]
    (h_noniso : ∀ i j, i ≠ j → IsEmpty (V i ≃ₗ[A] V j)) :
    Function.Surjective
      (fun a i => (Algebra.lsmul k k (V i) : A →ₐ[k] Module.End k (V i)) a :
        A → ∀ i, Module.End k (V i)) := by
  classical
  intro f
  -- The product module ∏ V_i is semisimple (each V_i is simple, hence semisimple)
  haveI : IsSemisimpleModule A (∀ i, V i) :=
    IsSemisimpleModule.congr (DFinsupp.linearEquivFunOnFintype (R := A) (M := V)).symm
  -- ∏ V_i is finite over End_A(∏ V_i) via k
  haveI : Module.Finite (Module.End A (∀ i, V i)) (∀ i, V i) :=
    Module.Finite.of_restrictScalars_finite k _ _
  -- Off-diagonal vanishing: for i ≠ j, the A-linear map V_j → V_i via c is zero
  have off_diag : ∀ (c : Module.End A (∀ i, V i)) (i j : ι), i ≠ j →
      ∀ w : V j, (c (Pi.single j w)) i = 0 := by
    intro c i j hij w
    -- The composition proj_i ∘ c ∘ single_j : V_j →ₗ[A] V_i
    let φ : V j →ₗ[A] V i :=
      (LinearMap.proj i).comp (c.comp (LinearMap.single A _ j))
    -- By Schur: bijective or zero. If bijective, V_j ≅ V_i, contradicting non-isomorphism.
    rcases φ.bijective_or_eq_zero with hbij | hzero
    · exact ((h_noniso i j hij).false (LinearEquiv.ofBijective φ hbij).symm).elim
    · exact LinearMap.congr_fun hzero w
  -- Diagonal entries are scalars: proj_i ∘ c ∘ single_i ∈ End_A(V_i) = k
  have diag_scalar : ∀ (c : Module.End A (∀ i, V i)) (i : ι),
      ∃ t : k, ∀ w : V i, (c (Pi.single i w)) i = t • w := by
    intro c i
    let ψ : Module.End A (V i) :=
      (LinearMap.proj i).comp (c.comp (LinearMap.single A _ i))
    obtain ⟨t, ht⟩ := (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed (A := A)
      (V := V i) k).2 ψ
    exact ⟨t, fun w => show ψ w = t • w by simp [ψ, ← ht]⟩
  -- Consequence: c acts on component i as scalar multiplication
  have c_scalar : ∀ (c : Module.End A (∀ i, V i)) (v : ∀ i, V i) (i : ι),
      (c v) i = (diag_scalar c i).choose • (v i) := by
    intro c v i
    have hdecomp : v = ∑ j, Pi.single j (v j) := by ext j; simp
    conv_lhs => rw [hdecomp, map_sum]
    rw [Finset.sum_apply, Finset.sum_eq_single i]
    · exact (diag_scalar c i).choose_spec (v i)
    · intro j _ hji
      exact off_diag c i j (Ne.symm hji) (v j)
    · intro hi; exact absurd (Finset.mem_univ i) hi
  -- Construct g : End_{End_A(M)}(M) with g(v)(i) = f_i(v_i)
  let g : Module.End (Module.End A (∀ i, V i)) (∀ i, V i) :=
    { toFun := fun v i => f i (v i),
      map_add' := fun v w => funext fun i => map_add (f i) (v i) (w i),
      map_smul' := fun c v => by
        ext i
        change f i ((c v) i) = (c (fun j => f j (v j))) i
        rw [c_scalar c v i, map_smul, c_scalar c (fun j => f j (v j)) i] }
  -- Apply the Jacobson density theorem to get a : A with a • m = g(m) for all m
  obtain ⟨a, ha⟩ :=
    Module.Finite.toModuleEnd_moduleEnd_surjective (R := A) (M := ∀ i, V i) g
  -- Extract the result: for each i, ρ_i(a) = f_i
  refine ⟨a, funext fun i => LinearMap.ext fun v => ?_⟩
  -- ha : Module.toModuleEnd ... a = g, means a • m = g m for all m
  -- Specialize to m = Pi.single i v and evaluate at component i
  -- ha says: Module.toModuleEnd ... a = g, i.e., a • m = g m for all m
  -- We need: (Algebra.lsmul k k (V i)) a v = f i v, i.e., a • v = f i v
  change a • v = f i v
  have h := congr_fun (LinearMap.congr_fun ha (Pi.single i v)) i
  have lhs : (Module.toModuleEnd (Module.End A (∀ i, V i)) (∀ i, V i) a
    (Pi.single i v)) i = a • v := by
    change a • (Pi.single i v : ∀ i, V i) i = a • v
    simp
  have rhs : g (Pi.single i v) i = f i v := by
    change f i ((Pi.single i v : ∀ i, V i) i) = f i v
    simp
  rw [lhs, rhs] at h
  exact h
