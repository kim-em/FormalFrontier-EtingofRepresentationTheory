import Mathlib
import EtingofRepresentationTheory.Chapter6.Definition6_1_4
import EtingofRepresentationTheory.Chapter6.Corollary6_8_4
import EtingofRepresentationTheory.Chapter6.Proposition6_6_5
import EtingofRepresentationTheory.Chapter6.Theorem6_5_2
import EtingofRepresentationTheory.Chapter6.InfiniteTypeConstructions

/-!
# Theorem (Problem 6.1.5): Finite Type iff Dynkin

A connected quiver Q is of finite type if and only if the corresponding unoriented
graph (i.e., with directions of arrows forgotten) is a Dynkin diagram
(see Theorem 6.5.2 / Gabriel's theorem).

## Mathlib correspondence

Gabriel's theorem is NOT in Mathlib. Quiver representations have basic support
(`Quiver`, `Representation`), but Gabriel's classification is absent.

## Formalization note

The statement uses `IsDynkinDiagram` (Definition 6.1.4) for the combinatorial
condition. `IsFiniteTypeQuiver` is defined in `FiniteTypeDefs.lean` using quiver
representation isomorphism and indecomposability, quantified over all orientations
and algebraically closed fields.
-/

open Etingof in
/-- A connected simple graph on n ≥ 1 vertices that is not graph-isomorphic to any
standard Dynkin type (A_n, D_n, E₆, E₇, E₈) has infinite representation type.

This is proved by case analysis on the graph structure:
- Graphs containing cycles → `cycle_not_finite_type` + subgraph transfer
- Trees with degree ≥ 4 → `tree_degree_ge_4_not_finite_type`
- Trees with ≥ 2 branch points of degree 3 → D̃₅ subgraph + `d5tilde_not_finite_type`
- T_{p,q,r} with p ≥ 2 → Ẽ₆ = T_{2,2,2} subgraph + `etilde6_not_finite_type`
- T_{1,q,r} with q ≥ 3 → Ẽ₇ type: extended Dynkin infinite type
- T_{1,2,r} with r ≥ 5 → Ẽ₈ type: extended Dynkin infinite type -/
private theorem not_ade_not_finite_type {n : ℕ} (adj : Matrix (Fin n) (Fin n) ℤ)
    (hn : 1 ≤ n)
    (hsymm : adj.IsSymm)
    (hdiag : ∀ i, adj i i = 0)
    (h01 : ∀ i j, adj i j = 0 ∨ adj i j = 1)
    (hconn : ∀ i j : Fin n, ∃ path : List (Fin n),
      path.head? = some i ∧ path.getLast? = some j ∧
      ∀ k, (h : k + 1 < path.length) →
        adj (path.get ⟨k, by omega⟩) (path.get ⟨k + 1, h⟩) = 1)
    (h_not_ade : ¬ ∃ t : DynkinType, ∃ σ : Fin t.rank ≃ Fin n,
      ∀ i j, adj (σ i) (σ j) = t.adj i j) :
    ¬ IsFiniteTypeQuiver n adj := by
  -- Non-ADE connected simple graphs contain forbidden subgraphs (cycles, extended
  -- Dynkin types) that have infinite representation type. The case analysis on
  -- graph structure (cycle vs tree, degree bounds, arm lengths) and the
  -- Ẽ₇/Ẽ₈ infinite type constructions are not yet formalized.
  -- See GitHub issues for the missing infrastructure.
  sorry

/-- Gabriel's theorem: a connected quiver (given by its symmetric adjacency matrix)
is of finite type (finitely many indecomposable representations up to isomorphism)
if and only if its underlying unoriented graph is a Dynkin diagram.
(Etingof Problem 6.1.5 / Theorem 6.5.2) -/
theorem Etingof.Theorem_6_1_5 (n : ℕ) (adj : Matrix (Fin n) (Fin n) ℤ)
    (hsymm : adj.IsSymm)
    (hdiag : ∀ i, adj i i = 0)
    (h01 : ∀ i j, adj i j = 0 ∨ adj i j = 1)
    (hconn : ∀ i j : Fin n, ∃ path : List (Fin n),
      path.head? = some i ∧ path.getLast? = some j ∧
      ∀ k, (h : k + 1 < path.length) →
        adj (path.get ⟨k, by omega⟩) (path.get ⟨k + 1, h⟩) = 1) :
    Etingof.IsFiniteTypeQuiver n adj ↔ Etingof.IsDynkinDiagram n adj := by
  constructor
  · -- Forward: finite type → Dynkin diagram
    intro hft
    refine ⟨hsymm, hdiag, h01, hconn, fun x hx => ?_⟩
    -- By contradiction: if B(x,x) ≤ 0, then the graph is not Dynkin, hence not ADE,
    -- hence has infinite representation type, contradicting finite type.
    by_contra h_not_pos
    push_neg at h_not_pos
    -- The other 4 conditions + ¬pos_def → ¬IsDynkinDiagram
    have h_not_dynkin : ¬ Etingof.IsDynkinDiagram n adj := by
      intro ⟨_, _, _, _, hpos⟩
      exact not_lt.mpr h_not_pos (hpos x hx)
    -- For n = 0: impossible (no nonzero x : Fin 0 → ℤ)
    by_cases hn : n = 0
    · subst hn; exact hx (funext (fun i => i.elim0))
    · -- For n ≥ 1: by Dynkin classification, not ADE
      have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
      have h_not_ade : ¬ ∃ t : Etingof.DynkinType, ∃ σ : Fin t.rank ≃ Fin n,
          ∀ i j, adj (σ i) (σ j) = t.adj i j := by
        intro hade
        exact h_not_dynkin ((Etingof.Theorem_Dynkin_classification n adj hn1).mpr hade)
      exact not_ade_not_finite_type adj hn1 hsymm hdiag h01 hconn h_not_ade hft
  · -- Backward: Dynkin diagram → finite type
    -- Every indecomposable has dim vector that is a positive root (Theorem 6.5.2b),
    -- and positive roots are finite (Theorem 6.5.2a).
    intro hDynkin k _inst_field _inst_algclosed Q _inst_ss hOrient
    -- Cast map from ℕ dim vectors to ℤ vectors
    set f : (Fin n → ℕ) → (Fin n → ℤ) := fun d i => ↑(d i)
    -- f is injective
    have hf_inj : Function.Injective f := by
      intro d₁ d₂ heq; ext i
      have := congr_fun heq i; simp only [f] at this; exact_mod_cast this
    -- The set of dim vectors of indecomposables maps into positive roots
    apply Set.Finite.subset
      ((Etingof.Theorem_6_5_2a_finiteness hDynkin).preimage (hf_inj.injOn))
    intro d ⟨V, hV_indec, hV_equiv⟩
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    -- Show f d is a positive root: nonneg, nonzero, B(f d, f d) = 2
    refine ⟨⟨?_, ?_⟩, fun i => Int.natCast_nonneg (d i)⟩
    · -- f d ≠ 0 (V is indecomposable → nontrivial at some vertex → d v ≥ 1)
      obtain ⟨⟨v, hv⟩, _⟩ := hV_indec
      intro heq
      have hv_zero : d v = 0 := by
        have h := congr_fun heq v
        change (d v : ℤ) = 0 at h
        exact_mod_cast h
      -- V.obj v ≃ₗ[k] (Fin 0 → k), so V.obj v is trivial, contradicting Nontrivial
      obtain ⟨e⟩ := hV_equiv v
      rw [hv_zero] at e
      haveI : Subsingleton (V.obj v) := e.toEquiv.injective.subsingleton
      exact not_nontrivial (V.obj v) hv
    · -- B(f d, f d) = 2: indecomposable dim vectors satisfy the Tits form condition.
      -- Derive Module.Free and Module.Finite from the linear equivs
      haveI : ∀ v, Module.Free k (V.obj v) := fun v =>
        Module.Free.of_equiv ((hV_equiv v).some.symm)
      haveI : ∀ v, Module.Finite k (V.obj v) := fun v =>
        Module.Finite.equiv ((hV_equiv v).some.symm)
      -- Bridge: show finrank equals d v via LinearEquiv
      have hdim : ∀ v, Module.finrank k (V.obj v) = d v := fun v => by
        rw [(hV_equiv v).some.finrank_eq, Module.finrank_fin_fun]
      -- Rewrite the goal to use finrank
      have : f d = fun v => (Module.finrank k (V.obj v) : ℤ) := by
        ext v; simp only [f]; rw [hdim v]
      rw [this]
      exact Etingof.indecomposable_bilinearForm_eq_two hDynkin hOrient V hV_indec

/-- Corollary: A connected simple graph that is not a Dynkin diagram has infinite
representation type. (Non-circular version, proved as corollary of Theorem_6_1_5.) -/
theorem Etingof.non_Dynkin_not_finite_type {n : ℕ} (adj : Matrix (Fin n) (Fin n) ℤ)
    (hsymm : adj.IsSymm)
    (hdiag : ∀ i, adj i i = 0)
    (h01 : ∀ i j, adj i j = 0 ∨ adj i j = 1)
    (hconn : ∀ i j : Fin n, ∃ path : List (Fin n),
      path.head? = some i ∧ path.getLast? = some j ∧
      ∀ k, (h : k + 1 < path.length) →
        adj (path.get ⟨k, by omega⟩) (path.get ⟨k + 1, h⟩) = 1)
    (h_not_dynkin : ¬ Etingof.IsDynkinDiagram n adj) :
    ¬ Etingof.IsFiniteTypeQuiver n adj := by
  intro hft
  exact h_not_dynkin ((Etingof.Theorem_6_1_5 n adj hsymm hdiag h01 hconn).mp hft)

/-- Corollary: A connected simple graph on n ≥ 1 vertices not isomorphic to any ADE type
has infinite representation type. -/
theorem Etingof.non_ADE_not_finite_type {n : ℕ} (adj : Matrix (Fin n) (Fin n) ℤ)
    (hn : 1 ≤ n)
    (hsymm : adj.IsSymm)
    (hdiag : ∀ i, adj i i = 0)
    (h01 : ∀ i j, adj i j = 0 ∨ adj i j = 1)
    (hconn : ∀ i j : Fin n, ∃ path : List (Fin n),
      path.head? = some i ∧ path.getLast? = some j ∧
      ∀ k, (h : k + 1 < path.length) →
        adj (path.get ⟨k, by omega⟩) (path.get ⟨k + 1, h⟩) = 1)
    (h_not_ade : ¬ ∃ t : Etingof.DynkinType, ∃ σ : Fin t.rank ≃ Fin n,
      ∀ i j, adj (σ i) (σ j) = t.adj i j) :
    ¬ Etingof.IsFiniteTypeQuiver n adj := by
  apply Etingof.non_Dynkin_not_finite_type adj hsymm hdiag h01 hconn
  intro hD
  exact h_not_ade ((Etingof.Theorem_Dynkin_classification n adj hn).mp hD)
