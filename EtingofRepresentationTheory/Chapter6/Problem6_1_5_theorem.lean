import Mathlib
import EtingofRepresentationTheory.Chapter6.Definition6_1_4
import EtingofRepresentationTheory.Chapter6.Corollary6_8_4
import EtingofRepresentationTheory.Chapter6.Proposition6_6_5
import EtingofRepresentationTheory.Chapter6.Theorem6_5_2

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
condition. `IsFiniteTypeQuiver` is defined using quiver representation isomorphism
and indecomposability, quantified over all orientations and algebraically closed fields.
-/

section QuiverRepresentationIso

variable {k : Type*} [Field k] {n : ℕ} {Q : Quiver (Fin n)}

/-- Two quiver representations are isomorphic if there exist linear isomorphisms at
each vertex that intertwine the edge maps. -/
def Etingof.QuiverRepresentation.AreIsomorphic
    (V W : @Etingof.QuiverRepresentation k (Fin n) _ Q) : Prop :=
  ∃ (e : ∀ v, V.obj v ≃ₗ[k] W.obj v),
    ∀ {a b : Fin n} (f : a ⟶ b),
      (e b).toLinearMap ∘ₗ V.mapLinear f = W.mapLinear f ∘ₗ (e a).toLinearMap

end QuiverRepresentationIso

/-- A quiver on n vertices (with underlying graph given by adjacency matrix adj) is of
**finite type** if for every algebraically closed field k and every orientation Q of
the graph, the set of dimension vectors supporting an indecomposable representation
is finite.

This is equivalent to there being only finitely many isomorphism classes of
indecomposable representations, since for finite type quivers each dimension vector
supports at most one indecomposable (up to isomorphism).
Uses `QuiverRepresentation.IsIndecomposable` from Proposition 6.6.5. -/
def Etingof.IsFiniteTypeQuiver (n : ℕ) (adj : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k]
    (Q : @Quiver.{0} (Fin n)), @Etingof.IsOrientationOf n Q adj →
      Set.Finite
        {d : Fin n → ℕ |
          ∃ (V : @Etingof.QuiverRepresentation k (Fin n) _ Q),
            V.IsIndecomposable ∧ ∀ v, V.obj v = (Fin (d v) → k)}

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
    -- We already have symmetry, diagonal, 0-1, and connectivity.
    -- Need positive definiteness: if B is not positive definite, then there are
    -- infinitely many positive roots, each giving an indecomposable (Problem 6.1.4).
    intro hft
    exact ⟨hsymm, hdiag, h01, hconn, fun x hx => by
      -- Contrapositive: if ∃ nonzero x with B(x,x) ≤ 0, produce infinitely many
      -- indecomposables. This requires Problem 6.1.4 infrastructure (not yet formalized).
      sorry⟩
  · -- Backward: Dynkin diagram → finite type
    -- Every indecomposable has dim vector that is a positive root (Theorem 6.5.2b),
    -- and positive roots are finite (Theorem 6.5.2a).
    intro hDynkin k _inst_field _inst_algclosed Q hOrient
    -- Cast map from ℕ dim vectors to ℤ vectors
    set f : (Fin n → ℕ) → (Fin n → ℤ) := fun d i => ↑(d i)
    -- f is injective
    have hf_inj : Function.Injective f := by
      intro d₁ d₂ heq; ext i
      have := congr_fun heq i; simp only [f] at this; exact_mod_cast this
    -- The set of dim vectors of indecomposables maps into positive roots
    apply Set.Finite.subset
      ((Etingof.Theorem_6_5_2a_finiteness hDynkin).preimage (hf_inj.injOn))
    intro d ⟨V, hV_indec, hV_type⟩
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
      rw [hV_type v] at hv
      exact not_nontrivial (Fin 0 → k) (by rw [hv_zero] at hv; exact hv)
    · -- B(f d, f d) = 2: indecomposable dim vectors satisfy the Tits form condition.
      -- This connects the type-equality formulation (V.obj v = Fin (d v) → k) to
      -- the Module.finrank formulation used by indecomposable_bilinearForm_eq_two.
      -- Requires deriving Module.Free/Finite from the type equality and showing
      -- Module.finrank k (V.obj v) = d v.
      sorry
