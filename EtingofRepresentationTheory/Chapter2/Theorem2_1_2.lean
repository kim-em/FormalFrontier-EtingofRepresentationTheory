import EtingofRepresentationTheory.Chapter2.Definition2_8_3
import EtingofRepresentationTheory.Chapter2.Definition2_8_10
import EtingofRepresentationTheory.Chapter6.Definition6_1_4
import EtingofRepresentationTheory.Chapter6.Definition6_4_7
import EtingofRepresentationTheory.Chapter6.Proposition6_6_5
import EtingofRepresentationTheory.Chapter6.Problem6_1_5_theorem
import EtingofRepresentationTheory.Chapter6.Theorem6_5_2
import EtingofRepresentationTheory.Chapter6.CoxeterInfrastructure

/-!
# Theorem 2.1.2: Gabriel's Theorem

The finite type property of a quiver Q does not depend on the orientation of edges.
The connected graphs that yield quivers of finite type are given by the Dynkin diagrams:
A_n, D_n, E_6, E_7, E_8.

## Mathlib correspondence

Gap — Gabriel's theorem is not in Mathlib. Only basic quiver infrastructure exists.

## Formalization note

Gabriel's theorem is a deep classification result connecting quiver representations to
Dynkin diagrams. It requires significant infrastructure (root systems, reflection functors,
positive definite quadratic forms on graphs). The statement is formalized; the proof
decomposes into focused sub-sorries bridging the Chapter 2 and Chapter 6 formalizations.

We formalize the key supporting concepts:
- `QuiverRepresentationEquiv`: isomorphism of quiver representations
- `HasFiniteRepresentationType`: finitely many iso classes of f.d. indecomposable reps
- `quiverUndirectedAdj`: the underlying undirected adjacency matrix of a quiver

`QuiverRepresentation.IsIndecomposable` is defined in `Proposition6_6_5.lean`.
-/

namespace Etingof

/-! ## Supporting definitions for Gabriel's theorem -/

/-- An equivalence (isomorphism) of quiver representations: a family of linear equivalences
at each vertex that commute with the arrow maps. -/
structure QuiverRepresentationEquiv (k : Type*) (Q : Type*) [CommSemiring k] [Quiver Q]
    (ρ₁ ρ₂ : QuiverRepresentation k Q) where
  /-- A linear equivalence at each vertex -/
  equivAt : ∀ v, ρ₁.obj v ≃ₗ[k] ρ₂.obj v
  /-- The equivalences commute with the arrow maps -/
  commutes : ∀ {v w : Q} (e : v ⟶ w) (x : ρ₁.obj v),
    equivAt w (ρ₁.mapLinear e x) = ρ₂.mapLinear e (equivAt v x)

/-- Quiver representation with all universes pinned to 0 (the natural setting for
finite-dimensional representations over a concrete field on a finite vertex set). -/
abbrev FinQuiverRep (k : Type) [CommSemiring k] (n : ℕ) [Quiver.{0} (Fin n)] :=
  QuiverRepresentation.{0, 0, 0, 0} k (Fin n)

/-- A quiver on `Fin n` over a field k has **finite representation type** if there exist
finitely many finite-dimensional indecomposable representations such that every
finite-dimensional indecomposable representation is isomorphic to one of them. -/
def HasFiniteRepresentationType (k : Type) [Field k] (n : ℕ)
    [Quiver.{0} (Fin n)] : Prop :=
  ∃ (m : ℕ) (reps : Fin m → FinQuiverRep k n),
    -- Each representative is finite-dimensional
    (∀ i, ∀ v, Module.Finite k ((reps i).obj v)) ∧
    -- Each representative is indecomposable
    (∀ i, (reps i).IsIndecomposable) ∧
    -- Every f.d. indecomposable rep is isomorphic to some representative
    (∀ (ρ : FinQuiverRep k n),
      (∀ v, Module.Finite k (ρ.obj v)) →
      ρ.IsIndecomposable →
      ∃ i, Nonempty (QuiverRepresentationEquiv k (Fin n) ρ (reps i)))

/-- The underlying undirected adjacency matrix of a quiver on `Fin n`.
For distinct vertices i ≠ j, the entry is 1 if there exists an arrow between them
in either direction, and 0 otherwise. Diagonal entries are 0. -/
noncomputable def quiverUndirectedAdj (n : ℕ) [Quiver.{0} (Fin n)]
    [∀ a b : Fin n, Decidable (Nonempty (a ⟶ b))] :
    Matrix (Fin n) (Fin n) ℤ :=
  fun i j => if i ≠ j ∧ (Nonempty (i ⟶ j) ∨ Nonempty (j ⟶ i)) then 1 else 0

/-- The underlying undirected graph of a quiver on `Fin n` is connected if for any two
vertices there exists a path of undirected adjacency edges between them. -/
def QuiverUndirectedConnected (n : ℕ) [Quiver.{0} (Fin n)]
    [∀ a b : Fin n, Decidable (Nonempty (a ⟶ b))] : Prop :=
  ∀ i j : Fin n, ∃ path : List (Fin n),
    path.head? = some i ∧ path.getLast? = some j ∧
    ∀ k, (h : k + 1 < path.length) →
      (quiverUndirectedAdj n)
        (path.get ⟨k, by omega⟩) (path.get ⟨k + 1, h⟩) = 1

/-! ## Properties of quiverUndirectedAdj -/

variable {n : ℕ} [Quiver.{0} (Fin n)] [∀ a b : Fin n, Decidable (Nonempty (a ⟶ b))]

lemma quiverUndirectedAdj_symm : (quiverUndirectedAdj n).IsSymm := by
  ext i j
  simp only [quiverUndirectedAdj, Matrix.transpose_apply]
  by_cases hij : i = j
  · subst hij; simp
  · simp only [hij, Ne.symm hij, ne_eq, not_false_eq_true, true_and, Or.comm]

lemma quiverUndirectedAdj_diag (i : Fin n) : quiverUndirectedAdj n i i = 0 := by
  simp [quiverUndirectedAdj]

lemma quiverUndirectedAdj_01 (i j : Fin n) :
    quiverUndirectedAdj n i j = 0 ∨ quiverUndirectedAdj n i j = 1 := by
  simp only [quiverUndirectedAdj]
  split <;> simp

omit [∀ a b : Fin n, Decidable (Nonempty (a ⟶ b))] in
/-- `HasFiniteRepresentationType` implies the set of dimension vectors of indecomposable
representations (for this specific field k and quiver Q) is finite. -/
lemma HasFiniteRepresentationType.finite_dimVectors (k : Type) [Field k]
    (hfrt : HasFiniteRepresentationType k n) :
    Set.Finite
      {d : Fin n → ℕ |
        ∃ (V : FinQuiverRep k n),
          (∀ v, Module.Finite k (V.obj v)) ∧
          V.IsIndecomposable ∧ ∀ v, Nonempty (V.obj v ≃ₗ[k] (Fin (d v) → k))} := by
  obtain ⟨m, reps, hfin, hindec, hcover⟩ := hfrt
  apply Set.Finite.subset (Set.finite_range (fun i v => Module.finrank k ((reps i).obj v)))
  intro d ⟨V, hV_fin, hV_indec, hV_equiv⟩
  simp only [Set.mem_range]
  obtain ⟨i, ⟨e⟩⟩ := hcover V hV_fin hV_indec
  use i
  ext v
  have h1 : Module.finrank k (V.obj v) = d v := by
    haveI : Module.Free k (V.obj v) := Module.Free.of_equiv (hV_equiv v).some.symm
    rw [(hV_equiv v).some.finrank_eq, Module.finrank_fin_fun]
  have h2 : Module.finrank k (V.obj v) = Module.finrank k ((reps i).obj v) :=
    (e.equivAt v).finrank_eq
  linarith

/-! ## Bridge lemmas between Chapter 2 and Chapter 6 definitions -/

/-- Convert a `QuiverRepresentation.Iso` (Chapter 6) to a `QuiverRepresentationEquiv`
(Chapter 2). These are the same concept with different packaging. -/
noncomputable def QuiverRepresentation.Iso.toEquiv
    {k : Type*} [CommSemiring k] {Q : Quiver (Fin n)}
    {ρ₁ ρ₂ : QuiverRepresentation k (Fin n)}
    (f : QuiverRepresentation.Iso ρ₁ ρ₂) :
    QuiverRepresentationEquiv k (Fin n) ρ₁ ρ₂ where
  equivAt := f.equivAt
  commutes e x := f.naturality e x

/-- If the Tits form on the underlying graph is not positive definite, then for any
algebraically closed field k and the given quiver Q, there are infinitely many
non-isomorphic finite-dimensional indecomposable representations.

This is the per-field version of the infinite type result. The existing
`not_posdef_infinite_type` (Chapter 6) proves `¬IsFiniteTypeQuiver` which quantifies
over all fields/orientations. This lemma extracts the consequence for ONE specific
field and quiver, via the contrapositive of `finite_dimVectors`.

The proof requires showing that the infinite family constructions in Chapter 6
(cycle families, star graph families, extended Dynkin families) produce
indecomposable representations for any algebraically closed field k and any
orientation of the underlying graph. The constructions are uniform in k, but
the existing formalization wraps them as `¬IsFiniteTypeQuiver` (¬∀) rather than
the stronger `∀¬` statement needed here. -/
private lemma not_posdef_not_HasFiniteRepresentationType
    (k : Type) [Field k] [IsAlgClosed k]
    (n : ℕ) [Quiver.{0} (Fin n)] [∀ a b : Fin n, Decidable (Nonempty (a ⟶ b))]
    [∀ a b : Fin n, Subsingleton (a ⟶ b)]
    (hOrient : IsOrientationOf ‹Quiver (Fin n)› (quiverUndirectedAdj n))
    (_hconn : QuiverUndirectedConnected n)
    (h_not_posdef : ∃ x : Fin n → ℤ, x ≠ 0 ∧
      ¬ (0 < dotProduct x ((2 • (1 : Matrix (Fin n) (Fin n) ℤ) -
        quiverUndirectedAdj n).mulVec x))) :
    ¬ HasFiniteRepresentationType k n :=
  -- The per-field infinite type result. The InfiniteTypeConstructions in Chapter 6
  -- prove ¬IsFiniteTypeQuiver (for ALL fields/orientations). Extracting the per-field
  -- version requires refactoring those proofs to expose the ∀k∀Q quantifier structure.
  -- See Issue #2255 for details on this bridge.
  sorry

/-- Backward direction bridge: `IsDynkinDiagram` implies `HasFiniteRepresentationType`
for any algebraically closed field and the given quiver.

This requires:
1. Showing the quiver is an orientation of its undirected adjacency (needs Subsingleton
   homs and no bidirectional arrows — these follow from HasFiniteRepType in the iff,
   but are needed independently for the backward direction)
2. Positive roots are finite (Theorem 6.5.2a)
3. Each positive root gives exactly one indecomposable (Theorem 6.5.2c)
4. Every indecomposable has dim vector = positive root (indecomposable_bilinearForm_eq_two)
5. Packaging into HasFiniteRepresentationType with the right universe and iso type -/
private lemma isDynkinDiagram_HasFiniteRepresentationType
    (k : Type) [Field k] [IsAlgClosed k]
    (n : ℕ) [Quiver.{0} (Fin n)] [∀ a b : Fin n, Decidable (Nonempty (a ⟶ b))]
    [∀ a b : Fin n, Subsingleton (a ⟶ b)]
    (hOrient : IsOrientationOf ‹Quiver (Fin n)› (quiverUndirectedAdj n))
    (_hconn : QuiverUndirectedConnected n)
    (hDynkin : IsDynkinDiagram n (quiverUndirectedAdj n)) :
    HasFiniteRepresentationType k n := by
  set adj := quiverUndirectedAdj n with hadj
  -- Step 1: Positive roots are finite
  have h_fin_roots := Theorem_6_5_2a_finiteness hDynkin
  haveI : Fintype {d : Fin n → ℤ | IsPositiveRoot n adj d} := h_fin_roots.fintype
  -- Step 2: For each positive root, 6.5.2c gives an indecomposable
  have h_exist : ∀ (r : {d : Fin n → ℤ | IsPositiveRoot n adj d}),
      ∃ (ρ : FinQuiverRep k n),
        (∀ v, Module.Free k (ρ.obj v)) ∧
        (∀ v, Module.Finite k (ρ.obj v)) ∧
        ρ.IsIndecomposable ∧
        (∀ v, (r.val v : ℤ) = ↑(Module.finrank k (ρ.obj v))) := by
    intro ⟨α, hα⟩
    obtain ⟨ρ, hFree, hFin, hIndec, hDim⟩ :=
      (Theorem_6_5_2c_bijection hDynkin k hOrient α hα).1
    exact ⟨ρ, hFree, hFin, hIndec, hDim⟩
  -- Step 3: Choose representatives
  choose rep hRep_free hRep_fin hRep_indec hRep_dim using h_exist
  -- Step 4: Enumerate roots via Fin m
  set m := Fintype.card {d : Fin n → ℤ | IsPositiveRoot n adj d}
  obtain ⟨rootEnum⟩ := Fintype.truncEquivFin {d : Fin n → ℤ | IsPositiveRoot n adj d}
  refine ⟨m, fun i => rep (rootEnum.symm i),
    fun i => hRep_fin _, fun i => hRep_indec _, ?_⟩
  -- Step 5: Every fd indecomposable is iso to some representative
  intro ρ hρ_fin hρ_indec
  -- Dim vector of ρ
  set d_ρ := fun v => (Module.finrank k (ρ.obj v) : ℤ)
  -- Module.Free (needed for bilinear form theorem)
  -- QuiverRepresentation only provides AddCommMonoid; upgrade to AddCommGroup for Module.Free
  haveI hρ_free : ∀ v, Module.Free k (ρ.obj v) := fun v =>
    @Module.Free.of_divisionRing k (ρ.obj v) _ (addCommGroupOfRing (k := k)) _
  -- B(d,d) = 2
  have hBdd := indecomposable_bilinearForm_eq_two hDynkin hOrient ρ hρ_indec
  -- d is nonneg and nonzero → positive root
  have hd_pos : ∀ i, 0 ≤ d_ρ i := fun i => Int.natCast_nonneg _
  have hd_nonzero : d_ρ ≠ 0 := by
    obtain ⟨v, hv⟩ := hρ_indec.1
    intro heq
    have hfr := congr_fun heq v
    simp only [d_ρ, Pi.zero_apply, Int.natCast_eq_zero] at hfr
    haveI : Subsingleton (ρ.obj v) :=
      @Module.finrank_zero_iff k (ρ.obj v) _ (addCommGroupOfRing (k := k)) _ _ |>.mp hfr
    exact absurd hv (not_nontrivial (ρ.obj v))
  have hd_root : IsPositiveRoot n adj d_ρ :=
    ⟨⟨hd_nonzero, by rwa [cartanMatrix] at hBdd⟩, hd_pos⟩
  -- Find the root's index
  set root : {d : Fin n → ℤ | IsPositiveRoot n adj d} := ⟨d_ρ, hd_root⟩
  use rootEnum root
  -- rep (rootEnum.symm (rootEnum root)) = rep root
  have hrw : rootEnum.symm (rootEnum root) = root := rootEnum.symm_apply_apply root
  -- Use uniqueness from 6.5.2c: any two indecomposables with same dim vector are iso
  have h_unique := (Theorem_6_5_2c_bijection hDynkin k hOrient d_ρ hd_root).2
  -- Set up instances for rep root
  haveI : ∀ v, Module.Free k ((rep root).obj v) := hRep_free root
  haveI : ∀ v, Module.Finite k ((rep root).obj v) := hRep_fin root
  -- Dim vector equalities
  have hρ_dimv : ∀ v, (d_ρ v : ℤ) = ↑(Module.finrank k (ρ.obj v)) := fun _ => rfl
  have hrep_dimv : ∀ v, (d_ρ v : ℤ) = ↑(Module.finrank k ((rep root).obj v)) :=
    hRep_dim root
  -- Get the Iso from uniqueness
  obtain ⟨iso⟩ := h_unique ρ (rep root) hρ_indec (hRep_indec root) hρ_dimv hrep_dimv
  -- Convert to QuiverRepresentationEquiv, adjusting for the rootEnum roundtrip
  exact ⟨by change QuiverRepresentationEquiv k (Fin n) ρ (rep (rootEnum.symm (rootEnum root)))
            rw [hrw]; exact iso.toEquiv⟩

/-! ## Gabriel's Theorem -/

/-- **Gabriel's theorem**: A connected quiver on `Fin n` vertices has finite representation
type over an algebraically closed field if and only if its underlying undirected graph
is a Dynkin diagram (i.e., is connected, simple, and has positive definite Cartan matrix,
which forces it to be one of A_n, D_n, E_6, E_7, or E_8).

The forward direction: if Q has finite type, its underlying graph must be Dynkin.
The backward direction: if the underlying graph is Dynkin, Q has finite type regardless
of the orientation of edges.

(Etingof Theorem 2.1.2) -/
theorem Theorem_2_1_2 (k : Type) [Field k] [IsAlgClosed k]
    (n : ℕ) [Quiver.{0} (Fin n)] [∀ a b : Fin n, Decidable (Nonempty (a ⟶ b))]
    [∀ a b : Fin n, Subsingleton (a ⟶ b)]
    (hOrient : IsOrientationOf ‹Quiver (Fin n)› (quiverUndirectedAdj n))
    (hconn : QuiverUndirectedConnected n) :
    HasFiniteRepresentationType k n ↔
      IsDynkinDiagram n (quiverUndirectedAdj n) := by
  constructor
  · -- Forward: finite representation type → Dynkin diagram
    intro hfrt
    refine ⟨quiverUndirectedAdj_symm, quiverUndirectedAdj_diag, quiverUndirectedAdj_01,
      hconn, fun x hx => ?_⟩
    -- Show positive definiteness by contradiction: if not positive definite,
    -- infinite type constructions give ¬HasFiniteRepresentationType
    by_contra h_not_pos
    exact absurd hfrt
      (not_posdef_not_HasFiniteRepresentationType k n hOrient hconn ⟨x, hx, h_not_pos⟩)
  · -- Backward: Dynkin diagram → finite representation type
    exact isDynkinDiagram_HasFiniteRepresentationType k n hOrient hconn

end Etingof
