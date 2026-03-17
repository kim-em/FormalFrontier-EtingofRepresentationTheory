import EtingofRepresentationTheory.Chapter6.Definition6_6_3
import EtingofRepresentationTheory.Chapter6.Definition6_6_4
import EtingofRepresentationTheory.Chapter6.Proposition6_6_5
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Proposition 6.6.8: Dimension Vector Under Reflection

(1) Let i be a sink and V surjective at i. Then d(F⁺ᵢ V) = sᵢ(d(V)).
(2) Let i be a source and V injective at i. Then d(F⁻ᵢ V) = sᵢ(d(V)).

where sᵢ is the simple reflection and d(V) is the dimension vector.

The proof computes dim(ker φ) = Σ_{j→i} dim V_j − dim V_i, showing that the
change in dimension vector at i equals −B(d(V), αᵢ), which is exactly sᵢ(d(V)).

## Mathlib correspondence

Requires reflection functors, dimension vectors, simple reflections, and the
bilinear form B on the root lattice. Mathlib has `CoxeterSystem` with simple
reflections, but the connection to quiver representations is not formalized.
-/

/-- The simple reflection sᵢ acting on an ℤ-valued dimension vector.

At vertex j ≠ i, the vector is unchanged: `sᵢ(d)_j = d_j`.
At vertex i: `sᵢ(d)_i = -d_i + Σ_a d(adj a)`.

The index type `ι` represents the edges adjacent to `i`:
- For a sink vertex, use `ι = ArrowsInto V i` with `adj = Sigma.fst`.
- For a source vertex, use `ι = ArrowsOutOf V i` with `adj = Sigma.fst`.

Since i is a sink (resp. source), all edges incident to i point into (resp. out of) i,
so the undirected adjacency sum reduces to a sum over `ArrowsInto` (resp. `ArrowsOutOf`).
(Etingof, §6.6) -/
def Etingof.simpleReflectionDimVector
    {V : Type*} [DecidableEq V]
    {ι : Type*} [Fintype ι] (adj : ι → V)
    (i : V) (d : V → ℤ) : V → ℤ :=
  fun v => if v = i then -d i + ∑ a, d (adj a) else d v

/-- The `Module.finrank` of a vertex space in a `QuiverRepresentation`, using the
representation's own bundled module instance. This avoids instance resolution
issues when the quiver instance on the vertex type differs from the ambient one
(e.g., for representations on reversed quivers). -/
noncomputable def Etingof.QuiverRepresentation.finrankAt'
    (k : Type*) [CommSemiring k] {Q : Type*} {inst : Quiver Q}
    (ρ : @Etingof.QuiverRepresentation k Q _ inst) (v : Q) : ℕ :=
  @Module.finrank k (ρ.obj v) _ (ρ.instAddCommMonoid v) (ρ.instModule v)

/-- At a sink with surjective map, the dimension vector transforms by the
simple reflection: `d(F⁺ᵢ V) = sᵢ(d(V))`.

At vertices j ≠ i, `F⁺ᵢ(V)_j = V_j` so the dimension is unchanged.
At vertex i, `F⁺ᵢ(V)_i = ker(φ)` where `φ : ⊕_{j→i} V_j → V_i`, and by
rank-nullity with φ surjective:
  `dim(ker φ) = Σ_{j→i} dim V_j − dim V_i = sᵢ(d(V))_i`.

(Etingof Proposition 6.6.8, part 1) -/
theorem Etingof.Proposition6_6_8_sink
    {k : Type*} [Field k]
    {V : Type*} [DecidableEq V] [Quiver V]
    {i : V} (hi : Etingof.IsSink V i)
    (ρ : Etingof.QuiverRepresentation k V)
    [∀ v, Module.Free k (ρ.obj v)] [∀ v, Module.Finite k (ρ.obj v)]
    [Fintype (Etingof.ArrowsInto V i)]
    (hsurj : Function.Surjective (ρ.sinkMap i)) :
    ∀ v, ((Etingof.reflectionFunctorPlus V i hi ρ).finrankAt' k v : ℤ) =
      Etingof.simpleReflectionDimVector (fun (a : Etingof.ArrowsInto V i) => a.1)
        i (fun w => (Module.finrank k (ρ.obj w) : ℤ)) v :=
  sorry

/-- At a source with injective map, the dimension vector transforms by the
simple reflection: `d(F⁻ᵢ V) = sᵢ(d(V))`.

At vertices j ≠ i, `F⁻ᵢ(V)_j = V_j` so the dimension is unchanged.
At vertex i, `F⁻ᵢ(V)_i = coker(ψ)` where `ψ : V_i → ⊕_{i→j} V_j`, and by
rank-nullity with ψ injective:
  `dim(coker ψ) = Σ_{i→j} dim V_j − dim V_i = sᵢ(d(V))_i`.

(Etingof Proposition 6.6.8, part 2) -/
theorem Etingof.Proposition6_6_8_source
    {k : Type*} [Field k]
    {V : Type*} [DecidableEq V] [Quiver V]
    {i : V} (hi : Etingof.IsSource V i)
    (ρ : Etingof.QuiverRepresentation k V)
    [∀ v, Module.Free k (ρ.obj v)] [∀ v, Module.Finite k (ρ.obj v)]
    [Fintype (Etingof.ArrowsOutOf V i)]
    (hinj : Function.Injective (ρ.sourceMap i)) :
    ∀ v, ((Etingof.reflectionFunctorMinus V i hi ρ).finrankAt' k v : ℤ) =
      Etingof.simpleReflectionDimVector (fun (a : Etingof.ArrowsOutOf V i) => a.1)
        i (fun w => (Module.finrank k (ρ.obj w) : ℤ)) v :=
  sorry
