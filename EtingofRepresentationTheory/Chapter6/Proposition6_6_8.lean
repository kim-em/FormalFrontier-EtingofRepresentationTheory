import EtingofRepresentationTheory.Chapter6.Definition6_5_1
import EtingofRepresentationTheory.Chapter6.Definition6_6_3
import EtingofRepresentationTheory.Chapter6.Definition6_6_4
import EtingofRepresentationTheory.Chapter6.Proposition6_6_5
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Proposition 6.6.8: Dimension Vector Under Reflection

(1) Let i be a sink and V surjective at i. Then d(F⁺ᵢ V) = sᵢ(d(V)).
(2) Let i be a source and V injective at i. Then d(F⁻ᵢ V) = sᵢ(d(V)).

where sᵢ is the simple reflection and d(V) is the dimension vector.

The reflection functors are defined as:
- F⁺ᵢ(V)_i = ker(φ) where φ : ⊕_{j→i} V_j → V_i (sink map)
- F⁻ᵢ(V)_i = coker(ψ) where ψ : V_i → ⊕_{i→j} V_j (source map)
- F±ᵢ(V)_v = V_v for v ≠ i

## Sink case (part 1)

The dimension formula at vertex i follows from rank-nullity applied to the
surjective sink map φ:
  dim(ker φ) + dim(V_i) = dim(⊕_{j→i} V_j) = ∑_{j→i} dim(V_j)

Since F⁺ᵢ(V)_i = ker(φ), this gives d(F⁺ᵢ V)_i = sᵢ(d(V))_i.
Away from i, d(F⁺ᵢ V)_v = d(V)_v since F⁺ᵢ(V)_v = V_v.

## Source case (part 2)

For the injective source map ψ, injectivity gives dim(Im ψ) = dim(V_i).
Therefore dim(coker ψ) = dim(⊕_{i→j} V_j) − dim(Im ψ) = ∑_{i→j} dim(V_j) − dim(V_i).

We state this as: dim(range ψ) = dim(V_i), which together with the standard
dimension formula for quotients gives d(F⁻ᵢ V)_i = sᵢ(d(V))_i.

## Formalization notes

The sink statement uses `LinearMap.ker` (= F⁺ᵢ(V)_i from Definition 6.6.3).
The source statement uses `LinearMap.range` to avoid forming the quotient module
(cokernel), which would require `AddCommGroup` — but `QuiverRepresentation` only
provides `AddCommMonoid` on vertex spaces.
-/

/-- At a sink where the sink map φ is surjective, the kernel of φ satisfies:
  dim(ker φ) + dim(V_i) = ∑_{j→i} dim(V_j)

Since F⁺ᵢ(V)_i = ker(φ) by Definition 6.6.3, and F⁺ᵢ(V)_v = V_v for v ≠ i,
this gives the dimension vector formula d(F⁺ᵢ V) = sᵢ(d(V)).
(Etingof Proposition 6.6.8, part 1) -/
theorem Etingof.Proposition6_6_8_sink
    {k : Type*} [Field k]
    {Q : Type*} [Quiver Q]
    {i : Q}
    {ρ : Etingof.QuiverRepresentation k Q}
    [∀ v, Module.Free k (ρ.obj v)] [∀ v, Module.Finite k (ρ.obj v)]
    [Fintype (Etingof.ArrowsInto Q i)]
    (hsurj : Function.Surjective (ρ.sinkMap i)) :
    Module.finrank k ↥(LinearMap.ker (ρ.sinkMap i)) + Module.finrank k (ρ.obj i) =
      ∑ a : Etingof.ArrowsInto Q i, Module.finrank k (ρ.obj a.1) :=
  sorry

/-- At a source where the source map ψ is injective, the range of ψ has the
same dimension as V_i:
  dim(range ψ) = dim(V_i)

Since F⁻ᵢ(V)_i = coker(ψ) = (⊕_{i→j} V_j) / Im(ψ) by Definition 6.6.4,
this implies dim(F⁻ᵢ V)_i = (∑_{i→j} dim V_j) − dim V_i = sᵢ(d(V))_i.
Combined with F⁻ᵢ(V)_v = V_v for v ≠ i, this gives d(F⁻ᵢ V) = sᵢ(d(V)).
(Etingof Proposition 6.6.8, part 2) -/
theorem Etingof.Proposition6_6_8_source
    {k : Type*} [Field k]
    {Q : Type*} [Quiver Q]
    {i : Q}
    {ρ : Etingof.QuiverRepresentation k Q}
    [∀ v, Module.Free k (ρ.obj v)] [∀ v, Module.Finite k (ρ.obj v)]
    (hinj : Function.Injective (ρ.sourceMap i)) :
    Module.finrank k ↥(LinearMap.range (ρ.sourceMap i)) =
      Module.finrank k (ρ.obj i) :=
  sorry
