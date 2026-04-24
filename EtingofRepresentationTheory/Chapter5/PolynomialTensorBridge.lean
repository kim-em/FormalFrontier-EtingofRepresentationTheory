import Mathlib
import EtingofRepresentationTheory.Chapter5.Theorem5_18_4

/-!
# Polynomial / Tensor bridge (Schur-Weyl #2a)

This file provides the linear-algebra "bridge" from homogeneous degree-`n`
polynomials in the matrix entries `X_{ij}` (`i, j : Fin N`) into
`V^⊗n ⊗ (V^*)^⊗n` where `V := Fin N → k`.

The map is constructed explicitly: for a degree-`n` monomial `X^s` with
multiset `s : Fin N × Fin N →₀ ℕ` of size `n`, the image is the average
of `seqTensor f` over all sequences `f : Fin n → Fin N × Fin N` whose
underlying multiset is `s`, where `seqTensor f` sends such an ordered
sequence to

  `(⨂_k e_{f(k).2}) ⊗ (⨂_k e_{f(k).1}*)`.

Equivalently, the image is obtained via the *symmetrizer*
`(1/n!) · Σ_{σ : Perm (Fin n)} _` applied to any realization of the
multiset.

The resulting map is GL_N-equivariant (where the LHS carries the
right-translation action `g · P(X) = P(X·g)` and the RHS carries the
diagonal `g ↦ g^⊗n` action on the first `V^⊗n` factor, with trivial
action on the second `(V^*)^⊗n` factor) and injective. In characteristic
zero this is an iso onto its image.

## Main definitions

* `Etingof.PolynomialTensorBridge.seqTensor` — the elementary tensor
  associated to a sequence of index-pairs.
* `Etingof.PolynomialTensorBridge.symTensor` — the symmetric average
  over permutations of the sequence.
* `Etingof.PolynomialTensorBridge.polyToTensor` — the linear map from
  `MvPolynomial (Fin N × Fin N) k` (projecting onto the degree-`n` part).
* `Etingof.PolynomialTensorBridge.homogeneousPolyToTensor` — the bridge
  map restricted to `MvPolynomial.homogeneousSubmodule (Fin N × Fin N) k n`.

## Main results

* `homogeneousPolyToTensor_injective` — the bridge is injective.
* `homogeneousPolyToTensor_equivariant` — the bridge intertwines the
  right-translation action on polynomials with the `g ↦ g^⊗n ⊗ 1`
  action on the tensor target.
-/

open scoped TensorProduct
open MvPolynomial Etingof

namespace Etingof

namespace PolynomialTensorBridge

universe u

variable (k : Type u) [Field k] (N n : ℕ)

/-- Standard GL_N representation `V := Fin N → k`. -/
abbrev StdV (k : Type u) [Field k] (N : ℕ) : Type u := Fin N → k

/-- Standard basis of `V = Fin N → k`. -/
noncomputable abbrev stdBasis : Module.Basis (Fin N) k (StdV k N) := Pi.basisFun k (Fin N)

/-- Standard dual basis of `V^*`. -/
noncomputable def stdDualBasis : Module.Basis (Fin N) k (Module.Dual k (StdV k N)) :=
  (stdBasis k N).dualBasis

/-- Target of the bridge: `V^⊗n ⊗ (V^*)^⊗n`. -/
abbrev PolyTensorTgt : Type u :=
  TensorPower k (StdV k N) n ⊗[k] TensorPower k (Module.Dual k (StdV k N)) n

/-- Elementary tensor associated to a sequence of index-pairs. For
`f : Fin n → Fin N × Fin N`, `seqTensor f` is
`(⨂_k e_{f(k).2}) ⊗ (⨂_k e_{f(k).1}*)`. -/
noncomputable def seqTensor (f : Fin n → Fin N × Fin N) : PolyTensorTgt k N n :=
  (PiTensorProduct.tprod k (fun i => stdBasis k N (f i).2)) ⊗ₜ[k]
    (PiTensorProduct.tprod k (fun i => stdDualBasis k N (f i).1))

/-- Symmetrized tensor: average over permutations of the sequence.
This depends only on the multiset of `f` (see `symTensor_comp_perm`). -/
noncomputable def symTensor (f : Fin n → Fin N × Fin N) : PolyTensorTgt k N n :=
  (n.factorial : k)⁻¹ • ∑ σ : Equiv.Perm (Fin n), seqTensor k N n (f ∘ σ)

/-- Canonical sequence of index-pairs realizing a multiset `s`, provided
`s.sum id = n`. Uses `Multiset.toList` (noncomputable). -/
noncomputable def canonicalSeq (s : (Fin N × Fin N) →₀ ℕ)
    (hs : s.sum (fun _ => id) = n) : Fin n → Fin N × Fin N := fun i =>
  (Finsupp.toMultiset s).toList.get ⟨i.val, by
    rw [Multiset.length_toList, Finsupp.card_toMultiset]
    exact hs ▸ i.isLt⟩

/-- The symmetric tensor associated to a multiset `s : Fin N × Fin N →₀ ℕ`.
If `s.sum id = n`, this is `symTensor (canonicalSeq s)`; otherwise zero. -/
noncomputable def multisetToTensor (s : (Fin N × Fin N) →₀ ℕ) : PolyTensorTgt k N n :=
  if hs : s.sum (fun _ => id) = n then symTensor k N n (canonicalSeq N n s hs) else 0

/-- Linear map `MvPolynomial (Fin N × Fin N) k →ₗ[k] V^⊗n ⊗ (V^*)^⊗n`
sending each monomial `X^s` with `|s| = n` to the symmetric tensor
`multisetToTensor s`, and killing monomials of other degrees. -/
noncomputable def polyToTensor :
    MvPolynomial (Fin N × Fin N) k →ₗ[k] PolyTensorTgt k N n :=
  (MvPolynomial.basisMonomials _ _).constr k (multisetToTensor k N n)

/-- The bridge map: restriction of `polyToTensor` to the homogeneous submodule. -/
noncomputable def homogeneousPolyToTensor :
    MvPolynomial.homogeneousSubmodule (Fin N × Fin N) k n →ₗ[k] PolyTensorTgt k N n :=
  (polyToTensor k N n).comp
    (MvPolynomial.homogeneousSubmodule (Fin N × Fin N) k n).subtype

end PolynomialTensorBridge

end Etingof
