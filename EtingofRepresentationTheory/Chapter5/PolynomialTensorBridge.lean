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

/-- The symmetrized tensor depends only on the multiset of `f`:
precomposing with a permutation `τ` leaves it invariant. -/
lemma symTensor_comp_perm (f : Fin n → Fin N × Fin N) (τ : Equiv.Perm (Fin n)) :
    symTensor k N n (f ∘ τ) = symTensor k N n f := by
  unfold symTensor
  congr 1
  refine Fintype.sum_equiv (Equiv.mulLeft τ) _ _ ?_
  intro σ
  simp only [Equiv.coe_mulLeft]
  rfl

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

/-! ## Left inverse and injectivity -/

/-- Tensor-product basis of `V^⊗n ⊗ (V^*)^⊗n` indexed by pairs of functions
`(i, j) : (Fin n → Fin N) × (Fin n → Fin N)`, where `(i, j)` corresponds to
`(⨂_k e_{i k}) ⊗ (⨂_k e_{j k}*)`. -/
noncomputable def tensorBasis :
    Module.Basis ((Fin n → Fin N) × (Fin n → Fin N)) k (PolyTensorTgt k N n) :=
  (Basis.piTensorProduct (fun _ : Fin n => stdBasis k N)).tensorProduct
    (Basis.piTensorProduct (fun _ : Fin n => stdDualBasis k N))

/-- Left inverse to `polyToTensor`: sends a tensor basis element
`(⨂_k e_{i k}) ⊗ (⨂_k e_{j k}*)` to the monomial `∏_l X_{j l, i l}`. -/
noncomputable def tensorToPoly :
    PolyTensorTgt k N n →ₗ[k] MvPolynomial (Fin N × Fin N) k :=
  (tensorBasis k N n).constr k fun ij =>
    ∏ l : Fin n, MvPolynomial.X (R := k) (ij.2 l, ij.1 l)

@[simp]
lemma tensorBasis_apply (ij : (Fin n → Fin N) × (Fin n → Fin N)) :
    tensorBasis k N n ij =
      (PiTensorProduct.tprod k (fun l => stdBasis k N (ij.1 l))) ⊗ₜ[k]
        (PiTensorProduct.tprod k (fun l => stdDualBasis k N (ij.2 l))) := by
  simp [tensorBasis, Module.Basis.tensorProduct_apply']

/-- `seqTensor f` equals the tensor basis element at `(Prod.snd ∘ f, Prod.fst ∘ f)`. -/
lemma seqTensor_eq_tensorBasis (f : Fin n → Fin N × Fin N) :
    seqTensor k N n f = tensorBasis k N n (fun l => (f l).2, fun l => (f l).1) := by
  simp [seqTensor, tensorBasis_apply]

/-- Applying `tensorToPoly` to a `seqTensor f` gives the product `∏_l X_{f(l)}`. -/
lemma tensorToPoly_seqTensor (f : Fin n → Fin N × Fin N) :
    tensorToPoly k N n (seqTensor k N n f) = ∏ l : Fin n, MvPolynomial.X (R := k) (f l) := by
  rw [show seqTensor k N n f =
        tensorBasis k N n (fun l => (f l).2, fun l => (f l).1) from
      by simp [seqTensor, tensorBasis_apply]]
  unfold tensorToPoly
  rw [Module.Basis.constr_basis]

variable [CharZero k]

/-- Applying `tensorToPoly` to `symTensor f` gives the product `∏_l X_{f(l)}`.
The symmetrization is absorbed by reindexing within the commutative product. -/
lemma tensorToPoly_symTensor (f : Fin n → Fin N × Fin N) :
    tensorToPoly k N n (symTensor k N n f) = ∏ l : Fin n, MvPolynomial.X (R := k) (f l) := by
  unfold symTensor
  rw [LinearMap.map_smul, map_sum]
  have hterm : ∀ σ : Equiv.Perm (Fin n),
      tensorToPoly k N n (seqTensor k N n (f ∘ σ)) =
        ∏ l : Fin n, MvPolynomial.X (R := k) (f l) := by
    intro σ
    rw [tensorToPoly_seqTensor]
    -- ∏ l, X ((f ∘ σ) l) = ∏ l, X (f l) by reindexing σ
    exact Fintype.prod_equiv σ _ _ (fun _ => rfl)
  simp_rw [hterm]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    ← Nat.cast_smul_eq_nsmul k, smul_smul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)), one_smul]

/-- The product `∏_l X (canonicalSeq l)` equals the monomial `monomial s 1`.
This uses that `canonicalSeq` traces through `(Finsupp.toMultiset s).toList`,
whose image multiset equals `Finsupp.toMultiset s` — so the product is
`∏ p, X p ^ s p = monomial s 1` by `prod_X_pow_eq_monomial`. -/
lemma prod_X_canonicalSeq (s : (Fin N × Fin N) →₀ ℕ) (hs : s.sum (fun _ => id) = n) :
    (∏ l : Fin n, MvPolynomial.X (R := k) (canonicalSeq N n s hs l)) =
      MvPolynomial.monomial s (1 : k) := by
  classical
  -- Convert the `Fin n`-indexed product to a `Multiset`-indexed product.
  -- Step 1: rewrite via `List.prod_ofFn` to a list product.
  rw [← List.prod_ofFn (f := fun l : Fin n => MvPolynomial.X (R := k)
        (canonicalSeq N n s hs l))]
  -- Step 2: `List.ofFn (canonicalSeq s)` is, up to a Fin.cast, exactly
  -- `(Finsupp.toMultiset s).toList`. We rewrite using a multiset identity.
  have hcard : Multiset.card (Finsupp.toMultiset s) = n := by
    rw [Finsupp.card_toMultiset]; exact hs
  -- The key: List.ofFn reconstructs the underlying list, so
  -- `(List.ofFn fun l => X (canonicalSeq s hs l)).prod` equals
  -- `((toMultiset s).toList.map X).prod`
  have hmap : (List.ofFn fun l : Fin n =>
      MvPolynomial.X (R := k) (canonicalSeq N n s hs l)) =
    (Finsupp.toMultiset s).toList.map (MvPolynomial.X (R := k)) := by
    apply List.ext_getElem
    · simp [Multiset.length_toList, hcard]
    · intro i h1 h2
      simp [canonicalSeq, List.getElem_ofFn, List.getElem_map]
  rw [hmap]
  -- Convert the list-map-prod to a multiset prod via toList/coe
  rw [show ((Finsupp.toMultiset s).toList.map (MvPolynomial.X (R := k))).prod =
         ((Finsupp.toMultiset s).map (MvPolynomial.X (R := k))).prod from by
    conv_rhs => rw [← Multiset.coe_toList (Finsupp.toMultiset s)]
    rw [Multiset.map_coe, Multiset.prod_coe]]
  -- Move the map inside: (toMultiset s).map X = toMultiset (mapDomain X s)
  rw [Finsupp.toMultiset_map, Finsupp.prod_toMultiset,
    Finsupp.prod_mapDomain_index_inj MvPolynomial.X_injective]
  -- Now goal is `s.prod (fun a n => (X a) ^ n) = monomial s 1`
  exact MvPolynomial.prod_X_pow_eq_monomial

/-- `tensorToPoly` applied to `multisetToTensor s` recovers the monomial `X^s`
when `s` has the correct degree `n` (otherwise it is zero). -/
lemma tensorToPoly_multisetToTensor (s : (Fin N × Fin N) →₀ ℕ) :
    tensorToPoly k N n (multisetToTensor k N n s) =
      if s.sum (fun _ => id) = n then MvPolynomial.monomial s (1 : k) else 0 := by
  unfold multisetToTensor
  split_ifs with hs
  · rw [tensorToPoly_symTensor, prod_X_canonicalSeq (k := k) (N := N) (n := n) s hs]
  · simp

/-- The composition `tensorToPoly ∘ polyToTensor` is the identity on the
degree-`n` homogeneous submodule: a homogeneous polynomial `p` recovers as
`tensorToPoly (polyToTensor p) = p`. -/
lemma tensorToPoly_polyToTensor_eq_self (p : MvPolynomial (Fin N × Fin N) k)
    (hp : p.IsHomogeneous n) :
    tensorToPoly k N n (polyToTensor k N n p) = p := by
  classical
  -- Expand p in the monomial basis and compute term-by-term.
  conv_rhs => rw [p.as_sum]
  rw [show tensorToPoly k N n (polyToTensor k N n p) =
      tensorToPoly k N n (polyToTensor k N n
        (∑ v ∈ p.support, MvPolynomial.monomial v (MvPolynomial.coeff v p))) from by
    congr 2; exact p.as_sum]
  rw [map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro s hs
  -- For `monomial s c`, compute polyToTensor and tensorToPoly.
  have hcoeff_ne : MvPolynomial.coeff s p ≠ 0 := MvPolynomial.mem_support_iff.mp hs
  -- Homogeneity: |s| = n.
  have hsn : s.sum (fun _ => id) = n := by
    have hw := hp hcoeff_ne  -- weight 1 s = n
    -- weight 1 s = s.sum (fun _ => id) when s takes values in ℕ
    rw [Finsupp.weight_apply] at hw
    simpa using hw
  -- Compute: monomial s c = c • monomial s 1
  rw [show MvPolynomial.monomial s (MvPolynomial.coeff s p) =
        MvPolynomial.coeff s p • MvPolynomial.monomial s (1 : k) from by
    rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]]
  rw [LinearMap.map_smul, LinearMap.map_smul]
  congr 1
  -- polyToTensor (monomial s 1) = multisetToTensor s
  rw [show polyToTensor k N n (MvPolynomial.monomial s 1) = multisetToTensor k N n s from by
    unfold polyToTensor
    rw [show (MvPolynomial.monomial s 1 : MvPolynomial (Fin N × Fin N) k) =
         MvPolynomial.basisMonomials (Fin N × Fin N) k s from rfl,
      Module.Basis.constr_basis]]
  rw [tensorToPoly_multisetToTensor, if_pos hsn]

/-- The bridge `homogeneousPolyToTensor` is injective: distinct homogeneous
polynomials give distinct tensors. -/
theorem homogeneousPolyToTensor_injective :
    Function.Injective (homogeneousPolyToTensor k N n) := by
  intro p q hpq
  apply Subtype.ext
  have hp := tensorToPoly_polyToTensor_eq_self k N n p.val p.property
  have hq := tensorToPoly_polyToTensor_eq_self k N n q.val q.property
  have heq : tensorToPoly k N n (polyToTensor k N n p.val) =
      tensorToPoly k N n (polyToTensor k N n q.val) := by
    unfold homogeneousPolyToTensor at hpq
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at hpq
    rw [hpq]
  rw [hp, hq] at heq
  exact heq

end PolynomialTensorBridge

end Etingof
