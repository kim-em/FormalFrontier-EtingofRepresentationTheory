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

## Status

Equivariance of the bridge under the GL_N-right-translation action on
polynomials vs. the `g ↦ g^⊗n ⊗ 1` action on the tensor target is the
intended companion property. It is deferred to a sibling issue so that
the construction and injectivity land first (injectivity is the key
property that `#2478` consumes via the left-inverse — equivariance will
be stated and proved alongside the final `polynomialRep_embeds_in_tensorPower`
assembly).
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

omit [CharZero k] in
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

/-! ## GL_N-equivariance

The bridge `polyToTensor` intertwines the right-translation action on
polynomials (sending `X_{ij}` to `Σ_l X_{il} · g_{l,j}`) with the
`g ↦ g^⊗n ⊗ id` action on `V^⊗n ⊗ (V^*)^⊗n`. -/

/-- Right-translation as an algebra hom on `MvPolynomial (Fin N × Fin N) k`.
On generators: `X_{ij} ↦ Σ_l X_{il} · C(g_{l,j})`. This is the action coming
from `(g · P)(X) = P(X · g)`. -/
noncomputable def polyRightTransl (g : Matrix (Fin N) (Fin N) k) :
    MvPolynomial (Fin N × Fin N) k →ₐ[k] MvPolynomial (Fin N × Fin N) k :=
  MvPolynomial.aeval fun ij : Fin N × Fin N =>
    ∑ l : Fin N, MvPolynomial.X (R := k) (ij.1, l) * MvPolynomial.C (g l ij.2)

/-- The `g^⊗n ⊗ id` action on `V^⊗n ⊗ (V^*)^⊗n`. The matrix `g` acts on the
first `V^⊗n` factor by tensor power; the second `(V^*)^⊗n` factor is left
unchanged. -/
noncomputable def tgtGLAction (g : Matrix (Fin N) (Fin N) k) :
    PolyTensorTgt k N n →ₗ[k] PolyTensorTgt k N n :=
  TensorProduct.map (PiTensorProduct.map fun _ : Fin n => g.toLin') LinearMap.id

/-- Expansion of `g.toLin'` on a standard basis vector. -/
lemma toLin'_stdBasis (g : Matrix (Fin N) (Fin N) k) (j : Fin N) :
    Matrix.toLin' g (stdBasis k N j) = ∑ b : Fin N, g b j • stdBasis k N b := by
  classical
  ext i
  rw [stdBasis, Pi.basisFun_apply, Matrix.toLin'_apply, Matrix.mulVec_single,
    MulOpposite.op_one, one_smul]
  simp only [Matrix.col_apply, Finset.sum_apply, Pi.smul_apply, Pi.basisFun_apply,
    Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- Expansion of `tgtGLAction g` on a `seqTensor`. -/
lemma tgtGLAction_seqTensor (g : Matrix (Fin N) (Fin N) k) (f : Fin n → Fin N × Fin N) :
    tgtGLAction k N n g (seqTensor k N n f) =
      ∑ b : Fin n → Fin N, (∏ l, g (b l) (f l).2) •
        seqTensor k N n (fun l => ((f l).1, b l)) := by
  classical
  unfold tgtGLAction seqTensor
  rw [TensorProduct.map_tmul, LinearMap.id_apply, PiTensorProduct.map_tprod]
  -- LHS first factor: tprod (fun l => g.toLin' (stdBasis (f l).2))
  simp_rw [toLin'_stdBasis]
  -- Expand the multilinear sum via MultilinearMap.map_sum on `tprod`.
  rw [MultilinearMap.map_sum (PiTensorProduct.tprod k)
        (g := fun (l : Fin n) (b : Fin N) => g b (f l).2 • stdBasis k N b)]
  -- Each summand factors a scalar product out of `tprod` via `map_smul_univ`.
  simp_rw [MultilinearMap.map_smul_univ (PiTensorProduct.tprod k)]
  -- Distribute the smul through the tensor product.
  rw [TensorProduct.sum_tmul]
  refine Finset.sum_congr rfl ?_
  intro b _
  rw [TensorProduct.smul_tmul']

/-- Expansion of `tgtGLAction g` on a `symTensor`. The bijection
`(σ, b) ↔ (σ, b ∘ σ⁻¹)` matches the inner sum on the LHS with the
inner sum coming from `symTensor`'s expansion on the RHS. -/
lemma tgtGLAction_symTensor (g : Matrix (Fin N) (Fin N) k) (f : Fin n → Fin N × Fin N) :
    tgtGLAction k N n g (symTensor k N n f) =
      ∑ c : Fin n → Fin N, (∏ l, g (c l) (f l).2) •
        symTensor k N n (fun l => ((f l).1, c l)) := by
  classical
  -- Expand LHS: tgtGLAction is linear, push it inside the symmetric sum.
  -- Unfold every `symTensor` (both LHS and the per-c RHS) to a `(n!)⁻¹ • Σ_τ` form.
  unfold symTensor
  rw [LinearMap.map_smul, map_sum]
  simp_rw [tgtGLAction_seqTensor]
  -- LHS shape: (n!)⁻¹ • ∑ τ ∑ b, X τ b. RHS shape: ∑ c, scalar • (n!)⁻¹ • ∑ τ, ...
  -- Pull the (n!)⁻¹ out of the c-sum on the RHS.
  simp_rw [smul_comm _ ((n.factorial : k)⁻¹), ← Finset.smul_sum]
  congr 1
  -- ∑ τ, ∑ b, X τ b = ∑ c, (scalar c) • ∑ τ, T σ c. Push scalar inside, then swap.
  simp_rw [Finset.smul_sum (s := (Finset.univ : Finset (Equiv.Perm (Fin n))))]
  rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin n → Fin N)))]
  refine Finset.sum_congr rfl fun τ _ => ?_
  -- Inner identity at fixed τ. Bijection on functions: e b := b ∘ τ.symm,
  -- equivalently c ↦ c ∘ τ via the inverse.
  refine Fintype.sum_equiv (Equiv.arrowCongr τ (Equiv.refl (Fin N))) _ _ ?_
  intro b
  simp only [Function.comp_apply]
  congr 1
  · -- product equality via reindex by τ
    refine Fintype.prod_equiv τ _ _ ?_
    intro l
    simp [Equiv.arrowCongr_apply]
  · -- seqTensor equality: (b ∘ τ.symm) (τ l) = b l
    congr 1
    funext l
    simp [Equiv.arrowCongr_apply]

/-! ### Polynomial side: `polyRightTransl` on products of `X`s -/

/-- A product of `X`s equals the monomial whose Finsupp records each pair's
multiplicity. The proof is a straight Finset induction using
`MvPolynomial.X = monomial (single _ 1) 1`. -/
private lemma prod_X_eq_monomial_fn (f : Fin n → Fin N × Fin N) :
    (∏ l : Fin n, MvPolynomial.X (R := k) (f l)) =
      MvPolynomial.monomial (∑ l : Fin n, Finsupp.single (f l) 1) (1 : k) := by
  classical
  have key : ∀ s : Finset (Fin n),
      (∏ l ∈ s, MvPolynomial.X (R := k) (f l)) =
        MvPolynomial.monomial (∑ l ∈ s, Finsupp.single (f l) 1) (1 : k) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s has ih =>
      rw [Finset.prod_insert has, Finset.sum_insert has, ih,
        show MvPolynomial.X (R := k) (f a) =
            MvPolynomial.monomial (Finsupp.single (f a) 1) (1 : k) from rfl,
        MvPolynomial.monomial_mul, mul_one]
  exact key _

/-- `polyRightTransl g` evaluated on a single `X`-generator. -/
@[simp]
lemma polyRightTransl_X (g : Matrix (Fin N) (Fin N) k) (ij : Fin N × Fin N) :
    polyRightTransl k N g (MvPolynomial.X ij) =
      ∑ l : Fin N,
        MvPolynomial.X (R := k) (ij.1, l) * MvPolynomial.C (g l ij.2) := by
  unfold polyRightTransl
  rw [MvPolynomial.aeval_X]

/-- Expansion of `polyRightTransl g` on a product `∏_l X (f l)`. The result
is a sum over choice functions `c : Fin n → Fin N`, with constant
multiplier `C(∏_l g (c l) (f l).2)` on the substituted monomial
`∏_l X((f l).1, c l)`. -/
lemma polyRightTransl_prod (g : Matrix (Fin N) (Fin N) k) (f : Fin n → Fin N × Fin N) :
    polyRightTransl k N g (∏ l : Fin n, MvPolynomial.X (R := k) (f l)) =
      ∑ c : Fin n → Fin N,
        MvPolynomial.C (∏ l : Fin n, g (c l) (f l).2) *
          (∏ l : Fin n, MvPolynomial.X (R := k) ((f l).1, c l)) := by
  classical
  rw [map_prod]
  simp_rw [polyRightTransl_X]
  -- Distribute the prod over the sum via prod_univ_sum.
  rw [Finset.prod_univ_sum
    (t := fun (_ : Fin n) => (Finset.univ : Finset (Fin N)))
    (f := fun l j => MvPolynomial.X (R := k) ((f l).1, j) *
                     MvPolynomial.C (g j (f l).2))]
  rw [show (Fintype.piFinset fun (_ : Fin n) => (Finset.univ : Finset (Fin N))) =
        (Finset.univ : Finset (Fin n → Fin N)) from Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun c _ => ?_
  -- Per c: ∏_l (X * C) = (∏ X) * (∏ C) = C(∏ g) * (∏ X)
  rw [Finset.prod_mul_distrib]
  rw [show (∏ l : Fin n, MvPolynomial.C (R := k) (g (c l) (f l).2)) =
      MvPolynomial.C (∏ l : Fin n, g (c l) (f l).2) from
    (map_prod (MvPolynomial.C (R := k)) _ _).symm]
  ring

/-! ### Multiset-invariance of `symTensor`

`symTensor f` only depends on the underlying multiset image of `f`. The proof
goes via constructing an explicit permutation `σ` matching two sequences with
the same multiset image, then applying `symTensor_comp_perm`. -/

/-- Given two functions `f g : Fin n → α` with the same multiset image, produce
an explicit permutation `σ : Equiv.Perm (Fin n)` with `g = f ∘ σ`. The
construction is by induction on `n`, peeling off the head `g 0` and matching
it against an element `l₀` of `f`'s domain. -/
private noncomputable def matchingPerm {α : Type*} [DecidableEq α] :
    ∀ {n : ℕ} (f g : Fin n → α),
      Multiset.map f (Finset.univ : Finset (Fin n)).val =
        Multiset.map g (Finset.univ : Finset (Fin n)).val →
      {σ : Equiv.Perm (Fin n) // g = f ∘ σ}
  | 0, _, g, _ => ⟨Equiv.refl _, funext fun i => i.elim0⟩
  | n + 1, f, g, h =>
      let hg0_mem : g 0 ∈ Multiset.map f (Finset.univ : Finset (Fin (n+1))).val := by
        rw [h]; exact Multiset.mem_map.mpr ⟨0, Finset.mem_univ _, rfl⟩
      let l₀ : Fin (n+1) := Classical.choose (Multiset.mem_map.mp hg0_mem)
      let l₀_spec :
        l₀ ∈ (Finset.univ : Finset (Fin (n+1))).val ∧ f l₀ = g 0 :=
        Classical.choose_spec (Multiset.mem_map.mp hg0_mem)
      let hl₀ : f l₀ = g 0 := l₀_spec.2
      let f' : Fin n → α := f ∘ l₀.succAbove
      let g' : Fin n → α := g ∘ Fin.succ
      let hpeel_f : Multiset.map f (Finset.univ : Finset (Fin (n+1))).val =
          f l₀ ::ₘ Multiset.map f' (Finset.univ : Finset (Fin n)).val := by
        conv_lhs => rw [Fin.univ_succAbove n l₀]
        simp only [Finset.cons_val, Multiset.map_cons, Finset.map_val,
          Multiset.map_map, Fin.coe_succAboveEmb]
        rfl
      let hpeel_g : Multiset.map g (Finset.univ : Finset (Fin (n+1))).val =
          g 0 ::ₘ Multiset.map g' (Finset.univ : Finset (Fin n)).val := by
        conv_lhs => rw [Fin.univ_succAbove n 0]
        simp only [Finset.cons_val, Multiset.map_cons, Finset.map_val,
          Multiset.map_map, Fin.coe_succAboveEmb, Fin.succAbove_zero]
        rfl
      let hms : Multiset.map f' (Finset.univ : Finset (Fin n)).val =
          Multiset.map g' (Finset.univ : Finset (Fin n)).val := by
        have hh : f l₀ ::ₘ Multiset.map f' (Finset.univ : Finset (Fin n)).val =
            f l₀ ::ₘ Multiset.map g' (Finset.univ : Finset (Fin n)).val := by
          rw [← hpeel_f, h, hpeel_g, hl₀]
        exact (Multiset.cons_inj_right _).mp hh
      let σ'_pkg := matchingPerm f' g' hms
      let σ' : Equiv.Perm (Fin n) := σ'_pkg.1
      let hσ' : g' = f' ∘ σ' := σ'_pkg.2
      let σ_fn : Fin (n+1) → Fin (n+1) :=
        Fin.cases l₀ (fun j => l₀.succAbove (σ' j))
      let hinj : Function.Injective σ_fn := by
        intro i j hij
        induction i using Fin.cases with
        | zero =>
          induction j using Fin.cases with
          | zero => rfl
          | succ b =>
            exfalso
            change l₀ = l₀.succAbove (σ' b) at hij
            exact (Fin.succAbove_ne l₀ (σ' b)) hij.symm
        | succ a =>
          induction j using Fin.cases with
          | zero =>
            exfalso
            change l₀.succAbove (σ' a) = l₀ at hij
            exact (Fin.succAbove_ne l₀ (σ' a)) hij
          | succ b =>
            change l₀.succAbove (σ' a) = l₀.succAbove (σ' b) at hij
            have h1 : σ' a = σ' b := l₀.succAbove_right_injective hij
            have h2 : a = b := σ'.injective h1
            exact congrArg Fin.succ h2
      let hbij : Function.Bijective σ_fn :=
        Finite.injective_iff_bijective.mp hinj
      ⟨Equiv.ofBijective σ_fn hbij, by
        funext i
        induction i using Fin.cases with
        | zero =>
          show g 0 = f (σ_fn 0)
          change g 0 = f l₀
          exact hl₀.symm
        | succ j =>
          show g (Fin.succ j) = f (σ_fn (Fin.succ j))
          change g (Fin.succ j) = f (l₀.succAbove (σ' j))
          have := congrFun hσ' j
          show g' j = f' (σ' j)
          exact this⟩

omit [CharZero k] in
/-- `symTensor` only depends on the underlying multiset of the sequence. -/
lemma symTensor_eq_of_multiset_eq (f g : Fin n → Fin N × Fin N)
    (h : Multiset.map f (Finset.univ : Finset (Fin n)).val =
         Multiset.map g (Finset.univ : Finset (Fin n)).val) :
    symTensor k N n f = symTensor k N n g := by
  classical
  obtain ⟨σ, hσ⟩ := matchingPerm f g h
  rw [hσ, symTensor_comp_perm]

omit [CharZero k] in
/-- For any sequence `g : Fin n → α`, the multiset of values `{g 0, …, g (n-1)}`
equals `Finsupp.toMultiset (∑ l, single (g l) 1)`. -/
private lemma toMultiset_sum_single_fn {α : Type*} [DecidableEq α] (g : Fin n → α) :
    Finsupp.toMultiset (∑ l : Fin n, Finsupp.single (g l) (1 : ℕ)) =
      Multiset.map g (Finset.univ : Finset (Fin n)).val := by
  classical
  rw [Finsupp.toMultiset_sum]
  simp only [Finsupp.toMultiset_single, one_smul]
  -- ∑ l ∈ univ, ({g l} : Multiset α) = univ.val.map g via Finset induction.
  induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, ih, Finset.insert_val, Multiset.ndinsert_of_notMem ha,
      Multiset.map_cons, Multiset.singleton_add]

/-- The bridge `polyToTensor` sends a product `∏_l X(f l)` of degree-1
generators to the symmetric tensor `symTensor f`. -/
lemma polyToTensor_prod_X (f : Fin n → Fin N × Fin N) :
    polyToTensor k N n (∏ l : Fin n, MvPolynomial.X (R := k) (f l)) =
      symTensor k N n f := by
  classical
  rw [prod_X_eq_monomial_fn]
  set s : (Fin N × Fin N) →₀ ℕ := ∑ l : Fin n, Finsupp.single (f l) 1 with hs_def
  -- polyToTensor on a basis monomial = multisetToTensor.
  have hpt : polyToTensor k N n (MvPolynomial.monomial s 1) = multisetToTensor k N n s := by
    unfold polyToTensor
    rw [show (MvPolynomial.monomial s 1 : MvPolynomial (Fin N × Fin N) k) =
         MvPolynomial.basisMonomials (Fin N × Fin N) k s from rfl,
       Module.Basis.constr_basis]
  rw [hpt]
  -- toMultiset s = multiset of f.
  have hf_multi : Finsupp.toMultiset s = Multiset.map f (Finset.univ : Finset (Fin n)).val := by
    rw [hs_def]; exact toMultiset_sum_single_fn n f
  -- |s| = n via card of toMultiset.
  have hsn : s.sum (fun _ => id) = n := by
    have hcard := congrArg Multiset.card hf_multi
    rw [Finsupp.card_toMultiset] at hcard
    rw [hcard]; simp
  unfold multisetToTensor
  rw [dif_pos hsn]
  -- symTensor (canonicalSeq s _) = symTensor f via multiset-invariance.
  refine symTensor_eq_of_multiset_eq k N n _ _ ?_
  -- multiset of canonicalSeq s = toMultiset s = multiset of f
  have hcard : Multiset.card (Finsupp.toMultiset s) = n := by
    rw [Finsupp.card_toMultiset]; exact hsn
  have hofFn : List.ofFn (canonicalSeq N n s hsn) = (Finsupp.toMultiset s).toList := by
    apply List.ext_getElem
    · simp [Multiset.length_toList, hcard]
    · intro i h1 h2
      simp [canonicalSeq]
  have huniv_map : Multiset.map (canonicalSeq N n s hsn)
      (Finset.univ : Finset (Fin n)).val =
      ((List.ofFn (canonicalSeq N n s hsn) : List _) : Multiset _) := by
    rw [show (Finset.univ : Finset (Fin n)).val = ((List.finRange n : List _) : Multiset _) from by
      simp [List.finRange]; rfl]
    rw [Multiset.map_coe, ← List.ofFn_eq_map]
  rw [huniv_map, hofFn, Multiset.coe_toList, hf_multi]

/-! ### Main equivariance theorem -/

omit [CharZero k] in
/-- `polyRightTransl g` preserves the homogeneous submodule of degree `m`. Each
generator `X_{ij}` (degree 1) maps to a sum of degree-1 monomials. -/
lemma polyRightTransl_isHomogeneous (g : Matrix (Fin N) (Fin N) k) {m : ℕ}
    {p : MvPolynomial (Fin N × Fin N) k} (hp : p.IsHomogeneous m) :
    (polyRightTransl k N g p).IsHomogeneous m := by
  have hgens : ∀ ij : Fin N × Fin N,
      (∑ l : Fin N,
          MvPolynomial.X (R := k) (ij.1, l) * MvPolynomial.C (g l ij.2)).IsHomogeneous 1 := by
    intro ij
    refine MvPolynomial.IsHomogeneous.sum _ _ _ ?_
    intro l _
    have := MvPolynomial.IsHomogeneous.mul (MvPolynomial.isHomogeneous_X (R := k) (ij.1, l))
      (MvPolynomial.isHomogeneous_C (σ := Fin N × Fin N) (g l ij.2))
    simpa using this
  have h := hp.aeval (fun ij => ∑ l : Fin N, MvPolynomial.X (R := k) (ij.1, l) *
    MvPolynomial.C (g l ij.2)) hgens
  simpa [polyRightTransl, one_mul] using h

/-- The bridge `polyToTensor` intertwines the right-translation action on
polynomials with the `g^⊗n ⊗ id` action on `V^⊗n ⊗ (V^*)^⊗n`, on
homogeneous degree-`n` polynomials. -/
theorem polyToTensor_rightTransl_of_isHomogeneous (g : Matrix (Fin N) (Fin N) k)
    {p : MvPolynomial (Fin N × Fin N) k} (hp : p.IsHomogeneous n) :
    polyToTensor k N n (polyRightTransl k N g p) =
      tgtGLAction k N n g (polyToTensor k N n p) := by
  classical
  -- Expand p as a sum of monomials and distribute through both sides.
  conv_lhs => rw [p.as_sum, map_sum (polyRightTransl k N g), map_sum (polyToTensor k N n)]
  conv_rhs => rw [p.as_sum, map_sum (polyToTensor k N n), map_sum (tgtGLAction k N n g)]
  apply Finset.sum_congr rfl
  intro s hs
  -- |s| = n by homogeneity.
  have hsn : s.sum (fun _ => id) = n := by
    have hcoeff : MvPolynomial.coeff s p ≠ 0 := MvPolynomial.mem_support_iff.mp hs
    have hw := hp hcoeff
    rw [Finsupp.weight_apply] at hw
    simpa using hw
  -- Pull out the scalar c := coeff s p (monomial s c = c • monomial s 1).
  rw [show MvPolynomial.monomial s (MvPolynomial.coeff s p) =
        (MvPolynomial.coeff s p) • MvPolynomial.monomial s (1 : k) from by
    rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]]
  rw [map_smul (polyRightTransl k N g), map_smul (polyToTensor k N n),
      map_smul (polyToTensor k N n), map_smul (tgtGLAction k N n g)]
  congr 1
  -- Goal: polyToTensor (polyRightTransl g (monomial s 1)) =
  --       tgtGLAction g (polyToTensor (monomial s 1))
  -- Express monomial s 1 = ∏_l X(canonicalSeq s _ l).
  rw [show MvPolynomial.monomial s (1 : k) =
        ∏ l : Fin n, MvPolynomial.X (R := k) (canonicalSeq N n s hsn l) from
      (prod_X_canonicalSeq (k := k) (N := N) (n := n) s hsn).symm]
  set f := canonicalSeq N n s hsn with hf_def
  rw [polyRightTransl_prod, map_sum]
  -- For each c, polyToTensor (C(scalar) * ∏ X(...)) = scalar • symTensor (...).
  have step : ∀ c : Fin n → Fin N,
      polyToTensor k N n (MvPolynomial.C (R := k) (∏ l, g (c l) (f l).2) *
          (∏ l, MvPolynomial.X (R := k) ((f l).1, c l))) =
        (∏ l, g (c l) (f l).2) • symTensor k N n (fun l => ((f l).1, c l)) := by
    intro c
    rw [show MvPolynomial.C (R := k) (∏ l, g (c l) (f l).2) *
          (∏ l, MvPolynomial.X (R := k) ((f l).1, c l)) =
        (∏ l, g (c l) (f l).2) • (∏ l, MvPolynomial.X (R := k) ((f l).1, c l)) from
      (MvPolynomial.smul_eq_C_mul _ _).symm]
    rw [LinearMap.map_smul, polyToTensor_prod_X]
  simp_rw [step]
  -- RHS: tgtGLAction g (polyToTensor (∏ X(f l))) = tgtGLAction g (symTensor f).
  rw [polyToTensor_prod_X, tgtGLAction_symTensor]

/-- The bridge `homogeneousPolyToTensor` is GL_N-equivariant: it intertwines the
right-translation action on homogeneous polynomials with the `g^⊗n ⊗ id`
action on `V^⊗n ⊗ (V^*)^⊗n`. -/
theorem homogeneousPolyToTensor_equivariant (g : Matrix (Fin N) (Fin N) k)
    (p : MvPolynomial.homogeneousSubmodule (Fin N × Fin N) k n) :
    homogeneousPolyToTensor k N n
        ⟨polyRightTransl k N g p.val,
          polyRightTransl_isHomogeneous (k := k) (N := N) (m := n) g p.property⟩ =
      tgtGLAction k N n g (homogeneousPolyToTensor k N n p) := by
  unfold homogeneousPolyToTensor
  simp only [LinearMap.comp_apply, Submodule.subtype_apply]
  exact polyToTensor_rightTransl_of_isHomogeneous (k := k) (N := N) (n := n) g p.property

end PolynomialTensorBridge

end Etingof
