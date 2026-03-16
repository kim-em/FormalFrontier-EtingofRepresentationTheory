import Mathlib
import EtingofRepresentationTheory.Infrastructure.IrreducibleEnumeration
import EtingofRepresentationTheory.Infrastructure.RegularCharacter

/-!
# Theorem 4.5.4: Second Orthogonality Relation (Column Orthogonality)

For g, h ∈ G, the column orthogonality of characters states:
$$\sum_{V} \chi_V(g) \cdot \chi_V(h^{-1})
= \begin{cases} |Z_G(g)| & g \sim h \\ 0 & \text{otherwise}\end{cases}$$

where the sum runs over irreducible representations V.

## Proof strategy

The proof computes tr(T) where T(x) = gxh⁻¹ on k[G] in two ways:

1. **Basis computation** (proved here): tr(T) counts fixed points
   `{x : gxh⁻¹ = x}`, bijects with `Z_G(g)` when `g ~ h`.

2. **Decomposition** (sorry'd, needs Peter-Weyl): Using
   `k[G] ≅ ⊕_V V ⊗ V*`, tr = `∑_V χ_V(g) · χ_V(h⁻¹)`.

## Mathlib correspondence

Column (second) orthogonality, not in Mathlib as of v4.28.
Row (first) orthogonality is `FDRep.char_orthonormal`.
-/

open CategoryTheory

universe u

variable {G : Type u} [Group G] [Fintype G]

/-! ### Group-theoretic lemmas on conjugation fixed points -/

section ConjugatorCounting

/-- Equivalence between `Z_G(g)` and `{x | x * g * x⁻¹ = h}` via
left multiplication by a conjugator `c` with `c * g * c⁻¹ = h`. -/
noncomputable def conjugatorEquiv (g h c : G)
    (hc : c * g * c⁻¹ = h) :
    ↥(Subgroup.centralizer ({g} : Set G)) ≃
      {x : G // x * g * x⁻¹ = h} where
  toFun z := ⟨c * z.1, by
    have hz := z.2
    rw [Subgroup.mem_centralizer_iff] at hz
    have hzg : z.1 * g * z.1⁻¹ = g := by
      have := (hz g (Set.mem_singleton g)).symm
      rw [mul_inv_eq_iff_eq_mul, this]
    calc c * z.1 * g * (c * z.1)⁻¹
        = c * (z.1 * g * z.1⁻¹) * c⁻¹ := by group
      _ = c * g * c⁻¹ := by rw [hzg]
      _ = h := hc⟩
  invFun x := ⟨c⁻¹ * x.1, by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    have hx := x.2
    have key : (c⁻¹ * x.1) * g * (c⁻¹ * x.1)⁻¹ = g := by
      calc _ = c⁻¹ * (x.1 * g * x.1⁻¹) * c := by group
        _ = c⁻¹ * h * c := by rw [hx]
        _ = c⁻¹ * (c * g * c⁻¹) * c := by rw [hc]
        _ = g := by group
    calc g * (c⁻¹ * x.1)
        = (c⁻¹ * x.1) * g * (c⁻¹ * x.1)⁻¹ * (c⁻¹ * x.1) := by
          rw [key]
      _ = (c⁻¹ * x.1) * g := by group⟩
  left_inv z := by ext; simp
  right_inv x := by ext; simp

open scoped Classical in
/-- The set `{x : G | x * g * x⁻¹ = h}` is empty when `g` and `h`
are not conjugate. -/
theorem conjugators_empty_of_not_isConj (g h : G)
    (hnh : ¬IsConj g h) :
    Finset.filter (fun x => x * g * x⁻¹ = h)
      Finset.univ = ∅ := by
  rw [Finset.filter_eq_empty_iff]
  intro x _ heq
  exact hnh (isConj_iff.mpr ⟨x, heq⟩)

open scoped Classical in
/-- When `g ~ h`, `|{x : G | x * g * x⁻¹ = h}| = |Z_G(g)|`. -/
theorem card_conjugators_eq_of_isConj (g h : G)
    (hgh : IsConj g h) :
    (Finset.filter (fun x => x * g * x⁻¹ = h)
      Finset.univ).card =
      Fintype.card
        ↥(Subgroup.centralizer ({g} : Set G)) := by
  obtain ⟨c, hc⟩ := isConj_iff.mp hgh
  rw [← Fintype.card_subtype]
  exact Fintype.card_congr
    (conjugatorEquiv g h c hc).symm

open scoped Classical in
/-- `|{x ∈ G | x * g * x⁻¹ = h}| = |Z_G(g)|` if `g ~ h`, else `0`.
-/
theorem card_conjugators (g h : G) :
    (Finset.filter (fun x => x * g * x⁻¹ = h)
      Finset.univ).card =
      if IsConj g h
        then Fintype.card
          ↥(Subgroup.centralizer ({g} : Set G))
        else 0 := by
  split
  · exact card_conjugators_eq_of_isConj g h ‹_›
  · simp [conjugators_empty_of_not_isConj g h ‹_›]

end ConjugatorCounting

/-! ### Main theorem -/

variable {k : Type u} [Field k] [IsAlgClosed k]

open scoped Classical in
/-- **Column orthogonality of characters** (Etingof Theorem 4.5.4).

For `g, h ∈ G`, `∑_V χ_V(g) · χ_V(h⁻¹)` over irreducible
representations equals `|Z_G(g)|` when `g ~ h`, else `0`.

The proof requires the Peter-Weyl decomposition
`k[G] ≅ ⊕_V V ⊗ V*` (not yet available). The group-theoretic
fixed-point counting is proved in `card_conjugators`. -/
theorem Etingof.Theorem4_5_4
    [NeZero (Nat.card G : k)]
    (D : IrrepDecomp k G) (V : Fin D.n → FDRep k G)
    (hV : ∀ i, Simple (V i))
    (hinj : ∀ i j, Nonempty ((V i) ≅ (V j)) → i = j)
    (hsurj : ∀ (W : FDRep k G), Simple W →
      ∃ i, Nonempty (W ≅ V i))
    (g h : G) :
    ∑ i : Fin D.n,
      (V i).character g * (V i).character h⁻¹ =
      if IsConj g h
        then (Fintype.card
          ↥(Subgroup.centralizer ({g} : Set G)) : k)
        else 0 := by
  sorry
