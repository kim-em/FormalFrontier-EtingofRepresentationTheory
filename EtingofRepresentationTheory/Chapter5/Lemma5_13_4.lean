import Mathlib

/-!
# Lemma 5.13.4: Module Homomorphisms via Idempotents

For an idempotent e in an algebra A and a left A-module M, there is a natural
isomorphism:

  Hom_A(Ae, M) ≅ eM

where eM = {m ∈ M | e • m = m} is the fixed-point set of e acting on M.

The forward map sends φ to φ(e), and the inverse sends m to the map x ↦ x • m.

## Mathlib correspondence

This is a standard result in module theory. Mathlib has idempotents and
module homomorphisms, but this specific statement may need to be proved.
-/

/-- For an idempotent e in ring A and left A-module M, the evaluation map φ ↦ φ(e)
gives an equivalence Hom_A(Ae, M) ≃ {m ∈ M | e • m = m}.
(Etingof Lemma 5.13.4) -/
noncomputable def Etingof.Lemma5_13_4
    {A : Type*} [Ring A]
    (e : A) (he : IsIdempotentElem e)
    (M : Type*) [AddCommGroup M] [Module A M] :
    (↥(Submodule.span A ({e} : Set A)) →ₗ[A] M) ≃ {m : M // e • m = m} where
  toFun φ :=
    let e' : ↥(Submodule.span A ({e} : Set A)) := ⟨e, Submodule.subset_span rfl⟩
    have he' : e • e' = e' := Subtype.ext (by change e * e = e; exact he.eq)
    ⟨φ e', by rw [← φ.map_smul, he']⟩
  invFun p :=
    { toFun := fun ⟨x, _⟩ => x • p.1
      map_add' := fun ⟨x, _⟩ ⟨y, _⟩ => add_smul x y p.1
      map_smul' := fun a ⟨x, _⟩ => by dsimp; exact mul_smul a x p.1 }
  left_inv φ := by
    ext ⟨x, hx⟩
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
    dsimp only [LinearMap.coe_mk, AddHom.coe_mk]
    have he' : e • (⟨e, Submodule.subset_span rfl⟩ :
        ↥(Submodule.span A ({e} : Set A))) = ⟨e, Submodule.subset_span rfl⟩ :=
      Subtype.ext (show e * e = e from he.eq)
    have h1 : (a • e) • φ ⟨e, Submodule.subset_span rfl⟩ =
        a • (e • φ ⟨e, Submodule.subset_span rfl⟩) := mul_smul a e _
    have h2 : e • φ ⟨e, Submodule.subset_span rfl⟩ =
        φ ⟨e, Submodule.subset_span rfl⟩ := by rw [← φ.map_smul, he']
    rw [h1, h2, ← φ.map_smul]; rfl
  right_inv p := Subtype.ext p.2
