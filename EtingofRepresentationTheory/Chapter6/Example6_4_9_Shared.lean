import EtingofRepresentationTheory.Chapter6.Definition6_4_3

/-!
# Example 6.4.9: Shared Infrastructure for Root Counting

Shared definitions and lemmas used by the E-type, A_n, and D_n root count proofs.
-/

/-- The set of positive roots of a graph given by its adjacency matrix. -/
def Etingof.positiveRoots (n : ℕ) (adj : Matrix (Fin n) (Fin n) ℤ) :
    Set (Fin n → ℤ) :=
  {x | Etingof.IsRoot n adj x ∧ ∀ i, 0 ≤ x i}

section RootCountShared

open Matrix Finset

/-- Count positive roots with coordinates in `{0, ..., B-1}`,
working over `Fin B` to avoid `Finset.image` overhead. -/
def rootCountFinset (n : ℕ)
    (adj : Matrix (Fin n) (Fin n) ℤ) (B : ℕ) :
    Finset (Fin n → Fin B) :=
  (univ : Finset (Fin n → Fin B)).filter fun v =>
    let x : Fin n → ℤ := fun i => (v i : ℤ)
    decide (x ≠ 0) &&
    decide (dotProduct x
      ((2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).mulVec x) = 2)

/-- Elements of rootCountFinset correspond to positive roots. -/
lemma rootCountFinset_mem {n : ℕ}
    {adj : Matrix (Fin n) (Fin n) ℤ}
    {B : ℕ} {v : Fin n → Fin B}
    (hv : v ∈ rootCountFinset n adj B) :
    (fun i => (v i : ℤ)) ∈ Etingof.positiveRoots n adj := by
  simp only [rootCountFinset, mem_filter, mem_univ, true_and,
    Bool.and_eq_true, decide_eq_true_eq] at hv
  exact ⟨⟨hv.1, hv.2⟩, fun i => Int.natCast_nonneg _⟩

/-- The embedding from `Fin n → Fin B` to `Fin n → ℤ` is injective. -/
lemma fin_to_int_injective {n B : ℕ} :
    Function.Injective
      (fun (v : Fin n → Fin B) (i : Fin n) => (v i : ℤ)) := by
  intro v w h
  funext i
  have : (v i : ℤ) = (w i : ℤ) := congr_fun h i
  exact Fin.ext (by exact_mod_cast this)

/-- If all positive roots have coords in `{0,...,B-1}`, then the
positive root count equals `rootCountFinset.card`. -/
lemma positiveRoots_card_eq {n : ℕ}
    {adj : Matrix (Fin n) (Fin n) ℤ} {B : ℕ}
    (hbound : ∀ x : Fin n → ℤ, Etingof.IsRoot n adj x →
      (∀ i, 0 ≤ x i) → ∀ i, x i < B) :
    (Etingof.positiveRoots n adj).Finite ∧
    Set.ncard (Etingof.positiveRoots n adj) =
      (rootCountFinset n adj B).card := by
  suffices h : Etingof.positiveRoots n adj =
      ↑((rootCountFinset n adj B).image
        (fun v i => (v i : ℤ))) by
    refine ⟨h ▸ ((rootCountFinset n adj B).image _).finite_toSet,
      ?_⟩
    rw [h, Set.ncard_coe_finset,
      Finset.card_image_of_injective _ fin_to_int_injective]
  ext x
  simp only [Etingof.positiveRoots, Set.mem_setOf_eq,
    Finset.coe_image, Set.mem_image, Finset.mem_coe]
  constructor
  · intro ⟨hroot, hpos⟩
    refine ⟨fun i => ⟨(x i).toNat, ?_⟩, ?_, ?_⟩
    · exact Int.toNat_lt (hpos i) |>.mpr (hbound x hroot hpos i)
    · simp only [rootCountFinset, mem_filter, mem_univ, true_and,
        Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨?_, ?_⟩
      · intro heq
        exact hroot.1 (by
          ext i
          have := congr_fun heq i
          simp only [Int.toNat_of_nonneg (hpos i),
            Pi.zero_apply] at this
          exact this)
      · have hconv : (fun i => ((x i).toNat : ℤ)) = x :=
          funext fun i => Int.toNat_of_nonneg (hpos i)
        simp only [hconv]; exact hroot.2
    · funext i; exact Int.toNat_of_nonneg (hpos i)
  · intro ⟨v, hv, hvx⟩
    subst hvx
    exact rootCountFinset_mem hv

end RootCountShared
