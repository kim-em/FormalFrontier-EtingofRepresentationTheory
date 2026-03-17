import EtingofRepresentationTheory.Chapter2.Definition2_8_3
import EtingofRepresentationTheory.Chapter6.Definition6_6_1
import EtingofRepresentationTheory.Chapter6.Definition6_6_3
import EtingofRepresentationTheory.Chapter6.Definition6_6_4
import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Proposition 6.6.5: Surjectivity/Injectivity at Sinks and Sources

Let Q be a quiver and V an indecomposable representation.

(1) If i is a sink, then either dim V_i = 1 and dim V_j = 0 for j ≠ i, or the map
    φ : ⊕_{j→i} V_j → V_i is surjective.

(2) If i is a source, then either dim V_i = 1 and dim V_j = 0 for j ≠ i, or the map
    ψ : V_i → ⊕_{i→j} V_j is injective.

The proof uses decomposition: if φ is not surjective, complement of Im(φ) gives a
direct sum decomposition, contradicting indecomposability unless V is the simple
representation at i.

## Mathlib correspondence

Requires quiver representation infrastructure (indecomposable representations,
dimension vectors). Not directly available in Mathlib.
-/

/-- Over a field, any `AddCommMonoid` module is actually an `AddCommGroup`, with negation
given by scalar multiplication by `-1`. This bridges `QuiverRepresentation` (which uses
`AddCommMonoid`) and APIs like `Submodule.exists_isCompl` (which require `AddCommGroup`).
The resulting `AddCommGroup` extends the existing `AddCommMonoid` — no diamond. -/
noncomputable def Etingof.addCommGroupOfField {k : Type*} [Field k] {M : Type*}
    [inst : AddCommMonoid M] [Module k M] : AddCommGroup M :=
  { inst with
    neg := fun x => (-1 : k) • x
    zsmul := fun n x => (n : k) • x
    neg_add_cancel := fun a => by
      change (-1 : k) • a + a = 0
      nth_rw 2 [show a = (1 : k) • a from (one_smul k a).symm]
      rw [← add_smul, neg_add_cancel, zero_smul]
    zsmul_zero' := fun a => by simp [zero_smul]
    zsmul_succ' := fun n a => by
      simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one,
                  Int.cast_add, Int.cast_natCast, Int.cast_one, add_smul, one_smul]
    zsmul_neg' := fun n a => by
      simp only [Int.negSucc_eq, Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one,
                  Int.cast_neg, smul_smul, neg_one_mul] }

/-- Any submodule of a module over a field has a complement. This wraps
`Submodule.exists_isCompl` by constructing the required `AddCommGroup` instance. -/
private noncomputable def Etingof.existsIsCompl_repr
    {k : Type*} [Field k] {M : Type*} [AddCommMonoid M] [Module k M]
    (p : Submodule k M) : ∃ q : Submodule k M, IsCompl p q := by
  letI : AddCommGroup M := Etingof.addCommGroupOfField (k := k)
  exact Submodule.exists_isCompl p

/-- A quiver representation is **indecomposable** if it is nonzero and cannot be
written as a direct sum of two nonzero sub-representations. -/
def Etingof.QuiverRepresentation.IsIndecomposable
    {k : Type*} [CommSemiring k] {Q : Type*} [Quiver Q]
    (ρ : Etingof.QuiverRepresentation k Q) : Prop :=
  (∃ v, Nontrivial (ρ.obj v)) ∧
  ∀ (W₁ W₂ : ∀ v, Submodule k (ρ.obj v)),
    (∀ {a b : Q} (e : a ⟶ b), ∀ x ∈ W₁ a, ρ.mapLinear e x ∈ W₁ b) →
    (∀ {a b : Q} (e : a ⟶ b), ∀ x ∈ W₂ a, ρ.mapLinear e x ∈ W₂ b) →
    (∀ v, IsCompl (W₁ v) (W₂ v)) →
    (∀ v, W₁ v = ⊥) ∨ (∀ v, W₂ v = ⊥)

/-- A quiver representation is the **simple representation at vertex i** if
the space at i is one-dimensional and all other spaces are zero. -/
def Etingof.QuiverRepresentation.IsSimpleAt
    {k : Type*} [CommSemiring k] {Q : Type*} [DecidableEq Q] [Quiver Q]
    (ρ : Etingof.QuiverRepresentation k Q) (i : Q)
    [∀ v, Module.Free k (ρ.obj v)] [∀ v, Module.Finite k (ρ.obj v)] : Prop :=
  Module.finrank k (ρ.obj i) = 1 ∧ ∀ j, j ≠ i → Module.finrank k (ρ.obj j) = 0

/-- The canonical map φ : ⊕_{j→i} V_j → V_i at a sink vertex i. -/
noncomputable def Etingof.QuiverRepresentation.sinkMap
    {k : Type*} [CommSemiring k] {Q : Type*} [Quiver Q]
    (ρ : Etingof.QuiverRepresentation k Q) (i : Q) :
    DirectSum (Etingof.ArrowsInto Q i) (fun a => ρ.obj a.1) →ₗ[k] ρ.obj i := by
  classical
  exact DirectSum.toModule k (Etingof.ArrowsInto Q i) (ρ.obj i) (fun a => ρ.mapLinear a.2)

/-- The canonical map ψ : V_i → ⊕_{i→j} V_j at a source vertex i. -/
noncomputable def Etingof.QuiverRepresentation.sourceMap
    {k : Type*} [CommSemiring k] {Q : Type*} [Quiver Q]
    (ρ : Etingof.QuiverRepresentation k Q) (i : Q)
    [Fintype (Etingof.ArrowsOutOf Q i)] :
    ρ.obj i →ₗ[k] DirectSum (Etingof.ArrowsOutOf Q i) (fun a => ρ.obj a.1) := by
  classical
  exact ∑ a : Etingof.ArrowsOutOf Q i,
    (DirectSum.lof k (Etingof.ArrowsOutOf Q i) (fun a => ρ.obj a.1) a).comp (ρ.mapLinear a.2)

/-- For an indecomposable representation at a sink, either V is the simple
representation at i, or the canonical map ⊕_{j→i} V_j → V_i is surjective.
(Etingof Proposition 6.6.5, part 1)

The proof constructs complementary sub-representations from the range of the
sink map and uses indecomposability. See the module docstring for details. -/
theorem Etingof.Proposition6_6_5_sink
    {k : Type*} [Field k] {Q : Type*} [DecidableEq Q] [Quiver Q]
    {ρ : Etingof.QuiverRepresentation k Q} {i : Q}
    [∀ v, Module.Free k (ρ.obj v)] [∀ v, Module.Finite k (ρ.obj v)]
    (hi : Etingof.IsSink Q i)
    (hρ : ρ.IsIndecomposable) :
    ρ.IsSimpleAt i ∨ Function.Surjective (ρ.sinkMap i) := by
  -- Upgrade to AddCommGroup (needed for complements); extends existing AddCommMonoid
  letI : ∀ v, AddCommGroup (ρ.obj v) := fun v => Etingof.addCommGroupOfField (k := k)
  -- At a sink, no arrow leaves i
  have sink_no_out : ∀ {a b : Q} (_ : a ⟶ b), a ≠ i :=
    fun {_ b} e h => (hi b).false (h ▸ e)
  -- Decide: is sinkMap surjective?
  by_cases hsurj : Function.Surjective (ρ.sinkMap i)
  · exact Or.inr hsurj
  · -- sinkMap not surjective → show V is simple at i
    left
    -- Range is a proper submodule; get a complement
    obtain ⟨W, hW⟩ := Submodule.exists_isCompl (LinearMap.range (ρ.sinkMap i))
    -- Build complementary subrepresentations:
    --   W₁ v = range(sinkMap) at i, ⊤ elsewhere
    --   W₂ v = W at i, ⊥ elsewhere
    set W₁ : ∀ v, Submodule k (ρ.obj v) := fun v =>
      if hv : v = i then hv ▸ LinearMap.range (ρ.sinkMap i) else ⊤
    set W₂ : ∀ v, Submodule k (ρ.obj v) := fun v =>
      if hv : v = i then hv ▸ W else ⊥
    -- W₁ is a subrepresentation
    have hW₁_sub : ∀ {a b : Q} (e : a ⟶ b), ∀ x ∈ W₁ a, ρ.mapLinear e x ∈ W₁ b := by
      intro a b e x _
      by_cases hb : b = i
      · -- b = i: convert transport, show membership via sinkMap definition
        classical
        simp only [W₁, dif_pos hb]
        rw [show hb ▸ LinearMap.range (ρ.sinkMap i) = LinearMap.range (ρ.sinkMap b)
            from by subst hb; rfl]
        refine ⟨DirectSum.lof k (Etingof.ArrowsInto Q b)
          (fun j => ρ.obj j.1) ⟨a, e⟩ x, ?_⟩
        simp [Etingof.QuiverRepresentation.sinkMap]
      · simp only [W₁, hb, dite_false]; exact Submodule.mem_top
    -- W₂ is a subrepresentation (vacuously — source vertex a ≠ i has W₂ a = ⊥)
    have hW₂_sub : ∀ {a b : Q} (e : a ⟶ b), ∀ x ∈ W₂ a, ρ.mapLinear e x ∈ W₂ b := by
      intro a b e x hx
      simp only [W₂, sink_no_out e, dite_false, Submodule.mem_bot] at hx
      rw [hx, map_zero]; exact Submodule.zero_mem _
    -- Complementarity at each vertex
    have hcompl : ∀ v, IsCompl (W₁ v) (W₂ v) := by
      intro v; by_cases hv : v = i
      · subst hv; simp only [W₁, W₂, dite_true]; exact hW
      · simp only [W₁, W₂, hv, dite_false]; exact isCompl_top_bot
    -- Apply indecomposability
    rcases hρ.2 W₁ W₂ hW₁_sub hW₂_sub hcompl with h1 | h2
    · -- W₁ = ⊥ everywhere: trivial modules at j ≠ i, range = ⊥ at i
      have hj_triv : ∀ j, j ≠ i → Subsingleton (ρ.obj j) := by
        intro j hj
        have h_top_eq_bot : (⊤ : Submodule k (ρ.obj j)) = ⊥ := by
          have := h1 j; simp only [W₁, hj, dite_false] at this; exact this
        exact subsingleton_of_forall_eq 0 fun x => by
          have hx : x ∈ (⊥ : Submodule k (ρ.obj j)) := h_top_eq_bot ▸ Submodule.mem_top
          rwa [Submodule.mem_bot] at hx
      -- Only vertex i can be nontrivial
      have hi_nt : Nontrivial (ρ.obj i) := by
        obtain ⟨v, hv_nt⟩ := hρ.1
        by_cases hvi : v = i
        · exact hvi ▸ hv_nt
        · exact absurd (hj_triv v hvi) (not_subsingleton (α := ρ.obj v))
      haveI := hi_nt
      -- ρ.obj i is a simple module: any submodule P is ⊥ or ⊤
      -- (because P and its complement give complementary subreps, and indecomposability
      -- forces one to be zero; all maps are trivial since other modules are zero)
      have h_simple : IsSimpleModule k (ρ.obj i) :=
        { eq_bot_or_eq_top := fun P => by
            obtain ⟨P', hP'⟩ := Submodule.exists_isCompl P
            set U₁ : ∀ v, Submodule k (ρ.obj v) := fun v =>
              if hv : v = i then hv ▸ P else ⊤
            set U₂ : ∀ v, Submodule k (ρ.obj v) := fun v =>
              if hv : v = i then hv ▸ P' else ⊥
            have hU₁_sub : ∀ {a b : Q} (e : a ⟶ b),
                ∀ x ∈ U₁ a, ρ.mapLinear e x ∈ U₁ b := by
              intro a b e x _
              haveI := hj_triv a (sink_no_out e)
              rw [Subsingleton.eq_zero x, map_zero]; exact Submodule.zero_mem _
            have hU₂_sub : ∀ {a b : Q} (e : a ⟶ b),
                ∀ x ∈ U₂ a, ρ.mapLinear e x ∈ U₂ b := by
              intro a b e x hx
              simp only [U₂, sink_no_out e, dite_false, Submodule.mem_bot] at hx
              rw [hx, map_zero]; exact Submodule.zero_mem _
            have hUcompl : ∀ v, IsCompl (U₁ v) (U₂ v) := by
              intro v; by_cases hv : v = i
              · subst hv; simp only [U₁, U₂, dite_true]; exact hP'
              · simp only [U₁, U₂, hv, dite_false]; exact isCompl_top_bot
            rcases hρ.2 U₁ U₂ hU₁_sub hU₂_sub hUcompl with hU1 | hU2
            · left; have := hU1 i; simp only [U₁, dite_true] at this; exact this
            · right
              have := hU2 i; simp only [U₂, dite_true] at this
              exact eq_top_of_isCompl_bot (this ▸ hP') }
      exact ⟨isSimpleModule_iff_finrank_eq_one.mp h_simple,
             fun j hj => by haveI := hj_triv j hj; exact Module.finrank_zero_of_subsingleton⟩
    · -- W₂ = ⊥ everywhere: W = ⊥ at i, so range = ⊤ → surjective, contradiction
      have hW_bot : W = ⊥ := by
        have := h2 i; simp only [W₂, dite_true] at this; exact this
      exact absurd (LinearMap.range_eq_top.mp (eq_top_of_isCompl_bot (hW_bot ▸ hW))) hsurj

/-- For an indecomposable representation at a source, either V is the simple
representation at i, or the canonical map V_i → ⊕_{i→j} V_j is injective.
(Etingof Proposition 6.6.5, part 2)

The proof is dual to the sink case, using the kernel of the source map. -/
theorem Etingof.Proposition6_6_5_source
    {k : Type*} [Field k] {Q : Type*} [DecidableEq Q] [Quiver Q]
    {ρ : Etingof.QuiverRepresentation k Q} {i : Q}
    [∀ v, Module.Free k (ρ.obj v)] [∀ v, Module.Finite k (ρ.obj v)]
    [Fintype (Etingof.ArrowsOutOf Q i)]
    (hi : Etingof.IsSource Q i)
    (hρ : ρ.IsIndecomposable) :
    ρ.IsSimpleAt i ∨ Function.Injective (ρ.sourceMap i) := by
  -- Upgrade to AddCommGroup (needed for complements); extends existing AddCommMonoid
  letI : ∀ v, AddCommGroup (ρ.obj v) := fun v => Etingof.addCommGroupOfField (k := k)
  -- At a source, no arrow enters i
  have source_no_in : ∀ {a b : Q} (_ : a ⟶ b), b ≠ i :=
    fun {a _} e h => (hi a).false (h ▸ e)
  -- Decide: is sourceMap injective?
  by_cases hinj : Function.Injective (ρ.sourceMap i)
  · exact Or.inr hinj
  · -- sourceMap not injective → show V is simple at i
    left
    -- Kernel is nontrivial
    have hker_ne_bot : LinearMap.ker (ρ.sourceMap i) ≠ ⊥ := by
      intro heq; exact hinj (LinearMap.ker_eq_bot.mp heq)
    -- Get a complement of the kernel
    obtain ⟨W, hW⟩ := Submodule.exists_isCompl (LinearMap.ker (ρ.sourceMap i))
    -- Build complementary subrepresentations:
    --   W₁ v = ker(sourceMap) at i, ⊥ elsewhere
    --   W₂ v = W (complement of ker) at i, ⊤ elsewhere
    set W₁ : ∀ v, Submodule k (ρ.obj v) := fun v =>
      if hv : v = i then hv ▸ LinearMap.ker (ρ.sourceMap i) else ⊥
    set W₂ : ∀ v, Submodule k (ρ.obj v) := fun v =>
      if hv : v = i then hv ▸ W else ⊤
    -- W₁ is a subrepresentation: for any arrow e : a → b, b ≠ i, so W₁ b = ⊥.
    -- Need ρ.mapLinear e x ∈ W₁ b = ⊥. Since a ≠ i too (source: no arrows in),
    -- wait — no. At a source, no arrows come INTO i, meaning for any arrow e : a → b,
    -- we need b ≠ i. Actually, IsSource says no arrows enter i, so b ≠ i for any arrow.
    -- But a could equal i if there are arrows OUT of i... wait, at a source, arrows go OUT of i.
    -- So there CAN be arrows a ⟶ b with a = i.
    -- Correction: source_no_in says b ≠ i. And a = i is possible.
    -- For W₁: if a = i, x ∈ W₁ i = ker(sourceMap), and b ≠ i, so W₁ b = ⊥.
    -- Need ρ.mapLinear e x = 0 when x ∈ ker(sourceMap) and e : i → b.
    -- x ∈ ker(sourceMap) means sourceMap x = 0.
    -- sourceMap = ∑_a lof(a) ∘ mapLinear(a.2), so (sourceMap x)_⟨b,e⟩ = mapLinear(e)(x).
    -- If sourceMap x = 0, then all components are 0, so mapLinear(e)(x) = 0 for each e. ✓
    -- If a ≠ i, x ∈ W₁ a = ⊥, so x = 0 and mapLinear e 0 = 0 ∈ W₁ b. ✓
    have hW₁_sub : ∀ {a b : Q} (e : a ⟶ b), ∀ x ∈ W₁ a, ρ.mapLinear e x ∈ W₁ b := by
      intro a b e x hx
      have hb : b ≠ i := source_no_in e
      simp only [W₁, hb, dite_false]; simp only [Submodule.mem_bot]
      by_cases ha : a = i
      · -- a = i: x ∈ ker(sourceMap), so all component maps send x to 0
        -- Use suffices to subst ha early, avoiding transport issues
        suffices ∀ (e' : i ⟶ b) (x' : ρ.obj i),
            x' ∈ LinearMap.ker (ρ.sourceMap i) → ρ.mapLinear e' x' = 0 by
          subst ha; exact this e x (by simpa [W₁, dif_pos rfl] using hx)
        intro e' x' hx'
        rw [LinearMap.mem_ker] at hx'
        -- sourceMap i x' = 0 means each component is 0.
        -- Evaluate at ⟨b, e'⟩: (sourceMap i x')_⟨b,e'⟩ = mapLinear e' x'
        -- because sourceMap = ∑_a lof(a) ∘ mapLinear(a.2) and only the ⟨b,e'⟩ term survives.
        suffices h_eval : (ρ.sourceMap i x') ⟨b, e'⟩ = ρ.mapLinear e' x' by
          rw [← h_eval, hx']; rfl
        -- Show (sourceMap i x') ⟨b, e'⟩ = mapLinear e' x' as a pure identity
        -- Then the suffices gives mapLinear e' x' = 0 from hx'
        classical
        -- Apply component ⟨b,e'⟩ to sourceMap
        change (DirectSum.component k (Etingof.ArrowsOutOf Q i)
          (fun s => ρ.obj s.1) ⟨b, e'⟩) (ρ.sourceMap i x') = ρ.mapLinear e' x'
        unfold Etingof.QuiverRepresentation.sourceMap
        simp only [LinearMap.sum_apply, LinearMap.coe_comp, Function.comp_apply,
          map_sum, DirectSum.component.of, Finset.sum_dite_eq', Finset.mem_univ, ite_true]
      · -- a ≠ i: x ∈ W₁ a = ⊥, so x = 0
        simp only [W₁, ha, dite_false, Submodule.mem_bot] at hx
        rw [hx, map_zero]
    -- W₂ is a subrepresentation: arrows b ≠ i, so W₂ b = ⊤. Always true.
    have hW₂_sub : ∀ {a b : Q} (e : a ⟶ b), ∀ x ∈ W₂ a, ρ.mapLinear e x ∈ W₂ b := by
      intro a b e x _
      simp only [W₂, source_no_in e, dite_false]; exact Submodule.mem_top
    -- Complementarity at each vertex
    have hcompl : ∀ v, IsCompl (W₁ v) (W₂ v) := by
      intro v; by_cases hv : v = i
      · subst hv; simp only [W₁, W₂, dite_true]; exact hW
      · simp only [W₁, W₂, hv, dite_false]; exact isCompl_bot_top
    -- Apply indecomposability
    rcases hρ.2 W₁ W₂ hW₁_sub hW₂_sub hcompl with h1 | h2
    · -- W₁ = ⊥ everywhere: ker(sourceMap) = ⊥ at i → injective, contradiction
      have hker_bot : LinearMap.ker (ρ.sourceMap i) = ⊥ := by
        have := h1 i; simp only [W₁, dite_true] at this; exact this
      exact absurd (LinearMap.ker_eq_bot.mp hker_bot) hinj
    · -- W₂ = ⊥ everywhere: ⊤ = ⊥ at j ≠ i (trivial), W = ⊥ at i
      have hj_triv : ∀ j, j ≠ i → Subsingleton (ρ.obj j) := by
        intro j hj
        have h_top_eq_bot : (⊤ : Submodule k (ρ.obj j)) = ⊥ := by
          have := h2 j; simp only [W₂, hj, dite_false] at this; exact this
        exact subsingleton_of_forall_eq 0 fun x => by
          have hx : x ∈ (⊥ : Submodule k (ρ.obj j)) := h_top_eq_bot ▸ Submodule.mem_top
          rwa [Submodule.mem_bot] at hx
      -- Only vertex i can be nontrivial
      have hi_nt : Nontrivial (ρ.obj i) := by
        obtain ⟨v, hv_nt⟩ := hρ.1
        by_cases hvi : v = i
        · exact hvi ▸ hv_nt
        · exact absurd (hj_triv v hvi) (not_subsingleton (α := ρ.obj v))
      haveI := hi_nt
      -- ρ.obj i is a simple module (same argument as sink case)
      have h_simple : IsSimpleModule k (ρ.obj i) :=
        { eq_bot_or_eq_top := fun P => by
            obtain ⟨P', hP'⟩ := Submodule.exists_isCompl P
            set U₁ : ∀ v, Submodule k (ρ.obj v) := fun v =>
              if hv : v = i then hv ▸ P else ⊥
            set U₂ : ∀ v, Submodule k (ρ.obj v) := fun v =>
              if hv : v = i then hv ▸ P' else ⊤
            have hU₁_sub : ∀ {a b : Q} (e : a ⟶ b),
                ∀ x ∈ U₁ a, ρ.mapLinear e x ∈ U₁ b := by
              intro a b e x hx
              simp only [U₁, source_no_in e, dite_false, Submodule.mem_bot]
              by_cases ha : a = i
              · simp only [U₁, ha, dite_true] at hx
                haveI := hj_triv b (source_no_in e)
                exact Subsingleton.eq_zero _
              · simp only [U₁, ha, dite_false, Submodule.mem_bot] at hx
                rw [hx, map_zero]
            have hU₂_sub : ∀ {a b : Q} (e : a ⟶ b),
                ∀ x ∈ U₂ a, ρ.mapLinear e x ∈ U₂ b := by
              intro a b e x _
              simp only [U₂, source_no_in e, dite_false]; exact Submodule.mem_top
            have hUcompl : ∀ v, IsCompl (U₁ v) (U₂ v) := by
              intro v; by_cases hv : v = i
              · subst hv; simp only [U₁, U₂, dite_true]; exact hP'
              · simp only [U₁, U₂, hv, dite_false]; exact isCompl_bot_top
            rcases hρ.2 U₁ U₂ hU₁_sub hU₂_sub hUcompl with hU1 | hU2
            · left; have := hU1 i; simp only [U₁, dite_true] at this; exact this
            · right
              have hP'_bot := hU2 i; simp only [U₂, dite_true] at hP'_bot
              exact eq_top_of_isCompl_bot (hP'_bot ▸ hP') }
      exact ⟨isSimpleModule_iff_finrank_eq_one.mp h_simple,
             fun j hj => by haveI := hj_triv j hj; exact Module.finrank_zero_of_subsingleton⟩
