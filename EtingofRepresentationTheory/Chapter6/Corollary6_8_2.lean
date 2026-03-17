import EtingofRepresentationTheory.Chapter6.Definition6_4_3
import EtingofRepresentationTheory.Chapter6.Definition6_4_10

/-!
# Corollary 6.8.2: Dimension Vectors Are Positive Roots

For any indecomposable representation V of a Dynkin quiver Q, d(V) is a positive root,
i.e., B(d(V), d(V)) = 2.

The proof: by Theorem 6.8.1, s_{i₁} ⋯ s_{iₘ}(d(V)) = αₚ. Since the sᵢ preserve B,
B(d(V), d(V)) = B(αₚ, αₚ) = 2.

## Mathlib correspondence

Requires dimension vectors, simple reflections preserving the bilinear form,
and Theorem 6.8.1. This is part of Gabriel's theorem (classification of
quivers of finite representation type).
-/

section BilinearFormPreservation

variable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)

/-- The bilinear form B(x, y) = xᵀ A y associated to a matrix A. -/
private def B (x y : Fin n → ℤ) : ℤ :=
  dotProduct x (A.mulVec y)

/-- Root reflection preserves the bilinear form of a symmetric matrix:
B(sα(v), sα(v)) = B(v, v) when A is symmetric and B(α, α) = 2.

The proof is a direct computation:
  sα(v) = v - B(v, α) · α
  B(sα(v), sα(v)) = B(v,v) - 2·B(v,α)·B(α,v) + B(v,α)²·B(α,α)
                   = B(v,v) - 2·c² + c²·2 = B(v,v)
where c = B(v, α) and we use B(α,v) = B(v,α) (symmetry) and B(α,α) = 2. -/
theorem Etingof.rootReflection_preserves_bilinearForm
    (hA : A.IsSymm)
    (α : Fin n → ℤ) (hα : dotProduct α (A.mulVec α) = 2)
    (v : Fin n → ℤ) :
    dotProduct (Etingof.rootReflection n A α v)
      (A.mulVec (Etingof.rootReflection n A α v)) =
    dotProduct v (A.mulVec v) := by
  unfold Etingof.rootReflection
  set c := dotProduct v (A.mulVec α) with hc_def
  -- Symmetry: B(α, v) = B(v, α) when A is symmetric
  have hsymm : dotProduct α (A.mulVec v) = c := by
    rw [Matrix.dotProduct_mulVec, ← hA.eq, Matrix.vecMul_transpose, dotProduct_comm]
  -- Expand B(v - cα, A(v - cα)) using linearity
  have h1 : A.mulVec (v - c • α) = A.mulVec v - c • A.mulVec α := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul]
  rw [h1]
  simp only [dotProduct_sub, sub_dotProduct, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  -- Goal should be: B(v,v) - c·B(v,α) - (c·B(α,v) - c²·B(α,α)) = B(v,v)
  rw [hsymm, hα]
  ring

/-- Simple reflection sᵢ preserves the bilinear form when the Cartan matrix is symmetric
and satisfies B(αᵢ, αᵢ) = 2 (which is the standard normalization for simple roots). -/
theorem Etingof.simpleReflection_preserves_bilinearForm
    (hA : A.IsSymm)
    (i : Fin n)
    (hroot : dotProduct (Pi.single i 1) (A.mulVec (Pi.single i 1)) = 2)
    (v : Fin n → ℤ) :
    dotProduct (Etingof.simpleReflection n A i v)
      (A.mulVec (Etingof.simpleReflection n A i v)) =
    dotProduct v (A.mulVec v) :=
  Etingof.rootReflection_preserves_bilinearForm A hA _ hroot v

/-- Iterated simple reflections preserve the bilinear form.
If each simple root αᵢ satisfies B(αᵢ, αᵢ) = 2, then applying any sequence of
simple reflections preserves B(v, v). -/
theorem Etingof.iteratedSimpleReflection_preserves_bilinearForm
    (hA : A.IsSymm)
    (hroots : ∀ i : Fin n, dotProduct (Pi.single i 1) (A.mulVec (Pi.single i 1)) = 2)
    (is : List (Fin n)) (v : Fin n → ℤ) :
    dotProduct (is.foldl (fun w i => Etingof.simpleReflection n A i w) v)
      (A.mulVec (is.foldl (fun w i => Etingof.simpleReflection n A i w) v)) =
    dotProduct v (A.mulVec v) := by
  induction is generalizing v with
  | nil => rfl
  | cons j js ih =>
    simp only [List.foldl_cons]
    rw [ih, Etingof.simpleReflection_preserves_bilinearForm A hA j (hroots j)]

end BilinearFormPreservation

section Corollary

/-- **Corollary 6.8.2**: If a vector x can be mapped to a simple root αₚ by a sequence
of simple reflections (as guaranteed by Theorem 6.8.1 for dimension vectors of
indecomposable representations of Dynkin quivers), then B(x, x) = 2, i.e., x is a root.

The proof: since each simple reflection preserves B, and the final result αₚ
satisfies B(αₚ, αₚ) = 2 (the diagonal of the Cartan matrix), we have B(x, x) = 2. -/
theorem Etingof.Corollary6_8_2
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (hA : A.IsSymm)
    (hroots : ∀ i : Fin n, dotProduct (Pi.single i 1) (A.mulVec (Pi.single i 1)) = 2)
    (x : Fin n → ℤ) (hx : x ≠ 0)
    (is : List (Fin n)) (p : Fin n)
    (hrefl : is.foldl (fun w i => Etingof.simpleReflection n A i w) x = Pi.single p 1) :
    Etingof.IsRoot n (2 • (1 : Matrix (Fin n) (Fin n) ℤ) - A) x := by
  constructor
  · exact hx
  · -- B(x, x) = B(sᵢ₁⋯sᵢₘ(x), sᵢ₁⋯sᵢₘ(x)) = B(αₚ, αₚ) = 2
    -- The Cartan matrix for IsRoot is C = 2·I - adj, and A here is C.
    -- We need: dotProduct x (C.mulVec x) = 2
    -- Since reflections preserve B_C and the final value is αₚ with B_C(αₚ, αₚ) = 2:
    have h1 := Etingof.iteratedSimpleReflection_preserves_bilinearForm A hA hroots is x
    rw [hrefl, hroots p] at h1
    -- h1 : 2 = dotProduct x (A.mulVec x)
    -- The IsRoot uses (2 • 1 - adj) as the Cartan matrix, which is A in our setup
    -- We need to convert: the bilinear form B_A(x,x) = dotProduct x (A.mulVec x)
    -- Goal: dotProduct x ((2 • 1 - (2 • 1 - A)).mulVec x) = 2
    -- Simplify: 2 • 1 - (2 • 1 - A) = A
    simp only [sub_sub_cancel]
    linarith

end Corollary
