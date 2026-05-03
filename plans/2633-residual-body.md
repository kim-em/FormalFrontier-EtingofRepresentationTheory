## Current state

Schur-Weyl L_i follow-up. The B-side simplicity clause
`IsSimpleModule (centralizer A) (S i →ₗ[A] V^⊗n)` is exposed at the
bimodule level via `Theorem5_18_4_bimodule_decomposition_explicit`
(see `Chapter5/Theorem5_18_4.lean:464`). The remaining task is to
propagate that clause to the GL_N-representation form.

**Partial progress already merged** (PR #2654, commit
[6f4ceed5](https://github.com/FormalFrontier/Etingof-RepresentationTheory-draft1/commit/6f4ceed5)):
the helper `isSimpleModule_monoidAlgebra_GL_of_centralizer_simple` is
now available in `Chapter5/SchurWeylGLTransfer.lean:553`. Its signature:

```lean
theorem isSimpleModule_monoidAlgebra_GL_of_centralizer_simple
    {N n : ℕ}
    {M : Type*} [AddCommGroup M] [Module k M] [Module.Finite k M]
    [Module (diagonalActionImage k (Fin N → k) n) M]
    [IsScalarTower k (diagonalActionImage k (Fin N → k) n) M]
    [IsSimpleModule (diagonalActionImage k (Fin N → k) n) M]
    [IsAlgClosed k]
    (ρ : Representation k (Matrix.GeneralLinearGroup (Fin N) k) M)
    (h_act : ∀ g x,
        ρ g x = (⟨PiTensorProduct.map (R := k)
              (fun _ : Fin n => Matrix.mulVecLin (R := k) g.val), _⟩ :
              diagonalActionImage k (Fin N → k) n) • x) :
    IsSimpleModule (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k))
      ρ.asModule
```

This subsumes the original Lemma A (centralizer = adjoin via
`Theorem5_18_4_centralizers`) and Lemma B (lattice transfer) of the
original plan. **Only the wrapper theorem itself remains.**

## Deliverables

Add `Theorem5_18_4_GL_rep_decomposition_simple` in
`Chapter5/Theorem5_18_4.lean`, immediately after
`Theorem5_18_4_GL_rep_decomposition` (line 696), with this signature:

```lean
theorem Theorem5_18_4_GL_rep_decomposition_simple
    (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    (N n : ℕ) (hN : n ≤ N) :
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι)
      (S : ι → Type u)
      (_ : ∀ i, AddCommGroup (S i))
      (_ : ∀ i, Module k (S i))
      (_ : ∀ i, Module (symGroupImage k (Fin N → k) n) (S i))
      (_ : ∀ i, IsSimpleModule (symGroupImage k (Fin N → k) n) (S i))
      (_ : ∀ i j,
        Nonempty (S i ≃ₗ[symGroupImage k (Fin N → k) n] S j) → i = j)
      (_ : ∀ i, Module.Finite k (S i))
      (L : ι → FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
      (_ : ∀ i, IsSimpleModule
        (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k))
        (L i).ρ.asModule),
      Nonempty (TensorPower k (Fin N → k) n ≃ₗ[k]
        DirectSum ι (fun i => S i ⊗[k] (L i : Type u)))
```

This is `Theorem5_18_4_GL_rep_decomposition` (line 696) with one extra
clause: `∀ i, IsSimpleModule (MonoidAlgebra k GL_N) (L i).ρ.asModule`,
inserted between the `L` parameter and the iso existential.

## Implementation strategy

1. Destructure both:
   - `Theorem5_18_4_GL_rep_decomposition_explicit k N n hN` — gives the
     concrete `ι`, `S' : ι → Submodule …`, `L : ι → FDRep …`,
     `L_carrier i : (L i : Type u) ≃ₗ[k] (↥(S' i) →ₗ[A] V^⊗n)`, the iso
     `e`, and the action formula
     `(L_carrier i ((L i).ρ g l)) v = PiTensorProduct.map … ((L_carrier i l) v)`.
   - `Theorem5_18_4_bimodule_decomposition_explicit k V n hN'` — gives
     the **same** `ι` + `S'` (since `_explicit` reuses it directly, see
     line 571) plus the centralizer-simplicity clause
     `IsSimpleModule (centralizer …) (S' i →ₗ[A] V^⊗n)`.

   Note that `_explicit` calls `_bimodule_decomposition_explicit`
   internally and forwards its `ι, S'` (line 571), so the two
   destructurings yield the same data — but you may need to call
   `_bimodule_decomposition_explicit` separately to extract the
   `homA_simp` clause that `_explicit` discards. Check whether reusing
   the `_explicit` invocation's intermediate destructure is feasible;
   if not, the two calls produce definitionally compatible data.

2. For each `i`, transfer centralizer-simplicity from
   `↥(S' i) →ₗ[A] V^⊗n` to `(L i : Type u)` via the `L_carrier i`
   isomorphism (use `IsSimpleModule.congr` or
   `LinearEquiv.isSimpleModule`). This requires `L_carrier i` to be
   compatible with the centralizer-action — since both sides have the
   same `Module (centralizer …)` structure (the carrier of `L i` is
   defeq to the hom-space by `FGModuleCat.of_carrier`), this should be
   immediate or follow from `LinearEquiv.refl`.

3. Apply `isSimpleModule_monoidAlgebra_GL_of_centralizer_simple` with
   - `M := (L i : Type u)` (with the now-transferred
     `IsSimpleModule (diagonalActionImage …) M` instance),
   - `ρ := (L i).ρ`,
   - `h_act` from the explicit action formula in
     `_explicit`'s output.

   The `centralizer = diagonalActionImage` identity is via
   `Theorem5_18_4_centralizers` (already used inside `_explicit`).
   Compose with the `IsScalarTower` instance for the centralizer-module
   structure on the hom-space.

4. Assemble the existential. The `S i := ↥(S' i)` (forgetting the
   submodule realisation, as in the existing `_GL_rep_decomposition`
   wrapper at line 711–718).

## Context

* File: `Chapter5/Theorem5_18_4.lean` (add after line 718, before
  `end Etingof`).
* Reference wrapper: `Theorem5_18_4_GL_rep_decomposition` at
  `Theorem5_18_4.lean:696` — this is the existing wrapper to refine.
* Helper: `isSimpleModule_monoidAlgebra_GL_of_centralizer_simple` at
  `SchurWeylGLTransfer.lean:553` (added in PR #2654).
* Centralizer identity: `Theorem5_18_4_centralizers` at
  `Theorem5_18_4.lean:268`.
* Parent issue: #2493 (Schur-Weyl L_i part C: final assembly).

## Verification

* Zero sorries.
* `lake build EtingofRepresentationTheory.Chapter5.Theorem5_18_4` passes.
* The new theorem is downstream-callable from the final-assembly issue
  (#2493) — no other consumers yet.

## Note on the previous body

The original issue body (pre-replan) called for Lemma A + Lemma B + the
wrapper theorem. Lemmas A and B are subsumed by the merged helper
`isSimpleModule_monoidAlgebra_GL_of_centralizer_simple` (PR #2654);
this update narrows the scope to just the wrapper theorem.
