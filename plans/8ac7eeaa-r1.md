## Current state

`EtingofRepresentationTheory/Chapter5/SpechtModuleBasis.lean` has two
existing bridges that, when composed, reduce
`v ∈ L_σ` to `v ∈ V ∧ supp(v) ≼ [σ]`:

- `polytabloidTab_in_lower_span_of_dominates` (line 1404) —
  `polytabloidTab T ∈ L_σ` whenever `[T] ≼ [σ]`.
- `tabloidSupport_straightening` (line 1260) — for `v ∈ V` with
  tabloid support bounded by `[σ]`,
  `v ∈ Span (polytabloidTab T : [T] ≼ [σ])`.

These are not yet packaged as a single bridge, but doing so is the
foundational reduction for the redesigned Algorithm A (see
`progress/algorithm-A-redesign.md`, §2.2). Once available, it lets
`garnir_twisted_in_lower_span_aux` be expressed as

```
twistedPolytabloid w σ ∈ L_σ
  ⇐ twistedPolytabloid w σ ∈ V         (residual, see R2)
    ∧ supp(twistedPolytabloid w σ) ≼ [σ]   (twistedPolytabloid_support_bound)
```

eliminating the unsound col-std existence sub-lemma that the
former #2648 / #2652 outline depended on.

## Deliverables

1. Add the lemma `in_L_of_in_V_of_supp_bounded` to
   `EtingofRepresentationTheory/Chapter5/SpechtModuleBasis.lean`,
   immediately after `polytabloidTab_in_lower_span_of_dominates`
   (line 1426) and before `twistedPolytabloid_pigeonhole_pair`
   (line 1444):

   ```lean
   /-- If `v ∈ V` (the SYT polytabloid span) and every tabloid in
   the support of `v` is dominated by `[σ]`, then `v ∈ L_σ`. -/
   private lemma in_L_of_in_V_of_supp_bounded
       (σ : Equiv.Perm (Fin n)) (hcs : isColumnStandard' n la σ)
       (hrp : 0 < rowInvCount' (la := la) σ)
       (v : TabloidRepresentation n la)
       (hv_V : v ∈ Submodule.span ℂ
                 (Set.range (fun T : StandardYoungTableau n la =>
                    polytabloidTab (n := n) (la := la) T)))
       (hv_supp : ∀ α, v (toTabloid n la α) ≠ 0 →
                       tabloidDominates la σ α) :
       v ∈ L_σ
   ```

   (Use the actual `L_σ` definition / abbreviation that
   `garnir_twisted_in_lower_span` targets. Match argument order
   with the existing bridges so call sites are mechanical.)

2. Prove it as the composition of the two existing bridges:
   - apply `tabloidSupport_straightening σ hcs v hv_V hv_supp`
     to land `v ∈ Span (polytabloidTab T : [T] ≼ [σ])`;
   - lift via `Submodule.span_le.mpr`, mapping each
     `polytabloidTab T` (with `[T] ≼ [σ]`) into `L_σ` using
     `polytabloidTab_in_lower_span_of_dominates σ hrp T hT_dom`.

3. Add a 1-line doc comment pointing to
   `progress/algorithm-A-redesign.md §2.2` for the rationale.

## Context

- **Parent**: #2605 → meditate #2660 → redesign note
  `progress/algorithm-A-redesign.md` (R1).
- **Foundational**: this is the small bridge lemma in §5.1 of the
  redesign note. It has **no dependencies** — both inputs are
  already merged. Suitable as a warm-up issue immediately after the
  meditate landed.
- The lemma is consumed by R2
  (`twistedPolytabloid_mem_V` / `garnir_twisted_in_lower_span`
  closure) and is the first piece of the Algorithm A redesign.

## Verification

- `lake build EtingofRepresentationTheory.Chapter5.SpechtModuleBasis`
  succeeds.
- Full `lake build` succeeds.
- Sorry count unchanged (this is a pure helper addition; the sorry
  on `garnir_twisted_in_lower_span` at line 1681 is closed by R2,
  not here).
- The new lemma has no `sorry` in its body.
- The proof is ≤ 60 lines.
