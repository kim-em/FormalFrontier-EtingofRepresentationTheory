# Algorithm A redesign — `garnir_twisted_in_lower_span_aux`

Meditate note for issue [#2660](https://github.com/FormalFrontier/Etingof-RepresentationTheory-draft1/issues/2660).
This file replaces the original Algorithm A outline (issue #2648 / #2652) which
the worker on session `494d71d1` showed to be unsound.  It documents

1. Why the original col-std existence sub-lemma is provably impossible in
   general,
2. A clean reformulation that turns the unsound combinatorial step into a
   well-posed reduction `f_w(σ) ∈ L_σ ⇐ f_w(σ) ∈ V`,
3. Three candidate strategies for closing the residual `f_w(σ) ∈ V` step,
4. The decomposition into single-session follow-up issues.

Future workers MUST read this note before touching
`SpechtModuleBasis.lean:1681` (`garnir_twisted_in_lower_span`).

---

## 1.  Investigation summary

### 1.1 What we are trying to prove

`garnir_twisted_in_lower_span` (`SpechtModuleBasis.lean:1681–1695`) is the
combinatorial heart of the SYT-basis dimension upper bound
`finrank_spechtModule_le_card_syt`.  It says: for col-std `σ` with
`rowInvCount' σ > 0`, and a "Garnir permutation" `w` supported on the
Garnir set `G` with `w ≠ 1`, `w ∉ ColumnSubgroup`, `w ∉ RowSubgroup`,

```
twistedPolytabloid w σ
  = Σ_{q ∈ Q_λ} sign(q) · δ_{[w · q⁻¹ · σ]}
  ∈ L_σ
```

where

```
L_σ := Span_ℂ {  ψ_τ
              | τ : Equiv.Perm (Fin n) col-std,
                ([σ] ≻ [τ])  ∨  ([τ] = [σ]  ∧  rowInvCount' τ < rowInvCount' σ) }
```

and `ψ_τ := generalizedPolytabloidTab τ`.

The proof is to be carried out inside a packed mutual induction on
`(srRank σ, rowInvCount' σ)` lex (issue #2649) where the IH for
`polytabloidTab_column_standard_in_span` is available at strictly smaller
lex measure:

```
IH : ∀ τ' col-std with (srRank τ', rowInvCount' τ') <_lex (srRank σ, rowInvCount' σ),
       ψ_{τ'} ∈ V          (V := Span (polytabloidTab T : T ∈ SYT(λ)))
```

### 1.2 Why the original outline (issue #2648) cannot work

The original sketch peeled off `α* ∈ supp(twistedPolytabloid w σ)` by
dominance and dispatched on whether `α*` admits a "good" col-std
representative `τ_{α*}` at the SAME tabloid (`[τ_{α*}] = [α*]`) with the
right strict-dominance / smaller-rowInv property.

Worker session `494d71d1` proved this dispatch unsound:

* **Construction failure** (skip comment on #2652, paragraphs 1–4):
  Starting from `[w q⁻¹ σ] = [σ]` we get `p := w q⁻¹ ∈ P_λ`.  The natural
  candidate `p · σ` is row-equivalent to `σ` but NOT col-std in general.
  Column-restandardising via `γ ∈ Q_λ` requires `γ ∈ P_λ ∩ Q_λ = {1}` to
  preserve the tabloid, so `γ = 1` only when `p · σ` is *already* col-std,
  which is a non-trivial side condition.

* **Sharper counter-example** (skip comment, second sub-section):
  taking the row-inversion pair `(p₁, p₂)` and applying
  `t = swap(p₁, p₂) ∈ P_λ` does decrease `rowInvCount'`, but `t · σ` is
  generally not col-std either: the col-std condition involves entries in
  *other* rows of the two affected columns, none of which are touched by
  `t`.

* **Existence-impossible counter-example** (this note, §4):
  for `λ = (2,2)`, the tabloid `[{2,3} | {0,1}]` has NO col-std
  representative at all, regardless of the construction used.  See §4
  for the elementary parity proof.  Hence the original dispatch is not
  rescuable by changing the construction; it is the *target* that does
  not exist.

### 1.3 The clean reformulation

The key observation that the original outline missed is that we already
have *two* perfectly good bridges in the file, both proved without
reference to col-std existence:

**Bridge A** (`polytabloidTab_in_lower_span_of_dominates`,
`SpechtModuleBasis.lean:1404`): for col-std `σ` with `rowInvCount' σ > 0`
and any SYT `T` with `[T] ≼ [σ]`,

```
polytabloidTab T  ∈  L_σ.
```

Hence `Span (polytabloidTab T : [T] ≼ [σ])  ⊆  L_σ`.

**Bridge B** (`tabloidSupport_straightening`,
`SpechtModuleBasis.lean:1260`): for any `v` in `V := Span (polytabloidTab T : T ∈ SYT(λ))`
whose tabloid support is bounded by `[σ]`,

```
v  ∈  Span (polytabloidTab T : [T] ≼ [σ]).
```

**Composition**.  If `v ∈ V` *and* `supp(v) ≼ [σ]` (which is exactly
what `twistedPolytabloid_support_bound` gives), then
`v ∈ Span (polytabloidTab T : [T] ≼ [σ]) ⊆ L_σ`.

So: **closing `garnir_twisted_in_lower_span_aux` is equivalent to
proving `f_w(σ) ∈ V`** (under the IH that ψ_{τ'} ∈ V at strictly smaller
lex).

This reformulation is the redesign.  It has two virtues:

* It **eliminates** the impossible col-std existence sub-lemma.
* It exposes the residual problem (`f_w(σ) ∈ V`) as a *fundamentally
  different* question — about how the Garnir-twisted sum embeds into the
  Specht module — for which several attack lines exist.

### 1.4 What does NOT close the residual problem

Two natural ideas FAIL.  Future workers should not retry these:

* **`f_w(σ) = w · ψ_σ` via S_n-invariance of V.**  In the standard
  representation theory, `V = tabloidProjection(SpechtModule)` is
  S_n-invariant.  But the Lean-side identification
  `Span (polytabloidTab T : T ∈ SYT(λ)) = tabloidProjection(SpechtModule)`
  is itself the dimension upper bound we are proving; the inclusion `≥`
  for that identity uses
  `generalizedPolytabloidTab_mem_span_polytabloidTab`, which IS the
  straightening theorem.  So invoking S_n-invariance of `V` *now* is
  circular.  See `SpechtModuleBasis.lean:2354` for the wrapper, and
  `tabloidProjection_spechtModule_le_span` (line 2391) for the existing
  one-direction inclusion.

* **Term-by-term polytabloid expansion.**  Expanding each
  `δ_{[w q⁻¹ σ]}` into a polytabloid by column-restandardising
  `w q⁻¹ σ` (yielding col-std `τ_q := γ_q · w q⁻¹ σ` via
  `garnirColReindex`) does not work cleanly:
  - `[τ_q] ⪰ [w q⁻¹ σ]` (col-restand can only INCREASE dominance),
  - but `[τ_q]` may be `≻ [σ]` strictly, in which case
    `(srRank τ_q, rowInvCount' τ_q)` could exceed `(srRank σ, rowInvCount' σ)`
    in lex order, and the IH does not apply.

  See §3.3 for why the "Q_high" residue is the obstruction.

---

## 2.  Redesigned Algorithm A

### 2.1 Top-level structure

```lean
private theorem garnir_twisted_in_lower_span_aux
    (σ : Equiv.Perm (Fin n)) (hcs : isColumnStandard' n la σ)
    (hrp : 0 < rowInvCount' (la := la) σ)
    (G : Finset (Fin n)) (w : Equiv.Perm (Fin n))
    (hw_supp : ∀ x, x ∉ G → w x = x)
    (hw_ne : w ≠ 1) (hw_col : w ∉ ColumnSubgroup n la)
    (hw_row : w ∉ RowSubgroup n la)
    (ih : ∀ τ', isColumnStandard' n la τ' →
          ((srRank la τ' < srRank la σ) ∨
           (srRank la τ' = srRank la σ ∧
            rowInvCount' (la := la) τ' < rowInvCount' (la := la) σ)) →
          ψ_{τ'} ∈ V) :
    twistedPolytabloid (la := la) w σ ∈ L_σ := by
  -- Reduction step (NEW):  reduce `_ ∈ L_σ` to `_ ∈ V`.
  --   bridge_A_B : ∀ v, v ∈ V → supp(v) ≼ [σ] → v ∈ L_σ
  --   support_bd : supp(twistedPolytabloid w σ) ≼ [σ]
  --                                       (twistedPolytabloid_support_bound)
  -- Hence it suffices to show `twistedPolytabloid w σ ∈ V`.
  apply bridge_A_B
  · exact twistedPolytabloid_support_bound σ hcs w
  -- Residual claim:  twistedPolytabloid w σ  ∈  V.
  -- Discharged by `twistedPolytabloid_mem_V` (Algorithm A core, §3).
  exact twistedPolytabloid_mem_V σ hcs hrp w hw_supp hw_ne hw_col hw_row ih
```

`bridge_A_B` is the composition of `tabloidSupport_straightening` with
`polytabloidTab_in_lower_span_of_dominates`; the proof is purely
mechanical (~25–40 lines).

`twistedPolytabloid_mem_V` is the residual claim:

```lean
twistedPolytabloid_mem_V :
  ∀ σ col-std, rowInv σ > 0,
    ∀ w "Neither" supported on G,
      ∀ IH, twistedPolytabloid w σ ∈ V
```

This is the actual Algorithm A core; it is **not** trivial and is itself
the subject of §3.

### 2.2 The reduction step in detail

The `bridge_A_B` lemma:

```lean
/-- If `v ∈ V` (the SYT polytabloid span) and `supp(v) ≼ [σ]`,
then `v ∈ L_σ`. -/
private lemma in_L_of_in_V_of_supp_bounded
    (σ : Equiv.Perm (Fin n)) (hcs : isColumnStandard' n la σ)
    (hrp : 0 < rowInvCount' (la := la) σ)
    (v : TabloidRepresentation n la)
    (hv_V : v ∈ Submodule.span ℂ (Set.range (fun T : StandardYoungTableau n la =>
              polytabloidTab (n := n) (la := la) T)))
    (hv_supp : ∀ α, v (toTabloid n la α) ≠ 0 → tabloidDominates la σ α) :
    v ∈ L_σ := by
  -- Step 1: tabloidSupport_straightening σ hcs v hv_V hv_supp gives
  --         v ∈ Span (polytabloidTab T : [T] ≼ [σ])
  have h_step1 := tabloidSupport_straightening σ hcs v hv_V hv_supp
  -- Step 2: that span sits inside L_σ via Bridge A.
  refine Submodule.span_le.mpr ?_ h_step1
  rintro _ ⟨⟨T, hT_dom⟩, rfl⟩
  exact polytabloidTab_in_lower_span_of_dominates σ hrp T hT_dom
```

Both `tabloidSupport_straightening` and
`polytabloidTab_in_lower_span_of_dominates` already exist in the file
(lines 1260 and 1404).  This reduction lemma is ~25 lines and can land
as a standalone PR independent of any further algorithmic decisions.

### 2.3 Validating the reduction on the [σ] = [α] case

The original's pain point — the `[σ] = [α]` case — disappears under the
new framework: it is no longer a case; it is part of the support-bound
condition `[α] ≼ [σ]`.  Once we know `f_w(σ) ∈ V`, the existing bridge
lemma `polytabloidTab_in_lower_span_of_dominates` handles
`[T] = [σ] ∧ rowInvCount' T = 0 < rowInvCount' σ` automatically (via
its `Or.inr` branch), with NO appeal to col-std-existence at the same
tabloid.

This is the crux of why the redesign works:  the col-std existence
sub-lemma is no longer needed *anywhere* in the proof.

---

## 3.  The residual claim:  `twistedPolytabloid w σ ∈ V`

This is the new combinatorial heart of the proof.  Three attack lines
are visible; (3.1) is the most promising.

### 3.1 Strategy A:  per-q dispatch via column-restandardisation + IH

For each `q ∈ Q_λ`, define `τ_q := garnirColReindex σ w q · w · q⁻¹ · σ`,
which is col-std and satisfies `[τ_q] ⪰ [w · q⁻¹ · σ]` (column moves
take col-std forms to dominance-greater tabloids).  `τ_q` lives in one
of three regions:

```
Q_low := { q | [τ_q] ≺ [σ] }                       -- IH applies
Q_eq  := { q | [τ_q] = [σ] ∧ rowInv τ_q < rowInv σ}-- IH applies
Q_eq' := { q | [τ_q] = [σ] ∧ rowInv τ_q ≥ rowInv σ}-- IH does NOT apply
Q_high:= { q | [τ_q] ≻ [σ] }                       -- IH does NOT apply
```

For `Q_low ∪ Q_eq` the IH gives `ψ_{τ_q} ∈ V`.  Each
`δ_{[w q⁻¹ σ]} = δ_{[γ_q⁻¹ τ_q]}` is the `(q' = γ_q)` term of
`ψ_{τ_q}`, so it can be expressed as

```
δ_{[w q⁻¹ σ]}  =  sign(γ_q) · ψ_{τ_q}
                 - sign(γ_q) · Σ_{q' ∈ Q_λ, q' ≠ γ_q} sign(q') · δ_{[q'⁻¹ τ_q]}
```

Substituting back into `f_w(σ)` yields

```
f_w(σ) =   Σ_{q ∈ Q_low ∪ Q_eq} sign(q) sign(γ_q) ψ_{τ_q}        (*)
         + (residual sum involving δ_{[q'⁻¹ τ_q]} for q' ≠ γ_q)
         + Σ_{q ∈ Q_eq' ∪ Q_high} sign(q) δ_{[w q⁻¹ σ]}.            (**)
```

Term (*) is in `V` by IH.  The residual sums need to vanish or to be
re-handled in `V`.  This is where the work is.

**Sub-claim 3.1.1** (residual cancellation):  the residual terms
involving `δ_{[q'⁻¹ τ_q]}` for `q' ≠ γ_q` rearrange into a sum that is
itself supp-bounded by `[σ]` and can be inducted on (multi-set-wise
strictly smaller than the original `f_w(σ)` support).

**Sub-claim 3.1.2** (Q_high vanishing):  the sum
`Σ_{q ∈ Q_high} sign(q) δ_{[w q⁻¹ σ]}` is zero by a sign-reversing
involution analogous to the one in
`twistedPolytabloid_apply_of_not_dominates`
(`SpechtModuleBasis.lean:1475`).  The intuition: Q_high arises only
when `w q⁻¹ σ` has a column "overflow" similar to the
`twistedPolytabloid_pigeonhole_pair` setup, and the corresponding
involution cancels these terms.

**Sub-claim 3.1.3** (Q_eq' equals empty):  for `q ∈ Q_eq'` we have
`[τ_q] = [σ]` AND `rowInv τ_q ≥ rowInv σ`.  Since `τ_q` is col-std with
the same tabloid as `σ`, and `σ` is also col-std, in fact
`τ_q = γ_q · w q⁻¹ σ` and `[τ_q] = [σ]` forces additional algebraic
identities that may yield `τ_q = σ` (hence `rowInv τ_q = rowInv σ`,
not strict).  But then `q · w⁻¹` lies in `P_λ`, hence
`w ∈ q⁻¹ P_λ ⊆ P_λ Q_λ`; combined with `w ∉ P_λ ∪ Q_λ`, this is
non-trivial.  The hope is that `Q_eq'` is in fact empty for "Neither"
`w`, but this needs verification.

**Status**: 3.1.1 is the most plausible (residual cancellation is
standard in straightening-style arguments).  3.1.2 is plausible but
requires constructing an explicit involution and verifying its
sign-reversing / Q-stability properties.  3.1.3 is speculative and
may be the hardest.

### 3.2 Strategy B:  prove `f_w(σ) ∈ V` non-constructively via the global Garnir identity

The Garnir identity `garnir_polytabloid_identity`
(`SpechtModuleBasis.lean:731`) gives

```
ψ_σ  =  −Σ_{w ≠ 1, supp w ⊆ G} sign(w) · twistedPolytabloid w σ.
```

Splitting the right-hand side as in the existing `garnir_straightening_step`,

```
ψ_σ  =  −(k · ψ_σ)  −  (Σ_{P\Q} ±ψ_σ)  −  (Σ_{Neither} sign(w) · f_w(σ))
```

so

```
(Σ_{Neither} sign(w) · f_w(σ))  =  −(constant) · ψ_σ
                                   ∈ V (under IH for ψ_σ),
```

where the "constant" depends on `k`.  This gives the SUM over Neither
`w`s in `V`, NOT each `f_w(σ)` individually.

If we set up the induction so that we only need the SUM (not individual
`f_w(σ)`), this strategy could close the proof immediately.

**Sub-claim 3.2.1** (architectural): refactor `garnir_straightening_step`
so that the call site of `garnir_twisted_in_lower_span` consumes only
the Neither-SUM-membership (in `L_σ` or `V`), not per-`w` membership.
The current split into per-`w` lemmas is an artefact of an earlier
design.

**Status**: This is architecturally cleaner but requires care: the
`(k=0)` corner case currently uses a per-`w` step (`t·σ` with same
tabloid), so the refactor is non-trivial.  Also, the IH for `ψ_σ`
inside the `garnir_straightening_step` proof of `ψ_σ` is itself
circular (we are trying to prove `ψ_σ ∈ V`).

Closer inspection: the right-hand side `(Σ_{Neither}) = −(constant) · ψ_σ`
gives `Σ_{Neither} ∈ V ⇔ ψ_σ ∈ V` (assuming constant ≠ 0).  These are
*equivalent*, so this strategy is **circular** for the OUTER goal.
Strategy B is therefore ruled out.

### 3.3 Strategy C:  prove `f_w(σ) ∈ V` via a *coarser* support filtration

Instead of inducting on `(srRank, rowInv)` lex, induct on a coarser
measure that treats `Q_high` correctly.

**Idea**: replace `srRank` (which counts strict-dominators of `σ`'s
tabloid) with a measure that counts strict-dominators in the
*sub-poset* `{[α] : [α] ≼ [σ]}`.  Then for `τ_q` with `[τ_q] ≻ [σ]`,
`τ_q` is OUTSIDE the sub-poset and is handled by a base-case argument
(e.g., the IH at the *outer* level, since `[τ_q] ≻ [σ]` reduces
absolute srRank).

**Status**: Requires a new measure and re-doing the well-foundedness
proof.  Overlaps with Strategy A's Q_high handling; if Strategy A
3.1.2 works, this strategy is unnecessary.

### 3.4 Recommended strategy

**Strategy A**, with the following decomposition:

1. Land the reduction `garnir_twisted_in_lower_span_aux ⇐ f_w(σ) ∈ V`
   first (≤ 60 lines, no algorithmic novelty).
2. Investigate sub-claim 3.1.3 (`Q_eq' = ∅` for "Neither" `w`).  If
   true, the proof simplifies considerably.
3. Investigate sub-claim 3.1.2 (Q_high vanishing involution).  This is
   the most novel piece; another meditate task may be required if the
   investigation does not yield a clean involution.
4. Assemble the per-q dispatch + residual induction in
   `twistedPolytabloid_mem_V`.

If 3.1.2 turns out infeasible after dedicated investigation, escalate
back to a meditate task with the new findings, OR pivot to
Strategy C.

---

## 4.  Counter-example record

### 4.1 `λ = (2,2)`, tabloid `[{2,3} | {0,1}]` has NO col-std representative

Cited by worker `494d71d1` on issue #2652 as the example that rules
out the "find any col-std rep at the same tabloid" construction.

**Claim**: there is no permutation `α : Equiv.Perm (Fin 4)` such that
- `toTabloid 4 (2,2) α = [{2,3} | {0,1}]`, AND
- `α` is col-std (`isColumnStandard' 4 (2,2) α`).

**Proof**.  For `λ = (2,2)`, the canonical row/column structure assigns
positions `0, 1` to row 0 (cells (0,0), (0,1)) and positions `2, 3` to
row 1 (cells (1,0), (1,1)).

`α` having `[{2,3} | {0,1}]` means the entries in positions `{0,1}`
under `α` are `{2,3}` (in some order) and the entries in positions
`{2,3}` are `{0,1}` (in some order).  Equivalently, `α(0), α(1) ∈ {2,3}`
and `α(2), α(3) ∈ {0,1}`.

Col-std for `α` requires (using `α.symm` to read entries by position):

* In column 0 (positions 0 and 2): `α.symm(σ_pos(0,0)) < α.symm(σ_pos(1,0))`
  where `σ_pos(r,c)` denotes the position assigned to cell `(r,c)`.
  Concretely, this means the entry-index in `Fin 4` for the cell
  `(0,0)` is smaller than that for `(1,0)`.  In our setup: `α.symm`
  evaluated at the column-0 entries.

The cleanest way: the col-std condition `α.symm p₂ > α.symm p₁` for
`p₁` strictly above `p₂` in the same column means "positional indices
along the column increase from top to bottom".  Equivalently, the entry
`α(top of column)` is the smaller one in that column.

Plugging in: in column 0, `α(0)` (top) must be smaller than `α(2)`
(bottom).  But `α(0) ∈ {2,3}` and `α(2) ∈ {0,1}`, so `α(0) > α(2)`.
Contradiction.

Hence no col-std `α` has the desired tabloid.  The original "find a
col-std rep" sub-lemma fails here.

### 4.2 `λ = (2,2)`, σ = swap(0,1) is the head of a non-trivial example

Same setup, with `σ = swap(0,1)` chosen as the OUTER variable.
`σ` is col-std, `rowInv σ = 1` (the pair (positions 0, 1) in row 0).

The Garnir straightening step applied to `σ` produces a "Neither" sum
that, after expansion, contains the tabloid `[{2,3} | {0,1}]` in its
support — the very tabloid that has no col-std representative.

This is the smallest concrete configuration where the unsoundness of
the original outline manifests.  Future workers can use this as the
running example when validating any redesign.

### 4.3 Other partitions

The same impossibility extends to any `λ ⊢ n` with at least two parts
of size ≥ 2 (e.g., `(3,2)`, `(2,2,1)`).  The general phenomenon is:
tabloids with "rows reversed" relative to the canonical partition order
admit no col-std representatives because col-std forces top-of-column
entries to be smaller than bottom-of-column entries, which contradicts
the row-reversal.

A useful necessary condition for `[α]` to admit a col-std rep at all:
**every column of `[α]` must contain a "column-decreasing" pair** of
entries from the smallest available subset, in the sense that the
multiset of column entries can be reordered top-to-bottom in increasing
order.  If `[α]` violates this, no col-std rep exists.  This condition
is non-trivial and depends on the partition structure.

### 4.4 `Q_eq' ≠ ∅` for "Neither" `w` (refutes Sub-claim 3.1.3)

Documented in detail in `progress/q-high-involution.md` §2.5 / §6.1
(the R3 meditate for issue #2676).

**Setup**: λ = (2,2), σ = swap(0,1) (col-std, rowInv 1, [σ] is the
maximum tabloid). w = (0 2 1) cycle (∈ Neither, supported on the
canonical Garnir set G = {0, 1, 2} for the (0, 1) row inversion).

**Witness**: at q = swap(1,3), the col-restandardisation forces
γ_q = swap(0,2)·swap(1,3), giving τ_q = swap(0,1)·swap(2,3) col-std
with [τ_q] = [σ] AND rowInv τ_q = 2 ≥ 1 = rowInv σ. Hence
q ∈ Q_eq', refuting the redesign note's §3.1's Sub-claim 3.1.3
(`Q_eq' = ∅`).

**Implication**: Strategy A's per-q dispatch must be AGGREGATED
(Strategy A*) to handle Q_eq' and Q_low ∪ Q_eq residuals together.
The "Q_high involution" originally scoped as Sub-claim 3.1.2 is
REPLACED by a residual cancellation argument that acts on a different
group of terms — see `q-high-involution.md` §3 for Strategy A* and §4
for the R2.a / R2.b / R2.c re-decomposition.

**Future workers**: do NOT retry "prove Q_eq' = ∅". The above is a
direct refutation by explicit witness.

---

## 5.  Re-decomposition into follow-up issues

The redesign decomposes into THREE follow-up issues, in dependency
order.  All three replace the current `garnir_twisted_in_lower_span_aux`
(former #2648) target.

### 5.1 Issue R1 (small, foundational): `feat(Ch5): bridge `f_w(σ) ∈ V → ∈ L_σ`

**Title**:  `feat(Ch5): in_L_of_in_V_of_supp_bounded — Bridge from V-membership to L_σ`

**Scope**:  ~60 lines in `SpechtModuleBasis.lean`, immediately after
`polytabloidTab_in_lower_span_of_dominates` (line 1426) and before
`twistedPolytabloid_pigeonhole_pair` (line 1444).

**Statement**: see §2.2 (`in_L_of_in_V_of_supp_bounded`).

**Proof**: composition of `tabloidSupport_straightening` and
`polytabloidTab_in_lower_span_of_dominates` via `Submodule.span_le.mpr`.

**Dependencies**: none (both inputs are already merged).

**Sizing**: 1 small session, ≤ 60 lines, ≤ 1 file.  Suitable as a
warm-up immediately after this meditate lands.

### 5.2 Issue R2 (medium, investigation + structural): `feat(Ch5): twistedPolytabloid_mem_V — Algorithm A reformulated`

**Title**:  `feat(Ch5): Algorithm A (V-side) — twistedPolytabloid_mem_V via per-q dispatch + residual induction`

**Scope**:  ~150–250 lines in `SpechtModuleBasis.lean`, replacing the
sorry'd `garnir_twisted_in_lower_span` body (line 1681).  Adds the new
helper `twistedPolytabloid_mem_V` and re-derives
`garnir_twisted_in_lower_span` as a corollary via Issue R1.

**Statement**:
```lean
private theorem twistedPolytabloid_mem_V
    (σ : Equiv.Perm (Fin n)) (hcs : isColumnStandard' n la σ)
    (hrp : 0 < rowInvCount' (la := la) σ)
    (G : Finset (Fin n)) (w : Equiv.Perm (Fin n))
    (hw_supp : ∀ x, x ∉ G → w x = x)
    (hw_ne : w ≠ 1) (hw_col : w ∉ ColumnSubgroup n la)
    (hw_row : w ∉ RowSubgroup n la)
    (ih : ∀ τ', isColumnStandard' n la τ' →
          ((srRank la τ' < srRank la σ) ∨
           (srRank la τ' = srRank la σ ∧
            rowInvCount' (la := la) τ' < rowInvCount' (la := la) σ)) →
          ψ_{τ'} ∈ V) :
    twistedPolytabloid (la := la) w σ ∈ V
```

**Proof outline**: see Strategy A in §3.1.  The key sub-lemmas are
3.1.1 (residual cancellation) and 3.1.2 (Q_high vanishing).
3.1.3 should be either proved (then Q_eq' is empty and the dispatch
simplifies) or routed through 3.1.1.

**Dependencies**: depends on R1 (for the corollary derivation of
`garnir_twisted_in_lower_span`) and on issue #2649 (the architectural
restructure that wires the IH through).

**Sizing**: 1 large session OR 2 medium sessions.  If the worker finds
3.1.2 (Q_high vanishing involution) infeasible within budget, they
should split off R3 below.

### 5.3 Issue R3 (only if R2 stalls): `meditate(Ch5): Q_high cancellation involution for twistedPolytabloid_mem_V`

**Title**:  `meditate(Ch5): construct sign-reversing involution on Q_high — twistedPolytabloid sub-cancellation`

**Scope**:  follow-up meditate IF R2 worker hits the Q_high problem
and cannot find an involution.  Investigates whether
`Σ_{q ∈ Q_high} sign(q) δ_{[w q⁻¹ σ]} = 0` holds via a sign-reversing
involution similar to `twistedPolytabloid_apply_of_not_dominates`
(line 1475).

**Output**:  meditate note `progress/q-high-involution.md`, either with
an explicit involution + correctness sketch, or a documented
infeasibility result that triggers a pivot to Strategy C (§3.3).

**Dependencies**: R2 in-progress.  This issue is conditional and should
be created only if R2's worker requests it via a `replan` or a
`Decomposed into …` breadcrumb.

---

## 6.  Verification checklist for the redesign

The redesign is "successful" if:

1. ✅ `polytabloidTab_in_lower_span_of_dominates` (the bridge in §1.3)
   already exists and is sufficient.  No new combinatorial bridge
   lemma is needed.
2. ✅ `tabloidSupport_straightening` (the second bridge) already
   exists.  No new combinatorial bridge lemma is needed.
3. ✅ The reduction `garnir_twisted_in_lower_span_aux ⇐ f_w(σ) ∈ V`
   is mechanical (Issue R1).
4. ⚠ Closing `f_w(σ) ∈ V` requires Strategy A or C, with non-trivial
   investigation.  Issue R2 captures the work; R3 is a contingency.
5. ✅ The col-std existence sub-lemma is **eliminated entirely** from
   the proof obligation.  The counter-example `[{2,3} | {0,1}]` no
   longer needs to be addressed; it simply contributes to
   `supp(f_w(σ))` like any other tabloid and is handled by the bridges.

The big architectural win: by routing through `V` rather than
constructing per-tabloid col-std reps, the redesign **respects** the
counter-example instead of fighting it.

---

## 7.  Files of interest (for the next worker)

- `EtingofRepresentationTheory/Chapter5/SpechtModuleBasis.lean`
  - line 1260: `tabloidSupport_straightening` (Bridge B)
  - line 1404: `polytabloidTab_in_lower_span_of_dominates` (Bridge A)
  - line 1444: `twistedPolytabloid_pigeonhole_pair` (sign-cancellation
    skeleton, useful precedent for Q_high involution in §3.1.2)
  - line 1475: `twistedPolytabloid_apply_of_not_dominates`
    (sign-cancellation EXAMPLE that should be the model for
    Sub-claim 3.1.2)
  - line 1612–1643: `twistedPolytabloid_support_bound`
  - line 1681: `garnir_twisted_in_lower_span` (the sorry to close)
  - line 925–976: `garnirColReindex` family (col-restandardisation
    machinery used in §3.1)
- `EtingofRepresentationTheory/Chapter5/TabloidModule.lean`
  - line 320: `tabloidDominates`
  - line 325: `tabloidStrictDominates`
  - line 938: `polytabloidTab`
  - line 1092: `generalizedPolytabloidTab`
  - line 1228: `tabloidProjection`
  - line 1274: `tabloidProjection_of_mul` (the equivariance fact;
    relevant to ruling out the failed S_n-invariance approach §1.4)

The next planner should create issue R1 from this note immediately.
R2 should be created at the same time but marked
`depends-on: R1, #2649`.  R3 is contingent and should NOT be created
upfront.
