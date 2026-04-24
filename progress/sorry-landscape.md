# Sorry Landscape Analysis — Wave 56

Generated 2026-04-24 by summarize session (issue #2546).

## Summary

**8 sorries** across 4 files (up from 7/4 in wave 55). The raw count
rose by one, but the landscape improved: **Wall 2 closed entirely**
(the `dTildeRep_mapLinear_transport` residual landed via PR #2495), and
**both new sorries are decomposition anchors** introduced deliberately
as part of active chains (Wall 3 C.1.a.ii and Schur-Weyl equivariance).
No new wall; no surprise sorries.

283 of 286 Lean files (98.9%) are sorry-free. 582/583 items (99.8%)
sorry-free.

**Definition-level sorries: 0.** All mathematical objects are constructed.

### Key story for wave 56

- **Wall 1 (Ẽ/T framework, Kim's decision):** unchanged. 3 sorries; same
  framework refutation as wave-55. Issue #2436 still `human-oversight`,
  still awaiting Kim's option choice (A / B / A+C / B+C). This is now
  the longest-running open item in the project.
- **Wall 2 (D̃_n indecomposability):** **CLOSED.** PR #2495
  (`dTildeRep_mapLinear_transport` via `dTildeCast` refactor) landed
  early in the wave, followed by style cleanup #2517/#2524. Wave-55's
  "mechanical residual" is gone. Ch6 Wall 2 line is now sorry-free.
- **Wall 3 (Garnir straightening):** **decomposed into a concrete
  multi-issue chain.** Parent #2450 broke into A/B/C, then C broke into
  C.1/C.2, then C.1 broke into C.1.a/C.1.b/C.1.c. Part A (`garnirColReindex`,
  PR #2503), Part B (`garnir_pigeonhole_collapse`, PR #2505), C.1 meditate
  (PR #2529), and C.1.a partial (support bound main theorem proved,
  helpers sorry'd — PR #2536) all landed. The chain's remaining sorries
  are `twistedPolytabloid_pigeonhole_pair` (PR #2550 open), and
  `garnir_twisted_in_lower_span` (final assembly, blocked).
- **Schur-Weyl chain:** **sub-issues #2a/#2b/#3 Part A landed; character
  identity skeleton + equivariance sorry introduced by design.**
  Chain makes heavy progress: the polynomial-tensor bridge (#2502),
  polynomial-rep embedding with injection + equivariance (#2528, #2538,
  #2539), `hP_mul` derivation (#2551), L_i FDRep structure (#2504),
  character additivity (#2516), trivial-tensor character
  multiplicativity (#2534), explicit bimodule with evaluation formula
  (#2509), and character-identity skeleton (#2542) all merged. The
  skeleton intentionally sorries a single equivariant Schur-Weyl
  decomposition theorem (now issue #2540), plus the parent
  `iso_of_formalCharacter_eq_schurPoly` remains for #6 (#2483).

### Merges since wave 55 (36 PRs, 2026-04-24T00:14Z → 2026-04-24T10:06Z):

Tabulated in chronological order. "Sorry Impact" annotates the
net-of-this-wave effect on the raw sorry count.

| PR | Time (UTC) | Title | Sorry Impact |
|----|-----------:|-------|--------------|
| #2480 | 03:17 | summarize: wave-55 sorry landscape + design-walls refresh | Docs |
| #2484 | 03:26 | progress: planner triage — close 4 replan, file Schur-Weyl #5 + #6 | Docs |
| #2485 | 03:32 | progress: planner cycle — no new work, cascade healthy | Docs |
| #2481 | 03:34 | feat(Ch5): upgrade Theorem5_18_4_decomposition using bimodule form | Infra |
| #2487 | 03:37 | progress: planner cycle — merge #2481, unblock #2458, file #2486 | Docs |
| #2488 | 03:47 | doc: #2450 skip analysis — whole-sum strategy validated on λ=(2,2) | Docs |
| #2490 | 03:51 | review(Ch5): bimodule foundation audit — sound, filed #2489 | Review |
| #2494 | 04:02 | doc: decompose #2458 (Schur-Weyl L_i identification) into #2491/2/3 | Docs |
| #2495 | 04:04 | feat(Ch6): close `dTildeRep_mapLinear_transport` (Wall 2 residual) | **−1** (Wall 2 ✓) |
| #2501 | 04:18 | progress: planner cycle — close #2458, decompose #2450 into 4 sub-issues | Docs |
| #2502 | 04:19 | feat(Ch5): polynomial-tensor bridge construction + injectivity | Infra |
| #2503 | 05:04 | feat(Ch5): Wall 3 #2450 part A — column-restandardizer API | Infra |
| #2504 | 05:07 | Schur-Weyl L_i (part A): endow bimodule L_i with FDRep GL_N structure | Infra |
| #2505 | 05:30 | feat(Ch5): Wall 3 #2450 part B — pigeonhole collapse lemma | Infra |
| #2508 | 05:34 | progress: planner cycle — close #2477, file 2 review issues | Docs |
| #2513 | 05:47 | review(Ch5): audit PolynomialTensorBridge — all 7 questions Pass | Review |
| #2516 | 05:55 | feat(Ch5 #2492): formalCharacter additivity over direct-sum reps | Infra |
| #2509 | 05:59 | feat(Ch5): explicit bimodule decomposition with evaluation formula | Infra |
| #2521 | 06:04 | progress: /work — decompose #2499 (Wall 3 part C) into #2519 + #2520 | Docs |
| #2523 | 06:26 | progress: /work — decompose #2519 (Wall 3 C.1) into #2522 (meditate) | Docs |
| #2524 | 06:28 | review-finding(Ch6): `dTildeRep_mapLinear_transport` show → change | Style |
| #2525 | 06:38 | review-finding(Ch5): drop unused `[CharZero k]` from `prod_X_canonicalSeq` | Style |
| #2518 | 06:41 | review(Ch6): audit Wall 2 Stage C closure (PR #2495) | Review |
| #2511 | 06:41 | feat(Ch5): `polyRightTransl` + `tgtGLAction` defs + bijection helpers | Infra |
| #2526 | 06:46 | progress: /work — merged PRs #2518, #2511; cycled #2436 | Docs |
| #2528 | 06:48 | feat(Ch5 #2478): `polynomialRep_embeds_in_tensorPower` injection | Infra |
| #2529 | 06:51 | meditate(Ch5): Wall 3 #2519 C.1 — correct algebraic identity | Docs |
| #2534 | 07:05 | Schur-Weyl L_i part B (subpart): trivial-tensor character multiplicativity | Infra |
| #2538 | 07:53 | feat(Ch5 #2527 Part A): bridge equivariance | Infra |
| #2536 | 08:14 | feat(Ch5 #2531): partial — state `twistedPolytabloid_support_bound` | Infra (main ✓) |
| #2539 | 08:34 | feat(Ch5): `polynomialRep_embeds_in_tensorPower` equivariance | Infra |
| #2542 | 08:48 | feat(Ch5 #2515 part B): character identity skeleton + sum-of-characters | **+1** (#2540) |
| #2544 | 08:50 | feat(Ch5 #2535): partial — involution scaffold for `_apply_of_not_dominates` | **+1** (#2543) |
| #2548 | 09:01 | progress: planner cycle f9c8801a — triage 3 replan, file 3 new issues | Docs |
| #2549 | 09:12 | doc(review #2547): Schur-Weyl equivariance audit — all PASS | Review |
| #2551 | 10:04 | feat(Ch5): derive `hP_mul` from `ρ.map_mul` via `MvPolynomial.funext` | Infra |
| #2552 | 10:06 | progress: handoff for #2545 (PR #2551 already merged) | Docs |

**Net counts:**
- Wall 2 closed: −1 (`dTildeRep_mapLinear_transport` landed).
- Wall 3 decomposition anchor: +1
  (`twistedPolytabloid_pigeonhole_pair` surfaced as the distilled
  combinatorial core; C.1.a main theorem
  `twistedPolytabloid_support_bound` now **sorry-free modulo** the
  pigeonhole helper, which is in flight via PR #2550).
- Schur-Weyl chain decomposition anchor: +1
  (`glTensorRep_equivariant_schurWeyl_decomposition` — the equivariant
  Schur-Weyl decomposition, now issue #2540 claimed).
- Raw count: 7 → 8 (+1). Files: 4 → 4 (unchanged).
- Infra / review / style / docs: 36 total; no regressions.

## Chapter Breakdown

| Chapter | Sorries | Files | Delta from Wave 55 |
|---------|---------|-------|--------------------|
| Ch2     | 1       | 1     | 0                  |
| Ch5     | 4       | 2     | +2 (#2540 equivariance, #2543 pigeonhole) |
| Ch6     | 3       | 1     | −1 (Wall 2 closed) |
| Ch9     | 0       | 0     | 0                  |

## Per-File Sorry Detail

### InfiniteTypeConstructions (Ch6) — 3 sorries: Wall 1 FRAMEWORK

All three sorries are **refuted-as-stated** pointers to Wall 1. Same
status as wave-55. Each theorem is provably **false** for every m ≥ 1
in its current single-nilpotent-twist construction (the `e_m` direction
peels off as a 1-dim summand at the center).

| Line | Theorem | Status |
|-----:|---------|--------|
| 3344 | `etilde6v2Rep_isIndecomposable (m hm)` | Refuted; awaits Wall 1 decision |
| 3599 | `etilde7Rep_isIndecomposable (m hm)` | Refuted; awaits Wall 1 decision |
| 3826 | `t125Rep_isIndecomposable (m hm)` | Refuted; awaits Wall 1 decision |

Reference: `progress/indecomposability-framework-investigation.md`.
Framework issue: #2436 (`human-oversight`, `replan`). Downstream:
`not_posdef_not_HasFiniteRepresentationType` (Theorem 2.1.2 forward).

### SpechtModuleBasis (Ch5) — 2 sorries: WALL 3 CHAIN ACTIVE

**Wall 3 decomposition** — the chain from wave-55 parent #2450 is now
4 sub-issues (A/B/C/D), with C itself split into C.1/C.2 and C.1 further
into C.1.a/C.1.b/C.1.c. A, B, C.1 meditate, and C.1.a main theorem have
all landed. What remains in-file:

- **Line 1094 — `twistedPolytabloid_pigeonhole_pair`** (C.1.a.ii)
  The combinatorial pigeonhole core: given a column-standard σ and
  a `q₀ ∈ ColumnSubgroup` whose `w · q₀⁻¹ · σ` has strictly greater
  cumulative count than σ at some threshold `(k, i)`, produce two
  distinct positions `a₁ ≠ a₂` in the same column with the same
  `w`-image row. **Issue #2543 has-pr (PR #2550 open).** The
  sign-reversing involution scaffold that consumes this helper already
  landed (PR #2544); `twistedPolytabloid_support_bound` is fully
  proved modulo this one sorry.

- **Line 1332 — `garnir_twisted_in_lower_span`** (final Wall 3 sorry)
  The combinatorial heart of the straightening theorem. Waiting for
  C.1.a + C.1.b + C.1.c + C.2 to close first, then final assembly
  via issue #2500 (part D). Currently blocked on the chain;
  wave-55's "framework wall" is now a multi-stage **in-flight proof**,
  not a framework question. The whole-sum cancellation strategy
  validated on λ=(2,2) counter-example is the guiding approach
  (see `progress/20260424T034536Z_2a4d9cc5.md`).

### FormalCharacterIso (Ch5) — 2 sorries: SCHUR-WEYL CHAIN ACTIVE

- **Line 399 — `iso_of_formalCharacter_eq_schurPoly`**
  The top-of-chain goal sorry, unchanged since wave-43. The Schur-Weyl
  chain from `progress/schur-weyl-scoping.md` eliminates this sorry
  via a 6-step argument. Chain status this wave:
  - `#1` ✅ merged (PR #2461): tensor-degree homogeneity.
  - `#2a` ✅ merged (PRs #2502, #2511, #2538): polynomial-tensor
    bridge construction + injectivity + equivariance.
  - `#2b` ✅ merged (PRs #2528, #2539): polynomial rep embedding
    `deg-n polys in g_ij ↪ (V^⊗n)^m` with equivariance.
  - `#3 Part A` ✅ merged (PR #2504): L_i FDRep GL_N structure.
  - `#3 Part B` partial (PR #2542 + issue #2540): character identity
    `char(V^⊗n) = Σ dim(Sᵢ)·char(Lᵢ)` proved modulo equivariance
    (see line 774 below).
  - `#3 Part C` blocked on #2540 (#2493: final assembly).
  - `#4` ✅ merged (PR #2462): `schurPoly_linearIndependent`.
  - `#5` (#2482) blocked on #3 Part C.
  - `#6` (#2483) — this sorry's final assembly, blocked on #2482.
  - Collateral infra: `hP_mul` derivation (#2551), bimodule foundation
    with evaluation formula (#2509), character additivity (#2516),
    trivial-tensor character multiplicativity (#2534).

- **Line 774 — `glTensorRep_equivariant_schurWeyl_decomposition`**
  **NEW this wave.** Intentional decomposition anchor introduced by
  PR #2542. The theorem states that the Schur-Weyl bimodule
  decomposition `V^⊗n ≃ ⨁ᵢ Sᵢ ⊗[k] Lᵢ` is GL_N(k)-equivariant, where
  the RHS action is trivial on each `Sᵢ` and the `Lᵢ` action on the
  second factor. Issue #2540 (`feat(Ch5): Wall - Schur-Weyl equivariant
  bimodule decomposition`) is **claimed**. Expected closure: one
  session once the proof of GL_N-equivariance of the bimodule
  decomposition from Theorem 5.18.4 is filled in (the pieces —
  isotypic components, evaluation equivalence, bimodule structure —
  are all in place).

### Theorem2_1_2 (Ch2) — 1 sorry: blocked on Wall 1

- **Line 173 — `not_posdef_not_HasFiniteRepresentationType`** (forward)
  Backward bridge proved by #2403 (wave 54). Forward bridge needs
  per-field infinite-type results from the Ẽ/T constructions, gated on
  Wall 1's framework decision. Issue #2401 carries this dependency.
  Unchanged since wave 54.

## Open PRs

| PR | Status | Branch |
|----|--------|--------|
| #2550 | mergeable=UNKNOWN, CI in flight | agent/f70c31f1 — Wall 3 C.1.a.ii pigeonhole |
| #2541 | mergeable=UNKNOWN, repair history | agent/936a1471 — Wall 3 C.1.b leading-tabloid elimination |

## Active Issues

| Issue | Title | Status |
|-------|-------|--------|
| #2546 | summarize: wave-56 sorry landscape + design-walls refresh | Claimed (this session) |
| #2540 | Schur-Weyl equivariant bimodule decomposition (#2515 part A) | Claimed |
| #2543 | Wall 3 C.1.a.ii — `twistedPolytabloid_pigeonhole_pair` | has-pr (#2550) |
| #2532 | Wall 3 C.1.b — Leading-tabloid elimination (Algorithm A) | has-pr (#2541) |

## Unclaimed / Replan Issues

| Issue | Title | Status |
|-------|-------|--------|
| #2535 | Wall 3 C.1.a.i — fibre-coefficient-zero helper (pigeonhole + involution) | replan (superseded by #2543) |
| #2436 | Framework decision: affine Dynkin infinite type (Ẽ_n / T(p,q,r)) | replan, `human-oversight`, awaits Kim |

## Blocked Issues

| Issue | Title | Blocked on |
|-------|-------|-----------|
| #2533 | Wall 3 C.1.c — glue C.1.a + C.1.b | #2543 + #2532 |
| #2520 | Wall 3 #2499 C.2 — τ classification | #2533 |
| #2500 | Wall 3 #2450 part D — final assembly | #2533 + #2520 |
| #2493 | Schur-Weyl L_i (part C): final assembly | #2540 |
| #2482 | polynomial GL_N-rep decomposes as direct sum of Schur modules (Schur-Weyl #5) | #2493 |
| #2483 | close `iso_of_formalCharacter_eq_schurPoly` (Schur-Weyl #6) | #2482 |
| #2401 | Prove Theorem2_1_2 bridges (forward + backward) | #2436 |

## Dependency Clusters

### Cluster A: Polytabloid / Straightening (Ch5, 2 sorries)
**Files:** SpechtModuleBasis (2 sorries, both Wall 3 chain)

- `twistedPolytabloid_pigeonhole_pair` (line 1094) — combinatorial
  pigeonhole. Issue #2543 has-pr (PR #2550).
- `garnir_twisted_in_lower_span` (line 1332) — the wave-55 framework
  wall, now structured as multi-stage chain ending at issue #2500.
  Blocked behind the C.1/C.2 completion cascade.

Wall 3 chain diagram (current):

```
#2543 (C.1.a.ii pigeonhole, has-pr) ─┐
                                     ├─→ #2533 (C.1.c glue) ─┐
#2532 (C.1.b algorithm A, has-pr) ───┘                       ├─→ #2500 (part D assembly) → kills line 1332
                                                             │
                                         #2520 (C.2 τ class) ┘
```

### Cluster B: Schur-Weyl chain closing `iso_of_formalCharacter_eq_schurPoly` (Ch5, 2 sorries)
**Files:** FormalCharacterIso (2 sorries — one top-of-chain goal, one
equivariance decomposition anchor)

- `glTensorRep_equivariant_schurWeyl_decomposition` (line 774) — issue
  #2540, claimed.
- `iso_of_formalCharacter_eq_schurPoly` (line 399) — blocked on #2482
  → #2493 → #2540.

Schur-Weyl chain diagram (current):

```
#2540 (equivariance, claimed) → #2493 (part C assembly) → #2482 (#5) → #2483 (#6) → kills line 399
```

### Cluster C: Ẽ/T framework wall (Ch6, 3 sorries) + blocked downstream (Ch2, 1 sorry)

**Files:** InfiniteTypeConstructions (3), Theorem2_1_2 (1)

- B1 (Wall 1): 3 sorries. Awaits Kim's Option A / B / A+C / B+C.
- B2 (Theorem 2.1.2 forward): 1 sorry blocked on B1.

### Cluster D: Morita Theory (Ch9) — CLOSED (wave 50)

## Trajectory

| Wave | Sorries | Files | Items sorry-free | Date       |
|------|---------|-------|------------------|------------|
| 43   | 13      | 10    | 579/583 (99.3%)  | 2026-04-04 |
| 44   | 10      | 8     | 580/583 (99.5%)  | 2026-04-05 |
| 45   | 15      | 8     | 580/583 (99.5%)  | 2026-04-06 |
| 46   | 15      | 8     | 580/583 (99.5%)  | 2026-04-08 |
| 47   | 9       | 6     | 581/583 (99.7%)  | 2026-04-11 |
| 48   | 8       | 6     | 581/583 (99.7%)  | 2026-04-11 |
| 49   | 10      | 6     | 581/583 (99.7%)  | 2026-04-12 |
| 50   | 13      | 5     | 581/583 (99.7%)  | 2026-04-13 |
| 51   | 21      | 5     | 582/583 (99.8%)  | 2026-04-17 |
| 52   | 17      | 4     | 582/583 (99.8%)  | 2026-04-17 |
| 53   | 13      | 4     | 582/583 (99.8%)  | 2026-04-17 |
| 54   | 14      | 4     | 582/583 (99.8%)  | 2026-04-23 |
| 55   | 7       | 4     | 582/583 (99.8%)  | 2026-04-24 |
| **56** | **8** | **4** | **582/583 (99.8%)** | **2026-04-24** |

**Wave 56 trend:** Raw count rose by 1 (7 → 8) but the landscape is
healthier than wave-55. Wall 2 (the single mechanical residual in
wave-55) is now fully closed. Two new sorries are decomposition
anchors introduced by design — one from the Wall 3 C.1.a chain
(pigeonhole helper #2543 has-pr), one from the Schur-Weyl chain
(equivariance #2540 claimed). **Of the 8 current sorries:**

- 3 are framework-wall stubs (Wall 1 Ẽ/T, await Kim).
- 1 is framework-blocked downstream (Theorem 2.1.2 forward → #2436).
- 4 are on active decomposition chains (Wall 3 and Schur-Weyl) with
  concrete sub-issues in flight or already in PR review.

## Honest Assessment

Wave 56 is the wave where **Wall 2 closed and Wall 3 became a real
proof in flight** rather than a wall.

**Strengths:**

1. **Wall 2 fully closed.** `dTildeRep_mapLinear_transport` (the wave-55
   mechanical residual) landed via PR #2495 (`dTildeCast` refactor),
   then received two rounds of polish (#2517/#2524 style, #2518 audit).
   Ch6 is now down to its three Wall 1 framework stubs only.

2. **Schur-Weyl chain had its biggest single-wave push to date.** The
   polynomial-tensor bridge (#2502), bridge equivariance (#2538),
   `polynomialRep_embeds_in_tensorPower` with injection + equivariance
   (#2528, #2539), `hP_mul` derivation (#2551), L_i FDRep structure
   (#2504), character additivity (#2516), trivial-tensor
   multiplicativity (#2534), explicit bimodule with evaluation formula
   (#2509), and character identity skeleton (#2542) all merged. The
   remaining equivariance sorry (#2540) is the single intentional
   decomposition anchor; one session's work.

3. **Wall 3 is decomposed and in flight.** The wave-55 framework wall
   became a 6-node chain:
   - Part A: `garnirColReindex` + sign tracking (#2503 ✓)
   - Part B: `garnir_pigeonhole_collapse` (#2505 ✓)
   - Part C meditate: whole-sum dominance-induction correctness (#2529 ✓)
   - C.1.a: support bound main theorem (#2536 ✓) + pigeonhole helper
     (#2543 PR open as #2550)
   - C.1.b: leading-tabloid elimination (#2541 PR open)
   - C.1.c / D: final assembly (#2533, #2500, blocked)

   Two sub-issues are already in PR review. The wave-55 doc said Wall 3
   was "stale" and "unclaimed"; this wave, every branch of the chain
   has a named owner and a concrete Lean statement.

4. **Review culture held up.** Four review passes this wave (#2490
   bimodule, #2513 bridge, #2518 Wall 2 closure, #2549 Schur-Weyl
   equivariance) each filed targeted follow-ups (#2489, #2512, #2545)
   rather than bulk rubber-stamping. The Wave 55 audit process is
   repeating cleanly at Wave 56 velocity.

**Concerns:**

1. **Wall 1 remains the single longest-running open item.** Issue #2436
   is `human-oversight`, `replan`. Three worker agents have now tried
   to claim it and been correctly blocked by `coordination claim`.
   Until Kim picks A / B / A+C / B+C, these 3 Ch6 sorries cannot be
   addressed and Theorem 2.1.2 forward (Cluster C downstream) cannot
   be unblocked.

2. **Wall 3 chain velocity is promising but unproven at the glue step.**
   C.1.a.i was split into C.1.a.ii mid-wave because the pigeonhole
   was further from the scaffold than the issue estimated (see
   `progress/20260424T085906Z_f9c8801a.md` / #2548). The glue step
   #2533 (C.1.c) and the final assembly #2500 (part D) have not yet
   been attempted; there is still model risk that C.1 terms end up
   outside the broadened disjunction, forcing another refactor.

3. **Schur-Weyl equivariance #2540 is non-trivial.** While the
   character-identity skeleton is proved modulo just this one
   theorem, the equivariance itself is a substantial claim: it
   requires tracking the GL_N-equivariance of the entire bimodule
   decomposition `V^⊗n ≃ ⨁ᵢ Sᵢ ⊗ Lᵢ` (not merely individual pieces).
   The review audit on #2538 / #2539 (#2547 / #2549) showed the
   current equivariance infrastructure is sound at the individual-level,
   but assembling it for the full decomposition is the remaining work.

4. **Raw sorry count went up.** Reported as a strength above
   (intentional decomposition anchors), but worth acknowledging: the
   count-based trajectory table shows 7 → 8, contrary to wave-55's
   halving. The "floor" (what would remain if all active chains close)
   is now 4 sorries (3 Wall 1 + 1 Ch2 downstream) — same as wave-55.

**Current priority ordering:**

1. **Kim's framework decision on Wall 1 (#2436).** Unblocks 3 Ch6
   sorries + 1 Ch2 downstream. No worker action available until then.
2. **PR #2550 (Wall 3 C.1.a.ii pigeonhole).** In CI; closes #2543
   and kills the line-1094 sorry.
3. **PR #2541 (Wall 3 C.1.b algorithm A).** In repair/CI; closes
   #2532.
4. **#2540 (Schur-Weyl equivariance).** Closes the FormalCharacterIso
   line-774 sorry; unblocks the whole #2493 → #2482 → #2483 cascade.
5. **#2533 → #2500 (Wall 3 C.1.c + D assembly).** Unblocks after
   PR #2550 + #2541 land; closes Wall 3 entirely.

**If Wall 1 is resolved and the active chains close**: 4 Ch6/Ch2
framework-stub sorries are replaced or re-proved, Wall 3 closes
(−1 Ch5), Schur-Weyl closes (−2 Ch5). Floor would be **0 sorries**,
achievable within Kim's framework-decision window plus ~1 worker-day
for the chain completions. That is a one-decision-plus-a-day path to
a fully-proved project, tighter than wave-55's "one-decision-plus-a-week"
estimate.

## Design walls snapshot

No walls have meaningfully shifted since wave 55 except:

- **Wall 2 is removed** (was Option-a resolution in wave-55;
  mechanical residual closed in wave-56).
- **Wall 3 is now a proof in flight, not a wall.** Concrete
  multi-stage chain with named owners per stage, per issue (#2543,
  #2532, #2533, #2520, #2500).
- **Wall 1 unchanged.**
- **Schur-Weyl chain** continues as a healthy multi-issue feature,
  not a wall (equivariance #2540 claimed).

Refer to `progress/design-walls-wave56.md` for the updated decision
sheet.
