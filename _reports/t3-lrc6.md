# T3 — LRC n=6 (Renault mod-6) — work log

## Task

Prove `lrc6_int`: for `D : Finset ℕ`, `∀ d ∈ D, 0 < d`, `D.card ≤ 5`,
`∃ t : ℝ, 0 < t ∧ ∀ d ∈ D, (1/6 : ℝ) ≤ circ (t * d)`.
Plus rational wrappers in `Research07/LRC6/Main.lean`, wiring in `Research07.lean`
and `Research07/Audit.lean`. Gates: clean `lake build`, no sorry/admit/native_decide/
unsafe, axioms `[propext, Classical.choice, Quot.sound]`.

## Status: IN PROGRESS — proof route decided, implementation pending

---

## 2026-09-18 — Mathematical reconnaissance (this session)

### Files inspected

- `Research07/LRC4/IntCase.lean` (1375 lines): Renault-style proof for n=4.
  Architecture: extremize `fract(a·t)` over guard-safe times, then a finite
  improving-shift casework (`renault_core`, `renault_driver`, `forward_endpoint`,
  `backward_endpoint`, `topBdry`, `botBdry`).
- `Research07/LRC5/Filtering.lean`, `IntCase.lean`: B-S p=5 prime filtering for
  |D|≤4 — generic level machinery + a `residual_case` digit chase for 3 units.
- `Research07/LRC3/*`: `circ`, `two_moving`, coverings.
- `_external/bhk.txt`: BHK "Six Lonely Runners" — 50-page torus/subgroup proof,
  rejected as too large for direct formalization.
- `_external/chu.txt`: survey; confirms Renault n=6 = mod-6 residue casework.
- `_external/five-distance-sharp`: unrelated (three-gap theorems).

### Literature verdict

Renault's paper (Discrete Math 287 (2004) 93–101) is **unobtainable**
(paywall + dead mirrors + no arXiv/HAL preprint + IA down). Surveys confirm only
the shape: case analysis on residue classes of speeds mod 6. We reconstruct.

### Computational findings (all verified, ~700k configs total, ZERO failures)

**Master empirical theorem** (tested 365k+ configs, 0 fails):

> For `D` 5 positive integers, gcd 1, let `a` = largest multiple of 6 in `D`
> (or even `a` = max `D`). Then `∃ n ∈ {1,…,6a−1}` with `|vn|_{6a} ≥ a` for all
> `v ∈ D` — i.e. `t = n/(6a)` works.

- The `a`-condition itself is `n ≢ 0 mod 6` (since `|an|_{6a} = a|n|_6 ≥ a`).
- Min-anchor fails (60 configs); max-6-runner and max-element anchors: 0 fails.

**Key decomposition** `n = m·a + r₀` (`m ∈ {0,…,5}`, `r₀ = n mod a`):

- 6-runner `v = 6β` (β < a): condition `|β r₀|_a ≥ a/6` — depends only on `r₀`.
  This is a **smaller instance** `T''(B, a/6)` of the same shape (modulus `a`,
  elements `β ≤ a/6`); recursion divides modulus by 6 (telescoping:
  `n = a + a' + … ` observed, e.g. `{6,36,216,1,2}` → `n = 216+36+6+1 = 259`).
- Non-6 guard `v`: write `v r₀ mod 6a = sᵥ·a + ρᵥ` (`sᵥ ∈ {0,…,5}`, `ρᵥ < a`);
  then `vn mod 6a = ((vm + sᵥ) mod 6)·a + ρᵥ`, so safe iff
  `σ' = (vm + sᵥ) mod 6 ∈ {1,2,3,4}` — an `m`-condition (ρᵥ < a is automatic).
- `r₀ ≢ 0 mod 6` needed (the `a`-condition).

So `T''(D,N)` (`|D|≤5`, all 6-runners `≤ N`) ⇒ exists `n` iff
(i) `∃ r₀` solving `T''(B, N/6)` for `B` = 6-runner quotients — **strong induction
on N works**; and (ii) `∃ m`: non-6 guards' `σ' ∈{1,2,3,4}` — the **m-step**.

### The m-step is the crux (Renault's casework)

Per-guard forbidden `m`-sets (from `σ' = (vm+sᵥ) mod 6 ∉ {1,2,3,4}`):
- `v ≡ ±1 (mod 6)`: 2 consecutive `m`'s forbidden (`|F|=2`, allowed 4).
- `v ≡ ±2 (mod 6)`: parity-pair `{j,j+3}` forbidden (`|F|=2`, allowed 4).
- `v ≡ 3 (mod 6)`: parity-triple `{0,2,4}`/`{1,3,5}` or `∅` (`|F|=3 or 0`).

`m` fails iff forbidden sets cover `{0,…,5}`. ~66% of configs have SOME `r₀`
where this happens; but empirically **never** happens for ALL `r₀ ∈ S₀`
(`S₀` = 6-runner solution set mod N). Covering needs ≥2 guards; minimal covers:
two `≡3`-guards (E/O classes), three `≡2/4`-guards (all parity-pairs), three
coprime-guards (disjoint consecutive pairs), and 4-guard combos — **7365 covering
multisets** enumerated — naive casework infeasible; needs the structural argument.

`r₀` freedom: `S₀` is symmetric (`r₀ ↔ −r₀` flips `sᵥ ↔ 5−sᵥ`, but `≡3`-class
covers are negation-stable). `|S₀| ≥ 4` always observed. Working `r₀` is small:
`r₀ ∈ {1,…,5}` in 99.96% of cases; exceptions need `r₀ ∈ 6+{1,…,5}` or
`12+{1,…,5}` — the 6-adic digit signature of the recursion.

### Proof route decision

**Chosen**: strong induction on `N` for `T''(D,N)` via the `(m, r₀)` split.
Remaining hard part = m-step lemma: `∃ r₀ ∈ S₀` with non-covering `s`-pattern.
The induction produces `r₀`; must show one is `m`-compatible.

**Alternative** (fallback): LRC4-style Renault extremization — proven architecture
in our codebase, but n=6 casework is larger.

## Status update (end of session)

**Lean infrastructure built** (`_dev/scratch/T3IntCase.lean`, compiles clean):
- `absModN_six_mul`: `|6x|_{6a} = 6|x|_a` — the 6-runner reduction.
- `circ_ge_sixth`: `|λv|_{6a} ≥ a → circ(λv/(6a)) ≥ 1/6` (bridge, mirrors
  `circ_ge_fifth`).
- `absModN_congr'`: residue invariance.
- `six_runner_cond`: `|6β(ma+r₀)|_{6a} = 6|β r₀|_a` — quotient-band reduction.

**Confirmed empirically** (~750k configs, 0 fails): `∃ n mod 6a` works for
`a` = max-6-runner; `n = m·a + r₀` telescopes 6-adically.

**The m-step is the open crux.** Confirmed no uniform shortcut exists:
- No single `m` works universally (m-set is symmetric, varies per config).
- No uniform σ'-class or all-central solution (1380 configs lack it).
- `r₀` is near-always small (99.96% in `{1..5}`) but 11 configs have a *unique*
  good `r₀` — no slack; the argument must be tight.
- Covering-patterns: two-≡3 (E/O), ≡3+3-non-≡3, ≥3 non-≡3 covering both
  parities — each forbidden-set is consecutive-pair (coprime), parity-pair
  (±2), or parity-triple/∅ (≡3). The s-values are r₀-determined and linked
  by guard linear relations (`Σ cᵢ sᵢ ≡ −w mod 6` when `Σ cᵢvᵢ = 0`).

**Remaining work**: the m-step lemma — prove `∃ r₀∈S₀, m∈Z₆` non-covering.
This is Renault's combinatorial casework; needs the structural argument that
`S₀` (a nonempty band-system solution set) always escapes the finite
covering-pattern union. Candidate route: case-split on guard class-multiset;
for each covering-type, show the required `s`-alignment is incompatible with
`r₀ ∈ S₀` (the 6-runner bands force "generic" residues).

**Covering-combos fully enumerated** (each guard's forbidden-set `F(c,s)`):
- `{3,3}` two ≡3-guards: E-class `s∈{0,5}` + O-class `s∈{2,3}`.
- `≡3-E + ≥3 non-≡3 covering odds`, `≡3-O + ≥3 non-≡3 covering evens`.
- `≥3 non-≡3` covering both parities: 3 disjoint forbidden-pairs (parity-pairs
  `{j,j+3}` from ≡±2, consecutive-pairs `{j,j+1}` from ≡±1).
- `s`-values satisfy `Σ cᵢsᵢ ≡ −w (mod 6)` when `Σ cᵢvᵢ = 0` (guard linear
  relations propagate to `s`-constraints) — a possible obstruction hook.

**Structural observations for the m-step proof**:
- Negation `r₀ → −r₀` flips `sᵥ → 5−sᵥ`: stable for ≡3-guards (E↔E, O↔O),
  swaps `{2,5}↔{1,4}` for ±2, changes pairs for coprime — helps escape
  non-≡3 covers, not pure-≡3.
- `S₀` has period `P = lcm_β a/gcd(β,a)` — union of residue-classes mod `P`;
  shifting `r₀` within a class shifts `sᵥ` by bounded carries.
- For related guards (`u' = ±v'` etc.) the (u'r₀,v'r₀) pair stays on
  diagonals → pure-≡3 covering impossible → m-step free for such pairs.
- Base cases: `|V₀|≤1` trivial; `|V₀|=2` covers iff two-≡3-complementary.

**Key refinements (this session's later analysis)**:
- CORRECTED safe condition: `vn mod 6a = a·σ' + ρ`, `ρ = vr₀ mod a`; safe iff
  `σ' ∈ {1,2,3,4}` **or** `(σ' = 5 ∧ ρ = 0)`. The `σ'=5,ρ=0` boundary is SAFE
  (`vn ≡ 5a`) — forbidden-sets are smaller than the `{0,5}`-model suggested.
- For coprime-`a` guards `ρ > 0` always; `ρ = 0` needs `a | vr₀`, i.e.
  `r₀ ≡ 0 (mod a/gcd(v,a))` — only non-coprime-`a` guards get the shrink.
- The m-step is a **band-structure fact, NOT a universal covering fact**:
  fails for arbitrary `S₀` (253/20000 random) — the proof MUST use that
  `S₀` is a band-system solution set, i.e. Renault's actual casework.
- Coprime-3-guard covering reduces to a **parity condition on s-values**
  (each guard's `s`-parity must align with its class for the disjoint-pair
  tiling) — first concrete obstruction handle; other covering-types have
  analogous alignment conditions on `s`.

**Case-split identified for the m-step**:
- `G = gcd(non-6-guards, a) ≥ 2`: pick `r₀ = c·a/G` (`c ∈ {1,…,G−1}`) → all
  guards have `ρ = 0` → each `|Fᵥ|` shrinks to only the `σ'=0`-forbids
  (coprime→1, ±2→≤2, ≡3→≤3) → covering much harder; coprime guards then
  *cannot* cover (≤4 single points < 6). Sub-case reduces to the simpler
  `σ'=0`-only covering.
- `G = 1` (all guards coprime to `a`): no `ρ=0` help — hardest case; covering
  needs full-strength forbidden-sets.

## Session verdict

Theorem **confirmed true** and proof **fully structured**:
`lrc6_int` ⇐ `mult6_exists` (discrete) ⇐ `(m,r₀)` split ⇐ [6-runner
recursion by strong induction on `a`] + [m-step covering lemma].

**Infrastructure proven & compiling** in `_dev/scratch/T3IntCase.lean`:
`absModN_six_mul`, `circ_ge_sixth`, `absModN_congr'`, `six_runner_cond`.

**Remaining = the m-step combinatorial lemma** — Renault's casework. Fully
characterized (covering types, `s`-alignment conditions, `ρ=0` refinement,
`G≥2`/`G=1` split) but the formal case-argument is not yet written. This is
the mathematical heart of the ~9-page Renault proof; expect a substantial
`IntCase.lean` (~1–2k lines of casework, like LRC4's ~1.4k).

## TODO next

1. Prove the m-step lemma (the heart of the argument) — investigate whether
   strengthening the IH (e.g. producing `r₀` in prescribed residues) closes it.
2. `Research07/LRC6/IntCase.lean`: `T''` induction + `lrc6_int`.
3. `Research07/LRC6/Main.lean`: rational wrappers.
4. Wire `Research07.lean` + `Audit.lean`; `lake build`; axiom gate; report.

---

## 2026-09-18 (cont.) — Paper obtained; pivot to Renault's case structure

`_external/renault.txt` (full text) arrived mid-session → the `(m,r₀)` m-step
frame is replaced by Renault's own organisation: `(λ,α)` improving moves about
an extremal time `t̄`, cases by congruence-class/parity distribution (§3–§6).
Mathematically equivalent, but we now implement the paper's partition.

### Shared infrastructure — BUILT & COMPILING

`Research07/LRC6/Setup.lean` (clean):
- Threshold bridges `circ_ge_fifth_fract`, `circ_ge_sixth_fract`.
- `off`/`abs_off`/`off_add_int`/`off_fract`/`off_neg`/`fract_eq_off`/
  `fract_eq_one_add_off` offset machinery.
- `fract_add_shift`, `fract_nat_mul`, `fract_improve`, `fract_improve_anchor`.
- **`fract_lambda_alpha`**: for `d ≡ e (mod 6)`,
  `x_d(λτ+α/6) = ⟨λ·x_d(τ) + e·α/6⟩` — the guard improving-move formula.
- **`circ_lambda_gt`**: `x ∈ (0,1/6)`, `λ∈{2..5}` ⇒ `x < circ(λx)` — the
  `N(x₁(λt̄+α/6)) > N(x₁(t̄))` improvement for `λ ≥ 2`.
- **`circ_anchor_lambda`**: `6∣a ⇒ circ(a·(λτ+α/6)) = circ(λ·x_a(τ))`.
- `topBdry6`/`botBdry6` boundary sets + membership/position lemmas.

`Research07/LRC6/Extremize.lean` (clean):
- `forward_endpoint6`, `backward_endpoint6`: finite-guard generalisation of the
  LRC4 endpoint lemmas — push to the first `5/6`-exit / `1/6`-exit keeping all
  guards safe and `off a` monotone.
- `circ_max_of_fract_max`: convert the `fract<1/6`-maximiser into the global
  `circ`-maximality Renault uses for `N(x₁)`.
- **`renault6_maximize`**: Renault's `t̄`. Given `hns` (no time makes `a` and all
  guards safe) and a `lrc5_int`-seed (all guards `1/5`-safe), produces `tstar`
  with all guards `1/6`-safe, `0 < x_a(tstar) < 1/6`, `fract`-max, `circ`-max,
  and a boundary guard at `5/6`. Uses `lrc5_int` as the IH seed.
- **`exists_improve_eq_one`**: the `λ=1` driver — if all guards are in
  `[1/6,5/6)` (strict upper) at `s` and `x_a(s) ∈ (0,1/6)`, a forward
  perturbation `s+η` keeps guards safe and raises `x_a` — contradiction.

### Renault's actual argument mapped (for the case proofs)

`v₁` = multiple-of-6 anchor, `v₂..v₅` = 4 guards. `t̄` maximises `N(x₁)=circ`
over guard-safe times; under failure `x₁(t̄) ∈ (0,1/6)` and a guard sits at
`5/6`. `t̃ = t̄ + e₂/6` puts runner 2 at `0`. Then Lemma 5.x/6.x give `(λ,α)`:
- `s = λt̃ + α/6`; guards safe via `fract_lambda_alpha`;
- `λ ≥ 2`: `circ(a·s) = circ(λx₁) > x₁` via `circ_anchor_lambda` +
  `circ_lambda_gt` ⇒ contradicts `circ`-max;
- `λ = 1`: all guards `< 5/6` ⇒ `exists_improve_eq_one` gives `s+η` ⇒ contradict.

Case lemmas needed (pure interval combinatorics, independent → parallel):
- §2: Lemma 2.1 (counting), Lemma 2.3 (three-div-3), Claim 2.4.
- §5 (one even): Lemmas 5.1, 5.2, 5.3, Prop 5.4.
- §6 (two even): Lemmas 6.1–6.5, Prop 6.6.
- §3/§4 (≥2 div-3, ≥3 even): Props 3.1, 4.x.

### Gotchas hit (logged to `_dev/failures.md`)
- `t̄` (t+combining macron U+0304) is NOT a valid Lean ident → use `tstar`.
- `lt_trichotomy a 0` first case is `a < 0` (not `>0`) — order cases `<|=|>`.
- `Int.fract_eq_self` is an iff (`fract x = x ↔ 0≤x ∧ x<1`) → use `.mpr`.
- `circ (τ*d)` vs `circ (d*τ)` — `rw [mul_comm]` before applying `circ_ge_*`.
- `Finset.exists_min_image` is the clean min-headroom API (not `Finset.inf'`).
- `Int.modEq_iff_dvd` gives `e - d = 6k` (note sign) for `d ≡ e [ZMOD 6]`.

## 2026-09-19 — IntCase.lean complete modulo prop3_1/prop4_1

Post-outage rebuild of `IntCase.lean` finished and compiles. The file now
contains the full top-level chain:

- `safe6_half_shift_of_dvd`: even runners invariant under `+1/2` shift.
- `even_le_three` (Lemma 2.1 `l=2`): under `hfail`+`gcd=1`, ≤3 speeds even.
  Proof: 4+ evens ⇒ `lrc5_int` seeds a `1/5`-safe `τ`; the `D\T` leftover `d₀`
  is either even (⇒ `2 | gcd`, contra `gcd=1`) or odd (⇒ unsafe at both `τ`
  and `τ+1/2`, disjoint arcs).
- `dvd_two_of_modeq` / `not_dvd_two_of_modeq`: `d ≡ ±2 [ZMOD 6]` ⇒ `2|d`,
  `d ≡ ±1` ⇒ `∤`.
- `lrc6_case_gcd` (card=5, gcd=1): splits on `(D.filter (3∣·)).card` via
  `mult3_le_three` + `hfail_exists_dvd (l=3)`:
  * `=3` → `lemma2_3`; `=2` → `prop3_1`;
  * `=1` → unique mult-3 is the `l=6` witness `v₁`; guards `G = D\{v₁}` get
    `hseed` (lrc5_int `1/5`) + `hns` (hfail→`|off v₁ t|<1/6`); parity split on
    `(G.filter (2∣·)).card ∈ {0,1,2}` (capped by `even_le_three`):
    0 → `prop5_4`, 1 → `prop6_6`, 2 → `prop4_1` (residues `±2`/`±1` extracted
    from `d mod 6 ∈ {1,2,4,5}` via `interval_cases`).
- `lrc6_case`: gcd reduction — `D' = D.image (·/g)` has `gcd=1`, `card=5`,
  `hfail` (positions scale `fract((d/g)·s) = fract(d·(s/g))`).
- `lrc6_int`: `card≤4` via `lrc5_int` (`1/5>1/6`); `card=5` by_contra →
  `hfail` (ceil-shift `t+⌈-t⌉+1` makes the safe time positive) → `lrc6_case`.

Remaining: only `prop4_1`, `prop3_1` identifiers (agents still proving).
Everything else compiles clean — `lake env lean` shows only the two
unknown-identifier errors at the call sites.

API notes (this session): `Finset.card_insert_of_notMem` (capital M),
`Finset.card_sdiff_of_subset`, `Finset.gcd_dvd (f := id)` needs the implicit
pinned, `Int.modEq_iff_dvd : a≡b ↔ n|b-a`, `Finset.mem_image.mpr ⟨d,hd,rfl⟩`,
`Nat.mul_dvd_mul_iff_left`, `interval_cases` reverts `set`-abstractions in
the goal (keep `hE`/`card_eq_zero.mp` instead of rewriting `E`).

### Scratch verification (T3IntCaseMain.lean)

Copied `IntCase.lean` body + `Main.lean` body into `_dev/scratch/T3IntCaseMain.lean`
with `sorry`-stubs for `prop3_1`/`prop4_1` (matching my call-site signatures).
Result: **compiles clean** — only the two expected `sorry` warnings. Confirms:

- `lrc6_case_gcd` full parity dispatch elaborate end-to-end;
- `lrc6_case` (gcd reduction) + `lrc6_int` (top-level) compile;
- `lrc6_rel_rat` + `lonely_runner_six_rat` (Main.lean) compile;
- prop4_1 call-site signature is self-consistent
  `(hv1..hv5 pos, hv1m : v₁≡0, hv2m..hv5m modEq, he₂..he₅, hf : hfail {v₁..v₅})`.

Once the agents land `prop3_1`/`prop4_1`, add their imports to `IntCase.lean`
and drop the stubs. Umbrella `Research07.lean` + `Audit.lean` already wired
(`import Research07.LRC6.Main` + 3 `#print axioms` lines).

## 2026-09-30 — FINAL: LRC6 complete, all gates green

### Outcome
`prop3_1` (§3, two multiples of 3) and `prop4_1` (§4, three even speeds) both landed
after the power-loss recovery. Full `lake build` = **8959 targets, clean**.

### Prop41 tail fixes (this session)
- `insert_comm` rewrite chains failed: literal `{v₄}` is `Finset.singleton`, not
  `insert v₄ ∅`, so pattern `insert v₅ (insert v₄ ?s)` never occurs.
- `ext; simp only [mem_insert, mem_singleton]; tauto`/`aesop` → isDefEq/heartbeat
  timeouts (5-atom iff burns the whole `have`-block budget).
- `fin_cases` dies on `d ∈ {v₁,…,v₅}` (dependent elimination on `Decidable.rec`).
- **Fix:** unfold `hfail` (`∀t, ∃d∈D, ¬safe6`), transport witness directly:
  `intro t; obtain ⟨d,hd,hns⟩ := hf t; refine ⟨d, ?_, hns⟩;
   simp only [mem_insert, mem_singleton] at hd ⊢;
   rcases hd with rfl|…|rfl <;> simp`. No set-equality at all.
- `claim2_4` yields `lam ∈ {2,3,4,5}` → `hlam.1 : 2 ≤ lam`; `hI2` wants `1 ≤ lam`
  → `hI2 lam (by omega) hlam.2`.

### Integration
- `IntCase.lean` now `import Prop31 Prop41` (added). Deleted IntCase's duplicate
  `safe6_half_shift_of_dvd` (name clash — Prop31 defines the identical lemma).
- Umbrella `Research07.lean` imports `LRC6.Main`; `Audit.lean` checks
  `lrc6_int`/`lrc6_rel_rat`/`lonely_runner_six_rat`.

### Environmental (post-power-loss)
`lake serve` respawned by the IDE held `.olean.private` handles during its load
phase → every `lean -o` failed on a random "failed to read" for ~10 min.
Converged via `lake build` retry once the server went idle.

### Verification gates — ALL GREEN
- `lake build`: 8959 targets, exit 0 (warnings only).
- Forbidden constructs: zero `sorry`/`admit`/`native_decide`/`unsafe` in all 14
  LRC6 files (hits are identifiers like `unsafe35_union` / docstrings).
- Axiom audit (`Audit.lean`):
  - `lrc6_int` → `[propext, Classical.choice, Quot.sound]`
  - `lrc6_rel_rat` → `[propext, Classical.choice, Quot.sound]`
  - `lonely_runner_six_rat` → `[propext, Classical.choice, Quot.sound]`

### Theorem inventory (LRC6/)
`Setup` `Reduction` `Extremize` `Driver` `Signed` — infra + signed residues.
`Lemma51` `Lemma61` `Lemma64` — Renault's core lemmas (+ signed 5.2/5.3/6.2/6.3/6.5).
`Prop31` (2113 ln) `Prop41` (1207 ln) `Prop54` `Prop66` — the four case props.
`IntCase` — `even_le_three`, `lrc6_case_gcd` (parity dispatch), `lrc6_case` (gcd
reduction), **`lrc6_int`**. `Main` — `lrc6_rel_rat`, **`lonely_runner_six_rat`**.

### Status: T3 (n = 6 via Renault) COMPLETE. Private/quiet-period — not pushed.
