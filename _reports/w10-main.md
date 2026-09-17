# W10 — `Research07/M3/Main.lean` sorries (lrc5_rel_real, lonely_runner_five)

Agent: W10 (fresh start after previous agent died on connection error).
Started: 2026-09-18 (session). Own file: `Research07/M3/Main.lean` only.

## Recon (tool calls 1–6)

- `M3/Main.lean` (lines 24–37): two sorries.
  - `lrc5_rel_real (w : Fin 4 → ℝ) (hw : ∀ i, w i ≠ 0) : ∃ t:ℝ, 0<t ∧ ∀ i, 1/5 ≤ circ (t * w i)`
  - `lonely_runner_five (v : Fin 5 → ℝ) (hv : Injective v) : ∀ i, ∃ t:ℝ, 0≤t ∧ ∀ j, j≠i → 1/5 ≤ dist ↑(t*v i) ↑(t*v j)`
- Frozen dependencies (still sorry'd in tree — fine, signatures usable):
  - `lrc5_rel_rat (w : Fin 4 → ℚ) (hw) : ∃ t:ℝ, 0<t ∧ ∀ i, 1/5 ≤ circ (t * ↑(w i))` — LRC5/Main.lean:26 (PROVEN, no sorry).
  - `lrc5_real_of_irrational_ratio (hlrc4) {u : Fin 4 → ℝ} (hpos : ∀i,0<u i) (hirr : ¬∃c:ℝ,∀i,∃q:ℚ, u i = c*q) : ∃ t>0, ∀i, 1/5 < circ (t*u i)` — M3/BHK.lean:47 (sorry'd).
  - `lrc4_rat_finset (S : Finset ℚ) (hpos) (hcard ≤3) : ∃ t>0, ∀q∈S, 1/4 ≤ circ (t*q)` — LRC4/Main.lean:24 (sorry'd). Exact hlrc4 shape.
  - `dist_unitAddCircle_eq_circ (x y : ℝ) : dist ↑x ↑y = circ (x - y)` — LRC3/Main.lean:22 (proven).
  - `circ_abs`, `circ_neg` — LRC3/Circ.lean:39,44 (proven).
- `Fin.succAbove_ne (p : Fin (n+1)) (i : Fin n) : p.succAbove i ≠ p` — Mathlib SuccPred.lean:560.
- `Fin.exists_succAbove_eq {x y : Fin (n+1)} (h : x ≠ y) : ∃ z, y.succAbove z = x` — SuccPred.lean:661. Call `Fin.exists_succAbove_eq hj` with `hj : j ≠ i` yields `∃ z, i.succAbove z = j` (x:=j, y:=i).
- `div_mul_cancel₀ (a) (h : b≠0) : a/b*b = a` — GroupWithZero/Units/Basic.lean:337.
- `abs_div : |a/b| = |a|/|b|` — Algebra/Order/Field/Basic.lean:671.
- `Rat.cast_zero : ((0:ℚ):α) = 0` — Data/Rat/Cast/Defs.lean:127.

## Plan

`lrc5_rel_real`:
1. `hcirc t ht i : circ (t*w i) = circ (t*|w i|)` via `← circ_abs, abs_mul, abs_of_nonneg ht`.
2. `by_cases hrat : ∃ c:ℝ, ∀ i, ∃ q:ℚ, |w i| = c*↑q`.
   - YES: `choose q hq`; `c≠0`, `q i≠0` from `hupos`. `lrc5_rel_rat q hq0` → `s>0`, `circ (s*↑q i) ≥ 1/5`. Take `t := s/|c|`. Key: `|s/|c| * (c*↑q i)| = |s*↑q i|` since `|s/|c| * c| = s`; then `circ` kills sign via `← circ_abs`. Works uniformly for c<0 (no case split needed).
   - NO: `lrc5_real_of_irrational_ratio lrc4_rat_finset hupos hrat` (u unifies to `fun i => |w i|` by Miller pattern); `.le` on strict bound.

`lonely_runner_five`: copy LRC5/Main.lean:81–94 pattern verbatim minus ℚ casts:
relative speeds `v (i.succAbove j') − v i`, nonzero by injectivity; `lrc5_rel_real` → t>0;
`rw [dist_unitAddCircle_eq_circ]`, `hsub` by `ring`, `circ_neg`, exact `hwt j'`.

## Progress (tool calls 7–18)

- **Blocker found (not my file):** `Research07/M3/Dirichlet.lean:155` — committed broken
  (W7b skeleton never compiled): `Unknown identifier 'zmultiples'` + isDefEq timeout.
  Transitive dep of my file (`Main → BHK → OrbitClosure → FlowDense → Dirichlet`).
  **Minimal fix applied:** `zmultiples (1:ℝ)` → `AddSubgroup.zmultiples (1:ℝ)`
  (v4.34 requires the namespace qualifier). Proof body only; no statement touched.
  `lake build Research07.M3.Dirichlet` → ✔ 15s. FLAG for orchestrator: out-of-scope
  edit, unavoidable to build `M3.Main`.
- **Parse trap:** `|s / |c| * |w i||` — trailing `||` lexes as `Bool.or` token;
  `| … |` with space before close-bar is rejected ("expected no space before").
  Fix: outer abs written as function app `abs (s / |c| * |w i|)` — same `Expr`
  (`Abs.abs`), so `rw [habs i]` still matches `← circ_abs`-produced `|·|` subterms.
- `lake build Research07.M3.Main` → **✔ Built (8940 jobs), zero errors, zero
  warnings on M3.Main itself.** Remaining `sorry` warnings are all in frozen
  upstream files (LRC4/Main, LRC4/IntCase, M3/Relations, Subtorus, FlowDense,
  OrbitClosure, BHK) — other work packages, expected.
- **Axioms:** `#print axioms lrc5_rel_real` / `lonely_runner_five` →
  `[propext, sorryAx, Classical.choice, Quot.sound]`. `sorryAx` is inherited from
  still-sorry'd frozen deps (`lrc5_real_of_irrational_ratio` BHK.lean:47,
  `lrc4_rat_finset` LRC4/Main.24); M3/Main.lean itself contains no `sorry`/`admit`/
  `native_decide`/`unsafe` (grep-verified). Once W5+W9 land, axioms reduce to the
  standard three.

## Proof structure (final, M3/Main.lean:24–85)

- `hcirc` (line 28): `circ (t*w i) = circ (t*|w i|)` for `t ≥ 0` via
  `← circ_abs, abs_mul, abs_of_nonneg`.
- Dichotomy `by_cases hrat : ∃ c:ℝ, ∀i, ∃q:ℚ, |w i| = c*↑q` (line 32) — matches
  `hirr` of `lrc5_real_of_irrational_ratio` verbatim after `u := fun i ↦ |w i|`
  (Miller-pattern unification via `hupos`).
- Rational branch (35–60): `choose q hq`; `hc0`, `hq0` from `hupos`; `s` from
  `lrc5_rel_rat q hq0`; **`t := s / |c|`** — sign of `c` handled *uniformly*:
  `hsc : |s/|c| * c| = s` (abs_mul/abs_div/abs_abs + `div_mul_cancel₀`),
  `habs : abs (s/|c| * |w i|) = |s * ↑(q i)|`, `key` closes via `← circ_abs`.
  No `c<0`/`c>0` case split needed — `|c|` kills it.
- Irrational branch (61–63): `lrc5_real_of_irrational_ratio lrc4_rat_finset hupos
  hrat`; `(hwt i).le` on strict `1/5 <`.
- `lonely_runner_five` (74–85): verbatim LRC5/Main.lean pattern — `Fin.succAbove`
  relative speeds, `Fin.exists_succAbove_eq`, `dist_unitAddCircle_eq_circ`,
  `ring` + `circ_neg`.

## Flags for orchestrator

1. `Research07/M3/Dirichlet.lean` was committed non-compiling; applied minimal
   namespace fix (line 155). W7b's file — verify their remaining work builds on it.
2. Untracked stray `Research07/W6Scratch.lean` sits in the import tree (W6
   countermodel scratch; nothing imports it). Not mine — left in place.
3. `M3/Main.lean` is DONE per contract: `lake build Research07.M3.Main` clean,
   both sorries proved, no new axioms beyond dep-inherited `sorryAx`.

## Status: COMPLETE.
