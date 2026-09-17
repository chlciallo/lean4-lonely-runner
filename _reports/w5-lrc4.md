# W5 — LRC4: Lonely Runner integer case (≤3 speeds, threshold 1/4) + rational corollary

Agent: W5 subagent. Started: (session start). Status: **in progress**.

## Task
- `Research07/LRC4/IntCase.lean`: `theorem lrc4_int (D : Finset ℕ) (hpos : ∀ d ∈ D, 0 < d) (hcard : D.card ≤ 3) : ∃ t : ℝ, 0 < t ∧ ∀ d ∈ D, (1/4 : ℝ) ≤ circ (t * d)`
- `Research07/LRC4/Main.lean`: `theorem lrc4_rel_rat (w : Fin 3 → ℚ) (hw : ∀ i, w i ≠ 0) : ∃ t : ℝ, 0 < t ∧ ∀ i, (1/4 : ℝ) ≤ circ (t * w i)`
- `circ` defined in `Research07/LRC3/Circ.lean`.
- Rules: no sorry/admit/native_decide/unsafe/new axioms.

## Progress log

### [T0] Setup
- Created this report. `_reports/` did not exist; created.
- Next: read `LRC3/Circ.lean`, `LRC5/IntCase.lean` (pad-to-card + gcd bridge), `LRC5/Main.lean` (clear denominators), `Research07.lean`/`Basic.lean` import wiring.

### [2026-09-17 ~17:20] W5 third attempt — environment + proof choice
- Env: `export PATH="$HOME/.elan/bin:$PATH"` then `lake env lean file.lean` works (Lean 4.34.0, mathlib v4.34.0). Mathlib import compiles fine.
- Read: `LRC3/Circ.lean` (circ API: `circ_eq` (|x−round x|), `circ_add_int`, `circ_neg`, `circ_abs`, `circ_half`, `circ_ge_third_iff`), `LRC3/TwoMoving.lean` (`two_moving : 0<a → 0<b → ∃ t>0, 1/3 ≤ circ(t*a) ∧ 1/3 ≤ circ(t*b)` — handles |D|≤2), `LRC3/Main.lean` (`dist_unitAddCircle_eq_circ`), `LRC5/Main.lean` (denominator-clearing template for `lrc4_rel_rat`), `LRC5/IntCase.lean` (p=5 machinery, too specialized to reuse).
- Downloaded `_external/chu.pdf` (useminar expository paper, contains Renault's [Ren04, Appendix A] n=4 proof in full); extracted to `_external/chu.txt`, §4.1 lines ~1229–1800.

## THE PROOF (Renault appendix A, reconstructed)
Write `x_i(t) := Int.fract (v_i * t)` (position on [0,1)); "safe" := x ∈ Icc (1/4) (3/4) ⟺ circ ≥ 1/4.
1. If no vᵢ ≡ 0 mod 4: `t = 1/4` works ({vᵢ/4} ∈ {1/4,1/2,3/4}).
2. Else some `a ≡ 0 mod 4`; call the others u,v. Let `T = {t : u,v safe}`.
   - `two_moving` + circ-continuity ⇒ T contains an open interval around some τ' ∈ (0,1) (shift τ by −⌊τ⌋ using `circ_add_int`; margin 1/3>1/4 gives δ-ball of radius min(1/(12u),1/(12v),…)).
   - `K := T ∩ Icc 0 1` compact nonempty. If ∃ t∈K with a safe → done. Else `circ(a·)<1/4` on K, so `φ(t) := a*t − round(a*t)` is continuous on K (round locally const since |φ|<1/4<1/2) → argmax t₀, argmin t₁ exist (`IsCompact.exists_isMaxOn`).
   - φ≢0 on K (interval J: at takes interval of values, pick t* with at*∉ℤ) ⇒ M:=φ(t₀)>0 or m:=φ(t₁)<0.
   - M>0 case: x_a(t₀)=M∈(0,1/4). Maximality ⇒ some runner at 3/4 (else t₀+ε∈K with φ>M: ε < min((3/4−x_u)/u,(3/4−x_v)/v,(1/4−M)/a,(1−t₀),t₀)/2…). Say x_u(t₀)=3/4 (else swap u,v).
   - M≤0 ⇒ m<0: at t₁, x_a(t₁)=m+1∈(3/4,1); minimality ⇒ some runner at 1/4 (backward-exit). Mirror s₀=−t₁: x_a(s₀)=1−x_a(t₁)∈(0,1/4), runner at 3/4 (1−1/4), and region-max `∀t∈T, x_a(t)<1/4 → x_a(t)≤x_a(s₀)` (via φ(−t+1)=−φ(t): φ odd + 1-periodic). Same config → core lemma.
3. **Core lemma** (inputs: a,u,v>0, 4|a, ¬(2|u ∧ 2|v), t₀, x_a(t₀)∈(0,1/4), x_u(t₀)=3/4, x_v(t₀)∈Icc, region-max `∀t, x_u∈Icc → x_v∈Icc → x_a(t)<1/4 → x_a(t)≤x_a(t₀)`):
   - key fract identities: `x_d(t+s) = fract(x_d(t) + d*s)` via `Int.fract_add_int`; `x_d(k*t) = fract(k*x_d(t))`.
   - Case **v even** ⇒ u odd (hpar; else all even). x_u(t₀+½)=fract(3/4+u/2)=1/4 (u odd); x_v(t₀+½)=x_v(t₀) (v even); x_a(t₀+½)=x_a(t₀) (a/2=2m∈ℤ).
     - x_v(t₀)<3/4: t=t₀+½+ε, ε<min(1/(2u),(3/4−x_v)/v,(1/4−M)/a): x_u=1/4+uε∈[1/4,3/4], x_v=x_v(t₀)+vε<3/4 safe, x_a=M+aε∈(M,1/4) ⇒ region-max violated ⇒ **case impossible**.
     - x_v(t₀)=3/4: t=2t₀: x_u=x_v=fract(3/2)=1/2 safe; x_a=2M. If 2M<1/4 → region-max violated (2t₀∈T) ⇒ impossible; else 2M∈[1/4,1/2) ⇒ **t=2t₀ is the answer**.
   - Case **v odd**: t₁'=3t₀, t₂'=3t₀+½. x_u(3t₀)=fract(9/4)=1/4; x_u(3t₀+½)=fract(1/4+u/2)∈{1/4(u even),3/4(u odd)} — safe either way. x_a=3M at both (a/2∈ℤ). x_v(3t₀)=fract(3x_v), x_v(3t₀+½)=fract(3x_v+½) (v odd) — antipodal ⇒ one safe. Pick that t: x_a=3M<3/4; if <1/4 → region-max violated; else **output t**.
   - Output |t| (circ even ⇒ sign irrelevant; t≠0 since x_v∈Icc ⇒ vt∉ℤ).
4. **Driver assembles**: card≤2 → two_moving; card 3 → not-all-even? all-even → halve + well-founded IH on sum; else residues mod 4: none≡0 → t=1/4; some a≡0 → Renault driver → core lemma.

## Formalization plan (IntCase.lean)
- `circ_ge_quarter_iff : 1/4 ≤ circ x ↔ ∃ k:ℤ, x ∈ Icc (k+1/4) (k+3/4)` — clone `circ_ge_third_iff` proof.
- `circ_ge_quarter_fract : 1/4 ≤ circ x ↔ Int.fract x ∈ Icc (1/4) (3/4)` — bridge lemma.
- fract helpers, `renault_core`, `renault_driver`, main induction `Nat.strong_induction_on` on `D.sum id`.
- Main.lean: clone `lrc5_rel_rat` (B=∏den, a_i=num·B/den, natAbs image, card≤3); `lrc4_rat_finset` directly via image of `(q*B).natAbs`-ish.

### [2026-09-17 ~19:00] W5 COMPLETE — orchestrator finished manually (agent died again)

The third W5 agent (`6d65c149`) died from a connection failure but left ~880 lines
of fully-compiling machinery: quarter-threshold lemmas, fract identities,
`topBdry`/`botBdry` finite sets, `forward_endpoint`/`backward_endpoint`, and
`renault_core`. The orchestrator completed the remaining ~300 lines:

- **`renault_driver`**: seed construction. `two_moving` gives τ₀ with
  `circ ≥ 1/3` margin on u,v ⇒ `fract ∈ Icc (1/3) (2/3)` ⊂ interior of the
  quarter-safe zone. If `off a τ₀ = 0`, perturb by
  `ε₁ = min(1/(24u), 1/(24v), 1/(8a))`: `u·ε₁ ≤ 1/24` keeps u,v safe via
  `fract_add_shift` + `Int.fract_eq_self`, and `a·(τ₀+ε₁) = round(a·τ₀) + a·ε₁`
  with `round_of_quarter` ⇒ `off a (τ₀+ε₁) = a·ε₁ > 0`.
- **Positive seed**: `forward_endpoint` pushes into `Ftop` (finite filtered
  boundary set), `exists_max_image` yields t₀ with `off a t₀ > 0` and the
  region-max property `hmax`; dispatch to `renault_core` (u or v on top
  boundary, symmetric case swaps u,v).
- **Negative seed**: `backward_endpoint` into `Fbot`, `exists_max_image` on
  `-off a` yields t₁ with `off a t₁ < 0`; reflect `s₀ = -t₁` —
  `Int.fract_neg` sends `1/4`-boundary to `3/4` and preserves the safe
  interval, `fract(a·s₀) = -off a t₁ ∈ (0, 1/4)`; same `renault_core`.
- **`lrc4_int`**: `Nat.strong_induction_on` on `D.sum id`. Cards 0/1/2 via
  `two_moving`. Card 3: all-even → halve (`Nat.div_pos`, injectivity of `·/2`
  on evens) + IH; else mod-4 residues — none ≡ 0 → `t = 1/4`
  (`Int.fract_natCast_add`, `interval_cases`); some `a ≡ 0 mod 4` →
  `renault_driver` with the right parity hypothesis.
- **`Main.lean`**: `lrc4_rel_rat` (Fin-3 denominator clearing, clone of
  `lrc5_rel_rat`), `lrc4_rat_finset` (S.image of `num.natAbs · (B/den)`).

## Verified facts (kernel-audited, final)

- `lake build`: clean, 8944 jobs.
- `#print axioms lrc4_int` = `[propext, Classical.choice, Quot.sound]` — NO sorryAx.
- `#print axioms lrc4_rel_rat`, `lrc4_rat_finset`: same, clean.
- `#print axioms lonely_runner_five` = `[propext, Classical.choice, Quot.sound]`
  — the full real-speeds LRC n=5 now compiles sorry-free end to end.

## Traps encountered (for future reference)

- `rw [h0]` where `h0 : a*τ₀ = ↑(round (a*τ₀))` rewrites INSIDE `round(...)`
  on the RHS producing `round(round(...))` — use `rw [← h0]` on the target
  instead.
- `Int.fract_neg` exists in Mathlib (don't re-derive); `round_neg` does NOT —
  use `round_eq_iff` + `round_of_quarter`.
- `off a (-t) = -off a t` is FALSE unconditionally (`a·t ≡ 1/2 mod 1`
  counterexample); needs `|off a t| < 1/4`.
- `Finset.exists_max_image` works on the finite boundary sets — no
  compactness/continuity needed (endpoint lemmas already land in
  `topBdry ∪ topBdry`).
- `rcases rfl` on `d = a` eliminates `a` (breaks later `half_eq a …`);
  use `rw [hda]` to rewrite `d → a` keeping names alive.
- `Nat.div_add_mod d 4 : 4 * (d/4) + d%4 = d` — divisor FIRST.
- `interval_cases h : d % 4` rewrites `d%4` to literals in hyps — `hmod0`
  becomes `0 ≠ 0`, so `absurd rfl hmod0` (not `absurd h`).
