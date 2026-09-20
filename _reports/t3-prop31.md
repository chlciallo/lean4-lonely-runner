# T3 — Prop 3.1 (two multiples of 3) — work log

Task: `Research07/LRC6/Prop31.lean`, prove
`prop3_1 {D : Finset ℕ} (hpos : ∀ d ∈ D, 0 < d) (hcard : D.card = 5) (h3two : (D.filter (fun d => 3 ∣ d)).card = 2) (hf : hfail D) : False`

## Paper structure (renault.txt §3, lines ~72-95)

- Two multiples of 3: v₁,v₂. Others (v₃,v₄,v₅) non-mult-3 (we get exactly 2 via `h3two`; paper uses Lemma 2.3 since its hypothesis is ≥2).
- Lemma 2.1 (l=6) → 6|v₁ or 6|v₂.
- **Argument 1**: t with v₁,v₂ safe + ≥2 others unsafe → ∃ l∈{0,1,2}, t+l/3 all-safe. Mechanism: unsafe runners (non-mult-3) each have bad-shift set ⊆ {0} ⇒ safe at l∈{1,2}; ≤1 safe non-mult-3 runner blocks ≤1 of {1,2}.
- **Argument 2**: t with v₁,v₂ safe + some runner i (non-mult-3) at xᵢ∈{1/6,1/2,5/6} → ∃ l all-safe. Mechanism: runner at boundary is safe at ALL three shifts ({x,x±1/3} = {1/6,1/2,5/6}); other two non-mult-3 block ≤2 shifts.
- **Extremization**: T={t: x₃(t)=5/6}, t̂ maximizes min{N(x₁),N(x₂)}.
  KEY REALIZATION (paper's "definition of t̂ implies N(x₂(3t̂)) ≤ N(x₁(t̂))"):
  at s with x_w(s) ∈ {1/6,1/2,5/6}, some l∈{0,1,2} puts x_w(s+l/3)=5/6 (needs 3∤w);
  mult-3 runners satisfy xᵢ(s+l/3)=xᵢ(s). So min{N₁,N₂}(s)=min(s+l/3)≤ max over T.
  ⇒ boundary corollary: x_w(s)∈{1/6,1/2,5/6} → min ≤ δ := min at t̂.
- At t̂: x₃=5/6 boundary → Arg2 ⇒ not both safe ⇒ min <1/6. WLOG N(x₂)≥N(x₁), so x₁ unsafe, δ=N(x₁(t̂))<1/6.
- Goal x₁(t̂)=0. Assume δ>0.
  - 3t̂: x₃=1/2 ⇒ min≤δ; N₁(3t̂)=3δ>δ ⇒ N₂(3t̂)≤δ<1/6 (b unsafe).
  - 5t̂: x₃=1/6 ⇒ same ⇒ N₂(5t̂)≤δ.
  - Preimages ⇒ x₂(t̂) ∈ (29/30,1/30)∪(11/30,7/18)∪(11/18,19/30).
    First interval ⇒ N₂(3t̂)=3N₂>N₂≥δ contradiction. Remaining ⇒ b safe at 2t̂,4t̂;
    x₂(3t̂)∈(1/10,1/6)∪(5/6,9/10) ⇒ δ>1/10 ⇒ x₁(t̂)∈(1/10,1/6)∪(5/6,9/10).
  - Cases (eᵢ = vᵢ mod 6 ∈{0,3} for i=1,2; 6|vᵢ ⇔ eᵢ=0):
    * (0,0): e₃=±1 → s=2t̂±1/6 ∈T (x₃=5/6), N₁=2δ, b safe ⇒ min>δ contra.
      e₃=±2 → w even ⇒ v₄,v₅ odd (Lemma2.1 ≤3 evens, needs hodd).
      2t̂,2t̂+1/2: a,b,w safe ⇒ some u∈{u,u'} unsafe each; same one impossible
      (odd ⇒ +1/2 flips to (1/3,2/3) safe) ⇒ z unsafe at 2t̂, z' unsafe at 2t̂+1/2
      ⇒ x_{z'}(2t̂)∈(1/3,2/3). t̃=4t̂+1/2 all safe ⇒ contra.
    * (6|a, e_b=3): e₃=±1 → 2t̂±1/6; e₃=±2 → 3t̂±1/6. x_a: ⟨λx_a⟩ (mult6), N=λδ;
      x_b: ⟨λx_b+1/2⟩ (e_b=3) ∈ safe ⇒ contra.
    * (e_a=3, 6|b): e₃=±1 → 2t̂±1/6 (x_a=⟨2x_a+1/2⟩ safe, x_b=⟨2x_b⟩ safe).
      e₃=±2 → s₁=t̂±1/6 has x_w=1/6, a,b safe; s₂=-s₁ ∈T(x_w=5/6), circ same ≥1/6 ⇒ contra.
  - ⇒ x₁(t̂)=0 ⇒ ∀t∈T: min=0 ⇒ some mult-3 at 0. At t=-1/(6v₃): 6v₃|v₁ or v₂.
- Per w∈R: 6w|v₁∨6w|v₂. Pigeonhole: m∈{v₁,v₂} hit twice (6u|m,6u'|m),
  third z: 6z|m∨6z|n (n=other). Lemma2.2 ⇒ 5n>m, 5m>n.
- t̄=1/(6m): x_m=1/6 safe, x_u,x_u'∈(0,1/36] unsafe. If n safe → Arg1 contra.
  Else x_n(t̄)∈(1/30,1/6) (n<5m,5n>m). s=5/(6m): m,n safe, u,u' unsafe → Arg1.

## Infrastructure found

- `safe6 d t := Int.fract (d*t) ∈ Icc 1/6 5/6`; `hfail D := ∀t ∃d∈D ¬safe6`; `not_hfail_iff`.
- Reduction.lean: `hfail_exists_dvd` (l∈{2..6}), `lemma2_2` (∃j≠i, i<5j), `lemma2_3`,
  `mult3_le_three`, `bad_third_le_one` (pairwise: l₁<l₂<3 → safe at one), `exists_good_third`,
  `exists_common_good_third`, `fract_third_shift`, `safe6_third_shift_of_dvd`,
  `safe6_of_circ_ge_fifth`, `unsafe_arc`, `unsafe_pair_abs`, `fract_add_small`.
- Setup.lean: `circ_ge_sixth_fract`, `circ_ge_fifth_fract`, `fract_add_shift`,
  `fract_nat_mul`, `fract_self_add`, `fract_lambda_alpha` (ℕ-shift), `fract_signed_shift` (ℤ-shift, e mod 6),
  `fract_improve`, `fract_signed_shift_anchor`, `off`/`abs_off`, `fract_eq_off`,
  `topBdry6`/`botBdry6`+pos+mem, `fract_neg_mem_Icc`, `fract_neg_eq_zero`.
- Driver.lean: `improve_ge_two_contra`, `improve_eq_one_contra`, `fract_intCast_div_six`,
  `alpha_Icc/Ico`, `neg_alpha_Icc/Ico`, `signed_alpha_Icc`, `circ_of_fract_lt_half`.
- Prop41.lean: `fract_int_mul` (ℤ mult), `fract_add_eq_fract_add_fract`,
  `closed_unsafe_arc`, `unsafe_add_shift_Icc`, `unsafe_add_shift_Ioo` (unsafe+{1/3,1/2,2/3}→safe!),
  `unsafe_pair_sixth`, `safe6_sixth_shift_anchor`, `safe6_sixth_shift_zero`,
  `all_safe_contra` (5 safe6 + hfail {a,b,c,z,y} → False).
- Extremize.lean: `renault6_maximize`, `forward/backward_endpoint6`, `exists_improve_eq_one`,
  `circ_max_of_fract_max`, `exists_pos_forall_mul_lt`.
- `lrc5_int D hpos (card≤4) : ∃t>0 ∀d∈D, 1/5 ≤ circ(t*d)`.
- circ: `circ x = ‖(x:UnitAddCircle)‖ = |x−round x|`; `circ_add_int`, `circ_neg`, `circ_le_half`,
  `circ_of_fract_lt_half`, `abs_sub_round_eq_min` (Mathlib: |x−round x| = min(fract,1−fract)? used in Setup).

## Plan (file layout)

1. Helpers: `circ_eq_zero_iff`, `circ_mul_lt_half` (circ=|z| for |z|≤1/2), `circ_nat_mul_gt` (0<circ<1/6, k∈{2..5} → circ(k·)>circ).
2. Third-shift boundary: `safe6_third_shift_boundary` (x∈{1/6,1/2,5/6} ⇒ safe all l<3), `third_shift_to_five_six` (∃l<3: x=5/6), `fract_third_of_dvd` (3|d ⇒ pos unchanged).
3. `arg1`, `arg2` (concrete 5-element hfail contradictions).
4. Unsafe preimage unions for ×3, ×5 → x_b membership + corollaries.
5. Extremization over discrete T (k:ℤ param, period w).
6. `anchor_eq_zero` (big middle casework).
7. `key_per_w` → 6w|v₁∨6w|v₂.
8. Pigeonhole + lemma2_2 + final t̄,s + arg1.
9. gcd reduction: prop31_core under hodd (∃ odd); main via D'=D.image(·/gcd).

## Log
- (start) read renault.txt §3, Reduction/Setup/Extremize/Driver/Prop41/Prop66.
- (cont) Build check: dead agent's 3 helpers DO NOT compile — bit-rot errors:
  `circ_eq_abs_of_abs_le_half` fails at x=0 branch (`fract x = x+1` needs x<0 strictly; min_eq_right side cond);
  `circ_lt_circ_nat_mul`: `neg_le_abs_self` renamed → `neg_le_abs`; gcongr now closes goal early ("No goals");
  min_comm unification needs explicit `show` rewrites of `1-(kz+1)` etc.
  Verified paper §3 (lines 72-93): full structure confirmed.
  Mathlib sigs: `Int.fract_eq_iff : fract a = b ↔ 0≤b ∧ b<1 ∧ ∃z:ℤ, a-b=z`;
  `fract_eq_zero_iff : fract a = 0 ↔ a ∈ range Int.cast`; `fract_neg (hx : fract x ≠ 0)`;
  `min_eq_left (h:a≤b) : min a b = a`; `fract_div_natCast_eq_div_natCast_mod : fract(m/n)=(m%n)/n`.
- (cont) FIXED bit-rot: file compiles clean again (3 helpers repaired: eq_or_lt split for x=0,
  `neg_le_abs`, explicit mul_le_mul_of_nonneg_left, show-rewrites + min_comm).
  Plan of attack settled: uniform improving-move engine `s = λt̂ + α/6` (λ∈{1..4}, α∈{1,3,5})
  via `fract_lambda_alpha` — negative paper shifts become α=5 (positions mod-1 equal).
  All per-cell work = `x_w(s) ∈ {1/6,1/2,5/6}` (→ min≤δ) + `circ(m·s),circ(n·s) > δ`.
  gcd reduction decided: prop3_1 reduces to `D' = D.image (·/g)` (g=gcd≥1 always works,
  no case split): card 5 (injOn via g|d), hpos (div_pos), hfail (t→t/g scaling),
  filter card 2 (needs 3∤g from h3two<5), gcd=1 (g·gcd'|g). Needed for the
  (6|m,6|n, e_w∈{2,4}) cell which needs w₄,w₅ odd via `mult2_le_three`.

## 2026-09-19 — Batch 2: boundary/third-shift/arg1/arg2 layer COMPILES

### Status
`lake env lean Research07/LRC6/Prop31.lean` → exit 0 (warnings only). File is 489 lines.

### Declarations now in Prop31.lean (all compiling)
- circ layer: `circ_eq_zero_iff`, `circ_eq_abs_of_abs_le_half`, `circ_lt_circ_nat_mul` (needs `0 < circ x`, `circ x < 1/6`, `2 ≤ k ≤ 5` → `circ x < circ (k*x)`), `circ_fract`, `circ_third_shift_of_dvd`, `circ_two_mul_of_quarter`, `circ_two_mul_fract`
- fract layer: `fract_add_eq_fract_add_fract`, `fract_eq_of_floor`, `fract_mul_div_three` (`fract (d*l/3) = (d*l % 3)/3`), `unsafe_add_shift_Ioo`
- third-shift: `safe6_third_shift_boundary` (x_w ∈ {1/6,1/2,5/6} stays safe under ALL l/3 shifts — even works without ¬3∣w since shifted positions stay in the boundary set), `third_shift_to_five_six` (boundary position → ∃ l<3 putting w exactly on 5/6)
- half-shift: `exists_good_half` (odd runner safe at t or t+1/2), `safe6_half_shift_of_dvd`
- `mult2_le_three` (l=2 mirror of `mult3_le_three`; needs gcd=1)
- `all_safe5_contra`, `arg1` (renault Argument 1), `arg2` (Argument 2)

### Key Lean lessons learned (build-failure driven)
- `by tac` inside a rw-TERM does NOT throw on failure: it logs "unsolved goals" and elaboration continues with sorryAx → `first | (rw [lem.mpr ⟨by norm_num,_⟩] ...) | ...` NEVER backtracks. For case-discriminating proofs use `norm_num [Int.fract]` (norm_num evaluates `Int.fract` of rational literals!) or `have`+`rw` (match failure is a real exception).
- `interval_cases h : expr` substitutes the expression with a literal everywhere incl. inside casts → `↑(k:ℕ)`; `push_cast` normalizes `↑(0/1/2 : ℕ)` to literals already (no extra simp needed; `simp only [Nat.cast_ofNat]` reports "no progress").
- `Int.fract_div_natCast_eq_div_natCast_mod` needs the denominator written `((3:ℕ):ℝ)`; `(3:ℝ)` won't match `↑?n`.
- `rw` closes goals by rfl-check: `rw [Nat.mul_mod, hw]` on `(w*l)%3 = k` closes it — trailing `norm_num` errors "no goals".
- `Nat.even_iff.mp h : d % 2 = 0` (not `2∣d`); use `even_iff_two_dvd.mp`. `Odd d` IS `∃ k, d = 2*k+1` definitionally.
- `fract_add_shift d t s : fract (↑d*(t+s)) = fract (fract(↑d*t) + ↑d*s)` — note `↑d*s` form; to get `↑d/2` use `← mul_div_assoc` then `mul_one`.
- `unsafe_pair_abs hu hv : |fract u - fract v| < 1/6 ∨ 2/3 < |fract u - fract v|`.
- `lrc5_int D hpos (hcard : card ≤ 4) : ∃ t, 0 < t ∧ ∀ d ∈ D, 1/5 ≤ circ (t*d)`; `safe6_of_circ_ge_fifth` bridges.
- `safe6_iff : safe6 d t ↔ 1/6 ≤ circ (↑d*t)`.

### Full paper argument decoded (renault.txt lines 73–93)
1. Extract v1,v2 (3|·), v3,v4,v5 (¬3|·); `hfail_exists_dvd l=6` → 6|v1 or 6|v2.
2. T = {t : x₃(t) = 5/6}; t̂ maximizes `min(circ v₁·, circ v₂·)` over T. Discrete set → finite image under k↦(k+5/6)/v₃, k mod v₃ → `Finset.range v₃` image + `Finset.max'`.
3. Maximality extends to ALL times with x₃ ∈ {1/6,1/2,5/6}: shift s by l/3 (`third_shift_to_five_six`) → x₃(s')=5/6 → min ≤ m; circ(vᵢ·(s+l/3)) = circ(vᵢ·s) by `circ_third_shift_of_dvd`.
4. arg2 at t̂ → not both safe → m < 1/6. WLOG N₂≥N₁ → N₁<1/6 (unsafe).
5. Assume x₁(t̂)≠0. `circ_lt_circ_nat_mul` k=3,5: N₁(3t̂),N₁(5t̂) > N₁(t̂). Maximality at 3t̂ (x₃=1/2), 5t̂ (x₃=1/6) → N₂(3t̂),N₂(5t̂) ≤ N₁(t̂) < 1/6 → ⟨3x₂⟩,⟨5x₂⟩ unsafe.
6. Interval solve (floor-case split, `interval_cases` on ⌊3x₂⌋∈{0,1,2}, ⌊5x₂⌋∈{0..4}, unsafe_arc on each → 60 linarith combos): x₂ ∈ (0,1/30)∪(29/30,1)∪(11/30,7/18)∪(11/18,19/30).
7. (0,1/30)∪(29/30,1) branches: circ(3x₂)=3circ x₂ > circ x₂ ≥ m contradiction (or x₂=0→m=0→x₁=0 goal). Remaining: x₂ ∈ (11/30,7/18)∪(11/18,19/30) → runner2 safe at 2t̂,4t̂; ⟨3x₂⟩ ∈ (1/10,1/6)∪(5/6,9/10) → N₂(3t̂)>1/10 → N₁(t̂)>1/10 → x₁ ∈ (1/10,1/6)∪(5/6,9/10).
8. Case split on (6|v₁,6|v₂)×e₃: e₃=±1 → t=2t̂±1/6 ∈ T, min>m contradiction; e₃=±2 → (a) if both 6|vᵢ: v₄,v₅ odd (mult2_le_three, NEEDS gcd=1) → runners 1,2,3 safe at 2t̂ and 2t̂+1/2 → unsafe runner ∈{4,5} each time, odd ⇒ different runners → x₄(2t̂)∈(5/6,1/6), x₅(2t̂)∈(1/3,2/3) (wlog) → t̃=4t̂+1/2 all safe → hfail contradiction; (b) if only one 6|vᵢ: t=3t̂±1/6 ∈ T, min>m contradiction; (c) e₃=±2 with e-pattern (3,0): t=-(t̂±1/6) ∈ T, circ preserved (circ(-x)=circ x), min≥1/6>m.
9. ⟹ x₁(t̂)=0 ⟹ ∀t∈T: min(N₁,N₂)=0 → x₁=0∨x₂=0 at t. t=-1/(6v₃) → 6v₃|v₁∨6v₃|v₂. Same for v₄,v₅.
10. Pigeonhole+wlog: 6v₄|v₁,6v₅|v₁,6v₃|v₁∨v₂ → lemma2_2 case analysis → v₁<5v₂ ∧ v₂<5v₁ (j∈{v₃,v₄,v₅} cases collapse via ≤/6 bounds).
11. t̄=1/(6v₁): x₁=1/6 safe, x₄,x₅∈(0,1/36] unsafe (6v₄,6v₅|v₁) → runner2 unsafe → x₂=v₂/(6v₁)∈(0,1/6)∪(5/6,1); v₂<5v₁ forces (0,1/6); 5v₂>v₁ forces (1/30,1/6). s=5/(6v₁): x₁=5/6,x₂∈(1/6,5/6) safe; x₄,x₅∈(0,5/36] unsafe → arg1 → False.

### Remaining work (ordered)
- [ ] `hfail_image_div`/`hfail_div` (hfail is scale-invariant: hfail D → hfail (D.image (·/g)))
- [ ] gcd-1 reduction wrapper for prop3_1
- [ ] `exists_T_max` (discrete max over {x₃=5/6})
- [ ] `boundary_min_le` (maximality at boundary positions via third-shift)
- [ ] `unsafe35_intervals` (floor-split lemma)
- [ ] x₁=0 case analysis (steps 5–8)
- [ ] 6w|vᵢ consequence + pigeonhole + lemma2_2 chains
- [ ] endgame at 1/(6v₁), 5/(6v₁) + arg1

## 2026-09-19 — Batch 3: `exists_min_circ_max` FIXED, scale/max layer COMPILES

### Status
`lake env lean Research07/LRC6/Prop31.lean` → **exit 0**. File ~589 lines.

### New declarations (compiling)
- `hfail_div` (L491): `hfail D → hfail (D.image (·/g))` for `0<g`, `g ∣ ∀d∈D` — scale invariance.
- `exists_min_circ_max` (L507): `∃ th, fract(w·th)=5/6 ∧ ∀t, fract(w·t)=5/6 → min(circ v₁t)(circ v₂t) ≤ min(circ v₁th)(circ v₂th)`. Method: `τ k = (↑k+5/6)/↑w`, max over `Finset.range w` via `Finset.exists_max_image`; arbitrary `t` reduces via `n=⌊w·t⌋`, `k'=(n%↑w).toNat`, and `circ(v·t)=circ(v·τk')` since `v·t = v·τk' + ↑(v·(n/↑w))` (`circ_add_int`).
- `boundary_min_le` (L578): boundary `{1/6,1/2,5/6}` positions inherit the `min≤m` bound via `third_shift_to_five_six` + `circ_third_shift_of_dvd`.

### Fixes applied (see _dev/failures.md 2026-09-19 entry)
- `by exact_mod_cast` inside `Int.toNat_of_nonneg` left `?b` mvar → pin `(show (w:ℤ) ≠ 0 by ...)`, drop wrong `.symm`.
- `Int.ediv_add_emod` → real name `Int.mul_ediv_add_emod`.
- `field_simp` closed `hvt` → drop trailing `ring`.
- `rw [hτv]` pattern absent → restructured: prove `(k':ℝ) = ↑n - ↑w*↑(n/↑w)` (`congrArg Int.cast` + `push_cast`), then `rw [hvt, hnt]; simp only [hτ]; rw [hk'r]; push_cast; field_simp; ring`.

## 2026-09-19 — Batch 3: interval layer LANDED, file compiles clean (747 lines)

### Status
`lake env lean Research07/LRC6/Prop31.lean` → exit 0, warnings only
(unreachable `exfalso; linarith` at line 634 — cosmetic).

NOTE: file was concurrently edited this session (591→747 lines).
Interval-arithmetic layer added by earlier/parallel session and now compiles:

- `fract_of_between` (fract x = x-n on [n,n+1)), `circ_eq_of_between`
- `unsafe35_union` — y∈(0,1), circ(3y),circ(5y)<1/6 →
  y ∈ (0,1/30)∪(29/30,1)∪(11/30,7/18)∪(11/18,19/30)  [the step-8 floor-split, DONE]
- `runner2_facts` — y ∈ (11/30,7/18)∪(11/18,19/30) → circ y ∈(11/30,7/18),
  circ(2y)∈(2/9,4/15), circ(2y+1/2)∈(7/30,5/18), circ(3y+1/2)∈(1/3,2/5),
  fract(2y),fract(4y) ∈ Icc[1/6,5/6], fract(3y) ∈ (1/10,1/6)∪(5/6,9/10)
- `runner1_facts` — y ∈ (1/10,1/6)∪(5/6,9/10) → circ(2y)=2circ y,
  circ(2y+1/2)∈(1/6,3/10), circ(y+1/2)∈(1/3,2/5), fract(2y),fract(4y) ∈ Icc
- `runner1_interval` — 0≤y<1, circ y ∈ (1/10,1/6) → y∈(1/10,1/6)∪(5/6,9/10)

### Fix applied this session
- line ~745 `runner1_interval`: `Or.inr ⟨by linarith, h.2⟩` → `⟨by linarith, by linarith⟩`
  (h.2 : 1/10 < 1-y, needed y < 9/10 — linarith closes both).

### Remaining (my plan, ordered)
- [ ] `fract_lambda_signed` (λt + sh/6, sh:ℤ — for 2t̂±1/6, 3t̂±1/6, t̂±1/6, -(s₁))
- [ ] `anchor_zero_side` — big casework: min-runner a, circ a ≤ circ b → circ(a t̂)=0
        cells: (e_a,e_b)∈{(0,0),(0,3),(3,0)} × w%6∈{1,2,4,5}
        (0,0)&e₃=±2 needs mult2_le_three (gcd=1) → d,e odd → t̃=4t̂+1/2 all safe
- [ ] `six_mul_dvd` per w∈{v₃,v₄,v₅}: exists_min_circ_max+boundary_min_le+arg2(min<1/6)+anchor → min=0 → at t=-1/(6w): 6w|v₁∨6w|v₂
- [ ] pigeonhole → m hit twice (6u,6u'|m), z third → lemma2_2 → 5n>m∧5m>n
- [ ] endgame t̄=1/(6m), s=5/(6m) + arg1
- [ ] `prop3_1` = gcd reduction (D.image (·/g)) + core under hgcd=1

## 2026-09-30 — `prop3_1` LANDED: file compiles clean, axioms clean

### Status — TASK COMPLETE
`lake env lean Research07/LRC6/Prop31.lean` → **exit 0**, warnings only.
`#print axioms prop3_1` → `[propext, Classical.choice, Quot.sound]` (gate ✓).
File: 2113 lines. Zero `sorry`/`admit`/`native_decide`/`unsafe`-keyword.

### New theorems added (L1663–2111)
- `six_mul_dvd` (L1663) — the `key_per_w`: at `t₀ = -1/(6w)`, `x_w = 5/6`,
  `min ≤ 0` ⇒ `min = 0` ⇒ `circ(v·t₀) = 0` unfolds via `circ_neg`,
  `circ_eq_zero_iff`, `Int.fract_eq_zero_iff` to `6w ∣ v`; cases via
  `min_choice` + `le_total` on `circ(a·th)` vs `circ(b·th)` (swapped call
  needs `Finset.insert_comm` for hpos/hgcd/hf and `min_comm` for hmax).
- `sixth_lt_of_dvd` (L1745) — copied verbatim from Prop41:1097
  (`6z ≤ a` ⇒ `fract(z·λ/(6a)) ∈ Ioo 0 (1/6)`, λ≤5).
- `endgame` (L1775) — generic over `{m,n,u,u',z} = D` bridge (`hset`):
  `lemma2_2` twice with membership rcases ⇒ `m < 5n ∧ n < 5m` in ALL
  subcases (the paper's "by symmetry" glosses a real case analysis:
  e.g. `6z∣n` lets `lemma2_2 m` return j=z giving `m < 5z ≤ 5n/6 < 5n`;
  omega discharges every branch). Then `t̄ = 1/(6m)`: `m` at `1/6` safe
  (`alpha_Icc` pattern), `u,u' ∈ (0,1/36]` unsafe (`sixth_lt_of_dvd`);
  `n` safe → `arg1` at `t̄`; else `xₙ(t̄) ∈ (1/30,1/6)` ⇒ `s = 5t̄`:
  `xₙ(s) = 5xₙ(t̄) ∈ (1/6,5/6)` safe, `u,u' ≤ 5/36` unsafe → `arg1` at `s`.
- `prop31_five` (L1893) — `hfail_exists_dvd (l=6)` ⇒ `6∣v₁ ∨ 6∣v₂`;
  three `six_mul_dvd` calls (w=v₃,v₄,v₅ with permed `hpos/hgcd/hf` for
  key4,key5 via `hperm4/hperm5`); 8-case `rcases` pigeonhole; two keys
  always agree ⇒ pick `m` twice-hit, apply `endgame` (identity or perm
  `hset` proofs by `ext;simp;rintro(rfl|…);simp`).
- `prop3_1` (L1971) — **the frozen statement**: `{D : Finset ℕ}`, card 5,
  `(D.filter (3∣·)).card = 2`, `hfail D` → `False`.
  `Finset.card_eq_succ`×2 extracts `T = {v₁,v₂}` (multiples),
  `card_sdiff_add_card_eq_card`+`card_eq_succ`×2 extracts `R = {v₃,v₄,v₅}`;
  `D = T∪R` via `sdiff_union_of_subset`. gcd reduction: `g := D.gcd id > 0`
  (`Nat.pos_of_dvd_of_pos`); `3∤g` (else filter = D, card 5≠2);
  `3∣d/g ↔ 3∣d` via `Nat.prime_three.coprime_iff_not_dvd` +
  `Coprime.dvd_of_dvd_mul_left`; quotient-gcd=1 via `g·g'∣g` +
  `dvd_mul_right` + `Nat.dvd_antisymm` + `mul_left_cancel₀`;
  `hfail_div` + `D.image (·/g) = {quotients}` (`Finset.image_insert` simp).

### Concurrent-session interaction
A parallel session fixed the `anchor_ordered` bullet-order permutation
itself (parity cells now sit at `w%6∈{2,4}` slots, matching `rcases`
order `1,2,4,5`). My earlier `hmw`-reorder fix was REVERTED (L1116) —
current file has the original `1∨2∨4∨5` disjunction.

### Fixes applied this session (ledger entries added)
- `hmw` reordered then reverted (parallel fix superseded).
- `six_mul_dvd`: `field_simp` closed goal (stray `ring`); `eq_div_iff`
  (not `div_eq_iff`) for `↑n = v/(6w)` orientation; `lt_or_ge` not `lt_or_le`.
- `endgame`/`prop31_five`: `hset.symm ▸` and `hset ▸` whnf timeouts →
  replaced by `rw [hset]`/`rw [← hset]` proof blocks; `lemma2_2 (i := m)`
  pins implicit to avoid mvar-goal `by`-blocks; `ext;simp;tauto` set-perm
  proofs hit `isDefEq` timeout → `constructor <;> rintro (rfl|…) <;> simp`.
- `prop3_1`: `rw [← hD]` direction (`hD : D = {vᵢ}`, rewrite `D`→literal
  needs `rw [hD]` in `∈ D` goals); `hRc` needed `rw [← hR] at hsplit`
  (omega can't see through `set`-bound `R`); `dvd_mul_of_dvd_right h g`
  already gives `3 ∣ g*(d/g)` (c*x not x*c); `Nat.mul_eq_one.mp` unknown →
  `Nat.dvd_antisymm`+`mul_left_cancel₀`.

### Gate summary
- build: exit 0 ✓
- axioms: `[propext, Classical.choice, Quot.sound]` ✓
- statement: `prop3_1 {D : Finset ℕ} (hpos : ∀ d ∈ D, 0 < d)
  (hcard : D.card = 5) (h3two : (D.filter (fun d => 3 ∣ d)).card = 2)
  (hf : hfail D) : False` — matches spec.
- NOTE: `Prop31.lean` is NOT yet imported by the umbrella `Research07.lean`
  (nor are Prop41/Prop54/Prop66 etc.) — standalone task file.

## Final verification pass (2026-09-18) — ALL GATES GREEN

### Linter cleanup
- Removed dead `| exfalso; linarith` fallback in `first` block (~L634, never-executed warning).
- `push_cast; ring` → `ring` (~L868, unused-tactic warning).
- `push_neg` → `push Not` ×3 (L924, L964, L1657 deprecation warnings).
- Result: `lake env lean Research07/LRC6/Prop31.lean` → exit 0, ZERO warnings.

### Gates
- `lake env lean -o ... Prop31.olean` → exit 0.
- `lake build` → **8959 jobs clean** (Prop31, IntCase, Main, Audit all built).
- Forbidden scan: no `sorry`/`admit`/`native_decide`/`unsafe` decls (only comment words).
- Axioms: `prop3_1`, `anchor_ordered`, `six_mul_dvd`, `prop31_five`, `lrc6_int`
  all `[propext, Classical.choice, Quot.sound]`.
- Frozen statement `prop3_1` unchanged; consumed at `LRC6/IntCase.lean:363`.

### Correction to earlier note
Prop31 IS reachable from the umbrella: `Research07.lean` → `LRC6.Main` →
`LRC6.IntCase` → `LRC6.Prop31` (so `#print axioms` coverage flows through
`lrc6_int`/`lrc6_rel_rat`/`lonely_runner_six_rat` in `Audit.lean`).

### Environment issue (recurring, known)
`lake build` intermittently fails with "failed to read file '<mathlib>.olean.private'"
on random mathlib modules — files are intact/readable (valid olean headers, right
version). Root cause = leftover `lake`/`lean` background processes holding olean
handles (same class as ledger's prior `transient-oleen-read + lock-contention` entry).
Fix: `taskkill` stray lake.exe/lean.exe, then retry `lake build` — converged after
~6 attempts first time, clean on attempt 1 after process cleanup.
