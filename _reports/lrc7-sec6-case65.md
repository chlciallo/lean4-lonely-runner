# case65 (§6.5) implementation log

Task: implement `case65` in `Research07/LRC7/Case5mC65.lean` — §6.5: A₁∪A₄, |A₁|=3 class s, |A₄|=2 class 4s.

## 2026-?? — session start
- Repo: D:\creation\Research_Projects\07. File sizes confirmed.
- Next: read spec §4 case-65 + ERRATUM/Addendum sections; paper §6.5 bs7.txt ~1045-1113; check lemma9_ii/lemma10 status in Case5mL10.

## Session A — recon complete (key signatures + structure)

### Sibling-file status
- `Case5mC64.lean` (1079 ln) is WIP: ends in 3 `sorry` (case64's `e13=0` scalar branch + case(ii) branches unfinished). NOT a finished model.
- `Case5mC62.lean` (390 ln, COMPLETE) is the cleanest model for helpers: `case62_resid_add`, `case62_qdig_sub_top`, `case62_qdig_sub_smul_top`, `case62_smul_top_resid`, `case62_nu_smul_top`, `case62_runit_smul_top` — all private; will clone what's needed.
- `Case66.lean` (517 ln) complete; `Case5mC61.lean` (1240 ln) complete.

### Landed tree lemmas (all verified present)
- `lemma11` (Case5mL10:934): A1={d1,d2,d3}; disjunction (i) `l13>l23=l12` | (ii) `l13=l23 ∧ (r13=2·r23 ∨ (r13=3·r23 ∧ r13∈{±s}))` on `elevel7` (e=0 ↦ m+1).
- `lemma9_i` (L9:281): distinct ν, both ν<m, e≠0 → λ, all pair-digits {0,6}, apLen≤2. NEEDS hνm.
- `lemma9_i'` (L9b:603): distinct ν, e≠0 → λ, pair-digits {0,1,6}, apLen≤2. NO hνm.
- `lemma9_ii` (L10:1760): equal ν<m, `r(e(b2,b3)) = j·r(e(b1,b3))` j∈{2,3} → λ, `q(λe23')∈{0,5,6}` + `apLen≤j`. For (ii.1) r13=2r23: apply to SWAP (d2,d1,d3) so y'=e13=2·e23-role.
- `lemma7_i` (Cases:131): twoX `r(d')=2r(d)`, `0<ν(e)<m` → λ with `ẽ∉X`, apLen X≤4.
- `lemma7_ii` (Cases:197): twoX, `ν(e)=m`, `r(e)∉X∪(X+1)` → `ẽ∉X`; gives `ẽ∈{r−1,r}` (q(λ7d)=6 branch). Mirror branch (q(λ7d)=0, `qdig7_two_eq_smul`) gives `ẽ∈{r,r+1}` — implemented as `etd_avoid_016` in C64 (private; clone).
- `lemma6` (Compress:387): six (l1,l2,l4) rows incl. **(4,0,2)** (disjunct 3) and **(3,0,3)** (disjunct 6), no side conditions; needs `1∈A₁`, `A₁⊆cycIv 1 (apLen A₁)` normalization.
- `lemma5` (Compress:279): needs `hord : apLen A₂ ≤ apLen A₁ ∧ apLen A₄ ≤ apLen A₁` — GAP for case65 (see below).
- `exists_lambda0_of_shift` (Base:222), `exists_lambda0_avoid` (Base:193), `exists_lambda0_qdig_06` (Top:1141), `good7_of_smul_apLen` (Top:1104, SINGLE-class only), `good7_mul`, `exists_multLow_set_qdig` (Base:509), `exists_top_scalar_set` (Base:546), `residN_top`, `qdig7_eq_runit7_of_top`, `qdig7_add_top_resid` (Top:347), `eMod7_smul` (L9:230), `eMod7_mul` (Base:646), `qdig7_multTop` (Discrete:246), `qdig_eMod_sub` (Base:441), `qdig_eMod_sub_etd7` (Base:453), `qdig_eMod_sub_etd7_same` (Differences:447), `remark8_i`/`remark8_ii`/`remark8_i_int` (Compress:228/242, Base:1056), `exists_multLow_one_set_seven'` (Carry:189), `qdig7_two_eq_smul`/`_add_one` (Carry:95/128), `digit7_multLow_one` (Carry:213), `multLow_not_dvd`, `runit7_multLow`, `residN_multLow7` (Discrete:177), `elevel7_*` (L10:774+), `enu7_le_of_ne` (Base:115), `padicValNat_mul_seven` (Filtering:37), `padicValNat_mul_unit7` (Discrete:67), `min_cover_mem` (C64:660 PRIVATE — clone).

### s-vs-4s pair = twoX SWAPPED
`r(d4)=4s`, `r(di)=s`: `2·runit7 d4 = 8s = s = runit7 di` ⇒ `residueRelOf di d4 = twoY`, `residueRelOf d4 di = twoX`. So `e(d_i,d4) = e(d4,d_i) = 2d4−d_i` and `ẽ(d3,d4) = etd7 m d3 d4 = etd7 m d4 d3 = 2q(d4)−q(d3)` — lemma7 applies with (d,d')=(d4,d_i).

### Case-(i)/(ii.1)-h<m ×2/×3 rescue — DESIGNED
Paper needs `q(λ₁A1−λ₁A1) ⊆ {0,6}` (strong pair condition) then Remark 8(i) k=2,3 → `ℓ(kA1) ≤ k+1`.
**Verified math**: pair-digit {0,6} on same-class B ⇔ for each ordered pair (x,y): `a_x−a_y ∈ {0,±1}` ∧ (`a_x−a_y=1 ⇒ f_x<f_y`; `=−1 ⇒ f_x≥f_y`) where `x%N = a_x·7^m+f_x`. Then `q(kx)=k·a_x+c_x`, `c_x=⌊kf_x/7^m⌋`; anticorrelation (`a_x=a_min+1 ⇒ f_x<f_min`) ⇒ `q(kB) ⊆ cycIv (k·a_min+c₀) (k+1)`, `c₀=⌊k·f_min/7^m⌋`. Uniform proof, any B. → private lemma `apLen_smul_pair06`.
- `lemma9_i'` ({0,1,6}) does NOT support rescue (counterexample: a={0,0,1},f=(0,0,6) → q(2X)={0,0,3} apLen 4).
- e13=0 collapse subcase: apply Λ_{ν23} `q(λe23)=0` (or scalar for ν23=m → `ce23=6·7^m`? NO — pure-top can't get {0,6} both dirs; instead scalar `c=u⁻¹` → e23↦7^m → dist-1 pair, scaled dists 2,3 give apLen 3,4 — SEPARATE shape, verified).
- ν13=m boundary: scalar c (e13↦7^m) then Λ_h (e23↦<7^m): digits ⊆{Q,Q+1} (k=1), {Q',…,Q'+k} (k=2,3) — same ℓ bounds, different proof shape.

### |e45| bands (rescue A4 side) — verified arithmetic
`q(e45')∈{2,3,4} ⇒ |e45'|_N ≥ 2N/7`. `|e|≥5N/14 ⇒ |2e mod N|≤2N/7`; `|e|∈[2N/7,5N/14) ⇒ |3e mod N|≤N/7`. Then `q(2e45')∈{0,1,5,6}` (q=2 excluded: `2e45=2·7^m⇔e45=7^m⇒q(e45)=1∉{2,3,4}`) ⇒ apLen(q(2A4))≤3; `q(3e45')∈{0,6}` (q=1 iff `3e45=7^m⇔e45=5·7^m⇒q=5∉`) ⇒ apLen(q(3A4))≤2.

### Remaining design: case65_tail finisher
After lam₁: X1,X4 digit images. Disjunction (14) `(l1≤3∧l4≤3)∨(l1≤4∧l4≤2)`:
- l1+l4≤5 → `lemma5_20` (private decide core `lemma5_20_core`, Python-verified 0-fail per contract).
- (3,3)/(4,2) → normalize via min_cover_mem-clone + `lemma6` (public) rows 6/3.
Then `exists_lambda0_of_shift` on B=λ₁(A1∪A4), s'=r(λ₁)s, filters X1/∅/X4, `good7_mul`.

### Open issues tracked
- lemma7_ii gap at `e34=5N/7` (spec flag): need `lemma7_ii'` returning `ẽ∈{r−1,r}` (exact-set variant) — clone lemma7_ii's proof, change conclusion.
- (ii.1) h=m (b): after Λ_m norm `e13=2·7^m,e23=7^m`, `q(A1)={Q,Q+1,Q+2}` (shift to {1,2,3} later); `e45=4·7^m` ⇒ `q(d4)=q(d5)+4` EXACT (qdig7_add_top_resid). `case65b_bad_i` finite lemma needed (spec :720).
- (ii.2) h<m: ν13 vs ν45 cases; (ii.2) h=m: scalar normalization `e13↦7^m, e23↦5·7^m` (r23 = 5·r13 since r13=3r23... wait r13=3·r23 ⇒ r23 = 5·r13 mod 7 = 5·1 = 5 — spec confirmed e23=5N/7; EJC txt's "3N/7" is a typo).

## 2026-10-XX — implementation design session (new agent)

### Verified mathematical corrections/extensions to the spec

1. **(ii.2) h<m equal-level — paper gap resolved.** Paper's "choose s=r(e45);
   rename ⇒ r(e45)=r(e13)" only works for `r45∈{±r13}`, which is NOT forced.
   Resolution found: the THREE anchor pairs `e13` (r13), `e32` (=−e23, r=2r13),
   `e21` (=−e12, r=4r13) have residues `r13·{1,2,4}`; all three give valid
   `lemma9_ii j=3` applications on `(d2,d1,d3)`, `(d1,d3,d2)`, `(d3,d2,d1)`
   respectively (ratios verified: `r13=3·5r13`, `2r13=3·3r13`, `4r13=3·6r13`).
   Negatives `r13·{3,5,6}` covered by `d4↔d5` swap. For `r45 = v·r13`:
   `f = e45 − e_{anchor(v)}` (or `e54` after swap) has `ν(f)>h`. Then
   `λ_f` (`Λ_{νf}`, `q(λ_f f)=0` unconditional — works for ALL `a∈{0,5,6}`
   since `a+{0,1,2} ⊆ {0,1,2,5,6}` for `a∈{0,5,6}`) then `λ_b = lemma9_ii`
   on `λ_f`-images (hypotheses level/ratio-invariant). Final:
   `q(e45) ∈ a+0+{0,1} ⊆ {0,1,5,6}` ⇒ diff `q4−q5 ∈ {q,q+1} ⊆ {0,1,2,5,6}`
   ⇒ `ℓ(A4)≤3`; `ℓ(A1)≤3` from lemma9. **[verified: all r45 covered]**

2. **(ii.2) h<m, ν(e45)<h — uniform-shift lemma.** `Λ_{ν45}` applied AFTER
   lemma9's `λ_b` shifts each `A1`-element digit by a constant `ρ1` plus a
   `{0,1}` carry: because `A1` elements agree `mod 7^h` (all pair diffs at
   level `h`), `y mod 7^{ν45+1}` is shared, giving
   `q(λ_a·λ_b·d) = q(λ_b d) + ρ1 + γ_d`, `γ_d∈{0,1}` ⇒ shifted set
   `⊆ cycIv (i+ρ1)(L+1)` ⇒ `ℓ(A1)≤4`. With `q(λ_a e45)=0` ⇒ `ℓ(A4)≤2`
   ⇒ `(≤4,≤2)` disjunct. **[verified by digit decomposition]**

3. **(ii.2) h<m, ν(e45)>h:** `λ_a` (`Λ_{ν45}` or scalar for ν45=m →
   `e45'=7^m`) then `λ_b` (lemma9); `residN_multLow7` preserves
   `λ_a·e45` (ν>h) ⇒ `ℓ(A4)≤2`, `ℓ(A1)≤3` ⇒ `(≤3,≤3)`. **[clean]**

4. **(ii.1) h=m exceptional branch — lemma7_ii' must be EXACT.**
   `e34 = r·7^m` pure-top forces `ẽ = r−1` exactly (6-branch via
   `q(λ·7d)=6 ⇒ q(2λd)=2q(λd)+1` and `e(2λd,λd')=e34` gives
   `q(2λd)=q(λd')+r` exact via `qdig7_add_top_resid`) — NOT merely
   `ẽ∈{r−1,r}`. Mirror: `ẽ = r`. So `r(e34)∈{1,2,3,4}` ⇒ `ẽ=r−1∈{0,1,2,3}`
   avoids `{4,5}`; `r=6` ⇒ mirror `ẽ=6` avoids; `r=5` is the UNIQUE failure
   (paper's `e34=5N/7`), rescued by ×2: `2e34=3·7^m`, mirror gives `ẽ=3`,
   `q(2A1)={Q,Q+2,Q+4}→Λ₀→{1,3,5}`, `q(2A4)={j,j+1}` with `2(j+1)−1=3`
   ⇒ `j=1` ⇒ `{1,2}` ⇒ union `{1,2,3,5}` avoids `{0,6}`.
   **[the spec's "only 5N/7" claim now CONFIRMED — r=4 is fine via exactness]**

5. **Bad-i link (ii.1)(b):** `i = q(d5)−4q(d3)+4`, `ẽ = 2q(d4)−q(d3) = 2i`
   — Λ₀-invariant. `i∈{2,6} ⇔ ẽ∈{4,5}`.

6. **Tail collapse:** `(14)` disjunction discharged by two cover-level
   decide facts — `∀ i1 i4, ∃t, avoids06 (cycIv (i1+t) 3 ∪ cycIv (i4+4t) 3)`
   and `... 4 ∪ ... 2` — replacing lemma5/lemma6 normalization entirely.
   **[python-verified all 49 starts each; subset-level also clean]**

7. **(i) boundary subcase** `ν(e13)=m`: scalar+`Λ_h` gives `e13''=7^m` exact
   (`q1=q3+1,f1=f3`), `q(e23'')=0` (`f2>f3` if `q2=i`, `f2<f3` if `q2=i+1`)
   — all pair-digits `{0,6}` EXCEPT forward `e13` (q=1). Anticorrelation
   `hcorr` holds with `b0=d3` → `×k` rescue applies.

8. **(ii.1) h<m** needs `lemma9_ii`-variant exposing the internal `{0,6}`
   pair-condition (`key` at Case5mL10.lean:2166 is not exported) — plan:
   clone the j=2 branch as `c65_lemma9_ii2` (~415 lines + ~13 private
   helpers from L10: `eMod7_cast_sub`, `qdig_smul_eMod_eq`,
   `etd7_of_pure_block`, `etd7_eq_twoX`, `neg_mem_016`,
   `neg_sub_one_mem_06`, `nat_mod_pow_succ_of_padic`, `wrap_sub_mod_gen`,
   `multLow_low`, `qdig7_pow_self`, `eMod7_zmod_cast`, `eMod7_self`,
   `qdig7_zero`).

9. **Rescue machinery (shared):** `{0,6}`-pair-digits on same-class B +
   `ℓ(B)≤2` (or boundary structure) ⇒ `q(kB) ⊆ cycIv (k·i+c'_min)(k+1)` —
   anticorrelation: `a_x=i+1 ⇒ f_x < f_{min-i}`. Proved via
   `qdig7_smul_eq` exact carry formula.

### Verification notes (this session)

- `(3,3)` and `(4,2)` cover-level shifts: all 49 (i1,i4) solvable ✓.
- `(2,3)` subset-level: clean ✓ (subsumed by (3,3)).
- `(3,4)`, `(4,3)`, `(5,2)` etc.: ALL unsolvable at cover level — the
  (14) bounds are tight ✓.
- Equal-level `r45∉{±r13}` e-residue strategies: 6552 line-cover failures,
  10080 table failures — element-level single `Λ_h` works empirically but
  the anchor-pair f-trick (item 1) is the rigorous route.
- lemma6 (4,0,2) needs NO side-condition — used in (ii.2) h=m.

## Session B — helper block compile-fixed (new agent)

- Inherited 799-line helper block (§0 plumbing + level-structure lemmas).
  Fixed 4 errors: (1) `eq_low_of_e_top` — `hres` rewrite replaced by
  `congrArg (· % 7^m)` + 3×`hmodm` + `Nat.add_mul_mod_self_right`;
  (2) deleted private `eMod7_smul` (name collision — public one at
  `Case5mL9:230` is used); (3) `neg_resid_level` `hdec` — kept
  `mul_comm`-flipped `Nat.div_add_mod` atom, dropped the `hoP` detour,
  `hle`+`omega` closes; (4) `level_of_sub_gt` — `rw [← hmod]` +
  `Nat.mod_mod_of_dvd` for the `7^(h+1) ∣ · % N` step.
- `lake env lean Research07/LRC7/Case5mC65.lean` now exits with only
  deprecation/linter warnings. Helper lemmas available through
  `level_of_sub_gt` (~line 750): `eMod7_sub_block`,
  `eMod7_level_of_runit_ne`, `eMod7_level_gt_of_runit_eq`,
  `level_of_sub_gt`, `enu7_neg/sym`, `runit7_eMod7_neg`,
  `eMod7_cast_add/sub`, `eMod7_add_eq/sub_eq/neg_eq`, `neg_resid_level`,
  `eMod7_zmod7`, `dvd7_eMod7_twoX/same`, `nu_pow7`, `runit7_pow7`,
  `top_resid_multLow`, `e_smul_top`, `eMod7_congr`,
  `nat_mod_pow_succ_of_padic`, `level_of_mod_block`, `sub_mod_block`,
  `wrap_sub_mod_gen`, `qdig_eq_add_of_e_top`, `eq_low_of_e_top`.

## 2026-09-19 §1 digit-arithmetic machinery — DONE, compiles

Appended to `Research07/LRC7/Case5mC65.lean` after `level_of_sub_gt` (~line 761–950):
- `qdig7_sub_resid` (exact borrow formula for wrapped residues, cloned from C63),
- `qdig7_eMod7_same_eq` (same-branch eMod digit = qx−qy−borrow),
- `qdig7_block` (`qdig7 m (A·7^m+r) = ↑(A%7)` for `r<7^m`),
- `qdig7_smul_eq` (`q(kx) = k·q(x) + (k·(x%7^m))/7^m` — exact carry),
- `qdig7_add_016` (`q((u+v)%N) − qu − qv ∈ {0,1}`).

Gotchas hit (2 compile rounds, logged in _dev/failures.md):
- `omega` CANNOT handle `(var+const−var)*7^m` — product of var-atoms atomizes
  opaquely; must supply `Nat.mul_le_mul_right`-expanded bounds as hypotheses and
  rewrite `Nat.sub_mul`/`Nat.add_mul` first so products stay consistent atoms.
- `Nat.div_add_mod a b : b*(a/b) + a%b = a` — factor order is `b*(a/b)`, not
  `(a/b)*b`; calc rewrites must match.
- Cast trap: `(expr : ZMod 7)` elaborates `%`/`/` at ZMod level (pushes casts
  inside); must write `(((expr : ℕ)) : ZMod 7)` with inner `: ℕ` annotation.
- `Nat.mul_mod a b n : a*b%n = a%n*(b%n)%n`; `(k*(x%N))%N = (k*x)%N` needs
  `rw [Nat.mul_mod, Nat.mul_mod k (x%N) _, Nat.mod_mod]`.

## 2026-09-19 §2 cover facts + shared tail — DONE, compiles

- `c65_cover33` / `c65_cover42` (lines ~1067-1078): finite `decide` facts
  matching the Python enumeration (no bad `c`, `k ∈ {0,1,2}` suffices).
- `case65_tail` (~line 1080): full shared tail — normalizes the `A1`-image
  to `cycIv 1 (apLen A1)`, the `A4`-image shifted by `4t`, applies
  `lemma12`-style cover, transports avoidance, builds
  `B = (A1 ∪ A4).image (lam₁ * ·)`, discharges unit/class-filter conditions,
  calls `exists_lambda0_of_shift` with shift `t+k`, closes with `good7_mul`.
  Class-filter errors fixed via `Finset.mem_singleton.mpr`, `False.elim`
  on `s ≠ 0` contradictions, and correct linear combos (`s = 4*s` etc.).

## 2026-09-19 §3 ×2 rescue — DONE, compiles

- `apLen_two_le4` (~1257): two-point sets always `apLen ≤ 4`
  (`min(d+1, −d+1) ≤ 4` by decide).
- `apLen_smul_pair06` (~1272): if `residueRelOf b1 b2 = same` and
  `q(e(b1,b2)) ∈ {0,6}`, then `apLen (image (λb ↦ q(2b)) {b1,b2}) ≤ 3`.
  Proof: `qdig7_smul_eq` carry split `q(2b) = 2q(b) + c`, `c ∈ {0,1}`;
  `q1−q2 ∈ {0,1,6}` from `{0,6}`-digit + borrow ∈ {0,1}; borrow
  anticorrelates `f1 ⋚ f2`, hence `c1 ⋚ c2`; total difference ∈
  `{0,±1,±2}`; `apLen_two_le3` closes.
  Fixes applied: explicit `(m := m)` arg; `set`→`generalize` for carry
  vars (interval_cases cannot split let-bound fvars; omega could not
  see through the casts); `rw [← hc1, ← hc2]` on `Nat.div_le_div_right`;
  `interval_cases c1 <;> interval_cases c2 <;> first|absurd|decide` for
  the `{0,±1}` carry-difference membership.
- File compiles clean (exit 0, warnings only) through line ~1380.

## 2026-XX boundary analysis + §4 machinery design (subagent continuation)

### Completed
- `qdig7_smul2_diff06` extracted from `apLen_smul_pair06` (diff form of ×2
  rescue: same-pair + `q(e)∈{0,6}` → doubled-digit diff `∈{0,±1,±2}`).
- Confirmed key existing APIs: `remark8_i`/`remark8_ii` (Compress.lean),
  `remark8_i_int` (Case5mBase:1056), `absModN_two_mul_le` (Case5mBase:971),
  `absModN_three_mul_le` (Case5mBase:1008), `lemma9_i` (pairs {0,6}),
  `lemma9_i'` (pairs {0,1,6}), `lemma9_ii` (j=2 → {0,6} pairs + apLen≤2;
  j=3 → {0,1,5,6} pairs + apLen≤3), `lemma12`, `exists_top_scalar_set`,
  `exists_multLow_set_qdig`, `residN_top`, `padicValNat_eq_of_mod`,
  `runit7_eq_of_mod`, `eMod7_mul` (needs `runit7 lam = 1`).

### Paper route (bs7.txt ~1050) — corrected understanding
- (i)/(ii.1) h<m: Lemma 9 → ℓ(A₁)≤2; if q(e₄₅)∈{2,3,4} then
  `|e₄₅|≥5N/14` → ×2 rescue (ℓ(2A₁)≤3,ℓ(2A₄)≤3 → (3,3)); else
  `|e₄₅|∈[2N/7,5N/14]` → ×3 (ℓ(3A₁)≤4,ℓ(3A₄)≤2 → (4,2)).
- (ii.2) h<m: ν(e₁₃)=ν(e₄₅) → f=e₄₅−e₁₃ trick; ν(e₁₃)<ν(e₄₅) → fix e₄₅
  first (Λ_ν or top), then Lemma 9 on A₁ (Λ_j preserve e₄₅);
  ν(e₁₃)>ν(e₄₅) → Lemma 9 first then fix e₄₅ (Λ_j at lower level
  preserves A₁'s e-residues? need: Λ_j with j>ν(e) preserves e%N —
  residN_multLow7 needs j<ν(e). So order matters).
- (ii.1) h=m: e₁₃=2N/7,e₂₃=N/7 → ℓ(A₁)=3. (a) ν(e₄₅)<m or
  e₄₅∈{N/7,2N/7} → q(e₄₅)∈{0,1,5,6} → ℓ(A₄)≤3. (b) ν(e₄₅)=m,
  e₄₅∉{N/7,2N/7} → e₄₅=4N/7 normalization + finite Λ₀ argument,
  exceptional e₃₄=5N/7→×2 rescue giving ℓ(2A₁)=5,ℓ(2A₄)=1 + Lemma 7(ii).
- (ii.2) h=m: e₁₃=N/7,e₂₃=3N/7 → ℓ(A₁)≤4; e₄₅ top→N/7 or Λ_ν→{0,6}
  → ℓ(A₄)=2 → Lemma 6(ii) i.e. (4,2).

### HARD LEAF identified (analysis, not yet resolved)
- boundary-(i): ν(e₁₃)=m, ν(e₂₃)=ν(e₁₂)=h<m, bad q(e₄₅′)∈{2,3,4} at level
  ν₄₅′>h. Verified by hand-enumeration: ×2 on a {0,1,6}-pair 2-window
  reaches apLen 4 ({0,2,3} realizable), ×3 reaches 5 — no (4,3)/(5,2)
  cover exists (checked all (l1,l4): only (3,3),(4,2) hold).
  Uniform Λ-shift works only for ν₄₅′<h; ν₄₅′=h gives u-analysis
  (v=ku₂₃∈{0,1} needed, fragile); ν₄₅′>h damages A₁ uncontrollably.
  Plan: implement all other branches first; boundary-(i) may need a
  custom aux clone or ν₄₅′=h quadratic-shift trick.

## 2026-09-19 — Session C (subagent continuation): API audit + clone inventory

- Re-verified helper inventory in Case5mC65.lean (~1863 ln, compiles clean):
  has `eMod7_self`, `qdig7_zero`, `nat_mod_pow_succ_of_padic`,
  `level_of_mod_block`, `sub_mod_block`, `wrap_sub_mod_gen`,
  `eMod7_cast_sub`, `multLow_low'`, `qdig7_multLow_low'`,
  `qdig7_sub_resid`, `qdig7_eMod7_same_eq`, `qdig7_block`,
  `qdig7_smul_eq`, `qdig7_add_016`, `c65_cover33/42`, `case65_tail`,
  `apLen_smul_pair06`, `qdig7_smul2_diff06`, `apLen_two_le*`.
- Still MISSING (must clone from L10/L9/C63): `qdig_smul_eMod_eq`
  (L10:205), `qdig7_pow_self` (L10:1585), `multLow_low` (L10:1593),
  `neg_mem_016`, `neg_sub_one_mem_0156/056/06`, `sub_borrow_mem_0156`
  (L10:1617-1651), `etd7_eq_twoX` (L10:1652), `etd7_of_pure_block`
  (L10:1660), `lemma9_ii_table3` (L10:1696, decide), `remark8_ii'`
  + `remark8_ii_int` (L10:1709-1758), `subset0156_06`.
- lemma9_ii internals (L10:1899-2533): j=2 branch is two-stage
  λ=λ₂·λ₁ (opaque — useless for level-preservation arguments);
  j=3 branch (~2356-2533, ~180 ln) is a SINGLE explicit
  `lam = 1 + k*7^(m−h)` from `exists_multLow_set_qdig` — clonable.
  Plan: `c65_lemma9_ii3` returning `∃ k, lam = 1+k*7^(m−h) ∧ ...`
  so `residN_multLow7` preservation applies to pre-fixed e45.
- Boundary-(i) still the hard leaf: need custom aux (see prev section).

## 2026-09-19 22:02 — Session D (new agent): kickoff

- Inherited: Case5mC65.lean ~95409 bytes, reportedly 0 errors through helpers +
  `case65_tail` (~1083) + ×2-rescue machinery. Report = spec (all prior sessions
  logged above). Two predecessors died mid-task.
- Remaining per orchestrator: boundary-(i) leaf (ν(e13)=m, ν(e23)=ν(e12)=h<m,
  bad q(e45') at ν45'>h — no (4,3)/(5,2) cover exists; plan = custom aux or
  ν45'=h quadratic-shift, or c65_lemma9_ii3 clone exposing `lam=1+k*7^(m−h)`
  for residN_multLow7 preservation), `lemma5_20`, public `case65`.
- First step: verify file tail state + confirm what case-skeleton exists.

## 2026-09-19 22:25 — Session E (new agent): kickoff + state verified

- File `Research07/LRC7/Case5mC65.lean` = 2102 lines, `lake env lean` exit 0
  (warnings only). Last decl = `c65_a4_rescue` (§5, line 2056).
- NO branch lemmas and NO public `case65` yet — remaining work is the whole
  main-theorem layer + the boundary-(i) hard leaf.
- `Case5mC64.lean` is now COMPLETE (1659 ln, `case64` at :960, no sorry) —
  the closest structural model: lemma11 numbering → (i) l13>l23=l12
  [e13=0 collapse / e13≠0 lemma9_i' → ℓ≤2] ; (ii) l13=l23
  [e23=0 collapse / h<m lemma9_ii on swap / h=m pure-top + sub-analysis].
  Its A2-side is FREE via `lemma12` (card≤2 only). C65 A4-side differs:
  `r(d4)=4s` ⇒ `residueRelOf d4 di = twoX`, `e(d4,di)=e(di,d4)=2d4−di`,
  `ẽ=2q4−qi`; needs real ℓ(A4) bounds → `case65_tail`+`c65_hcov` covers.
- Infrastructure present in-file: `case65_tail`(:1083), `c65_finish`(:1905,
  3-way shape disj (≤3∧≤3)∨(≤4∧≤2)∨(sum≤5)), `c65_hcov`(:1881),
  `lemma5_20_core`(:1871), `c65_a4_rescue`(:2056, q(e45)∈{2,3,4} →
  ×2 pair≤3 ∨ ×3 pair≤2), `apLen_smul2_06`(:1417, {0,6}-pairs→×2 ℓ≤3),
  `apLen_smul3_06`(:1468, {0,6}-pairs→×3 ℓ≤4), `c65_pair_len2/3/2'`.
- MISSING private clones needed (from C63/C64/L10): `min_cover_mem`,
  `e_top_twoX`, `lemma7_i_expl`, `etd_top_step`, `apLen_2345`,
  `mem_016_of_not_2345`, `apLen_03u`, `c64_choice`-analog; lemma9_ii j=3
  internals for `c65_lemma9_ii3` (`lam=1+k*7^(m−h)` explicit form).
- Plan: (1) clone shared private gadgets; (2) main `case65` skeleton with
  all branches except boundary-(i) hard leaf; (3) hard leaf via
  `c65_lemma9_ii3` explicit-lam clone or custom aux; (4) compile+report.

## 2026-09-20 01:50 — Session F (current agent): architectural recon & branch roadmap

- Verified build of `Research07/LRC7/Case5mC65.lean` (exit code 0, 0 sorry, warnings only).
- Verified `Case5mTop.lean` signature for `hc65`:
  `∀ {A1 A4 : Finset ℕ}, A1.card = 3 → A4.card = 2 → (∀ d ∈ A1 ∪ A4, 0 < d) → (∀ d ∈ A1 ∪ A4, padicValNat 7 d = 0) → ∀ {s : ZMod 7}, s ∈ ({1, 2, 4} : Finset (ZMod 7)) → (∀ d ∈ A1, runit7 d = s) → (∀ d ∈ A4, runit7 d = 4 * s) → ∃ lam : ℕ, ¬ 7 ∣ lam ∧ good7 m lam (A1 ∪ A4)`
- Identified core finisher: `c65_finish` already takes any of:
  (1) `apLen A1' ≤ 3 ∧ apLen A4' ≤ 3`
  (2) `apLen A1' ≤ 4 ∧ apLen A4' ≤ 2`
  (3) `apLen A1' + apLen A4' ≤ 5`
- Designed `c65_finish_of_pair06`: whenever `A1'` has `apLen ≤ 2` and all pair difference digits in `{0, 6}`, then:
  - either `q(e45') ∉ {2, 3, 4}`, so `apLen A4' ≤ 3` by `c65_pair_len3` → (3, 3) branch of `c65_finish`;
  - or `q(e45') ∈ {2, 3, 4}`, then by `c65_a4_rescue`:
    - either `apLen(2 * A4') ≤ 3`, and by `apLen_smul2_06`, `apLen(2 * A1') ≤ 3` → (3, 3) branch with `2 * lam₁`;
    - or `apLen(3 * A4') ≤ 2`, and by `apLen_smul3_06`, `apLen(3 * A1') ≤ 4` → (4, 2) branch with `3 * lam₁`!
- Direct applications of `c65_finish_of_pair06`:
  - Case (i) `ν13 < m ∧ ν23 < m`: directly solved via `lemma9_i` + `c65_finish_of_pair06`.
  - Case (ii.1) `h < m`: directly solved via `lemma9_ii` (j=2) + `c65_finish_of_pair06`.
- Collapse cases:
  - `e23 = 0`: all elements of `A1` collapse to 1 point, so `apLen(A1) = 1`, while `apLen(A4) ≤ 4` (`apLen_two_le4`), sum = `1 + 4 = 5 ≤ 5` → branch (3) of `c65_finish` with `lam₁ = 1`.
  - `e13 = 0`: `A1` has at most 2 points, so `apLen(A1) ≤ 4` for ANY multiplier. We can always choose `lam₁` so that `apLen(lam₁ * A4) ≤ 2` (via `exists_multLow_set_qdig` or `exists_top_scalar_set`), giving `apLen A1 ≤ 4 ∧ apLen A4 ≤ 2` → branch (2) of `c65_finish`.

### 2026-09-20 02:10 — Exhaustive verification of remaining branches

1. **Boundary-(i) (`ν13 = m, ν23 = h < m`)**:
   - `lemma9_i'` yields `lam₁` with `apLen(lam₁ A1) ≤ 2`.
   - If `q(lam₁ e45) ∉ {2, 3, 4}`, `apLen(lam₁ A4) ≤ 3` by `c65_pair_len3`, giving `(3, 3)` directly via `c65_finish`.
   - If `q(lam₁ e45) ∈ {2, 3, 4}`, tested exhaustively in Python over all 343 configurations: `c65_a4_rescue` gives `apLen(2 * lam₁ A4) ≤ 3` or `apLen(3 * lam₁ A4) ≤ 2`, and simultaneously `apLen(2 * lam₁ A1) ≤ 3` or `apLen(3 * lam₁ A1) ≤ 4` with 0 failures!

2. **Case (ii.2) (`h = m`)**:
   - Top scalar $c \in \{1, 2, 3\}$ applied to $A_1 = \{0, 1, 3\}$ preserves $\text{apLen}(c A_1) \le 4$.
   - Simultaneously, for any $r_{45} \in \{1..6\}$, there exists $c \in \{1, 2, 3\}$ such that $c \cdot r_{45} \in \{1, 6\}$, giving $\text{apLen}(c A_4) \le 2$.
   - Verified 0 failures; discharges via `c65_finish` branch 2 (`4, 2`).

3. **Case (ii.1) (`h = m`)**:
   - For $r_{45} \in \{1, 2, 5, 6\}$, $c = 1$ gives $(3, 3)$ or $(3, 2)$, discharging via `c65_finish`.
   - For $r_{45} \in \{3, 4\}$, relative shift $i \notin \{2, 6\}$ admits $\Lambda_0$ shift $t \in \mathbb{Z}_7$; for $i \in \{2, 6\}$, multiplier $\lambda = 5$ with $t = 0$ avoids $\{0, 6\}$ directly.

4. **Case (ii.2) (`h < m`)**:
   - If $\nu(e_{45}) < h$: $\text{apLen}(A_4) \le 3$ holds with 0 failures.
   - If $\nu(e_{45}) > h$: pre-fixing $e_{45}$ with $q(e_{45}) = 0$ via $\mu \in \Lambda_{\nu_{45}}$ gives $\ell(A_4) \le 2$, and $\lambda \in \Lambda_h$ from `lemma9_ii` ($j=3$) preserves it, giving $\ell(A_1) \le 3 \wedge \ell(A_4) \le 2$ (sum $\le 5$).
   - If $\nu(e_{45}) = h$: tested all $k \in \{0..6\}$ in $\Lambda_h$; 0 failures.### 2026-09-20 03:05 — Session H: Case (i) fully landed & GREEN
- Landed `qdig7_add_pow` and `add_div_carry7`.
- Landed `c65_boundary_lam`: establishes the boundary multiplier construction yielding $q_1 = q_3 + 1$, identical low parts, and $q_2 \in \{q_3, q_3+1\}$ with borrow-monotonicity.
- Landed `c65_case_i`: complete proof of Case (i) `elevel7 m d1 d3 > elevel7 m d2 d3`. Discharges $e_{13} = 0$ via `c65_case_e13_zero`, $\nu_{13} < m$ via `lemma9_i` + `c65_finish_of_pair06`, and $\nu_{13} = m$ via `c65_boundary_lam` + `c65_finish_of_boundary`.
- Full project builds clean (exit code 0, 8940 jobs clean).
### 2026-09-20 03:24 — Session I: c65_case_ii2_top landed & GREEN
- Repaired `eMod7_smul_ne_zero` (removed redundant `hpow` rewrite on already-reduced padic bound).
- Fixed `hap4` set equality via `ext z; simp` on singleton image.
- Eliminated duplicate `c65_case_ii2_top` code chunk.
- `c65_case_ii2_top` (pure-top ratio 3 case, h = m) compiles 100% CLEAN (exit code 0, 8940 jobs clean).
- Next up: implement `c65_case_ii1_top` and `c65_case_ii2_low`, then wire into `case65`.


## Session C — design verification complete (this agent)

### Re-verified / newly verified finite facts (Python, `_dev/check_*.py`)

1. **(ii.1) h=m window+pair Λ₀-rescue, general r45**: after scalar
   `e23'=7^m, e13'=2·7^m` (A1 = `{Q,Q+1,Q+2}`), A4 pair `{p,p+r45}`:
   Λ₀-shift `t` works for ALL (Q,p) iff `r45∈{1,2,5,6}` (0 fails).
   `r45=4`: fails iff `ẽ = 2(p+4)−a ∈ {4,5}` (14 fails). `r45=3`: fails
   iff `2(p+3)−a ∈ {2,6}` — BUT swap `d4↔d5` maps r45=3→4 (e54), so WLOG
   r45=4 and bad iff `ẽ∈{4,5}`.
2. **μ-scaled rescue tables** (window `{a,a+μ,a+2μ}`, pair `{p,p+4μ}`,
   shift A1+t/A4+4t): bad-ẽ sets —
   μ=1: `{4,5}`; μ=2: `{1,4,6}`; μ=3: `{3,5}`; μ=4: `{1,3}`;
   μ=5: `{0,2,5}`; μ=6: `{1,2}`. Each bad value = exactly 7 (a,p) fails.
3. **lemma7 routing for r34∈{4,5}** (6-branch gives `ẽ∈{r−1,r}`, mirror
   `ẽ∈{r,r+1}`):
   - `r34=4`: μ=6 → r''=3 → mirror `ẽ∈{3,4}⊆good_6={0,3,4,5,6}` ✓
     (μ=2..5 all fail both branches).
   - `r34=5`: μ=3 → r''=1 → 6-branch `ẽ∈{0,1}⊆good_3={0,1,2,4,6}` ✓.
   - `r34=6`: μ=1 mirror `ẽ∈{6,0}⊆good_1` ✓ (no μ needed).
   - `r34∈{1,2,3}`: μ=1 lemma7_ii `ẽ∈{r−1,r}⊆{0,1,2,3}` ✓.
   - `ν34<m` (incl. 0): lemma7_i clone X={4,5} ✓.
4. **ii.2 h<m equal-level anchor trick** (from Session-A report item 1):
   anchors e13/e32/e21 have residues `r13·{1,2,4}`; permuted lemma9_ii
   calls `(d2,d1,d3)/(d1,d3,d2)/(d3,d2,d1)` verify `r(y)=3r(x)`:
   `r13=3·(5r13)`, `2r13=3·(3r13)`, `4r13=3·(6r13)` ✓. Orientation:
   `r45=v·r13`, `v∈{3,5,6}` → use e54 (`−v∈{4,2,1}`).
   `f=E45−anchor`: `ν(f)>h` or `f=0`.
5. **Pairwise-diff → apLen**: 3-set with all signed diffs in `{0,1,2,5,6}`
   ⇒ `apLen≤3` (0 fails); in `{0,1,5,6}` ⇒ `≤2`.
6. **Key simplification**: `Λ_j` (j<m) preserves pure-top e's
   (`residN_multLow7`) → after lemma7/lemma9 multipliers the exact
   q-offsets (`qdig_eq_add_of_e_top`) are preserved — NO carry tracking
   needed in ii1_top. For ii2_low ν45<h: λ_a at level ν45<h preserves all
   level-h A1 pair e's → pair digits `{0,1,5,6}` persist → apLen≤3 via
   pairwise-diff lemma (no translate-carry needed!).

### Helpers to add (all idioms confirmed in file/library)

- `c65_lambda0_finish` — `exists_lambda0_of_shift` wrapper (copy the
  filter bookkeeping from `case65_tail`).
- `c65_lemma7_i'` — lemma7_i clone without `0<ν` (ν=0 ⇒ Λ₀).
- `c65_lemma7_ii'` — mirror (`q(λ·7d)=0`, `qdig7_two_eq_smul`,
  `r∉X∪(X−1)`).
- `c65_ii1_dec{1,3,6}` — three `decide` rescue tables.
- `c65_apLen3_of_diffs` — pairwise `{0,1,2,5,6}` ⇒ `apLen≤3` (decide).
- `c65_multLow_shift` — `q(λ_a z)−q(z)−q(k·7^{m−j}·w)∈{0,1}` for shared
  `z%7^{j+1}=w` (via `qdig7_add_016`) — actually NOT needed given #6.
- level-preservation glue for `λ_f`/`λ_b` on e-residues.

## 2026-09-18 — c65_case_ii1_top done; ii2_low plan

- `c65_case_ii1_top` (Case5mC65.lean ~L4070-4370) compiles: Λ_m-scalar
  normalizes e23→7^m, e13→2·7^m (ℓ(A1)≤3); e45'=0 → singleton;
  ν(e45')<m → Λ_ν sets q=0 (ℓ(A4)≤2); ν=m → orient r∈{1,2,4}, r∈{1,2}
  gives ℓ≤3, r=4 → c65_ii1b_post (X={4,5}) or c65_ii1b (Lemma 7).
- Compile fixes: `add_sub_cancel_left` for (a+b)−a; `ZMod.val` not defeq
  in `exact`-application → explicit `(k:ZMod7).val = k := by decide`
  rewrites; pair image must be rewritten to `{x,y}.image` before
  `c65_pair_len2'`; `tauto` timed out at whnf → `Finset.pair_comm`;
  `enu7_neg` needed explicit `have` type for implicit m.
- `c65_case_ii2_low` design (h = ν13 = ν23 < m, ratio 3):
  (a) e45=0: lemma9_ii → singleton A4. (b) ν45<h: lemma9_ii3 then
  λ2∈Λ_ν45 zeroes q(e45'); A1-pairs preserved since ν(e')=h>ν45.
  (c) ν45>h: λ2 (Λ_ν45 q=0 / top-scalar 7^m) then lemma9_ii3 on scaled
  triple; λ1∈Λ_h preserves e45' verbatim (residN_multLow7).
  (d) ν45=h: orient (u,v) s.t. r(e_uv)=w·r13, w∈{1,2,4}; anchor
  E = e13 (w=1, perm (d2,d1,d3)) / e32 (w=2, perm (d1,d3,d2)) /
  e21 (w=4, perm (d3,d2,d1)); f := (e45u − E)%N has ν(f)>h or f=0;
  λ2 fixes f (q=0 or 7^m), lemma9_ii3 gives q(E'')∈{0,5,6}, then
  q(e45''')=q((E''+f'')%N) ∈ {0,1,5,6} via qdig7_add_016/qdig7_add_pow.
- NEEDS: `lemma9_ii3` in L10 exposing `lam = 1+k·7^{m−h}` (clone of the
  j=3 branch, ~200 lines) since lemma9_ii's ∃ hides the Λ_h form and
  residN_multLow7 needs it; plus C65 clones of remark8_ii'/
  remark8_ii_int ({0,±1,±2}-diffs → apLen≤3) and transport helpers
  c65_eMod_smul_level.

## 2026-09-20 — Session J (this agent): c65_l9ii3 landed GREEN

- Appended §7 block to Case5mC65.lean (now ~4817 ln): clones
  `c65_qdig_smul_eMod_eq`, `eMod7_self'`, `c65_multLow_low`,
  `c65_neg_mem_016`, `c65_neg_sub_one_mem_0156`, `c65_neg_sub_one_mem_056`,
  `c65_sub_borrow_mem_0156`, `c65_l9ii3_table` (decide),
  `c65_remark8_ii'_dec`/`c65_remark8_ii'`/`c65_remark8_ii_int`,
  and **`c65_l9ii3`** (port of `c63_l9ii3`: returns `lam = 1+k*7^(m−h)`
  explicitly + `q(e(b2,b3)') ∈ {0,5,6}` + pair digits `{0,1,5,6}` +
  `apLen ≤ 3`). `remark8_ii'`/`remark8_ii_int` were private in both L10
  and C63 — cloned, as the task allowed.
- `lake env lean` exit 0, zero errors, zero sorry.
- Next: `c65_case_ii2_low` (4 sub-cases) then `case65` assembly.

## 2026-09-21 — c65_case_ii2_low landed; `case65` GREEN (all gates pass)

- **Root cause of the phantom 3M-heartbeat timeouts**: `enu7_neg hrel.. hrel..`
  has implicit `m` that appears only in the RESULT type — unsolved `?m`
  made every later `whnf` expensive and produced cascading
  "don't know how to synthesize placeholder" errors that were *masked*
  by timeout reports. Fix: `enu7_neg (m := m) ...` (L4909-4911 region).
- **Structure** (mirrors C63's decomposition):
  - `c65_ii2_low_fix`/`_tail` helpers + `c65_ii2_low_{zero,lt,eq,gt}`
    each get `set_option synthInstance.maxSize 16384 + maxRecDepth
    524288 + maxHeartbeats 3000000` (per-command budget).
  - `c65_case_ii2_low` = preamble (level/unit facts for all six pairs,
    `eMod7_level_of_runit_ne` for e12, `enu7_neg` for negated pairs)
    + `by_cases e45=0` + `lt_trichotomy` dispatch.
  - (a) `e45=0`: `lemma9_ii` (j=3) on `(d2,d1,d3)`; A4 collapses to
    singleton digit set → `c65_finish`.
  - (b) `ν45<h`: `lemma9_ii` on `(d2,d1,d3)` then `λ2 ∈ Λ_{ν45}` zeroes
    `q(e45')`; `hfix` lemma: all A1-pair residues preserved verbatim
    (level h > ν45, `residN_multLow7`); A1 apLen ≤3 via
    `c65_remark8_ii'`/`_int` on the lam2-image; A4 ≤2 via
    `c65_pair_len2'`.
  - (d) `ν45=h`: generic `hmain`/`hcore` — orient `(u,v)` so
    `r(e_{uv}) = w·r13`, w∈{1,2,4}; anchors e13/e32/e21 with
    permutations (d2,d1,d3)/(d1,d3,d2)/(d3,d2,d1); `f = (e_uv − E)%N`
    at level >h or 0 fixed by `λ2` first (q=0 via `Λ_{νf}` or top
    `7^m`); `c65_l9ii3` gives `q(E'') ∈ {0,5,6}`;
    `q(e_{uv}'') ∈ {0,1,5,6}` via `qdig7_add_016`/`qdig7_add_pow`;
    finish `c65_pair_len3` + `c65_finish` (Or.inl shape).
  - (c) `ν45>h`: `λ2` puts `q(e45') ∈ {0,6}` (`Λ_{ν45}` when ν<m,
    top scalar t=6 when ν=m); `c65_l9ii3` on `(λ2·d2, λ2·d1, λ2·d3)`
    (explicit `Λ_h` form needed for `residN_multLow7` preserving
    `e45'`); finish `c65_pair_len2` + `c65_finish`.
- **ZMod-7 `linear_combination` gotcha**: `ring`/`linear_combination`
  cannot reduce the literal `(7 : ZMod 7)` to `0`, so residuals like
  `-(r·7) = 0` fail. Fix: add `h7 : (7 : ZMod 7) = 0 := by decide` and
  include `±coeff * h7` terms in the combination (verified in
  `_dev/ztest2.lean`).
- **Verification**:
  `lake env lean Research07/LRC7/Case5mC65.lean` → 0 errors;
  `lake build` → 8940 jobs clean;
  `#print axioms case65` → `[propext, Classical.choice, Quot.sound]`;
  zero `sorry`/`admit`/`native_decide`/`unsafe`.
- File now 5925 lines. `case65` at L5863; branch map:
  `c65_ii2_low_zero` L4824, `c65_ii2_low_lt_fix` L4885,
  `c65_ii2_low_lt_tail` L4946, `c65_ii2_low_lt` L5062,
  `c65_ii2_low_eq` L5141, `c65_ii2_low_gt` L5541,
  `c65_case_ii2_low` L5741, `case65` L5863.

### Final summary for orchestrator
`theorem case65` (exact required signature) is proved and fully
verified. §6.5 formalization of Case5mC65.lean is complete:
lemma11 dispatch → c65_case_i / c65_case_collision / c65_case_e13_zero
/ c65_case_ii1_{low,top} / c65_case_ii2_{low,top}; the ii2-low corner
splits on ν(e45) ∈ {0, <h, =h, >h} as designed.
