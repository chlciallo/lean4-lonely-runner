
### ORCHESTRATOR NOTE — lemma10 hypothesis form corrected

The `h10` hypothesis in your contract uses the `residueRelOf = same`
premise — that statement form was found FALSE earlier (countermodel
{1,50,99,3}@m=1, mixed same-pair classes). The real `lemma10` (landing
in `Case5mL10.lean`) uses `(s : ZMod 7) (hsame : ∀ d ∈ A1, runit7 d = s)`
like `lemma11`. In your case context `hcls`/`hcls1` gives `runit7 d = s`
directly — satisfies both forms. PREFERRED: if `lemma10` exists in
`Case5mL10.lean` by the time you write the proof, drop `h10` and use it
directly. Otherwise keep the `h10` parameter but isolate its application
to ONE `obtain` site so the orchestrator can shim premise/level-measure
drift (real lemma10 may emit `elevel7`-based conclusions — under
`eMod7 ≠ 0`, `elevel7 m x y = padicValNat 7 (eMod7 m x y)`).

### ORCHESTRATOR NOTE 2 — h9ii conclusion shape

In the `h9ii` hypothesis from your contract, the last conjunct should be
`apLen (...) ≤ j` (j = the index you pass, 2 or 3) — NOT unconditionally
`≤ 3`. For `j = 2` this gives `apLen ≤ 2`, which is what the
`exists_lambda0_qdig_06` shift-into-{0,6} step needs. If your written
signature says `≤ 3`, change it to `≤ j` (with `j` the bound variable
from the `∀ {j : ℕ}, j = 2 ∨ j = 3 →` quantifier — move the conjuncts
inside that binder's scope accordingly). The extra pairwise
`{0,1,5,6}`-clause may stay (it's derivable from the apLen bound via
`qdig_eMod_sub_etd7_same`, so instantiable either way).

## 2026-XX resume — exploration log (new agent)

- Report file had ONLY the two orchestrator notes (26 lines). Spec read in full
  (`lrc7-sec6-spec.md` §4.3 lines 463-505, §5.2 table spec lines 731-749).
- `Case5mC62.lean` = helpers only, NO `theorem case62` (sibling still WIP).
- `Case5mC64.lean` line 1077-1079: `case64` theorem itself ends in 3 `sorry` —
  WIP, not green. Do NOT rely on it as a pattern for completeness; its
  *infrastructure* (lemma7_i_expl, etd_avoid_016, etd_top_step, case64_tail/
  finish3/finish4, low-level clones) is however a perfect template for C63.
- Case64 helpers worth cloning into C63: `eMod7_lt`, `rel_same`, `eMod7_same_eq`,
  `eq_resid_of_eMod7_eq_zero`, `eMod7_self`, `qdig7_zero`, `runit7_zero`,
  `mul_pow_add_div`, `eMod7_zmod_cast`, `qdig_eq_add_of_e_top`, `eMod7_zmod7`,
  `dvd7_eMod7_twoX`, `dvd7_eMod7_same`, `nu_pow7`, `runit7_pow7`,
  `top_resid_multLow`, `e_smul_top`, `eMod7_twoX_add`, `e_top_twoX`,
  `lemma7_i_expl`, `etd_avoid_016`, `etd_top_step`, `apLen_le7'`,
  `min_cover_mem`, `mem_016_of_not_2345`, `apLen_2345` — all `private` in
  C64 so must be cloned (renamed c63_) or re-proved in my file.

## 2026-XX continuation — architecture locked (agent 3)

### Verified API set
- `lemma5` (Compress.lean:279): needs `hord : apLen A₂ ≤ apLen A₁ ∧ apLen A₄ ≤ apLen A₁`;
  returns `∃t avoids06(...)` OR `(3,1,1) ∧ ∀d∈A₂,d'∈A₄: 2d−d' ∈ {2,4}`.
- `lemma11` (Case5mL10:934): labels A1={d1,d2,d3}, disjunction:
  (i) `L13 > L23 = L12` ; (ii) `L13 = L23` AND (ratio-2 `r13 = 2r23` OR
  ratio-3 `r13 = 3r23 ∧ (r13 = s ∨ r13 = -s)`).
- `lemma9_i'` (Case5mL9b:603): unequal levels → `apLen ≤ 2` + pair digits `{0,1,6}`.
- `lemma9_ii` (Case5mL10:1764): `j=2∨j=3`, equal levels `< m` → apLen ≤ j,
  ALL pair e-digits ∈ {0,1,5,6}, plus `j=2 →` pair digits ∈ {0,6}.
  For `j=3` also `q(λe(b2,b3)) ∈ {0,5,6}`. **Problem**: does NOT expose the
  multiplier — must clone j=3 branch as `c63_l9ii3` returning `∃k<7, lam = 1+k·7^{m−h}`.
- `exists_lambda0_of_shift` (Case5mBase:216): `t` → `1+K·7^m ∈ Λ₀` realizer.
- `exists_multLow_set_qdig` (Case5mBase:~530): `Λ_j` sets `q(λx)=c` for ν(x)=j<m.
- `exists_top_scalar_set` (Case5mBase:~560): ν(x)=m → `c<7` scalar sets `q(cx)=t`, `c·x ≡ t·7^m`.
- `residN_multLow7`, `eMod7_mul`, `etd7_multLow_same`, `qdig7_multLow`,
  `qdig_eMod_sub` (same pair: `q(e)−ẽ ∈ {0,6}`), `qdig_eMod_sub_etd7` (general `{0,±1}`),
  `apLen_image_add`, `remark8_i_int`, `remark8_ii_int`, `enu7_le_of_ne`,
  `padicValNat_mul_seven` (Filtering.lean:37), `elevel7` (=m+1 iff e=0).
- Carry: `digit7_multLow_one` (Case5mBase), `qdig7_two_eq_smul`/`_add_one`,
  `exists_multLow_one_set_seven'` (Λ₁ sets `q(λ·7d)=c`), `residN_top`.
- Finite: `bad63`, `case63_bad_pairs`, `case63_eps_avoid`, `case63_table`,
  `case63_table_rescue` — all in Case5mBase.

### Corrected sign conventions (vs paper text)
- e_ij := eMod7 m d_i d_j (SAME pair) = d_i − d_j residues.
  lemma11's `r13 = j·r23` with e13 = d1−d3 (paper had d3−d1). Ratio-3 → j=3.
- e34 := eMod7(d3,d4) twoX = 2d3−d4; e45 := eMod7(d4,d5) twoX = 2d4−d5.
  ẽ34 = 2q3−q4, ẽ45 = 2q4−q5 (twoX ẽ = 2qx−qy).
- twoX digit-diff box: `ẽ ∈ q(e)+{0,±1}` (from qdig_eMod_sub_etd7: q(e)−ẽ∈{0,1,6}).
- Bad pair = (ẽ34, ẽ45) = (2−i, 2i−j) — VERIFIED: (2,4),(2,5),(3,2),(3,3),
  (4,3),(4,4),(5,1),(5,2) — case63_bad_pairs already proves this exact set.

### Boundary h=m ε-mechanism (fully verified numerically)
For twoX pair with pure-top e = v·7^m: `ẽ = v − δ`, δ = carry
`⌊2·low(x) − low(y)⌋/7^m ∈ {0,1}` (NOT v+1 — corrected direction).
Λ₁ multiplier λ = 1+k·7^{m−1}: low(λx) mod 7^m = l_x + A_x·7^{m−1} where
A_x = digit7(m−1,λx) = (digit7(m−1,x) + k·u_x) mod 7 = q(λ·7x).
With A3 := q(λ·7d3) settable to any value (exists_multLow_one_set_seven'):
δ34 = [2A3+c4 ≥ 7], A4 = (2A3+c4) mod 7, δ45 = [2A4+c5 ≥ 7], c_i∈{0,1}.
Setting A3 = 4ε1+2ε2 yields δ34 = ε1, δ45 = ε2 UNIFORMLY (all 4 cells checked).
→ (ẽ34,ẽ45) = (v34−ε1, v45−ε2), and case63_eps_avoid picks ε1,ε2 ∈{0,1}
with that pair ∉ bad63.

### Full branch plan
- (i): lemma9_i' → apLen ≤2 → lemma5 (exception needs apLen=3 → impossible).
- (ii.1) h<m: lemma9_ii j=2 → apLen ≤2 → lemma5.
- (ii.1) h=m: scalar normalizes e13→2·7^m, e23→7^m (r13=2r23 forces both);
  digit set {a,a+1,a+2} apLen=3; singletons; lemma5 exception needs
  ẽ45∉{2,4}: ν(e45)<m → lemma7_i_expl X={2,4}; ν(e45)=m → Λ₁ pair-carry
  (ẽ = v45 or v45−1; pick the one ∉{2,4}).
- (ii.2) h<m: c63_l9ii3 (explicit Λ_h). (a) ν(e45)≠h: normalize q(e45)=6
  (Λ_ν45 or scalar; ordering per paper), Λ_h preserves q(e45) iff ν45>h;
  if ν45<h apply Λ_ν45 AFTER (preserves e_ij mod N via residN_multLow7).
  → ẽ45 ∈ {5,6,0} avoids{2,4} → lemma5.
  (b) ν(e45)=h: f = e13−e45 (r45=±r13 → ν>h) or g = e13+e45 (−r13 case);
  normalize q(f)=0 or pure-top N/7 → ẽ-param := q13−q45 (+) or
  q13+q45+1 (−) ∈{0,1} — invariant under Λ_h (r13∓r45=0);
  ũ = 3q13+5q23 invariant (3r13+5r23=0 for ratio-3);
  δ := q13−q23−q12 ∈{0,1} borrow; case63_table(e,ũ,δ) → q45 ∈{0,6} in
  the ≤3 case → set q(λe45)=q45 via Λ_h → apLen ≤2 or (≤3 ∧ ẽ45∉{2,4});
  (e,ũ)=(0,3) → rescue via doubled elements 2·(λA): classes {2s,4s,s}
  = {s',2s',4s'} with s'=2s; q(2e45)∈{6,0} → ẽ(2d4,2d5)∈{0,1,5,6}.
- (ii.2) h=m: normalize e13→3·7^m, e23→7^m (scalar) → q(A1)={a,a+1,a+3}
  (EXACT diffs, pure top). Cell lemma `c63_cell` (decide): ∃t avoids06 ∨
  (2a−i,2i−j)∈bad63. Bad cell → ẽ34 ∈{2..5} → ν(e34)<m: lemma7_i_expl
  X={2,3,4,5}; ν(e34)=m∧ν(e45)<m: lemma7_i_expl on (d4,d5) with X
  depending on v34∈{2..6} (X={4,5}/{2,3,4,5}/{2,3,4}/{1,2,3,4}/{1,2},
  all apLen≤4); ν(e34)=ν(e45)=m: ε-mechanism above.

## 2026-09-19 continuation — agent 4 (implementation start)

### State found
- File compiled all helpers after ONE fix: line 930 `multLow_shift_qdig`
  needed `le_of_eq hx.symm` (was `le_of_eq hx`, direction mismatch).
  `lake build Research07.LRC7.Case5mC63` → 8940 jobs GREEN (helpers only;
  no `case63` theorem yet, no `sorry`).
- `lemma9_ii` (Case5mL10:1764) landed with 5-conjunct form, `apLen ≤ j`.
  j=3 branch internally builds `lam = 1 + k·7^{m−hν}` via
  `exists_multLow_set_qdig hνm hyν hy0 t` with `t` from `lemma9_ii_table3`
  (line 2352). For `c63_l9ii3` the j=3 block (lines 2348–2530) must be
  cloned with `q(λy)` target EXPOSED (needed to set `q(λe45)` in (ii.2.b)).
- Finite tables `bad63`, `case63_bad_pairs`, `case63_eps_avoid`,
  `case63_table`, `case63_table_rescue` all present + green in
  Case5mBase.lean:1246–1400.
- `exists_lambda0_of_shift` (Case5mBase:222): needs `s ≠ 0` only (NOT
  `s ∈ {1,2,4}`) — works after ANY unit scalar normalization.
- **`lemma5` needs `s ∈ {1,2,4}`** — hypothesis `_hs` is UNUSED in proof
  (marker only). Plan: clone as `c63_lemma5` w/o class hyp (needed since
  scalar normalization by `c ∉ {1,2,4}` moves classes to `cs ∉ {1,2,4}`).

### Design notes (verified against spec)
- Scalar normalization constraint analysis: after `·c` scaling, classes
  are `{cs,2cs,4cs}`; `exists_lambda0_of_shift` fine (cs≠0). lemma5
  `_hs` needs `cs∈{1,2,4}` ⇔ `c∈{1,2,4}` — can't guarantee since
  `c = v23⁻¹` arbitrary → clone lemma5.
- (ii.1) h=m: scale `c = v23⁻¹` → `(e13,e23) = (2,1)·7^m` →
  `q(A1) = {a,a+1,a+2}` apLen 3 (qdig_eq_add_of_e_top).
- (ii.2) h=m: scale `c = v23⁻¹` → `(3,1)·7^m` → `q(A1) = {a,a+1,a+3}`
  apLen 4 → then Λ₀ anchors `q(A1)={1,2,4}`, `q(d3)=1` for bad-pairs table.

## 2026-XX — Paper re-read (bs7-ejc.txt §6.3 verbatim) + final architecture

Read the actual paper §6.3 (lines 625-770 of `_external/bs7-ejc.txt`). Confirmed branch plan and found critical simplifications:

### Key discovery: pure-top differences force ZERO borrows
For a same-pair difference `e(x,y) = v·7^m` (pure top, the h=m situation), the wrapped relation
`res(x)+N−res(y) ≡ v·7^m` forces `res(x) = res(y)+v·7^m` EXACTLY (both <N, no wrap) →
`q(x) = q(y)+v` and `lo(x) = lo(y)`. So the digit-set borrow-freedom vanishes:
- (ii.1) h=m: e13=2·7^m, e23=7^m ⇒ q(A1) = {z,z+1,z+2} EXACTLY (apLen=3 always).
- (ii.2) h=m: e13=3·7^m, e23=7^m ⇒ q(A1) = {z,z+1,z+3} EXACTLY (apLen=4 always).
These set-forms are preserved under ANY further multiplier that keeps e13,e23 pure-top
(scalars, Λ_j j<m, Λ₀ all preserve pure-top residues) — so the finish re-analyzes the
final cell {z',z'+1,z'+3} freely.

### Confirmed §6.3 structure (paper verbatim)
- (i) and (ii.1) h<m: Lemma 9 → ℓ(A1)≤2 → Lemma 5 (sum=4, no exception).
- (ii.2) h<m:
  - (a) ν45≠h: ν45>h → Lemma 2 on e45 (q∈{0,6}) then Lemma 9 (ℓ≤3); ν45<h → Lemma 9
    first then Lemma 2 on scaled e45. Pair-diffs preserved by residN; apLen≤3 re-derived
    via remark8_ii' on final set. Lemma 5 (exception excluded by ẽ45∈{0,1,5,6}).
  - (b) ν45=h, r45=±r13: the ũ-table (= case63_table). −case: apply table to E=−e45,
    q(λe45) = −V−1 (since q(−x) = −q(x)−1 for lo(x)≠0). (0,3)-cell: V=3 → doubled
    pair-digits ∈{0,6} → doubled set ⊆{0,1,6}-translate → apLen≤3 → Lemma 5 with
    exception excluded by ẽ(2d4,2d5) ∈{0,6}+{0,±1} ⊆{0,1,5,6} ∌{2,4}.
- (ii.1) h=m: scalar→{z,z+1,z+2}; Lemma 7 for the pair (ν45<m: X={2,4}; ν45=m:
  Λ₁ single-pair carry — both δ'∈{0,1} reachable → pick avoiding {2,4}).
- (ii.2) h=m: scalar→{z,z+1,z+3}, anchor z=1. Cell analysis: fails ⇔ bad pairs.
  - ν34<m: Lemma7(i) X={2,3,4,5} on (d3,d4) → ẽ34∉{2..5} → non-bad.
  - ν34=m, ν45<m: Lemma7(i) on (d4,d5), X={2,3,4,5} if ẽ34∈{2,3}, X={1,2,3,4} if
    ẽ34∈{4,5} (ẽ34∈{0,1,6} trivial).
  - ν34=ν45=m: ε-mechanism — q(7d3)=4ε1+2ε2 realizes (ẽ34',ẽ45')=(v34−ε1,v45−ε2);
    case63_eps_avoid picks non-bad pair.

### Verified finite facts (Python)
- c63_cell: ∀z,i,j (∃t avoids06{z+t,z+1+t,z+3+t,i+2t,j+4t}) ∨ (2z−i,2i−j)∈bad63 — all
  56 failures are bad-pairs. VERIFIED all z.
- case63_table matches paper's ũ-table values (q13=V+ê, q23=3(ũ−3(V+ê))).
- ε-chain formula VERIFIED (112-cell): δ34' = δ34+⌊(c4+2w)/7⌋−2⌊(c3+w)/7⌋,
  δ45' = δ45+⌊(c5+4w)/7⌋−2⌊(c4+2w)/7⌋ with c4=(2c3+γ4)%7, δ34=⌊(2c3+γ4)/7⌋,
  c5=(2c4+γ5)%7, δ45=⌊(2c4+γ5)/7⌋, w=(4ε1+2ε2−c3)%7 gives δ34'=ε1, δ45'=ε2.

### Needed new theorems
- c63_l9ii3: explicit-multiplier clone of lemma9_ii j=3 (lam = 1+k·7^{m−h}) — all
  helpers already cloned in file (lemma9_ii_table3, qdig_smul_eMod_eq, etc.).
- c63_pure_top_same/twoX, c63_lo1, c63_eps_table, c63_eps_chain, c63_single_carry,
  c63_cell, c63_finish.

## 2026-09-19 (cont'd) — §2a pure-top block COMPLETE, build green (8940 jobs)

### Repaired heredoc truncation + completed pure_top_twoX
- `pure_top_res_eq` (line ~1038): same-branch `x%N = (y%N + v·7^m)%N` ✓
- `pure_top_low_eq` (line ~1072): same-branch `x%7^m = y%7^m` ✓ (fixed zero_add→add_zero)
- `pure_top_twoX` (line ~1090): for `r(y)=2r(x)`, `e=v·7^m` gives
  `∃ δ<2, 2·lo(x) = lo(y) + δ·7^m ∧ etd7 = v − δ` ✓
  Key fixes: (a) carry part via `W+res_y = 2res_x+N` reduced mod `7^m` (Nat.add_mod,
  mod_mod_of_dvd) — avoided messy decomposition; (b) `δ` bound via `obtain ∃` so
  it's a clean omega atom (div-atom `2fx/7^m` inside products breaks omega's
  atomization: `7^m*d` vs `d*7^m` are distinct atoms); (c) `hexp` must write
  `2*(qx*7^m)` not `2*qx*7^m` — `(2*qx)*7^m ≠ 2*(qx*7^m)` as omega atoms;
  (d) etd part via `↑(2qx+7+δ−qy) = v` then `natCast_sub_add`+cast rewrites+`linear_combination`.
- W' = 2res_x+N−res_y = (2qx+7+δ−qy)·7^m decomposition via hWq+Nat.sub_mul.

### Status
File compiles (8940 jobs). Remaining todos: c63_lo1 (Λ₁ lo-decomp), eps_chain,
single_carry+c63_l9ii3, finish, then all 5 lemma11 branches + public theorem.

## 2026-09-19 20:00 — agent 5 (c1ce833e successor) session start

- Read full report (212 lines). File = 1453 lines, uncommitted (`??` in git status).
- Plan: verify compile → inventory done helpers → eps_chain → single_carry +
  c63_l9ii3 → finish → 5 lemma11 branches → public case63.
- Report is spec; will update every ~10 tool calls.

## 2026-09-19 20:20 — agent 6 (session start)

- Read full report (219 lines). **CRITICAL FINDING: file does NOT compile.**
  `lake env lean` shows 18 errors, all inside agent-5's `c63_lo1` (line ~1205)
  and `c63_eps_pair` (1256–1453). The "compiles clean" status in the task
  contract was stale (predates agent 5's edits). Git: file untracked, no
  earlier version to revert to.
- Error inventory (root causes): (a) `rw` pattern misses —
  `(k*(x%7))%7` not a subterm; `pow_succ'` vs `pow_succ` name swap
  (this Mathlib: `pow_succ : a^(n+1) = a^n * a`); `add_mul_mod_self_left`
  vs `_right` (modulus is right factor here); `Nat.add_mod` chains hit the
  outer sum first leaving `(A+B)%P` unexpanded for `mod_eq_zero_of_dvd`.
  (b) omega atom trap AGAIN: `u*7^(m+1)` vs `7^(m+1)*u` distinct atoms.
  (c) `Nat.ModEq.mul_left` apply on `X≡X` reflexive goal.
- Plan: fix `c63_lo1`+`c63_eps_pair` in place (statements are correct —
  downstream design depends on them), then eps_chain, single_carry,
  c63_l9ii3, finish, 5 lemma11 branches, public case63.

## 2026-09-19 session cont: c63_lo1 + c63_eps_pair GREEN

- `lake env lean Research07/LRC7/Case5mC63.lean` → **0 errors** (file now 1414L).
- Rewrote `c63_lo1` (~1195) entirely on `Nat.ModEq` congruences + `mod_mul_div`/`Nat.div_add_mod` strip; old `Nat.add_mul_mod_self_left`/`omega`-on-product-atoms approach abandoned.
- `c63_eps_pair` (~1268): rebuilt via `pure_top_twoX` → mod-P reduction for (i), `linear_combination` P-division for `β+2c3=c4+7δ`, ModEq chain for (ii), transformed-pair `pure_top_twoX` + `c63_lo1`×2 + carry identity for (iii).
- **Statement bug fixed**: `2 * A % 7` parses as `(2*A)%7` (same-prec left-assoc) but the true carry needs `2*(A%7)`; inserted explicit parens in hpart2-RHS and δ'-numerator. With the old parse the δ' was off by 1 when A3%7 ≥ 4.
- Pitfalls hit: `mul_left'` (not `mul_right`) scales modulus to `c*n`; leading `.name` on a fresh line parses as a lambda; `Nat.le_of_lt_succ` for `%7 < 7 → ≤ 6`; `dvd_mul_of_dvd_right` for `c*b` order; `rw [Nat.ModEq, Nat.mod_mod]` to unfold ModEq cleanly.
- Remaining: `eps_chain`, `single_carry`, `c63_l9ii3`, `c63_finish`/`c63_lemma5`, five `lemma11` branches, public `case63`. File ends at c63_eps_pair; all referenced tables (`case63_table`, `case63_eps_avoid`, `case63_bad_pairs`, `case63_table_rescue`) live in `Case5mBase.lean`.
## 2026-09-19 late — agent 7 progress

- eps_chain (L1675): two c63_eps_pair applications, compiles.
- single_carry (L1693): exists k<7 realizing any prescribed m-1 digit w<7 of Λ₁·x for 7-unit x; via k=(w-c)·u⁻¹ in ZMod7. Pitfalls: cast pushed inside on set-RHS (wrote ((expr : ℕ) : ZMod 7)); padicValNat 7 0 = 0 so 0<x hypothesis needed; ZMod.natCast_zmod_val takes ONE arg.
- File GREEN at ~1721 lines. Next: c63_l9ii3 clone of lemma9_ii j=3 block (Case5mL10 ~2348-2530), then branch lemmas + public case63.

## 2026-XX — agent 8 (successor to f95fb346) session start

- File = 2028 lines (per contract; verifying). Predecessor killed mid-write — first
  step is compile check `lake env lean Research07/LRC7/Case5mC63.lean`.
- Report read in full. Remaining per last section: c63_l9ii3 clone, branch
  lemmas (5 lemma11 branches), finish/lemma5 clone, public case63.

## agent 8 — compile check: GREEN

- `lake env lean` → 0 errors, warnings only (deprecated if_pos/if_neg, unused vars).
- File inventory: helpers L128–1194, c63_lo1 L1195, c63_eps_pair L1268,
  c63_of_avoid L1420, c63_tail2 L1568, c63_tail3 L1614, eps_chain L1675,
  single_carry L1697, c63_l9ii3 L1728–2028 (DONE, compiles).
- Remaining: c63_lemma5 clone (no `s∈{1,2,4}` hyp), 5 lemma11 branches,
  public case63. Next: read c63_of_avoid/tail2/tail3 to map finish infra.

## 2026-09-20 01:15 — final serial agent takeover

- Predecessor landed `c63_finish2`, `c63_finish3`, `c63_case_i`, `c63_case_collision`, `c63_case_ii1_low`, and was finishing `c63_case_ii1_top`.
- Repaired 4 rewrite matching order failures in `c63_case_ii1_top` using `hlam2_mul`.
- `lake env lean Research07/LRC7/Case5mC63.lean` compiles completely GREEN (zero errors).
- Cleaned and verified helpers `c63_sigma_double` (using `interval_cases` + first-branch search), `bad63_first_coord`, `bad63_first_coord_in`, `bad63_second_coord_23`, `bad63_second_coord_45`, and `apLen_1234`.
- `lake env lean Research07/LRC7/Case5mC63.lean` compiles completely GREEN (0 errors).
- All helpers up to line 2560 are solid.
- Now implementing `c63_case_ii2_top`.
- `c63_case_ii2_top` fully implemented and compiles GREEN (exit 0, 0 errors).
  Fixed association and runit7_ne_zero argument types across branches.
- Next: implement `c63_case_ii2_low`, then main theorem `case63`.


## 2026-09-20 (cont) — ii2_low bad-pair branch: full plan + finite checks

- The remaining `sorry` is the `hpair` false branch of `c63_case_ii2_low`
  (≈L3020). Paper §6.3 splits on `ν45 := ν(e45)` vs `h := ν(e23)`:
  * `ν45 < h`: two-stage recipe verified by simulation (0 failures):
    choose `Λ_h(k)` so `q(e13^λ)`,`q(e23^λ) ∈ {0,5,6}` and
    `(q13',q23') ∉ {(0,5),(5,0)}` (finite table, verified: always exists);
    then `Λ_{ν45}` fixes the A1 residues and sets `q(e45'') = 0` →
    `etd'' ∈ {0,1,6}`. apLen≤3 via pairwise diffs ⊆ {0,1,2,5,6}:
    `apLen>3` ⟺ `(D13'',D23'') ∈ {(1,5),(5,1)}` ⟺ `(q13',q23') ∈
    {(0,5),(5,0)}` — excluded.
  * `ν45 > h`: normalize `e45` first (`Λ_{ν45}` → q=0 if `ν45<m`; scalar
    `c` → residue `6·7^m` if `ν45=m`), then `Λ_h` for A1 (c63_l9ii3);
    higher-level `e45` is preserved by `residN_multLow7` /
    `lambda_low_top_resid`.
  * `ν45 = h`: normalize `f = e13 − σ·e45` (σ = r45/r13 ∈ ±1 after cyclic
    relabeling of (d1,d2,d3)) at level `νf > h` (Λ_{νf} → q=0, or scalar →
    `7^m`, or `f=0`); invariants `ẽ = q13−q45 ∈ {0,1}`, `ũ = 3q13+5q23`;
    `case63_table` picks `q45''`; borrow coupling `b13=b12+b23−δ` via
    `qdig_smul_eMod_eq` on `e12=e13−e23`; `(0,3)` cell → ×2 doubling via
    `case63_table_rescue` + `qdig7_smul_carry`.
- Glue lemmas available in-file: `qdig7_multLow`, `residN_multLow7`,
  `exists_multLow_set_qdig`, `exists_top_scalar_set`, `residN_top`,
  `eMod7_mul`, `eMod7_smul`, `qdig_eMod_sub` (same-branch borrow ∈{0,6}),
  `qdig_eMod_sub_etd7` (∈{0,1,6}), `qdig_smul_eMod_eq`, `qdig7_sub_resid`,
  `etd7_eq_twoX`, `rel_same_of_mul`, `remark8_ii'` (diffs⊆{0,1,2,5,6}→
  apLen≤3), `apLen_image_add`, `padicValNat_eq_of_mod`,
  `runit7_eq_of_mod`, `padicValNat_mul_seven`, `qdig7_smul_carry`.
- To port (small): `nat_mod_pow_succ_of_padic`, `level_of_mod_block`,
  `neg_resid_level`/`eMod7_neg_eq` (for σ=−1 via `E45 := eMod7 m d5
  (2*d4) = −e45 mod N`), complement-digit lemma.

## 2026-09-21 — COMPLETE: equal-level rescue landed, file GREEN

`c63_case_ii2_low` is now sorry-free and `lake env lean
Research07/LRC7/Case5mC63.lean` finishes with **0 errors** (109 warnings
only: deprecations + unused-variable lints).

### Final architecture of the ν45 = h rescue (`≈L3700–4830`)

- `c63_eq_dec` — finite decidable check for the `(0,3)`-exceptional-cell
  doubling table (proved by `decide`).
- `c63_eq_double` — doubling rescue: `lam2 = 2·lam` puts the A1 digits in
  `{0,6}`, translated diffs in `{0,1,6}`, `apLen ≤ 3`, A2/A4 pair avoids
  `{2,4}`; finishes via `c63_finish3`. (`runit7` relation needed four
  `runit7_mul` splits to unfold `lam2 = 2·lam`.)
- `c63_eq_step2` — applies the `Λ_j` shift `lam2 = 1 + K·7^{m−j}` with
  `K = (T − q(g'))·r(g')⁻¹`; gets `q(g'') = T`, `q(e13'') = ẽ + T`,
  `q(e23'') = 3(ũ − 3q(e13''))`, borrow consistency `b13 = b12 + b23 − δ`,
  then dispatches: `(0,3)`-cell → `c63_eq_double`, else `case63_table`'s
  `T` → `c63_finish2`/`c63_finish3`. `hgrel` now carries
  `↑(eMod7 (lam·d4)(lam·d5)) = (if σ=1 then 1 else −1) * ↑(lam·g % N)`
  in `ZMod N` (avoids mixed `ZMod 7`/`ZMod N` multiplication).
- `c63_eq_core` — builds the auxiliary residue: `g = e45` or `N − e45`
  per sign `σ`; `f = e13 ∓ e45` is either `0` (contradiction) or has
  level `> j`; normalizes `f` by `Λ_j` (`νf < m`) or top-level scalar
  (`νf = m`), giving `g' = (lam1·g) % N` with `ν(g') = j`,
  `r(g') = r(e13')`, `ẽ ∈ {0,1}`; feeds `c63_eq_step2`.
- `c63_ii2_low_eq` — six-case dispatcher on `w := r(e45) ∈ {u,…,6u}`
  via cyclic permutations of `(d1,d2,d3)` with sign `σ ∈ ±1`.

### Recurring pitfall fixed globally

`ring`/`ring_nf` do **not** reduce literals mod 7 (`x·14 = 0`,
`x = 15x`, `-x = x·6` all stick). Uniform fix: `h7/h7z : (7 : ZMod 7)
= 0` by `decide`, then `linear_combination (±coeff) * h7`. Also:
`linear_combination -(t * h)` does not parse — use `(-t) * h`;
multi-line `(by tac1\ntac2)` as a function argument is
indentation-fragile — single-lined all dispatcher args.

### Verification gates (all pass)

- `lake env lean Research07/LRC7/Case5mC63.lean`: exit 0, 0 errors.
- Forbidden tokens `sorry|admit|native_decide|unsafe`: 0 occurrences.
- `#print axioms case63`: `[propext, Classical.choice, Quot.sound]`.
- `case63` statement unchanged (public theorem, L4903; axiom audit run
  via in-file `#print axioms` since the module olean is not in the
  package import set).
- File length: **4989 lines**.
