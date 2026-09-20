# case62 — §6.2 (|A₁|=4, |Ar|=1) work log

Agent: (this session). Task: prove `case62` in NEW file `Research07/LRC7/Case5mC62.lean`.
Orchestrator notes at top preserved (h10 form; h9ii must end `apLen ≤ j`).

## 2026-09-XX session log (timestamps approximate)

### Findings — environment state
- `Case5mL10.lean` (1573 lines): **`lemma10` EXISTS** at line 1192 with the
  EXACT signature from contract (s : ZMod 7) (hsame : ∀ d ∈ A1, runit7 d = s) form,
  conclusion `∃ d1..d4 ∈ A1, pairwise ≠ ∧ (ν(e21) > ν(e31) ∨ (∃h uniform levels ∧
  r(e31)=2r(e21) ∧ (r(e41)=3r(e21) ∨ r(e41)=4r(e21))))`. → **Use lemma10 directly,
  NO h10 parameter needed.**
- **`lemma9_ii` does NOT exist yet** (no sorry stub either) → need `h9ii` hypothesis.
- `lemma9_i` (Case5mL9:281) and `lemma9_i'` (Case5mL9b:603) exist. `lemma9_i'`
  drops the `<m` level hypothesis: needs `hpos`, `hunit`, `hsame` (runit7 equal),
  `hν : ν(e(b1,b3)) ≠ ν(e(b2,b3))`, `he : eMod7 ≠ 0 both`; conclusion
  `∃ lam, ¬7∣lam ∧ (pairwise qdig7 eMod7 on lam-scaled triple ∈ {0,1,6}) ∧
  apLen (triple.image (qdig7 m ∘ (lam*·))) ≤ 2`. USE lemma9_i' (handles ν=m boundary).
- `Case5mC61.lean` EXISTS but is INCOMPLETE (ends line 831, `sorry` at 827-828,
  NO `theorem case61`). Its `case61_tail` (line 498) is the model for the
  compressed-triple → good7 pipeline: exists_lambda0_qdig_06 → eMod7_multLow0
  verbatim transport → {q4,q5}≠{2,4} via `apLen_pair06_le` else ×3 dichotomy →
  `good7_of_smul_apLen`. Private helpers there I may clone: `mul_pow_add_div`,
  `residue_decomp`, `qdig7_sub_resid`, `eMod7_lt`, `eMod7_self`, `rel_same`,
  `eMod7_same_eq`, `qdig7_eMod_same`, `dvd7_eMod7_of_same`, `eMod7_multLow0`,
  `eq_resid_of_eMod7_eq_zero`, `qdig7_three_mul`, `apLen_mono'`, `apLen_le7`.
  WARNING: those are all `private` in C61 — must re-clone in my file (or prove own).
- Dispatcher `hc62` signature (Case5mTop:822) matches contract exactly.

### Key API signatures (verified)
- `good7 m lam A := ∀ d ∈ A, qdig7 m (lam*d) ∉ {0,6}` (Case5mBase:130)
- `exists_lambda0_qdig_06` (Case5mTop:1141): `hunit, hs≠0, hcls (=s), apLen(image qdig7)≤2
  → ∃ lam ∈ multLow7 m 0, ∀ d∈B, qdig7 m (lam*d) ∈ {0,6}`
- `good7_of_smul_apLen` (Case5mTop:1104): `hm:0<m, hpos, hunit, hs≠0, hsame(=s),
  hlam':¬7∣lam', apLen((A.image (lam'*·)).image (qdig7 m))≤5 → ∃lam,¬7∣lam ∧ good7 m lam A`
- `exists_lambda0_of_shift` (Case5mBase:222): `hm:0<m, hs:s≠0, hunit, hcls:runit7∈{s,2s,4s},
  t:ZMod7, avoids06( (filter=s).image(qdig).image(+t) ∪ (filter=2s).image(+2t) ∪
  (filter=4s).image(+4t) ) → ∃ lam ∈ multLow7 m 0, good7 m lam A`
- `lemma5` (Compress:279): `s∈{1,2,4}, hord: apLen A₂≤apLen A₁ ∧ apLen A₄≤apLen A₁,
  apLen A₁+apLen A₂+apLen A₄≤5 → (∃t, avoids06(union of +t/+2t/+4t images)) ∨
  (apLen A₁=3 ∧ apLen A₂=1 ∧ apLen A₄=1 ∧ ∀d∈A₂∀d'∈A₄, 2d−d'∈{2,4})`
- `lemma6` (Compress:387): `s∈{1,2,4}, 1∈A₁, A₁⊆cycIv 1 (apLen A₁), 6-disjunct →
  ∃t, avoids06(...)`. Disjuncts: (5,0,1)+ẽA4:2d'−1∉{4,6}; (5,1,0)+ẽA2:2−d'∉{2,3};
  (4,0,2); (4,2,0)+cond; (3,3,0); (3,0,3).
- `lemma7_i` (Case5mCases:131): `νd=νd'=0, pos, r(d')=2r(d), 0<ν(e)<m, apLen X≤4 →
  ∃lam,¬7∣lam ∧ etd7 m (lam d)(lam d') ∉ X`
- `lemma7_ii` (Case5mCases:197): `2≤m, νd=νd'=0, pos, r(d')=2r(d), ν(e)=m,
  r(e)∉X∪X+1 → ∃lam,¬7∣lam ∧ etd7 m (lam d)(lam d') ∉ X`
- `exists_multLow_set_qdig` (Case5mBase:509): `j<m, ν(x)=j, x≠0 → ∃k<7,
  qdig7 m ((1+k*7^(m−j))*x) = c`
- `exists_top_scalar_set` (Case5mBase:546): `ν(x)=m, x≠0, t≠0 → ∃0<c<7,
  (c*x)%7^(m+1) = t.val*7^m ∧ qdig7 m (c*x)=t`
- `qdig7_smul_carry` (Case5mBase:469): `(qdig7 m (c*x) − c*qdig7 m x).val < c`
  for `0<c<7`. `qdig7_smul_carry_mem` (497): membership in `(range c).image cast`.
- `apLen_le_iff` (Discrete:387): `apLen X ≤ L ↔ ∃i, X ⊆ cycIv i L` (L≤7)
- `cycIv i L` = {(x−i).val < L} (Discrete:360); `cycIv_one`,`cycIv_two`,`cycIv_zero`,
  `mem_cycIv` exist.
- `apLen_empty` (Compress:149): apLen ∅ = 0. `nonempty_of_apLen_pos` (154).
- `exists_shift_avoid` (Compress:205). `apLen_pair06_le` (Case5mBase:1088):
  `{0,6,a,b}≠{2,4} config → apLen{0,6,a,b}≤5` — CHECK exact stmt.
- `eMod7_smul` (Case5mL9:230, PUBLIC there): `runit7 c ≠ 0 → eMod7 m (c*x)(c*y)
  = (c * eMod7 m x y) % 7^(m+1)`
- `qdig7_sub_resid` PRIVATE at Case5mL9:138 and Case5mL10:139 — clone.
- `elevel7` (Case5mL10:774): `if eMod7=0 then m+1 else padicValNat(eMod7)`;
  `elevel7_of_ne`, `elevel7_of_eq`, `elevel7_le`, `elevel7_sym` exist.
- `etd7` (Differences:64): ẽ on digits. `eMod7` (Differences:55).
- `runit7_mul` (Case5mBase:572), `qdig7_eq_runit7_of_top` (Case5mCases:106):
  `ν(x)=m → qdig7 m x = runit7 x`. `qdig_eMod_sub_etd7_same` (Differences:447).

### Paper §6.2 (bs7.txt:849-877) distilled
A1={d1..d4} (Lemma-10 order), r(d5)∈{2s,4s}, B={d1,d2,d3}, E=(A1−A1)\{0}.
- CASE A: ν(E)≠{m} → Lemma10+Lemma9 → ℓ(B)≤2 → eq(7) shift q(B)⊂{0,6}.
  q(d4)≠3 → ℓ(A1)≤4; q(d4)=3 → q(2·A1)⊂{0,1,5,6}, ℓ≤4. Lemma5 closes.
  [NOTE paper typo: second "ν(E)≠{m}" should be "={m}".]
- CASE B: ν(E)={m} (all diffs level m).
  (ii.1): rescale r(e21)⁻¹ → r(e21)=1,r(e31)=2,r(e41)=3 as level-m residues →
  q(d_i)−q(d_1) = those → q(A1) 4 consecutive → ℓ≤4 → Lemma5.
  (ii.2): Λm puts q({e13,e24,e34})⊂{1,2,4} → pairwise diffs of q(d_i) in
  {±1,±2,±4}?? (paper just says ℓ(A1)≤5). Lemma7 arranges ẽ(d4,d5)∉{4,6}
  (d5∈A4 → lemma6 disjunct1) or ẽ(d4,d5)∉{2,3} (d5∈A2 → disjunct2), unless
  e45=3N/7 → rescale ×2: q({2e14,2e24,2e34})⊂{1,4,2}={1,2,4}, 2e45=6N/7,
  ẽ(2d4,2d5)∉{2,3} → lemma6 disjunct2 on scaled set.

### Open design questions
- h9ii exact signature: mirror lemma9_i shape + j∈{2,3} ratio + `apLen≤j`.
  Orchestrator note: last conjunct `apLen ≤ j` inside the `∀{j}, j=2∨j=3→` scope.
  Will write: `(h9ii : ∀ {m : ℕ} (hm : 0 < m) {b1 b2 b3 : ℕ},
    0<b1 ∧ 0<b2 ∧ 0<b3 → ν=0 triple → runit7 equal →
    ν(e13)=ν(e23) → <m → eMod7≠0 both →
    ∀ {j:ℕ}, j=2 ∨ j=3 → runit7 (eMod7 m b2 b3) = j*runit7(eMod7 m b1 b3) →
    ∃ lam, ¬7∣lam ∧ pairwise-digits∈{0,1,5,6} ∧ apLen ≤ j)` — must double check
  vs how case62 USES it: Case A with ν(e21)=ν(e31)=h<m and r(e31)=2r(e21)
  → j=2 → apLen≤2 → then eq(7) shift to {0,6}.
  WAIT — lemma10 (ii) gives uniform level h for ALL pairs. If h<m, Case A uses
  lemma9_ii on B={d1,d2,d3} with j=2 (r(e31)=2r(e21)). If h=m that's Case B.
  In Case A subcase (i) ν(e21)>ν(e31): lemma9_i' on B with x=e31? Need
  b's s.t. the two edges at common vertex have ≠ levels: lemma9_i' uses
  b1,b2,b3 with x=e(b1,b3), y=e(b2,b3), ν(x)≠ν(y). Take b3=d1, b1=d2,b2=d3:
  x=e(d2,d1)=e21, y=e(d3,d1)=e31, ν(e21)>ν(e31)≠. ✓ gives apLen≤2 directly.
- TODO: check `apLen_pair06_le` exact signature; `exists_shift_avoid`;
  `qdig_eMod_sub_etd7` shape; whether `apLen X ≥ 1` for nonempty X exists
  (need `0 < apLen` ↔ nonempty).

## 2026-09-21 — implementation design finalized (agent: case62 main)

### Major simplification found
For level-`m` differences, digit offsets are EXACT (no borrow):
`eMod7 m x y = r.val * 7^m` verbatim (`residN_top`, Case5mBase:524), so
`x % N = (y % N + r.val * 7^m) % N` and `qdig7_add_top_resid`
(Case5mTop:347, PUBLIC) gives `q(x) = q(y) + r(e)`.  Therefore the whole
borrow-formula / common-f machinery is UNNEEDED for Case B: after any
`Λ_j`/`Λ_m`/`Λ₀` unit multiplier, `q(λd_i) - q(λd_1) = r(e_i1)` verbatim
(level-m residues are verbatim under `lam % 7 = 1` multipliers since
`(λ-1)·u·7^m ≡ 0 mod 7^{m+1}` for `λ = 1 + k·7^{m-j}`, `j ≥ 1`).

### Lemma-7 clone requirement
Only need `lam % 7 = 1` (not mod `7^e`): `runit7 lam = 1`
(`runit7_eq_one_of_mod7`, Case5mBase:597) suffices for `eMod7_mul`
(Case5mBase:646).  Clones `case62_avoid` (= lemma7_i, Case5mCases:131,
~30 lines) and `case62_avoid_top` (= lemma7_ii, Case5mCases:197, ~95
lines, verbatim text obtained) both get `lam % 7 = 1` as an extra
conclusion conjunct (trivial: `1 + k·7^{m-j}` with `m-j ≥ 1`).

### Case B final structure (all offsets exact)
`lemma10` gives `d1..d4`.  `u := r(e21)`:
- (i) `ν(e21) > ν(e31)`: case-B forces `e31 = 0` (else `ν = m` both,
  contradicting `>`).  Then `q3 = q1`; offsets `{0, u, w}` with
  `w = r(e41)` or `0`.  Finite fact `∀ u w, u ≠ 0 → ∃ c ≠ 0,
  apLen {0,cu,cw} ≤ 4` (decide) → lemma5 tail.
- (ii.1) `r(e41) = 3u`: `∀ u ≠ 0, ∃ c ≠ 0, apLen {0,cu,2cu,3cu} ≤ 4`
  (decide) → lemma5 tail.
- (ii.2) `r(e41) = 4u`: rescale `c = u⁻¹` → offsets `{0,1,2,4}` (exact),
  `apLen = 5`, covering start = `d1` (offset-0 element).  Then Lemma-6
  path: Lemma-7-style avoidance on pair `(d1,d5)` [A2: `r(d5)=2r(d1)`] or
  `(d5,d1)` [A4: `r(d1)=2r(d5)`], `lam ≡ 1 mod 7` (preserves offsets +
  translates base), Λ₀-normalize `q(d1) ↦ 1`, then `lemma6` disjunct
  (5,1,0)/(5,0,1) + `exists_lambda0_of_shift` + pullback.
- `e21 = 0` → all `e_i1 = 0` → all `d_i` share residues → image
  singleton → lemma5 tail directly.

### e45 = 0 edge (paper glosses over it)
- A2 (`d5 ≡ 2d1`): `ẽ = 2q(d1)−q(d5) ∈ q(e)+{0,±1} = {0,1,6}` auto-avoids
  `{2,3}` — `qdig_eMod_sub_etd7` (public, Case5mBase:453).
- A4 (`d5` in `4s`, pair `(d5,d1)`, `e = 0` → `2d5 ≡ d1`):
  `ẽ = −carry(2d5) ∈ {0,6}`; the `6`-case is bad.  FIX: `Λ₁`-element
  `1+k·7^{m-1}` chosen via `digit7_multLow_one` (Carry:213) so that
  `digit7 (m−1) (λd5) = 0` → low part `< 7^{m-1}` → `2·low < 7^m` →
  carry 0 → `ẽ = 0 ∉ {4,6}`.  Provable ~50 lines.

### lemma5/lemma6 tail wrappers (digit-level)
`case62_tail5`: `apLen D1 ≤ 4`, `card (filter-2s ∪ filter-4s) ≤ 1` →
lemma5 (hord from card≤1 → apLen≤1) → disjunct2 impossible (one filter
empty) → `exists_lambda0_of_shift` → pullback.  `case62_tail6`: `D1 ⊆
cycIv 1 5`, `1 ∈ D1`, `apLen D1 = 5`, card≤1 leftover, digit conditions
`2−d' ∉ {2,3}` / `2d'−1 ∉ {4,6}` → lemma6 disjunct (5,1,0)/(5,0,1) →
`exists_lambda0_of_shift`.

### h9ii hypothesis (orchestrator contract)
Single obtain-site, mirrors `lemma9_i'` shape with ratio `r(y) = j·r(x)`:
```lean
(h9ii : ∀ {m : ℕ} (hm : 0 < m) {b1 b2 b3 : ℕ},
    (0 < b1 ∧ 0 < b2 ∧ 0 < b3) →
    (padicValNat 7 b1 = 0 ∧ padicValNat 7 b2 = 0 ∧ padicValNat 7 b3 = 0) →
    (runit7 b1 = runit7 b2 ∧ runit7 b2 = runit7 b3) →
    padicValNat 7 (eMod7 m b1 b3) = padicValNat 7 (eMod7 m b2 b3) →
    padicValNat 7 (eMod7 m b1 b3) < m →
    eMod7 m b1 b3 ≠ 0 ∧ eMod7 m b2 b3 ≠ 0 →
    ∀ {j : ℕ}, j = 2 ∨ j = 3 →
    runit7 (eMod7 m b2 b3) = (j : ZMod 7) * runit7 (eMod7 m b1 b3) →
    ∃ lam : ℕ, ¬ 7 ∣ lam ∧
      (∀ x ∈ ({b1,b2,b3} : Finset ℕ), ∀ y ∈ ({b1,b2,b3} : Finset ℕ),
        qdig7 m (eMod7 m (lam*x) (lam*y)) ∈ ({0,1,5,6})) ∧
      apLen (({b1,b2,b3} : Finset ℕ).image (fun d => qdig7 m (lam*d))) ≤ j)
```
Used ONLY in case-A (ii) `h < m` branch, `(b1,b2,b3) = (d2,d3,d1)`,
`j = 2` (from `r(e31) = 2·r(e21)`).

### Case A (some `ν < m`, `e ≠ 0`) — simplified
- (i) `ν(e21) > ν(e31)`, `e31 ≠ 0`: `lemma9_i'` → `apLen ≤ 2` → tail5.
- (i) `e31 = 0`: `ν(e21) > 0` so `e21 ≠ 0`; digit set `{q1,q2,q4}` —
  NOT always ≤4.  Plan: `Λ_ν`/`top-scalar` λ₁ with `q(λ₁e21) = 6` →
  `q2−q1 ∈ {0,5,6}` (borrow `5` possible!) → then a second multiplier:
  Actually `{q1,q1+w,q4}` with `w ∈ {0,5,6}`: for `w=5` `{0,5,z}` has
  apLen-5 configs (`z∈{2,3}`).  Alternative: rescale-first plan — see
  pending question below.
- (ii) `h < m`: h9ii → apLen ≤ 2 → tail5.  `e21 = 0` → collapse →
  singleton → tail5.

### PENDING design question (case A (i) e31=0 borrow-5)
`q(λ₁d2) − q(λ₁d1) = 5` leaves `{a,a+5,a+w}` which can have apLen 5
(`{0,5,2}`,`{0,5,3}`).  Options: (a) choose `q(λ₁e21)` differently —
`q(e) = 6` forces `ẽ ∈ {0,5,6}`; the `5` is the borrow — kill it via
EXACTNESS: if `ν(e21) = m` use top-scalar (exact, `ẽ = c·r(e21)`);
if `ν < m` the offset is inexact — alternative: rescale by `c` with
`e' = (c·e21)%N` at level m?  NO — `ν` preserved.  Alternative (b):
take the `2·λ₁` trick — `e(2λd2, 2λd1) = (2e)%N`; borrow relations
restart.  Alternative (c): handle `{a,a+5,a+w}` apLen-5 configs via
lemma6 (anchor = the `a+5`-element? covering start of `{0,5,2}` is
`5` = d2's offset...) — heavy.  Alternative (d): for `w = 5` note
`{a,a+5,a+w}` IS a 3-set — apLen ≤ 5 always; the apLen-5 subcases
`w ∈ {2,3}`-relative can be re-rescaled by `c` choosing
`apLen{0,5c,wc} ≤ 4` — the `pair_rescale` decide covers `{0,cv,cw}` —
for `v=5`: `{0,5,2}` `c=3` → `{0,1,6}` apLen3 ✓ — WAIT the digit set
under scalar `c` is NOT `c·{digits}` for ν<m differences (inexact).
Hmm.  RESOLUTION NEEDED: simplest may be lemma9-style — for `e31=0`,
`d3 ≡ d1` means `B` has ≤2 residue classes; then apply the
**pair-rescale on `{0, u, w}` where `u = ẽ(d2,d1)` UNNORMALIZED** —
no wait the offsets aren't exact.  Cleanest: use `exists_lambda0_qdig_06`
needs `apLen ≤ 2` — for `{a,a+5}` that fails (apLen 3).  BUT
`apLen {a,a+5} = 3 ≤ 3` — then the digit set `{a,a+5,a+w}` after Λ₀
shift `u` becomes `{a+u, a+5+u, a+w+u}` — Λ₀ shifts all by same `u`
(ᴀ1 class): set `{0,5,w−a'}`+translate — apLen 3-set ≤5; sum≤6 fails.
So need `apLen ≤ 4` on the 3-set `{q1,q2,q4}`: 3-set apLen≤4 UNLESS
it's a "5-triple" `{0,1,4}`-type... the decide: `∀ a b : ZMod 7,
apLen {0,a,b} ≤ 4 ∨ apLen {0,a,b} = 5` — for apLen-5 triples (computed:
`{0,3,6},{0,3,4},{0,1,4},{0,3,5},{0,2,5},{0,2,4}` up to translation).
Then rescale `c` must escape — the pair `{0,c(q2−q1),c(q4−q1)}` — but
offsets under scalar are INEXACT for ν<m pairs (borrow).  HOWEVER the
set `{0,c(q2−q1), c(q4−q1)}` is what we get approximately...
FINAL RESOLUTION (paper-faithful): for `e31 = 0` the differences
`e(λd2,λd1)` have `q = 6` by construction and `ẽ ∈ {0,5,6}` — the
`5`-case means `q(λd2)−q(λd1) = 5` — then `{q1,q2} = {a,a+5}` —
paper claims `q(λB) ⊆ {0,6}` — i.e. needs `ẽ ∈ {0,6}` — so paper's
Lemma-2 application must ALSO kill the borrow: Lemma 2(i) on the
DIFFERENCE `e21` (an element of level ν) puts `q(λe21)=6`; the ẽ-vs-q
discrepancy `∈{0,1,6}` is Lemma 4.  Paper glosses; BUT note
`q(λB) ⊆ {0,6}` requires `q(λd2)−q(λd1) ∈ {0,6}` — for that we need
the EXACT relation `x2%N = (x1%N + q·7^m)%N`-style — which holds iff
`e(λd2,λd1)` is a pure top residue — i.e. `ν(e') = m` — which is NOT
what Λ_ν gives (keeps ν<m).  Alternative: apply Λ₀ shift (j=0):
`(λ₀·e)%N = e` verbatim (residN_multLow7 needs `j<ν(x)`: j=0<ν(e21)
since ν≥1 ✓) — Λ₀ preserves e verbatim AND shifts digits by `K·r`:
`q(λ₀d) = q(d) + K·s'` — q(e) unchanged (=6 if arranged before), ẽ
unchanged (differences cancel).  So the borrow is unavoidable —
`ẽ∈{0,5,6}` is what we get.  So the 3-set `{q1,q1+w,q4}` with
`w∈{0,5,6}`: `w=0` → 2-pt apLen≤4; `w=6` → `{0,6,z}` apLen≤4 iff
`z≠3` (apLen_triple_le) → `z=3` → ×2 (dilate2_dec); `w=5` → `{0,5,z}`:
apLen≤4 iff `z∉{2,3}` (decide: `∀z, z∉{2,3}→apLen{0,5,z}≤4`); `z∈{2,3}`
→ rescale by `c`: `{0,5c,zc}` — choose `c` with `apLen{0,5c,cz}≤4` —
`pair_rescale`-style decide `∀z∈{2,3}, ∃c≠0, apLen{0,5c,cz}≤4` —
`z=2`: c=1:`{0,5,2}` bad; c=2:`{0,3,4}` bad; c=3:`{0,1,6}` ✓;
`z=3`: c=1`{0,5,3}` bad; c=2`{0,3,6}` bad; c=3`{0,1,2}` ✓ — c=3 works
both — BUT the rescaled offsets aren't `c·{5,z}` (borrow

**RESOLUTION for e31=0 borrow-5**: digit set {q1,q1+w,q4}, w∈{0,5,6}. Plan: (a) w∈{0,6} → {0,6,z}-shape via Lambda0-shift → apLen_triple_le + ×2 for z=3. (b) w=5 → {0,5,z}: apLen≤4 iff z∉{2,3} (decide); z∈{2,3} → rescale-by-3 experiment: q(3λd_i) = 3q_i + carry(f_i) ∈ approx-set — carry∈{0,1,2} (qdig7_smul_carry): positions {3q1+c1, 3q2+c2, 3q4+c4}: decide over (z,carries): need ∃ assignment ≤4 — OR simpler: case-split further / reuse lemma6 path. Will resolve in code.

## 2026-09-22 — implementation session (agent: case62 finisher)

### Verified API (all public unless noted)
- `lemma10` L10:1192 — `(hcard : 4 ≤ card) (hpos) (hunit) (s) (hsame : ∀d∈A1, runit7 d = s)`
  → `∃d1∈..∃d4∈A1, pairwise≠ ∧ (νe21>νe31 ∨ (∃ℓ uniform ∧ r(e31)=2r(e21) ∧ r(e41)∈{3,4}r(e21)))`.
- `lemma9_i'` L9b:603 — triple (b1,b2,b3), `ν(e13)≠ν(e23)`, `e≠0` → `∃lam, ¬7∣ ∧ pair-digits∈{0,1,6} ∧ apLen≤2`.
- `lemma9_ii` L10:1760 — same-level `<m`, `r(e23)=j·r(e13)` j∈{2,3} → `∃lam, ¬7∣ ∧ q(e23)∈{0,5,6} ∧ apLen≤j`.
- `lemma5` Compress:279 — `s∈{1,2,4}`, `hord : apLen A₂≤apLen A₁ ∧ apLen A₄≤apLen A₁`,
  `sum≤5` → `∃t, avoids06(union +t/+2t/+4t)` ∨ (3,1,1)-exception.
- `lemma6` Compress:387 — `1∈A₁`, `A₁⊆cycIv 1 (apLen A₁)`, 6 disjuncts incl (5,0,1) `2d'−1∉{4,6}` / (5,1,0) `2−d'∉{2,3}` → `∃t, avoids06(...)`.
- `lemma7_i` Cases:131 / `lemma7_ii` Cases:197 — `∃lam, ¬7∣ ∧ etd7(lam d,lam d')∉X`. lams are multLow ⇒ `lam%7=1` (multLow_mod7, Differences:133) but conclusion doesn't say it → **clone privately with extra conjunct**.
- `exists_lambda0_of_shift` Base:222 — `hm, hs≠0, hcls∈{s,2s,4s}, t, avoids06(union)` → `∃lam∈multLow7 m 0, good7`.
- `exists_lambda0_qdig_06` Top:1141 — `hunit,hs≠0,hcls(=s),apLen≤2` → `∃lam∈multLow7 m 0, ∀d∈B, q(lam d)∈{0,6}`.
- `good7_of_smul_apLen` Top:1104 (single-class only), `exists_lambda0_avoid` Base:193 (single-class).
- `qdig_eMod_sub_etd7` Base:453 — `q(e)−ẽ∈{0,1,6}` UNCONDITIONAL.
- `qdig_eMod_sub` Base:441 — same-branch `q(e)−(qx−qy)∈{0,6}`.
- `eMod7_smul` L9:230 (public), `eMod7_mul` Base:646 (runit7 lam=1), `eMod7_two_mul_left` Cases:69.
- `exists_top_scalar_set` Base:546, `exists_multLow_set_qdig` Base:509, `residN_top` Base:524,
  `qdig7_multTop` Discrete:246, `qdig7_multLow` Discrete:208, `residN_multLow7` Discrete:177,
  `padicValNat_eq_of_mod` Differences:230 (ν preserved by congruence when ≤m),
  `padicValNat_mul_unit7` Discrete:67, `multLow_mod7` Diff:133, `multLow_not_dvd` Diff:143,
  `runit7_multLow` Diff:151, `qdig7_lambda0` Base:147, `qdig7_smul_carry` Base:469,
  `digit7_multLow_one` Carry:213 (two-digit update), `digit7_multLow_one_res` Carry:172,
  `exists_multLow_one_set_seven'` Carry:189, `qdig7_seven` Carry:31,
  `qdig7_congr` Filtering:31, `enu7_le_of_ne` Base:115 (`e≠0 → ν≤m`),
  `apLen_le_iff` Discrete:387, `apLen_le_seven` Discrete:?, `apLen_empty` Compress:149,
  `nonempty_of_apLen_pos` Compress:154, `apLen_image_add` Base:164, `mem_cycIv` Compress:73,
  `cycIv_zero/one/two` Compress:76/87/99, `avoids06_union3` Compress:69, `exists_not_mem_three` Base:1241.
- Clones needed (private elsewhere): `eMod7_self`, `runit7_zero`, `eq_zero_of_runit7_eq_zero`,
  `qdig7_mod'`, `rel_same` (file already HAS `case62_rel_same`), `qdig7_zero`,
  `eq_resid_of_eMod7_eq_zero` (file HAS `case62_resid_eq_of_eMod_eq_zero`).
- `digit7 j x = ((x/7^j)%7 : ZMod7)` Discrete:44.

### Structure decided (NO top-level htop split needed)
lemma10 → (i) νe21>νe31 | (ii) uniform ℓ:
- (i) e31=0 → normalize q(e21')=6 (multLow if ν<m, top-scalar if =m) → pair-diff∈{0,6} → apLen≤2 → tail5.
  e31≠0 → lemma9_i' (d2,d3,d1) → tail5.
- (ii) e21=0 → all collapse (d2,d3,d4≡d1) → tail5 lam'=1 (image apLen 1≤2).
  e21≠0 → ℓ<m: lemma9_ii (d2,d3,d1) j=2 → tail5.  ℓ=m (Case B):
    (ii.1) r(e41)=3u → cub_rescale c → offsets {0,cu,2cu,3cu} apLen≤4 → finish.
    (ii.2) r(e41)=4u → offsets {0,u,2u,4u} → scale c₁=c₀·u⁻¹ (c₀∈{1,2,4} stab) →
      {0,1,2,4} apLen5 + ẽ-avoid → lemma6 → tail6.

### Tail design
- `case62_finish`: set B, s≠0, hcls∈{s,2s,4s}, apLen(s-filter-img)≤4, apLen(2s/4s-filter-img)≤1,
  s-filter nonempty, one of 2s/4s-filter empty → lemma5 (hord via nonempty→apLen≥1; sum≤5 via empty;
  (3,1,1)-exception dead) → `∃lam∈multLow7 m 0, good7 m lam B`.
- `case62_tail5`: triple {b1,b2,b3}+d4 ∈ s-class ⊆ A, d5 leftover, lam' ¬7∣, apLen(triple-img)≤2 →
  exists_lambda0_qdig_06 → {0,6} → q4: ≠3 → apLen{0,6,q4}≤4 → finish;
  =3 → ×2 carry {0,1} → {0,1,5,6} ≤4 → finish with marker s₂=2s'' (classes rotate: big class→2s'').
- `case62_tail6`: scaled set, anchor d1-class-s, offsets {0,1,2,4} w.r.t. d1, leftover d5,
  ẽ-conds (A4: etd7(lam''d5,lam''d1)∉{4,6}; A2: etd7(lam''d1,lam''d5)∉{2,3}) →
  Λ₀ normalize q(d1)↦1 (ẽ invariant: A4 2·4t−t=0; A2 2t−2t=0) → A₁-img={1,2,3,5}⊆cycIv 1 5, apLen5,
  A₂∨A₄={q5'''} → lemma6 → exists_lambda0_of_shift.
- good7 compose: `good7 m lam₀ (A.image (lam'·))` → `good7 m (lam₀·lam') A` (mem_image+mul_assoc).

### (ii.2) ẽ-avoidance detail
- Pair: A4→(d5,d1) twoX (r(d1)=2r(d5): s=2·4s ✓), e=2d5−d1, X={4,6}; A2→(d1,d5) twoX, e=2d1−d5, X={2,3}.
- e=0: A2 auto (ẽ∈{0,1,6} via qdig_eMod_sub_etd7, λ₂=1); A4 Λ₁-fix: digit7_multLow_one sets
  digit7(m−1)(λd5)=0 → f5<7^{m−1} → 2f5<7^m → no borrow → ẽ=0 (private `case62_avoid_zero` ~50ln).
- 0<ν<m: `case62_avoid` (lemma7_i clone +lam%7=1), X={4,6}/{2,3} (apLen2≤4).
- ν=m: stab c₀∈{1,2,4} on w=u⁻¹·r(e) (stab46→r∉{0,4,5,6}=X∪X+1 for X={4,6};
  stab23→∉{2,3,4} for X={2,3}); then `case62_avoid_top` (lemma7_ii clone +lam%7=1).
- ν(e)≥1 when e≠0: `case62_dvd7_twoX`/`twoY` already in file (7∣e for both pair types).
- e'=(c₁e)%N: ν=m preserved (case62_nu_smul_top); ν<m preserved (padicValNat_eq_of_mod);
  ≠0 preserved (unit coprime to N); runit scaled (case62_runit_smul_top).
- Offsets chain: case62_qdig_sub_smul_top (c₁ scalar) then case62_qdig_sub_smul1_top (λ₂≡1).

### Remaining risk
- heartbeat on big membership splits → use explicit Finset.mem_insert chains, set_option on heavy theorems.
- (ii.2) has ~4 multiplier composition steps — keep each in own private lemma.

## 2026-09-22 session 2 (agent: case62 finisher, continued)

### Compile status on entry — FILE DOES NOT COMPILE
Errors found (all in helper layer, NO `theorem case62` exists yet):
1. L743 `case62_avoid_zero.hf.heq`: `Nat.mod_mul_right_div_self` wrong — need
   `Nat.mod_mul_left_div_self` (`m % (k*n) / n = m/n % k`).
2. L769-793 `hrel'` block: omega-fail `< 2*N` bound is FALSE (t can be 2).
   Fix: ModEq route — `N ∣ 2X'+N−Y'` ⇒ `Y' ≡ 2X'+N [MOD N]` via
   `Nat.modEq_iff_dvd` (ℤ-cast, `⟨-(t:ℤ), _⟩` + `Nat.cast_sub hle`),
   then `Nat.add_mod_right` + `Nat.mod_eq_of_lt hylt`.
3. L797 `hXdec`: `Nat.div_add_mod` now `n*(m/n)+m%n=m` (was `m/n*n+...`) —
   leftover `7^m*(a/7^m)+... = a/7^m*7^m+...` needs `mul_comm`.
4. L803 `h2f`/`hlt` omegas: need explicit `hpow : 2*7^(m-1) ≤ 7^m` in context
   (omega can't relate `7^(m-1)`/`7^m`). Add once after `hf`.
5. L813 `hdecomp` ring-fail: replace with calc using
   `hsplit : 2*q5 = 2*q5%7 + 7*(2*q5/7)` + `h7m : 7^(m+1) = 7*7^m`.
6. L930/941/959 `apLen_mono'' _ _`: takes ONE arg (subset proof);
   restructure `refine le_trans (apLen_mono'' ?_) bound`.
7. L1062/1066 `Finset.not_nonempty_empty hne'` gives `False` — needs `.elim`.
- `apLen_mono''` (file-local, L72): `(hXY : X ⊆ Y) → apLen X ≤ apLen Y`.
- `Nat.div_add_mod : n*(m/n)+m%n=m`; `Nat.modEq_iff_dvd : a≡b ↔ ↑n∣↑b−↑a` (ℤ);
  `Nat.add_mod_right : (x+z)%z = x%z`; `Nat.mod_add_div : m%k+k*(m/k)=m`.
- Next: fix these 7 sites → then write `case62` (main theorem missing).

### Compile fixes applied (session 2, cont.)
All 7 error sites fixed; file now compiles CLEAN through `case62_finish` (L~1060).
- `Nat.mod_mul_left_div_self` swap; `hrel'` via `Nat.modEq_iff_dvd` + `⟨(t:ℤ),_⟩`
  + `← Nat.cast_sub hle` + `rw [ht]` + `push_cast`/`ring`; `hmod'` cast + `Nat.add_mod_right`.
- `hXdec` via `(Nat.div_add_mod _ _).symm` + `Nat.mod_mod_of_dvd` + `← hq5` + `mul_comm`.
- `hpow2 : 2*7^(m-1) ≤ 7^m` added after `hf` (fixes both omegas in hYeq/hqy2).
- `hlt` rebuilt with `2*q5%7 ≤ 6` via `Nat.mod_lt (2*q5) (show (0:ℕ)<7 ...)` + omega.
- `hdecomp` as 4-step calc; step2 needs `conv_lhs => rw [hsplit]` (else rw hits `2*q5` inside `%7`,`/7` on RHS too).
- `le_trans (apLen_mono'' ?_) bound`; `case62_apLen_single (qdig7 m (c*d5))` pinned.
- `(Finset.not_nonempty_empty hne').elim`.
- `Nat.add_mul_mod_self_right : (x+y*z)%z = x%z` — ORIGINAL was correct (modulus=RIGHT factor).
### Remaining: `theorem case62` itself + tail5/tail6 pipelines (all missing).

### Architecture finalized (session 2)
- `case62_wrap` (NEW): fuses prepare+finish. Given A (d5 + s-class elts),
  `¬7∣c`, `apLen((s-filter).image (q∘c·)) ≤4` → `∃lam,¬7∣∧good7 lam A`.
  **KEY SIMPLIFICATION**: all lemma9 outputs (apLen≤2 or ≤3) feed DIRECTLY
  into wrap whenever the leftover element collapses into the triple or is
  handled by the {0,6}+q4 trick — no separate tail needed for apLen≤4 inputs.
- `case62_tail5`: lam' + triple {b1,b2,b3} (apLen≤2) + wild d4 →
  exists_lambda0_qdig_06 (class s'=r(lam')·s) → q(triple)⊆{0,6} → s-class
  image ⊆ {0,6,q4}: q4≠3→wrap(Q={0,6,q4}); q4=3→×2 dilate→Q={0,1,5,6}→wrap.
- Case (i) e31=0: residue-collapse tree; all-level-h<m triangle needs
  r-arithmetic clones (residN_level + eMod7_sub_eq + enu7_neg + runit_sub)
  → ratio decide `case62_ratio23` → lemma9_ii (apLen≤3) → wrap.
- Case (ii): h<m→lemma9_ii j=2→tail5; h=m (ii.1) r(e41)=3u→cub_rescale→wrap;
  (ii.2) r(e41)=4u→c=c₀·u⁻¹ (stab46/stab23 when ν(e45)=m) → offsets {0,1,2,4}
  → avoid/avoid_top/avoid_zero on pair → Λ₀-normalize q(d1)=1 → lemma6
  (5,0,1)/(5,1,0) → exists_lambda0_of_shift → compose.
- API notes: enu7=abbrev padicValNat(eMod7); enu7_sym/eMod7_sub_eq/
  runit7_eMod7_neg all PRIVATE in L10 (must clone); padicValNat_mul_seven
  (Filtering:37) `¬7∣lam → d≠0 → ν(lam·d)=ν(d)`; padicValNat_eq_of_mod
  (Diff:230) `a%N=b%N → ν(a)≤m → a≠0 → ν(a)=ν(b)`; eMod7_smul (L9:230)
  `runit7 c≠0 → e(c·x,c·y)=(c·e)%N`; eMod7_mul (Base:646) `r(lam)=1 →
  e(lam·x,lam·y)=(lam·e)%N`.

### case62_wrap + case62_tail5 COMPILED
- `case62_wrap` (prepare+finish fusion): `¬7∣c` + `apLen Q ≤4` +
  `∀d∈A, r(d)=s → q(c·d)∈Q` → `∃lam,¬7∣∧good7`. Uses
  `padicValNat_mul_seven` for hunit of scaled set, `good7_mul` pullback.
- `case62_tail5`: lam'+triple(apLen≤2)+wild d4 → exists_lambda0_qdig_06 →
  q(triple)⊆{0,6} → s-image ⊆{0,6,q4}: q4≠3→wrap({0,6,q4}); q4=3→
  dilate c→2c, case62_carry2+case62_mem0156 → Q={0,1,5,6} → wrap.
- GOTCHA fixed: `rcases case62_coverN h with rfl` substitutes the RHS
  variable (b1) not `d` — use named `h` + `rw [h]` in goal instead.

### r-arithmetic clone chain COMPILED (from C65 verbatim)
- Added (all private): case62_eMod7_zmod_cast, _zmod_cast_same,
  _cast_sub, _sub_eq, _neg_eq, _nat_mod_pow_succ_of_padic,
  _level_of_mod_block, _wrap_sub_mod_gen, _sub_mod_block,
  _neg_resid_level, _enu7_neg, _enu7_sym, _runit7_eMod7_neg,
  _eMod7_sub_block, _eMod7_level_of_runit_ne,
  _eMod7_level_gt_of_runit_eq.
- Key: `case62_eMod7_level_of_runit_ne` gives `ν(e(x,y))=h ∧
  r(e(x,y))=r(e(x,l))−r(e(y,l))` when both edges to l have level h<m —
  this powers the all-level-h triangle: w := r(e24) = u − v.
- Triangle dispatch (e31=0, ν(e21)=ν(e41)=ν(e24)=h<m): u≠v else e24=0.
  v=j·u (j∈{2,3}) → lemma9_ii(d2,d4,d1); u=j·v → lemma9_ii(d4,d2,d1);
  else v=−u → w=2u → lemma9_ii(d1,d2,d4) via r(e14)=−v, r(e24)=w.
- h=m variant of the same: exact offsets {0,u,v}→scale by t·u⁻¹,
  t=1 unless v/u=4 (t=2) → apLen≤4 → wrap. (Only 3 residues — no w needed.)

## 2026-09-19 — main-theorem architecture finalised

After `case62_tail6` compiled clean, designed the public `case62` proof:

**Dispatch plan (verified against signatures):**
- Extract `d5` via `Finset.card_eq_one`; `A := A1 ∪ Ar`; `hother`,
  `hne`, `hpos/hunit` restrictions.
- `lemma10` → case (i) `ν(e21)>ν(e31)` / case (ii) uniform `h`+ratios.
- (i) `e31≠0` → `lemma9_i'` on `(d2,d3,d1)` → `case62_tail5` (d4 wild).
- (i) `e31=0` → triangle-r dispatch via `case62_eMod7_level_of_runit_ne` /
  `case62_eMod7_level_gt_of_runit_eq` (l=d1, h=ℓ):
  * `e41=0` or `e24=0` → 2-point image → `case62_wrap` c=1.
  * `ν41≠ν21` → `lemma9_i'` on `(d4,d2,d1)` → wrap image (d3→d1).
  * `ν41=ν21=ℓ`, `u=v` → `e24=0` or `ν(e24)>ℓ` → `lemma9_i'` `(d2,d1,d4)` → wrap.
  * `u≠v` → `r(e24)=u−v`; `ℓ<m` → ratio decide `v=j·u ∨ u=j·v ∨ v=−u`
    → `lemma9_ii` on `(d2,d4,d1)`/`(d4,d2,d1)`/`(d1,d2,d4)` → wrap image
    (d3→d1 collapse via `eq_resid` clone needed).
  * `ℓ=m` → offsets `{0,u,v}`; rescale `t·u⁻¹` (t=1, or t=2 when v/u=4)
    → `apLen{0,t,tv/u}≤4` → wrap.
- (ii) `e21=0` → all `e=0` (r=0→e=0) → image `{q1}` → wrap c=1.
- (ii) `h<m` → `lemma9_ii` on `(d2,d3,d1)` j=2 → `case62_tail5`.
- (ii) `h=m`, `r(e41)=3c0` → `case62_cub_rescale` c → `Q={q(c·d1)}+{0,w,2w,3w}`
  → wrap (offsets via `case62_qdig_sub_smul_top`).
- (ii) `h=m`, `r(e41)=4c0` → `case62_tail6'` (GENERALISED tail6):
  anchor `a=d1`, `t=1`/`a'=d1` for `c0∈{1,2,4}`; `t=5`/`a'=` element with
  `u·r(e(a',d1))=3` for `c0∈{3,5,6}`. `lam2` from new dispatcher
  `case62_lam2_avoid'` (e≠0: `case62_avoid` for 0<ν<m, `case62_avoid_top`
  for ν=m with stab-rescale `c∈{1,2,4}` when `r(e)` bad; u=r(lam2)).
  X-sets: `{2,3}`/`{4,6}` (c0∈{1,2,4}, a'=d1, no shift);
  `{3,4}`/`{0,2}` (c0∈{3,5,6}, ẽ(a',d5)=ẽ(d1,d5)+6 / ẽ(d5,a')=ẽ(d5,d1)−3).
  e=0 handled: 2s always fine (shift+6); 4s needs carry-1 variant
  `case62_avoid_zero_carry` (digit7(m−1)(lam·d5)≥4).

**Key facts:** pair e's for twoX are ≡0 mod7 → ν≥1 or e=0;
`e(d5,d1)=0` possible for twoX (2d5≡d1) — the carry-1 branch;
`apLen` bounds: {2,3}=2,{4,6}=3,{3,4}=2,{0,2}=3 (all ≤4);
stab sets: X={3,4}→`c·r∈{1,2,6}`; X={0,2}→`c·r∈{4,5,6}`.

**Still needed:** `eq_resid_of_eMod7_eq_zero` clone (C62 lacks it),
`case62_pair01` (b−a∈{0,1}→apLen≤2), `case62_lam2_avoid'`,
`case62_tail6'` generalisation, then `case62` itself.

## 2026-09-19 session 3 (agent: case62 finisher, cont. after a487480a cancel)

### Entry state (verified, 20:18)
- `Case5mC62.lean` = 3223 lines, IDENTICAL to `_dev/tmp_case62.lean` (diff empty).
- NO `theorem case62`, NO sorry/admit in file. Ends mid-assembly: last decl
  `private theorem case62_i` (L2818–3223) = full case-(i) branch of the dispatch.
- Machinery present (all compiled-status unknown until lake run):
  `case62_eq_resid_of_eMod7_eq_zero` L339 (the eq_resid clone — DONE),
  `case62_pair01` L611, `case62_avoid` L778, `case62_avoid_top` L839,
  `case62_avoid_zero` L937, `case62_avoid_zero_carry` L1086,
  `case62_lam2_avoid_pos` L1126, **`case62_lam2_avoid'` L1205 (DONE)**,
  `case62_prepare` L1258, `case62_finish` L1406, `case62_wrap` L1454,
  `case62_tail5` L1488, `case62_tail6` L2015, **`case62_tail6'` L2428 (DONE)**,
  r-arith clones L1782–1979, `case62_coset124`/`offsets_1235`/`nu_pow7`/`runit7_pow7`
  L1980–2014.
- Report's "still needed" list is STALE: eq_resid clone, pair01, lam2_avoid',
  tail6' all already in file. Remaining = `case62_ii` (uniform-level branch)
  + public `theorem case62`.
- Staged text: `_dev/c62_main_i.txt` (383ln, likely already integrated as
  case62_i), `_dev/c62_main_ii4.txt` (551ln — candidate for case62_ii body or
  the ii-branch of case62), `c62_tail6p2.txt`, `block.txt`, `docblock.txt`.
- Plan: read c62_main_ii4.txt + tail of case62_i → determine ii-branch shape →
  write `case62_ii` (or inline) + `theorem case62` → compile → iterate.

### Session 3 result — COMPLETE (2026-09-19 ~20:55)

**`theorem case62` compiles; whole file 0 errors** (`lake env lean
Research07/LRC7/Case5mC62.lean`, ~44s). `#print axioms case62` =
`[propext, Classical.choice, Quot.sound]` (gate OK). No
sorry/admit/native_decide/unsafe.

**Signature correction**: `hc62` (Case5mTop:822) is **|A1|=4, |Ar|=1**
(`Ar` singleton with `runit7 ∈ {2s,4s}`) — NOT the 2+2+1 contract text
(that's `hc66`). case62 applied as `(case62 hm)` in Case5m.lean:32 — no
h10/h9ii params (uses `lemma10`/`lemma9_ii` directly, both now public in
Case5mL10:1192/1763).

### What was added this session (file → 4068 lines)
- `case62_ii4` (L3234, pasted from `_dev/c62_main_ii4.txt` verbatim, then
  6 fixes below) — the `{0,1,2,4}`-offset/lemma6 route for `r(e41)=4u`.
- `case62_ii` (L3785, NEW) — uniform-level dispatch: `e21=0` collapse →
  wrap c=1; `h<m` → `lemma9_ii (j:=2)` on (d2,d3,d1) → `case62_tail5`;
  `h=m` ratio-3 → `case62_cub_rescale` + `case62_wrap` (Q = translate of
  `{0,wu,2wu,3wu}`); ratio-4 → `case62_ii4`.
- `theorem case62` (L3992, NEW) — extracts `d5` via `card_eq_one`, builds
  `hother`/`hne`/`hcover` (A1={d1..d4} via `eq_of_subset_of_card_le` +
  card4 from the 6 pairwise-≠; s-class ⊆ A1 since `s∉{2s,4s}`), calls
  `lemma10`, dispatches to `case62_i`/`case62_ii`.

### Failure+fix log this session (also in `_dev/failures.md`)
- staged ii4 `fin_cases cu <;> simp_all` left cu=0 → replaced by
  `decide` over `∀ cu : ZMod 7, cu ≠ 0 → cu∈{1,2,4}∨cu∈{3,5,6}`.
- `ring` cannot reduce `8≡1 mod 7`: `s = 2*(4*s)` (hrel51, hshift46 ×2)
  and `u*s = 2*(u*(4*s))` (hshift46' ×2) → `(by decide : ∀ a, a=2*(4*a))`
  / `(by decide : ∀ a b, a*b=2*(a*(4*b)))`; also needed a SECOND `one_mul`
  in the rw chain (`one_mul` rewrites only the first `1*_` match).
- my `case62_ii`: `subst heq` eliminated `m` not `h` → removed subst,
  pass `hνXX.trans heq` for `ν=m` args.
- `linear_combination (2:ZMod7)*h4` for `s=4*s→s=0` fails (mod-7 coef
  needs char reduction) → `mul_eq_zero` route via `3*s=0` (pure `-h4`).
- `linear_combination` sign on `mem_image` goals: `-hqXs` (goal is
  `x+qd1 = qd`, atom is `qd-qd1-x` negated).
- `apLen`-kernel literal must match `cub_rescale`'s `(2*w)*u` grouping —
  state Q as `{0, w*u, 2*w*u, 3*w*u}` (not `2*(w*u)`).
- `lemma9_ii (j := 2)` — pin the implicit `j` or the `↑j` unification
  against literal `2` may not fire.

### Files touched
- `Research07/LRC7/Case5mC62.lean`: +845 lines (ii4 paste + fixes + ii +
  case62). tmp backup at `_dev/tmp_case62_backup.lean` (pre-#print state,
  identical to final minus nothing).
- `_dev/c62_main_ii.txt`: my case62_ii+case62 staging (292 lines).
- `_dev/failures.md`: 2 ledger lines appended.

### Remaining notes for orchestrator
- `Case5m.lean` line 32 now has `(case62 hm)` satisfiable — but `case61`
  (Case5mC61) still has `sorry` at ~L827 per session-1 notes; full
  `lake build` still gated on that file, not this one.
- All other staged fragments (`c62_tail6p2.txt`, `block.txt`,
  `docblock.txt`) were already integrated earlier — nothing else pending.
- DONE = met: `case62` compiles, whole file 0 errors.
