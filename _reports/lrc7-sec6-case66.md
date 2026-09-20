# lrc7-sec6-case66.md — Case66.lean implementation log (BS7 §6.6)

Task: prove `case66` (signature frozen in task contract) in
`Research07/LRC7/Case66.lean`. Subagent report per AGENTS.md protocol.

## 2026-09-19 06:00 — API survey findings (read-only phase)

Spec §4.6 (`_reports/lrc7-sec6-spec.md:576-625`) + ERRATUM addendum
(`:1063-1085`, the §6.6 delicate-branch VERIFIED recipe) read.

Key decls confirmed present:

* `Case5mBase.lean`:
  - `enu7` (l.50), `mem_multLow7` (53), `eq_one_add_of_mem_multLow7` (64),
    `not_dvd_of_mem_multLow7(_zero)` (70/76),
    `eMod7_multLow_low` (82), `enu7_multLow_low` (104),
    `enu7_le_of_ne` (115): `eMod7 m x y ≠ 0 → enu7 ≤ m`.
  - `good7` (130) = `∀ d ∈ A, qdig7 m (lam*d) ∉ {0,6}`;
    `good7_mul` (137): pulls `good7` back through image.
  - `qdig7_lambda0` (147), `apLen_image_add` (164),
    `exists_lambda0_avoid` (193), `exists_lambda0_of_shift` (222) —
    workhorse Λ₀ bridge: `avoids06 (A₁+t ∪ A₂+2t ∪ A₄+4t)` (filter-based)
    → `∃ lam ∈ multLow7 m 0, good7`.
  - `qdig_eMod_sub` (441): same-class `q(e(x,y)) − (qx − qy) ∈ {0,6}`.
  - `qdig_eMod_sub_etd7` (453): unconditional `q(e)−ẽ ∈ {0,1,6}`.
  - `qdig7_smul_carry` (469): `q(c·x) − c·q(x)` has val < c.
  - `exists_multLow_set_qdig` (509): `ν(x)=j<m → ∀c, ∃k<7,
    qdig7 m ((1+k*7^{m-j})*x) = c`.
  - `residN_top` (524), `exists_top_scalar_set` (546):
    `ν(x)=m → ∃c∈(0,7), (c*x)%N = t·7^m ∧ qdig7 m (c*x) = t` (t≠0).
  - `runit7_mul` (572), `runit7_eq_one_of_mod7` (597),
    `runit7_mul_of_mod7` (611), `eMod7_mul` (646): `runit7 lam = 1 →
    eMod7 m (lam*x) (lam*y) = (lam * eMod7 m x y) % N`.
  - `eMod7_add` (664): same-class triple `e(x,y)+e(y,z) ≡ e(x,z)`.
  - `filtered7_mod7` (691): filtered7 + `lam % 7 = 1`.
  - `absModN_lt_iff_qdig7` (782), `qdig7_mem0156_of_absModN_le` (910),
    `absModN_two_mul_le` (969), `absModN_three_mul_le` (1005),
    `remark8_i_int` (1056).
  - Finite decides: `bad66a` (1281), `case66a_bad` (1294),
    `case66a_eps` (1307), `case66b_good` (1321) — all green.
* `Case5mCases.lean`: `runit7_two` (29), `eMod7_two_mul_left` (69),
  `qdig7_eq_runit7_of_top` (106), `lemma7_i` (131), `lemma7_ii` (197 —
  the `q(λ·7d)=6` branch giving `ẽ ∈ {r(e)−1, r(e)}`).
* `Carry.lean`: `qdig7_eq_digit7` (26), `qdig7_seven` (31),
  `digit7_add`/`digit7_add_mem`/`qdig7_add_mem` (51/67/86),
  `qdig7_two_eq_smul` (95), `qdig7_two_eq_smul_add_one` (128),
  `runit7_of_padic_zero` (165), `digit7_multLow_one_res` (172),
  `exists_multLow_one_set_seven'` (189), `digit7_multLow_one` (213).
* `Case5mTop.lean`: `qdig7_add_top_resid` (346):
  `x%N = (y%N + k*7^m)%N → q(x) = q(y)+k`.
* `Case5mL9.lean`: `eMod7_smul` (230): `runit7 c ≠ 0 →
  eMod7 m (c*x) (c*y) = (c*eMod7 m x y) % N`; `lemma9_i` (281).
* `Filtering.lean`: `qdig7_congr` (31), `padicValNat_mul_seven` (37),
  `exists_k_all_good7` (57), `filtered7` (114), `filtered7_good` (225),
  `exists_top_scalar` (270).
* `Discrete.lean`: `level7`,`qdig7`,`runit7`,`digit7`,`multLow7`,
  `multTop7` defs; `qdig7_multLow` (208): `ν(x)=j →
  q((1+k*7^{m-j})x) = q(x)+k·r(x)`; `qdig7_multTop` (246):
  `ν(x)=m → q(l*x) = l·r(x)`; `residN_multLow7` (177):
  `j<ν(x) → (1+k*7^{m-j})*x % N = x % N`; `qdig7_add_one` (288);
  `cycIv`/`apLen`/`apLen_le_iff`/`mem_cycIv`; `absModN_top_ge7` (93).
* `Compress.lean`: `bad06`/`avoids06`/`avoids06_union3` (43-69),
  `mem_cycIv` (73), `exists_shift_avoid` (205), `remark8_i/ii` (228/242),
  `lemma5` (279 — needs `hord : apLen A₂ ≤ apLen A₁ ∧ apLen A₄ ≤ apLen A₁`,
  else (3,1,1)-exception disjunct), `lemma6` (387), `lemma12` (516).
* `Differences.lean`: `residueRel`/`residueRelOf`/`eMod7`/`etd7`/
  `ratioCases` defs (40-72); `residueRelOf_eq_*` (75/89/105);
  `runit7_eq_of_rel_same` (121); `multLow_mod7`/`multLow_not_dvd`/
  `runit7_multLow`/`runit7_multLow_apply` (133-189);
  `residueRel_multLow` (192); `etd7_multLow_same` (204);
  `etd7_multLow_low` (379); `qdig_eMod_sub_etd7_same` (447).

## Plan (draft)

`A1={d1,d2}` class `s`, `A2={d3,d4}` class `2s`, `A4={d5}` class `4s`.
`e12 = eMod7 m d1 d2`, `e34 = eMod7 m d3 d4` (both `same`-branch since
`s≠2s`, `2s≠4s` when `s≠0`).

Finishing lemma `finish66` (to write): if `lam` has `lam%7=1` (or more
generally is a 7-unit scaling classes uniformly) and
`apLen(q(lam''A1)), apLen(q(lam''A2)) ≤ 2` then done via
`lemma5`+`exists_lambda0_of_shift` (ordering handled by `s↦2s` rotation
when `apLen A2 > apLen A1`; `(3,1,1)`-exception impossible since
apLens ≤ 2).

Sub-case tree on `(enu7 e12, enu7 e34)` — pending detailed derivation,
see next sections.

## 2026-09-XX — carry analysis verified for all `m ≥ 2` (pre-implementation)

The Λ₁ perturbation `(1+j·7^{m-1})` on a unit `x` shifts:
* `(m−1)`-digit: `A_i ↦ (A_i + j·r_i) % 7` where `r_i = x%7` — via
  `digit7_multLow_one` (Carry.lean:213).
* low part `g_i = x % 7^{m-1}`: FIXED (increment divisible by `7^{m-1}`).
* residue `eMod7 m (λx)(λy)`: fixed for level-`m` differences
  (`λ·r·7^m ≡ r·7^m mod N` since `2m−1 ≥ m+1 ⟺ m ≥ 2` — uses `2 ≤ m`).

For a twoX pair `(x,y)` with `eMod7 m x y = r·7^m` (ν = m):
write `2·(x%P) − (y%P) = σ·P` with `P = 7^{m-1}`, `σ ∈ {0,1}` (forced:
`2x'−y' ≡ 0 mod 7^m` gives `2g_x ≡ g_y mod P`; range `(−P,2P)`).
Then `2A_x − A_y + σ ∈ {0,7}` (consistency) and the shifted etd satisfies

  `etd7 m (λ_j x) (λ_j y) = r − ε₁(j)`,
  `ε₁(j) = if 2*(A_x+j*r_x)%7·val + σ = (A_y+j*r_y)%7·val + 7 then 1 else 0`.

Verified by Python enumeration:
* eps1-cover: for all `(a2,a4,σ)` with `2a2+σ ∈ {a4,a4+7}`, both ε values
  are realized by some `u ∈ ZMod 7` (`u = j·r_x`). 0 failures.
* eps2-cover (case a-iii): for all `(a2,a4,a5,σ,σ')` with
  `2a2+σ ∈ {a4,a4+7}` and `2a5+σ' ∈ {a2,a2+7}`, all 4 `(ε₁,ε₂)` patterns
  realized. 0 failures.

This subsumes the paper's sketchy `ẽ ∈ {r−1, r}` claims AND fixes the
m=2 subtlety (top-digit shift under Λ₁ is `j·(x/7)%7 + carry`, not
`j·runit7` — but the borrow formulas only involve the `A`-digits and the
fixed `σ`, so the analysis is uniform for `m ≥ 2`).

### Case-tree architecture (final, to implement)

After scalar normalization `c·s⁻¹` on `e12`/`e34` separately (compose two
scalars — need both normalized simultaneously: use single scalar making
`r(e12') ∈ {1,2,4}`, then handle `e34` cases with `r34' ∈ {1,...,6}` —
NO: normalize BOTH: `e12' = r'·7^{ν12}` with `r'∈{1,2,4}` via scalar on
`e12` only fixes e12; `e34` needs its own normalization — but a single
scalar `c` multiplies both residues by the same `c`! Plan: choose scalar
`c` such that `c·r12 ∈ {1,2,4}`; then `r34' = c·r34` may be any nonzero.
For the ratio relations only `r12'/r34'` matters:
`r34' ∈ {r12', 2r12', 4r12'}` in the same-residue... wait NO — r12/r34
are both in `{1,..,6}` with `r12 = r34` or `r12 = 2r34` or `r34 = 2r12`
— the relative ratios are what the case split uses; after common scaling
`c` the relations preserved. So choose `c` s.t. `c·r34 ∈ {1,2,4}`? or
normalize the SUBORDINATE pair. Cleanest: pick scalar `c` with
`c·r34 ∈ {1,2,4}` — then `r12' ∈ {r34', 2r34', 4r34'} ⊆ {1,2,4}` too
automatically! Since `r12' ∈ {r34', 2r34', r34'/2·4?}` — r12 ∈
{r34, 2r34, 4r34} (from same-class: ratio ∈{1,2,4}? NO — e12/e34 are
difference residues in {1..6}, and their ratio need not be in {1,2,4}!
RE-CHECK: the case split is `r12 = r34`, `r12 = 2r34`, `r34 = 2r12` —
ratios {1,2,4} — is that forced? e12 = e(d1,d2) same-class → r12 ∈
{±(s−s)}... r12 = runit7(d1−d2)·can be ANY nonzero — NOT restricted to
{1,2,4}! The case split `r12 ∈ {r34, 2r34, 4r34}` must come from
elsewhere — the paper says "wlog r(e12) ∈ {1,2,4}" via Lemma 2's scalar
freedom... and then case split on r34 vs r12 covers ALL pairs since after
fixing r12 ∈{1,2,4}, r34 is compared: paper splits on whether
r(e34) ∈ {r12, r12/2, 2r12} — the remaining ratios {3,5,6}·r34 must
still be handled! RE-READ the paper: it normalizes BOTH e's
independently?? Lemma 2 scalar acts on ALL elements simultaneously —
can only normalize ONE residue. Paper: "we may assume r(e12)=1" hmm —
actually paper §6.6 text: 'Let e12 = e(d1,d2), e34 = e(d3,d4). If
ν(e12) ≠ ν(e34)... If ν equal and r(e12)=r(e34)... If r(e12) ≠ r(e34)
and ν < m... ν = m: (a) r(e12)=2r(e34), (b) r(e12)=4r(e34)??' — the
paper's (b) is r(e12)=4r(e34)·i.e. r34 = 2r12 wait NO: paper (b) has
e12 = N/7 (r=1), e34 = 2N/7 (r=2) → r34 = 2·r12 — consistent with my
earlier reading. And the FULL enumeration of (r12,r34) ∈ {1,2,4}²
after normalizing r34? Hmm — the paper normalizes r(e34)?? Let me
recheck ejc_pages.txt — it says case (a) `e12 = 2N/7, e34 = N/7` and
(b) `e12 = N/7, e34 = 2N/7`. For equal-ν different-r: possible pairs
(r12,r34) ∈ 36 combos; paper claims only (2,1) and (1,2) after scaling?
c·(r12,r34) = (2,1) solvable iff r12 = 2r34; = (1,2) iff r34 = 2r12.
Pairs with r12 = r34 scale to (r,r) — equal-r branch. What about
r12 = 4r34 — e.g. (4,1) or (1,2)·(r12,r34)=(4,1): scale c: c·4=2·? c·4
∈{2}, c·1=1 → c=4·? 4·4=16≡2·c=4 gives (2,4)·= (2r', r') with r'=4 —
that's (a)-shaped (r12 = 2r34·4·? (2,4): r12=2, r34=4 → r12 = 4·r34·—
hmm (2,4): 2 = 4·4 mod7? 4·4=16≡2 YES → r12 = 4·r34 ⟺ r34 = 2·r12 —
that's case (b)! So ALL pairs (r12,r34) with r12≠r34: either
r12 = 2r34 or r34 = 2r12 — because {r12,r34}⊂{1,...,6}·NO that's not
true in general — e.g. (3,5): 3≠5, 3≠2·5=3·? 2·5=10≡3 YES r12=2r34·—
hmm: for ANY two nonzero residues a,b mod7: either a=2b or b=2a or
a=b? NO: (3,1): 3≠1, 3≠2, 1≠6·— 3∉{1,2,4}·the point is the paper
must handle ALL ratio pairs. The claim `r12/r34 ∈ {1,2,4}` is NOT
automatic — need to recheck the paper text.)

OPEN QUESTION (resolve before coding the case split): which
(r12,r34)-pairs does the paper cover? From the extracted text: it lists
`(a) e12=2N/7, e34=N/7` and `(b) e12=N/7, e34=2N/7` — presumably after
choosing the scalar c so that BOTH e's land in {1,2,4}·7^m — possible
only if r12/r34 ∈ {1,2,4}·{1/2,1/4}. For a ratio like r12=3r34 —
paper must have an argument that e-residues of same-class pairs are
constrained... `runit7(e(d1,d2))` for same-class = unit of d1−d2 —
arbitrary. UNLESS the normalization uses a different scalar freedom —
Lemma 2 (exists_multLow_set_qdig etc.) gives digits, not residues. Hmm —
maybe paper wlog assumes e12 = 1 or 2 or 4·7^ν AND enumerates r34 ∈
{1..6}: cases r34 = r12 (equal), r34 = 2r12 or 4r12 (b-like),
r34 = r12·{3,5,6} — the {3,5,6} ratios — does paper cover them? The
extracted §6.6 passage only shows (a),(b) — MUST recheck whether ratio
r12/r34 ∈ {3,5,6} can occur — YES it can (d1−d2, d3−d4 arbitrary
units). So the paper's case split as extracted may be INCOMPLETE or I'm
missing normalization — FLAGGED for re-examination of ejc_pages.txt.

### ORCHESTRATOR NOTE (2026-10-06) — the `{3,5,6}`-ratio question RESOLVED

Re-read paper line 1118: "**Up to renaming the elements in A** we may
assume r(e12), r(e34) ∈ {1,2,4}". The renaming is the two INDEPENDENT
within-pair swaps:

* `A1 = {d1,d2}`: swapping d1↔d2 flips `e12 → e(d2,d1) = −e12 mod N`,
  hence `runit7(−e) = −runit7(e)` (ν(−e)=ν(e) since ν(e) < m+1 = ν(N)).
  Negation pairs `{1↔6, 2↔5, 3↔4}`, so one of {r, −r} ∈ {1,2,4} ALWAYS.
* Same for `A2 = {d3,d4}` → `r(e34) ∈ {1,2,4}` independently.

So ratios {3,5,6} never need separate treatment — the Lean proof should
extract the two elements of each pair-class and CHOOSE the orientation
with `runit7 e ∈ {1,2,4}` (finite fact: for `e` with `runit7 e ≠ 0`,
`runit7 e ∈ {1,2,4} ∨ runit7 (N − e) ∈ {1,2,4}` — small `decide`/`fin_cases`
on the residue).

**Collision edge case** (eMod7 = 0, i.e. d1 ≡ d2 mod N): `runit7 = 0`,
renaming can't help — but then `q(λd1) = q(λd2)` for ALL λ, so
`ℓ(λA1) = 1 ≤ 2` trivially; the pair set collapses and the
`ν(e12)≠ν(e34)`/uniform-h analysis only needs nonzero differences.
Handle collisions as an early trivial branch (ℓ(A1)≤1 or ℓ(A2)≤1 →
`exists_lambda0_avoid`/lemma5 finish).

Then the case tree:
* `ν(e12)≠ν(e34)` → Lemma 2 (`exists_lambda0_of_shift`-style two-level
  machinery / spec §3.3 `lemma2` equivalents) → `q(e12),q(e34)∈{0,6}` →
  (15) `ℓ(A1),ℓ(A2)≤2` → lemma5.
* `ν(e12)=ν(e34)`, `r12=r34`: `f=e12−e34`, `ν(f)>ν(e12)` — lemma2 on
  `(f,e34)` or direct; `q(e12)=q(f+e34)∈{0,6}` via carry lemma4.
* `r12≠r34` (so `r12=2·r34` or `r34=2·r12` after renaming), `ν<m`:
  lemma9 (9ii shape) → both in {0,6}.
* `ν(e12)=ν(e34)=m` delicate branch: (a) `r12=2r34` → normalize
  `e12=2N/7, e34=N/7`, λk for k∈{1,2,3} puts `q(λk·A2)={k,k+2}` etc —
  the `case66a_*`/`case66b_good` finite tables; (b) `r12=4r34`
  symmetric. My earlier 0/15012-failure recipe check covers the
  delicate recipe viability.

## 2026-10-07 — resumption by new agent; compile + recipe findings

* Case66.lean compiles clean (exit 0, warnings only) — helper layer intact.
* Read spec §4.6, ERRATUM addendum, paper text (bs7-ejc.txt:764-802).
* **FINISH DESIGN (verified conceptually)**: goal reduces to producing
  unit `λ'` with `q(λ'·e12), q(λ'·e34) ∈ {0,6}` ⇒ pair `apLen ≤ 2` each
  (via `qdig_eMod_sub_etd7_same`: `q(e)−ẽ ∈{0,6}` ⇒ `ẽ∈{0,1,6}`).
  Then `lemma5` + `exists_lambda0_of_shift` on `B = (A1∪A2∪A4).image (λ'*·)`:
  * if `apLen qB2 ≤ apLen qB1`: lemma5 (qB1,qB2,qB4), class `s'=r(λ')·s`.
  * else (apLen qB1 < qB2): **re-parameterize `s''=r(λ')·2s`** — then A2 is
    class-1, A4 is class-2 (`4s=2·2s`), A1 is class-4 (`s=4·2s`)!
    lemma5 (qB2,qB4,qB1) → `avoids06(qB2+t ∪ qB4+2t ∪ qB1+4t)` which is
    exactly the `exists_lambda0_of_shift` union under s''.
    Sum ≤ 2+2+1=5 always; (3,1,1)-exception impossible (apLen ≤2).
* **Collision**: `e12=0` ⇔ `d1≡d2 mod N` ⇒ `q(λd1)=q(λd2)` ∀λ ⇒ apLen=1
  automatically — only need the other pair's `q∈{0,6}` (single-target setter).
* **Distinct levels** `ν12≠ν34`: two-step recipe (higher first via
  `exists_multLow_set_qdig`/`exists_top_scalar_set`, then `Λ_{low}` on the
  lower which preserves the higher via `residN_multLow7`). λ=λ_b·λ_a.
* **Equal-r, level h**: `f=(e12−e34)%N`, `e12≡f+e34`, recipe `t_f=6,
  t_base=0` ⇒ `q(λe12)=6+0+C ∈{6,0}` ∀C∈{0,1} — clean!
* **DELICATE BRANCH SOLVED (r_dbl=2·r_base, h<m)**: `f=(e_dbl−2e_base)%N`,
  `e_dbl≡f+2e_base`, `q(λe_dbl)=q(λf)+2q(λe_base)+C`, C∈{0,1,2}.
  **RULE: `t_f=6` always** (λ₁=Λ_{νf} k=(6−qf)·r_f⁻¹ if νf<m; scalar
  c=6·r_f⁻¹ if νf=m; f=0 handled separately with t_base=C0-dependent).
  Then `t_base = 6 if C=2 else 0`: q=6+2·t_base+C ∈{0,6} verified:
  C=0→{6};C=1→{0};C=2→t=6 gives 6. **PYTHON-VERIFIED 0 failures**
  (`_dev/scratch/check66_del5.py`, m∈{1,2,3}, ~735k configs).
  Key: C depends only on λ₁ and base residues, NOT on k₂ (Λ_h preserves
  low blocks) — so compute C after fixing λ₁, then choose t_base.
* Level-m cases (a)/(b): model `{k,k+2},{2k−x,2k−x+1},{4y+4k}` (case a,
  x=ẽ(d2,d4), y=ẽ(d2,d5)) via `case66a_bad`/`case66a_eps`/`case66b_good`
  tables + Λ₁-ε machinery (`q(λ·7d5)=4ε₂+2ε₁`). This is the remaining hard
  part — ẽ's are Λ₀-invariant, pair digits frozen at level m.

## 2026-XX-XX — BREAKTHROUGH: level-m mechanism fully decoded and Python-verified

### The σ-linkage (new key insight)
When `e(x,y) = r·7^m` is a PURE-TOP residue (or 0), the low parts are linked
EXACTLY: `y % 7^m = (2·(x%7^m)) % 7^m` (twoX case). Hence the borrow is
one-sided: `ẽ(x,y) = r − σ` with `σ = ⌊2·(x%7^m)/7^m⌋ ∈ {0,1}` — never `r+1`.
So `ẽ ∈ {r−1, r}` AUTOMATICALLY (the lemma7_ii bound is free!). Uniform:
- twoX `e=2x−y`: `ẽ = 2q(x)−q(y) = r − σ(x)`, `σ(x)=q(2x)−2q(x)∈{0,1}`
- twoY `e=2y−x`: `ẽ = 2q(y)−q(x) = r − σ(y)`
- same `e=x−y`: `ẽ = q(x)−q(y) = r` exactly (σ=0), and `q(x)=q(y)+r`.
This bound survives ANY multiplier preserving the residue (all Λ_j, j<m).

### Middle subcase hole RESOLVED (was feared (6,6) at r24=5)
With σ-linkage, `x = r24−σ24 ∈ {r24−1,r24}`; for r24=5, `x∈{4,5}` — `x=6`
impossible, so `y∉{2,4}` (lemma7_i setter) kills ALL bad pairs.
Verified: `_dev/scratch/check66_eps7.py` — 0 holes/74088 configs (m=2)
and 4.1M configs (m=3) with CORRECT model (d5 = inv2·(d2+e25) mod N,
inv2=(N+1)/2 — an earlier model used d5=4·(d2+e25) treating 4 as 2⁻¹ mod N;
results coincidentally still held but the realized-pair data was garbage).

### Last subcase (ν(e24)=ν(e25)=m) — verified mechanism
- `(x,y) = (r24−σ24, r25−σ25)`, `σ_i = ⌊2·(λd_i %7^m)/7^m⌋ ∈ {0,1}` — the
  four corners are exactly `(r24−ε1, r25−ε2)`, ε∈{0,1}² (matches case66a_eps).
- `σ_i = (2·w_i + cm_i)/7` where `w_i = digit_{m−1}(λ_k d_i)`,
  `cm_i = ⌊2·(d_i %7^{m−1})/7^{m−1}⌋ ∈{0,1}`.
- `w5 = (b5 + k·r5)%7` (settable via k), `w2 = (2·w5+cm)%7` (linkage).
- Finite check verified: `∀ cm c2' a b ∈{0,1}: ∃w<7: (2w+cm)/7=b ∧
  (2·((2w+cm)%7)+c2')/7=a` — `decide`-able (112 cases).
  `_dev/scratch/check66_eps10.py`: param combos all realized; end-to-end
  verified m=2,3 (0 failures).

### Case (a) algorithm (normalized e12'=2·7^m, e34'=7^m via scalar c=r34⁻¹)
- `0<ν(e24)<m`: lemma7_i X={4,5,6} on (d2,d4) → x∉{4,5,6} → done.
- `ν(e24)=m` or e24=0 (r24∈{0..6}): x∈{r24−1,r24} always.
  - r24∈{1,2,3}: x∈{0,1,2} auto-safe → done.
  - r24∈{0,4,5,6}: `0<ν(e25)<m` → lemma7_i on (d5,d2) with X={2,4}
    (r24∈{4,5}) or {4,6} (r24∈{0,6}) → done;
    else (ν(e25)=m or e25=0) → corner realization (eps4) → done.
### Case (b) algorithm (normalized e12'=7^m, e34'=2·7^m via c=r12⁻¹)
Need only x=ẽ(d2,d4)∉{2,4} (case66b_good covers all y'):
- `0<ν(e24)<m` → lemma7_i X={2,4}.
- `ν(e24)=m`: r24∈{1,6} auto-safe ({r24−1,r24}∩{2,4}=∅); r24∈{2,3,4,5}:
  σ24-setter via `q(λ·7d2)=w` (w=4 → σ24=1 for r24∈{2,4}; w=0 → σ24=0 for
  r24∈{3,5}).
- e24=0: x∈{0,6} safe.
- `q(λk d4)=k` model: {k,k+2,4x+4k,4x+4k+1,2k−y'} = case66b_good.
### λk model (a): `q(λk·A) = {k,k+2,2k−x,2k−x+1,4y+4k}` with x=ẽ(d2,d4),
y=ẽ(d2,d5) — all Λ₀-invariant; case66a_bad contrapositive gives k∈{1,2,3}.

## Stage 1 DONE — `case66_finish` compiles (0 errors)
- Added: `apLen_pair_le2` (decide), `apLen_pair_of_qe`, `apLen_singleton_le1`,
  `apLen_pos_of_nonempty`, `rel_same_of_mul`, `case66_finish` (~line 517-815).
- `case66_finish`: lam₁ with both pair `q(e)∈{0,6}` → apLen≤2 bounds →
  lemma5 (direct on (X1,X2,X4) when X2≤X1, rotated (X2,X4,X1) with s''=2s'
  when X1<X2) → exists_lambda0_of_shift → Λ₀·lam₁.
- Gotchas recorded: (a) `ring`/`ring_nf` do NOT reduce `x*8 = x` in ZMod 7 —
  use `rw [← mul_assoc, show (4:ZMod 7)*2 = 1 from by decide, one_mul]`;
  (b) `{x}` needs `Finset.mem_singleton_self` not `mem_insert_self`;
  (c) `set s'' := 2*s'` folds `2*s'` in earlier haves — reuse it;
  (d) `hs0 h0 : False` ≠ goal — use `absurd h0 hs0`.

## 2026-10-08 — `case66_top` implementation design (this agent, session start)

Target: `case66_top` (signature in task). File at 1006 lines, compiles clean.
Prior agent landed `case66_finish` (line 770): `(lam₁, q(e12'),q(e34')∈{0,6})`
→ lemma5+Λ₀ finish. My job: produce the lam₁ for the `ν(e12)=ν(e34)=m` branch.

### Verified model derivation (re-derived from paper text bs7-ejc.txt:784-798)
* Orientation: within-pair swaps → `r12,r34 ∈{1,2,4}` (`eMod7_same_swap` +
  `neg_resid`; `r∉{1,2,4} ⇒ −r∈{1,2,4}` decide).
* `r12 = r34`: scalar `c` via `exists_top_scalar_set` (t=6) → `q(c·e12)=q(c·e34)=6`
  → `case66_finish`. EASY.
* `r12=2r34` (case a): scalar `c` (t=1 on e34) → `e12'=2·7^m`, `e34'=7^m`.
  `r34=2r12` (case b): scalar `c` (t=1 on e12) → `e12'=7^m`, `e34'=2·7^m`.
  (All (r12,r34)∈{1,2,4}² with r12≠r34 fall in a or b — checked: (1,4)=a,
  (2,1)=a, (4,2)=a; (1,2)=b,(2,4)=b,(4,1)=b.)
* λ₀-normalization makes `q(λ₀·L1·c·d_anchor)=0`; λk `=1+jk·7^m`,
  `jk = k·r(anchor)⁻¹`. Models (Λ₀ preserves top residues + etd7):
  - (a) anchor d2: `q(A1)={k,k+2}`, `q(A2)={2k−x,2k−x+1}`, `q(d5)=4y+4k`,
    `x=ẽ(d2,d4)` (twoX), `y=ẽ(d2,d5)` (twoY) — matches `case66a_bad`.
  - (b) anchor d4: `q(A2)={k,k+2}`, `q(A1)={4a+4k,4a+4k+1}`, `q(d5)=2k−b`,
    `a=ẽ(d2,d4)`, `b=ẽ(d4,d5)` — matches `case66b_good`.
* KEY SIMPLIFICATION (re-derived): Λ₁ ε-machinery via
  `exists_multLow_one_set_seven'` — sets `digit7(m−1)(λ·d) = w` directly
  (qdig7_seven bridge), NO j-computation needed.
  **Magic-w**: `w := 4·ε₂ + 2·ε₁` realizes `(σ24',σ25') = (ε₁,ε₂)` for ALL
  carry params `cm5,cm2∈{0,1}` (verified by hand: ε=(0,0)→w=0→σ=(0,0);
  (1,0)→w=2→σ=(1,0); (0,1)→w=4→σ=(0,1); (1,1)→w=6→σ=(1,1)).
  Provable by `interval_cases` — no 112-case decide needed.
* σ-linkage (NEW unified lemma `etd_combo_of_low`): for
  `e=(a·u+N−v)%N`, a∈{1,2}, `e%7^m=0`: `a·q(u)−q(v) = e/7^m − ⌊a·(u%7^m)/7^m⌋`.
  Covers same (a=1, σ=0), twoX (a=2,u=x), twoY (a=2,u=y).
* linkage for corner: `e25` twoY `e%7^m=0` → `x%7^m = (2·(y%7^m))%7^m`
  (`low_link_twoY`) → `w2Z = (2·w5Z+cm5)%7`, `u2Z=(2u5)%7^{m−1}`.
* lemma7_i must be re-proved with EXPLICIT `1+k·7^{m−ν}` multiplier
  (`exists_multLow_etd7_avoid`) — ∃-form hides the Λ structure needed for
  `lambda_low_top_resid` residue preservation.

### Sub-case tree (case a)
* `0<ν(E24)<m`: lemma7_i' on (D2,D4) X={4,5,6} → x'∉{4,5,6} → ¬bad.
* `E24=0∨ν=m` (R24:=E24/7^m ∈{0..6}):
  - `R24∈{1,2,3}`: x'∈{R24−1,R24}⊆{0,1,2,3} auto-safe.
  - `R24∈{0,4,5,6}`: `0<ν(E25)<m` → lemma7_i' on (D5,D2) [twoX since
    r(D2)=2·r(D5)]: X={2,4} (R24∈{4,5}) or X={4,6} (R24∈{0,6}) — {2,4,6}
    has apLen 5, CANNOT be covered by lemma7_i (needs ≤4)!
    else (E25=0∨ν=m) → corner: eps at (R24,R25) → w=4ε₂+2ε₁ →
    `(x',y')=(R24−ε₁,R25−ε₂)∉bad66a`.
* (b): `0<ν(E24)<m`→lemma7_i' X={2,4}; `E24=0`→a'∈{0,6}; `ν=m`:
  R24∈{1,6} auto; {2,4}→σ'=1 (w=4); {3,5}→σ'=0 (w=0).

### New private lemmas (to write, ~in order)
`qdig7_top_resid`, `etd_combo_of_low`+3 instantiations, `two_mul_low_div`,
`low_link_twoY`, `multLow1_mod_low`, `sigma_eps_magic` (interval_cases),
decide-tables (neg_mem124, case66a_auto/safeA/safeB/notbad_x, case66b_auto),
`exists_multLow_etd7_avoid` (lemma7_i copy, explicit λ),
`case66a_finish`, `case66b_finish`, `case66a`, `case66b`, `case66_top`.

## ORCHESTRATOR NOTE (integration contract) — `case66` main theorem

Orchestrator is writing `case66` (public, hc66-shaped) taking a trailing
hypothesis parameter `hc66top` for the delicate branch — PLEASE SHAPE
`case66_top` to exactly this signature so `case66 hm ... hc66top := case66_top hm` plugs in:

```lean
∀ {d1 d2 d3 d4 d5 : ℕ}, d1 ≠ d2 → d3 ≠ d4 →
  0 < d1 → 0 < d2 → 0 < d3 → 0 < d4 → 0 < d5 →
  padicValNat 7 d1 = 0 → padicValNat 7 d2 = 0 →
  padicValNat 7 d3 = 0 → padicValNat 7 d4 = 0 → padicValNat 7 d5 = 0 →
  ∀ {s' : ZMod 7}, s' ∈ ({1, 2, 4} : Finset (ZMod 7)) →
  runit7 d1 = s' → runit7 d2 = s' →
  runit7 d3 = 2 * s' → runit7 d4 = 2 * s' → runit7 d5 = 4 * s' →
  eMod7 m d1 d2 ≠ 0 → eMod7 m d3 d4 ≠ 0 →
  padicValNat 7 (eMod7 m d1 d2) = m →
  padicValNat 7 (eMod7 m d3 d4) = m →
  ∃ lam₁ : ℕ, ¬ 7 ∣ lam₁ ∧
    qdig7 m (eMod7 m (lam₁ * d1) (lam₁ * d2)) ∈ ({0, 6} : Finset (ZMod 7)) ∧
    qdig7 m (eMod7 m (lam₁ * d3) (lam₁ * d4)) ∈ ({0, 6} : Finset (ZMod 7))
```

i.e. `case66_top {m} (hm : 2 ≤ m) : <the ∀-type above>` (element-level
hypotheses; `m` explicit, `d`s implicit). If your version differs, keep
your own statement and we will write a 10-line adapter — do NOT rewrite
`case66` yourself; the orchestrator owns the main theorem (inserted
before the `§4` comment).

## 2026-10-08 (session 3) — helpers compile; hc66top contract FALSE → reshape to good7

* `Case66.lean` now compiles **0 errors** (~1980 lines) with all helper
  machinery in place: `etd_combo_of_low` (+3 instantiations `etd7_same/twoX/
  twoY_of_low`), `two_mul_low_div`, `low_link_twoY`, `multLow1_mod_low`,
  `sigma_eps_magic`, `sigma_single`, `neg_mem124`, `case66a_*_dec`×4,
  `case66b_*_dec`×3, `exists_multLow_etd7_avoid`, `qdig7_top_resid`.
* `case66` (orchestrator's) compiles taking `hc66top` hypothesis.
* **COUNTERMODEL — hc66top conclusion false for r12≠r34**: for pure-top
  `e12 = r12·7^m`, `e(λd1,λd2) = (λ·e12)%N` (`eMod7_smul`), so
  `q(e(λd1,λd2)) = runit7(λ)·r12`. `runit7(λ)` unit ⇒ `∈{0,6}` iff `=6`.
  Both pairs ⇒ `runit7 λ = 6·r12⁻¹ = 6·r34⁻¹` ⇒ `r12 = r34`. For
  `r12 ≠ r34` NO `lam₁` achieves both `qdig ∈ {0,6}` — the paper's actual
  argument there produces `good7` directly via the λk/avoids06 mechanism
  (`case66a_bad`/`case66b_good`), NOT the qdig-{0,6} intermediate.
* **Reshape (countermodel-justified, AGENTS.md frozen-statement rule)**:
  `hc66top` conclusion → `∃ lam, ¬7∣lam ∧ good7 m lam {d1,…,d5}`;
  `case66` top branch calls it directly on the main goal (bypasses
  suffices/case66_finish). `case66_top` proves exactly that.
* Verified model (case a, normalized e12'=2·7^m, e34'=7^m, anchor d2):
  `q(λkλ₀d2)=k`, `q(λkλ₀d1)=k+2`, `q(λkλ₀d4)=2k−x`, `q(λkλ₀d3)=2k−x+1`,
  `q(λkλ₀d5)=4y+4k` — `x=ẽ(d2,d4)` twoX, `y=ẽ(d2,d5)` twoY (`r(d2)=2r(d5)`
  since 2·4s=8s=s!). Case b mirrored with anchor d4.
* ε-corner: uniform Λ₁ `λ_w`, `w=digit_{m−1}(λd5)` settable via
  `exists_multLow_one_set_seven'` on `7·d5` + `qdig7_seven`;
  `σ25'=(2w+cm5)/7=ε₂`, `w2=(2w5+cm5)%7`, `σ24'=(2w2+c2')/7=ε₁` via
  `sigma_eps_magic` — all carry params cm,c2'∈{0,1} covered.
