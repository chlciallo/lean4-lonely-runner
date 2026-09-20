# lrc7-sec6-next.md — B1/B2 shared-lemma layer for `|A|=5, m≥2` (BS7 §6)

Agent: continuation after `Case5mBase.lean` (B0) + `Carry.lean` (§3.7 engine).
Contract: verify B0 build; implement next bounded piece in NEW file
`Research07/LRC7/Case5mCases.lean` (imports `Case5mBase` + `Carry`).
Do NOT modify `Case5mBase.lean` except build fixes.

## 2026-10-02 — TASK 1 verification result

- `python _dev/memwatch.py 12288 _dev/memlog/c5mb_1.csv -- lake env lean
  Research07/LRC7/Case5mBase.lean` → **exit 0, 66s, peak 9933MB**.
- Zero `sorry`/`admit`/`native_decide`/`unsafe` (grep; only "admits" in a
  comment at line 1313).
- All 6 `#print axioms` at file tail → `[propext, Classical.choice, Quot.sound]`
  for `exists_lambda0_of_shift`, `qdig_eMod_sub_etd7_two`, `filtered7_mod7`,
  `case63_table`, `case66b_good`, `case61_dichot`.
- Residual warnings only: `if_pos`/`if_neg` deprecation lints, one unused
  `hm` linter hint at L222 (`exists_lambda0_of_shift`). **No errors.**
- VERDICT: Case5mBase.lean (1407 ln) is GREEN and complete w.r.t. its spec
  scope (B0 = §3.1/§3.2/§3.4/§3.8 + §5.1 + §5.2 decides).

## Spec-position assessment (from `_reports/lrc7-sec6-spec.md` §8)

Remaining after B0, in dependency order:
| Unit | Content | Status |
|---|---|---|
| B1 lemma7 | `lemma7_i`, `lemma7_ii` (+ 7d machinery — DONE in Carry.lean) | **this agent** |
| B2 lemma9/10/11 | 3-compression + numbering | pending |
| C1–C6 | case61…case66 | pending (need B0–B2) |
| C7 | `lrc7_case5m` assembly + `hc6` sign-flip leaf | pending |

`Carry.lean` (GREEN, 334 ln) already has `digit7_multLow_one`,
`exists_multLow_one_set_seven'`, `qdig7_seven`, `qdig7_two_eq_smul`,
`qdig7_two_eq_smul_add_one` — the whole §3.7 engine. So B1 reduces to the
two `lemma7` theorems + small residue helpers.

## lemma7_i design (paper Lemma 7(i), verified against ejc.txt:528-553)

```lean
theorem lemma7_i {m : ℕ} {d d' : ℕ}
    (hd : padicValNat 7 d = 0) (hd' : padicValNat 7 d' = 0)
    (hpos : 0 < d) (hpos' : 0 < d')
    (hrel : runit7 d' = 2 * runit7 d)
    (hν : 0 < padicValNat 7 (eMod7 m d d'))
    (hνm : padicValNat 7 (eMod7 m d d') < m)
    {X : Finset (ZMod 7)} (hX : apLen X ≤ 4) :
    ∃ lam : ℕ, ¬ 7 ∣ lam ∧ etd7 m (lam * d) (lam * d') ∉ X
```
Proof (paper): pick `x ∉ X+{0,1,2}` (`exists_not_mem_three hX`), set
`λ = 1+k·7^{m−h}` (`h = ν(e)`) with `q(λe) = x−1` (`exists_multLow_set_qdig`).
Then `eMod7 m (λd)(λd') = (λe)%N` (`eMod7_mul`, needs `runit7 λ = 1` =
`runit7_multLow`), `q(λe) = q((λe)%N) = x−1` (`qdig7_congr`+`Nat.mod_mod`),
`ẽ ∈ q(λe)−{0,1,6} = {x−1,x−2,x} ⊆ Xᶜ` via `qdig_eMod_sub_etd7`
(unconditional). `¬7∣λ` = `multLow_not_dvd hνm`.

## lemma7_ii design (paper Lemma 7(ii), m ≥ 2 — the Λ₁·7d trick)

```lean
theorem lemma7_ii {m : ℕ} (hm : 2 ≤ m) {d d' : ℕ}
    (hd : padicValNat 7 d = 0) (hd' : padicValNat 7 d' = 0)
    (hpos : 0 < d) (hpos' : 0 < d')
    (hrel : runit7 d' = 2 * runit7 d)
    (hν : padicValNat 7 (eMod7 m d d') = m)
    {X : Finset (ZMod 7)}
    (hr : runit7 (eMod7 m d d') ∉ X ∪ X.image (· + 1)) :
    ∃ lam : ℕ, ¬ 7 ∣ lam ∧ etd7 m (lam * d) (lam * d') ∉ X
```
Paper (ejc.txt:546-553): choose `λ ∈ Λ₁` with `q(λ·7d) = 6` ⇒
`q(λ·2d) = 2q(λd)+1` (`qdig7_two_eq_smul_add_one`, Carry.lean).
Then `ẽ(λd,λd') = 2q(λd)−q(λd')` (twoX preserved, `runit7 λ = 1`); apply
`qdig_eMod_sub_etd7_same` to the SAME-class pair `(2λd, λd')`
(`r(2λd) = 2r(d) = r(λd')`): `e(2λd,λd') = λe ≡ e` (verbatim,
`residN_multLow7`, `ν(e) = m > 1`) ⇒ `q(e) − (q(2λd)−q(λd')) ∈ {0,6}` ⇒
`r(e) − ẽ − 1 ∈ {0,6}` ⇒ `ẽ ∈ {r(e)−1, r(e)} ⊆ Xᶜ` by `hr`
(`r ∉ X` and `r−1 ∉ X` ⟸ `r ∉ X+1`).
Helpers needed: `qdig7_eq_runit7_of_top` (`ν(x)=m ⇒ qdig7 m x = runit7 x`),
`eMod7_two_mul_left` (`eMod7 m (2x) y = eMod7 m x y` when `r(y)=2r(x)`),
private `eMod7_zmod_cast` clone (private in Case5mBase — re-implement).

## API notes for Case5mCases.lean

- `eMod7_zmod_cast` is `private` in Case5mBase → local copy needed.
- `exists_multLow_one_set_seven' {m d} (hm : 0 < m) (hd : ν(d)=0) (hd0 : 0<d)
  (c)` gives `∃ k<7, qdig7 m ((1+k*7^{m-1})*(7*d)) = c` (Carry.lean).
- `qdig7_two_eq_smul_add_one {m x} (hm : 0<m) (h : qdig7 m (7*x) = 6) :
  qdig7 m (2*x) = 2*qdig7 m x + 1` (Carry.lean).
- `runit7 2 = 2`: via `padicValNat.eq_zero_of_not_dvd (by decide : ¬7∣2)`.
- `residueRelOf (2*λd) (λd') = same` needs `r(λd')=2r(d)=r(2λd)` and
  `r(d)≠0` (via `runit7_mul`, `runit7_multLow`, `runit7_ne_zero`).

## 2026-10-02 — B1 BUILD RESULT: `Case5mCases.lean` GREEN (lemma7_i + lemma7_ii)

File: `Research07/LRC7/Case5mCases.lean`, 301 lines.
Build: `python _dev/memwatch.py 12288 _dev/memlog/c5mc_5.csv --
lake env lean Research07/LRC7/Case5mCases.lean` → **exit 0, 40.1s,
peak 8958MB** (cap 12288MB). Residual warnings only: `if_pos`/`if_neg`
deprecation lints, unused-var hints on paper-matching hyps.

Declarations (line numbers):
- `runit7_two` (L29), `eMod7_zmod_cast` private clone (L38),
  `eMod7_two_mul_left` (L69), `qdig7_eq_runit7_of_top` (L106).
- `lemma7_i` (L131): `0 < ν(e) < m` branch — Λ_h shift via
  `exists_multLow_set_qdig` + `qdig_eMod_sub_etd7`, avoids `apLen X ≤ 4`.
- `lemma7_ii` (L197): `ν(e) = m` branch — Λ₁·7d trick via
  `exists_multLow_one_set_seven'` + `qdig7_two_eq_smul_add_one` +
  `qdig_eMod_sub_etd7_same` on the `(2λd, λd')` same-class pair.

Axiom gate (`#print axioms` at tail, L298-301): **all four**
`[propext, Classical.choice, Quot.sound]` — `lemma7_i`, `lemma7_ii`,
`eMod7_two_mul_left`, `qdig7_eq_runit7_of_top`.
Forbidden constructs: zero `sorry`/`admit`/`native_decide`/`unsafe`.

### Build errors fixed this session (logged in `_dev/failures.md`)

1. `Nat.ModEq` is not a `%`-equality — `rw` for `eMod7 % N` found no
   occurrence; use the relation or convert via its `%`-def first.
2. `pow_succ' 7 m` yields `7^(m+1) = 7*7^m`; target wanted `7^m*7` —
   add `mul_comm`.
3. `padicValNat.zero` deprecated → direct zero-val rewrite.
4. `ring` does not discharge `etd7 = -2 + x` nor `-7 + x = x` in ZMod 7
   (literal `7` not folded to `0`) — rewrite `(7 : ZMod 7) = 0` via
   `ZMod.natCast_self 7` first.
5. `hx 0` produces `x - 0 ∉ X` — `simpa`/`sub_zero` before use.

## Remaining §6 scope (for orchestrator split) — in dependency order

| Unit | Content | Notes / API already available |
|---|---|---|
| B2 lemma9_i | 3 same-class elems, `ν(x)≠ν(y)` ⇒ mult with `q(λeij)∈{0,6}` + `apLen(λB)≤2` | Needs NEW `qdig7_sub_resid` (borrow bound on wrapped residue diff — private copies of `residue_decomp`/`mul_pow_add_div`/`qdig7_eMod_of`/`natCast_sub_add` since Case5mBase's are private), `eMod7_smul` (scalar c, via `eMod7_zmod_cast`+branch preservation), `padicValNat((c·x)%N)=ν(x)` bookkeeping (`padicValNat_mul_seven`+`padicValNat_eq_of_mod`), `exists_top_scalar_set` (ν=m edge: pre-scale `c=6·r(e)⁻¹`), `filtered7_mod7`, `remark8_i_int`+`remark8_i`. Triple must be ordered so `b3` = shared element (`x=e(b1,b3)`, `y=e(b2,b3)`, `ν(x)≠ν(y)`). |
| B2 lemma9_ii | same-level `ν(x)=ν(y)<m` 3-compression | same machinery + Λ_ν-set digit set |
| B2 lemma10 | `ν(e21)>ν(e31)` dichotomy / numbering | case-split, `e23=e21+e13` valuation dominance |
| B2 lemma11 | labeling / `r(e)` avoidances | finite labeling decides |
| C1 `case61` | `case61_dichot` consumed | B0 has the decides |
| C2 `case62` | | |
| C3 `case63` | `case63_table`/`case63_table_rescue` + 7d carry (`digit7_multLow_one`) | |
| C4 `case64` | | |
| C5 `case65` | absModN inequalities | |
| C6 `case66` | `case66b_good` + bad-pair decides + epsilon tricks | |
| C7 `lrc7_case5m` | assemble `hc6` leaf + `normU7` sign-flip | `NormU.lean`: `normU7_absModN`, `normU7_pos`, `normU7_not_dvd`, `normU7_padic`, `normU7_runit` |

## Structured summary for orchestrator

- **B0** `Case5mBase.lean` — verified GREEN, axioms clean.
- **B1** `Case5mCases.lean` — **DONE GREEN**: `lemma7_i`, `lemma7_ii` +
  helpers; axioms `[propext, Classical.choice, Quot.sound]`; peak 9.0GB;
  no forbidden constructs.
- **Next bounded unit**: `lemma9_i` needs the largest new machinery
  (`qdig7_sub_resid` + `eMod7_smul` + top-scalar ν=m edge). Recommend
  splitting B2 as `lemma9_i` alone (one agent), then `lemma9_ii +
  lemma10 + lemma11` (one agent), before C1–C6.
- Do NOT modify `Case5mBase.lean` (frozen, GREEN); new lemmas for B2
  belong appended to `Case5mCases.lean` (its `eMod7_zmod_cast` private
  clone is reusable) or a new `Case5mCases9.lean` if file size/memory
  becomes an issue (Case5mCases already ~9GB peak at 301 lines).
