# lrc7-sec6-lemma9ip.md — Lemma 9(i') boundary variant (`Case5mL9b.lean`)

Incremental per `_reports` protocol. Task: prove `lemma9_i'` in NEW file
`Research07/LRC7/Case5mL9b.lean` — the `ν(e)=m` boundary variant of
`lemma9_i` (Case5mL9.lean, DONE/GREEN) with pair condition relaxed
`{0,6}` → `{0,1,6}` and no `hνm` hypothesis.

---

## 2026-10-03 — recon (file layout + API verification)

Read in full:

- `Research07/LRC7/Case5mL9.lean` (550 ln): `lemma9_i` proved with
  `hνm : νx < m ∧ νy < m` giving all-pairs `qdig ∈ {0,6}` + `apLen ≤ 2`.
  `eMod7_smul` is PUBLIC (line 230, `(hc : runit7 c ≠ 0)`). Private
  helpers there (must clone): `mul_pow_add_div`, `residue_decomp`,
  `natCast_sub_add`, `eMod7_zmod_cast`, `rel_same`,
  `eMod7_zmod_cast_same`, `qdig7_zero`, `eq_six_of_not_mem_five`,
  `qdig7_sub_resid`, `qdig_smul_eMod_eq`. Proof pattern per pair:
  `eval u v A B` = `eMod7_mul/smul` → `qdig7_congr` → `qdig_smul_eMod_eq`
  → `qdig7_sub_resid` borrow formula; then `ite_eq_left/right` + `decide`.
- `Discrete.lean` (423 ln): `residN_multLow7` (line 177:
  `(hjm : j < m) (hx : j < padicValNat 7 x) → (1+k*7^{m-j})*x % 7^{m+1} = x % 7^{m+1}`),
  `qdig7_multLow` (208), `qdig7_multTop` (246), `qdig7_eq_cast_div` (280),
  `qdig7_add_one` (289), `cycIv` (360), `apLen`, `apLen_le_iff` (387).
- `Case5mBase.lean`: `not_dvd_of_mem_multLow7` (70), `mem_multLow7` (53),
  `enu7_le_of_ne` (115 — note: on `eMod7 m x y ≠ 0`, gives `enu7 ≤ m`;
  `enu7 m x y = padicValNat 7 (eMod7 m x y)`), `exists_multLow_set_qdig`
  (509: `∃ k<7, qdig7 m ((1+k*7^{m-j})*x) = c`), `residN_top` (524),
  `exists_top_scalar_set` (546: `∃c, 0<c<7 ∧ (c*x)%N = t.val*7^m ∧
  qdig7 m (c*x) = t`, needs `(ht : t ≠ 0)`), `runit7_mul` (572),
  `runit7_eq_one_of_mod7` (597), `eMod7_mul` (646), `filtered7_mod7` (691),
  `remark8_i_int` (1056), `qdig_eMod_sub` (441).
- `Differences.lean`: `eMod7` def (55 — residue mod 7^{m+1}, if-chain on
  `runit7` ratios), `residueRelOf` (48), `residueRelOf_eq_same` (105),
  `multLow_not_dvd` (143), `runit7_multLow` (151), `runit7_eq_of_mod` (284).
- `Compress.lean`: `remark8_i` (228: `x−y ∈ {0,1,6}` diffs → `apLen ≤ k+1`),
  `mem_cycIv` (73), `apLen_le_seven` (145).
- `Filtering.lean`: `qdig7_congr` (31), `padicValNat_mul_seven` (37).
- Spec erratum `_reports/lrc7-sec6-spec.md` lines 948–1043: exact
  `lemma9_i'` statement; `{0,1,6}` is negation-closed and verified
  sufficient; `apLen ≤ 2` must NOT go via `remark8_i_int` (needs `{0,6}`)
  — prove digit structure directly (`q(λb3)=a`, `q(λb1)=a+1`,
  `q(λb2) ∈ {a,a+1}`).

## Proof plan (from contract, math verified)

`by_cases hνm : νx < m ∧ νy < m`:
1. `<m` case: `lemma9_i` → `{0,6} ⊆ {0,1,6}` (decide).
2. else: `enu7_le_of_ne` gives `νx,νy ≤ m`; `hν` distinct + not-both-`<m`
   ⇒ exactly one `= m`. Core boundary lemma proved once for
   `ν(e(b1,b3)) = m ∧ ν(e(b2,b3)) < m`; mirror case via swapped triple
   `(b2,b1,b3)`, set equality by `Finset.insert_comm`.

Core lemma (`x` level m, `y` level `j < m`):
- `exists_top_scalar_set hxν hx0 (t:=1)` → `c ∈ (0,7)`, `(c*x)%N = 7^m`,
  `q(c*x)=1`; `¬7∣c`.
- `exists_multLow_set_qdig hjm (ν(c*y)=j) _ 0` → `k<7`,
  `q((1+k*7^{m-j})*(c*y)) = 0`; `lam₂ := 1+k*7^{m-j}`.
- `residN_multLow7 hjm (j < ν(c*x)=m)` → `(lam₂*(c*x))%N = (c*x)%N = 7^m`.
- `lam := lam₂*c`; `¬7∣lam` via `Nat.Prime.dvd_mul`; `runit7 lam ≠ 0`
  via `runit7_mul` + `runit7_multLow` + `runit7_ne_zero`.
- `f := (lam₂*(c*y))%N`; `0 < f < 7^m` (`q=0` ⇒ `f<7^m`; `f≠0` since
  `ν(lam₂*c*y)=j<m`). `(lam*y)%N = f`, `(lam*x)%N = 7^m`.
- Pairs via `eval` (same as L9 but `eMod7_smul hlamr`):
  e13: A=lam*x,B=0 → 1−0−0=1; e31: A=0,B=lam*x, borrow `0<0` F → 6;
  e23: A=lam*y,B=0 → 0; e32: A=0,B=lam*y, borrow `0<f` T → 6;
  e12: A=lam*x,B=lam*y, borrow `0<f` T → 1−0−1=0; e21: f<0 F → 0−1=6;
  diag 0.
- `apLen ≤ 2`: `q(λb3)=:a`; `λb1 ≡ λb3 + 7^m` → `q = a+1` (helper
  `qdig7_add_pow`); `λb2 ≡ λb3 + f` → `q = a + carry`, `carry =
  (w%7^m + f)/7^m ∈ {0,1}` (clone `add_div_carry7`) → `q−a ∈{0,1}`,
  `(q−a).val < 2` → `mem_cycIv`, `apLen_le_iff` at L=2.

Compile gate: `python _dev/memwatch.py 12288 _dev/memlog/c5l9b.csv --
lake env lean Research07/LRC7/Case5mL9b.lean`; `#print axioms lemma9_i'`
must show only `[propext, Classical.choice, Quot.sound]`.

---

## 2026-10-05 — implementation + build log

File written: `Research07/LRC7/Case5mL9b.lean` (~644 ln), imports
`Research07.LRC7.Case5mL9`. Private clones (same names as L9):
`mul_pow_add_div`, `residue_decomp`, `natCast_sub_add`,
`eMod7_zmod_cast`, `rel_same`, `eMod7_zmod_cast_same`, `qdig7_zero`,
`eq_six_of_not_mem_five`, `qdig7_sub_resid`, `qdig_smul_eMod_eq`;
new boundary helpers `add_div_carry7`, `qdig7_add_pow`,
`resid_lt_of_qdig7_zero`, `mod_pos_of_val_lt`; core `lemma9_ip_aux`
(private) + `theorem lemma9_i'` + `#print axioms lemma9_i'`.

Build 1 (FAIL, 3 errors — ledger `_dev/failures.md` 2026-10-05):

1. L442 `hycast` pattern `↑y` not found — `set lam := lam₂*c` left `lam` a
   *let-var*, so `↑lam` matched `Nat.cast_mul`'s `↑(?a*?b)` (via let-value
   `lam₂*c`) and stole one of the three `Nat.cast_mul` rewrites, leaving
   `↑(lam*y)` unrewritten. FIX: `clear_value lam` (line 335) — `lam`
   becomes an opaque fvar; `↑lam` no longer matches cast patterns.
   (`set`-bound `x`,`y`,`f` are safe: their let-values' heads are
   `eMod7`-def/`%`, not `*`.)
2. L535 `hcarry` unsolved — `add_div_carry7` emits `(a%c + b%c)/c`; needed
   `Nat.mod_eq_of_lt hf_lt` to reduce `f % 7^m → f` (only `f/7^m → 0` was
   rewritten). FIX: `rwa [Nat.div_eq_of_lt hf_lt, add_zero,
   Nat.mod_eq_of_lt hf_lt] at h`.
3. L577 `ZMod.val_natCast` unmatched — `(((…)/7^m) : ZMod 7)` ascription
   elaborated the WHOLE div-expression at `ZMod 7` (coercion pushed onto
   `↑lam`, `↑b3`, `↑f`; `%`,`/` became ZMod ops), so `(carryexpr).val` was
   not `Nat.cast`-form. FIX: `set carry := ((lam*b3)%7^m+f)/7^m` (ℕ var)
   and write `(carry : ZMod 7)`.

Build 2 — **GREEN**, exit 0, 30.2 s, peak 8976 MB (cap 12288),
`_dev/memlog/c5l9b.csv`. `#print axioms lemma9_i'` →
`[propext, Classical.choice, Quot.sound]` exactly (no `sorryAx`).
`grep sorry|admit|native_decide|unsafe` → only doc-comment word "admit".

## Final structured summary (for orchestrator)

- **Deliverable**: `Research07/LRC7/Case5mL9b.lean` — `theorem lemma9_i'`
  with the user-specified signature (`hpos`, `hunit`, `hsame`, `hν`
  distinct-valuations, `he` nonzeros; conclusion `∃ lam, ¬7∣lam ∧
  all-pairs qdig ∈ {0,1,6} ∧ apLen ≤ 2`). No `hνm` hypothesis.
- **Status**: GREEN. Axioms `[propext, Classical.choice, Quot.sound]`.
  No sorry/admit/native_decide/unsafe. Compile 30 s / 9.0 GB.
- **Structure**: `by_cases` on `νx<m ∧ νy<m`. Below-`m` branch calls
  `lemma9_i` verbatim and embeds `{0,6} ⊆ {0,1,6}` via a `decide`d
  `hsub`. Boundary branch: `enu7_le_of_ne` caps both valuations at `m`;
  `hν` + `¬hνm` forces exactly one `= m`. `lemma9_ip_aux` (private,
  ~300 ln) proves the `νx=m ∧ νy<m` orientation; mirror case applies it
  to `(b2,b1,b3)` and restores the set via `Finset.insert_comm`.
- **Aux construction**: `c ∈ {1..6}` with `(c*x)%N = 7^m`, `q(c*x)=1`
  (`exists_top_scalar_set`, `t=1`); `lam₂ = 1+k·7^{m−j} ∈ Λ_j` with
  `q(lam₂*(c*y)) = 0` (`exists_multLow_set_qdig`); `lam = lam₂*c`
  (opaque via `clear_value`). `(lam*x)%N = 7^m` by `residN_multLow7`;
  `f := (lam*y)%N ∈ (0,7^m)`. Nine ordered pairs via `eval`/`hcast`
  machinery cloned from L9 → digits `{0,1,6}`.
- **apLen route**: direct digit structure (NOT `remark8_i_int`):
  `a := q(λb3)`, `q(λb1) = a+1` (`qdig7_add_pow`), `q(λb2) = a+carry`
  with `carry = ((λb3)%7^m+f)/7^m ≤ 1` (`add_div_carry7` clone) →
  image ⊆ `cycIv a 2` (`mem_cycIv`) → `apLen_le_iff` at `L=2`.
- **Files touched**: `Research07/LRC7/Case5mL9b.lean` (new),
  `_dev/failures.md` (1 line), this report. Protected files untouched.
- **Caveats**: `hunit` is unused by the boundary aux (level-0 units are
  only needed by `lemma9_i`'s `filtered7` route); kept in signature per
  spec. `{0,6}` all-pairs is genuinely false at the `ν=m` edge —
  the relaxed `{0,1,6}` is the correct statement.
