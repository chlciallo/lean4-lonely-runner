# lrc7-case5mbase.md — B0 helper layer for `|A|=5, m≥2` (BS7 §6)

Task: create `Research07/LRC7/Case5mBase.lean` (imports Compress + Differences).
No existing file may be modified. Deliverables per spec §3 (excl. §3.3/§3.7),
§5.1, §5.2. Build under `python _dev/memwatch.py 12288 _dev/memlog/case5mbase_N.csv`.

## Plan / signature decisions (recorded up front)

- `enu7` abbrev = `padicValNat 7 (eMod7 m x y)`; λ-index helpers:
  `mem_multLow7`/`eq_one_add_of_mem_multLow7`/`not_dvd_of_mem_multLow7`,
  `eMod7_multLow_low`, `enu7_multLow_low`, `enu7_le_of_ne`.
- `qdig7_smul_carry`: spec's `∈ (Finset.range c).image` is FALSE at `c = 0`
  (range 0 = ∅). Added `hc0 : 0 < c`; paper's claim is `c ≥ 1` anyway.
  Provide both `.val < c` (`qdig7_smul_carry`) and range-membership form.
- `filtered7_mod7`: must re-run the `filtered7` induction (the produced lam is
  existential-opaque) — copy proof with `lam % 7 = 1` conjunct in `key`.
- `exists_lambda0_avoid`/`exists_lambda0_of_shift`: need `hm : 0 < m`,
  `hunit : ∀ d ∈ A, padicValNat 7 d = 0` (Λ₀ shift identity `qdig7_multLow`
  needs level 0), `hs : s ≠ 0` (for `t·s⁻¹`). Documented additions, not
  weakenings (conclusions unchanged).
- `qdig7_lambda0`: spec omits `0 < m`; identity holds at `m = 0` too
  (`qdig7 0 y = ↑y`); prove both cases — no hypothesis added.
- `case63_table`: encoded as `∀ δ ∈ {0,1}, ∃ q45, ∀ b12 b13 b23 ∈ {0,1},
  b13 = b12+b23−δ → apLen {0,q45+e+b13, 3(u−3(q45+e))+b23} ≤ 2 ∨ (≤3 ∧ q45 ∈ {0,6})`.
  (e,u) = (0,3) excluded (paper's ×2-rescue cell; separate `case63_table_rescue`).
  Borrow-coupling is ESSENTIAL: (e,u)=(1,4),δ=0 free-quantification fails
  ({0,6,1} apLen 3 with q45=5 ∉ {0,6}); also (1,4) needs different q45 per δ
  (5 for δ=0, 6 for δ=1) → ∃ must sit inside ∀ δ.
- `absModN` suite at scale `N = 7^{m+1}`: `|x| < 7^m ↔ q ∈ {0,6}` needs
  `ν(x) < m` (boundary `6·7^m` excluded by `f ≠ 0`); `|x| ≥ 2·7^m ↔ q ∈ {2,3,4}`
  needs `ν < m` on the ⇒ side; `5N ≤ 14|x| → |2x| ≤ 2·7^m`;
  `2·7^m ≤ |x| ∧ 14|x| ≤ 5N → |3x| ≤ 7^m`; `|x| ≤ 2·7^m → q ∈ {0,1,5,6}` (ν<m).
- Private helpers `residue_decomp`, `mul_pow_add_div`, `natCast_sub_add`,
  `qdig7_eMod_of`, `div_mod_pow_cast` are `private` in Differences.lean →
  re-implemented locally under same names.

## Build log

(append after each attempt)

## Resume log

### 2026-10-02 resume (3rd agent)

**State on entry**: file at 1306 lines, does NOT compile (~40 errors; previous
agent died mid-debug). `lake env lean` via memwatch: exit 1, peak 9.4GB.

**Error inventory + planned fixes** (verified signatures via `_dev/scratch/c5mb_probe.lean`):
- L60 `mem_multLow7 (j:=0)` m-uninferable → add `(m:=m)`.
- L187 `Finset.image_id X` not a fn → `Finset.image_id'` (or `simp`).
- L254/262 `K*(2*s)`: `←mul_assoc` wrong direction → `mul_left_comm K _ s` then `hKs`.
- L444/456/501/1091 same m-inference issue → `(m:=m)`/`(x:=x)`.
- L478 base case `0+1` literal vs `1` → rw `show (0:ℕ)+1=1` + `Nat.cast_one` chain or `simp`.
- L491 `←natCast_zmod_val` rewrote inside `δ.val` → restrict via `conv_lhs` or
  rewrite RHS `Nat.cast_add` first.
- L560/805 `ZMod.val_eq_zero` needs explicit arg `(ZMod.val_eq_zero _).mp`.
- L633/639/645 `eMod7_zmod_cast`: `push_cast` distributed `↑(7^(m+1))` so `hN`
  pattern fails → use `Nat.cast_add`/`Nat.cast_mul`/`hcast`/`hN`/`ring`, no push_cast.
- L661 `eMod7_mul`: RHS is product not cast → `rw [← Nat.cast_mul] at hL` first.
- L683 `eMod7_add`: `≡` isn't `%`-form → assign ModEq to `_%_=_%_` via defeq then rw.
- L877 `Nat.mul_sub` pattern on `(e-5)*E` → restructure he4 with `Nat.mul_le_mul_left E`.
- L897-918 interval_cases branches: `rw [←e', hk, natCast_zmod_val]` dies on
  `ZMod.val k = ZMod.val k`; `subst` fails on `k = e` (let-var) → replace with
  `congrArg ZMod.val hk` + `rw [hqval]`; or `hq' : qdig = ↑e` then `rw [hq']; decide`.
- L968/978 omega can't derive `E*e` bounds (nonlinear atoms) → feed
  `Nat.mul_le_mul_left E` facts.
- L990 `right` on Eq goal (wrong disjunct order) → uniform `rw [hq']; decide`.
- L1014/1045 `Nat.mul_mod` : `a*b%n = a%n * (b%n) %n` — use
  `mul_comm` + `Nat.mul_mod` + `Nat.mod_eq_of_lt`.
- L1020 `2*r<N` unprovable (2r=N possible) → `lt_or_eq_of_le` split.
- L1129/1141/1263 decide maxRecDepth/synth → `set_option maxRecDepth 524288` +
  `synthInstance.maxSize 16384` per-theorem.
- L193 unused `hm` warning → rename `_hm` (signature unchanged).

**API confirmed**: `qdig7 m x = ↑((x % 7^(m+1))/7^m)`; `eMod7` same-branch =
`(x%N + N - y%N) % N`; `absModN x N = min (x%N) (N - x%N)` (rfl);
`(2:ZMod 7).val = 2` by rfl; `ZMod.val_eq_zero` takes explicit arg.

**Remaining spec item in B0 scope**: `case61_dichot` (§5.2, §6.1 ×3 dichotomy).
Design (verified by hand): residues `u = x%N`, q=0 → `u<E`; q=6 → `u≥6E`,
`f := u-6E = u%E`. `q(e(x,y))∈{0,6}` ⇒ `|e|_N ≤ E` ⇒ coupling `f_i ≤ f_j`
for q0-elem i, q6-elem j. `d(3u)`: q0 → `3u/E ∈ {0,1,2}` (=0 iff `3u<E`);
q6 → `4+3f/E ∈ {4,5,6}` (=4 iff `3f<E`). Split on `∃ elem, d=4`:
yes → q0 elems all `d=0` → image ⊆ {0,4,5,6} ⊆ {0,1,4,5,6};
no → image ⊆ {0,1,2,5,6}.

## Final summary

(pending)
