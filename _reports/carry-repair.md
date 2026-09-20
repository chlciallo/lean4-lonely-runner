# Carry.lean repair report

Agent: carry-repair (subagent). File owned exclusively: `Research07/LRC7/Carry.lean`.
Build: `python _dev/memwatch.py 12288 _dev/memlog/carry_N.csv -- lake env lean Research07/LRC7/Carry.lean`

## 2026-09-19 00:38 — Initial recon

- Read `Research07/LRC7/Carry.lean` (334 lines, 12 decls), error log `_dev/memlog/carry2.log`
  (~27 errors), reference file `Research07/LRC7/Discrete.lean` (defs `qdig7`, `digit7`,
  `runit7`, reference proofs `mod_pow_mul7`, `div_pow_mul7`, `qdig7_multLow`,
  `add_div_carry7` — the last is `private`, not importable).
- Root causes found in log (recurring tags):
  1. `Nat.div_add_mod a b` here proves `b * (a/b) + a%b = a` (divisor LEFT of quotient);
     `Nat.mod_add_div a b` proves `a%b + b*(a/b) = a`. File assumed quotient-left forms.
     (Lean core `Init/Data/Nat/Div/Basic.lean:241,255`.)
  2. `Nat.add_mul_div_left` needs `(a + c*b)/c` (divisor LEFT of product);
     `Nat.add_mul_div_right` needs `(a + b*c)/c` — the file consistently needed RIGHT.
     (core `Div/Basic.lean:331,336`.)
  3. `pow_succ'` (`a^(n+1) = a*a^n`) vs `pow_succ` (`a^(n+1) = a^n*a`) — two sites
     needed `pow_succ'`.
  4. `rw [← div_add_mod]` rewrites *all* `x` occurrences → must use `conv_lhs =>`.
  5. omega cannot multiply two non-literal atoms (e.g. `a*(x/a%b)`, `S%7 * 7^(m-1)`).
  6. `(e/7 : ZMod 7)` is a type error — needs `((e/7 : ℕ) : ZMod 7)` ascription
     (HDiv ℕ ℕ (ZMod 7) does not exist).
  7. `rw` instantiates once per occurrence — `ZMod.natCast_mod` fired only once;
     use `simp only` for all-occurrence rewrites.
  8. `inv_mul_cancel₀ hu` failed: `0`-instance diamond (semiring MulZeroClass `0`
     vs GroupWithZero `0` in `ZMod 7`) — `rw`-level unification can't bridge.

- **FALSE STATEMENT FOUND**: `exists_multLow_one_set_seven {m d} (hm : 0 < m)
  (hd : padicValNat 7 d = 0) (c : ZMod 7) : ∃ k < 7, qdig7 m ((1+k*7^(m-1))*(7*d)) = c`
  is FALSE for `d = 0`, `c ≠ 0`: `padicValNat 7 0 = 0` (Defs.lean:66 `padicValNat.zero`),
  and `(…)*0 = 0`, `qdig7 m 0 = 0`, so all `k` give `0 ≠ c`.
  Spec `_reports/lrc7-sec6-spec.md:320` states it WITH `(hd0 : 0 < d)` (and `hm : 2 ≤ m`) —
  the file dropped `hd0` in transcription. Per contract: corrected variant under NEW name
  `exists_multLow_one_set_seven'` (adds `hd0 : 0 < d`, keeps `0 < m` — mathematically
  sufficient and more general than spec's `2 ≤ m`). `runit7_ne_zero hd0` (Discrete.lean:61)
  gives `runit7 d ≠ 0` for free.

- Key API verified in this mathlib (grep):
  `Nat.mod_mul_right_div_self (m n k) : m % (n*k)/n = m/n % k` (core `Nat/Mod.lean:57`)
  — `mod_mul_div` is literally this lemma.
  `Nat.add_mul_div_left (x z) {y} (0<y) : (x + y*z)/y = x/y + z`;
  `Nat.add_mul_div_right (x y) {z} (0<z) : (x + y*z)/z = x/z + y`.
  `Nat.mul_le_mul_right (k) (h : n≤m) : n*k ≤ m*k` (core Basic.lean:757).
  `Nat.div_lt_iff_lt_mul (0<k) : x/k < y ↔ x < y*k` (core Div/Basic.lean:314).
  `Nat.div_eq_of_lt (a<b) : a/b = 0`; `Nat.mod_eq_of_lt`; `Nat.mul_div_mul_left (n k) (0<m) : m*n/(m*k) = n/k` (protected).
  `Nat.div_div_eq_div_mul (m n k) : m/n/k = m/(n*k)` (protected).
  `Nat.eq_zero_of_dvd_of_lt (a∣b) (b<a) : b = 0`.
  `ZMod.val_lt [NeZero n] (a) : a.val < n`; `ZMod.natCast_zmod_val [NeZero n] : (↑a.val)=a`;
  `ZMod.natCast_self (n) : (↑n : ZMod n) = 0` — NO NeZero needed;
  `ZMod.natCast_mod (a n) : ((a%n : ℕ):ZMod n) = ↑a`;
  `ZMod.natCast_eq_natCast_iff' : (↑a : ZMod c)=↑b ↔ a%c = b%c`;
  `ZMod.natCast_eq_zero_iff : (↑a : ZMod b)=0 ↔ b∣a`.
  `Inv (ZMod n)` exists for all n (Basic.lean:720) → `decide` can compute `u⁻¹`.
  `Finset.mem_insert_self a s : a ∈ insert a s`;
  `Finset.mem_singleton_self a : a ∈ {a}`; `Finset.mem_insert_of_mem : a∈s → a∈insert b s`.
  No global `Fact (Nat.Prime 7)` instance (only `fact_prime_two/three`); `Nat.prime_seven` exists.

## 2026-09-19 ~01:00 — Agent #3 pickup (executing plan)

- Prior report above is recon by agent #2 (died before edits). Executing now.
- Downstream check: `Case4Int.lean:9` comments out the Carry import ("pending
  repair") and uses private copies `digit7_add_mem'`/`qdig7_add_mem'`/`digit7_add'`
  (lines 338-394) — verbatim WORKING versions I can copy:
  * `digit7_add'` hdiv: `show` rearranges to `... + 7^m * (a/7^m + b/7^m)`
    (divisor-LEFT) then `Nat.add_mul_div_left`, then `ring`.
  * `digit7_add_mem'`: `Nat.div_lt_iff_lt_mul` + `interval_cases (...) <;> simp`.
  * `qdig7_add_mem'`: only THREE `rw [qdig7_eq_digit7]` (each rw rewrites all
    occurrences of one instance; 4th fails).
  * `qdig7_eq_digit7'` uses `Nat.mod_mul_right_div_self` directly.
- Spec `lrc7-sec6-spec.md:320` confirms `exists_multLow_one_set_seven` SHOULD have
  `(hd0 : 0 < d)` (and `2 ≤ m`); file dropped `hd0` → FALSE at `d = 0`.
  Contract → corrected variant `exists_multLow_one_set_seven'` (adds `hd0`,
  keeps `0 < m`, strictly more general than spec). Nothing imports Carry.lean
  yet so the rename is safe; old (false) decl must be REMOVED (can't compile
  a false theorem without sorry).
- `linear_combination`/`nlinarith` used elsewhere in repo → available via
  import chain.
- Plan adjustments confirmed by reading carry2.log goal states:
  * `hx` inside `hdecomp`: `rw [← h1]` rewrites ALL `x` → use `conv_lhs` with
    `← Nat.div_add_mod` twice, then `rw [h3, hm1]; ring`.
  * `hkx`/`hq`/`hSsplit`: `Nat.mod_add_div` gives `a%b + b*(a/b) = a`
    (divisor LEFT) — file wrote `a/b*b`; fix via `have := ...; omega`.
  * `hcarry`/`hkdiv` statements contain `(... / 7 : ZMod 7)` → HDiv ℕ ℕ (ZMod 7)
    failure → ascribe inner `(... / 7 : ℕ)` then cast.
  * `h` inside hcarry: `rw [hq]` would hit `k*(x%7)` nested inside
    `(k*(x%7))%7` → `conv_lhs => rw [hq]`.
  * Final step: `rw [hcarry]` fails (target `↑(S/7)+↑(k*(x%7)/7)` not a subterm
    due to assoc) → `linear_combination hcarry`.
  * `hlo` in hdivhi: bound `S%7*7^(m-1) ≤ 6*7^(m-1)` via `Nat.mul_le_mul_right`
    then `rw [hm1]; omega`.
  * `hval` (6-case): `(ZMod.natCast_eq_natCast_iff).mp h'` gives `≡ 6 [MOD 7]`;
    omega understands ModEq with literal modulus.
  * `inv_mul_cancel₀` diamond → `∀ u : ZMod 7, u ≠ 0 → u⁻¹*u = 1 := by decide`
    applied to `hu := runit7_ne_zero hd0`.

## 2026-09-19 ~01:15 — All planned edits applied (agent #3)

Applied to `Research07/LRC7/Carry.lean`:
1. `mod_mul_div` → `exact Nat.mod_mul_right_div_self x a b` (16-line proof → 1 line).
2. `qdig7_seven`: `← pow_succ` → `← pow_succ'` (goal `7^m = 7*7^(m-1)`).
3. `digit7_add_mul_pow`: `add_mul_div_left` → `add_mul_div_right`.
4. `digit7_add` hdiv: verbatim copy of working `Case4Int.digit7_add'` —
   `show` rearranges to `... + 7^m * (a/7^m + b/7^m)`, `add_mul_div_left`, `ring`.
5. `digit7_add_mem` hc: `div_lt_iff_lt_mul` + `interval_cases <;> simp`
   (copy of `digit7_add_mem'`).
6. `qdig7_add_mem`: 3 rws (was 4).
7. `qdig7_two_eq_smul_add_one`: `hval` via `omega` on ModEq hyp;
   `pow_succ'`; `add_mul_div_right`; dropped trailing `ring` (rw auto-closes).
8. `exists_multLow_one_set_seven` → REMOVED (FALSE at d=0); NEW
   `exists_multLow_one_set_seven'` with `(hd0 : 0 < d)` added;
   `hu := runit7_ne_zero hd0`; `hmul` via
   `∀ u : ZMod 7, u ≠ 0 → u⁻¹*u = 1 := by decide` (avoids inv_mul_cancel₀
   0-instance diamond).
9. `digit7_multLow_one`: statement carry `(((…)/7 : ℕ) : ZMod 7)`;
   `hx` via `conv_lhs` double `← Nat.div_add_mod` + `rw [h3, hm1]; ring`;
   `hkx`/`hq`/`hSsplit` fixed to `mod_add_div`'s `b*(a/b)` order;
   `hdivlo`/`hdivhi`/`hk7`/hcarry-end all → `add_mul_div_right`;
   `hlo` via `Nat.mul_le_mul_right` bound + `rw [hm1]; omega`;
   first conjunct → `simp only [ZMod.natCast_mod, hS, …]`;
   `hkdiv`/`hcarry` statements get inner `ℕ` ascriptions;
   `h` in hcarry via `conv_lhs => rw [hq]` (nested `(k*(x%7))%7`);
   final step → `linear_combination hcarry`;
   `h49` via `ZMod.natCast_self 7`.
10. Build pending: `carry_3.csv`.

## 2026-09-19 ~01:40 — Build carry_3: 3 residual errors, all fixed

`carry_3` (59s, peak 9.0GB) residuals:
- `hval` (line ~138): `omega` does NOT see through `a ≡ 6 [MOD 7]` when `a`
  is itself a `%`-expression — it abstracted `x/7^(m-1)` and `(x/7^(m-1))/7`
  as independent atoms, dropped the ModEq link. FIX:
  `(ZMod.natCast_eq_natCast_iff' _ _ _).mp h'` gives `a%7 = 6%7` directly
  (verified `Mathlib/Data/ZMod/Basic.lean:510`), then
  `simpa [Nat.mod_mod] using hv` (mod_mod strips `a%7%7`, reduceMod 6%7).
- `exists_multLow_one_set_seven'` `hinv` (line ~198): `decide` on
  `∀ u : ZMod 7, u ≠ 0 → u⁻¹ * u = 1` FAILS — `Fintype.decidableForallFintype`
  kernel-reduction gets stuck on `u⁻¹` (ZMod inv via gcd/Bezout doesn't
  reduce). FIX: `∃ v : ZMod 7, v * u = 1` — decidable WITHOUT `⁻¹`
  (only `*` and `=` reduce) → `obtain ⟨v, hv⟩`, `k0 := (c - dig) * v`,
  `rw [mul_assoc, hv, mul_one]`.
- `hS7` `congr`-subgoal (line ~315): `rw [Nat.mul_mod, Nat.mul_mod]` — the
  second generic `Nat.mul_mod` re-matched the already-rewritten LHS
  `((k%7)*(x%7))%7` (it is itself `a*b%n` form) instead of the RHS
  `(k*(x%7))%7`, leaving `k%7*(x%7%7)%7 = k*(x%7)%7`. FIX: explicit
  instance `Nat.mul_mod k (x % 7) 7` for the RHS hit, then `Nat.mod_mod`.

`carry_4`: **exit=0** (72.2s, peak 9.0GB). Remaining diagnostics: warnings
only — `ha`/`hb` unused in `mod_mul_div` (fixed via `_ha`/`_hb`), `haveI`
style lint at line 192 (`NeZero 7` instance genuinely needed for
`ZMod.val_lt`/`ZMod.natCast_zmod_val` — linter false-positive, kept).

`lake build Research07.LRC7.Carry`: GREEN, 8927 jobs, ~22s for the file.

Axiom gate (`_dev/scratch/CarryAx.lean`, all 13 decls):
`[propext, Classical.choice, Quot.sound]` for every decl — PASS.

Forbidden constructs: grep `sorry|admit|native_decide|unsafe` — none.

Downstream: only ref to Carry is `Case4Int.lean:9` commented-out import
("pending repair") — nothing imports it; the `exists_..._seven` →
`exists_..._seven'` rename is safe. `Case4Int` keeps its private
`digit7_add_mem'`/`qdig7_add_mem'` copies (not my file — untouched).

Failure ledger: 2 lines appended to `_dev/failures.md`
(false-statement tag for the d=0 countermodel; lemma-arg-order +
rw-scope + kernel-reduce-fail tag for the rest).

## Fix plan (per-theorem)
- `mod_mul_div` → `exact Nat.mod_mul_right_div_self x a b` (ha/hb unused, warning OK).
- `mod_mul_div` → `exact Nat.mod_mul_right_div_self x a b` (ha/hb unused, warning OK).
- `qdig7_eq_digit7` unchanged; `qdig7_seven` fix `pow_succ`→`pow_succ'`.
- `digit7_add_mul_pow`/`digit7_add` → `Nat.add_mul_div_right`-style div/mods;
  `digit7_add` hdiv rebuilt like `add_div_carry7` (divisor-left product + ring).
- `digit7_add_mem` → bound carry `< 2` via `Nat.div_lt_iff_lt_mul` then omega.
- `qdig7_add_mem` → `simp only [qdig7_eq_digit7]`.
- `qdig7_two_eq_smul` untouched (no errors). `qdig7_two_eq_smul_add_one`:
  hval via `ZMod.natCast_eq_natCast_iff'`+omega; `pow_succ'`; `add_mul_div_right`; end `ring`.
- `exists_multLow_one_set_seven'` NEW (hd0 added): `hu := runit7_ne_zero hd0`;
  `∀ u : ZMod 7, u ≠ 0 → u⁻¹*u = 1` by `decide` (avoids `≠`-instance diamond).
- `digit7_multLow_one`: statement cast `(.../7 : ℕ) : ZMod 7`;
  `hx` via `conv_lhs => rw [← div_add_mod, ← div_add_mod]` + `ring`;
  `hkx`/`hSsplit` corrected `mod_add_div` form; `add_mul_div_right`;
  `hlo` via `Nat.mul_le_mul_right`/`gcongr` then omega; branch-1 `simp only`;
  `hkdiv`/`hcarry` rebuilt (casts + `Nat.mul_mod`+`Nat.mod_mod` + `add_mul_div_left`);
  final `rw [← hcarry]; ring`.
