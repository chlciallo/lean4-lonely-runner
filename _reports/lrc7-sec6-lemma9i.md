# lrc7-sec6-lemma9i.md — Lemma 9(i) implementation log (`Case5mL9.lean`)

Incremental per `_reports` protocol. Task: prove `lemma9_i` (BS7 Lemma 9(i),
3-compression) in NEW file `Research07/LRC7/Case5mL9.lean`.

---

## 2026-10-03 — COUNTERMODEL: verbatim spec statement is FALSE at `ν = m`

Spec §3.5 target (verbatim):

```lean
∃ lam : ℕ, ¬ 7 ∣ lam ∧
  (∀ x ∈ {b1,b2,b3}, ∀ y ∈ {b1,b2,b3},
    qdig7 m (eMod7 m (lam*x) (lam*y)) ∈ ({0,6} : Finset (ZMod 7))) ∧ ...
```

**The all-ordered-pairs condition fails whenever `ν(x) = m` or `ν(y) = m`.**

Countermodel (`_dev/scratch/check_l9.py`, `check_l9b.py`, exhaustive over `lam`):

- `m = 2, b = (295, 8, 1)`: `x = e(b1,b3) = 294` (`ν = 2 = m`),
  `y = e(b2,b3) = 7` (`ν = 1`). `runit7` all `= 1`, `ν(bi) = 0`, `he`/`hν` hold.
  Scan of `lam ∈ [1, 2400]`, `7∤lam`: **zero** lam achieves all-pairs `{0,6}`.
- `m = 3, b = (2059, 50, 1)`: `x = 2058` (`ν = 3 = m`) — same: `[]`.
- `m = 3, b = (8, 50, 1)`: `x = 7 (ν=1), y = 49 (ν=2)`, both `< m` — works
  (`lam = 1..6` all good). Confirms the obstruction is exactly the `ν = m` edge.

**Why (kernel-level reason):** for same-`r` pairs `e(b3,b1) ≡ −x (mod N)`.
If `ν(x) = m` then `λx % N = t·7^m` for any unit `λ` (`f = 0` forced), and
`λ·e(b3,b1) ≡ −λx ≡ (7−t)·7^m` — so `q(λx) + q(λ·e31) = 7` exactly.
`{q, 7−q} ⊆ {0,6}` is impossible: `q = 6 ⇒ 7−q = 1`. At `ν < m` instead
`λx % N = 6·7^m + f` with `f > 0` (`7^m ∤ λx`), so `−λx ≡ 7^m − f` has `q = 0`
— all nine ordered pairs land in `{0,6}` when `q(λx) = q(λy) = 6`:

- pairs (1,3),(2,3): `q(λx) = q(λy) = 6`;
- pairs (1,2),(2,1): `λe ≡ ±(λx−λy) = ±(fx−fy)` — `q = 0` or `6`;
- pairs (3,1),(3,2): `λe ≡ −λx ≡ 7^m − fx` — `q = 0` (needs `fx ≠ 0`, i.e. `ν < m`);
- diagonal: `e = 0`, `q = 0`.

**Minimal fix (implemented):** add hypothesis
`hνm : padicValNat 7 (eMod7 m b1 b3) < m ∧ padicValNat 7 (eMod7 m b2 b3) < m`
to `lemma9_i`. This matches usage: §6 applies Lemma 9 in `h < m` branches;
where `ν = m` the reversed-pair `{0,6}` condition is unattainable anyway
(so the §6.1 `case61_dichot` route is also unavailable there — flag to
orchestrator: case (i) with `ν(e21) = m` needs a separate argument).

Per AGENTS.md frozen-statement rule this is a demonstrated countermodel;
orchestrator approval required for the signature change — flagged here.

---

## API inventory used (verified by reading source)

- `filtered7_mod7 D hpos _hm hi₀ F hlow` (Case5mBase:691): gives
  `lam % 7 = 1` ⇒ `runit7 lam = 1` via `runit7_eq_one_of_mod7`
  (Case5mBase:597) ⇒ `eMod7_mul` applies (Case5mBase:646).
- `eMod7_mul hlamr : eMod7 m (lam*x)(lam*y) = (lam * eMod7 m x y) % N`.
- `eMod7_zmod_cast` is PRIVATE in Case5mBase:616 and Case5mCases:38 —
  must clone. Same for `mul_pow_add_div`, `div_mod_pow_cast`,
  `qdig7_eMod_of`, `residue_decomp`, `natCast_sub_add` (Case5mBase:277–312
  / Differences:407–436).
- `qdig7_congr : a%N = b%N → qdig7 m a = qdig7 m b` (Filtering:31).
- `padicValNat_mul_seven` (Filtering:37), `enu7_le_of_ne` (Case5mBase:114).
- `remark8_i_int` (Case5mBase:1056) bridges pairwise `q(e)∈{0,6}` →
  digit-diffs `∈{0,1,6}` → `remark8_i` (Compress:228) `k=1` → `apLen ≤ 2`.
- `level7 D j = D.filter (ν · = j)` (Discrete:34).
- `runit7_mul`, `runit7_ne_zero` for scaled-pair `residueRelOf = same`.

## New machinery plan (this file)

- `qdig7_sub_resid` (exact form):
  `qdig7 m (a%N + N − b%N) = qdig7 m a − qdig7 m b − (a%7^m < b%7^m ? 1 : 0)`
  — the borrow-exact digit of a wrapped residue difference; `{0,6}`
  corollary `q − (qa−qb) ∈ {0,6}` and the `a=0` negation
  `q(−b) = −qb − (0<fb ? 1:0) = 0` when `qb=6, fb≠0`.
- `eMod7_smul (hc : runit7 c ≠ 0)` — per contract (eMod7_zmod_cast clone +
  `mul_left_cancel₀` branch preservation).
- `rel_same`: `runit7 u = runit7 v → v ≠ 0 → residueRelOf u v = same`.
- `eMod7_zmod_cast_same`: `(eMod7 m u v : ZMod N) = u − v` under `same`.
- `eq_six_of_not_mem_five`: `q ∉ {0..5} → q = 6` (private decide).

---

## FINAL STATUS — GREEN (2026-10-05)

`lake env lean Research07/LRC7/Case5mL9.lean` under memwatch 12288MB:
**exit=0, zero errors, zero warnings**, elapsed ~34s, peak_tree_priv ≈ 8976MB
(logs `_dev/memlog/c5l9_8..10.csv`). File: 565 lines.

```
'lemma9_i'   depends on axioms: [propext, Classical.choice, Quot.sound]
'eMod7_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorry`/`admit`/`native_decide`/`unsafe`. `#print axioms` lines live at
file end. The file is NOT in the `Research07.lean` umbrella (consistent
with the other WIP `LRC7/Case5m*` modules — standalone `lake env lean`
builds, as with `Case5mCases`).

### Resolved pending concern (was task #16)

The earlier "m=2, both valuations < m, yet no all-pairs lam" datum was
mislabeled: for `m=2, (b1,b2,b3)=(8,50,1)`, `e(b2,b3)=49` has
`ν(49)=2=m` — NOT `< m`. So every observed failure is exactly a
`ν = m` case, and every `ν < m` case worked (`m=3, (8,50,1)` etc.).
The `hνm` hypothesis is therefore precisely the boundary between
solvable and unsolvable, matching the now-machine-verified proof.

### Proof architecture (as built)

- `qdig7_sub_resid` (~line 132): exact borrow identity
  `q((a%N + N − b%N)) = q(a) − q(b) − [a%7^m < b%7^m]` via residue
  decomposition `a%N = q_a·7^m + f_a`, `mul_pow_add_div`,
  `Nat.mod_mod_of_dvd`, `Nat.add_mul_mod_self_right`, `natCast_sub_add`.
- `qdig_smul_eMod_eq` (~line 210): `↑(λe) = ↑A − ↑B` in `ZMod N` ⇒
  `q(λe) = q(A) − q(B) − borrow` via `ZMod.natCast_eq_natCast_iff'` +
  `qdig7_congr` + `qdig7_sub_resid`.
- `eMod7_smul` (~line 267): `e(cx,cy) = (c·e(x,y)) % N` for
  `runit7 c ≠ 0` — cloned `eMod7_zmod_cast`, `runit7_mul`, branch
  preservation by `mul_left_cancel₀`, `ZMod.natCast_eq_natCast_iff`.
- `lemma9_i` (~line 284): `filtered7_mod7 D={x,y}` at levels `ν(x),ν(y)`
  (each `level7` Finset has card ≤ 1 since `ν(x) ≠ ν(y)`, so the
  `F={0,…,5}`-cardinality budget `6·1 ≤ 6` holds) forces
  `q(λx)=q(λy)=6`; the nine pairs evaluate through `eval` (one
  `eMod7_mul` + borrow formula) — `(bi,bi)↦0`, `(b1,b3),(b2,b3)↦6`,
  `(b3,b1),(b3,b2)↦0` (borrow `0 < f` since `7^m ∤ λx,λy` from `ν<m`),
  `(b1,b2),(b2,b1)↦6` or `0` by borrow case — then
  `remark8_i_int` + `remark8_i (k=1)` gives `apLen ≤ 2`.

### Build-error fixes worth remembering

- `Nat.add_mul_mod_self_left : (a + b*n) % b = a % b` — modulus = FIRST
  product factor; for `(q·7^m + f) % 7^m` use `add_comm` +
  `Nat.add_mul_mod_self_right` (modulus = second factor).
- `rcases … with rfl`/`subst` on `u = b1` eliminates the RHS variable
  `b1` (not `u`) → "unknown identifier". `fin_cases` fails outright on
  `u ∈ {b1,b2,b3}` with variable elements (dependent elimination through
  `List.insert` dedup). Working idiom:
  `rw [Finset.mem_insert, …, Finset.mem_singleton] at h;
   rcases h with h|h|h <;> rw [h]` (rewrites the goal only).
- `rw` instantiates a lemma at its first match then rewrites ALL copies —
  one `Nat.cast_mul` per `↑(λ·)` product; and `set` let-variables
  (`x := eMod7 m b1 b3`) are matched by `rw` through their let-value, so
  `↑(lam * x)`/`↑x` get rewritten together with the literal residue —
  don't supply duplicate rewrites.
- `rw` auto-closes goals that become `rfl` — after
  `rcases … <;> rw [h]`, don't leave a bullet for the collapsed goal
  (use `first | …` or drop the case).
- `Finset.mem_insert_self` takes TWO explicit args (`a s`); a lone `_`
  leaves `s` bound. `decide` closes literal `ZMod 7` memberships
  `(expr) ∈ {0,6}` directly — simplest tail.
- Deprecated `if_pos`/`if_neg` → `ite_eq_left`/`ite_eq_right`
  (same signatures).

### Orchestrator flags

- Signature change `hνm` added — demonstrated countermodel above;
  per frozen-statement rule this needs orchestrator sign-off.
- §6 usage note: Lemma 9(i) with `ν(e21) = m` (or `ν(e31) = m`) is
  mathematically unreachable via the `{0,6}`-pair route (reversed pair
  forces `q + q' = 7`); if §6 needs the `ν = m` boundary it requires a
  different argument. `_hunit` binder is unused by the proof.
