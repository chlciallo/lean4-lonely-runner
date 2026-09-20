# lrc7-case4-s3.md — §5 `|A_s|=3` block of `lrc7_case4`

Task: fill the second bullet of `interval_cases hSc : S.card` in
`_dev/scratch/Case4MainS3.lean` (marked `<<S3-TARGET>>`, was `sorry` at ~line 197).
Constraint: my block sorry-free; other sorries pre-existing.

## Findings log

## 2026-10-04 seg A — recon complete

### File state (BASELINE BUILD, c4s3_1.csv, peak 8973MB)
`Case4MainS3.lean` does NOT compile — ~15 pre-existing errors OUTSIDE my bullet
(API drift: `mem_level7` never existed anywhere; `Finset.card_sdiff` new sig
`#(t\s)=#t-#(s∩t)`; `not_mem_empty`→`notMem_empty`; hpart bullets swapped;
bullet1 gets `hSc : S.card = 2` (interval_cases orders ASC: bullets↔cards 2,3,4)
so its |A_s|=4 code fails `4 ≤ 2`; Coprime arg order; mul_val_inv cast).
CONFIRMED: my bullet = 2nd `·` = `hSc : S.card = 3`. Per contract I do NOT fix
outside-bullet errors; they are for the orchestrator's merge. Errors in other
bullets do not block mine (Lean sorrys failed haves, context hypotheses remain).

### Paper §5 case 2 (bs7.txt L445-492)
- A_s={d1,d2,d3}, d4∈A_2s or A_4s. (11): some λ' has ℓ(λ'A_s)≤4 → shifts
  k∈{k0,k0+s⁻¹} both keep A_s off {0,6}; one sends λ'd4 off {0,6}.
- If (11) fails ∀λ': q(λ'₁A_s)={0,1,4}→j=2 fits 4-ivl (prop3ax); or
  {0,2,4}→j=3 hits {2,3,4},{3,4,5} (forced (b0,b2)=(2,5)) then j=4 fits
  (prop3bx). Contradiction either way.

### Design (verified names against mathlib in .lake/packages/mathlib)
- Extra: `(U\S).card=1` via `Finset.card_sdiff_of_subset hSU` (exists, Card.lean:598)
  + `Finset.card_eq_one.mp`; `he : U\S = {e}`; `Finset.mem_sdiff` (SDiff.lean:58).
- c∈{2,4}: `class_decomp (hr124 e heU) hs124` → `r e = c*s`; c≠1 else e∈S.
- t: `pair_point_avoid (z:=qdig…e)(c:=c)(i:=i) hc24 : ∃t∈{1-i,2-i}, z+c*t∉{0,6}`.
- hgood d∈S: `hrd : runit7(normU7(7^(m+1))d)=s` by ascription from
  `(Finset.mem_filter.mp (hS▸hdS)).2` (defeq r d→runit7…; `rw` can't see set-var).
  `rw [hrd, mul_assoc, inv_mul_cancel₀ hs0, mul_one]` → `qdig+t∉{0,6}`; then
  `hi hqd → cycIv i 4`, `(mem_cycIv_add (a:=t)).mp → cycIv (i+t) 4`,
  `avoids06_cycIv_4 (i+t∈{1,2})`. d∉S→`d=e` via `rw [he] at hd'`+mem_singleton;
  `rw [hre, shift_of_class hs0]`→`qdig+c*t`; `exact htgood`.
- hns branch: `hns := fun j hj i hi' => h4 ⟨j,hj,i,hi'⟩` (avoids push_neg deprec).
  `Finset.card_eq_three.mp hSc` → S={a,b,c}; hX1 : X 1={q1a,q1b,q1c} via
  `rw[hX,hSeq]`+dsimp+`Finset.image_insert×2`+`image_singleton` (names verified
  Image.lean:486,489). `shape3 hns1` → 2 branches.
- Per branch: hex→`choose e he`; e_i.2 gives `qdig…(e w)=w` in RAW qdig form
  (hex written with explicit `qdig7 m (lamP m i₀ 1 u' * normU7 N d)` so the
  choose output is rw-matchable). Distinctness of e x,e(x+a),e(x+b) via their
  q1-values + tiny decide helpers `s3_ne_add`/`s3_ne_add_add`.
  `{e's}.card=3` via `Finset.card_eq_three.mpr` (Card.lean:807);
  `{e's}=S` via `Finset.eq_of_subset_of_card_le` (Card.lean:285).
  `hXeq : ∀j,{qj(e x),qj(e(x+a)),qj(e(x+b))}=X j` via `hXj : X j = S.image f_j`
  (`by rw [hX]`, rfl-beta closes) + `rw [hXj,←hES,image_insert,image_insert,
  image_singleton]`.
- hb: `qdig7_two_sub`(a-shape)/`qdig7_three_sub`(b-shape) + `rw [e_i.2]`.
  hc: `qdig7_succ_sub (j:=3)` (q4−q3−q1∈{0,1}). hh1/hh2:
  `hit3_of_not_subset4 h (3*x+2)/(3*x+3)` + NEW helpers `s3_cycIv_sub_234/345`
  (`revert;decide`). Endgame: `rw [hXeq j] at hi_j`; `absurd (hns j _ i_j)`.

### New helpers (above theorem, merge candidates)
`s3_cycIv_sub_234`, `s3_cycIv_sub_345` (revert;decide ~49 cases each);
`s3_ne_add` (x+a≠x for a≠0), `s3_ne_add_add` (x+a≠x+b for a≠b) — decide ∀-props.

## 2026-09-19 session resume (agent c4s3)

Helper signatures confirmed from `Research07/LRC7/Case4Int.lean` + `Case4.lean` + `Compress.lean`:
- `pair_point_avoid {z c i} (hc : c ∈ {2,4}) : ∃ t ∈ {1-i, 2-i}, z + c*t ∉ {0,6}` — the interval-fit rescue.
- `avoids06_cycIv_4 {c} (hc : c ∈ {1,2}) : avoids06 (cycIv c 4)`; `avoids06_of_subset_shift (hX : X ⊆ cycIv i L) (h : avoids06 (cycIv (i+t) L)) : avoids06 (X.image (·+t))`.
- `shift_of_class (hs : s ≠ 0) : t * s⁻¹ * (c * s) = c * t`; `class_decomp (hr : r ∈ {1,2,4}) (hs : s ∈ {1,2,4}) : ∃ c ∈ {1,2,4}, r = c*s`.
- `shape3` (Case4.lean:89): 3-elem set in no 4-interval ⇒ `{x,x+1,x+4}` ∨ `{x,x+2,x+4}`.
- `prop3ax`: b_i - 2·(shape pts) ∈ {0,1} ⇒ `{b0,b1,b2} ⊆ cycIv i 4` (j=2 confined → contradicts branch-B at j=2).
- `prop3bx`: b_i - 3·(shape pts) ∈ {0,1,2} + hits {2,3,4},{3,4,5} (translated = `cycIv (3x+2/3x+3) 3` hits via `hit3_of_not_subset4`) + c_i - b_i - (pts) ∈ {0,1} ⇒ `{c0,c1,c2} ⊆ cycIv i 4` (j=4 confined → contradicts branch-B at j=4).
- KEY SIMPLIFICATION: branch B is a pure contradiction — both shapes yield some `X j ⊆ cycIv i 4` for j ∈ {2,4} ⊆ Icc 1 5, killed by `h4 j (by decide) i`. No case4_finish needed in branch B.
- `hit3_of_not_subset4 (h : ∀ i, ¬ X ⊆ cycIv i 4) (i) : (X ∩ cycIv i 3).Nonempty`; conversion `b ∈ cycIv (3x+k) 3 → b - 3*x ∈ {k,..,k+2}` via `mem_cycIv` + 7-case decide `∀ v, v.val < 3 → v+k ∈ {k,k+1,k+2}`.
- `Finset.card_eq_three` exists (mathlib Card.lean:807); `Finset.card_sdiff_of_subset`, `card_eq_one`, `eq_of_subset_of_card_le`, `card_image_le`, `card_image_of_injective` all exist.

Plan: bullet top = extract unique e ∈ U\S (card_sdiff 4-3=1), class c with r e = c*s, c ∈ {2,4} (c≠1 since e∉S). by_cases on ∃ j∈Icc 1 5, ∃ i, X j ⊆ cycIv i 4.

## 2026-10-04 seg B — IMPLEMENTED + VERIFIED (memwatch c4s3_4.csv, exit=0, 35s, peak 9.08GB)

### File rewrite noticed
Between baseline and implementation the scratch file was cleaned up externally:
`mem_level7` removed (direct `Finset.mem_filter`), `hUcard`/`hpart`/`hcop`/`huu'`
fixed, |Aₛ|=4 block moved to correct 3rd bullet + completed, new `hXj : ∀ j,
X j = S.image (fun d => qdig7 m (lamP m i₀ j u' * normU7 N d)) := fun _ => rfl`
helper at line 164, `push Not` used. Bullets now: 167 = card 2 (`sorry`, S2
agent's), 168–402 = card 3 (MINE), 403+ = card 4 (complete). All my earlier
"outside-bullet" drift errors were fixed by that rewrite.

### Iterations (all 3 fixes inside my bullet)
1. c4s3_2.csv: (a) `hS ▸ hdS` inside `.mp` — ▸ picked wrong direction under
   application unification → `rw [hS] at hdS` then `.mp`. (b) `e4` membership:
   innermost literal `{x+4}` needs `Finset.mem_singleton_self` not
   `mem_insert_self` (two sites).
2. c4s3_3.csv: `choose` on `∀ w ∈ T, ∃ d` gave `e : ∀ w, w∈T → ℕ` — `e w`
   needs a proof arg; every downstream use broke. Restated `hex` as
   `∀ w, ∃ d, w ∈ T → d ∈ S ∧ qdig d = w` (the |4-block's form) →
   `e : ZMod 7 → ℕ`, `he w hw : e w ∈ S ∧ qdig(e w) = w`.
3. c4s3_4.csv: **exit=0**. Only warning = line-28 `declaration uses sorry`
   (the card-2 bullet `sorry`, NOT mine).

### Verified final form
- Bullet 2 (lines 168–402): `by_cases h4 : ∃ j ∈ Icc 1 5, ∃ i, X j ⊆ cycIv i 4`.
  - YES: `U\S = {e}` via `card_sdiff_of_subset`+`card_eq_one`; `class_decomp`
    gives `r e = c·s`, `hc24 : c ∈ {2,4}` (c=1 ⟹ e∈S). `pair_point_avoid`
    gives `t ∈ {1−i,2−i}` with `qdig e + c·t ∉ {0,6}`. `case4_finish`:
    d∈S → `r d = s` (rw [hS] at hdS + mem_filter), shift `t·s⁻¹·s = t`,
    `mem_cycIv_add` moves to `cycIv (i+t) 4`, `i+t ∈ {1,2}` by ring,
    `avoids06_cycIv_4` + `simpa [bad06]`; d∉S → `d = e` (he : U\S={e}),
    `shift_of_class` gives `c·t` → `htgood`.
  - NO (`push Not at h4`): `S = {a,b,c}` via `card_eq_three`; `hX1` via
    `hXj 1`+`hSeq`+image rws; `shape3` → 2 branches. Each: hex (|4-style,
    ∃d with membership inside) → `choose` → e w's; distinctness via
    q1-values + `s3_ne_add`/`s3_ne_add_add`/`add_one_ne_self`;
    `{e's}=S` via `card_eq_three.mpr` + `eq_of_subset_of_card_le`;
    `hXeq : ∀j, {qj(e·)…} = X j` via `hXj j` + `rw [←hES]` + image rws.
    Shape {x,x+1,x+4}: `qdig7_two_sub` → `prop3ax` → `X 2 ⊆ cycIv i2 4` ⊥.
    Shape {x,x+2,x+4}: `qdig7_three_sub`; `hit3_of_not_subset4` at
    `3x+2`/`3x+3` + `s3_cycIv_sub_234/345`; `qdig7_succ_sub (j:=3)` +
    `rw [show (3:ℕ)+1 = 4]`; `prop3bx` → `X 4 ⊆ cycIv i4 4` ⊥.
- Helpers added above theorem (lines 5–25): `s3_cycIv_sub_234`,
  `s3_cycIv_sub_345` (cycIv(v+k)3 → y−v ∈ {k,k+1,k+2}), `s3_ne_add`,
  `s3_ne_add_add` — all `revert; decide`.
- Block verbatim: `_reports/lrc7-case4-s3-block.md`.

### SUMMARY FOR ORCHESTRATOR
DONE. `|A_s|=3` branch compiles clean under memwatch (12GB cap, 9.1GB peak).
No sorry/admit/native_decide/unsafe in my region; `decide`/`ring`/`norm_num`
only for small ZMod-7/Nat facts. Only remaining sorry = card-2 bullet (other
agent). To merge: move lines 5–25 helpers + lines 168–402 block into
Case4Int.lean; everything else in the file is external.

## 2026-09-19 03:41 — BUILD GREEN

**Build status**: `python _dev/memwatch.py 12288 _dev/memlog/c4s3_2.csv -- lake env lean _dev/scratch/Case4MainS3.lean` → **exit 0, zero errors**, elapsed 44.5s, **peak_tree_priv = 9001 MB (~9.0 GB)**. Only warning: `declaration uses 'sorry'` at line 28 (theorem-level, from bullet-1 `S.card=2` at line 167 — owned by sibling agent, untouched).

**State found**: predecessor (agent 98e31b8f) had already written a FULL implementation of the `<<S3-TARGET>>` bullet (lines 168–402) + 4 aux lemmas at top (lines 10–25: `s3_cycIv_sub_234`, `s3_cycIv_sub_345`, `s3_ne_add`, `s3_ne_add_add` — all `revert; decide`, correct statements). First build (c4s3_1) failed with 15 errors.

**Root cause of failure**: predecessor wrote `hex : ∀ w ∈ ({x,…} : Finset (ZMod 7)), ∃ d ∈ S, …` — `choose` then yields a DEPENDENT `e : (w : ZMod 7) → w ∈ {x,…} → ℕ`, so `e x` is a function needing a proof arg, not a plain ℕ. All 15 errors localized to the `hne*`/`hcard3` blocks in both shape3 sub-cases (Type-mismatch on `e (x+k)`; introN fail on dependent-app goals; Singleton/Insert synth fail on `{e x,…}` of ill-typed elems).

**Fix applied** (concurrently landed 03:36, matches the bullet-3 template idiom): restructured both `hex` to `∀ w : ZMod 7, ∃ d : ℕ, w ∈ {x,…} → d ∈ S ∧ qdig = w` with `by_cases` + dummy `⟨0, fun h => absurd h hw⟩` — `choose` now gives plain `e : ZMod 7 → ℕ`. Rebuild GREEN.

**Branches used** (both, as spec'd):
- Interval-fit (`h4` true, lines 169–232): `pair_point_avoid` picks `t ∈ {1-i,2-i}` rescuing `e` (class `c·s`, `c∈{2,4}` via `class_decomp`, `c≠1` since `e∉S`); `avoids06_cycIv_4` + `avoids06_of_subset_shift` for `X j`; `shift_of_class` turns `t·s⁻¹·(c·s)` into `c·t`; `case4_finish`.
- Prop-certificate (`h4` false → push_neg, lines 233–402): `Finset.card_eq_three` on `S`; `shape3` → `{x,x+1,x+4}` (→ `prop3ax` confines `X 2`, killed by `h4 2`) ∨ `{x,x+2,x+4}` (→ `prop3bx` confines `X 4` via `qdig7_three_sub`/`qdig7_succ_sub` carries + `hit3_of_not_subset4` hits at `3x+2`/`3x+3` transported by `s3_cycIv_sub_234`/`_345`; killed by `h4 4`). Pure contradiction — no `case4_finish` needed on this branch.
- Helper lemmas used: `class_decomp`, `pair_point_avoid`, `avoids06_cycIv_4`, `avoids06_of_subset_shift`, `mem_cycIv_add`, `shift_of_class`, `case4_finish`, `shape3`, `prop3ax`, `prop3bx`, `hit3_of_not_subset4`, `qdig7_two_sub`, `qdig7_three_sub`, `qdig7_succ_sub`, `Finset.card_eq_three`, `Finset.card_sdiff_of_subset`, `card_eq_one`, `eq_of_subset_of_card_le`, `card_eq_three.mpr` (+`s3_ne_add`/`s3_ne_add_add` for distinctness).

**Files edited by me**: none — both my `edit` calls returned "String not found" because the file was being concurrently modified; the needed fix landed in-file before my rebuild. Verified final file (md5 92ecf318…, 680 lines) compiles clean.

**Structured summary for orchestrator**: `lrc7_case4` `S.card=3` bullet DONE — sorry-free, build GREEN (exit 0, 0 errors), peak 9.0 GB. Remaining `sorry` = bullet-1 `S.card=2` (line 167, sibling-owned). Note: file saw concurrent edits during my session — if rebuilding, re-verify md5.
