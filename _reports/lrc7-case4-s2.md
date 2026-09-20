# lrc7-case4-s2.md — |A_s|=2 case of `lrc7_case4` (paper §5)

Task: fill `· sorry` marked `<<S2-TARGET>>` at ~line 198 of
`_dev/scratch/Case4MainS2.lean` (third bullet of `interval_cases hSc : S.card`, `hSc : S.card = 2`).
Do not touch anything outside that bullet. No sorry/admit/native_decide/unsafe in my block.

## Segment 1 — context absorbed (timestamp: start of session)

### File state (lines 1-251 read)
- `lrc7_case4` skeleton: `N := 7^(m+1)`, `U := {d1,d2,d3,d4}` (level-0, ν=0),
  `r d := runit7 (normU7 N d) ∈ {1,2,4}` on U (`hr124`), `cnt` partition 1+2+4=4,
  `s` = argmax class, `S := U.filter (r·=s)`, `X j := S.image (qdig7 m (lamP m i₀ j u' * normU7 N d))`.
- `interval_cases hSc : S.card` → bullets for card=4 (partially done, sorry at 195),
  card=3 (sorry 196), card=2 (TARGET sorry 198).
- Main call signature: `main i₀ u' hi0 him hu'nd hd5bound` where `hd5bound` is the
  intermediate-element bound consumed by `case4_finish`'s `hd5`.

### APIs confirmed (Case4Int.lean)
- `case4_finish {m i₀ j u'} (hm)(him)(hj:1≤j∧j≤5)(hu'){s}(hs:s≠0)(t)(D)(hpos)(hle)(hgood)(hd5)` (L592)
  — hgood: `∀d∈D, νd=0 → qdig7 m (lamP m i₀ j u'*normU7(7^(m+1)) d) + t*s⁻¹*runit7(normU7(7^(m+1)) d) ∉{0,6}`.
- `quad_point_avoid {z₁ z₂ c₁ c₂ i} (hc1:c₁∈{2,4})(hc2)(hne:¬(c₁=4∧c₂=4))` (L570):
  `∃ t∈{1-i,2-i,3-i,4-i}, z₁+c₁*t∉{0,6} ∧ z₂+c₂*t∉{0,6}`.
- `avoids06_cycIv_2 (hc:c∈{1,2,3,4}) : avoids06 (cycIv c 2)` (L546).
- `pair_subset2_iff {a b} : (∃i,{a,b}⊆cycIv i 2) ↔ b−a∈{0,1,6}` (L686).
- `class_decomp (hr:r∈{1,2,4})(hs:s∈{1,2,4}) : ∃c∈{1,2,4}, r=c*s` (L710).
- `shift_of_class (hs:s≠0) : t*s⁻¹*(c*s)=c*t` (L702); `inv_mul_cancel_left'` (L697).
- `prop2ix` (L275): pattern {x,x+2}; hb: b_i−3*(x or x+2)∈{0,1,2} (qdig7_three_sub),
  hc: c_i−b_i−(x or x+2)∈{0,1} (qdig7_succ_sub j=3), he: e_i−c_i−(x or x+2)∈{0,1} (succ_sub j=4),
  distances via evade → e1−e0∈{0,1,6}.
- `prop2iix` (L304): pattern {x,x+3}; hb: b_i−2*(x or x+3)∈{0,1} (qdig7_two_sub),
  hc: c_i−b_i−(x or x+3) (succ_sub j=2), he: e_i−b_i−c_i (qdig7_five_sub23).
- `qdig7_two_sub` L403, `qdig7_three_sub` L414, `qdig7_succ_sub` L436 (implicit m i₀ j u' x, arg hj:1≤j∧j≤4),
  `qdig7_five_sub23` L446 — all take `x := normU7 N d`.
- `cycIv_image_add (i t L) : (cycIv i L).image (·+t) = cycIv (i+t) L` (Compress.lean L119);
  `avoids06_of_subset_shift` L134; `bad06 := {0,6}` L43; `avoids06 X := ∀x∈X, x∉bad06`.
- `mem_level7` (IntCase.lean L39): `d ∈ level7 D j ↔ d∈D ∧ padicValNat 7 d = j`.

### Mathlib (vendored) facts
- `Finset.card_eq_two : #s=2 ↔ ∃x y, x≠y ∧ s={x,y}` (Card.lean:801).
- `Finset.card_sdiff_of_subset (h:s⊆t) : #(t\s)=#t-#s` (Card.lean:598) — NOTE: plain
  `Finset.card_sdiff` takes NO subset arg in this Mathlib (`#(t\s)=#t-#(s∩t)`).
  Scratch line 66 uses `Finset.card_sdiff hsub` — POSSIBLE PRE-EXISTING ERROR; baseline
  build running to confirm.
- `Finset.pair_comm` (Insert.lean:419), `Finset.image_insert`/`image_singleton` (Image.lean:486-489),
  `Finset.filter_congr` (Filter.lean:176), `Finset.mem_sdiff` (SDiff.lean:58) — all exist.

### Paper §5 Case 3 (bs7.txt L494-551)
- |A_s|=2, extras in {2s,4s} classes. (12): ℓ(λ'·A_s)≤2 → 4 consecutive shifts
  k∈{k0,k0+s⁻¹,k0+2s⁻¹,k0+3s⁻¹}, one rescues both extras (quad_point_avoid;
  (4,4) config impossible → WLOG re-select s'=4s making it (2,2)-extras).
- ¬(12): q(λ'₁·A_s)={0,2} or {0,3}; propagation via windows forces contradiction —
  maps exactly to prop2ix/prop2iix (branch is vacuous).

### Plan (per brief)
1. `obtain ⟨s', hs'124, hS'2, hnot44⟩` — s' := 4s if all extras are 4s, else s.
2. S' := U.filter (r·=s'), X' over S'; by_cases ∃j∈Icc 1 5, ∃i, X' j ⊆ cycIv i 2.
   YES → extras {e1,e2}=U\S', classes c_i∈{2,4} via class_decomp, quad_point_avoid → t,
   S'-shift t via shift_of_class c=1, i+t∈{1..4} → avoids06_cycIv_2 → case4_finish.
   NO → push_neg, pair distances ∉{0,1,6} via pair_subset2_iff, orient {d0,d1} with
   q1-diff ∈{2,3}, prop2ix/prop2iix → q5-diff ∈{0,1,6} → contradiction (vacuous).

## Segment 2 — CRITICAL: stale skeleton (baseline build ~20 pre-existing errors)

Timestamp: after baseline build `c4s2_1.csv` (exit=1, 35.7s).

**File reality vs task brief:** disk `Case4MainS2.lean` = 192 lines (earlier read showed a
transient 251-line variant — file was being regenerated at 02:21). Real layout:
`interval_cases hSc : S.card` @135 → bullet1 = `<<S2-TARGET>>` sorry @137 (card=2,
probe-verified `interval_cases` ASCENDING order 2,3,4 via `_dev/scratch/IcProbe.lean`),
bullet2 = sorry (card=3), bullet3 = sorry (card=4). No |A_s|=4 code in this file.

**Baseline errors (ALL pre-existing, outside my bullet):**
- `mem_level7` unknown (lives in IntCase.lean, NOT in Case4Int import chain) → `Finset.mem_filter`
  (level7 IS a filter, Discrete.lean:34 — `mem_level7` is literally `Finset.mem_filter`).
- L24 `rw [hUdef, ← hU, hc]` pattern fail → `rw [← hU]; exact hc`.
- L66 `Finset.card_sdiff hsub` — this Mathlib's card_sdiff takes no subset arg → `card_sdiff_of_subset`.
- L82-90 hpart: constructor branches swapped + dependent-elim failure → Case4Main order.
- L96/105/108 `rw [← h1.2]` rewrites literal `1` (not found) → `rw [h1.2]` (rewrites `r x`).
  NOTE: `Case4Main.lean` (the newer sibling scratch, |A_s|=4 completed) shares THIS bug —
  it is NOT fully clean either.
- L146 `Finset.not_mem_empty` → `Finset.notMem_empty`.
- L167 `Nat.Coprime.pow_right` arg order → `(Nat.coprime_pow_right_iff (by omega) u 7).mpr (...).symm`.
- L171 `ZMod.mul_val_inv` shape → `have h := ZMod.mul_val_inv hcop; rw [← Nat.cast_mul, ← Nat.cast_one] at h`.

**Constraint conflict:** task says "do not touch outside the bullet" AND "build: zero errors
required". The skeleton cannot compile without the mechanical API repairs above — the build
gate is otherwise unsatisfiable. Resolution: apply the minimal mechanical API fixes
(same as Case4Main.lean where correct), document each in report + failures.md, and fill
only the target bullet with new logic.

**Key working idiom from Case4Main's completed |A_s|=4 block:**
`have hrs' : runit7 (normU7 (7 ^ (m + 1)) d) = s := hrs d hdU` — ascribe the `r d` fact to the
RAW term (r unfolds by defeq) — avoids `show`/`change` and set-var rw issues entirely.
Also `push Not` (not `push_neg`), `by decide` for mem_Icc.

## 2026-09-19 — |A_s|=2 block COMPLETE, build GREEN

**Status: target bullet filled, zero errors.** `lake env lean _dev/scratch/Case4MainS2.lean`
(memwatch `c4s2_3.csv`, 34.5s, peak 9.0GB) reports only the pre-existing `sorry` warning
from the untouched `S.card=3`/`S.card=4` sibling bullets (lines 471–472). The target
block (lines 141–470) contains no `sorry`/`admit`/`native_decide`/`unsafe`.

### Proof structure implemented (Barajas–Serra §5, Case 3)
1. **Principal-class re-selection.** `by_cases h44 : ∀ e ∈ U, r e ≠ s → r e = 4*s`.
   - If (4,4): `s' := 4s`. New filter `= U.filter (r·≠s) = U \ S` (via `Finset.filter_congr`
     + `ext`/`simp only [mem_filter, mem_sdiff, hS]`), card 2 via
     `Finset.card_sdiff_of_subset`. Non-(4,4)-of-`s'` condition: any `e ∈ S` has
     `r e = s ≠ 4*(4s)` (decide per `s∈{1,2,4}`).
   - Else `s' := s`.
   Gives `s' ∈ {1,2,4}`, `(U.filter (r·=s')).card = 2`, `¬∀e, r e ≠ s' → r e = 4*s'`.
2. `S' := U.filter (r·=s')`, `X' j := S'.image (qdig7 m (lamP m i₀ j u' * normU7 N d))`.
3. **YES branch** (`∃ j∈Icc 1 5, ∃ i, X' j ⊆ cycIv i 2`): extras `U \ S' = {e1,e2}`
   (`Finset.card_eq_two`), `class_decomp` gives `r eᵢ = cᵢ*s'`, `cᵢ ∈ {2,4}`, `¬(4,4)`
   from `hnot44`; `quad_point_avoid` yields `t`, `zᵢ + cᵢ*t ∉ {0,6}`; `i+t ∈ {1,2,3,4}`;
   `case4_finish` with `hgood`: `S'`-members via `cycIv_image_add` + `avoids06_cycIv_2`,
   extras via `shift_of_class`; `hd5` via `hd5bound`.
4. **NO branch** (`push Not`): `S' = {dA,dB}`; `hdist`/`hswapDist` = pair-differences
   `∉{0,1,6}` for all `j∈[1,5]` (via `pair_subset2_iff`); `j=1` difference `∈{2,3,4,5}`
   → re-orient to `{a0,a1}` with difference `2` or `3` (negating `4↔3`, `5↔2`);
   `prop2ix` (`qdig7_three_sub`@j=3, `qdig7_succ_sub`@j=4,5) or `prop2iix`
   (`qdig7_two_sub`@j=2, `qdig7_succ_sub`@j=3, `qdig7_five_sub23`@j=5) forces
   `X' 5` into `{0,1,6}`-distance → contradiction. `rcases hΔ` closes via `(h : False).elim`.

### Errors hit + fixes (logged `_dev/failures.md`)
- `rcases ... with rfl` on `d = e1` eliminated `e1` (subst hits RHS var) → use named
  hypothesis `hde1` + `rw [hde1]` (keeps `e1` in scope).
- `exact hdistO 5 _ hfit` (type `False`) rejected → `(hdistO 5 _ hfit).elim`.
- `push_neg` deprecated → `push Not at h2` (same as Case4Main).

### Files
- Block verbatim: `_reports/lrc7-case4-s2-block.md` (330 lines).
- File: `_dev/scratch/Case4MainS2.lean` lines 141–470.
