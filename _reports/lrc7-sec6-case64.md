
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

---

## Session 2 (2026-10-07) — dependency audit + design

### Landed signatures confirmed (all in import closure of Case5mTop+Case5mL9b+Case5mL10)
- `lemma11` (Case5mL10:934): labels A1 = {d1,d2,d3}, disjunction over `elevel7`
  (effective level, `e=0` ↦ m+1). 3-way: `l13>l23=l12` | `l13=l23`+`r13=2r23` |
  `l13=l23`+`r13=3r23`+`r13∈{±s}`.
- `lemma9_i'` (Case5mL9b:603): distinct padicValNat levels, both `e≠0` →
  λ with all pair-digits ∈{0,1,6} AND `apLen(q-image) ≤ 2`. No <m needed.
- `lemma9_i` (Case5mL9:281): same + both levels <m → pair-digits {0,6}, apLen≤2.
- `lemma7_i` (Case5mCases:131): twoX pair, `0<ν(e)<m` → λ (Λ_h) with
  `ẽ ∉ X` for `apLen X ≤ 4`. Multiplier OPAQUE (∃-packed).
- `lemma7_ii` (Case5mCases:197): twoX pair, `ν(e)=m`, `r(e) ∉ X∪(X+1)` →
  `ẽ ∉ X`; implements q(λ·7d)=6 branch giving `ẽ∈{r−1,r}`.
- `lemma12` (Compress): `A₁ ⊆ cycIv 1 (apLen A₁)`, `1∈A₁`, `card A₂≤2` →
  `∃k∈{0,1,2}, avoids06 (A₁+k ∪ A₂+2k)`. Only needs card of A₂!
- `lemma6` (Compress:387): six (ℓ₁,ℓ₂,ℓ₄) cases — the (4,2,0) case needs
  `∀d'∈A₂, d'+1∈A₂ → 2−d'≠4` (paper's `ẽ35≠4`).
- `exists_lambda0_of_shift` (Case5mBase:222): realizes a ZMod7 shift `t` as
  `λ∈Λ₀` over a 3-class set `{s,2s,4s}`; `avoids06` of shifted filter-images.
- `good7_mul` (Case5mBase:137): `good7 m λ' (A.image (λ·)) → good7 m (λ'λ) A`.
- `exists_top_scalar_set` (Case5mBase:546): `ν(x)=m,x≠0,t≠0` → `c∈{1..6}` with
  `(c*x)%N = t.val*7^m`, `q(cx)=t`.
- `residN_top` (Case5mBase:524): `ν(x)=m → x%N = (q(x)).val*7^m`.
- `qdig7_eq_runit7_of_top` (Case5mCases:106): `ν(x)=m → q(x)=r(x)`.
- `qdig7_add_top_resid` (Case5mTop:347): `x%N=(y%N+k·7^m)%N → q(x)=q(y)+k`.
- `eMod7_smul` (Case5mL9:230, PUBLIC): `e(cx,cy)=(c·e(x,y))%N` for `r(c)≠0`.
- `eMod7_mul` (Case5mBase:646): same for `r(lam)=1`.
- `qdig7_multTop` (Discrete:246): `ν(x)=m → q(l*x)=l·r(x)`.
- `qdig_eMod_sub_etd7` (Case5mBase:453): `q(e)−ẽ∈{0,1,6}` unconditional.
- `qdig_eMod_sub_etd7_same` (Differences:447): `q(e)−ẽ∈{0,6}` same-branch.
- `exists_multLow_set_qdig` (Case5mBase:509): `ν(x)=j<m` → Λ_j sets q(λx)=c.
- `exists_multLow_one_set_seven'` (Carry:189): `q(λ·7d)` settable via Λ₁.
- `qdig7_two_eq_smul` (Carry:95): `q(7x)=0 → q(2x)=2q(x)` — THE MIRROR.
- `qdig7_two_eq_smul_add_one` (Carry:128): `q(7x)=6 → q(2x)=2q(x)+1`.
- `padicValNat_mul_seven` (Filtering:37): `¬7∣l → ν(l·d)=ν(d)`.
- `padicValNat_eq_of_mod` (Differences:230): `a%N=b%N,ν(a)≤m → νa=νb`.
- `eMod7_two_mul_left` (Case5mCases:69): `e(2x,y)=e(x,y)` for twoX (x,y).
- PRIVATE-but-needed (will clone): `eMod7_lt`, `rel_same`, `eMod7_same_eq`,
  `eq_resid_of_eMod7_eq_zero`, `eMod7_zmod_cast` (ZMod N cast of eMod7).

### Design decisions
- `case64` takes `h9ii` hypothesis (spec §3.5 lemma9_ii verbatim + j-indexed
  `apLen ≤ j` per orchestrator note). `lemma10`/`h10` NOT needed (card 3 uses
  lemma11 only).
- Bridge `case64_finish`: given `lam₁`, either `apLen X1 ≤ 3` (→lemma12(i)) or
  `∃i∈X1, X1 ⊆ cycIv i 4 ∧ apLen X1=4 ∧ ∃d'∈A2, 2i−q(λ₁d')∈{0,1,6}`
  (→lemma12(ii) after normalizing `t'=1−i`); then `exists_lambda0_of_shift`
  with `t=t'+k` on `B=(A1∪A2).image (λ₁·)`, `s'=r(λ₁)·s`; closes via
  `good7_mul`. `min_cover_mem` lemma: min-cover start `i∈X` automatically
  (else X⊆cycIv(i+1)(L−1) contra).
- lemma12 route subsumes paper's lemma6 route: `card A₂≤2` suffices, no
  `apLen X2=2`/renaming needed. So the top-top branch only needs
  `ẽ(anchor,d')∈{0,1,6}` for the anchor = element mapping to interval start.
- Top normalization: `ν(e)=m` → `e=r.val·7^m` exactly → after scalar c,
  `e'=(c*r).val·7^m` → `q(cx)=q(cy)+c*r` EXACT via qdig7_add_top_resid.
  So `X1={Q,Q+u,Q+3u}` for `u=c·a` (a=r(e23)); `apLen=4` iff u≠0 (decide).
- Anchor/offset table: u∈{1,3}→i=Q,anchor=d3,off=0; u∈{4,5}→i=Q+u,
  anchor=d2,e(anchor,d')=e_{3,d'}+2·e23 (off=2a); u∈{2,6}→i=Q+3u,anchor=d1,
  e(anchor,d')=e_{3,d'}+2·e13 (off=6a). Residue arithmetic via cloned
  `eMod7_zmod_cast` → `e(d2,d4)=(e34+2e23)%N` etc.
- Λ_j (j<m) preserves pure-top e-residues verbatim: `(λ·v·7^m)%N=v·7^m`
  since `λ−1` divisible by 7 → preserves X1-shape {Q,Q+u,Q+3u} exactly.
  ⇒ need explicit-multiplier variants of lemma7_i/ii returning `∃k<7`.
- Top-top choice lemma (finite, decide over ZMod7): ∀aβγ≠0 ∃c≠0:
  `u=ac∈{1,3}∧(cγ∈{0,1,6}∨cβ∈{0,1,6})` ∨ `u∈{4,5}∧(c(γ+2a)∨c(β+2a))` ∨
  `u∈{2,6}∧(c(γ+6a)∨c(β+6a))`. **Python-verified all 216 triples (incl β=γ)**;
  96 configs strictly need r'=6 (mirror branch), 0 strictly need 1 or 0.
- `etd_avoid_016` local: twoX pair, ν(e)=m, r(e)∈{1,6} → ∃k<7 with
  `ẽ((1+k7^{m−1})d,(1+k7^{m−1})d')∈{0,1,6}` — r=1: q(λ·7d)=6 branch
  (lemma7_ii pattern → ẽ∈{0,1}); r=6: q(λ·7d)=0 mirror via
  `qdig7_two_eq_smul` → ẽ∈{6,0}.
- `e'=0` (r'=0 incl. base+off·a=0): `q(e')=0 → −ẽ∈{0,1,6} → ẽ∈{0,1,6}` direct.
- `ν(e34)=ν(e35)=m` also needs `e34≠0∧e35≠0` (implied). `β=γ` allowed (e45=0).

### Failure-ledger note (carried from summary)
Earlier finite claims for the top-top branch were wrong (bad inverse table,
anchor-insensitive formulations); corrected enumeration: restricted
strategies leave 36–72 unsolved; `r'∈{0,1,6}` + anchor-offset covers all.

## 2026-09-18 — plan revision: lemma9_ii must be PROVEN (no h9ii param)

`case5m_dispatch`'s `hc64` (Case5mTop:839) fixes the dispatcher-facing
`case64` signature — **no `h9ii` hypothesis** — so lemma9_ii must be
proved locally as `lemma9_ii64`.  Since §6.4 only needs `apLen ≤ 3`
(Lemma 12(i) route), a weaker form suffices:

- **j = 3** (`r13 = 3r23`): single `Λ_h` multiplier with `k = u·a⁻¹`
  (`a = r23`); `q(λe23) = qx+u`, `q(λe13) = qy+3u`; pair-digit fuzz
  `δ ∈ {0,1}` absorbed by the decide lemma
  `lemma9_ii3_table : ∀ qx qy, ∃ u, ∀ δ1 δ2 ∈ {0,1},
    apLen {0, qx+u+δ1, qy+3u+δ2} ≤ 3`.
  Python check: all 49 (qx,qy) admit a `u` covering all 4 carry combos.
- **j = 2** (`r13 = 2r23`): paper two-step — `e := eMod7 m e23 e13`
  (twoX pair of residues; `r(e) = 0` so `7 ∣ e` when `e ≠ 0`);
  normalize `q(λ₁e) = 0` (`ν(e) < m`, `exists_multLow_set_qdig`) or
  `(λ₁e)%N = 7^m` (`ν(e) = m`, `exists_top_scalar_set`); then
  `ẽ(λ₁x,λ₁y) ∈ {0,1,6}` (Lemma 4 bound; the `7^m` subcase needs the
  sharp `ẽ ∈ {0,1}` bound `etd7_of_pure_block'` — `q(v) = q(2u)−1` via
  `2u+6·7^m` arithmetic + `qdig7_smul_carry`); `λ₂ ∈ Λ_h` sets
  `q(λ₂λ₁x) ∈ {0,6}` (target `0` if `ẽ ∈ {0,1}`, `6` if `ẽ = 6`);
  `ẽ`-invariance under `Λ_h` (`2r(u)−r(v) = 0` for twoX) gives
  `q(λ₂λ₁y) = 2q(λ₂λ₁x)−ẽ ∈ {0,6}`; then `q(Lb_i)−q(Lb_3) ∈ {0,1,6}`
  ⇒ `X ⊆ q₃+{0,1,6}` ⇒ `apLen ≤ 3`.  **No `y−x` borrow needed**
  (only `≤ 3`, not the paper's `≤ 2` — the `ẽ=1 ∧ f₂<f₁` corner that
  makes the paper's `q(λ'λ(y−x)) ∈ {0,6}` subtle is irrelevant).
- `ν(e) ≥ h+1` not needed; `e = 0` degenerates (`λ₁ = 1`, `q(e) = 0`).

## Session 3 (2026-10-09) — finishing Case5mC64

### Baseline state audit (surprise finding)

Task brief said "compiles except 2-3 sorries at 1077-1079" — FALSE on inspection.
`lake env lean` shows ~20 additional errors through the file, apparently from a
mathlib bump / mid-refactor (metavar defaulting, renamed lemmas, rw-order
breakage, a literal syntax error, `ZMod7` typos, `subst` eliminating d_i vars).

Error inventory (line → cause):
- 179: `Nat.mul_lt_mul_of_pos_right (ZMod.val_lt v) hN` produces `v*7^(m+1) < 7*7^(m+1)`; need `pow_succ'` + `0<7^m`.
- 187-188 (`qdig_eq_add_of_e_top`): `rw [Nat.add_mod_right]` closes goal (`exact` has no goals); `h2` addends commuted vs `hmodeq` target.
- 257 (`nu_pow7`): leftover `0 + m = m` — needs `zero_add` in rw chain.
- 428,493 (`etd_avoid_016`): `exists_multLow_one_set_seven' (by omega) hd hpos c` — implicit `?m` defaults to `d'`; pin `(by omega : 0 < m)`.
- 480: `linear_combination hb` wrong sign → `-hb`.
- 582,592 (`etd_top_step`): literal `ZMod7` (missing space) — unknown identifier.
- 655 (`mem_016_of_not_2345`): `fin_cases x <;> simp_all` leaves all 7 goals; use `revert h; decide`.
- 671 (`min_cover_mem`): `ring_nf` no progress (line ~671-676).
- 768-796 (`case64_tail` hfilt1/2): rcases on `x ∈ B` where `B` a `set`-var → Quot.lift; must `Finset.mem_image.mp` first.
- 802: `Finset.eq_empty_iff_forall_not_mem` unknown constant → `Finset.filter_eq_empty_iff`.
- 828-833 (`case64_tail` end): `rw [Finset.image_image]` hit LHS (X1 unfolds) not RHS — use conv_rhs; missing `Finset.image_empty`/`union_empty` for the A4=∅ union.
- 896 (`case64_finish4` hX1): image_insert/image_singleton rw order hits outer image first; use simp only chain.
- 916-933: `subst ha` eliminates `d_i` (RHS var) → use `anchor` in branch bodies.
- 988: `lemma11 hA1 s ...` leaves `{m}` implicit unassigned → `?m.225` metavars in hdis; pin `(m := m)`.
- 1068: `rw [(ZMod.natCast_eq_zero_iff _ _).mp]` invalid (proof term not eq); restructure hrc via `hrcast`.
- 1071: `hsc` type mismatch `runit7 c` vs `↑c` — prove via `runit7_mul` + `hrcast`.
- 1074: syntax error in `rwa [...] at hrc ⊢` — rewrite hrel13' cleanly.
- 1077-1079: the 3 real sorries (case-i ν(e23)=m normalization; case-i e13≠0 via lemma9_i'; case-ii ratios).
