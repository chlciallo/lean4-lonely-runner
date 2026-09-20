# lrc7-sec6-case61 — implementation log (Case5mC61.lean)

Task: prove `case61` — Barajas–Serra §6.1, five level-0 elements sharing one
residue class `s ∈ {1,2,4}` admit a good multiplier.  New file only:
`Research07/LRC7/Case5mC61.lean` importing `Case5mTop` + `Case5mL9b`.
`h10`/`h9ii` arrive as hypotheses (Lemma 10 / Lemma 9(ii) still being
finalized by another agent).

## 2026-09-19 — survey + finite verification

### API survey results (signatures confirmed)

- `case61_caseB` (Case5mTop.lean:563): handles the `ν(E) ⊆ {m}∪{0}`-case —
  `htop : ∀ x∈A, ∀y∈A, x≠y → eMod7 m x y = 0 ∨ padicValNat 7 (eMod7 m x y) = m`,
  needs `hm : 0 < m`, `hcard : A.card ≤ 5`, `hs : s ≠ 0`, `hcls`.
- `good7_of_smul_apLen` (Case5mTop.lean:1104): `apLen ((A.image (lam'*·)).image (qdig7 m)) ≤ 5`
  → `∃ lam, ¬7∣lam ∧ good7 m lam A` given `¬7∣lam'`.
- `exists_lambda0_qdig_06` (Case5mTop.lean:1141): `apLen (B.image (qdig7 m)) ≤ 2`
  on a level-0 single-class `B` → `∃ lam ∈ multLow7 m 0, ∀ d∈B, qdig7 m (lam*d) ∈ {0,6}`.
  Exactly the Λ₀-shift step.
- `lemma9_i'` (Case5mL9b.lean:603): triple, `ν(e13)≠ν(e23)`, both `e≠0` →
  `∃ lam, ¬7∣lam ∧ ∀ pairs qdig(eMod7) ∈ {0,1,6} ∧ apLen image ≤ 2`.  No `<m`
  hypotheses needed (handles the `ν=m` boundary).
- `exists_multLow_set_qdig` (Case5mBase.lean:509): `ν(x)=j<m, x≠0 → ∃k<7,
  qdig7 m ((1+k·7^{m−j})·x) = c`.
- `exists_top_scalar_set` (Case5mBase.lean:546): `ν(x)=m, x≠0 → ∃0<c<7,
  (c·x)%N = t.val·7^m ∧ qdig7 m (c·x) = t`.
- `eMod7_mul` (Case5mBase.lean:646): `runit7 lam = 1 → eMod7 m (lam·x)(lam·y)
  = (lam·eMod7 m x y)%N`.  `eMod7_smul` (Case5mL9.lean:230) same for
  `runit7 c ≠ 0`.
- `qdig_eMod_sub` (Case5mBase.lean:441): same-rel pair →
  `q(e) − (q(x)−q(y)) ∈ {0,6}`.
- `qdig7_eq_cast_div` (Discrete.lean:280): `qdig7 m y = ↑(y/7^m)`.
- `qdig7_congr` (Filtering.lean:31): `a%N = b%N → qdig7 m a = qdig7 m b`.
- `qdig7_lambda0` (Case5mBase.lean:147): `ν(d)=0 → qdig7 m ((1+k·7^m)·d)
  = qdig7 m d + k·runit7 d`.
- `enu7_le_of_ne` (Case5mBase.lean:115): `e≠0 → ν(e) ≤ m`.
- `residN_multLow7` (Discrete.lean:177): `j<ν(x) → (1+k·7^{m−j})·x %N = x%N`.
- `apLen_pair06_le` (Case5mBase.lean:1088, public): `¬(a=2∧b=4) ∧ ¬(a=4∧b=2)`
  → `apLen {0,6,a,b} ≤ 5`.
- Private-but-needed (clone): `qdig7_sub_resid` (exact borrow formula,
  Case5mL9.lean:138), `residue_decomp`, `mul_pow_add_div`, `natCast_sub_add`,
  `eMod7_lt`, `eMod7_self`, `eMod7_neg_eq`, `apLen_mono'`, `rel_same`,
  `eMod7_zmod_cast_same`.
- `elevel7` machinery lives in Case5mL10 — NOT in our import chain (Top/L9b
  only); avoid it.

### Finite claims verified by Python (all clean)

- `{0,6,p,q}` has `apLen ≤ 5` iff `{p,q} ≠ {2,4}` (49 pairs, 0 bad).
- `apLen {0,1,2,5,6} = 5`, `apLen {0,1,4,5,6} = 5`.
- `q∈{2,4}, c∈{0,1,2} → 3q+c ∈ {0,1,5,6}` (mod 7).
- `x ∈ cycIv i 2 → x + (6−i) ∈ {0,6}`.
- **Nat-valued ×3 dichotomy** (the real `f < 7^m` version — the repo's
  `case61_dichot`/`'` are stated over normalized `ZMod 7` f-values and CANNOT
  be instantiated directly for `m ≥ 2` since `f.val`-order ≠ real order and
  `⌊3f.val/7⌋` ≠ `⌊3f/7^m⌋`; must prove a fresh nat version):
  `qᵢ∈{0,6}, fᵢ<7^m, qᵢ−qⱼ−borrow(fᵢ<fⱼ) ∈ {0,1,6}` (6 ordered pairs)
  ⇒ `{3qᵢ+⌊3fᵢ/7^m⌋}` ⊆ `{0,1,2,5,6}` or ⊆ `{0,1,4,5,6}`.
  Verified exhaustively: m=1 (1526 valid configs, 0 bad), m=2 (477848, 0 bad);
  `{0,6}` envelope at m=2 also 0 bad.
- Negation digit: `q(N − (6·7^m+f)) = 1` iff `f=0`, else `0` (m=1,2,3).

### Proof plan

`case61`: `hs0 : s≠0` (from `s∈{1,2,4}`); `hsame` all-pairs `residueRelOf =
same` (equal runit7 `s`, nonzero).  `by_cases htop`: Case B → `case61_caseB`.
Case A (`¬htop`): witness `(u,v)` with `e≠0`, `ν<m`.  Apply `h10` at `A1 := A`
→ `d1..d4` distinct + (i) `ν(e21)>ν(e31)` or (ii) uniform `ℓ` + ratios.
Extract `d5` via `card_sdiff` (card `5−4=1`).

- (i) `e31≠0`: `lemma9_i'` on `(d2,d3,d1)` → pairs `{0,1,6}`, `apLen≤2`.
- (i) `e31=0` (then `d3≡d1`, `ν(e21)≥1`): set `q(λ₁e21)=6` via
  `exists_multLow_set_qdig`/`exists_top_scalar_set`; pairs via
  `qdig_eMod_sub` + `eMod7` congruence lemmas (avoids negation-residue
  analysis); `apLen≤2` since `q(λd3)=q(λd1)`.
- (ii) `e21≠0` (then `e31,e41≠0` via `r(·)=j·r(e21)`): `h9ii` on `(d2,d3,d1)`
  at `j=2` (`r(e31)=2r(e21)`, `ν(e31)=ℓ<m`) → pairs `{0,6}⊆{0,1,6}`,
  `apLen≤2`.
- (ii) `e21=0` (then `e31=e41=0`, `d2,d3,d4≡d1`): `e51≠0` else `htop`;
  `ν(e51)=ℓ<m`; Λ_ℓ sets `q(λ₁e51)=6` → `q(λ₁d5)−q(λ₁d1)∈{0,6}` →
  `q(λ₁A)⊆{q(λd1),q(λd5)}` `apLen≤2≤5` → `good7_of_smul_apLen` directly.

Tail (shared): `exists_lambda0_qdig_06` on `B=(triple).image(λ₁·)` → `λ₀∈Λ₀`
with `q(λ₀λ₁bᵢ)∈{0,6}`.  Pair bound transport: `eMod7 (λ₀u)(λ₀v) = eMod7 u v`
verbatim for same-class pairs (Λ₀ kills `7^m`-multiples of `e`, and `7∣e`
since `e ≡ λ₁(x−y) ≡ 0 mod 7`).  Borrow formula `qdig7_sub_resid` (cloned)
gives the 6 constraints.  `{q4',q5'}≠{2,4}` → `apLen_pair06_le` +
`good7_of_smul_apLen` (λ'=λ₀λ₁).  `={2,4}` → `qdig7_three_mul` (exact
`q(3x)=3q+⌊3f/7^m⌋`) + `case61_dichot_nat` → `apLen≤5` →
`good7_of_smul_apLen` (λ'=3λ₀λ₁).

`h9ii` signature adjustment vs task: `apLen ≤ j` (paper-faithful, needed:
`≤3` cannot pin `{0,6}`), pair bound conditional `j=2 → {0,6}` plus
unconditional `{0,1,5,6}` (matches paper/`lemma9_ii` j-branches).
