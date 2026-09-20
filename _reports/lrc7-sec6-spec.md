# lrc7-sec6-spec.md — Formalization spec for `Case5m.lean` (BS7 §6: `|A|=5, m>1`)

Report maintained incrementally per `_reports` protocol; final assembly
2026-09-18 (single-thread dig; intermediate findings persisted in
`_dev/sec6spec/verify.py` and `_dev/sec6spec/ejc_pages.txt`).

Task: specification dig only — no Lean implementation, no builds.
Deliverable: a theorem-signature-level plan for `Research07/LRC7/Case5m.lean`
sufficient to write the file without re-deriving the proof.

Sources read:
- `_external/bs7-ejc.txt` §6 (lines 470–800), §2 notation (lines 60–240),
  §4 overview (line 342 area), §5 (Λ′ family, eqs. 8–10).
- `_external/bs7-ejc.pdf` — extracted to `_dev/sec6spec/ejc_pages.txt`;
  used to resolve all pdftotext corruptions (§0.2, §4.6 R2 verdict).
- `_external/bs7.txt` (arXiv HTML — better symbol rendering; used to repair
  pdftotext-mangled formulas, see §0.2).
- `_reports/bs7-structure.md` §6 + version-discrepancy table.
- Interfaces: `LRC7/Discrete.lean`, `Filtering.lean`, `Differences.lean`,
  `Compress.lean`, `Finite.lean` (`lrc7_m1`), `Case4.lean` (style model).
- `_reports/lrc7-interfaces.md` (frozen contracts), `_reports/lrc7-compress.md`.

Independent verification: `_dev/sec6spec/verify.py` — every finite `ZMod 7`
claim quoted below was brute-force checked; results marked **[verified]**.

---

## 0. Standing facts

### 0.1 Global hypotheses (what the caller `IntCase` will supply)

`m = max ν₇(D) ≥ 2` (paper: `m > 1`), `N = 7^{m+1}`.
`A = D₇(0)`, `|A| = 5`, all elements positive, `¬ 7 ∣ d`.
After sign-flip preprocessing: residues `(A)₇ ⊆ {1,2,4}` (i.e. `runit7 d ∈ {1,2,4}`).
The sixth element `d6` has `ν₇(d6) = m` (top level; automatically good by
`absModN_top_ge7`).

`m ≥ 2` is *used* in: Lemma 7(ii) (`ν(7d) = 1 < m`), §6.3 (ii.2) `h=m`
(`q(7d₃) = 4ε₁+2ε₂`), §6.6(a) (`q(7d₅) = 4ε₂+2ε₁`). All are `Λ₁`-moves on
`ν = 1` elements — the formal statement should carry `hm : 2 ≤ m`.

### 0.2 Corrections to the EJC-txt found during this dig (implementers: trust these, not the raw txt)

The EJC PDF (`_external/bs7-ejc.pdf`, extracted to `_dev/sec6spec/ejc_pages.txt`)
was consulted for all corrupted passages; the entries below are the verdicts.

| Loc | EJC-txt reading | Correct statement | Status |
|---|---|---|---|
| §6.5 (i)/(ii.1) | `\|e45\| ≤ 5N/14 ⇒ \|2e45\| ≥ 2N/7`; `\|e45\| ∈ [2N/7,5N/14] ⇒ \|3e45\| ≥ N/7` | PDF/arXiv: `\|e45\|_N ≥ 5N/14 ⇒ \|2e45\|_N ≤ 2N/7`; `\|e45\|_N ∈ [2N/7,5N/14] ⇒ \|3e45\|_N ≤ N/7` | **[verified]** numerically for N = 49, 343. PDF confirms the `≤`-directions. |
| §6.5 opener | "`A2 = {d4,d5}`" | Notation slip in the paper itself: the 2-element class is `A4` (residue `4s`) — otherwise the case would be §6.4 and Lemma 6(ii) `(4,0,2)` would not apply. | confirmed via PDF |
| §6.5 (ii.1)(b) | `q(A4) = {i,i+4}` | `i = q(d5)`, `q(d4) = i+4` (exact — `e45 = 4N/7` level `m` forces `f4=f5`). Then `i∈{2,6}` ⇔ `q(d4)∈{6,3}` ⇔ `ẽ(d3,d4) = 2q(d4)−1 ∈ {4,5}` | **[verified]** exact match to paper's "{4,5}" |
| §6.6(a) pair formula | `q(λ_k·A2) = {2k−ẽ, (2k−1)−ẽ}` (printed in EJC *and* arXiv) | Printed formula gives `{(3,2),(3,4),(4,4),(5,4),(5,6)}` ≠ (16). Correct: `q(d3) = q(d4)+1` **exactly** — `e34 = N/7` at level `m` forces `f3 = f4` (no borrow possible) — so `A2 = {2k−x, 2k−x+1}` yielding the paper's `{(4,2),(4,4),(5,4),(6,4),(6,6)}` | **[verified]**; the printed `(2k−1)` is a typo for `(2k+1)` |
| §6.6(b) | EJC-PDF: `q(λ_k d5) = 2q(λ_k d4) − ẽ(d4,d5) = 2k − ẽ(d4,d5)` | confirmed (the garbled alternative in earlier notes was wrong) | confirmed via PDF |
| §6.6 same-level `r`-differs | "`q(λe12), q(λe34) ∈ {0,1,5,6}`; since `λe12 ≠ 5N/7` and `λe34 ≠ 5N/7`, (15) holds" | `{0,1,5,6}` alone gives **128 counterexamples** (verified) — insufficient; `{0,6}` gives 0. Budget `Σ|F| = 10 > 6` blocks a naïve `filtered7`. See §4.6 for the `f = e12−2e34` reconstruction + residual-band analysis. | **genuine reconstruction needed — flagged R2** |
| §6.1 | `{q(d₄),q(d₅)} = {2,4} ⇒ ℓ(A1) ≤ 5` (EJC); `≠ {2,4} ⇒ ℓ ≤ 4` (arXiv) | Both wrong/mangled. Truth: `apLen({0,6,a,b}) ≤ 5` **iff `{a,b} ≠ {2,4}`** (the only failing pair is `{2,4}`, giving ℓ = 6). So: `≠{2,4}` → ℓ ≤ 5 done; `={2,4}` → the ×3 argument. | **[verified]** by exhaustive check of the 49 pairs. |
| §6.1 ×3 step | "either q(3·A1) ⊆ {0,1,2,5,6} or ⊆ {0,1,4,5,6}" | True **only under the difference condition** `q(B−B) ⊆ {0,6}` (which Lemma 9/Remark 8 supplies): `f₀ < f₆` coupling forbids the joint bad carries. Under free carries it has 540 counterexamples. | **[verified]** 0/26754 failures in the `N=49` toy model with `q(B−B) ⊆ {0,6}` enforced. |

---

## 1. Notation map (paper → existing Lean)

| Paper | Lean | Status |
|---|---|---|
| `ν₇(x)` on elements | `padicValNat 7 d` | ✅ |
| `ν(e)` on differences | `padicValNat 7 (eMod7 m x y)` | ✅ usable; **edge**: `eMod7 = 0` (difference ≡ 0 mod N, i.e. `ν ≥ m+1`) gives `padicValNat 0 = 0` — needs `≠ 0` guards in hypotheses. See §3.1. |
| `r(x)` | `runit7 x` | ✅ |
| `q(x)` leading digit | `qdig7 m x` | ✅ |
| `(x)_N`, `\|x\|_N` | `x % N`, `absModN x N` (LRC5) | ✅ |
| `Λ_{j< m}` | `multLow7 m j = {1+k·7^{m−j}}` | ✅ |
| `Λ_m` | `multTop7 = {1,…,6}` | ✅ |
| `ℓ(X)` | `apLen (X : Finset (ZMod 7))` | ✅ `apLen_le_iff` |
| `q(λ_k d) = q(d)+k·r(d)` (eq. 10) | `qdig7_multLow` with `j = 0` | ✅ (`hx : padicValNat 7 d = 0`) |
| eq. (2) verbatim residues | `residN_multLow7` | ✅ |
| eq. (3) level-`j` shift | `qdig7_multLow` | ✅ |
| eq. (5)/(9) `q((j+1)x) ∈ q(jx)+q(x)+{0,1}` | `qdig7_add_one` | ✅ one-step; **iterated `{0,…,j}` bound missing** (§3.4) |
| `e(x,y)` | `eMod7 m x y` (residue mod `7^{m+1}`) | ✅ |
| `ẽ(x,y)` | `etd7 m x y` | ✅ |
| Lemma 4(i) `ẽ` Λ-invariance | `etd7_multLow_same` (same level `j`), `etd7_multLow_low` (`j < ν`) | ✅ |
| Lemma 4(ii) `\|ẽ−q(e)\|≤1`, same-`r` | `qdig_eMod_sub_etd7_same` → `∈{0,6}` | ✅ same-r only; **twoX/twoY case missing** (§3.2) |
| Lemma 2 (filtering) | `filtered7` (+`filtered7_good`, `exists_k_all_good7`, `exists_top_scalar`) | ✅ |
| Remark 8 | `remark8_i` (diffs ∈{0,±1} ⇒ `apLen (k·B) ≤ k+1`), `remark8_ii` | ✅ on `ZMod 7` image sets |
| Lemma 5 | `lemma5` (incl. `hord` ordering + (3,1,1)-exception disjunct) | ✅ |
| Lemma 6 | `lemma6` (six triples, anchor `1 ∈ A₁`, `A₁ ⊆ cycIv 1 ℓ`) | ✅ |
| Lemma 12 | `lemma12` | ✅ |
| `q(λA)∩{0,6}=∅` | `avoids06` on shifted images; `exists_shift_avoid` | ✅ `ZMod 7` level |
| Lemma 7 (`ẽ`-avoidance) | — | ❌ **missing** (§3.3) |
| Lemma 9 (3-compression) | — | ❌ **missing** (§3.5) |
| Lemma 10/11 (numbering) | — | ❌ **missing** (§3.6) |
| `λ′_j` top multipliers (§5) | — | ❌ **not needed in §6** — §6 uses only `Λ₀`, `Λ_m`, `Λ_h` (`1≤h<m`), and `Λ₁`-`7d` tricks. No `λ′_j` appears in §6 (the §5 `d5`-family is absent since `d6` is top-level and auto-good). |
| `q(7x)` = 2nd digit | — | ❌ **missing** (§3.7) |

---

## 2. The multiplier algebra — how "we may assume" formalizes

The paper's idiom "there is λ ∈ Λ_h such that P" / "we may assume P" must be
read as: **there exists a unit λ (product of Λ-elements) such that the scaled
configuration λ·A satisfies P**. Lean pattern: every lemma concludes
`∃ lam, ¬ 7 ∣ lam ∧ P (scaled data)`; composition is
`⟨lam₂ * lam₁, Nat.Prime.not_dvd_mul …, by rwa [mul_assoc]⟩`.
No `wlog` machinery is needed — just nested `obtain` + `∃`-intro.

**Stability rules** (why the paper's successive assumptions are sound —
implementers must respect this order):

1. `Λ₀ = multLow7 m 0` preserves *every* `e`-residue verbatim
   (`residN_multLow7`, since all `e`-differences have `ν ≥ 1 > 0`), and shifts
   `q(d) ↦ q(d) + k·r(d)` for level-0 `d` (`qdig7_multLow`, `j=0`). Class-s
   elements all shift by the same `k·s`, class-`2s` by `2ks`, class-`4s` by
   `4ks` — this is exactly the `t / 2t / 4t` shift structure in
   `lemma5/lemma6/lemma12` (the `s` parameter is a marker; the shift is
   `k·s` for unnormalized `λ_k = 1+k·7^m`).
2. `Λ_m = multTop7` scalars: `q(c·d) = c·r(d)` for level-`m` elements
   (`qdig7_multTop`) — used to normalize `e`-residues `e = tN/7`; on level-0
   elements `q(c·d) ∈ c·q(d) + {0,…,c−1}` (carry bound, §3.4).
   Multiplication by `c ∈ {1,…,6}` permutes the residue classes
   `s ↦ cs` — after a scalar, class labels rotate (used in §6.5 ×2/×3 and
   §6.2's `e15=3N/7` fallback).
3. `Λ_h` (`1 ≤ h < m`): preserves residues of elements at levels `> h`
   verbatim (`residN_multLow7`) — in particular all `e`-residues at level
   `m`; shifts `q(e)` of level-`h` differences bijectively
   (`qdig7_multLow`); **perturbs top digits of level-0 elements** by a
   carry-controlled amount (this is *how Lemma 7 works*). It is applied
   **before** the final `Λ₀` normalization; the needed `ℓ`-bounds survive
   because they are re-derived from the (preserved) `e`-residues, not from
   absolute digits.
4. Order convention used below: `Λ_m` normalize level-`m` `e`-residues →
   `Λ_h`-filtering/avoidance (Lemma 7, Lemma 2 on differences) →
   `Λ₀` final positioning (`q(A₁) ⊆ {1,…,ℓ}`, anchor `q(d)=1`) →
   `lemma5/lemma6/lemma12/exists_shift_avoid` finishing shift.
   `Λ₀` never disturbs any `e`-residue or `ẽ`-value… — careful:
   `ẽ(λ_k d, λ_k d')` under `Λ₀`: both `q`s shift by `k·r` —
   `ẽ` changes *predictably* (`etd7_multLow_same` shows invariance when the
   shift is `k·r(x)` on both — for level-0 pairs with `Λ₀`, `q(d)↦q(d)+k·r(d)`
   so `ẽ` shifts by `k·r(d)` or `2k·r(d)−k·r(d')` per case — the
   `lemma5`-exception `ẽ ∈ {2,4}` condition is on the *final* digits anyway).

**Residue/`runit7` bookkeeping under scalars**: `filtered7`'s λ is a product
of `Λ_{j<m}` elements, each `≡ 1 (mod 7)` — so `lam % 7 = 1` and
`runit7 (lam*d) = runit7 d` (needs a small corollary, §3.8). `multTop7`
scalars change `r(d)` to `c·r(d)` — after them, class labels must be
re-derived.

---

## 3. Missing infrastructure (gaps to fill *before* or *inside* Case5m.lean)

### 3.1 `e`-level helper

```lean
/-- ν of a difference residue; garbage when the residue is 0 (`ν(e) ≥ m+1`). -/
abbrev enu7 (m x y : ℕ) : ℕ := padicValNat 7 (eMod7 m x y)
```
Callers must carry `eMod7 m x y ≠ 0` where a level is used. (Alternative:
state hypotheses on `Int` differences `|2x−y|` etc. — heavier; residues are
consistent with existing `eMod7`.)

### 3.2 Lemma 4(ii), non-same case — MISSING

```lean
theorem qdig_eMod_sub_etd7_two {m x y : ℕ}
    (hrel : residueRelOf x y ≠ residueRel.same) :
    qdig7 m (eMod7 m x y) - etd7 m x y ∈ ({0, 1, 6} : Finset (ZMod 7))
```
(`q(e) ∈ ẽ + {−1,0,1}` for `e = 2x−y`/`2y−x`; borrow analysis exactly like
`qdig_eMod_sub_etd7_same` but two-sided.) Needed for *every* `ẽ∈q(e)+{0,±1}`
step (Lemma 7, all the `ẽ ≈ q(e)` transfers).

### 3.3 Lemma 7 — MISSING (belongs in `Differences.lean` or `Case5m.lean`)

```lean
/-- Paper Lemma 7(i): avoid a set X with ℓ(X) ≤ 4 when ν(e) < m. -/
theorem lemma7_i {m : ℕ} {d d' : ℕ}
    (hd : padicValNat 7 d = 0) (hd' : padicValNat 7 d' = 0)
    (hpos : 0 < d) (hpos' : 0 < d')
    (hrel : runit7 d' = 2 * runit7 d)              -- residueRelOf = twoX
    (hν : 0 < padicValNat 7 (eMod7 m d d'))
    (hνm : padicValNat 7 (eMod7 m d d') < m)
    {X : Finset (ZMod 7)} (hX : apLen X ≤ 4) :
    ∃ lam : ℕ, ¬ 7 ∣ lam ∧ etd7 m (lam * d) (lam * d') ∉ X
```
Proof sketch: `h = ν(e)`; choose `x ∉ X+{0,1,2}` (`apLen (X+{0,1,2}) ≤ 6` —
small `decide`-able helper `exists_avoid_three_translates`); set
`λ = 1+k·7^{m−h}` with `q(λe) = x−1` via `qdig7_multLow` (bijectivity of
`k ↦ q(e)+k·r(e)`); then `ẽ(λd,λd') ∈ q(λe)+{0,1,6} ⊆ Xᶜ` via §3.2 +
`eMod7_mul` (see below) + `residueRel_multLow`.

```lean
/-- Paper Lemma 7(ii): the `7d` trick, needs m ≥ 2. -/
theorem lemma7_ii {m : ℕ} (hm : 2 ≤ m) {d d' : ℕ}
    (hd : padicValNat 7 d = 0) (hd' : padicValNat 7 d' = 0)
    (hpos : 0 < d) (hpos' : 0 < d')
    (hrel : runit7 d' = 2 * runit7 d)
    (hν : padicValNat 7 (eMod7 m d d') = m)
    {X : Finset (ZMod 7)}
    (hr : runit7 (eMod7 m d d') ∉ X ∪ X.image (· + 1)) :
    ∃ lam : ℕ, ¬ 7 ∣ lam ∧ etd7 m (lam * d) (lam * d') ∉ X
```
Proof: `λ ∈ Λ₁` with `q(λ·7d) = 0` (or `6` for the mirrored branch — see
§6.5(b) usage) forces `q(λ·2d) = 2q(λd)` (no top carry, §3.7);
`λe = e` verbatim (`ν(e)=m>h=1`); `ẽ(λd,λd') = 2q(λd)−q(λd') ∈ q(e)+{0,6}`
via `qdig_eMod_sub_etd7_same` on the pair `(λ·2d, λ·d')` (same-r pair) —
`ẽ ∈ {r(e), r(e)−1} ⊆ Xᶜ` by `hr`. **The case `q(λ·7d)=6` analog gives
`q(λ·2d) = 2q(λd)+1` and `ẽ ∈ {r(e)+1, r(e)}` — the paper only cites
`r ∉ X ∪ (X+1)`; implementing both signs is safest** (the paper's text:
"similar argument … choosing λ ∈ Λ₁ such that q(λ(7d)) = 6 so that
q(λ(2d)) = 2q(λd)+1").

Ingredients needed (all small, all MISSING):
- `eMod7_mul`: `eMod7 m (lam*x) (lam*y) ≡ lam * eMod7 m x y` mod `7^{m+1}`
  when `runit7 lam = 1` (or generally with residueRel bookkeeping —
  for `Λ_h` elements `runit7 = 1`, `residueRel_multLow` preserves the case).
- `qdig7_seven_mul` / `qdig7_two_mul` (§3.7).

### 3.4 Iterated carry bound — MISSING

```lean
/-- eq. (5)/(9) iterated: q(c·x) ∈ c·q(x) + {0,…,c−1} for c < 7. -/
theorem qdig7_smul_carry {m c x : ℕ} (hc : c < 7) :
    qdig7 m (c * x) - (c : ZMod 7) * qdig7 m x ∈ (Finset.range c).image …
```
(i.e. `(qdig7 m (c*x) − c·qdig7 m x).val < c`; induction on `c` using
`qdig7_add_one`.) Used in §6.1 (×3), §6.2 (×2), §6.5 (×2,×3), and wherever
`q(j·d)` for `j ≤ 6` is bounded.

### 3.5 Lemma 9 — MISSING

```lean
/-- Paper Lemma 9(i): three same-class elements, different difference levels. -/
theorem lemma9_i {m : ℕ} {b1 b2 b3 : ℕ}
    (hpos : 0 < b1 ∧ 0 < b2 ∧ 0 < b3)
    (hunit : padicValNat 7 b1 = 0 ∧ padicValNat 7 b2 = 0 ∧ padicValNat 7 b3 = 0)
    (hsame : runit7 b1 = runit7 b2 ∧ runit7 b2 = runit7 b3)
    (hν : padicValNat 7 (eMod7 m b1 b3) ≠ padicValNat 7 (eMod7 m b2 b3))
    (he : eMod7 m b1 b3 ≠ 0 ∧ eMod7 m b2 b3 ≠ 0) :
    ∃ lam : ℕ, ¬ 7 ∣ lam ∧
      (∀ x ∈ ({b1,b2,b3} : Finset ℕ), ∀ y ∈ ({b1,b2,b3} : Finset ℕ),
        qdig7 m (eMod7 m (lam*x) (lam*y)) ∈ ({0,6} : Finset (ZMod 7))) ∧
      apLen (({b1,b2,b3} : Finset ℕ).image (fun d => qdig7 m (lam*d))) ≤ 2
```
(The difference-condition conclusion is needed for the §6.1 carry coupling;
the `apLen ≤ 2` follows from it via `remark8_i` at `k = 1`… actually the
paper applies Remark 8(i) to get `ℓ(λB) ≤ 2`; in Lean: the q-difference
condition `q(λ(bi−bj)) ∈ {0,6}` gives pairwise digit-diffs ∈ {0,±1} via
`qdig_eMod_sub_etd7_same`, then `remark8_i` with `k=1`.)
Proof: `filtered7` on the two differences `{x, y}` (each `|F| = 2`, sum 4 ≤ 6)
setting `q(λx) = q(λy) = 6`; then `q(λ(x−y)) ∈ {0,6}` by the {0,6}-arithmetic
of same-q pairs — needs a small lemma: `q(a) = q(b) = 6 ⇒ q(subMod a b) ∈ {0,6}`
… wait actually `{0,6}` requires the f-order analysis (§0.2 row 5):
`q(bi−bj) ∈ {0,6}` iff lower digits ordered correctly — the paper gets it
directly from `q(λx) = q(λy) = 6` plus `q(λ(x−y)) ∈ q(λx)−q(λy)+{0,6} = {0,6}`.
Verify: `x−y` difference of two level-0 elements — `e(b1,b2)` same-r:
`q(e) − ẽ ∈ {0,6}`, `ẽ = 6−6 = 0` → `q(e) ∈ {0,6}` ✓ via
`qdig_eMod_sub_etd7_same`. Good — clean.

```lean
/-- Paper Lemma 9(ii): same level h < m, r(y) = j·r(x), j ∈ {2,3}. -/
theorem lemma9_ii {m : ℕ} {b1 b2 b3 : ℕ}
    (hpos : …) (hunit : …) (hsame : …)
    (h : padicValNat 7 (eMod7 m b1 b3) = padicValNat 7 (eMod7 m b2 b3))
    (hm' : padicValNat 7 (eMod7 m b2 b3) < m)
    {j : ℕ} (hj : j = 2 ∨ j = 3)
    (hr : runit7 (eMod7 m b2 b3) = (j : ZMod 7) * runit7 (eMod7 m b1 b3)) :
    ∃ lam : ℕ, ¬ 7 ∣ lam ∧
      qdig7 m (eMod7 m (lam*b2) (lam*b3)) ∈ ({0,5,6} : Finset (ZMod 7)) ∧
      apLen (({b1,b2,b3} : Finset ℕ).image (fun d => qdig7 m (lam*d))) ≤ j
```
(`j=2`: the `e = 2x−y`/`ẽ ∈ {0,1,6}` route + `q(λx) ∈ {0,6}`; `j=3`: the
`3q(y)+5q(x)` table → `q(λy) ∈ {0,5,6}`, `q(λx) ∈ {0,1,5,6}`,
`q(λ(y−x)) ∈ {0,1,5,6}` → `remark8_ii`. The `j=3` subcase should emit the
pairwise `{0,1,5,6}`-difference condition too, same pattern as above.)

### 3.6 Lemma 10 / 11 (numbering) — MISSING

Finite pigeonhole arguments over `ν`/`r` values of difference residues.
Since `A1` is a `Finset`, labelings come out as existential elements:

```lean
theorem lemma10 {m : ℕ} {A1 : Finset ℕ} (hcard : 4 ≤ A1.card)
    (hpos : ∀ d ∈ A1, 0 < d) (hunit : ∀ d ∈ A1, padicValNat 7 d = 0)
    (hsame : ∀ d ∈ A1, ∀ d' ∈ A1, d ≠ d' →
      residueRelOf d d' = residueRel.same)   -- same class
    : ∃ d1 ∈ A1, ∃ d2 ∈ A1, ∃ d3 ∈ A1, ∃ d4 ∈ A1,
      d1 ≠ d2 ∧ d1 ≠ d3 ∧ d1 ≠ d4 ∧ d2 ≠ d3 ∧ d2 ≠ d4 ∧ d3 ≠ d4 ∧
      (padicValNat 7 (eMod7 m d2 d1) > padicValNat 7 (eMod7 m d3 d1) ∨
        (∃ h : ℕ,
          (∀ x ∈ A1, ∀ y ∈ A1, x ≠ y →
            eMod7 m x y ≠ 0 → padicValNat 7 (eMod7 m x y) = h) ∧
          runit7 (eMod7 m d3 d1) = 2 * runit7 (eMod7 m d2 d1) ∧
          (runit7 (eMod7 m d4 d1) = 3 * runit7 (eMod7 m d2 d1) ∨
           runit7 (eMod7 m d4 d1) = 4 * runit7 (eMod7 m d2 d1))))
```
(Paper's case (i) is `ν(e21) > ν(e31)` — the two-element asymmetry; case (ii)
the uniform level `h` + ratio structure. The coloring argument "two
intersecting pairs different colors" is a small combinatorial `rcases` tree —
needs care but no new infrastructure.)

```lean
theorem lemma11 {m : ℕ} {A1 : Finset ℕ} (hcard : A1.card = 3) (s : ZMod 7)
    (hpos : …) (hunit : …) (hsame : ∀ d ∈ A1, runit7 d = s) :
    ∃ d1 ∈ A1, ∃ d2 ∈ A1, ∃ d3 ∈ A1, A1 = {d1,d2,d3} ∧
      ((enu7 m d1 d3 > enu7 m d2 d3 ∧ enu7 m d2 d3 = enu7 m d1 d2) ∨
       (enu7 m d1 d3 = enu7 m d2 d3 ∧
         (runit7 (eMod7 m d1 d3) = 2 * runit7 (eMod7 m d2 d3) ∨
          (runit7 (eMod7 m d1 d3) = 3 * runit7 (eMod7 m d2 d3) ∧
            (runit7 (eMod7 m d1 d3) = s ∨ runit7 (eMod7 m d1 d3) = -s)))))
```
(Note `eij = e(di,dj) = di−dj` for same-class pairs — `residueRelOf = same`
throughout A1, so `eMod7` reduces to the `same` branch; `e12 = e13−e23` as
residues — a useful identity `eMod7 m d1 d2 ≡ eMod7 m d1 d3 − eMod7 m d2 d3`.)

### 3.7 The `7x` digit machinery — MISSING (needed for Lemma 7(ii), §6.3, §6.6)

```lean
/-- `q(7x)` reads the second-leading base-7 digit of `x`. -/
theorem qdig7_seven (m x : ℕ) (hm : 0 < m) :
    qdig7 m (7 * x) = digit7 (m - 1) x

/-- `q(λ·7d)` is settable to any value via `λ ∈ Λ₁` (ν(7d) = 1 < m). -/
theorem exists_multLow_one_set_seven {m d : ℕ} (hm : 2 ≤ m)
    (hd : padicValNat 7 d = 0) (hd0 : 0 < d) (c : ZMod 7) :
    ∃ k : ℕ, k < 7 ∧ qdig7 m ((1 + k * 7 ^ (m - 1)) * (7 * d)) = c

/-- `q(7x) = 0` kills the top carry of `2x`: `q(2x) = 2·q(x)`. -/
theorem qdig7_two_eq_smul {m x : ℕ} (h : qdig7 m (7 * x) = 0) :
    qdig7 m (2 * x) = 2 * qdig7 m x

/-- `q(7x) = 6` (i.e. second digit forces carry 1): `q(2x) = 2q(x)+1`. -/
theorem qdig7_two_eq_smul_add_one {m x : ℕ} (h : qdig7 m (7 * x) = 6) :
    qdig7 m (2 * x) = 2 * qdig7 m x + 1
```
And the 2-digit expansion of a `Λ₁`-action on a level-0 element (the
**carry engine** behind `q(7d₃) = 4ε₁+2ε₂`):
```lean
theorem digit7_multLow_one {m k x : ℕ} (hm : 1 ≤ m) :
    digit7 m ((1 + k * 7 ^ (m - 1)) * x)
      = digit7 m x + (k : ZMod 7) * digit7 1 x + carry
    ∧ digit7 (m-1) ((1 + k * 7 ^ (m - 1)) * x)
      = digit7 (m-1) x + (k : ZMod 7) * digit7 0 x
```
where `carry = (digit7 (m−1) x + k·digit7 0 x ≥ 7)` as `ZMod 7`/`ℕ`. Exact
statement: `x + k·7^{m−1}·x ≡ x + k·(x mod 7²)·7^{m−1} (mod 7^{m+1})`, so the
perturbation is `k·x₀` at position `m−1` plus `k·x₁` at position `m` plus the
carry `⌊(x_{m−1}+k·x₀)/7⌋` — an *exact* 2-digit update, no hidden noise.
This is the single most technical missing piece (see §7, risk R1).

### 3.8 Assorted small gaps

- `filtered7_mod7` : the `filtered7` multiplier satisfies `lam % 7 = 1`
  (all factors `≡ 1 mod 7`) — hence `runit7 (lam*d) = runit7 d`.
- `exists_multLow_set_qdig` : `∃ k < 7, qdig7 m ((1+k·7^{m−j})*x) = c`
  for `ν(x) = j < m`, any `c : ZMod 7` (bijectivity corollary of
  `qdig7_multLow` + `runit7_ne_zero`).
- `exists_top_scalar_set` : for `ν(x) = m`, `∃ c ∈ {1,…,6}: c*x ≡ t·7^m
  (mod 7^{m+1})` for any target `t ≠ 0` — i.e., level-`m` residue
  normalization `e ↦ kN/7`. (Currently `exists_top_scalar` only avoids a
  forbidden set; the normalization is `c = t·runit7(x)⁻¹` via
  `qdig7_multTop` + the fact that level-`m` residue = `q·7^m` — needs a
  lemma `residN_top : padicValNat 7 x = m → x % 7^{m+1} = (qdig7 m x).val * 7^m`.)
- `absModN` inequalities for §6.5 (all `[verified]` numerically):
  `N/7 ≤ |x|_N` from `q(x) ∈ {2,3,4}`-type bounds;
  `|x|_N ≥ 5N/14 → |2x|_N ≤ 2N/7`; `|x|_N ∈ [2N/7,5N/14] → |3x|_N ≤ N/7`;
  and `|x|_N ≤ 2N/7 → qdig7 m x ∈ {0,1,5,6}`-style conversions.
  These are plain `ℕ`/`absModN` lemmas (case `N = 7^{m+1}`).
- `eMod7` algebra: `eMod7 m (lam*x) (lam*y) ≡ lam * eMod7 m x y`,
  `eMod7 m x y + eMod7 m y z ≡ eMod7 m x z` (same-r chains),
  `eMod7 m (c*x) (c*y) ≡ c * eMod7 m x y` for scalar `c`.
- `subMod`-free difference digits: `qdig7 m (eMod7 m x y)` already models
  `q(x−y)`; for `q(2x−y)` non-same cases `eMod7`'s twoX/twoY branches match.
- `apLen` of explicit small sets: `apLen {a, a+1, a+2, a+4} = 5`-type lemmas
  (finite `decide`/`interval_cases`).
- Class machinery: `A.filter (runit7 d = s)` + the argmax lemma
  `∃ s ∈ {1,2,4}: apLen(q(A_s)) ≥ apLen(q(A_{2s})), apLen(q(A_{4s}))`
  (the `hord` hypothesis of `lemma5`), plus the rotation
  `s ↦ 2s ↦ 4s ↦ s` cycling `(A1,A2,A4)` used to place the singleton in A4.

---

## 4. Per-subsection content (math, in paper notation)

Throughout: `A` = five level-0 elements, residues in `{1,2,4}`.
`A1` = a class of *larger length* (residue `s`), `A2`/`A4` = classes `2s`/`4s`.
`eij := e(di,dj)`, `E := (A1−A1)∖{0}` as residues mod `N`.

### 4.1 §6.1 — `|A1| = 5` (single class `s`)

Label via **Lemma 10** on `A1 = {d1,…,d5}`.

**Case A: `ν(E) ≠ {m}`.** Lemma 10 gives (i) `ν(e21) > ν(e31)` or
(ii) uniform `h` with `r(e31) = 2r(e21)`, `r(e41) ∈ {3,4}·r(e21)`.
Apply **Lemma 9** to `B = {d1,d2,d3}` (x = e13 = −e31, y = e23;
case (i) uses `ν(x)≠ν(y)` after sign swap; case (ii) has `r(x') = 2r(y')`,
`j=2`): obtain `λ` with `q(λ·(B−B)) ⊆ {0,6}` and `ℓ(λB) ≤ 2`. Then `Λ₀`
normalizes `q(λB) ⊆ {0,6}` (shift `i ↦ 6`, the wrapping 2-interval `{6,0}`).
- If `{q(d₄),q(d₅)} ≠ {2,4}` (as a set): `apLen(q(A1)) ≤ 5`
  (**[verified]**: `{2,4}` is the *only* pair giving ℓ 6) →
  `exists_shift_avoid` → done.
- If `{q(d₄),q(d₅)} = {2,4}`: multiply by `3 ∈ Λ_m`.
  `q(3d₄),q(3d₅) ∈ 3·{2,4}+{0,1,2} ⊆ {0,1,5,6}`;
  `q(3B) ⊆ {0,1,2} ∪ {4,5,6}`. Under `q(B−B) ⊆ {0,6}` the f-order coupling
  (`f₀ < f₆` for each 0/6 pair — from `q(b₀−b₆) ∈ {0,6}`) kills the joint
  bad carries, giving `q(3·A1) ⊆ {0,1,2,5,6}` or `⊆ {0,1,4,5,6}`, hence
  `ℓ(3·A1) ≤ 5` → `exists_shift_avoid` → done **[verified]**.
  *Formalization note*: rather than tracking `f`-digits abstractly, prove the
  dichotomy as a finite lemma on `(q_i, f_i)` with `f_i < 7` at the digit
  level — the constraint `q(bi−bj) ∈ {0,6}` translates to `f` orderings;
  the check above was done at `N=49` granularity and is exact for `m ≥ 1`
  because only `f`-order matters for the carry dichotomy.

**Case B: `ν(E) = {m}`.** `E1 = {e51,e41,e31,e21} ⊆ {kN/7}` (4 distinct
nonzero residues); complement `{iN/7, jN/7}`. Multiply by `(i−j)⁻¹` (a
`Λ_m` scalar): `{ci,cj}` become adjacent, so `{0,ci,cj}` contains the
2-run `{ci,cj}` and `E1 ⊆ cycIv` of length 5 — "the elements of E1 are
consecutive" (= `apLen ≤ 5`). Then `q(A1) ⊆ a + E1` (level-`m` differences
give *exact* digit differences) → `ℓ(A1) ≤ 5` → Lemma 5/shift → done.
(All 4-subsets of `{1,…,6}` dilate into a 5-interval — verified conceptually
in the dig; easy `decide` as a `ZMod 7` fact: `∀ E ⊆ univ, card E = 4 →
∃ c ≠ 0, apLen (E.image (·*c)) ≤ 5`.)

### 4.2 §6.2 — `|A1| = 4`, leftover `d5` with `r(d5) ∈ {2s,4s}`

`A1 = {d1,d2,d3,d4}` labeled by Lemma 10; `B = {d1,d2,d3}`.

**Case A: `ν(E) ≠ {m}`.** Lemma 9 → `ℓ(B) ≤ 2`, `Λ₀` → `q(B) ⊆ {0,6}`.
`q(d₄) ≠ 3` ⇒ `ℓ(A1) ≤ 4` wait — paper: `q(d₄) = 3` ⇒ `q(2·A1) ⊆ {0,1,5,6}`
(`2·{0,6,3}+carries`) ⇒ `ℓ(2·A1) ≤ 4` hmm — arXiv says `ℓ(A1) ≤ 4` in both
branches. Check: `q(d4)=3`: `{0,6,3}` has apLen 4 ({6,0,3}? gaps — `{0,3,6}`:
misses {1,2,4,5}, runs {1,2},{4,5} → apLen 5!). Hmm — `q(A1) ⊆ {0,6,3}`:
apLen({0,3,6}) = 5, not 4! So for `q(d4)=3` they scale ×2: `q(2·{0,6,3})`
with carries ⊆ `{0,1}∪{5,6}∪{6,0,1}` → `q(2A1) ⊆ {0,1,5,6}`? `2·3+{0,1} =
{6,0}`, `2·6+{0,1}={5,6}`, `2·0+{0,1}={0,1}` → union ⊆ `{0,1,5,6}` — a set
of apLen … `{0,1,5,6}` misses `{2,3,4}` run 3 → apLen 4 ✓ "ℓ(2·A1) ≤ 4".
Then Lemma 5 with `ℓ ≤ 4+0+1 ≤ 5` (A4 = {d5} or A2 = {d5}, other empty) —
wait `d5 ∈ A2 ∪ A4`: lengths (4,1,0) or (4,0,1) → `lemma5` (sum ≤ 5).
For `q(d4) ≠ 3`: `apLen({0,6,q4}) ≤ 4` when `q4 ∉ {3}`? Check `{0,6,q}`:
q=3 → 5; q=4 → `{0,4,6}` gaps 4,2,1 → misses run {1,2,3}? `{0,4,6}` misses
{1,2,3,5}: runs {1,2,3} len 3 → apLen 4 ✓; q=3 is the only bad one
(`{0,3,6}`: runs {4,5},{1,2} → apLen 5). So `q(d4) ≠ 3 ⇒ ℓ ≤ 4` ✓ consistent
with arXiv "if q(d4) ≠ 3 then ℓ(A1) ≤ 4" — **EJC-txt dropped the ≠ sign**;
verified by the same computation (only `q4 = 3` fails).

**Case B: `ν(E) = {m}`.**
- (ii.1) `r(e41) = 3r(e21)`: multiply by `r(e21)⁻¹` (Λ_m) ⇒
  `e41 = 3N/7, e31 = 2N/7, e21 = N/7` ⇒ `q(A1) = {a,a+1,a+2,a+3}`, `ℓ ≤ 4`
  → Lemma 5 (sum ≤ 5 with `d5` singleton).
- (ii.2) `r(e41) = 4r(e21)`: Λ_m ⇒ `q({e21,e31,e41}) ⊆ {1,2,4}` ⇒
  `q(A1) = {a,a+1,a+2,a+4}`, `ℓ = 5`.
  `d5 ∈ A4`: **Lemma 7** ⇒ `ẽ(d1,d5) ∉ {4,6}` → Lemma 6(i) (5,0,1)
  (anchor `q(d1) = 1` via Λ₀ re-normalization).
  `d5 ∈ A2`: Lemma 7 ⇒ `ẽ(d1,d5) ∉ {2,3}` → Lemma 6(i) (5,1,0);
  "unless `e15 = 3N/7`" (PDF-confirmed). Details: Lemma 7(ii) needs
  `r(e15) ∉ X∪(X+1) = {2,3,4}` — fails for `r ∈ {2,3,4}`, not only `3`.
  Resolution **[verified]**: the `{x,2x,4x}` difference-structure of A1
  has scalar stabilizer `{1,2,4} ⊆ Z_7*` (c·{1,2,4} = {1,2,4}), and for
  every `r(e15)` a stabilizer scalar sends `r ↦ 1` or out of `{2,3,4}`:
  `r = 2 ↦ c=4:1`, `r = 4 ↦ c=2:1`, `r = 3 ↦ c∈{2,4}:{6,5}` — the last
  is exactly the paper's `×2` fallback (`2e15 = 6N/7`, `ẽ ∈ {5,6,0}`
  auto-avoids `{2,3}` — no Lemma 7 needed there).
  Implementation note: handle `r(e15) ∈ {2,4}` by the stabilizer scalar
  (which preserves `q({e21,e31,e41}) ⊆ {1,2,4}`-structure ⇒ `ℓ ≤ 5`)
  then Lemma 7(ii); `r = 3` via the printed fallback.

### 4.3 §6.3 — `|A1| = 3`, `|A2| = |A4| = 1`

`A1 = {d1,d2,d3}` (Lemma 11 labeling), `A2 = {d4}`, `A4 = {d5}`.

- **(i) and (ii.1), `h < m`**: Lemma 9 → `ℓ(A1) ≤ 2` → Lemma 5
  (sum `2+1+1 = 4 ≤ 5`; also `(3,1,1)` escape via `ℓ ≤ 2 < 3`).
- **(ii.2), `h < m`**: `r(e13) = 3r(e23) = ±s`.
  - (a) `ν(e45) ≠ ν(e13)`: if `ν(e45) > ν(e13)`: Lemma 2 on `e45` ⇒
    `q(e45) ∈ {0,6}` ⇒ `ẽ(d4,d5) ∈ q(e45)+{0,±1} ⊆ {0,1,5,6}` (the
    twoX `±1` bound, §3.2); then Lemma 9(j=3) ⇒ `ℓ(A1) ≤ 3` ⇒
    Lemma 5 `(3,1,1)`-non-exception (`ẽ ∉ {2,4}`) or `ℓ ≤ 2`.
    If `ν(e45) < ν(e13)`: order-swapped — Lemma 9 first, then Lemma 2
    on `e45`.
  - (b) `ν(e45) = ν(e13) = h`: `r(e45) = ±r(e13)`; `f = e13 ∓ e45`,
    `ν(f) > h`, `q(f) = 0` (Lemma 2) ⇒ `ẽ(e13,e45) = q(e13)−q(e45) ∈ {0,1}`
    (invariant under `Λ_{j≤h}` — Lemma 4(i)). `ũ := 3q(e13)+5q(e23)`.
    **The 14-cell table** (semantics verified on sample cells): for each
    `(ẽ, ũ)` choose `q(e45)` by Lemma 2 (single-element Λ_h shift; e45 is a
    difference at level h — wait, `q(e45)` is set by `Λ_h` multiplying the
    *difference residue* `e45`; in Lean: `exists_multLow_set_qdig` on the
    element `eMod7 m d4 d5`), then `q(e13) = q(e45)+ẽ`,
    `q(e23) = 3(ũ−3q(e13))`, `q(e12) ∈ q(e13)−q(e23)−{0,1}`.
    Result: every cell except `(ẽ,ũ) = (0,3)` yields `ℓ(A1) ≤ 3` +
    `ẽ(d4,d5) ∉ {2,4}` **or** `ℓ(A1) = 2` → Lemma 5. `(0,3)` cell: multiply
    by 2: `q({2e45,2e13,2e23}) ⊆ {0,6}` and `q(2e12) ∈ {0,1,5,6}` → same
    Lemma-5 conditions in the ×2 config. `r(e45) = −r(e13)` symmetric
    (`f = e13+e45`, `q(−e45)`).
- **(ii.1), `h = m`**: Λ_m ⇒ `e13 = 2N/7, e23 = N/7` ⇒ `q(A1) = {a,a+1,a+2}`,
  `ℓ = 3`. Lemma 7 ⇒ `ẽ(d4,d5) ∉ {2,4}` → Lemma 5 `(3,1,1)` non-exception.
- **(ii.2), `h = m`**: Λ_m ⇒ `e13 = 3N/7, e23 = N/7` ⇒ `ℓ(A1) = 4`;
  Λ₀ ⇒ `q(A1) ⊆ {1,2,3,4}`, `q(d3) = 1`. `i = q(d4), j = q(d5)`.
  Eq. (1) fails only for the 8 bad `(i,j)` **[verified]**:
  `i ∈ {0,6}, j ∈ {2,3}` or `j ∈ {0,6}, i ∈ {4,5}`, i.e.
  `(ẽ34,ẽ45) ∈ {(2,4),(2,5),(3,2),(3,3),(4,3),(4,4),(5,1),(5,2)}`
  where `ẽ34 = 2q(d3)−q(d4) = 2−i`, `ẽ45 = 2q(d4)−q(d5) = 2i−j`.
  - `ν(e34) < m`: Lemma 7(i) `X = {2,3,4,5}` (ℓ = 4) ⇒ `ẽ34 ∉` it → done.
  - `ν(e34) = m, ν(e45) < m`: Lemma 7(i) on `(d4,d5)` with
    `X = {2,3,4,5}` if `ẽ34 ∈ {2,3}` else `X = {1,2,3,4}` → avoids all 8.
  - `ν(e34) = ν(e45) = m`: one of `(q(e34)−ε1, q(e45)−ε2)`, `εi ∈ {0,1}`,
    avoids the 8 bad pairs **[verified]**; realized by
    `q(λ·7d₃) = 4ε₁+2ε₂` via `λ ∈ Λ₁` (`ν(7d₃) = 1 < m`, needs `m ≥ 2`) —
    the "routine checking" is a 2-digit carry propagation
    (`d4 = 2d3 + tN/7` couples the carries) — see §3.7, risk R1.

### 4.4 §6.4 — `|A1| = 3`, `|A2| = 2`

`A1 = {d1,d2,d3}`, `A2 = {d4,d5}`, `A4 = ∅`.

- (i)/(ii.1) `h<m`: Lemma 9 → `ℓ(A1) ≤ 3` → **Lemma 12(i)**.
- (ii.1) `h=m`: `e13 = 2N/7, e23 = N/7` ⇒ `ℓ = 3` → Lemma 12(i).
- (ii.2) `h=m`: `e13 = 3N/7, e23 = N/7` ⇒ `ℓ = 4`.
  `ν(e34) < m` or `ν(e35) < m`: Lemma 7(i) sets the corresponding `ẽ ∉
  {2,3,4,5}` ⇒ `ẽ(d3,d') ∈ {0,1,6}` for some `d' ∈ A2` → Lemma 12(ii).
  `ν(e34) = ν(e35) = m` ⇒ `ν(e45) = m` (`e45 = e35−e34`);
  `s := (3·r(e45))₇`; rename `d4↔d5` ⇒ `e45 = e23 = N/7` ⇒ `q(A2) = {i,i+1}`,
  `ℓ(A1) = 4, ℓ(A2) = 2`; Lemma 7 ⇒ `ẽ35 ≠ 4` → **Lemma 6(ii)** `(4,2,0)`
  (needs `ẽ(d,d') ≠ 4` for `d'` the lower element — verify which of
  `d4,d5` is `q⁻¹(i)` during implementation; the paper's `ẽ35 ≠ 4` must land
  on the right element, possibly after the rename).

### 4.5 §6.5 — `|A1| = 3`, `|A4| = 2`

`A1 = {d1,d2,d3}`, `A4 = {d4,d5}`, `A2 = ∅`. Target disjunction **(14)**:
`(ℓ(A1) ≤ 3 ∧ ℓ(A4) ≤ 3) ∨ (ℓ(A1) ≤ 4 ∧ ℓ(A4) ≤ 2)` ⇒ Lemma 5 or 6(ii)/(iii).

- (i)/(ii.1) `h<m`: Lemma 9 → `ℓ(A1) ≤ 2`. If `ℓ(A4) ≤ 3` done (Lemma 5).
  Else `q(e45) ∈ {2,3,4}` ⇒ `|e45|_N ∈ [2N/7,3N/7]`:
  `|e45|_N ≥ 5N/14 ⇒ |2e45|_N ≤ 2N/7` ⇒ `ℓ(2·A4) ≤ 3`, `ℓ(2·A1) ≤ 3`
  (Remark 8(i), `k=2`) ⇒ (14);
  `|e45|_N ∈ [2N/7,5N/14] ⇒ |3e45|_N ≤ N/7` ⇒ `ℓ(3·A4) ≤ 2`, `ℓ(3·A1) ≤ 4`
  (Remark 8(i), `k=3`) ⇒ (14). **[verified both inequalities]**
- (ii.2) `h<m`: `ν(e13) = ν(e45)`: set `s = r(e45)`, rename so
  `r(e45) = r(e13)`; `f = e45−e13`, `ν(f) > ν(e13)`, `q(f) = 0` (or `f=N/7`)
  via Lemma 2; Lemma 9(ii) ⇒ `q(e13) ∈ {0,5,6}`, `ℓ(A1) ≤ 3` ⇒
  `q(e45) ∈ q(e13)+q(f)+{0,1}` ⇒ `|q(e45)| ≤ 2` ⇒ `ℓ(A4) ≤ 3` ⇒ (14).
  `ν(e13) ≠ ν(e45)`: larger-level one first via Lemma 2
  (`q(e45) ∈ {0,6}` or `e45 = N/7`), then Lemma 9 ⇒ `ℓ(A1) ≤ 3`,
  `ℓ(A4) ≤ 2` ⇒ (14).
- (ii.1) `h=m`: `e13 = 2N/7, e23 = N/7` ⇒ `ℓ(A1) = 3`; rename ⇒
  `r(e45) ∈ {1,2,4}`.
  - (a) `ν(e45) < m` or `e45 ∈ {N/7,2N/7}`: Lemma 2 ⇒ `q(e45) ∈ {0,1,5,6}`
    ⇒ `ℓ(A4) ≤ 3` ⇒ (14).
  - (b) `ν(e45) = m`, `e45 ∉ {N/7,2N/7}` ⇒ `e45 = 4N/7` (`r ∈ {1,2,4}`
    rename), `q(A1) = {1,2,3}` (Λ₀, `q(d3) = 1`), `q(A4) = {i,i+4}`
    with `i = q(d5)`, `q(d4) = i+4` (exact, since `e45 = d4−d5 = 4N/7`
    is level-`m` ⇒ `f4 = f5`, no borrow). PDF-verified: "three available
    multipliers in Λ₀ … all fail for A4 iff `i ∈ {2,6}`, and so
    `ẽ(d3,d4) ∈ {4,5}`" — indeed `i ∈ {2,6}` ⇔ `q(d4) ∈ {6,3}` ⇔
    `ẽ(d3,d4) = 2q(d4)−q(d3) = 2q(d4)−1 ∈ {4,5}` **[verified, exact]**.
    Lemma 7 ⇒ `ẽ(d3,d4) ∉ {4,5}` unless `e34 = 5N/7` (avoid set
    `X = {4,5}`, `r(e34) = 5 ∈ X∪(X+1)` — Lemma 7's only failure).
    For `e34 = 5N/7`: multiply by 2 ⇒ `ℓ(2·A1) = 5`, `ℓ(2·A4) = 2`,
    `2e34 = 3N/7`; "by Lemma 7(ii) we can avoid `ẽ(2d3,2d4) = 2`";
    Λ₀ ⇒ `q(2·A1) = {1,3,5}` (`q(2d3) = 1`) and "since
    `ẽ(2d3,2d4) = 3`" ⇒ `q(2·A4) = {1,2}` ⇒ union `{1,2,3,5}` avoids
    `{0,6}` directly — done.
    **Flag (real subtlety)**: `ẽ(2d3,2d4) ∈ q(2e34)+{0,±1} = {2,3,4}`;
    avoiding `2` leaves `{3,4}`, but `ẽ = 4` gives `q(2d4) = 6` BAD.
    `lemma7_ii` as stated needs `r(2e34) = 3 ∉ X∪(X+1)` — with `X={2}`,
    `X∪(X+1) = {2,3} ∋ 3` — **not applicable**. The paper's conclusion
    needs the `q(λ·7d) = 0`-branch's sharper range `ẽ ∈ {r(e),r(e)−1}
    = {3,2}` *plus* a way to exclude the `2`: likely the `r(e) ∉ X∪(X+1)`
    hypothesis is meant for the reversed pair or there's an additional
    carry-exclusion — **implementer must re-derive; recommend a
    `lemma7_ii'` variant returning the exact `ẽ`-set `{r,r−1}` so the
    case can pick the branch, or handle `e34 = 5N/7` via the
    `q(7d)`-ε machinery directly.**
- (ii.2) `h=m`: `s := r(e45)`, rename ⇒ `r(e13) = r(e45)`;
  Λ_m ⇒ `e13 = N/7, e23 = 5N/7` (EJC; `3r(e23) = r(e13) = 1` ⇒ `r(e23) = 5`)
  ⇒ `q(A1) = {a,a+1,a+5}`, `ℓ ≤ 4`. `ν(e45) = m` ⇒ `e45 = N/7` ⇒ `ℓ(A4) = 2`;
  `ν(e45) < m` ⇒ Lemma 2 `q(e45) ∈ {0,6}` ⇒ `ℓ(A4) = 2` ⇒
  Lemma 6(ii) `(4,0,2)`.

### 4.6 §6.6 — `|A1| = 2` (`(2,2,1)` shape after `s`-rotation)

`A1 = {d1,d2}`, `A2 = {d3,d4}`, `A4 = {d5}`; `r(e12), r(e34) ∈ {1,2,4}`.
Goal **(15)**: `ℓ(A1) ≤ 2 ∧ ℓ(A2) ≤ 2` ⇒ Lemma 5 (`2+2+1 = 5`).

- `ν(e12) ≠ ν(e34)`: Lemma 2 on both ⇒ `q(e12), q(e34) ∈ {0,6}` ⇒ (15).
- `ν(e12) = ν(e34)`, `r(e12) = r(e34)`: `f = e12−e34`, `ν(f) > ν(e12)`;
  `ν(f) ≤ m`: Lemma 2 ⇒ `q(f) = 6, q(e34) = 0`; `ν(f) > m`: `q(f) = 0`,
  Lemma 2 ⇒ `q(e34) = 6`. Both ⇒ `q(e12) = q(f+e34) ∈ {0,6}` ⇒ (15).
- `ν(e12) = ν(e34) < m`, `r` differs (`r(e12) = 2r(e34)` or `2r(e12) = r(e34)`):
  **verified delicate**. EJC-PDF text (checked against `bs7-ejc.pdf` p.16):
  "by Lemma 2 … `q(λe12), q(λe34) ∈ {0,1,5,6}`. Since `λe12 ≠ 5N/7` and
  `λe34 ≠ 5N/7`, (15) holds." Finite check (`verify.py`):
  `q ∈ {0,1,5,6}` alone ⇒ **128 counterexamples** — literally insufficient;
  `q ∈ {0,6}` ⇒ **0 failures** — the real requirement. But `Σ|F| = 10 > 6`
  blocks `filtered7` from producing `{0,6}` on both at a shared level, and a
  single `k` can't always hit `{0,6}` on both targets (2∩2 disjoint).
  Working reconstruction: apply the same trick as the equal-`r` branch —
  `f = e12 − 2e34` (or `2e12 − e34`) has `ν(f) > h`; Lemma 2 with
  `q(f) = 6, q(e34) = 0` (budget-feasible, different levels) gives
  `q(e12) = q(f+2e34) ∈ {6,0,1}`; residual failures = **7 configs**, all at
  the carry-2 boundary (`q(e12) = 1` + borrow ⇒ element-diff `2` ⇒ `ℓ = 3`).
  The paper's "≠ 5N/7" exclusions presumably cover this residual band —
  **implementer must reconstruct this step; suggest either (a) a bespoke
  variant of the `f`-argument that additionally controls the carry, or
  (b) a direct `decide`-verified disjunction on the achieved q-values
  showing one of `k ∈ {1,…,6}` (not just `{1,2,3}`) works.** Alternative
  target assignment `(q_f, q_e34)` enumeration shows no single choice
  removes all 7 — the extra condition is genuinely needed.
- `ν(e12) = ν(e34) = m`:
  - (a) `r(e12) = 2r(e34)`: Λ_m ⇒ `e12 = 2N/7, e34 = N/7`;
    `λ_k ∈ Λ₀` with `q(λ_k d2) = k`, `k ∈ {1,2,3}`:
    `q(λ_k·A1) = {k,k+2}`, `q(λ_k·A2) = {2k−x, 2k−x+1}` (`x = ẽ(d2,d4)`;
    **note**: `q(d4) = 2q(d2)−x`, `q(d3) = q(d4)+1` — the corrected model,
    §0.2), `q(λ_k d5) = 4y+4k` (`y = ẽ(d2,d5)`, `4 = 2⁻¹ mod 7`).
    Bad pairs (16) **[verified]** = `{(4,2),(4,4),(5,4),(6,4),(6,6)}`.
    `ν(e24) < m` or `e24 ∈ {N/7,2N/7,3N/7}`: Lemma 7 ⇒ `ẽ(d2,d4) ∉ {4,5,6}`
    ⇒ (16) avoided.
    `ν(e24) = m`, `ν(e25) < m`: set `ẽ(d2,d5) ∉ {2,4}` if
    `e24 ∈ {4N/7,5N/7}`, `ẽ(d2,d5) ∉ {4,6}` if `e24 ∈ {0,6N/7}` ⇒ avoided.
    `ν(e24) = ν(e25) = m`: `(q(e24)−ε1, q(e25)−ε2)` one of 4 avoids all
    bad pairs **[verified]**; realized via `q(λ·7d5) = 4ε₂+2ε₁` (`Λ₁`,
    `m ≥ 2`) — the "argument of 6.3 applied to `7d5`".
  - (b) `r(e12) = 4r(e34)`: Λ_m ⇒ `e12 = N/7, e34 = 2N/7`;
    `λ_k` with `q(λ_k d4) = k`: `q(λ_k·A2) = {k,k+2}`,
    `q(λ_k·A1) = {4a+4k, 4a+4k+1}` (`a = ẽ(d2,d4)`),
    `q(λ_k d5) = 2k−b` (`b = ẽ(d4,d5)`).
    Lemma 7 ⇒ `ẽ(d2,d4) ∉ {2,4}`; then **every** `(a,b)` admits a good
    `k ∈ {1,2,3}` iff `a ∉ {2,4}` **[verified]** — EJC's `{2,4}` is the
    exact minimal avoid-set (arXiv `{2,4,6}` also works but is weaker).

---

## 5. Proposed Lean declaration list for `Case5m.lean`

Convention mirroring `lrc7_m1` and the `Compress.lean` style (public
theorems are `ZMod 7`-or-`ℕ`-level; `decide` certificates `private`).

```lean
import Research07.LRC7.Compress
import Research07.LRC7.Differences
```

### 5.1 Shared goal predicate + plumbing

```lean
/-- A multiplier is *good* for `A` at level `m` if every scaled leading
digit avoids `{0,6}` (equivalently `|λd|_N ≥ 7^m`). -/
def good7 (m lam : ℕ) (A : Finset ℕ) : Prop :=
  ∀ d ∈ A, qdig7 m (lam * d) ∉ ({0, 6} : Finset (ZMod 7))

theorem good7_mul {m lam lam' : ℕ} {A : Finset ℕ} (h : good7 m lam' (A.image (lam * ·))) ...
```
Pattern for composition: from `good7 m lam' (lam '' A)` get
`good7 m (lam' * lam) A` by `Finset.image_image` + `mul_assoc`.

```lean
/-- Bridge to the `Compress.lean` shift lemmas: a `Λ₀`-element shifts
`qdig` by `k·runit7`. -/
theorem qdig7_lambda0 {m d k : ℕ} (hd : padicValNat 7 d = 0) :
    qdig7 m ((1 + k * 7 ^ m) * d) = qdig7 m d + (k : ZMod 7) * runit7 d
-- = qdig7_multLow (j := 0)

/-- Shift lemma, integer level: `apLen ≤ 5` ⇒ ∃ `λ ∈ Λ₀` good. -/
theorem exists_lambda0_avoid {m : ℕ} {A : Finset ℕ}
    (h : apLen (A.image (qdig7 m)) ≤ 5) (hsame : ∀ d ∈ A, runit7 d = s) :
    ∃ lam ∈ multLow7 m 0, good7 m lam A
-- ∃ k: shift q(d) ↦ q(d)+k·s maps the covering interval off {0,6}
-- via exists_shift_avoid (uniform shift since all runit7 = s).

/-- Generalized: mixed classes — `lemma5`/`lemma6` produce `t`; build
`λ = 1 + k·7^m` with `k·s ≡ t`, `2k·s ≡ 2t`, `4k·s ≡ 4t` — i.e. `k = t·s⁻¹`
wait — the shift on class `c·s` is `k·(c·s) = c·(ks)`: setting `ks = t`
works for all three classes simultaneously: `k = t·s⁻¹` — then A1 shifts
by `t`, A2 by `2t`, A4 by `4t` automatically. Single lemma: -/
theorem exists_lambda0_of_shift {m : ℕ} (s : ZMod 7) (hs : s ≠ 0)
    {A : Finset ℕ} (hcls : ∀ d ∈ A, runit7 d ∈ ({s, 2*s, 4*s} : Finset _))
    (t : ZMod 7)
    (h : avoids06 ((A₁.image (·+t)) ∪ (A₂.image (·+2*t)) ∪ (A₄.image (·+4*t)))) :
    ∃ lam ∈ multLow7 m 0, good7 m lam A
```
(with `Aⱼ = A.filter (runit7 · = j*s)`.) This is the **workhorse** joining
`lemma5/lemma6/lemma12` to integer multipliers.

### 5.2 `ZMod 7` finite lemmas (`private …_dec : … := by decide`, public wrappers)

```lean
-- §6.1: the unique failing pair
theorem apLen_pair06_le {a b : ZMod 7} (h : ¬(a = 2 ∧ b = 4) ∧ ¬(a = 4 ∧ b = 2)) :
    apLen ({0,6,a,b} : Finset (ZMod 7)) ≤ 5

-- §6.1 ×3 dichotomy at the *digit* level (see §4.1 note):
theorem case61_dichot {q0 q6 f0 f6 q4 q5 f4 f5 : ZMod 7} ... : ...

-- §6.2: {0,6,q} ⊆ 4-interval iff q ≠ 3
theorem apLen_triple_le {q : ZMod 7} (hq : q ≠ 3) :
    apLen ({0,6,q} : Finset (ZMod 7)) ≤ 4

-- §6.1 B: every 4-subset of {1,…,6} dilates into a 5-interval
theorem apLen_four_dilate {E : Finset (ZMod 7)} (hE : E.card = 4) (h0 : 0 ∉ E) :
    ∃ c : ZMod 7, c ≠ 0 ∧ apLen (E.image (· * c)) ≤ 5

-- §6.3 (ii.2) h=m: the 8 bad pairs
def bad63 : Finset (ZMod 7 × ZMod 7) := {(2,4),(2,5),(3,2),(3,3),(4,3),(4,4),(5,1),(5,2)}
theorem case63_bad_pairs {i j : ZMod 7}
    (h : ∀ t : ZMod 7, ¬ avoids06 ({1+t,2+t,4+t,i+2*t,j+4*t} : Finset _)) :
    (2-i, 2*i-j) ∈ bad63
theorem case63_eps_avoid (p q : ZMod 7) :
    ∃ ε₁ ε₂ : ZMod 7, ε₁ ∈ {0,1} ∧ ε₂ ∈ {0,1} ∧ (p-ε₁, q-ε₂) ∉ bad63

-- §6.6(a): bad pairs (16) under the corrected model
def bad66a : Finset (ZMod 7 × ZMod 7) := {(4,2),(4,4),(5,4),(6,4),(6,6)}
theorem case66a_bad {x y : ZMod 7}
    (h : ∀ k ∈ ({1,2,3}:Finset (ZMod 7)), ¬ avoids06
      ({k,k+2, 2*k-x, 2*k-x+1, 4*y+4*k} : Finset _)) :
    (x, y) ∈ bad66a
theorem case66a_eps (p q : ZMod 7) : ∃ ε₁ ε₂ ∈ ({0,1}:Finset _), (p-ε₁,q-ε₂) ∉ bad66a

-- §6.6(b): exact avoid-set {2,4}
theorem case66b_good {a b : ZMod 7} (ha : a ∉ ({2,4}:Finset _)) :
    ∃ k ∈ ({1,2,3}:Finset (ZMod 7)), avoids06
      ({k,k+2, 4*a+4*k, 4*a+4*k+1, 2*k-b} : Finset _)

-- §6.5(ii.1)(b): three Λ₀ shifts; all fail iff i ∈ {2,6}
theorem case65b_bad_i {i : ZMod 7}
    (h : ∀ t : ZMod 7, ¬ avoids06 ({1+t,2+t,3+t,i+4*t,i+4+4*t} : Finset _)) :
    i ∈ ({2,6} : Finset (ZMod 7))

-- Lemma 7(i)'s translate: x ∉ X+{0,1,2} exists when apLen X ≤ 4
theorem exists_not_mem_three {X : Finset (ZMod 7)} (hX : apLen X ≤ 4) :
    ∃ x : ZMod 7, ∀ u ∈ ({0,1,2}:Finset _), x - u ∉ X

-- §6.5 (i): |e| bounds (as ZMod-7-free ℕ lemmas, not decide)
-- see §3.8 absModN list.

-- §6.3 (ii.2.b): the ũ-table — encode as ONE finite lemma:
theorem case63_table (e u : ZMod 7) (he : e ∈ ({0,1}:Finset _)) :
    ∃ q45 : ZMod 7, <cell-dependent conclusion: with q13 = q45+e,
      q23 = 3*(u-3*q13), q12 ∈ q13-q23-{0,1}: either
        (apLen ≤ 2 shape) ∨ (apLen ≤ 3 shape ∧ 2i-j ∉ {2,4})>
```
The table should be stated in terms of the *consequences* (see §4.3):
`∀ (e ∈ {0,1}) (u ∈ Z_7)`, the chosen `q45` yields difference-digits from
which `ℓ(A1) ≤ 2`, or `ℓ(A1) ≤ 3 ∧ ẽ(d4,d5) ∉ {2,4}` follows. The precise
row data (for the implementation file docstring):

```
ẽ=0: q(e45) = [0,6,0,3,6,0,6]  (ũ = 0..6)
     rows: (0,0,{0,6}) (6,5,{0,1}) (0,6,{0,1}) (3,3,{0,6}) (6,0,{6,5}) (0,1,{6,5}) (6,6,{0,6})
ẽ=1: q(e45) = [6,0,6,0,(5|6),6,5]
     rows: (0,0,{0,6}) (1,1,{0,6}) (0,6,{0,1}) (1,0,{0,1}) (6,0,{6})|(0,5,{1}) (0,1,{5,6}) (6,6,{6,6})
     (ũ=4 splits: q45=5 if q(e12)=q(e13)−q(e23); q45=6 if q(e12)=q(e13)−q(e23)−1)
special: (ẽ,ũ)=(0,3) → ×2 rescue instead of Lemma 5.
```

### 5.3 Mid-level lemmas (ℕ-level, carry/difference tracking)

- `qdig7_smul_carry` (§3.4), `qdig7_seven` family (§3.7),
  `digit7_multLow_one` (§3.7),
  `lemma7_i`, `lemma7_ii` (§3.3), `lemma9_i`, `lemma9_ii` (§3.5),
  `lemma10`, `lemma11` (§3.6), `eMod7_mul`/`eMod7_add` algebra (§3.8),
  `filtered7_mod7`, `exists_multLow_set_qdig`, `exists_top_scalar_set`,
  `residN_top`, absModN-`q` conversion lemmas (§3.8),
  `remark8_i_int`: bridge `q(B−B) ⊆ {0,6}` → `remark8_i` hypothesis
  (pairwise digit-diffs ∈ {0,±1}) via `qdig_eMod_sub_etd7_same`.

### 5.4 The six case theorems (independently compilable)

```lean
theorem case61 {m : ℕ} (hm : 2 ≤ m) {A : Finset ℕ} (hcard : A.card = 5)
    (hpos : ∀ d ∈ A, 0 < d) (hunit : ∀ d ∈ A, padicValNat 7 d = 0)
    {s : ZMod 7} (hs : s ∈ ({1,2,4} : Finset (ZMod 7)))
    (hcls : ∀ d ∈ A, runit7 d = s) :
    ∃ lam : ℕ, ¬ 7 ∣ lam ∧ good7 m lam A

theorem case62 {m : ℕ} (hm : 2 ≤ m) {A1 Ar : Finset ℕ}
    (hc1 : A1.card = 4) (hcr : Ar.card = 1)
    (hpos : ∀ d ∈ A1 ∪ Ar, 0 < d) (hunit : ∀ d ∈ A1 ∪ Ar, padicValNat 7 d = 0)
    {s : ZMod 7} (hs : s ∈ ({1,2,4}:_))
    (h1 : ∀ d ∈ A1, runit7 d = s)
    (hr : ∀ d ∈ Ar, runit7 d ∈ ({2*s, 4*s} : Finset _)) :
    ∃ lam : ℕ, ¬ 7 ∣ lam ∧ good7 m lam (A1 ∪ Ar)

theorem case63 {m : ℕ} (hm : 2 ≤ m) {A1 A2 A4 : Finset ℕ}
    (hc1 : A1.card = 3) (hc2 : A2.card = 1) (hc4 : A4.card = 1)
    (hpos : ∀ d ∈ A1 ∪ A2 ∪ A4, 0 < d) (hunit : ∀ d ∈ _, padicValNat 7 d = 0)
    {s : ZMod 7} (hs : s ∈ ({1,2,4}:_))
    (h1 : ∀ d ∈ A1, runit7 d = s) (h2 : ∀ d ∈ A2, runit7 d = 2*s)
    (h4 : ∀ d ∈ A4, runit7 d = 4*s) :
    ∃ lam : ℕ, ¬ 7 ∣ lam ∧ good7 m lam (A1 ∪ A2 ∪ A4)

theorem case64 {m : ℕ} (hm : 2 ≤ m) {A1 A2 : Finset ℕ}
    (hc1 : A1.card = 3) (hc2 : A2.card = 2) ... (h2 : runit7 = 2*s) : ...

theorem case65 {m : ℕ} (hm : 2 ≤ m) {A1 A4 : Finset ℕ}
    (hc1 : A1.card = 3) (hc4 : A4.card = 2) ... (h4 : runit7 = 4*s) : ...

theorem case66 {m : ℕ} (hm : 2 ≤ m) {A1 A2 A4 : Finset ℕ}
    (hc1 : A1.card = 2) (hc2 : A2.card = 2) (hc4 : A4.card = 1) ... : ...
```

### 5.5 Top theorem

```lean
/-- The case `|A| = 5`, `m ≥ 2` (paper §6): five units plus a top-level
element admit a multiplier with all distances `≥ M/7`. -/
theorem lrc7_case5m (A : Finset ℕ) (hA : A.card = 5)
    (hpos : ∀ d ∈ A, 0 < d) (hunit : ∀ d ∈ A, padicValNat 7 d = 0)
    (hcls : ∀ d ∈ A, runit7 d ∈ ({1, 2, 4} : Finset (ZMod 7)))
    {m : ℕ} (hm : 2 ≤ m)
    (d6 : ℕ) (hd6 : padicValNat 7 d6 = m) (hd6pos : 0 < d6) :
    ∃ lam M : ℕ, 0 < lam ∧ 0 < M ∧ 7 ∣ M ∧
      ∀ d ∈ A ∪ {d6}, M / 7 ≤ absModN (lam * d) M
```
Assembly: choose `s` = argmax-apLen class (gives `hord`); rotate `s` so the
shape matches a case; dispatch to `case61`–`case66` obtaining `lam` with
`good7 m lam A`; convert each `d ∈ A` via `absModN_ge_iff_qdig7`
(`ν(λd) = 0 < m`); `d6` via `absModN_top_ge7`; `M := 7^{m+1}`.
Then `lrc7_case5m` has the *same output shape* as `lrc7_m1`, so `IntCase`
treats them uniformly.

**Cardinality-split completeness**: with `A1` = max-apLen class and free
`s`-rotation (`s ↦ 2s` cycles `(A1,A2,A4) ↦ (A2,A4,A1)`; `s ↦ 4s` the other
direction), every 5-split reduces to one of: `(5,0,0)`→61, `(4,·,·)`→62
(leftover covers both `2s`,`4s`), `(3,1,1)`→63, `(3,2,0)`→64, `(3,0,2)`→65,
`(2,2,1)`→66 (singleton placed in A4 by rotation — singletons have
`ℓ = 1` so never the max-length class unless all ℓ = 1; handle that
degenerate subcase inside case66's Lemma-5 path or note it separately:
if all three classes have `apLen ≤ 2`… actually (15) covers it).

---

## 6. Verified finite facts (from `_dev/sec6spec/verify.py`)

| Claim | Result |
|---|---|
| 6.6(a) bad set under model `A2={2k−x,2k−x+1}`, `d5={4y+4k}`, `k∈{1,2,3}` | exactly `{(4,2),(4,4),(5,4),(6,4),(6,6)}` = paper (16) |
| 6.6(a) ε-shift: `∀(p,q) ∃ε₁ε₂∈{0,1}: (p−ε₁,q−ε₂) ∉ bad` | all covered |
| 6.6(b) no-good-k pairs | `(a,b) ∈ {(2,4),(2,5),(4,4),(4,5)}` ⇒ avoid-set `a ∉ {2,4}` exact |
| 6.3 (ii.2) h=m bad `(i,j)` | `{i∈{0,6},j∈{2,3}} ∪ {j∈{0,6},i∈{4,5}}` = 8 pairs; `(ẽ34,ẽ45)`-form matches paper |
| 6.3 ε-shift coverage | all covered |
| 6.5(ii.1)(b) `q(A4)={i,i+4}` all-Λ₀-fail | iff `i ∈ {2,6}` |
| 6.5 `\|e\|≥5N/14 ⇒ \|2e\|≤2N/7`; `\|e\|∈[2N/7,5N/14] ⇒ \|3e\|≤N/7` | true for N=49,343 |
| 6.1 `apLen{0,6,a,b}` | ≤5 ∀ pairs except `{2,4}` (ℓ=6) |
| 6.1 ×3 dichotomy under `q(B−B)⊆{0,6}` | 0 failures / 26754 (N=49 model) |

---

## 7. Flagged gaps & risks

- **R1 (`q(7d)` ε-trick, highest risk)** — §6.3 (ii.2) `h=m` and §6.6(a):
  realizing `(ẽ34,ẽ45) = (q(e34)−ε₁, q(e45)−ε2)` via `q(λ·7d₃)=4ε₁+2ε₂` is a
  2-digit carry computation through `d3 → d4 = 2d3+tN/7 → d5`. The paper's
  "routine checking" is genuinely a small carry theorem (see `§3.7`).
  Recommend: implement `digit7_multLow_one` first, then a bespoke lemma
  `exists_lambda1_eps` producing the ε-pair; verify the whole claim by
  `decide` over the *digit variables* `(q, a)` if it can be made parametric
  in `m` (the relevant digits are `m`, `m−1`, `1`, `0` only).
- **R2** — §6.6 `ν(e12)=ν(e34)<m` branch: the `{0,1,5,6}` vs `{0,6}`
  reading determines whether ℓ ≤ 3 or ℓ ≤ 2 results; EJC-txt garbled.
  Check PDF p.16; the `{0,6}` version suffices and is probably correct.
- **R3** — §6.5 (ii.1)(b) `e34 = 5N/7` tail: verify `ẽ(2d3,2d4) = 3` /
  `q(2A4) = {1,2}` reconstruction; also `e45 = 4N/7` normalization via the
  `r(e45) ∈ {1,2,4}` rename.
- **R4** — `eMod7 = 0` edge (`ν(e) > m`): excluded by `≠ 0` hypotheses;
  make sure case splits cover `ν(e) ≥ m+1` (residue 0) — it implies
  `q(e) = 0` which is usually *good* (difference already inside `{0,6}`)
  — handle explicitly or rule out where the paper's "ν = m" is claimed.
- **R5** — Lemma 9/7 conclusions must be stated on the *scaled* elements
  (`lam * d`) with `ẽ`/`q` evaluated at scale `m` — the
  `etd7_multLow_same/low` invariance lemmas only cover `Λ_j` at levels
  `≤ common level`; `Λ_m` scalars change `ẽ` in a controlled way
  (`etd7` is `ZMod 7`-linear in `c` when `runit7` scales — needs a
  `etd7_multTop` lemma: `etd7 m (c*x) (c*y) = c*etd7 m x y`-ish —
  actually `q(c d) = c·q(d)` only for level-`m` elements; for level 0
  `q(cd)` has carries — the `ẽ` under scalars is the carry-bound relation
  again; flag that `ẽ` after `multTop` is NOT exact).
- **R6** — `lemma5`'s `hord` (A1 = max-length class): the case theorems
  that use `lemma5` must get `apLen A2 ≤ apLen A1 ∧ apLen A4 ≤ apLen A1`
  of the *q-images at the moment of application* — since `Λ₀` shifts
  preserve `apLen` (translation-invariant — need `apLen_image_add` lemma,
  easy) but `Λ_h`/`Λ_m` do not, apply `lemma5` only at the final step.
- **R7** — the (3,1,1) exception: `lemma5` returns the disjunct
  `∀d∈A2,∀d'∈A4: 2d−d' ∈ {2,4}` on *q-digits*; the case proofs escape it
  via Lemma 7 — order: Lemma 7's `λ` perturbs `q(A1)`; re-establish
  `ℓ(A1) ≤ 3` *after* it (difference-structure argument), then apply
  `lemma5`'s main disjunct.
- **R8** — Lemma 10/11's `∃`-labeled elements: proofs are pigeonhole
  arguments on `ν`/`r` assignments; consider a helper `Finset` lemma for
  "two pairs share a vertex" and `r`-value counting on `ZMod 7`
  (`|r(E)|` cases: `= 1` impossible?, `< 6`, `= 6`).

## 8. Suggested parallel split (each unit independently compilable)

Prereq (shared, must land first — small): §3.1, §3.2, §3.4, §3.7, §3.8
helpers + `exists_lambda0_of_shift` (§5.1). Put them in `Differences.lean`/
`Compress.lean` or a new `Case5mBase.lean` so case files only consume them.

| Unit | Content | Deps | Est. |
|---|---|---|---|
| B0 base | §3 helpers, `good7`, Λ₀-bridges | Discrete/Filtering/Differences/Compress | ~600 ln |
| B1 lemma7 | `lemma7_i/ii` + `7d` machinery | B0 | ~300 ln |
| B2 lemma9/10/11 | numbering + 3-compression | B0 | ~500 ln |
| C1 case61 | §6.1 | B0–B2 | ~300 ln |
| C2 case62 | §6.2 | B0–B2 | ~300 ln |
| C3 case63 | §6.3 (incl. ũ-table) | B0–B2 + `decide` table | ~600 ln |
| C4 case64 | §6.4 | B0–B2 | ~250 ln |
| C5 case65 | §6.5 | B0–B2 + absModN lemmas | ~350 ln |
| C6 case66 | §6.6 | B0–B2 + bad-pair decides | ~400 ln |
| C7 top | `lrc7_case5m` assembly | all cases | ~200 ln |

C1–C6 depend only on B0–B2 → parallel. C3 is the largest (table);
C6 second (two sub-branches + ε-trick). Cases can live in one file
`Case5m.lean` with `section`-separated private lemmas, or split
`Case5m61.lean`… if compile times demand.

---

## 9. Structured summary for the orchestrator

- **Status**: §6 fully decomposed; all finite combinatorial claims
  independently verified (`_dev/sec6spec/verify.py`); pdftotext corruptions
  resolved against `_external/bs7-ejc.pdf` (full text in
  `_dev/sec6spec/ejc_pages.txt`) — verdict table at §0.2.
- **Deliverable ready**: signatures in §5; missing-lemma inventory in §3
  (≈ 20 items; the only *hard* one is the `7d` carry engine §3.7/R1).
- **New findings vs earlier notes**: (i) §6.6(a)'s printed `(2k−1)−ẽ` is a
  typo — correct is `q(d3) = q(d4)+1` exact (level-m `e34` forces `f3=f4`,
  no borrow); (ii) §6.5(b)'s `{4,5}` is exact with `q(d4) = i+4`;
  (iii) §6.2's `e15`-exception: `{1,2,4}`-stabilizer scalars also handle
  `r ∈ {2,4}` (not just the paper's `3`); (iv) §6.1's ×3 dichotomy needs
  the `q(B−B) ⊆ {0,6}` difference-condition coupling (free carries fail)
  — so `lemma9_i` must *emit* that condition, not just `apLen ≤ 2`.
- **Two genuinely open micro-steps** (paper text insufficient as printed;
  repairs proposed in-line): R2 — §6.6 `ν(e12)=ν(e34)<m`, `r`-differs:
  needs `{0,6}` on both `e`s (verified 0-fail) but printed `{0,1,5,6}`-route
  is insufficient (128 counterexamples); `f = e12−2e34` leaves a 7-config
  residual band. R3 — §6.5(b) `e34 = 5N/7` tail: `ẽ = 3` not derivable
  from `lemma7_ii` as stated; needs a `lemma7_ii'` returning the exact
  `ẽ`-set `{r(e),r(e)−1}`.
- **Key architectural rule**: multiplier order `Λ_m → Λ_h → Λ₀`; all
  needed invariants live in `e`-residues (`ν ≥ 1`) which `Λ₀` and
  `Λ_{h<level}` preserve; `lemma5/6/12` are applied last.
- **Top shape**: `lrc7_case5m` mirrors `lrc7_m1` (`∃ lam M …`), with
  `hm : 2 ≤ m` and `hcls : runit7 d ∈ {1,2,4}` from sign-flip preprocessing.
- **Do not** start Lean work before B0's `digit7_multLow_one` design is
  settled — it determines whether the ε-tricks are `decide`-able.
- **Parallel split**: B0–B2 shared base (~1400 ln), C1–C6 case theorems
  independently (~2200 ln), C7 assembly (~200 ln). See §8.

---

## ERRATUM 2026-09-19 — `lemma9_i` pair condition (countermodel + repair)

**Countermodel**: the spec's conclusion `∀ x y ∈ B, qdig7 m (eMod7 m (λx) (λy)) ∈ {0,6}`
is **unprovable** when some difference hits `ν(e) = m` (the paper's `λx = N/7` edge:
`qdig(7^m) = 1 ∉ {0,6}`, and any exact `c·7^m` residue reverses to `(7−c)·7^m` with
`q ∈ {1..6}\{0,6}`). Empirically confirmed: exhaustive λ-search for `B=(295,8,1)`,
`m=2`, `ν(e13)=2=m` — zero all-pairs-`{0,6}` solutions (`_dev/scratch/check_l9*.py`).

**Repair** (verified): relax the pair condition to `{0,1,6}` —
```lean
(∀ x ∈ B, ∀ y ∈ B, qdig7 m (eMod7 m (lam*x) (lam*y)) ∈ ({0,1,6} : Finset (ZMod 7)))
```
- Provable in all cases: `ν(x),ν(y)<m` → paper route gives `{0,6}` ⊆ `{0,1,6}`;
  `ν(·)=m` edge → paper's `λx=N/7` gives pair qdigs in `{0,1,6}` exactly
  (forward `q=1`, reversal `q=6`; cross pairs `{0,6}`).
- Sufficient for §6.1: the ×3 dichotomy re-verified under the relaxed
  `q(B−B) ⊆ {0,1,6}` constraint — **0 failures / 41160** configs (294 configs
  are covered only by the relaxed bound; they correspond to `f`-equality cases).
- `apLen ≤ 2` conjunct unchanged: empirically always jointly achievable
  (400/400 instances, worst = 2). In Lean the `apLen` proof should NOT go via
  `remark8_i_int` (needs `{0,6}`); prove the digit structure directly
  (diffs can reach `±2`, so the `λ`-choice argument matters).

**`lemma9_ii` unaffected** — its hypothesis already has `h < m`, no `N/7` edge.

## ADDENDUM 2026-09-19 — C7 `hc6` adapter: `normU7` non-injectivity

`normU7 (7^{m+1})` can collapse `A.image` below 5: `d_i ≡ −d_j mod N` maps to the
same rep (each rep has ≤ 2 preimages), so `|A'| ∈ {3,4,5}`. Mathematically
harmless — colliding pairs satisfy `circ(λd_i) = circ(λd_j)` (identical
constraints) — but `lrc7_case5m`'s `A.card = 5` hypothesis breaks.

**Adapter spec for `hc6`** (inside `lrc7_case5m` or the hc6 wrapper):
1. `A' := A.image (normU7 (7^(m+1)))`; `|A'| ≥ 3` (≤2 preimages per rep).
2. `|A'| = 5` → normalize done; dispatch `case61`–`case66` on `A'`.
3. `|A'| = 4` → `D' := A' ∪ {d6}` has `level7 D' 0 = A'` (card 4), top `d6` at
   `ν = m` → apply `lrc7_case4` directly (its hypotheses match: `0<m`, `hmax`,
   `card ≤ 6`).
4. `|A'| = 3` → needs a small leaf: 3 units + top `d6`. Route via `filtered7`
   on the 3 units (|F| capacity OK) + `absModN_top_ge7` for `d6`; or reuse an
   existing `exists_multLow_set_qdig`-style lemma. Budget a separate named
   lemma `lrc7_case3u_top` if no existing API closes it.
Transfer each `d ∈ A`'s bound via `normU7_absModN`; `¬7∣lam` not required by
hc6's output shape.

### ERRATUM update — dual resolution adopted

The `lemma9_i` agent (`c4d283e5`) independently found the same countermodel and
chose the **hypothesis fix**: `hνm : ν(x) < m ∧ ν(y) < m`, keeping `{0,6}` —
implemented in `Research07/LRC7/Case5mL9.lean`. This is the **primary** form
(`remark8_i_int` bridge applies verbatim).

**Consumer guidance**: apply `lemma9_i` wherever the `hνm` bound is derivable
(e.g. via `e`-additivity: `e23 ≡ e21 − e31`, so `ν(e21) > ν(e31)` forces
`ν(e23) = ν(e31) < m` for the *base-d3* pair choice; the *base-d1* choice
`x = e21` can leave `ν(x) = m`). Where an `m`-edge genuinely persists, use the
`{0,1,6}` variant below instead — same `λ`-construction, weaker pair bound:

```lean
theorem lemma9_i' {m : ℕ} {b1 b2 b3 : ℕ} (... same hyps, NO hνm ...) :
    ∃ lam : ℕ, ¬ 7 ∣ lam ∧
      (∀ x ∈ B, ∀ y ∈ B, qdig7 m (eMod7 m (lam*x) (lam*y)) ∈ ({0,1,6})) ∧
      apLen (B.image (fun d => qdig7 m (lam*d))) ≤ 2
```

`{0,1,6}` is negation-closed and covers the `N/7` edge (verified: dichotomy
0-fail under it). Do NOT rewrite `lemma9_i` itself — the two forms coexist.

**Refined fallback routing** (supersedes item 4 above): `|A'| ≥ 3` always
(≤2 preimages per rep). Routes: `|A'| = 5` → `case61`–`case66`;
`|A'| = 4` → `lrc7_case4` on `A' ∪ {d6}`; `|A'| = 3` → `A' ∪ {d6}` has ≤ 4
elements — either (a) `lrc5_int` gives `circ ≥ 1/5 ≥ 1/7` at the ℝ-level and
the hc6 adapter converts (needs a `circ≥1/5` → `absModN` cert bridge — check
whether lrc5's internals expose a `(λ,M)` cert; if not, ℝ-bridge via the
EXISTING `lrc7_int_of`-style conversion is needed), or (b) a direct
`Λ₀`-shift lemma on 3 units (single class: `apLen ≤ 3` → 4 valid shifts vs
2 forbidden; split classes: `quad_point_avoid`-adjacent — verify the
`1+1+1` finite fact before choosing).

**|A'| = 3 resolved** (verified 2026-09-19): with `t ∈ ZMod 7` including `0`
(the `λ = 1` identity shift), every `(p₁,p₂,p₃)` and every class-coefficient
pattern `(1,1,2)/(1,1,4)/(1,2,2)/(1,4,4)/(1,2,4)` admits a `Λ₀` shift
avoiding `{0,6}` — **0 failures / all configs**. So `lrc7_case3u_top` is a
small leaf: partition `A'` by `runit7`-class, apply the `lemma5/6/12`
union-shift with `t` from the finite fact, `absModN_top_ge7` covers `d6`.
No `lrc5` bridge needed.

**`|A'| = 3` IMPLEMENTED** (2026-09-19): `lrc7_case3u_top` proved GREEN in
`_dev/scratch/Case3uTop.lean` (exit=0, axioms whitelist, ~9GB). The proof is
the counting argument (cleaner than enumerating coefficient patterns): each
of the ≤3 shifted points `p + c·t` (`c ∈ {1,2,4}`) forbids ≤ 2 shifts
`t = (v−p)·c⁻¹`, `v ∈ {0,6}` — a `badShift`-biUnion of card ≤ 6 < 7, so a
valid `t` exists; then `exists_lambda0_of_shift` (s=1) gives `λ ∈ Λ₀` with
`good7`, `absModN_ge_iff_qdig7` covers the units, `absModN_top_ge7` covers
`d6`. Output: `∃ λ, 0<λ ∧ ¬7∣λ ∧ ∀d∈A∪{d6}, 7^m ≤ absModN (λd) N` — drops
straight into the `hc6` adapter. Pending: move to a tree file at C7 merge.

**§6.1 boundary dichotomy VERIFIED** (2026-09-19, `_dev/scratch/Case61DichotP.lean`):
`case61_dichot'` — the `×3` dichotomy survives the `{0,1,6}` pair envelope
of `lemma9_i'` (1526/1526 admissible configs; raw `decide` over 7⁶ vars
times out, so the proof mirrors `case61_dichot`'s skeleton). Constraint
direction flips: `(0,6)`-pairs are unconstrained, `(6,0)`-pairs give
`f₀ ≤ f₆` (non-strict, `case61_flt'_dec`); `case61_mem_t2'_dec` takes the
non-strict `f ≤ f₆` bound. With this + `case61_dichot`, Case A covers both
lemma9 forms: `hνm` → `{0,6}` → `case61_dichot`; boundary → `{0,1,6}` →
`case61_dichot'`.

**§6.1 Case B digit-shift VERIFIED** (same session,
`_dev/scratch/Case61B.lean`): `qdig7_add_top_resid` —
`x ≡ y + k·7^m (mod 7^{m+1})` ⇒ `qdig7 m x = qdig7 m y + k` (exact, no
borrow). This is the lemma making `q(A₁)` a translate of the top-residue
digits `K = {k₂,…,k₅}` in the `ν(E) = {m}` sub-case; combined with
`apLen_four_dilate` (already in Case5mBase) it gives `ℓ(A₁) ≤ 5` after the
dilating scalar.

**§6.6 delicate branch (r-differs, h<m) — recipe VERIFIED** (2026-09-19):
the EJC text says "we can set `e12` and `e34` in `{0,6}` by Lemma [9]" —
Lemma 9 needs a shared-base triple so a literal application fails; the
working construction is the f-trick composite `λ = λ₂·λ₁`:

* `f := (e12 − 2·e34) % N` (residue; `r(e12) = 2r(e34)` ⇒ leading digits
  cancel ⇒ `ν(f) > h`; symmetric case `2r(e12) = r(e34)` uses `f = 2e12−e34`).
* `λ₂ ∈ Λ_h` (`multLow7 m h`): sets `q(λ₂·(λ₁e34))` to any target via
  `exists_multLow_set_qdig` — the exhaustive check uses target `∈ {0,6}`.
* `λ₁`: `ν(f) < m` → `exists_multLow_set_qdig` on `f` (`q(λ₁f) = t_f`);
  `ν(f) = m` → `exists_top_scalar_set` (scalar `c ∈ {1,…,6}`, `q = t_f ≠ 0`);
  `ν(f) > m` (f ≡ 0) → `λ₁ = 1`. `residN_multLow7` keeps `λ₂` from
  disturbing `λ₁f` (applied second, `h < ν(f)`).
* `λ = λ₂·λ₁`; `¬7∣λ` (`runit7 = 1` for `Λ_{<m}` factors; scalar `∈{1..6}`).
* `λe12 ≡ λf + 2·λe34 (mod N)` ⇒ `q(λe12)` determined by the two set
  digits + carry.

Exhaustive check (`m∈{1,2,3}`, all level-`h` residue pairs with r-ratio 2,
`k₂ ∈ {0..6}`, `t_f ∈ {0..6}`, `λ₁` restricted to units `{1,…,6}` at
`ν(f)=m`): **15012 configs, 0 failures** — some `(k₂, t_f)` always works.
Lean proof shape: `by_cases` on `ν(f)` vs `m`, then a small disjunction
over the carry; the search space is the same 49-combo budget as the
`filtered7` two-target setting.

**`hord` signature amendment** (2026-09-19): `lemma5`/`lemma6`/`lemma12`
consume `hord : apLen A₂ ≤ apLen A₁ ∧ apLen A₄ ≤ apLen A₁` on the digit
sets *at application time* — the paper's "we may assume `ℓ(A₁) ≥ ℓ(A₂),
ℓ(A₄)`" WLOG. The §5.4 case signatures omitted it; the case theorems
`case63`–`case66` (any that invoke `lemma5`/`lemma6`/`lemma12` on
multi-class unions) should carry

```lean
(hord : apLen (A2.image (qdig7 m)) ≤ apLen (A1.image (qdig7 m)) ∧
        apLen (A4.image (qdig7 m)) ≤ apLen (A1.image (qdig7 m)))
```

and the `lrc7_case5m` dispatcher picks `A1` = an argmax-`apLen` class
(finite argmax over the ≤3 nonempty classes; ties broken arbitrarily).
`apLen_image_add` (Case5mBase:164) makes `apLen` translation-invariant, so
a Λ₀-shifted set keeps its ordering — `hord` transfers through the
`exists_lambda0_of_shift` stage. Non-Λ₀ scalings (×2/×3 rescues) do NOT
preserve `apLen`; in those sub-branches the proof re-establishes ordering
on the scaled sets or avoids `lemma5` entirely.

## Addendum 2026-10-06c — shared §6 helpers now in Case5mTop.lean (GREEN)

Two new public lemmas, verified, axioms `[propext, Classical.choice, Quot.sound]`:

* `exists_lambda0_qdig_06` (Case5mTop, end of file): for a single-class
  unit set `B` (`∀d∈B, padicValNat=0`, `runit7 d = s`, `s≠0`) with
  `apLen (B.image (qdig7 m)) ≤ 2`, produces `∃ lam ∈ multLow7 m 0` with
  `∀ d ∈ B, qdig7 m (lam*d) ∈ {0,6}` — the paper's "by (7) we may assume
  q(B) ⊂ {0,6}" step. NOTE: Λ₀-shifts do NOT disturb pair-difference
  digits (eMod7 levels ≥1 ⇒ λ_k·e ≡ e mod N) and do NOT disturb lower
  digits f (λ_k·b ≡ b mod 7^m) — so dichot hypotheses survive the shift.
* `apLen_06_pair` (Case5mTop): `{p,q} ≠ {2,4} → apLen {0,6,p,q} ≤ 5`
  (verified: `{2,4}` is the UNIQUE bad pair, giving ℓ=6 on {0,2,4,6}).
* `good7_of_smul_apLen` (Case5mTop, end): `apLen((λ'·A).image qdig7) ≤ 5`
  + `¬7∣λ'` → `∃lam, ¬7∣lam ∧ good7 m lam A` — the shared case-endgame
  finisher (scales + Λ₀-shifts in one step).
* `lrc7_case3u_top` (Case5mTop): collapse fallback, `card ≤ 3` single-
  class-set union variant — used by `lrc7_hc6_of` for `|A'| ≤ 3`.

For case61: apply `h10`/`h9ii` → get `λ₁` with `apLen(λ₁·B)≤2` →
`exists_lambda0_qdig_06` on `λ₁·B` (all class `runit7 λ₁·s`) → digits of B
in `{0,6}`; pair conditions unchanged since pair-differences have level ≥1
and Λ₀ multipliers fix them (prove: `0 < padicValNat 7 e → qdig7 m
((1+k*7^m)*e) = qdig7 m e` via `qdig7_lambda0`-adjacent reasoning — the
shift term `k·runit7 e` vanishes since `runit7 e = 0` when `7∣e`).
Then `{q4,q5}≠{2,4}` → `apLen_06_pair` + `apLen_mono'` (private in file:
`X⊆Y → apLen X ≤ apLen Y`) → `exists_lambda0_avoid`/`good7_of_smul_apLen`.
`{q4,q5}={2,4}` → ×3-rescale + `case61_dichot`/`case61_dichot'` (needs the
`qdig7 m (3*x)` carry formula `3q + ⌊3f/7⌋` — prove locally).

## ERRATUM 2026-10-06d — `lemma10` hypothesis form (countermodel)

Per `_dev/failures.md` (2026-09-19 entry): the `hsame : ∀ d d' ∈ A1, d≠d' →
residueRelOf d d' = same` form of Lemma 10 is **FALSE** — countermodel
`{1,50,99,3}` at m=1 (mixed classes 1/3/6 with all pairs `same`, all
`eMod7` levels 0, no valid numbering). The faithful hypothesis is the
equal-unit-residue form (same as `lemma11`):

```lean
(s : ZMod 7) (hsame : ∀ d ∈ A1, runit7 d = s)
```

**All case agents (61/62/63/…)**: if your contract gave you an `h10`
hypothesis with the `residueRelOf`-form premise, NOTE the fix — in the
case context you have `hcls : ∀ d ∈ A1, runit7 d = s` which satisfies
BOTH forms. Preferred: if `lemma10` has already landed in
`Case5mL10.lean` when you write your proof, use the REAL theorem
directly and drop the `h10` parameter; otherwise keep `h10` as written
but isolate its use to a single `obtain` site (the orchestrator will
shim the premise/level-measure differences at instantiation — the real
lemma10 may emit `elevel7`-based conclusions like `lemma11` does; under
`eMod7 ≠ 0`, `elevel7 = padicValNat` via `elevel7_of_ne`-style lemmas).

## Addendum 2026-10-06e — h9ii bound is `apLen ≤ j` (j-indexed)

`lemma9_ii`'s real conclusion per spec §3.5 is `apLen ≤ j` (j∈{2,3}),
not a flat `≤3`. Case agents parameterizing on `h9ii` must use the
j-indexed bound — `j=2` yields the `≤2` needed by
`exists_lambda0_qdig_06`; `j=3` yields `≤3` + `{0,±1,±2}` pairs for
`remark8_ii`.

## ADDENDUM 2026-09-19 (orchestrator, late session)

**`case61_dichot`/`case61_dichot'` (ZMod7-f form) are NOT applicable at m≥2.**
A single `f : ZMod 7` cannot encode both the residue order (`x % 7^m`
comparison, needed for the borrow hypotheses) and the real ×3 carry
`⌊3·(x % 7^m)/7^m⌋` (middle third {3,4} has only 2 slots for 3 distinct
residues). Python: 9/1804 valid triples admit no faithful `f`. The
dichotomy CONCLUSION itself is true (m=2 real-carry check: 0 bad under
`{0,6}` and `{0,1,6}` envelopes on `q(bᵢ)∈{0,6}`-constrained triples);
an honest `(qᵢ, eᵢ=⌊3rᵢ/7^m⌋, bᵢⱼ=⟦rᵢ<rⱼ⟧)` model verifies 0-bad/390 and
0-bad/552 models — the abstract lemma needs only e-monotonicity under
borrow-1 and tie→e-equal (no transitivity/antisymmetry needed; `{0,1,6}`
envelope suffices for both). ac471cb7 independently reached the same
conclusion and is building `case61_dichot_nat` (real `fᵢ : ℕ < 7^m` form,
structured proof) inside `Case5mC61.lean` — that file is the canonical
location; do not duplicate the name in shared files.

**Aggregation probe verified** (`_dev/scratch/AggProbe.lean`):
`lrc7_hc6_aux (case61 hm) (case62 hm) (case63 hm) (case64 hm) (case65 hm)
(case66 hm) A hA hpos hnd d6 hd6 hd6pos hm` type-checks (each `caseXY hm`
matches its `hcXY` slot; `2 ≤ m` vs `1 < m` is defeq). Final `lrc7_hc6`
must live in a new `Case5m.lean` (or `Main.lean` itself) importing all six
`Case5mC6x` files — NOT `Case5mTop.lean` (cycle: cases import Top).

**Dead agent:** 4521234e (case62) produced only 3 scratch `decide` facts
(`_dev/scratch/Case62A.lean`: `case62_apLen4_of_ne3`, `case62_dilate2_dec`,
`case62_apLen_rescaled` — all correct, reusable). Re-dispatched as d51a8976.

## Addendum 2026-09-19 (post-crash): lemma9_ii strengthened + lemma10 signature

`lemma9_ii` (Case5mL10.lean) now returns the FIVE-conjunct form:

    ∃ lam, ¬ 7 ∣ lam ∧
      qdig7 m (eMod7 m (lam*b2) (lam*b3)) ∈ {0,5,6} ∧
      (∀ x y ∈ {b1,b2,b3}, qdig7 m (eMod7 m (lam*x) (lam*y)) ∈ {0,1,5,6}) ∧
      (j = 2 → ∀ x y ∈ {b1,b2,b3}, qdig7 m (eMod7 m (lam*x) (lam*y)) ∈ {0,6}) ∧
      apLen (image qdig) ≤ j

(the proof already established the pair bounds internally via `hBL`;
they are now exported — same `lam`, no new hypotheses).
Destructuring pattern: `⟨lam, hlam7, hdig056, hp0156, hp06j2, hap⟩`.

`lemma10` (Case5mL10.lean:1192) signature:

    theorem lemma10 {m} {A1 : Finset ℕ} (hcard : 4 ≤ A1.card)
        (hpos) (hunit) (s : ZMod 7) (hsame : ∀ d ∈ A1, runit7 d = s) :
        ∃ d1 ∈ A1, ∃ d2 ∈ A1, ∃ d3 ∈ A1, ∃ d4 ∈ A1,
          (six pairwise ≠) ∧ (ν(e21) > ν(e31) ∨ (∃ ℓ, uniform ∧ r31=2r21 ∧ r41∈{3,4}r21))

note the hypothesis is `∀ d ∈ A1, runit7 d = s` (class form), NOT
`residueRelOf = same` — the same-rel form cannot be inverted without
ratioCases. `Case5mC61.lean` shows the canonical use (`case61 hm lemma10 lemma9_ii`).

`case61` is DONE (green, axioms clean). Its `hsame`/`hsameB` pattern for
building `residueRelOf = same` from `runit7 = s` is at Case5mC61:1240ish
(`rel_same`).
