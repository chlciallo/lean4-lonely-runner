/-
Copyright (c) 2026 Research07 contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Research07 contributors
-/
import Research07.LRC7.Compress
import Research07.LRC7.Differences

/-!
# Shared helper layer for the `|A| = 5, m ≥ 2` cases (Barajas–Serra §6)

This file is the "B0" base of the §6 formalization (see
`_reports/lrc7-sec6-spec.md`): `ℕ`- and `ZMod 7`-level plumbing lemmas consumed
by the case theorems `case61`–`case66` and the `Λ₁`-`7d` carry engine.

Contents:

* `enu7` — the `ν`-level of a difference residue `eMod7 m x y` (§3.1), with
  `Λ_j`-index bookkeeping (`multLow7` membership, verbatim `eMod7` under
  `Λ_{j<ν}`) and `enu7_le_of_ne`.
* `qdig_eMod_sub_etd7_two` — Lemma 4(ii), two-sided case:
  `q(e) − ẽ ∈ {0,±1}` when `residueRelOf ≠ same` (§3.2); also the unconditional
  `qdig_eMod_sub_etd7` (`∈ {0,1,6}`) and the digit-difference form
  `qdig_eMod_sub` for same-class pairs.
* `qdig7_smul_carry` — iterated carry bound `q(c·x) ∈ c·q(x) + {0,…,c−1}`
  (§3.4, paper eqs. (5)/(9)).
* `filtered7_mod7` — `filtered7` with the extra invariant `lam % 7 = 1`
  (hence `runit7 (lam*d) = runit7 d` via `runit7_mul`); `exists_multLow_set_qdig`
  (Λ_j digit bijectivity); `residN_top`/`exists_top_scalar_set` (level-`m`
  residue normalization, §3.6/§3.8).
* `eMod7` algebra (§3.8): `eMod7_mul`, `eMod7_add`, `eMod7_zmod_cast`.
* `absModN ↔ qdig7` conversions at scale `N = 7^{m+1}` (§3.8): all the
  `|x|_N`-vs-`q(x)` facts used in §6.5, plus the `2x`/`3x` band bounds.
* `good7` predicate + `Λ₀` bridges (§5.1): `good7_mul`, `qdig7_lambda0`,
  `exists_lambda0_avoid`, `exists_lambda0_of_shift`, `apLen_image_add`,
  `remark8_i_int`.
* Finite `ZMod 7` lemmas (§5.2): `private …_dec := by decide` certificates with
  public wrappers, incl. the §6.3 ũ-table (`case63_table`/`case63_table_rescue`)
  and the `bad63`/`bad66a` bad-pair sets.

Conventions mirror `Compress.lean`/`Case4.lean`: `avoids06` models
`q(λA) ∩ {0,6} = ∅`; `Λ₀ = multLow7 m 0` shifts `q(d) ↦ q(d)+k·r(d)`.
-/

private instance : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩

/-! ### §3.1 `e`-level helper and `Λ`-index arithmetic -/

/-- ν of a difference residue; garbage when the residue is `0` (`ν(e) ≥ m+1`). -/
abbrev enu7 (m x y : ℕ) : ℕ := padicValNat 7 (eMod7 m x y)

/-- `Λ_j` membership for `k < 7`. -/
theorem mem_multLow7 {m j k : ℕ} (hk : k < 7) :
    1 + k * 7 ^ (m - j) ∈ multLow7 m j :=
  Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr hk, rfl⟩

/-- `Λ₀` membership for `k < 7`. -/
theorem mem_multLow7_zero {m k : ℕ} (hk : k < 7) :
    1 + k * 7 ^ m ∈ multLow7 m 0 := by
  have h := mem_multLow7 (m := m) (j := 0) hk
  rwa [Nat.sub_zero] at h

/-- A `Λ_j` element is `1 + k·7^{m−j}` for some `k < 7`. -/
theorem eq_one_add_of_mem_multLow7 {m j lam : ℕ} (h : lam ∈ multLow7 m j) :
    ∃ k < 7, lam = 1 + k * 7 ^ (m - j) := by
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp h
  exact ⟨k, Finset.mem_range.mp hk, rfl⟩

/-- `Λ_j` elements are `7`-units for `j < m`. -/
theorem not_dvd_of_mem_multLow7 {m j lam : ℕ} (hjm : j < m)
    (h : lam ∈ multLow7 m j) : ¬ 7 ∣ lam := by
  obtain ⟨k, -, rfl⟩ := eq_one_add_of_mem_multLow7 h
  exact multLow_not_dvd hjm

/-- `Λ₀` elements are `7`-units for `m > 0`. -/
theorem not_dvd_of_mem_multLow7_zero {m lam : ℕ} (hm : 0 < m)
    (h : lam ∈ multLow7 m 0) : ¬ 7 ∣ lam :=
  not_dvd_of_mem_multLow7 hm h

/-- `eMod7` is verbatim under `Λ_j` for `j` below both element levels
(residues and `runit7` are both preserved). -/
theorem eMod7_multLow_low {m j k x y : ℕ} (hjm : j < m)
    (hx : j < padicValNat 7 x) (hy : j < padicValNat 7 y)
    (hxm : padicValNat 7 x ≤ m) (hx0 : x ≠ 0)
    (hym : padicValNat 7 y ≤ m) (hy0 : y ≠ 0) :
    eMod7 m ((1 + k * 7 ^ (m - j)) * x) ((1 + k * 7 ^ (m - j)) * y)
      = eMod7 m x y := by
  have hxres := residN_multLow7 (k := k) hjm hx
  have hyres := residN_multLow7 (k := k) hjm hy
  have hxm' : padicValNat 7 ((1 + k * 7 ^ (m - j)) * x) ≤ m := by
    rw [padicValNat_mul_seven (multLow_not_dvd hjm) hx0]
    exact hxm
  have hym' : padicValNat 7 ((1 + k * 7 ^ (m - j)) * y) ≤ m := by
    rw [padicValNat_mul_seven (multLow_not_dvd hjm) hy0]
    exact hym
  have hx0' : (1 + k * 7 ^ (m - j)) * x ≠ 0 := mul_ne_zero (by omega) hx0
  have hy0' : (1 + k * 7 ^ (m - j)) * y ≠ 0 := mul_ne_zero (by omega) hy0
  have hrx := runit7_eq_of_mod hxres hxm' hx0'
  have hry := runit7_eq_of_mod hyres hym' hy0'
  unfold eMod7
  rw [hrx, hry, hxres, hyres]

/-- The `e`-level is verbatim under `Λ_j` for `j` below both element levels. -/
theorem enu7_multLow_low {m j k x y : ℕ} (hjm : j < m)
    (hx : j < padicValNat 7 x) (hy : j < padicValNat 7 y)
    (hxm : padicValNat 7 x ≤ m) (hx0 : x ≠ 0)
    (hym : padicValNat 7 y ≤ m) (hy0 : y ≠ 0) :
    enu7 m ((1 + k * 7 ^ (m - j)) * x) ((1 + k * 7 ^ (m - j)) * y)
      = enu7 m x y := by
  unfold enu7
  rw [eMod7_multLow_low hjm hx hy hxm hx0 hym hy0]

/-- A nonzero difference residue has level `≤ m` (`eMod7` is already a
residue mod `7^{m+1}`, so `ν > m` would force `e = 0`). -/
theorem enu7_le_of_ne {m x y : ℕ} (h : eMod7 m x y ≠ 0) : enu7 m x y ≤ m := by
  have hlt : eMod7 m x y < 7 ^ (m + 1) := by
    unfold eMod7
    split_ifs <;> exact Nat.mod_lt _ (Nat.pow_pos (by norm_num))
  by_contra hm
  push Not at hm
  have hdvd : 7 ^ (m + 1) ∣ eMod7 m x y :=
    (Nat.pow_dvd_iff_le_padicValNat (by norm_num) h).mpr hm
  have h0 : eMod7 m x y = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hlt
  exact h h0

/-! ### §5.1 The `good7` goal predicate and `Λ₀` bridges -/

/-- A multiplier is *good* for `A` at level `m` if every scaled leading
digit avoids `{0,6}` (equivalently `|λd|_N ≥ 7^m` via `absModN_ge_iff_qdig7`). -/
def good7 (m lam : ℕ) (A : Finset ℕ) : Prop :=
  ∀ d ∈ A, qdig7 m (lam * d) ∉ ({0, 6} : Finset (ZMod 7))

theorem good7_empty (m lam : ℕ) : good7 m lam (∅ : Finset ℕ) := fun _ h => by
  simp at h

/-- Composition: `good7` on the scaled image pulls back to `good7` on `A`. -/
theorem good7_mul {m lam lam' : ℕ} {A : Finset ℕ}
    (h : good7 m lam' (A.image (lam * ·))) : good7 m (lam' * lam) A := by
  intro d hd
  have hd' : lam * d ∈ A.image (lam * ·) := Finset.mem_image.mpr ⟨d, hd, rfl⟩
  have hg := h _ hd'
  rwa [← mul_assoc] at hg

/-- Bridge to the `Compress.lean` shift lemmas: a `Λ₀`-element shifts `qdig`
by `k·runit7` (this is `qdig7_multLow` at `j = 0`; the `m = 0` edge is
proved directly since `qdig7 0 y = ↑y`). -/
theorem qdig7_lambda0 {m d k : ℕ} (hd : padicValNat 7 d = 0) :
    qdig7 m ((1 + k * 7 ^ m) * d) = qdig7 m d + (k : ZMod 7) * runit7 d := by
  rcases eq_or_ne m 0 with rfl | hm
  · have hq : ∀ y : ℕ, qdig7 0 y = (y : ZMod 7) := fun y => by
      rw [qdig7_eq_cast_div, pow_zero, Nat.div_one]
    have hr : runit7 d = (d : ZMod 7) := by
      unfold runit7
      rw [hd, pow_zero, Nat.div_one]
    rw [hq, hq, hr, pow_zero]
    push_cast
    ring
  · have h0m : 0 < m := Nat.pos_of_ne_zero hm
    have h := qdig7_multLow (j := 0) (k := k) h0m hd
    rwa [Nat.sub_zero] at h

/-- Translation invariance of `apLen` (risk R6): shifting a residue set does
not change its covering length. -/
theorem apLen_image_add (X : Finset (ZMod 7)) (t : ZMod 7) :
    apLen (X.image (· + t)) = apLen X := by
  have hstep : ∀ (Y : Finset (ZMod 7)) (s : ZMod 7),
      apLen (Y.image (· + s)) ≤ apLen Y := by
    intro Y s
    have hY : apLen Y ≤ 7 := apLen_le_seven Y
    obtain ⟨i, hi⟩ := (apLen_le_iff Y (apLen Y) hY).mp le_rfl
    have himg : Y.image (· + s) ⊆ cycIv (i + s) (apLen Y) := by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      have hxy : x + s - (i + s) = x - i := by ring
      rw [mem_cycIv, hxy]
      exact (mem_cycIv.mp (hi hx))
    exact (apLen_le_iff (Y.image (· + s)) (apLen Y) hY).mpr ⟨i + s, himg⟩
  apply le_antisymm
  · exact hstep X t
  · have h1 := hstep (X.image (· + t)) (-t)
    have hid : (X.image (· + t)).image (· + -t) = X := by
      rw [Finset.image_image]
      rw [show ((fun x : ZMod 7 => x + -t) ∘ fun x => x + t) = fun x => x from by
        funext x
        simp only [Function.comp_apply]
        ring]
      exact Finset.image_id'
    rw [hid] at h1
    exact h1

/-- Shift lemma, integer level: `apLen ≤ 5` on the `q`-image ⇒ some
`λ ∈ Λ₀` is good (uniform shift since all `runit7 = s`). -/
theorem exists_lambda0_avoid {m : ℕ} (_hm : 0 < m) {A : Finset ℕ} {s : ZMod 7}
    (hs : s ≠ 0) (hunit : ∀ d ∈ A, padicValNat 7 d = 0)
    (hsame : ∀ d ∈ A, runit7 d = s)
    (h : apLen (A.image (qdig7 m)) ≤ 5) :
    ∃ lam ∈ multLow7 m 0, good7 m lam A := by
  classical
  set X := A.image (qdig7 m)
  obtain ⟨i, hi⟩ := (apLen_le_iff X 5 (by norm_num)).mp h
  obtain ⟨t, ht⟩ := exists_shift_avoid (le_refl 5) hi
  set K : ZMod 7 := t * s⁻¹ with hK
  have hKs : K * s = t := by
    rw [hK, mul_assoc, inv_mul_cancel₀ hs, mul_one]
  refine ⟨1 + K.val * 7 ^ m, mem_multLow7_zero (ZMod.val_lt K), ?_⟩
  intro d hd
  have hq := qdig7_lambda0 (m := m) (d := d) (k := K.val) (hunit d hd)
  rw [ZMod.natCast_zmod_val K] at hq
  have hqd : qdig7 m d ∈ X := Finset.mem_image.mpr ⟨d, hd, rfl⟩
  have hmem : qdig7 m d + t ∈ X.image (· + t) :=
    Finset.mem_image.mpr ⟨qdig7 m d, hqd, rfl⟩
  have hnb := ht _ hmem
  have hsh : qdig7 m ((1 + K.val * 7 ^ m) * d) = qdig7 m d + t := by
    rw [hq, hsame d hd, hKs]
  rw [hsh]
  exact hnb

/-- **The workhorse** joining `lemma5`/`lemma6`/`lemma12`/`exists_shift_avoid`
to integer multipliers: the shift `t` produced by a `ZMod 7` covering lemma is
realized by `λ = 1 + k·7^m ∈ Λ₀` with `k = t·s⁻¹` — class-`c·s` elements shift
by `c·t` automatically. -/
theorem exists_lambda0_of_shift {m : ℕ} (hm : 0 < m) {s : ZMod 7} (hs : s ≠ 0)
    {A : Finset ℕ} (hunit : ∀ d ∈ A, padicValNat 7 d = 0)
    (hcls : ∀ d ∈ A, runit7 d ∈ ({s, 2 * s, 4 * s} : Finset (ZMod 7)))
    (t : ZMod 7)
    (h : avoids06
      (((A.filter fun d => runit7 d = s).image (qdig7 m)).image (· + t)
        ∪ ((A.filter fun d => runit7 d = 2 * s).image (qdig7 m)).image (· + 2 * t)
        ∪ ((A.filter fun d => runit7 d = 4 * s).image (qdig7 m)).image (· + 4 * t))) :
    ∃ lam ∈ multLow7 m 0, good7 m lam A := by
  classical
  set K : ZMod 7 := t * s⁻¹ with hK
  have hKs : K * s = t := by
    rw [hK, mul_assoc, inv_mul_cancel₀ hs, mul_one]
  rw [avoids06_union3] at h
  obtain ⟨h1, h2, h4⟩ := h
  refine ⟨1 + K.val * 7 ^ m, mem_multLow7_zero (ZMod.val_lt K), ?_⟩
  intro d hd
  have hq := qdig7_lambda0 (m := m) (d := d) (k := K.val) (hunit d hd)
  rw [ZMod.natCast_zmod_val K] at hq
  have hmem := hcls d hd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with hr | hr | hr
  · -- class `s`: `q(λd) = q(d) + t` lands in the shifted `A₁`-image.
    have hqd : qdig7 m d ∈ (A.filter fun d => runit7 d = s).image (qdig7 m) :=
      Finset.mem_image.mpr ⟨d, Finset.mem_filter.mpr ⟨hd, hr⟩, rfl⟩
    have hsh : qdig7 m ((1 + K.val * 7 ^ m) * d) = qdig7 m d + t := by
      rw [hq, hr, hKs]
    rw [hsh]
    exact h1 _ (Finset.mem_image.mpr ⟨qdig7 m d, hqd, rfl⟩)
  · -- class `2s`: `q(λd) = q(d) + 2t`.
    have hqd : qdig7 m d ∈ (A.filter fun d => runit7 d = 2 * s).image (qdig7 m) :=
      Finset.mem_image.mpr ⟨d, Finset.mem_filter.mpr ⟨hd, hr⟩, rfl⟩
    have hK2 : K * (2 * s) = 2 * t := by rw [mul_left_comm K 2 s, hKs]
    have hsh : qdig7 m ((1 + K.val * 7 ^ m) * d) = qdig7 m d + 2 * t := by
      rw [hq, hr, hK2]
    rw [hsh]
    exact h2 _ (Finset.mem_image.mpr ⟨qdig7 m d, hqd, rfl⟩)
  · -- class `4s`: `q(λd) = q(d) + 4t`.
    have hqd : qdig7 m d ∈ (A.filter fun d => runit7 d = 4 * s).image (qdig7 m) :=
      Finset.mem_image.mpr ⟨d, Finset.mem_filter.mpr ⟨hd, hr⟩, rfl⟩
    have hK4 : K * (4 * s) = 4 * t := by rw [mul_left_comm K 4 s, hKs]
    have hsh : qdig7 m ((1 + K.val * 7 ^ m) * d) = qdig7 m d + 4 * t := by
      rw [hq, hr, hK4]
    rw [hsh]
    exact h4 _ (Finset.mem_image.mpr ⟨qdig7 m d, hqd, rfl⟩)

/-! ### §3.2 Lemma 4(ii), non-same case

The proof mirrors `qdig_eMod_sub_etd7_same`: decompose the residues as
`q·7^m + f` and read off the top digit of `e'` case by case. For
`e = 2x−y` (twoX) the expression `2x' + N − y'` has top digit `2q₁−q₂+δ`
with `δ ∈ {−1,0,1}` according to `2f₁` vs `f₂`; twoY is symmetric. -/

/-- `(a·7^m + b) / 7^m = a` when `b < 7^m` (local copy; the original is
`private` in `Differences.lean`). -/
private theorem mul_pow_add_div {a b m : ℕ} (hb : b < 7 ^ m) :
    (a * 7 ^ m + b) / 7 ^ m = a := by
  have hP : 0 < 7 ^ m := Nat.pow_pos (by norm_num)
  rw [add_comm (a * 7 ^ m) b, mul_comm a (7 ^ m),
    Nat.add_mul_div_left _ _ hP, Nat.div_eq_of_lt hb, zero_add]

/-- `(a % 7^{m+1}) / 7^m` and `a / 7^m` agree modulo `7`. -/
private theorem div_mod_pow_cast (a m : ℕ) :
    (((a % 7 ^ (m + 1)) / 7 ^ m : ℕ) : ZMod 7)
      = ((a / 7 ^ m : ℕ) : ZMod 7) := by
  rw [pow_succ', Nat.mod_mul_left_div_self,
    ZMod.natCast_eq_natCast_iff', Nat.mod_mod]

/-- `qdig7` of a wrapped residue equals the unwrapped digit cast. -/
private theorem qdig7_eMod_of (m a : ℕ) :
    qdig7 m (a % 7 ^ (m + 1)) = ((a / 7 ^ m : ℕ) : ZMod 7) := by
  rw [qdig7_eq_cast_div]
  exact div_mod_pow_cast a m

/-- Decompose `x % 7^{m+1}` as `q·7^m + f` with `q < 7`, `f < 7^m`. -/
private theorem residue_decomp {m x : ℕ} :
    ∃ q f : ℕ, x % 7 ^ (m + 1) = q * 7 ^ m + f ∧ q < 7 ∧ f < 7 ^ m := by
  refine ⟨(x % 7 ^ (m + 1)) / 7 ^ m, (x % 7 ^ (m + 1)) % 7 ^ m, ?_, ?_,
    Nat.mod_lt _ (Nat.pow_pos (by norm_num))⟩
  · rw [mul_comm, Nat.div_add_mod]
  · rw [Nat.div_lt_iff_lt_mul (Nat.pow_pos (by norm_num)), ← pow_succ']
    exact Nat.mod_lt _ (Nat.pow_pos (by norm_num))

/-- Cast a truncated-subtraction digit expression into `ZMod 7`. -/
private theorem natCast_sub_add {a b c : ℕ} (h : c ≤ a + b) :
    ((a + b - c : ℕ) : ZMod 7) = (a : ZMod 7) + b - c := by
  have hcast : ((a + b - c : ℕ) : ZMod 7)
      = (((a + b - c : ℕ) : ℤ) : ZMod 7) := by simp
  rw [hcast, Int.ofNat_sub h]
  push_cast
  ring

/-- **Lemma 4(ii), non-same case**: for `e = 2x−y` or `e = 2y−x`,
`q(e) − ẽ ∈ {0,±1}` — the borrow at the top digit is `−1`, `0` or `+1`.
The proof mirrors `qdig_eMod_sub_etd7_same`: decompose the residues as
`q·7^m + f`, expand `2a + 7^{m+1} − b` into a digit block plus a low block,
and read off the top digit in each of the three borrow branches. -/
theorem qdig_eMod_sub_etd7_two {m x y : ℕ}
    (hrel : residueRelOf x y ≠ residueRel.same) :
    qdig7 m (eMod7 m x y) - etd7 m x y ∈ ({0, 1, 6} : Finset (ZMod 7)) := by
  obtain ⟨q1, f1, hX, hq1, hf1⟩ := residue_decomp (m := m) (x := x)
  obtain ⟨q2, f2, hY, hq2, hf2⟩ := residue_decomp (m := m) (x := y)
  have hP : 0 < 7 ^ m := Nat.pow_pos (by norm_num)
  have hNe : (7 : ℕ) ^ (m + 1) = 7 * 7 ^ m := pow_succ' 7 m
  -- Shared computation: the top digit of `2u + 7^{m+1} − v`, where
  -- `u = qa·7^m + fa`, `v = qb·7^m + fb`, is `2qa − qb + δ` with
  -- `δ ∈ {−1,0,1}` according as `2fa` borrows/carries against `fb`.
  have aux : ∀ (qa fa qb fb : ℕ), qa < 7 → fa < 7 ^ m → qb < 7 → fb < 7 ^ m →
      (((2 * (qa * 7 ^ m + fa) + 7 ^ (m + 1) - (qb * 7 ^ m + fb))
          / 7 ^ m : ℕ) : ZMod 7) - (2 * (qa : ZMod 7) - qb)
        ∈ ({0, 1, 6} : Finset (ZMod 7)) := by
    intro qa fa qb fb hqa hfa hqb hfb
    have hB : qb * 7 ^ m ≤ 6 * 7 ^ m :=
      Nat.mul_le_mul (by omega : qb ≤ 6) (le_refl (7 ^ m))
    by_cases hfb2 : fb ≤ 2 * fa
    · by_cases hlt : 2 * fa - fb < 7 ^ m
      · -- no borrow and no carry: digit `2qa + 7 − qb` (≡ `2qa − qb`)
        have hexp : (2 * qa + 7 - qb) * 7 ^ m
            = 2 * (qa * 7 ^ m) + 7 * 7 ^ m - qb * 7 ^ m := by
          rw [Nat.sub_mul, Nat.add_mul, mul_assoc]
        have hcalc : 2 * (qa * 7 ^ m + fa) + 7 ^ (m + 1) - (qb * 7 ^ m + fb)
            = (2 * qa + 7 - qb) * 7 ^ m + (2 * fa - fb) := by
          rw [hNe, hexp]
          omega
        rw [hcalc, mul_pow_add_div hlt]
        have hq : ((2 * qa + 7 - qb : ℕ) : ZMod 7)
            = 2 * (qa : ZMod 7) - qb := by
          rw [natCast_sub_add (by omega : qb ≤ 2 * qa + 7)]
          have h7 : ((7 : ℕ) : ZMod 7) = 0 := by decide
          rw [h7]
          push_cast
          ring
        rw [hq]
        have he : 2 * (qa : ZMod 7) - qb - (2 * (qa : ZMod 7) - qb) = 0 := by
          ring
        rw [he]
        decide
      · -- carry `+1`: `2fa − fb = 7^m + c`, digit `2qa + 8 − qb`
        have hge : 7 ^ m ≤ 2 * fa - fb := by omega
        have hexp : (2 * qa + 8 - qb) * 7 ^ m
            = 2 * (qa * 7 ^ m) + 8 * 7 ^ m - qb * 7 ^ m := by
          rw [Nat.sub_mul, Nat.add_mul, mul_assoc]
        have hcalc : 2 * (qa * 7 ^ m + fa) + 7 ^ (m + 1) - (qb * 7 ^ m + fb)
            = (2 * qa + 8 - qb) * 7 ^ m + (2 * fa - fb - 7 ^ m) := by
          rw [hNe, hexp]
          omega
        rw [hcalc, mul_pow_add_div (by omega : 2 * fa - fb - 7 ^ m < 7 ^ m)]
        have hq : ((2 * qa + 8 - qb : ℕ) : ZMod 7)
            = 2 * (qa : ZMod 7) - qb + 1 := by
          rw [natCast_sub_add (by omega : qb ≤ 2 * qa + 8)]
          have h8 : ((8 : ℕ) : ZMod 7) = 1 := by decide
          rw [h8]
          push_cast
          ring
        rw [hq]
        have he : 2 * (qa : ZMod 7) - qb + 1 - (2 * (qa : ZMod 7) - qb)
            = 1 := by
          ring
        rw [he]
        decide
    · -- borrow `−1`: digit `2qa + 6 − qb`
      have hlt : 2 * fa < fb := by omega
      have hexp : (2 * qa + 6 - qb) * 7 ^ m
          = 2 * (qa * 7 ^ m) + 6 * 7 ^ m - qb * 7 ^ m := by
        rw [Nat.sub_mul, Nat.add_mul, mul_assoc]
      have hcalc : 2 * (qa * 7 ^ m + fa) + 7 ^ (m + 1) - (qb * 7 ^ m + fb)
          = (2 * qa + 6 - qb) * 7 ^ m + (7 ^ m + 2 * fa - fb) := by
        rw [hNe, hexp]
        omega
      rw [hcalc, mul_pow_add_div (by omega : 7 ^ m + 2 * fa - fb < 7 ^ m)]
      have hq : ((2 * qa + 6 - qb : ℕ) : ZMod 7)
          = 2 * (qa : ZMod 7) - qb - 1 := by
        rw [natCast_sub_add (by omega : qb ≤ 2 * qa + 6)]
        have h6 : ((6 : ℕ) : ZMod 7) = -1 := by decide
        rw [h6]
        push_cast
        ring
      rw [hq]
      have he : 2 * (qa : ZMod 7) - qb - 1 - (2 * (qa : ZMod 7) - qb)
          = -1 := by
        ring
      rw [he]
      decide
  -- Split on the actual `if` conditions of `eMod7`/`etd7`; `hrel` rules out
  -- the `same` branch (where neither `2`-ratio holds).
  by_cases h2x : runit7 y = 2 * runit7 x
  · -- `e = 2x − y`, `ẽ = 2q(x) − q(y)`
    have hE : eMod7 m x y
        = (2 * (x % 7 ^ (m + 1)) + 7 ^ (m + 1) - (y % 7 ^ (m + 1)))
          % 7 ^ (m + 1) := by
      unfold eMod7
      rw [if_pos h2x]
    have hEt : etd7 m x y = 2 * (q1 : ZMod 7) - q2 := by
      unfold etd7
      rw [if_pos h2x]
      show 2 * qdig7 m x - qdig7 m y = _
      unfold qdig7
      rw [hX, hY, mul_pow_add_div hf1, mul_pow_add_div hf2]
    rw [hE, hEt, qdig7_eMod_of, hX, hY]
    exact aux q1 f1 q2 f2 hq1 hf1 hq2 hf2
  · by_cases h2y : runit7 x = 2 * runit7 y
    · -- `e = 2y − x`, `ẽ = 2q(y) − q(x)`
      have hE : eMod7 m x y
          = (2 * (y % 7 ^ (m + 1)) + 7 ^ (m + 1) - (x % 7 ^ (m + 1)))
            % 7 ^ (m + 1) := by
        unfold eMod7
        rw [if_neg h2x, if_pos h2y]
      have hEt : etd7 m x y = 2 * (q2 : ZMod 7) - q1 := by
        unfold etd7
        rw [if_neg h2x, if_pos h2y]
        show 2 * qdig7 m y - qdig7 m x = _
        unfold qdig7
        rw [hY, hX, mul_pow_add_div hf2, mul_pow_add_div hf1]
      rw [hE, hEt, qdig7_eMod_of, hY, hX]
      exact aux q2 f2 q1 f1 hq2 hf2 hq1 hf1
    · exact absurd ((residueRelOf_eq_same).mpr ⟨h2x, h2y⟩) hrel

/-- Same-branch digit-difference form: `q(e)` is `q(x) − q(y)` up to a
borrow `∈ {0,6}` (i.e. `q(x)−q(y) ∈ q(e)+{0,1}`). -/
theorem qdig_eMod_sub {m x y : ℕ} (hrel : residueRelOf x y = residueRel.same) :
    qdig7 m (eMod7 m x y) - (qdig7 m x - qdig7 m y)
      ∈ ({0, 6} : Finset (ZMod 7)) := by
  have h := qdig_eMod_sub_etd7_same (m := m) hrel
  obtain ⟨hne1, hne2⟩ := (residueRelOf_eq_same).mp hrel
  have hEt : etd7 m x y = qdig7 m x - qdig7 m y := by
    unfold etd7
    rw [if_neg hne1, if_neg hne2]
  rwa [hEt] at h

/-- **Lemma 4(ii), unconditional**: `q(e) − ẽ ∈ {0,±1}` in all branches
(`{0,6}` in the same-`r` case, `{0,±1}` otherwise). -/
theorem qdig_eMod_sub_etd7 {m x y : ℕ} :
    qdig7 m (eMod7 m x y) - etd7 m x y ∈ ({0, 1, 6} : Finset (ZMod 7)) := by
  by_cases h : residueRelOf x y = residueRel.same
  · have h2 := qdig_eMod_sub_etd7_same (m := m) h
    rcases Finset.mem_insert.mp h2 with h0 | h6
    · rw [h0]
      decide
    · rw [Finset.mem_singleton] at h6
      rw [h6]
      decide
  · exact qdig_eMod_sub_etd7_two h

/-! ### §3.4 Iterated carry bound (paper eqs. (5)/(9)) -/

/-- `q(c·x) ∈ c·q(x) + {0,…,c−1}`: induction on `c` using `qdig7_add_one`;
each step adds a carry of `0` or `1`, so the total carry has `val < c`. -/
theorem qdig7_smul_carry {m c x : ℕ} (hc0 : 0 < c) (hc : c < 7) :
    (qdig7 m (c * x) - (c : ZMod 7) * qdig7 m x).val < c := by
  induction c with
  | zero => omega
  | succ c ih =>
    rcases eq_zero_or_pos c with hc0' | hc0'
    · subst hc0'
      rw [show (0 : ℕ) + 1 = 1 from rfl, Nat.cast_one, one_mul, one_mul, sub_self,
        ZMod.val_zero]
      exact Nat.one_pos
    · have ih' := ih hc0' (by omega)
      set E := qdig7 m (c * x) - (c : ZMod 7) * qdig7 m x with hE
      have hδ := qdig7_add_one m c x
      set δ := qdig7 m ((c + 1) * x) - qdig7 m (c * x) - qdig7 m x with hδ'
      have hstep : qdig7 m ((c + 1) * x) - ((c + 1 : ℕ) : ZMod 7) * qdig7 m x
          = δ + E := by
        rw [hδ', hE]
        push_cast
        ring
      rw [hstep]
      have hsum : δ.val + E.val < 7 := by omega
      have hcast : δ + E = ((δ.val + E.val : ℕ) : ZMod 7) := by
        rw [Nat.cast_add, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
      rw [hcast, ZMod.val_natCast, Nat.mod_eq_of_lt hsum]
      omega

/-- Finset-membership form (the spec signature): the carry lies in
`(range c).image Nat.cast`. -/
theorem qdig7_smul_carry_mem {m c x : ℕ} (hc0 : 0 < c) (hc : c < 7) :
    qdig7 m (c * x) - (c : ZMod 7) * qdig7 m x
      ∈ (Finset.range c).image (fun n : ℕ => (n : ZMod 7)) := by
  have h := qdig7_smul_carry (m := m) (x := x) hc0 hc
  rw [Finset.mem_image]
  exact ⟨(qdig7 m (c * x) - (c : ZMod 7) * qdig7 m x).val,
    Finset.mem_range.mpr h, ZMod.natCast_zmod_val _⟩

/-! ### §3.5 `Λ_j` digit bijectivity -/

/-- Corollary of `qdig7_multLow` + `runit7_ne_zero`: for `ν(x) = j < m` the
leading digit can be set to any `c : ZMod 7` by a `Λ_j` element. -/
theorem exists_multLow_set_qdig {m j x : ℕ} (hjm : j < m)
    (hx : padicValNat 7 x = j) (hx0 : x ≠ 0) (c : ZMod 7) :
    ∃ k : ℕ, k < 7 ∧ qdig7 m ((1 + k * 7 ^ (m - j)) * x) = c := by
  have hr : runit7 x ≠ 0 := runit7_ne_zero (Nat.pos_of_ne_zero hx0)
  set K : ZMod 7 := (c - qdig7 m x) * (runit7 x)⁻¹ with hK
  refine ⟨K.val, ZMod.val_lt K, ?_⟩
  rw [qdig7_multLow hjm hx, ZMod.natCast_zmod_val K, hK]
  have hmul : (c - qdig7 m x) * (runit7 x)⁻¹ * runit7 x = c - qdig7 m x := by
    rw [mul_assoc, inv_mul_cancel₀ hr, mul_one]
  rw [hmul]
  ring

/-! ### §3.6 Level-`m` residue normalization -/

/-- A level-`m` residue is exactly `q·7^m` (`r(x) = qdig7 m x`). -/
theorem residN_top {m x : ℕ} (hx : padicValNat 7 x = m) :
    x % 7 ^ (m + 1) = (qdig7 m x).val * 7 ^ m := by
  rcases eq_or_ne x 0 with rfl | hx0
  · subst hx
    simp [qdig7]
  set u := Nat.divMaxPow x 7 with hu
  have hx_eq : x = u * 7 ^ m := by
    have h := Nat.divMaxPow_mul_pow_padicValNat 7 x
    rw [hx, ← hu] at h
    exact h.symm
  have hu7 : ¬ 7 ∣ u := Nat.not_dvd_divMaxPow (by norm_num) hx0
  have hmod : x % 7 ^ (m + 1) = (u % 7) * 7 ^ m := by
    rw [hx_eq, pow_succ', Nat.mul_mod_mul_right]
  have hq : (qdig7 m x).val = u % 7 := by
    unfold qdig7
    rw [hx_eq, pow_succ', Nat.mul_mod_mul_right,
      Nat.mul_div_cancel _ (Nat.pow_pos (by norm_num)), ZMod.val_natCast,
      Nat.mod_mod]
  rw [hmod, hq]

/-- For `ν(x) = m`, a `Λ_m` scalar normalizes the residue to any
`t·7^m` with `t ≠ 0` (`c = t·r(x)⁻¹`). -/
theorem exists_top_scalar_set {m x : ℕ} (hx : padicValNat 7 x = m) (hx0 : x ≠ 0)
    {t : ZMod 7} (ht : t ≠ 0) :
    ∃ c : ℕ, 0 < c ∧ c < 7 ∧ (c * x) % 7 ^ (m + 1) = t.val * 7 ^ m ∧
      qdig7 m (c * x) = t := by
  have hr : runit7 x ≠ 0 := runit7_ne_zero (Nat.pos_of_ne_zero hx0)
  set C : ZMod 7 := t * (runit7 x)⁻¹ with hC
  have hC0 : C ≠ 0 := mul_ne_zero ht (inv_ne_zero hr)
  have hcpos : 0 < C.val := by
    have : C.val ≠ 0 := by rwa [Ne, ZMod.val_eq_zero]
    omega
  have hc7 : ¬ 7 ∣ C.val := by
    intro hdvd
    have h0 : C.val = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (ZMod.val_lt C)
    exact hC0 ((ZMod.val_eq_zero C).mp h0)
  have hval : padicValNat 7 (C.val * x) = m := by
    rw [padicValNat_mul_seven hc7 hx0, hx]
  have hq : qdig7 m (C.val * x) = t := by
    rw [qdig7_multTop hx, ZMod.natCast_zmod_val C, hC, mul_assoc,
      inv_mul_cancel₀ hr, mul_one]
  refine ⟨C.val, hcpos, ZMod.val_lt C, ?_, hq⟩
  rw [residN_top hval, hq]

/-! ### §3.8 `runit7`/`eMod7` algebra and `absModN` conversions -/

/-- `runit7` is multiplicative (the unit part mod 7 of a product is the
product of unit parts). -/
theorem runit7_mul (a b : ℕ) :
    runit7 (a * b) = runit7 a * runit7 b := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp [runit7]
  rcases eq_or_ne b 0 with rfl | hb
  · simp [runit7]
  have hν : padicValNat 7 (a * b) = padicValNat 7 a + padicValNat 7 b :=
    padicValNat.mul ha hb
  have hda : a / 7 ^ padicValNat 7 a * 7 ^ padicValNat 7 a = a :=
    Nat.div_mul_cancel
      ((Nat.pow_dvd_iff_le_padicValNat (by norm_num) ha).mpr le_rfl)
  have hdb : b / 7 ^ padicValNat 7 b * 7 ^ padicValNat 7 b = b :=
    Nat.div_mul_cancel
      ((Nat.pow_dvd_iff_le_padicValNat (by norm_num) hb).mpr le_rfl)
  have hab : a * b = (a / 7 ^ padicValNat 7 a) * (b / 7 ^ padicValNat 7 b)
      * 7 ^ (padicValNat 7 a + padicValNat 7 b) := by
    conv_lhs => rw [← hda, ← hdb]
    rw [pow_add]
    ring
  unfold runit7
  rw [hν, hab, Nat.mul_div_cancel _ (Nat.pow_pos (by norm_num))]
  push_cast
  ring

/-- `runit7` of a `≡ 1 (mod 7)` multiplier is `1` (so `ν lam = 0`). -/
theorem runit7_eq_one_of_mod7 {lam : ℕ} (h : lam % 7 = 1) : runit7 lam = 1 := by
  have h0 : lam ≠ 0 := by
    rintro rfl
    simp at h
  have hν : padicValNat 7 lam = 0 := by
    apply padicValNat.eq_zero_of_not_dvd
    intro hd
    rw [Nat.dvd_iff_mod_eq_zero] at hd
    omega
  unfold runit7
  rw [hν, pow_zero, Nat.div_one]
  exact (ZMod.natCast_eq_natCast_iff' _ _ _).mpr h

/-- Multiplying by `lam ≡ 1 (mod 7)` preserves `runit7`. -/
theorem runit7_mul_of_mod7 {lam d : ℕ} (h : lam % 7 = 1) :
    runit7 (lam * d) = runit7 d := by
  rw [runit7_mul, runit7_eq_one_of_mod7 h, one_mul]

/-- `eMod7` as a `ZMod N` value is the defining linear combination. -/
private theorem eMod7_zmod_cast (m x y : ℕ) :
    ((eMod7 m x y : ℕ) : ZMod (7 ^ (m + 1))) =
      if runit7 y = 2 * runit7 x then 2 * (x : ZMod _) - (y : ZMod _)
      else if runit7 x = 2 * runit7 y then 2 * (y : ZMod _) - (x : ZMod _)
      else (x : ZMod _) - (y : ZMod _) := by
  have hcast : ∀ a : ℕ,
      ((a % 7 ^ (m + 1) : ℕ) : ZMod (7 ^ (m + 1))) = (a : ZMod _) := by
    intro a
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr (Nat.mod_mod a _)
  have hN : ((7 ^ (m + 1) : ℕ) : ZMod (7 ^ (m + 1))) = 0 := ZMod.natCast_self _
  unfold eMod7
  split_ifs with h1 h2
  · rw [hcast, Nat.cast_sub (by
      have : y % 7 ^ (m + 1) < 7 ^ (m + 1) := Nat.mod_lt _ (Nat.pow_pos (by norm_num))
      omega : y % 7 ^ (m + 1) ≤ 2 * (x % 7 ^ (m + 1)) + 7 ^ (m + 1))]
    rw [Nat.cast_add, Nat.cast_mul, hcast x, hcast y, hN, Nat.cast_ofNat]
    ring
  · rw [hcast, Nat.cast_sub (by
      have : x % 7 ^ (m + 1) < 7 ^ (m + 1) := Nat.mod_lt _ (Nat.pow_pos (by norm_num))
      omega : x % 7 ^ (m + 1) ≤ 2 * (y % 7 ^ (m + 1)) + 7 ^ (m + 1))]
    rw [Nat.cast_add, Nat.cast_mul, hcast y, hcast x, hN, Nat.cast_ofNat]
    ring
  · rw [hcast, Nat.cast_sub (by
      have : y % 7 ^ (m + 1) < 7 ^ (m + 1) := Nat.mod_lt _ (Nat.pow_pos (by norm_num))
      omega : y % 7 ^ (m + 1) ≤ x % 7 ^ (m + 1) + 7 ^ (m + 1))]
    rw [Nat.cast_add, hcast x, hcast y, hN]
    ring

/-- `eMod7` scales with the multiplier when `runit7 lam = 1` (e.g. `Λ_j`
elements): `e(λx, λy) ≡ λ·e(x,y) (mod 7^{m+1})`. -/
theorem eMod7_mul {m lam x y : ℕ} (hlam : runit7 lam = 1) :
    eMod7 m (lam * x) (lam * y) = (lam * eMod7 m x y) % 7 ^ (m + 1) := by
  have hr : ∀ z : ℕ, runit7 (lam * z) = runit7 z := fun z => by
    rw [runit7_mul, hlam, one_mul]
  have hL : ((eMod7 m (lam * x) (lam * y) : ℕ) : ZMod (7 ^ (m + 1)))
      = (lam * eMod7 m x y : ZMod (7 ^ (m + 1))) := by
    rw [eMod7_zmod_cast, eMod7_zmod_cast, hr x, hr y]
    split_ifs with h1 h2 <;> push_cast <;> ring
  have hlt : eMod7 m (lam * x) (lam * y) < 7 ^ (m + 1) := by
    unfold eMod7
    split_ifs <;> exact Nat.mod_lt _ (Nat.pow_pos (by norm_num))
  rw [← Nat.cast_mul] at hL
  rw [ZMod.natCast_eq_natCast_iff] at hL
  have hL' : eMod7 m (lam * x) (lam * y) % 7 ^ (m + 1)
      = (lam * eMod7 m x y) % 7 ^ (m + 1) := hL
  rwa [Nat.mod_eq_of_lt hlt] at hL'

/-- `e`-chain rule (same-`r` triples): `e(x,y) + e(y,z) ≡ e(x,z)`. -/
theorem eMod7_add {m x y z : ℕ}
    (hxy : residueRelOf x y = residueRel.same)
    (hyz : residueRelOf y z = residueRel.same)
    (hxz : residueRelOf x z = residueRel.same) :
    (eMod7 m x y + eMod7 m y z) % 7 ^ (m + 1) = eMod7 m x z := by
  obtain ⟨hxy1, hxy2⟩ := (residueRelOf_eq_same).mp hxy
  obtain ⟨hyz1, hyz2⟩ := (residueRelOf_eq_same).mp hyz
  obtain ⟨hxz1, hxz2⟩ := (residueRelOf_eq_same).mp hxz
  have hcast : ((eMod7 m x y + eMod7 m y z : ℕ) : ZMod (7 ^ (m + 1)))
      = (eMod7 m x z : ZMod (7 ^ (m + 1))) := by
    rw [Nat.cast_add, eMod7_zmod_cast, eMod7_zmod_cast, eMod7_zmod_cast,
      if_neg hxy1, if_neg hxy2, if_neg hyz1, if_neg hyz2,
      if_neg hxz1, if_neg hxz2]
    ring
  have hlt : eMod7 m x z < 7 ^ (m + 1) := by
    unfold eMod7
    split_ifs <;> exact Nat.mod_lt _ (Nat.pow_pos (by norm_num))
  rw [ZMod.natCast_eq_natCast_iff] at hcast
  have hcast' : (eMod7 m x y + eMod7 m y z) % 7 ^ (m + 1)
      = eMod7 m x z % 7 ^ (m + 1) := hcast
  rwa [Nat.mod_eq_of_lt hlt] at hcast'

/-- `filtered7` with residue bookkeeping: the produced multiplier is a
product of `Λ_j`-elements, hence `lam % 7 = 1` — so `runit7 (lam*d) = runit7 d`
via `runit7_mul_of_mod7`. (Restatement of `filtered7` with the extra
invariant; the `lam` is existential-opaque, so the invariant must be
tracked through the same induction.) -/
theorem filtered7_mod7 (D : Finset ℕ) (hpos : ∀ d ∈ D, 0 < d) {m i₀ : ℕ}
    (_hm : ∀ d ∈ D, padicValNat 7 d ≤ m) (hi₀ : i₀ ≤ m)
    (F : ℕ → Finset (ZMod 7))
    (hlow : ∀ j, j < i₀ → ((level7 D j).sum fun d => (F d).card) ≤ 6) :
    ∃ lam : ℕ, ¬ 7 ∣ lam ∧ lam % 7 = 1 ∧
      (∀ d ∈ D, i₀ ≤ padicValNat 7 d →
        (lam * d) % 7 ^ (m + 1) = d % 7 ^ (m + 1)) ∧
      ∀ d ∈ D, padicValNat 7 d < i₀ →
        qdig7 m (lam * d) ∉ F d := by
  classical
  have key : ∀ t : ℕ, t ≤ i₀ → ∃ lam : ℕ, ¬ 7 ∣ lam ∧ lam % 7 = 1 ∧
      (∀ d ∈ D, i₀ ≤ padicValNat 7 d →
        (lam * d) % 7 ^ (m + 1) = d % 7 ^ (m + 1)) ∧
      ∀ d ∈ D, i₀ - t ≤ padicValNat 7 d → padicValNat 7 d < i₀ →
        qdig7 m (lam * d) ∉ F d := by
    intro t
    induction t with
    | zero =>
      intro _
      refine ⟨1, by decide, by decide, ?_, ?_⟩
      · intro d _ _; rw [one_mul]
      · intro d _ h1 h2; simp at h1; omega
    | succ t ih =>
      intro ht
      obtain ⟨Lam, hLam7, hLammod, hver, hgd⟩ := ih (Nat.le_of_succ_le ht)
      have hLam0 : Lam ≠ 0 := by rintro rfl; exact hLam7 (dvd_zero 7)
      set j := i₀ - (t + 1) with hj
      have hji : j < i₀ := by omega
      have hjm : j < m := by omega
      have hSval : ∀ x ∈ (level7 D j).image (fun d => Lam * d),
          padicValNat 7 x = j := by
        intro x hx
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
        obtain ⟨haD, haν⟩ := Finset.mem_filter.mp ha
        rw [padicValNat_mul_seven hLam7 (ne_of_gt (hpos a haD)), haν]
      have hSpos : ∀ x ∈ (level7 D j).image (fun d => Lam * d), 0 < x := by
        intro x hx
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
        obtain ⟨haD, -⟩ := Finset.mem_filter.mp ha
        exact Nat.mul_pos (Nat.pos_of_ne_zero hLam0) (hpos a haD)
      set F' : ℕ → Finset (ZMod 7) := fun x => F (x / Lam) with hF'def
      have hF'd : ∀ d : ℕ, F' (Lam * d) = F d := by
        intro d
        simp only [hF'def]
        rw [Nat.mul_div_right d (Nat.pos_of_ne_zero hLam0)]
      have hScard : ((level7 D j).image (fun d => Lam * d)).sum
          (fun x => (F' x).card) ≤ 6 := by
        rw [Finset.sum_image]
        · simp only [hF'd]
          exact hlow j hji
        · intro a _ b _ hab
          exact Nat.mul_left_cancel (Nat.pos_of_ne_zero hLam0) hab
      obtain ⟨k, hk7, hkg⟩ := exists_k_all_good7 hjm
        ((level7 D j).image (fun d => Lam * d)) hSval hSpos F' hScard
      have hμ7 : ¬ 7 ∣ 1 + k * 7 ^ (m - j) := multLow_not_dvd hjm
      have hLam'7 : ¬ 7 ∣ (1 + k * 7 ^ (m - j)) * Lam :=
        Nat.Prime.not_dvd_mul Nat.prime_seven hμ7 hLam7
      have hLam'mod : ((1 + k * 7 ^ (m - j)) * Lam) % 7 = 1 := by
        rw [Nat.mul_mod, multLow_mod7 hjm, hLammod]
      refine ⟨(1 + k * 7 ^ (m - j)) * Lam, hLam'7, hLam'mod, ?_, ?_⟩
      · intro d hd hν
        have hd0 : d ≠ 0 := ne_of_gt (hpos d hd)
        have hx : padicValNat 7 (Lam * d) = padicValNat 7 d :=
          padicValNat_mul_seven hLam7 hd0
        have hjx : j < padicValNat 7 (Lam * d) := by rw [hx]; omega
        have h1 := residN_multLow7 (k := k) hjm hjx
        rw [mul_assoc, h1, hver d hd hν]
      · intro d hd hνj hνi
        have hd0 : d ≠ 0 := ne_of_gt (hpos d hd)
        rcases eq_or_lt_of_le hνj with hEq | hLt
        · have hdl : d ∈ level7 D j := Finset.mem_filter.mpr ⟨hd, hEq.symm⟩
          have hxS : Lam * d ∈ (level7 D j).image (fun d => Lam * d) :=
            Finset.mem_image.mpr ⟨d, hdl, rfl⟩
          have hg := hkg (Lam * d) hxS
          rw [hF'd] at hg
          rwa [mul_assoc]
        · have hx : padicValNat 7 (Lam * d) = padicValNat 7 d :=
            padicValNat_mul_seven hLam7 hd0
          have hjx : j < padicValNat 7 (Lam * d) := by rw [hx]; exact hLt
          have h1 := residN_multLow7 (k := k) hjm hjx
          have hqd : qdig7 m (((1 + k * 7 ^ (m - j)) * Lam) * d)
              = qdig7 m (Lam * d) := by
            apply qdig7_congr
            rw [mul_assoc]; exact h1
          rw [hqd]
          exact hgd d hd (by omega) hνi
  obtain ⟨lam, hlam7, hlammod, hver, hgd⟩ := key i₀ le_rfl
  exact ⟨lam, hlam7, hlammod, hver, fun d hd hlt => hgd d hd (by omega) hlt⟩

/-- `|x|_N < 7^m` iff the leading digit is `0` or `6`, provided `ν(x) < m`
(the `f = 0` boundary `x ≡ 6·7^m` is excluded by `7^m ∤ x`). -/
theorem absModN_lt_iff_qdig7 {m y : ℕ} (hval : padicValNat 7 y < m)
    (hy : y ≠ 0) :
    absModN y (7 ^ (m + 1)) < 7 ^ m
      ↔ qdig7 m y ∈ ({0, 6} : Finset (ZMod 7)) := by
  have hge := absModN_ge_iff_qdig7 (d := y) (lam := 1) hval
    (Nat.pos_of_ne_zero hy) (by decide : ¬ 7 ∣ (1 : ℕ))
  rw [one_mul] at hge
  have hval' : (qdig7 m y).val < 7 := ZMod.val_lt _
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro h
    have hn : ¬ (1 ≤ (qdig7 m y).val ∧ (qdig7 m y).val ≤ 5) := by
      intro hc
      have := hge.mpr hc
      omega
    push Not at hn
    by_cases h1 : 1 ≤ (qdig7 m y).val
    · have := hn h1
      have h6 : (qdig7 m y).val = 6 := by omega
      right
      have e : ((qdig7 m y).val : ZMod 7) = 6 := by rw [h6]; decide
      rwa [ZMod.natCast_zmod_val] at e
    · have h0 : (qdig7 m y).val = 0 := by omega
      left
      exact (ZMod.val_eq_zero (qdig7 m y)).mp h0
  · rintro (h0 | h6)
    · have hv : (qdig7 m y).val = 0 := by
        rw [h0]; decide
      have hn : ¬ (1 ≤ (qdig7 m y).val ∧ (qdig7 m y).val ≤ 5) := by omega
      have := hge.mp.mt hn
      omega
    · have hv : (qdig7 m y).val = 6 := by
        rw [h6]; decide
      have hn : ¬ (1 ≤ (qdig7 m y).val ∧ (qdig7 m y).val ≤ 5) := by omega
      have := hge.mp.mt hn
      omega

/-- Forward direction of `absModN_lt_iff_qdig7`: `|x|_N < 7^m` forces
`q(x) ∈ {0,6}` (`ν(x) < m`). -/
theorem qdig_lt_of_absModN_lt {m y : ℕ} (hval : padicValNat 7 y < m)
    (hy : y ≠ 0) (h : absModN y (7 ^ (m + 1)) < 7 ^ m) :
    qdig7 m y ∈ ({0, 6} : Finset (ZMod 7)) :=
  (absModN_lt_iff_qdig7 hval hy).mp h

/-- `|x|_N ≥ 2·7^m` iff `q(x) ∈ {2,3,4}` (`ν(x) < m`; the `5·7^m` boundary
is excluded by `f ≠ 0`). -/
theorem absModN_ge_two_iff_qdig7 {m y : ℕ} (hval : padicValNat 7 y < m)
    (hy : y ≠ 0) :
    2 * 7 ^ m ≤ absModN y (7 ^ (m + 1))
      ↔ qdig7 m y ∈ ({2, 3, 4} : Finset (ZMod 7)) := by
  unfold absModN
  set E := 7 ^ m with hE
  set r := y % 7 ^ (m + 1) with hr
  set e := r / E with he
  set f := r % E with hf
  have hEpos : 0 < E := Nat.pow_pos (by norm_num)
  have hN : 7 ^ (m + 1) = 7 * E := pow_succ' 7 m
  have hrN : r < 7 ^ (m + 1) := Nat.mod_lt _ (Nat.pow_pos (by norm_num))
  have hrN2 : r < 7 * E := by rw [← hN]; exact hrN
  have hr_eq : r = E * e + f := (Nat.div_add_mod r E).symm
  have hf_lt : f < E := Nat.mod_lt _ hEpos
  have he_lt : e < 7 := (Nat.div_lt_iff_lt_mul hEpos).mpr hrN2
  have hfy : f = y % E :=
    Nat.mod_mod_of_dvd y (by rw [hE]; exact Nat.pow_dvd_pow 7 (by omega))
  have hndvd : ¬ 7 ^ m ∣ y := by
    intro h
    have : m ≤ padicValNat 7 y :=
      (Nat.pow_dvd_iff_le_padicValNat (by norm_num) hy).mp h
    omega
  have hf_ne : f ≠ 0 := by
    rw [hfy, hE, Ne, ← Nat.dvd_iff_mod_eq_zero]
    exact hndvd
  have hqval : (qdig7 m y).val = e := by
    unfold qdig7
    rw [ZMod.val_natCast]
    exact Nat.mod_eq_of_lt he_lt
  constructor
  · intro h
    have h1 : 2 * E ≤ r := by
      have := Nat.min_le_left r (7 ^ (m + 1) - r)
      omega
    have h2 : 2 * E ≤ 7 ^ (m + 1) - r := by
      have := Nat.min_le_right r (7 ^ (m + 1) - r)
      omega
    -- `q = e ∈ {2,3,4}`: `e ≥ 2` from `r ≥ 2E`; `e ≤ 4` from `r < 5E` (`f>0`)
    have hf0 : 0 < f := Nat.pos_of_ne_zero hf_ne
    have he2 : 2 ≤ e := by
      by_contra hc
      push Not at hc
      have hE2 : E * e ≤ E * 1 := Nat.mul_le_mul_left E (by omega : e ≤ 1)
      omega
    have he4 : e ≤ 4 := by
      by_contra hc
      push Not at hc
      have hE5 : E * 5 ≤ E * e := Nat.mul_le_mul_left E (by omega : 5 ≤ e)
      omega
    have hq' : qdig7 m y = ((e : ℕ) : ZMod 7) := by
      rw [← ZMod.natCast_zmod_val (qdig7 m y)]
      rw [hqval]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    interval_cases e <;> rw [hq'] <;> decide
  · simp only [Finset.mem_insert, Finset.mem_singleton]
    have hf0 : 0 < f := Nat.pos_of_ne_zero hf_ne
    rintro (h2 | h3 | h4)
    · have he : e = 2 := by
        have hv := congrArg ZMod.val h2
        rwa [hqval] at hv
      rw [he] at hr_eq
      omega
    · have he : e = 3 := by
        have hv := congrArg ZMod.val h3
        rwa [hqval] at hv
      rw [he] at hr_eq
      omega
    · have he : e = 4 := by
        have hv := congrArg ZMod.val h4
        rwa [hqval] at hv
      rw [he] at hr_eq
      omega

/-- `|x|_N ≥ 2·7^m` forces `q(x) ∈ {2,3,4}` (`ν(x) < m`). -/
theorem qdig_ge_of_absModN_ge {m y : ℕ} (hval : padicValNat 7 y < m)
    (hy : y ≠ 0) (h : 2 * 7 ^ m ≤ absModN y (7 ^ (m + 1))) :
    qdig7 m y ∈ ({2, 3, 4} : Finset (ZMod 7)) :=
  (absModN_ge_two_iff_qdig7 hval hy).mp h

/-- `|x|_N ≤ 2·7^m` forces `q(x) ∈ {0,1,5,6}` (`ν(x) < m`; boundaries
`2·7^m`, `5·7^m` excluded by `f ≠ 0`). -/
theorem qdig7_mem0156_of_absModN_le {m y : ℕ} (hval : padicValNat 7 y < m)
    (hy : y ≠ 0) (h : absModN y (7 ^ (m + 1)) ≤ 2 * 7 ^ m) :
    qdig7 m y ∈ ({0, 1, 5, 6} : Finset (ZMod 7)) := by
  unfold absModN at h
  set E := 7 ^ m with hE
  set r := y % 7 ^ (m + 1) with hr
  set e := r / E with he
  set f := r % E with hf
  have hEpos : 0 < E := Nat.pow_pos (by norm_num)
  have hN : 7 ^ (m + 1) = 7 * E := pow_succ' 7 m
  have hrN : r < 7 ^ (m + 1) := Nat.mod_lt _ (Nat.pow_pos (by norm_num))
  have hrN2 : r < 7 * E := by rw [← hN]; exact hrN
  have hr_eq : r = E * e + f := (Nat.div_add_mod r E).symm
  have hf_lt : f < E := Nat.mod_lt _ hEpos
  have he_lt : e < 7 := (Nat.div_lt_iff_lt_mul hEpos).mpr hrN2
  have hfy : f = y % E :=
    Nat.mod_mod_of_dvd y (by rw [hE]; exact Nat.pow_dvd_pow 7 (by omega))
  have hndvd : ¬ 7 ^ m ∣ y := by
    intro hd
    have : m ≤ padicValNat 7 y :=
      (Nat.pow_dvd_iff_le_padicValNat (by norm_num) hy).mp hd
    omega
  have hf_ne : f ≠ 0 := by
    rw [hfy, hE, Ne, ← Nat.dvd_iff_mod_eq_zero]
    exact hndvd
  have hf0 : 0 < f := Nat.pos_of_ne_zero hf_ne
  have hqval : (qdig7 m y).val = e := by
    unfold qdig7
    rw [ZMod.val_natCast]
    exact Nat.mod_eq_of_lt he_lt
  -- `min(r, N−r) ≤ 2E` gives `r ≤ 2E` or `N−r ≤ 2E`.
  have hcases : e ≤ 1 ∨ 5 ≤ e := by
    by_cases hle : r ≤ 7 ^ (m + 1) - r
    · left
      have hmin : min r (7 ^ (m + 1) - r) = r := Nat.min_eq_left hle
      rw [hmin] at h
      -- `r ≤ 2E`, `f > 0` → `e ≤ 1` (else `r ≥ 2E + f > 2E`)
      by_contra hc
      push Not at hc
      have hE2 : E * 2 ≤ E * e := Nat.mul_le_mul_left E (by omega : 2 ≤ e)
      omega
    · right
      push Not at hle
      have hmin : min r (7 ^ (m + 1) - r) = 7 ^ (m + 1) - r :=
        Nat.min_eq_right hle.le
      rw [hmin] at h
      -- `N − r ≤ 2E`, `f > 0` → `r > 5E` → `e ≥ 5`
      by_contra hc
      push Not at hc
      have hE4 : E * e ≤ E * 4 := Nat.mul_le_mul_left E (by omega : e ≤ 4)
      omega
  have hq' : qdig7 m y = ((e : ℕ) : ZMod 7) := by
    rw [← ZMod.natCast_zmod_val (qdig7 m y)]
    rw [hqval]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  rcases hcases with he1 | he5 <;> interval_cases e <;> rw [hq'] <;> decide

/-- `|2x|_N ≤ 2N/7` when `|x|_N ≥ 5N/14` (§6.5(i); `5N ≤ 14|x|` is the
integral form of `|x| ≥ 5N/14`). -/
theorem absModN_two_mul_le {m x : ℕ}
    (h : 5 * 7 ^ (m + 1) ≤ 14 * absModN x (7 ^ (m + 1))) :
    absModN (2 * x) (7 ^ (m + 1)) ≤ 2 * 7 ^ m := by
  unfold absModN at h ⊢
  set N := 7 ^ (m + 1) with hN
  set E := 7 ^ m with hE
  have hNe : N = 7 * E := by rw [hN, hE]; exact pow_succ' 7 m
  set r := x % N with hr
  have hrN : r < N := Nat.mod_lt _ (by rw [hN]; exact Nat.pow_pos (by norm_num))
  have hN7 : 7 ≤ N := by
    rw [hN, show (7 : ℕ) = 7 ^ 1 from (pow_one 7).symm]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hmod : (2 * x) % N = (2 * r) % N := by
    rw [mul_comm 2 x, mul_comm 2 r, hr, Nat.mul_mod,
      Nat.mod_eq_of_lt (by omega : 2 < N)]
  rw [hmod]
  rcases le_total r (N - r) with hle | hge
  · -- `|x| = r`, `r ≥ 5N/14`, `2r ≤ N`
    have hmin : min r (N - r) = r := Nat.min_eq_left hle
    rw [hmin] at h
    have h2N : 2 * r ≤ N := by omega
    rcases lt_or_eq_of_le h2N with hlt | heq
    · rw [Nat.mod_eq_of_lt hlt]
      omega
    · rw [heq, Nat.mod_self]
      omega
  · -- `|x| = N − r`, `N − r ≥ 5N/14`, `N < 2r < 2N`
    have hmin : min r (N - r) = N - r := Nat.min_eq_right hge
    rw [hmin] at h
    have h2r : (2 * r) % N = 2 * r - N := by
      rw [Nat.mod_eq_sub_mod (by omega : N ≤ 2 * r)]
      exact Nat.mod_eq_of_lt (by omega)
    rw [h2r]
    omega

/-- `|3x|_N ≤ N/7` when `|x|_N ∈ [2N/7, 5N/14]` (§6.5(i)). -/
theorem absModN_three_mul_le {m x : ℕ}
    (hlo : 2 * 7 ^ m ≤ absModN x (7 ^ (m + 1)))
    (hhi : 14 * absModN x (7 ^ (m + 1)) ≤ 5 * 7 ^ (m + 1)) :
    absModN (3 * x) (7 ^ (m + 1)) ≤ 7 ^ m := by
  unfold absModN at hlo hhi ⊢
  set N := 7 ^ (m + 1) with hN
  set E := 7 ^ m with hE
  have hNe : N = 7 * E := by rw [hN, hE]; exact pow_succ' 7 m
  set r := x % N with hr
  have hrN : r < N := Nat.mod_lt _ (by rw [hN]; exact Nat.pow_pos (by norm_num))
  have hN7 : 7 ≤ N := by
    rw [hN, show (7 : ℕ) = 7 ^ 1 from (pow_one 7).symm]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hmod : (3 * x) % N = (3 * r) % N := by
    rw [mul_comm 3 x, mul_comm 3 r, hr, Nat.mul_mod,
      Nat.mod_eq_of_lt (by omega : 3 < N)]
  rw [hmod]
  rcases le_total r (N - r) with hle | hge
  · -- `|x| = r ∈ [2N/7, 5N/14]`, `3r ∈ [6N/7, 15N/14]`
    have hmin : min r (N - r) = r := Nat.min_eq_left hle
    rw [hmin] at hlo hhi
    by_cases h3r : 3 * r < N
    · have hm : (3 * r) % N = 3 * r := Nat.mod_eq_of_lt h3r
      rw [hm]
      omega
    · have hm : (3 * r) % N = 3 * r - N := by
        rw [Nat.mod_eq_sub_mod (by omega : N ≤ 3 * r)]
        exact Nat.mod_eq_of_lt (by omega)
      rw [hm]
      omega
  · -- `|x| = N − r ∈ [2N/7, 5N/14]`, `3r ∈ [27N/14, 15N/7]`
    have hmin : min r (N - r) = N - r := Nat.min_eq_right hge
    rw [hmin] at hlo hhi
    by_cases h3r : 3 * r < 2 * N
    · have hm : (3 * r) % N = 3 * r - N := by
        rw [Nat.mod_eq_sub_mod (by omega : N ≤ 3 * r)]
        exact Nat.mod_eq_of_lt (by omega)
      rw [hm]
      omega
    · have hm : (3 * r) % N = 3 * r - 2 * N := by
        rw [Nat.mod_eq_sub_mod (by omega : N ≤ 3 * r),
          Nat.mod_eq_sub_mod (by omega : N ≤ 3 * r - N)]
        have : 3 * r - N - N = 3 * r - 2 * N := by omega
        rw [this]
        exact Nat.mod_eq_of_lt (by omega)
      rw [hm]
      omega

/-- **Remark 8 (i) bridge** (`remark8_i_int`): if every difference residue of
a same-class set `B ⊆ ℕ` has `q ∈ {0,6}`, then the pairwise digit
differences of `q(B)` lie in `{0,±1}` — the hypothesis of `remark8_i`. -/
theorem remark8_i_int {m : ℕ} {B : Finset ℕ}
    (hsame : ∀ x ∈ B, ∀ y ∈ B, residueRelOf x y = residueRel.same)
    (hB : ∀ x ∈ B, ∀ y ∈ B,
      qdig7 m (eMod7 m x y) ∈ ({0, 6} : Finset (ZMod 7))) :
    ∀ a ∈ B.image (qdig7 m), ∀ b ∈ B.image (qdig7 m),
      a - b ∈ ({0, 1, 6} : Finset (ZMod 7)) := by
  intro a ha b hb
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hb
  have hsame' := hsame x hx y hy
  have hsub := qdig_eMod_sub (m := m) hsame'
  have hq := hB x hx y hy
  -- `q(e) ∈ {0,6}` and `q(e) − (qx−qy) ∈ {0,6}` → `qx−qy ∈ {0,6}−{0,6} = {0,1,6}`
  simp only [Finset.mem_insert, Finset.mem_singleton] at hq hsub ⊢
  rcases hq with hq | hq <;> rcases hsub with hsub | hsub <;>
    rw [hq] at hsub <;>
    first
      | (have e : qdig7 m x - qdig7 m y = qdig7 m (eMod7 m x y) -
            (qdig7 m (eMod7 m x y) - (qdig7 m x - qdig7 m y)) := by ring
         rw [e, hq, hsub]
         decide)

/-! ### §5.2 Finite `ZMod 7` lemmas (`private …_dec := by decide` + wrappers) -/

/-- §6.1: `{0,6,a,b}` has `apLen ≤ 5` unless `{a,b} = {2,4}` (the unique
failing pair, `apLen = 6`). -/
private theorem apLen_pair06_le_dec :
    ∀ a b : ZMod 7,
      ¬(a = 2 ∧ b = 4) ∧ ¬(a = 4 ∧ b = 2) →
        apLen ({0, 6, a, b} : Finset (ZMod 7)) ≤ 5 := by
  decide

theorem apLen_pair06_le {a b : ZMod 7}
    (h : ¬(a = 2 ∧ b = 4) ∧ ¬(a = 4 ∧ b = 2)) :
    apLen ({0, 6, a, b} : Finset (ZMod 7)) ≤ 5 := apLen_pair06_le_dec a b h

/-- §6.2: `{0,6,q}` fits in a `4`-interval iff `q ≠ 3`. -/
private theorem apLen_triple_le_dec :
    ∀ q : ZMod 7, q ≠ 3 → apLen ({0, 6, q} : Finset (ZMod 7)) ≤ 4 := by
  decide

theorem apLen_triple_le {q : ZMod 7} (hq : q ≠ 3) :
    apLen ({0, 6, q} : Finset (ZMod 7)) ≤ 4 := apLen_triple_le_dec q hq

set_option synthInstance.maxSize 16384 in
set_option maxRecDepth 524288 in
/-- §6.1 case B: every `4`-subset of the units dilates into a `5`-interval. -/
private theorem apLen_four_dilate_dec :
    ∀ E : Finset (ZMod 7), E.card = 4 → 0 ∉ E →
      ∃ c : ZMod 7, c ≠ 0 ∧ apLen (E.image (· * c)) ≤ 5 := by
  decide

theorem apLen_four_dilate {E : Finset (ZMod 7)} (hE : E.card = 4)
    (h0 : 0 ∉ E) :
    ∃ c : ZMod 7, c ≠ 0 ∧ apLen (E.image (· * c)) ≤ 5 :=
  apLen_four_dilate_dec E hE h0

/-- §6.1 case-A `×3` dichotomy, borrow fact: a `0`/`6` pair satisfying
the difference constraint `q(b₀−b₆) = 0−6−(f₀<f₆ ? 1:0) ∈ {0,6}` forces
`f₀ < f₆` (the `f`-order coupling of spec §4.1). -/
private theorem case61_flt_dec :
    ∀ f₀ f₆ : ZMod 7,
      (0 : ZMod 7) - 6 - (if f₀.val < f₆.val then 1 else 0)
        ∈ ({0, 6} : Finset (ZMod 7)) →
      f₀.val < f₆.val := by
  decide

/-- §6.1 `×3` dichotomy, first alternative: a `{0,6}`-digit whose `6`-case
has `f ≥ 3` scales into `{0,1,2,5,6}` (`0 ↦ ⌊3f/7⌋ ∈ {0,1,2}`,
`6 ↦ 4+⌊3f/7⌋ ∈ {5,6}`). -/
private theorem case61_mem_t1_dec :
    ∀ q f : ZMod 7, q ∈ ({0, 6} : Finset (ZMod 7)) →
      (q = 6 → 3 ≤ f.val) →
      3 * q + ((3 * f.val / 7 : ℕ) : ZMod 7)
        ∈ ({0, 1, 2, 5, 6} : Finset (ZMod 7)) := by
  decide

/-- §6.1 `×3` dichotomy, second alternative: with a `6`-digit witness
`f₆ ≤ 2`, every coupled `0`-digit has `f < f₆ ≤ 2` (carry `0`), so all
scaled digits lie in `{0,1,4,5,6}`. -/
private theorem case61_mem_t2_dec :
    ∀ q f f₆ : ZMod 7, q ∈ ({0, 6} : Finset (ZMod 7)) →
      f₆.val < 3 → (q = 0 → f.val < f₆.val) →
      3 * q + ((3 * f.val / 7 : ℕ) : ZMod 7)
        ∈ ({0, 1, 4, 5, 6} : Finset (ZMod 7)) := by
  decide

/-- §6.1 case-A `×3` dichotomy at the digit level (`N = 49` model, spec
§4.1 note).  For three `B`-digits `qᵢ ∈ {0,6}` with sub-digits `fᵢ`
satisfying the pairwise difference constraint
`q(bᵢ−bⱼ) = qᵢ − qⱼ − (fᵢ < fⱼ ? 1 : 0) ∈ {0,6}`, the `×3`-scaled digits
`3·qᵢ + ⌊3fᵢ/7⌋` either all lie in `{0,1,2,5,6}` or all in
`{0,1,4,5,6}` — i.e. `q(3·A1)` avoids `{3,4}` resp. `{2,3}` (the
`{q₄,q₅} = {2,4}` digits contribute only `{0,1,5,6} ⊆` both targets, so
`apLen ≤ 5` follows).  Constraint content: a `0`/`6` pair forces
`f₀ < f₆` (`case61_flt_dec`), so a `6`-digit with `f ≤ 2` forces all
`0`-digits `f ≤ 1` (carry `0`, second alternative) while `f₆ ≥ 3`
everywhere gives the first. -/
theorem case61_dichot {q₁ q₂ q₃ f₁ f₂ f₃ : ZMod 7}
    (hq₁ : q₁ ∈ ({0, 6} : Finset (ZMod 7)))
    (hq₂ : q₂ ∈ ({0, 6} : Finset (ZMod 7)))
    (hq₃ : q₃ ∈ ({0, 6} : Finset (ZMod 7)))
    (h₁₂ : q₁ - q₂ - (if f₁.val < f₂.val then (1 : ZMod 7) else 0)
      ∈ ({0, 6} : Finset (ZMod 7)))
    (h₁₃ : q₁ - q₃ - (if f₁.val < f₃.val then (1 : ZMod 7) else 0)
      ∈ ({0, 6} : Finset (ZMod 7)))
    (h₂₁ : q₂ - q₁ - (if f₂.val < f₁.val then (1 : ZMod 7) else 0)
      ∈ ({0, 6} : Finset (ZMod 7)))
    (h₂₃ : q₂ - q₃ - (if f₂.val < f₃.val then (1 : ZMod 7) else 0)
      ∈ ({0, 6} : Finset (ZMod 7)))
    (h₃₁ : q₃ - q₁ - (if f₃.val < f₁.val then (1 : ZMod 7) else 0)
      ∈ ({0, 6} : Finset (ZMod 7)))
    (h₃₂ : q₃ - q₂ - (if f₃.val < f₂.val then (1 : ZMod 7) else 0)
      ∈ ({0, 6} : Finset (ZMod 7))) :
    ({3 * q₁ + ((3 * f₁.val / 7 : ℕ) : ZMod 7),
      3 * q₂ + ((3 * f₂.val / 7 : ℕ) : ZMod 7),
      3 * q₃ + ((3 * f₃.val / 7 : ℕ) : ZMod 7)} : Finset (ZMod 7))
      ⊆ ({0, 1, 2, 5, 6} : Finset (ZMod 7)) ∨
    ({3 * q₁ + ((3 * f₁.val / 7 : ℕ) : ZMod 7),
      3 * q₂ + ((3 * f₂.val / 7 : ℕ) : ZMod 7),
      3 * q₃ + ((3 * f₃.val / 7 : ℕ) : ZMod 7)} : Finset (ZMod 7))
      ⊆ ({0, 1, 4, 5, 6} : Finset (ZMod 7)) := by
  have key : ∀ qi qj fi fj : ZMod 7,
      qi - qj - (if fi.val < fj.val then (1 : ZMod 7) else 0)
        ∈ ({0, 6} : Finset (ZMod 7)) →
      qi = 0 → qj = 6 → fi.val < fj.val := by
    intro qi qj fi fj h hqi hqj
    rw [hqi, hqj] at h
    exact case61_flt_dec fi fj h
  by_cases h1 : q₁ = 6 → 3 ≤ f₁.val
  · by_cases h2 : q₂ = 6 → 3 ≤ f₂.val
    · by_cases h3 : q₃ = 6 → 3 ≤ f₃.val
      · left
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl
        · exact case61_mem_t1_dec q₁ f₁ hq₁ h1
        · exact case61_mem_t1_dec q₂ f₂ hq₂ h2
        · exact case61_mem_t1_dec q₃ f₃ hq₃ h3
      · obtain ⟨h3, hf3⟩ := not_imp.mp h3
        have hf3 : f₃.val < 3 := not_le.mp hf3
        right
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl
        · exact case61_mem_t2_dec q₁ f₁ f₃ hq₁ hf3
            (fun h0 => key q₁ q₃ f₁ f₃ h₁₃ h0 h3)
        · exact case61_mem_t2_dec q₂ f₂ f₃ hq₂ hf3
            (fun h0 => key q₂ q₃ f₂ f₃ h₂₃ h0 h3)
        · exact case61_mem_t2_dec q₃ f₃ f₃ hq₃ hf3
            (fun h0 => absurd (h0.symm.trans h3) (by decide))
    · obtain ⟨h2, hf2⟩ := not_imp.mp h2
      have hf2 : f₂.val < 3 := not_le.mp hf2
      right
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact case61_mem_t2_dec q₁ f₁ f₂ hq₁ hf2
          (fun h0 => key q₁ q₂ f₁ f₂ h₁₂ h0 h2)
      · exact case61_mem_t2_dec q₂ f₂ f₂ hq₂ hf2
          (fun h0 => absurd (h0.symm.trans h2) (by decide))
      · exact case61_mem_t2_dec q₃ f₃ f₂ hq₃ hf2
          (fun h0 => key q₃ q₂ f₃ f₂ h₃₂ h0 h2)
  · obtain ⟨h1, hf1⟩ := not_imp.mp h1
    have hf1 : f₁.val < 3 := not_le.mp hf1
    right
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact case61_mem_t2_dec q₁ f₁ f₁ hq₁ hf1
        (fun h0 => absurd (h0.symm.trans h1) (by decide))
    · exact case61_mem_t2_dec q₂ f₂ f₁ hq₂ hf1
        (fun h0 => key q₂ q₁ f₂ f₁ h₂₁ h0 h1)
    · exact case61_mem_t2_dec q₃ f₃ f₁ hq₃ hf1
        (fun h0 => key q₃ q₁ f₃ f₁ h₃₁ h0 h1)

set_option synthInstance.maxSize 16384 in
set_option maxRecDepth 524288 in
/-- Lemma 7(i)'s translate: some `x` misses `X + {0,1,2}` when `apLen X ≤ 4`
(`X ⊆ cycIv i 4` ⇒ `X + {0,1,2} ⊆ cycIv i 6` ⇒ `i−1` avoids). -/
private theorem exists_not_mem_three_dec :
    ∀ X : Finset (ZMod 7), apLen X ≤ 4 →
      ∃ x : ZMod 7, ∀ u ∈ ({0, 1, 2} : Finset (ZMod 7)), x - u ∉ X := by
  decide

theorem exists_not_mem_three {X : Finset (ZMod 7)} (hX : apLen X ≤ 4) :
    ∃ x : ZMod 7, ∀ u ∈ ({0, 1, 2} : Finset (ZMod 7)), x - u ∉ X :=
  exists_not_mem_three_dec X hX

/-- §6.3 (ii.2) `h = m`: the `8` bad `(ẽ34, ẽ45)` pairs. -/
def bad63 : Finset (ZMod 7 × ZMod 7) :=
  {(2, 4), (2, 5), (3, 2), (3, 3), (4, 3), (4, 4), (5, 1), (5, 2)}

/-- §6.3 (ii.2) `h = m`: with `q(A₁) = {1,2,4}` anchored, `q(d₄) = i`,
`q(d₅) = j`, every `Λ₀`-shift fails iff `(ẽ34,ẽ45) = (2−i, 2i−j)` is one of
the `8` bad pairs. -/
private theorem case63_bad_pairs_dec :
    ∀ i j : ZMod 7,
      (∀ t : ZMod 7,
        ¬ avoids06 ({1 + t, 2 + t, 4 + t, i + 2 * t, j + 4 * t}
          : Finset (ZMod 7))) →
      (2 - i, 2 * i - j) ∈ bad63 := by
  decide

theorem case63_bad_pairs {i j : ZMod 7}
    (h : ∀ t : ZMod 7,
      ¬ avoids06 ({1 + t, 2 + t, 4 + t, i + 2 * t, j + 4 * t}
        : Finset (ZMod 7))) :
    (2 - i, 2 * i - j) ∈ bad63 := case63_bad_pairs_dec i j h

/-- §6.3 ε-shift coverage: one of the four `(p−ε₁, q−ε₂)`, `εᵢ ∈ {0,1}`,
avoids all bad pairs. -/
private theorem case63_eps_avoid_dec :
    ∀ p q : ZMod 7,
      ∃ ε₁ ε₂ : ZMod 7, ε₁ ∈ ({0, 1} : Finset (ZMod 7)) ∧
        ε₂ ∈ ({0, 1} : Finset (ZMod 7)) ∧ (p - ε₁, q - ε₂) ∉ bad63 := by
  decide

theorem case63_eps_avoid (p q : ZMod 7) :
    ∃ ε₁ ε₂ : ZMod 7, ε₁ ∈ ({0, 1} : Finset (ZMod 7)) ∧
      ε₂ ∈ ({0, 1} : Finset (ZMod 7)) ∧ (p - ε₁, q - ε₂) ∉ bad63 :=
  case63_eps_avoid_dec p q

/-- §6.6(a): the `5` bad `(ẽ(d2,d4), ẽ(d2,d5))` pairs — equation (16),
under the corrected model `q(d3) = q(d4)+1`. -/
def bad66a : Finset (ZMod 7 × ZMod 7) := {(4, 2), (4, 4), (5, 4), (6, 4), (6, 6)}

/-- §6.6(a): `λ_k`, `k ∈ {1,2,3}` sends `q(A₁) ↦ {k,k+2}`,
`q(A₂) ↦ {2k−x, 2k−x+1}`, `q(d₅) ↦ 4y+4k`; all three fail iff `(x,y)` is a
bad pair. -/
private theorem case66a_bad_dec :
    ∀ x y : ZMod 7,
      (∀ k ∈ ({1, 2, 3} : Finset (ZMod 7)),
        ¬ avoids06 ({k, k + 2, 2 * k - x, 2 * k - x + 1, 4 * y + 4 * k}
          : Finset (ZMod 7))) →
      (x, y) ∈ bad66a := by
  decide

theorem case66a_bad {x y : ZMod 7}
    (h : ∀ k ∈ ({1, 2, 3} : Finset (ZMod 7)),
      ¬ avoids06 ({k, k + 2, 2 * k - x, 2 * k - x + 1, 4 * y + 4 * k}
        : Finset (ZMod 7))) :
    (x, y) ∈ bad66a := case66a_bad_dec x y h

/-- §6.6(a) ε-shift coverage. -/
private theorem case66a_eps_dec :
    ∀ p q : ZMod 7,
      ∃ ε₁ ε₂ : ZMod 7, ε₁ ∈ ({0, 1} : Finset (ZMod 7)) ∧
        ε₂ ∈ ({0, 1} : Finset (ZMod 7)) ∧ (p - ε₁, q - ε₂) ∉ bad66a := by
  decide

theorem case66a_eps (p q : ZMod 7) :
    ∃ ε₁ ε₂ : ZMod 7, ε₁ ∈ ({0, 1} : Finset (ZMod 7)) ∧
      ε₂ ∈ ({0, 1} : Finset (ZMod 7)) ∧ (p - ε₁, q - ε₂) ∉ bad66a :=
  case66a_eps_dec p q

/-- §6.6(b): the exact minimal avoid-set `{2,4}` for `a = ẽ(d2,d4)` —
every `b` admits a good `k ∈ {1,2,3}`. -/
private theorem case66b_good_dec :
    ∀ a b : ZMod 7, a ∉ ({2, 4} : Finset (ZMod 7)) →
      ∃ k ∈ ({1, 2, 3} : Finset (ZMod 7)),
        avoids06 ({k, k + 2, 4 * a + 4 * k, 4 * a + 4 * k + 1, 2 * k - b}
          : Finset (ZMod 7)) := by
  decide

theorem case66b_good {a b : ZMod 7} (ha : a ∉ ({2, 4} : Finset (ZMod 7))) :
    ∃ k ∈ ({1, 2, 3} : Finset (ZMod 7)),
      avoids06 ({k, k + 2, 4 * a + 4 * k, 4 * a + 4 * k + 1, 2 * k - b}
        : Finset (ZMod 7)) := case66b_good_dec a b ha

/-- §6.5 (ii.1)(b): with `q(A₁) = {1,2,3}` and `q(A₄) = {i, i+4}`, all
`Λ₀`-shifts fail iff `i ∈ {2,6}` (⇔ `ẽ(d3,d4) = 2q(d4)−1 ∈ {4,5}`). -/
private theorem case65b_bad_i_dec :
    ∀ i : ZMod 7,
      (∀ t : ZMod 7,
        ¬ avoids06 ({1 + t, 2 + t, 3 + t, i + 4 * t, i + 4 + 4 * t}
          : Finset (ZMod 7))) →
      i ∈ ({2, 6} : Finset (ZMod 7)) := by
  decide

theorem case65b_bad_i {i : ZMod 7}
    (h : ∀ t : ZMod 7,
      ¬ avoids06 ({1 + t, 2 + t, 3 + t, i + 4 * t, i + 4 + 4 * t}
        : Finset (ZMod 7))) :
    i ∈ ({2, 6} : Finset (ZMod 7)) := case65b_bad_i_dec i h

set_option synthInstance.maxSize 16384 in
set_option maxRecDepth 524288 in
/-- §6.3 (ii.2.b) ũ-table. For each `(ẽ, ũ) ≠ (0,3)` and each borrow
`δ = q(e13)−q(e23)−q(e12) ∈ {0,1}` there is a `q(e45)` such that the
borrow-coupled digit set `{0, q13+b13, q23+b23}` (with
`q13 = q45+ẽ`, `q23 = 3(ũ−3q13)`, `b13 = b12+b23−δ`) either has
`apLen ≤ 2`, or `apLen ≤ 3` while `q45 ∈ {0,6}` (so `ẽ(d4,d5)` avoids
`{2,4}`). Row data (spec §5.2):
`ẽ=0: q45 = [0,6,0,3,6,0,6]`; `ẽ=1: q45 = [6,0,6,0,(5|6),6,5]`. -/
private theorem case63_table_dec :
    ∀ e u : ZMod 7, e ∈ ({0, 1} : Finset (ZMod 7)) → ¬(e = 0 ∧ u = 3) →
      ∀ δ ∈ ({0, 1} : Finset (ZMod 7)), ∃ q45 : ZMod 7,
        ∀ b12 ∈ ({0, 1} : Finset (ZMod 7)),
        ∀ b13 ∈ ({0, 1} : Finset (ZMod 7)),
        ∀ b23 ∈ ({0, 1} : Finset (ZMod 7)),
        b13 = b12 + b23 - δ →
        apLen ({0, q45 + e + b13, 3 * (u - 3 * (q45 + e)) + b23}
            : Finset (ZMod 7)) ≤ 2 ∨
        (apLen ({0, q45 + e + b13, 3 * (u - 3 * (q45 + e)) + b23}
            : Finset (ZMod 7)) ≤ 3 ∧
          q45 ∈ ({0, 6} : Finset (ZMod 7))) := by
  decide

theorem case63_table {e u : ZMod 7} (he : e ∈ ({0, 1} : Finset (ZMod 7)))
    (hne : ¬ (e = 0 ∧ u = 3)) {δ : ZMod 7}
    (hδ : δ ∈ ({0, 1} : Finset (ZMod 7))) :
    ∃ q45 : ZMod 7,
      ∀ b12 ∈ ({0, 1} : Finset (ZMod 7)),
      ∀ b13 ∈ ({0, 1} : Finset (ZMod 7)),
      ∀ b23 ∈ ({0, 1} : Finset (ZMod 7)),
      b13 = b12 + b23 - δ →
      apLen ({0, q45 + e + b13, 3 * (u - 3 * (q45 + e)) + b23}
          : Finset (ZMod 7)) ≤ 2 ∨
      (apLen ({0, q45 + e + b13, 3 * (u - 3 * (q45 + e)) + b23}
          : Finset (ZMod 7)) ≤ 3 ∧
        q45 ∈ ({0, 6} : Finset (ZMod 7))) :=
  case63_table_dec e u he hne δ hδ

/-- §6.3 (ii.2.b) `(ẽ,ũ) = (0,3)` cell ×2-rescue: with `q45 = 3` the doubled
difference-digits satisfy `2·q45 + c ∈ {0,6}` (c ∈ {0,1}) for `e45,e13,e23`,
`2·q12 + c ∈ {0,1,5,6}` for `e12`, the doubled digit-set has `apLen ≤ 2`,
and `6 + {0,1,6}` (the `ẽ(2d4,2d5)` range) avoids `{2,4}`. -/
private theorem case63_table_rescue_dec :
    (∀ c ∈ ({0, 1} : Finset (ZMod 7)), (2 : ZMod 7) * 3 + c ∈ ({0, 6} : Finset _)) ∧
    (∀ q12 ∈ ({0, 6} : Finset (ZMod 7)), ∀ c ∈ ({0, 1} : Finset (ZMod 7)),
      (2 : ZMod 7) * q12 + c ∈ ({0, 1, 5, 6} : Finset _)) ∧
    (∀ a ∈ ({0, 6} : Finset (ZMod 7)), ∀ b ∈ ({0, 6} : Finset (ZMod 7)),
      apLen ({0, a, b} : Finset (ZMod 7)) ≤ 2) ∧
    (∀ c ∈ ({0, 1, 6} : Finset (ZMod 7)), (6 : ZMod 7) + c ∉ ({2, 4} : Finset _)) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

theorem case63_table_rescue :
    (∀ c ∈ ({0, 1} : Finset (ZMod 7)), (2 : ZMod 7) * 3 + c ∈ ({0, 6} : Finset _)) ∧
    (∀ q12 ∈ ({0, 6} : Finset (ZMod 7)), ∀ c ∈ ({0, 1} : Finset (ZMod 7)),
      (2 : ZMod 7) * q12 + c ∈ ({0, 1, 5, 6} : Finset _)) ∧
    (∀ a ∈ ({0, 6} : Finset (ZMod 7)), ∀ b ∈ ({0, 6} : Finset (ZMod 7)),
      apLen ({0, a, b} : Finset (ZMod 7)) ≤ 2) ∧
    (∀ c ∈ ({0, 1, 6} : Finset (ZMod 7)), (6 : ZMod 7) + c ∉ ({2, 4} : Finset _)) :=
  case63_table_rescue_dec

#print axioms exists_lambda0_of_shift
#print axioms qdig_eMod_sub_etd7_two
#print axioms filtered7_mod7
#print axioms case63_table
#print axioms case66b_good
#print axioms case61_dichot
