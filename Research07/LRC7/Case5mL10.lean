/-
Copyright (c) 2026 Research07 contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Research07 contributors
-/
import Research07.LRC7.Case5mCases

/-!
# Case lemmas for the `|A| = 5, m ≥ 2` analysis — Lemma 9(ii), 10, 11

This file is the "B2" layer of the §6 formalization (see
`_reports/lrc7-sec6-spec.md` §8): paper Lemma 9(ii) (same-level differences
with `r(y) = j·r(x)`, `j ∈ {2,3}`) and the numbering Lemmas 10/11.

Contents:

* Difference-residue helpers: `eMod7_congr`, `eMod7_smul` (unit scalar
  rescaling), `qdig7_sub_resid` (exact borrow formula for wrapped
  subtraction), `qdig_smul_eMod_eq` (the `eval` engine).
* `pow_dvd_eMod7_two` — for a `twoX` pair `(x,y)` at level `h`,
  `7^{h+1} ∣ e(x,y)`.
* `remark8_ii'` — the `{0,±1,±2}`-difference variant of Remark 8(ii)
  (`{0,1,2,5,6}`; the existing `remark8_ii` collapses to `{0,±1}` under
  the `∀`-pair quantification).
* `elevel7` — the *effective level* of a difference residue: `m+1` when
  `eMod7 = 0` (the true difference has `ν ≥ m+1`; the residue reads `0`).
* `lemma9_ii`, `lemma10`, `lemma11`.

NOTE on `lemma11`: the spec's `enu7 = padicValNat` statement is FALSE for
elements congruent mod `7^{m+1}` (`padicValNat 7 0 = 0` inverts the
ordering); the theorem is stated with `elevel7` — see
`_reports/lrc7-sec6-l91011.md` for the countermodel, mirroring the
`lemma9_i` `hνm` deviation precedent.
-/

section LRC7L10

/-! ### §0.1 Private clones of digit helpers (`Differences`/`Case5mL9`) -/

/-- `(a·7^m + b) / 7^m = a` when `b < 7^m`. -/
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

/-- `ZMod`-cast of `eMod7`: the wrapped residue casts to the
branch expression (local copy; `private` in `Case5mBase`/`Case5mCases`). -/
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

/-- Equal `runit7` forces the `same` branch (nonzero second element). -/
private theorem rel_same {u v : ℕ} (h : runit7 u = runit7 v) (hv : v ≠ 0) :
    residueRelOf u v = residueRel.same := by
  have hv0 : runit7 v ≠ 0 := runit7_ne_zero (Nat.pos_of_ne_zero hv)
  rw [residueRelOf_eq_same]
  refine ⟨?_, ?_⟩ <;> intro hcon <;> rw [h] at hcon <;>
    · have hz : runit7 v = 0 := by
        have e : runit7 v - 2 * runit7 v = 0 := sub_eq_zero.mpr hcon
        have e2 : runit7 v - 2 * runit7 v = - runit7 v := by ring
        rw [e2] at e
        exact neg_eq_zero.mp e
      exact hv0 hz

/-- `eMod7` casts to a plain difference in the `same` branch. -/
private theorem eMod7_zmod_cast_same {m u v : ℕ}
    (h : residueRelOf u v = residueRel.same) :
    ((eMod7 m u v : ℕ) : ZMod (7 ^ (m + 1))) = (u : ZMod _) - (v : ZMod _) := by
  obtain ⟨h1, h2⟩ := (residueRelOf_eq_same).mp h
  rw [eMod7_zmod_cast, if_neg h1, if_neg h2]

/-- `qdig7 m 0 = 0`. -/
private theorem qdig7_zero (m : ℕ) : qdig7 m 0 = 0 := by
  unfold qdig7
  simp

/-- **Exact borrow formula** for the wrapped residue difference
`(a % N + N − b % N)`: writing `a % N = q_a·7^m + f_a`,
`b % N = q_b·7^m + f_b`, the top digit is `q_a − q_b` minus the borrow
`1` iff `f_a < f_b`.  The `{0,6}`-membership corollary is the
`x−y`/`y−x` engine; the `a = 0` case is the negation engine
(`q(−b) = −q(b) − (f_b ≠ 0 ? 1 : 0)`). -/
private theorem qdig7_sub_resid {m a b : ℕ} :
    qdig7 m (a % 7 ^ (m + 1) + 7 ^ (m + 1) - b % 7 ^ (m + 1))
      = qdig7 m a - qdig7 m b
        - if a % 7 ^ m < b % 7 ^ m then (1 : ZMod 7) else 0 := by
  obtain ⟨q1, f1, hX, hq1, hf1⟩ := residue_decomp (m := m) (x := a)
  obtain ⟨q2, f2, hY, hq2, hf2⟩ := residue_decomp (m := m) (x := b)
  have hP : 0 < 7 ^ m := Nat.pow_pos (by norm_num)
  have hNe : (7 : ℕ) ^ (m + 1) = 7 * 7 ^ m := pow_succ' 7 m
  have hqA : qdig7 m a = (q1 : ZMod 7) := by
    unfold qdig7
    rw [hX, mul_pow_add_div hf1]
  have hqB : qdig7 m b = (q2 : ZMod 7) := by
    unfold qdig7
    rw [hY, mul_pow_add_div hf2]
  have hf1e : a % 7 ^ m = f1 := by
    have hmod : a % 7 ^ (m + 1) % 7 ^ m = a % 7 ^ m :=
      Nat.mod_mod_of_dvd a (Nat.pow_dvd_pow 7 (Nat.le_succ m))
    rw [← hmod, hX, add_comm (q1 * 7 ^ m) f1,
      Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hf1]
  have hf2e : b % 7 ^ m = f2 := by
    have hmod : b % 7 ^ (m + 1) % 7 ^ m = b % 7 ^ m :=
      Nat.mod_mod_of_dvd b (Nat.pow_dvd_pow 7 (Nat.le_succ m))
    rw [← hmod, hY, add_comm (q2 * 7 ^ m) f2,
      Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hf2]
  rw [qdig7_eq_cast_div]
  by_cases hb : f1 < f2
  · -- borrow: `a' + N − b' = (q1 + 6 − q2)·7^m + (f1 + 7^m − f2)`
    have hexp : (q1 + 6 - q2) * 7 ^ m = q1 * 7 ^ m + 6 * 7 ^ m - q2 * 7 ^ m := by
      rw [Nat.sub_mul, Nat.add_mul]
    have hB : q2 * 7 ^ m ≤ 6 * 7 ^ m :=
      Nat.mul_le_mul (by omega : q2 ≤ 6) (le_refl _)
    have hcalc : a % 7 ^ (m + 1) + 7 ^ (m + 1) - b % 7 ^ (m + 1)
        = (q1 + 6 - q2) * 7 ^ m + (f1 + 7 ^ m - f2) := by
      rw [hX, hY, hNe, hexp]
      omega
    rw [hcalc, mul_pow_add_div (by omega : f1 + 7 ^ m - f2 < 7 ^ m)]
    have hq : ((q1 + 6 - q2 : ℕ) : ZMod 7) = (q1 : ZMod 7) - q2 - 1 := by
      rw [natCast_sub_add (by omega : q2 ≤ q1 + 6)]
      have h6 : ((6 : ℕ) : ZMod 7) = -1 := by decide
      rw [h6]
      ring
    rw [hq, hqA, hqB]
    rw [if_pos (by rwa [hf1e, hf2e] : a % 7 ^ m < b % 7 ^ m)]
  · -- no borrow: `a' + N − b' = (q1 + 7 − q2)·7^m + (f1 − f2)`
    have hge : f2 ≤ f1 := Nat.le_of_not_gt hb
    have hexp : (q1 + 7 - q2) * 7 ^ m = q1 * 7 ^ m + 7 * 7 ^ m - q2 * 7 ^ m := by
      rw [Nat.sub_mul, Nat.add_mul]
    have hB : q2 * 7 ^ m ≤ 7 * 7 ^ m :=
      Nat.mul_le_mul (by omega : q2 ≤ 7) (le_refl _)
    have hcalc : a % 7 ^ (m + 1) + 7 ^ (m + 1) - b % 7 ^ (m + 1)
        = (q1 + 7 - q2) * 7 ^ m + (f1 - f2) := by
      rw [hX, hY, hNe, hexp]
      omega
    rw [hcalc, mul_pow_add_div (by omega : f1 - f2 < 7 ^ m)]
    have hq : ((q1 + 7 - q2 : ℕ) : ZMod 7) = (q1 : ZMod 7) - q2 := by
      rw [natCast_sub_add (by omega : q2 ≤ q1 + 7)]
      have h7 : ((7 : ℕ) : ZMod 7) = 0 := by decide
      rw [h7]
      ring
    rw [hq, hqA, hqB]
    rw [if_neg (by rwa [hf1e, hf2e] : ¬ a % 7 ^ m < b % 7 ^ m)]
    ring

/-- The `q`-digit of a scalar multiple of a difference residue whose
`ZMod N` value is the combination `A − B`: reduces to the borrow formula
`qdig7_sub_resid` via the residue congruence. -/
private theorem qdig_smul_eMod_eq {m lam e A B : ℕ}
    (hcast : ((lam * e : ℕ) : ZMod (7 ^ (m + 1))) = (A : ZMod _) - (B : ZMod _)) :
    qdig7 m (lam * e)
      = qdig7 m A - qdig7 m B
        - if A % 7 ^ m < B % 7 ^ m then (1 : ZMod 7) else 0 := by
  have hcast' : ((lam * e : ℕ) : ZMod (7 ^ (m + 1)))
      = ((A % 7 ^ (m + 1) + 7 ^ (m + 1) - B % 7 ^ (m + 1) : ℕ) : ZMod _) := by
    rw [hcast]
    have hlt : B % 7 ^ (m + 1) ≤ A % 7 ^ (m + 1) + 7 ^ (m + 1) := by
      have := Nat.mod_lt B (Nat.pow_pos (by norm_num) : 0 < 7 ^ (m + 1))
      omega
    rw [Nat.cast_sub hlt, Nat.cast_add, ZMod.natCast_mod, ZMod.natCast_mod,
      ZMod.natCast_self]
    ring
  have hwrap : (lam * e) % 7 ^ (m + 1)
      = (A % 7 ^ (m + 1) + 7 ^ (m + 1) - B % 7 ^ (m + 1)) % 7 ^ (m + 1) :=
    (ZMod.natCast_eq_natCast_iff' _ _ _).mp hcast'
  rw [qdig7_congr hwrap]
  exact qdig7_sub_resid

/-- `eMod7` of an element with itself is `0`. -/
private theorem eMod7_self (m x : ℕ) : eMod7 m x x = 0 := by
  rcases eq_or_ne x 0 with rfl | hx0
  · simp [eMod7]
  · have hr : runit7 x ≠ 0 := runit7_ne_zero (Nat.pos_of_ne_zero hx0)
    have h2 : ¬ runit7 x = 2 * runit7 x := by
      intro h
      have h' : 2 * runit7 x - runit7 x = 0 := by rw [← h, sub_self]
      rw [show 2 * runit7 x - runit7 x = runit7 x by ring] at h'
      exact hr h'
    unfold eMod7
    rw [if_neg h2, if_neg h2]
    have hlt : x % 7 ^ (m + 1) < 7 ^ (m + 1) :=
      Nat.mod_lt _ (Nat.pow_pos (by norm_num))
    have h : x % 7 ^ (m + 1) + 7 ^ (m + 1) - x % 7 ^ (m + 1) = 7 ^ (m + 1) := by
      omega
    rw [h, Nat.mod_self]

/-- `eMod7` is a residue `< 7^{m+1}`. -/
private theorem eMod7_lt (m x y : ℕ) : eMod7 m x y < 7 ^ (m + 1) := by
  unfold eMod7
  split_ifs <;> exact Nat.mod_lt _ (Nat.pow_pos (by norm_num))

/-- `e(cx, cy) ≡ c·e(x,y) (mod 7^{m+1})` whenever `runit7 c ≠ 0` (the
residue-ratio branches are preserved since multiplication by a unit
scales both `runit7`s uniformly).  `eMod7_mul` is the `runit7 c = 1`
special case. -/
private theorem eMod7_smul {m c x y : ℕ} (hc : runit7 c ≠ 0) :
    eMod7 m (c * x) (c * y) = (c * eMod7 m x y) % 7 ^ (m + 1) := by
  have hL : ((eMod7 m (c * x) (c * y) : ℕ) : ZMod (7 ^ (m + 1)))
      = (c * eMod7 m x y : ZMod (7 ^ (m + 1))) := by
    rw [eMod7_zmod_cast, eMod7_zmod_cast]
    simp only [runit7_mul]
    have sc1 : (runit7 c * runit7 y = 2 * (runit7 c * runit7 x)) ↔
        (runit7 y = 2 * runit7 x) := by
      constructor
      · intro h
        apply mul_left_cancel₀ hc
        rwa [show 2 * (runit7 c * runit7 x) = runit7 c * (2 * runit7 x) from
          by ring] at h
      · intro h; rw [h]; ring
    have sc2 : (runit7 c * runit7 x = 2 * (runit7 c * runit7 y)) ↔
        (runit7 x = 2 * runit7 y) := by
      constructor
      · intro h
        apply mul_left_cancel₀ hc
        rwa [show 2 * (runit7 c * runit7 y) = runit7 c * (2 * runit7 y) from
          by ring] at h
      · intro h; rw [h]; ring
    by_cases h1 : runit7 y = 2 * runit7 x
    · rw [if_pos h1, if_pos (sc1.mpr h1)]
      push_cast; ring
    · rw [if_neg h1, if_neg (fun hcon => h1 (sc1.mp hcon))]
      by_cases h2 : runit7 x = 2 * runit7 y
      · rw [if_pos h2, if_pos (sc2.mpr h2)]
        push_cast; ring
      · rw [if_neg h2, if_neg (fun hcon => h2 (sc2.mp hcon))]
        push_cast; ring
  have hlt : eMod7 m (c * x) (c * y) < 7 ^ (m + 1) := by
    unfold eMod7
    split_ifs <;> exact Nat.mod_lt _ (Nat.pow_pos (by norm_num))
  rw [← Nat.cast_mul] at hL
  rw [ZMod.natCast_eq_natCast_iff] at hL
  have hL' : eMod7 m (c * x) (c * y) % 7 ^ (m + 1)
      = (c * eMod7 m x y) % 7 ^ (m + 1) := hL
  rwa [Nat.mod_eq_of_lt hlt] at hL'

/-- `eMod7` respects `mod`-congruence of its arguments (with matching
`runit7`): only the residues `x % N`, `y % N` and the unit digits enter. -/
private theorem eMod7_congr {m x y x' y' : ℕ}
    (hx : x % 7 ^ (m + 1) = x' % 7 ^ (m + 1))
    (hy : y % 7 ^ (m + 1) = y' % 7 ^ (m + 1))
    (hrx : runit7 x = runit7 x') (hry : runit7 y = runit7 y') :
    eMod7 m x y = eMod7 m x' y' := by
  unfold eMod7
  rw [hx, hy, hrx, hry]

/-! ### §0.2 Level structure of residues (`ν`/`r` under `±`) -/

private instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-- **Block form**: `e ≡ r(e)·7^{ν(e)} (mod 7^{ν(e)+1})` for `e ≠ 0`. -/
private theorem nat_mod_pow_succ_of_padic {e h : ℕ} (he : e ≠ 0)
    (hν : padicValNat 7 e = h) :
    e % 7 ^ (h + 1) = (runit7 e).val * 7 ^ h := by
  set u := Nat.divMaxPow e 7 with hu
  have he_eq : e = u * 7 ^ h := by
    have hh := Nat.divMaxPow_mul_pow_padicValNat 7 e
    rw [hν] at hh
    exact hh.symm
  have hmod : e % 7 ^ (h + 1) = (u % 7) * 7 ^ h := by
    rw [he_eq, pow_succ', Nat.mul_mod_mul_right]
  have hdiv : e / 7 ^ h = u := by
    rw [he_eq]
    exact Nat.mul_div_cancel _ (Nat.pow_pos (by norm_num))
  have hr : (runit7 e).val = u % 7 := by
    unfold runit7
    rw [hν, hdiv, ZMod.val_natCast]
  rw [hmod, hr]

/-- A natural `w` congruent to `s·7^h (mod 7^{h+1})` with `0 < s < 7` has
level exactly `h` and unit digit `s`. -/
private theorem level_of_mod_block {w h s : ℕ}
    (hmod : w % 7 ^ (h + 1) = s * 7 ^ h) (hs : 0 < s) (hs7 : s < 7) :
    w ≠ 0 ∧ padicValNat 7 w = h ∧ runit7 w = (s : ZMod 7) := by
  have hP : 0 < 7 ^ h := Nat.pow_pos (by norm_num)
  have hw_eq : w = 7 ^ h * (s + 7 * (w / 7 ^ (h + 1))) := by
    conv_lhs => rw [← Nat.div_add_mod w (7 ^ (h + 1))]
    rw [hmod, pow_succ']
    ring
  have hw0 : w ≠ 0 := by
    rintro rfl
    rw [Nat.zero_mod] at hmod
    rcases Nat.mul_eq_zero.mp hmod.symm with hs0 | h70
    · omega
    · exact absurd h70 hP.ne'
  have hν : padicValNat 7 w = h := by
    have hdvd : 7 ^ h ∣ w := ⟨_, hw_eq⟩
    have hndvd : ¬ 7 ^ (h + 1) ∣ w := by
      intro hd
      rw [Nat.dvd_iff_mod_eq_zero] at hd
      rw [hmod] at hd
      rcases Nat.mul_eq_zero.mp hd with hs0 | h70
      · omega
      · exact absurd h70 hP.ne'
    have hle := (Nat.pow_dvd_iff_le_padicValNat (by norm_num) hw0).mp hdvd
    have hlt : padicValNat 7 w < h + 1 := by
      by_contra hc
      push_neg at hc
      exact hndvd ((Nat.pow_dvd_iff_le_padicValNat (by norm_num) hw0).mpr hc)
    omega
  refine ⟨hw0, hν, ?_⟩
  unfold runit7
  rw [hν]
  have hdiv : w / 7 ^ h = s + 7 * (w / 7 ^ (h + 1)) := by
    conv_lhs => rw [hw_eq]
    exact Nat.mul_div_cancel_left _ hP
  rw [hdiv, Nat.cast_add, Nat.cast_mul,
    show ((7 : ℕ) : ZMod 7) = 0 from ZMod.natCast_self 7, zero_mul, add_zero]

/-- Sum of two level-`h` naturals reads `(r(u)+r(v))·7^h` mod `7^{h+1}`. -/
private theorem add_mod_block {u v h : ℕ} (hu : u ≠ 0) (hv : v ≠ 0)
    (huν : padicValNat 7 u = h) (hvν : padicValNat 7 v = h) :
    (u + v) % 7 ^ (h + 1) = (runit7 u + runit7 v).val * 7 ^ h := by
  have hvv : (runit7 u + runit7 v).val
      = ((runit7 u).val + (runit7 v).val) % 7 := ZMod.val_add _ _
  rw [Nat.add_mod, nat_mod_pow_succ_of_padic hu huν,
    nat_mod_pow_succ_of_padic hv hvν, ← Nat.add_mul, pow_succ',
    Nat.mul_mod_mul_right, hvv]

/-- Difference of two level-`h` naturals reads `(r(u)−r(v))·7^h` mod
`7^{h+1}` (wrapped subtraction `u − v` inside the modulus). -/
private theorem sub_mod_block {u v h : ℕ} (hu : u ≠ 0) (hv : v ≠ 0)
    (huν : padicValNat 7 u = h) (hvν : padicValNat 7 v = h) :
    (u % 7 ^ (h + 1) + 7 ^ (h + 1) - v % 7 ^ (h + 1)) % 7 ^ (h + 1)
      = (runit7 u - runit7 v).val * 7 ^ h := by
  have hub := nat_mod_pow_succ_of_padic hu huν
  have hvb := nat_mod_pow_succ_of_padic hv hvν
  have hru7 : (runit7 u).val < 7 := ZMod.val_lt _
  have hrv7 : (runit7 v).val < 7 := ZMod.val_lt _
  have hvv : (runit7 u - runit7 v).val
      = ((runit7 u).val + 7 - (runit7 v).val) % 7 := by
    have hcast : (runit7 u - runit7 v : ZMod 7)
        = (((runit7 u).val + 7 - (runit7 v).val : ℕ) : ZMod 7) := by
      rw [Nat.cast_sub (by omega : (runit7 v).val ≤ (runit7 u).val + 7)]
      push_cast
      rw [show (7 : ZMod 7) = 0 from by decide, add_zero,
        ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    rw [hcast, ZMod.val_natCast]
  rw [hub, hvb]
  have hsub : (runit7 u).val * 7 ^ h + 7 ^ (h + 1) - (runit7 v).val * 7 ^ h
      = ((runit7 u).val + 7 - (runit7 v).val) * 7 ^ h := by
    rw [pow_succ', Nat.sub_mul, Nat.add_mul]
  rw [hsub, pow_succ', Nat.mul_mod_mul_right, hvv]

/-- `(a + c − b) % P` depends only on `a % P`, `b % P` when `P ∣ c`
(and the subtraction does not truncate). -/
private theorem wrap_sub_mod_gen {a b c P : ℕ} (hP : 0 < P) (hc : P ∣ c)
    (hle : b ≤ a + c) :
    (a + c - b) % P = (a % P + P - b % P) % P := by
  obtain ⟨k, rfl⟩ := hc
  have hlt1 : b ≤ a + P * k := hle
  have hlt2 : b % P ≤ a % P + P := by
    have := Nat.mod_lt b hP
    omega
  have hcast : ((a + P * k - b : ℕ) : ZMod P)
      = ((a % P + P - b % P : ℕ) : ZMod P) := by
    rw [Nat.cast_sub hlt1, Nat.cast_sub hlt2]
    push_cast
    rw [ZMod.natCast_self, ZMod.natCast_mod, ZMod.natCast_mod]
    ring
  exact (ZMod.natCast_eq_natCast_iff' _ _ _).mp hcast

/-- The negated residue `N − e` (for `0 < e < N`, `ν(e) ≤ m`) has the
same level as `e` and unit `−r(e)`. -/
private theorem neg_resid_level {m e : ℕ} (he : e ≠ 0)
    (helt : e < 7 ^ (m + 1)) (hνm : padicValNat 7 e ≤ m) :
    padicValNat 7 (7 ^ (m + 1) - e) = padicValNat 7 e ∧
    runit7 (7 ^ (m + 1) - e) = - runit7 e := by
  set h := padicValNat 7 e with hh
  have hub := nat_mod_pow_succ_of_padic he rfl
  have hu7 : (runit7 e).val < 7 := ZMod.val_lt _
  have hu0 : 0 < (runit7 e).val := by
    rcases Nat.eq_zero_or_pos (runit7 e).val with h0 | h0
    · exfalso
      rw [ZMod.val_eq_zero] at h0
      exact runit7_ne_zero (Nat.pos_of_ne_zero he) h0
    · exact h0
  have hmod : (7 ^ (m + 1) - e) % 7 ^ (h + 1)
      = (7 - (runit7 e).val) * 7 ^ h := by
    obtain ⟨K, hK⟩ := Nat.pow_dvd_pow 7 (by omega : h + 1 ≤ m + 1)
    have hK' : 7 ^ (m + 1) = K * 7 ^ (h + 1) := by rw [hK, mul_comm]
    have hdec : 7 ^ (m + 1) - e
        = (K - e / 7 ^ (h + 1) - 1) * 7 ^ (h + 1)
          + (7 ^ (h + 1) - e % 7 ^ (h + 1)) := by
      have he' := Nat.div_add_mod e (7 ^ (h + 1))
      rw [mul_comm] at he'
      have helt' : e / 7 ^ (h + 1) < K := by
        rw [Nat.div_lt_iff_lt_mul (Nat.pow_pos (by norm_num)), ← hK']
        exact helt
      have hr : e % 7 ^ (h + 1) < 7 ^ (h + 1) :=
        Nat.mod_lt _ (Nat.pow_pos (by norm_num))
      have hoP : e / 7 ^ (h + 1) * 7 ^ (h + 1) + 7 ^ (h + 1)
          ≤ K * 7 ^ (h + 1) := by
        have hle : (e / 7 ^ (h + 1) + 1) * 7 ^ (h + 1)
            ≤ K * 7 ^ (h + 1) :=
          Nat.mul_le_mul_right _ (by omega)
        rwa [Nat.add_mul, one_mul] at hle
      have hexp : (K - e / 7 ^ (h + 1) - 1) * 7 ^ (h + 1)
          = K * 7 ^ (h + 1) - e / 7 ^ (h + 1) * 7 ^ (h + 1)
            - 7 ^ (h + 1) := by
        rw [Nat.sub_mul, Nat.sub_mul, one_mul]
      rw [hexp, hK']
      omega
    rw [hdec]
    have hsplit : ((K - e / 7 ^ (h + 1) - 1) * 7 ^ (h + 1)
          + (7 ^ (h + 1) - e % 7 ^ (h + 1))) % 7 ^ (h + 1)
        = (7 ^ (h + 1) - e % 7 ^ (h + 1)) % 7 ^ (h + 1) := by
      rw [add_comm,
        mul_comm (K - e / 7 ^ (h + 1) - 1) (7 ^ (h + 1))]
      exact Nat.add_mul_mod_self_left _ _ _
    rw [hsplit]
    have hlt' : 7 ^ (h + 1) - e % 7 ^ (h + 1) < 7 ^ (h + 1) := by
      have hpos : 0 < e % 7 ^ (h + 1) := by
        rw [hub]
        exact Nat.mul_pos hu0 (Nat.pow_pos (by norm_num))
      omega
    rw [Nat.mod_eq_of_lt hlt', hub, pow_succ', Nat.sub_mul]
  have ⟨hw0, hνw, hrw⟩ :=
    level_of_mod_block hmod (by omega : 0 < 7 - (runit7 e).val)
      (by omega : 7 - (runit7 e).val < 7)
  refine ⟨hνw, ?_⟩
  rw [hrw]
  rw [Nat.cast_sub (by omega : (runit7 e).val ≤ 7)]
  push_cast
  rw [show (7 : ZMod 7) = 0 from by decide, zero_sub,
    ZMod.natCast_zmod_val]

/-! ### §0.3 `eMod7` congruence algebra on same-branch triples -/

/-- `(e(x,z) : ZMod N) = e(x,y) + e(y,z)` when all pairs are `same`. -/
private theorem eMod7_cast_add {m x y z : ℕ}
    (hxy : residueRelOf x y = residueRel.same)
    (hyz : residueRelOf y z = residueRel.same)
    (hxz : residueRelOf x z = residueRel.same) :
    ((eMod7 m x z : ℕ) : ZMod (7 ^ (m + 1)))
      = (eMod7 m x y : ZMod _) + (eMod7 m y z : ZMod _) := by
  rw [eMod7_zmod_cast_same hxz, eMod7_zmod_cast_same hxy,
    eMod7_zmod_cast_same hyz]
  ring

/-- As naturals: `e(x,z) = (e(x,y) + e(y,z)) % N`. -/
private theorem eMod7_add_eq {m x y z : ℕ}
    (hxy : residueRelOf x y = residueRel.same)
    (hyz : residueRelOf y z = residueRel.same)
    (hxz : residueRelOf x z = residueRel.same) :
    eMod7 m x z = (eMod7 m x y + eMod7 m y z) % 7 ^ (m + 1) := by
  have h := eMod7_cast_add (m := m) hxy hyz hxz
  rw [← Nat.cast_add] at h
  rw [ZMod.natCast_eq_natCast_iff'] at h
  have hlt : eMod7 m x z < 7 ^ (m + 1) := eMod7_lt _ _ _
  rwa [Nat.mod_eq_of_lt hlt] at h

/-- `(e(x,y) : ZMod N) = e(x,l) − e(y,l)` for `same` pairs. -/
private theorem eMod7_cast_sub {m x y l : ℕ}
    (hxl : residueRelOf x l = residueRel.same)
    (hyl : residueRelOf y l = residueRel.same)
    (hxy : residueRelOf x y = residueRel.same) :
    ((eMod7 m x y : ℕ) : ZMod (7 ^ (m + 1)))
      = (eMod7 m x l : ZMod _) - (eMod7 m y l : ZMod _) := by
  rw [eMod7_zmod_cast_same hxy, eMod7_zmod_cast_same hxl,
    eMod7_zmod_cast_same hyl]
  ring

/-- As naturals: `e(x,y) = (e(x,l) + N − e(y,l)) % N`. -/
private theorem eMod7_sub_eq {m x y l : ℕ}
    (hxl : residueRelOf x l = residueRel.same)
    (hyl : residueRelOf y l = residueRel.same)
    (hxy : residueRelOf x y = residueRel.same) :
    eMod7 m x y
      = (eMod7 m x l + 7 ^ (m + 1) - eMod7 m y l) % 7 ^ (m + 1) := by
  have h := eMod7_cast_sub (m := m) hxl hyl hxy
  have hcast : ((eMod7 m x y : ℕ) : ZMod (7 ^ (m + 1)))
      = ((eMod7 m x l + 7 ^ (m + 1) - eMod7 m y l : ℕ) : ZMod _) := by
    rw [h]
    have hlt : eMod7 m y l ≤ eMod7 m x l + 7 ^ (m + 1) := by
      have := eMod7_lt m y l
      omega
    rw [Nat.cast_sub hlt, Nat.cast_add, ZMod.natCast_self]
    ring
  rw [ZMod.natCast_eq_natCast_iff'] at hcast
  have hlt : eMod7 m x y < 7 ^ (m + 1) := eMod7_lt _ _ _
  rwa [Nat.mod_eq_of_lt hlt] at hcast

/-- `e(y,x) = (N − e(x,y)) % N` for `same` pairs (both `0` or negated). -/
private theorem eMod7_neg_eq {m x y : ℕ}
    (hxy : residueRelOf x y = residueRel.same)
    (hyx : residueRelOf y x = residueRel.same) :
    eMod7 m y x = (7 ^ (m + 1) - eMod7 m x y) % 7 ^ (m + 1) := by
  have hcast : ((eMod7 m y x : ℕ) : ZMod (7 ^ (m + 1)))
      = ((7 ^ (m + 1) - eMod7 m x y : ℕ) : ZMod _) := by
    rw [eMod7_zmod_cast_same hyx]
    have hlt : eMod7 m x y < 7 ^ (m + 1) := eMod7_lt _ _ _
    rw [Nat.cast_sub (by omega : eMod7 m x y ≤ 7 ^ (m + 1)), ZMod.natCast_self,
      eMod7_zmod_cast_same hxy]
    ring
  rw [ZMod.natCast_eq_natCast_iff'] at hcast
  have hlt : eMod7 m y x < 7 ^ (m + 1) := eMod7_lt _ _ _
  rwa [Nat.mod_eq_of_lt hlt] at hcast

/-! ### §0.4 Consequences: level arithmetic of difference residues -/

/-- `e(y,x)` has the same level and negated unit as `e(x,y)` (`same`
pairs). -/
private theorem enu7_neg {m x y : ℕ}
    (hxy : residueRelOf x y = residueRel.same)
    (hyx : residueRelOf y x = residueRel.same) :
    padicValNat 7 (eMod7 m y x) = padicValNat 7 (eMod7 m x y) ∧
    runit7 (eMod7 m y x) = - runit7 (eMod7 m x y) := by
  rw [eMod7_neg_eq hxy hyx]
  rcases eq_or_ne (eMod7 m x y) 0 with he | he
  · rw [he, Nat.sub_zero, Nat.mod_self]
    simp [runit7]
  · set e := eMod7 m x y
    have hlt : e < 7 ^ (m + 1) := eMod7_lt _ _ _
    have hνm : padicValNat 7 e ≤ m := by
      have hndvd : ¬ 7 ^ (m + 1) ∣ e := by
        intro hd
        exact he (Nat.eq_zero_of_dvd_of_lt hd hlt)
      by_contra hc
      push_neg at hc
      exact hndvd ((Nat.pow_dvd_iff_le_padicValNat (by norm_num) he).mpr hc)
    have hw : (7 ^ (m + 1) - e) % 7 ^ (m + 1) = 7 ^ (m + 1) - e := by
      rw [Nat.mod_eq_of_lt (by omega : 7 ^ (m + 1) - e < 7 ^ (m + 1))]
    rw [hw]
    exact neg_resid_level he hlt hνm

/-- `e(y,x)` has the same level as `e(x,y)` (`same` pairs). -/
private theorem enu7_sym {m x y : ℕ}
    (hxy : residueRelOf x y = residueRel.same)
    (hyx : residueRelOf y x = residueRel.same) :
    padicValNat 7 (eMod7 m y x) = padicValNat 7 (eMod7 m x y) :=
  (enu7_neg hxy hyx).1

/-- `e(y,x)` has negated unit (`same` pairs). -/
private theorem runit7_eMod7_neg {m x y : ℕ}
    (hxy : residueRelOf x y = residueRel.same)
    (hyx : residueRelOf y x = residueRel.same) :
    runit7 (eMod7 m y x) = - runit7 (eMod7 m x y) :=
  (enu7_neg hxy hyx).2

/-- **Block value of `e(x,y)`** through a common point `l` when both
`(x,l)`, `(y,l)` pairs have level `h ≤ m`: reads
`(r(e_{xl}) − r(e_{yl}))·7^h` mod `7^{h+1}`. -/
private theorem eMod7_sub_block {m x y l h : ℕ}
    (hxl : residueRelOf x l = residueRel.same)
    (hyl : residueRelOf y l = residueRel.same)
    (hxy : residueRelOf x y = residueRel.same)
    (hxl0 : eMod7 m x l ≠ 0) (hyl0 : eMod7 m y l ≠ 0)
    (hxlν : padicValNat 7 (eMod7 m x l) = h)
    (hylν : padicValNat 7 (eMod7 m y l) = h) (hm : h ≤ m) :
    eMod7 m x y % 7 ^ (h + 1)
      = (runit7 (eMod7 m x l) - runit7 (eMod7 m y l)).val * 7 ^ h := by
  rw [eMod7_sub_eq hxl hyl hxy]
  rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 7 (by omega : h + 1 ≤ m + 1))]
  rw [wrap_sub_mod_gen (Nat.pow_pos (by norm_num))
    (Nat.pow_dvd_pow 7 (by omega : h + 1 ≤ m + 1))
    (by have := eMod7_lt m y l; omega)]
  exact sub_mod_block hxl0 hyl0 hxlν hylν

/-- **Block value of `e(x,z)`** as the sum of the `(x,y)`, `(y,z)`
residues at common level `h ≤ m`. -/
private theorem eMod7_add_block {m x y z h : ℕ}
    (hxy : residueRelOf x y = residueRel.same)
    (hyz : residueRelOf y z = residueRel.same)
    (hxz : residueRelOf x z = residueRel.same)
    (hxy0 : eMod7 m x y ≠ 0) (hyz0 : eMod7 m y z ≠ 0)
    (hxyν : padicValNat 7 (eMod7 m x y) = h)
    (hyzν : padicValNat 7 (eMod7 m y z) = h) (hm : h ≤ m) :
    eMod7 m x z % 7 ^ (h + 1)
      = (runit7 (eMod7 m x y) + runit7 (eMod7 m y z)).val * 7 ^ h := by
  rw [eMod7_add_eq hxy hyz hxz]
  rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 7 (by omega : h + 1 ≤ m + 1))]
  rw [Nat.add_mod]
  rw [nat_mod_pow_succ_of_padic hxy0 hxyν,
    nat_mod_pow_succ_of_padic hyz0 hyzν]
  have hvv : (runit7 (eMod7 m x y) + runit7 (eMod7 m y z)).val
      = ((runit7 (eMod7 m x y)).val + (runit7 (eMod7 m y z)).val) % 7 :=
    ZMod.val_add _ _
  rw [hvv, ← Nat.add_mul, pow_succ', Nat.mul_mod_mul_right]

/-- Equal `r`'s through a common point force `e(x,y) = 0` or level
`> h` (the "collision" alternative). -/
private theorem eMod7_level_gt_of_runit_eq {m x y l h : ℕ}
    (hxl : residueRelOf x l = residueRel.same)
    (hyl : residueRelOf y l = residueRel.same)
    (hxy : residueRelOf x y = residueRel.same)
    (hxl0 : eMod7 m x l ≠ 0) (hyl0 : eMod7 m y l ≠ 0)
    (hxlν : padicValNat 7 (eMod7 m x l) = h)
    (hylν : padicValNat 7 (eMod7 m y l) = h) (hm : h ≤ m)
    (hr : runit7 (eMod7 m x l) = runit7 (eMod7 m y l)) :
    eMod7 m x y = 0 ∨ h < padicValNat 7 (eMod7 m x y) := by
  have hblk := eMod7_sub_block hxl hyl hxy hxl0 hyl0 hxlν hylν hm
  rw [hr, sub_self, ZMod.val_zero, zero_mul] at hblk
  rcases eq_or_ne (eMod7 m x y) 0 with h0 | h0
  · exact Or.inl h0
  · right
    have hdvd : 7 ^ (h + 1) ∣ eMod7 m x y := Nat.dvd_iff_mod_eq_zero.mpr hblk
    exact (Nat.pow_dvd_iff_le_padicValNat (by norm_num) h0).mp hdvd

/-- Distinct `r`'s through a common point give `e(x,y)` level `h` and
unit `r(e_{xl}) − r(e_{yl})`. -/
private theorem eMod7_level_of_runit_ne {m x y l h : ℕ}
    (hxl : residueRelOf x l = residueRel.same)
    (hyl : residueRelOf y l = residueRel.same)
    (hxy : residueRelOf x y = residueRel.same)
    (hxl0 : eMod7 m x l ≠ 0) (hyl0 : eMod7 m y l ≠ 0)
    (hxlν : padicValNat 7 (eMod7 m x l) = h)
    (hylν : padicValNat 7 (eMod7 m y l) = h) (hm : h ≤ m)
    (hr : runit7 (eMod7 m x l) ≠ runit7 (eMod7 m y l)) :
    eMod7 m x y ≠ 0 ∧ padicValNat 7 (eMod7 m x y) = h ∧
      runit7 (eMod7 m x y)
        = runit7 (eMod7 m x l) - runit7 (eMod7 m y l) := by
  have hblk := eMod7_sub_block hxl hyl hxy hxl0 hyl0 hxlν hylν hm
  have hs : 0 < (runit7 (eMod7 m x l) - runit7 (eMod7 m y l)).val := by
    rcases Nat.eq_zero_or_pos
        (runit7 (eMod7 m x l) - runit7 (eMod7 m y l)).val with h0 | h0
    · exfalso
      rw [ZMod.val_eq_zero] at h0
      exact hr (sub_eq_zero.mp h0)
    · exact h0
  have hs7 : (runit7 (eMod7 m x l) - runit7 (eMod7 m y l)).val < 7 :=
    ZMod.val_lt _
  obtain ⟨hw0, hνw, hrw⟩ := level_of_mod_block hblk hs hs7
  rw [ZMod.natCast_zmod_val] at hrw
  exact ⟨hw0, hνw, hrw⟩

/-- When `r(e_{xy}) + r(e_{yz}) = 0`, the sum residue `e_{xz}` vanishes
or jumps above `h`. -/
private theorem eMod7_level_gt_of_runit_add {m x y z h : ℕ}
    (hxy : residueRelOf x y = residueRel.same)
    (hyz : residueRelOf y z = residueRel.same)
    (hxz : residueRelOf x z = residueRel.same)
    (hxy0 : eMod7 m x y ≠ 0) (hyz0 : eMod7 m y z ≠ 0)
    (hxyν : padicValNat 7 (eMod7 m x y) = h)
    (hyzν : padicValNat 7 (eMod7 m y z) = h) (hm : h ≤ m)
    (hr : runit7 (eMod7 m x y) + runit7 (eMod7 m y z) = 0) :
    eMod7 m x z = 0 ∨ h < padicValNat 7 (eMod7 m x z) := by
  have hblk := eMod7_add_block hxy hyz hxz hxy0 hyz0 hxyν hyzν hm
  rw [hr, ZMod.val_zero, zero_mul] at hblk
  rcases eq_or_ne (eMod7 m x z) 0 with h0 | h0
  · exact Or.inl h0
  · right
    have hdvd : 7 ^ (h + 1) ∣ eMod7 m x z := Nat.dvd_iff_mod_eq_zero.mpr hblk
    exact (Nat.pow_dvd_iff_le_padicValNat (by norm_num) h0).mp hdvd

/-- Non-canceling sum: `e_{xz}` has level `h`, unit `r_{xy} + r_{yz}`. -/
private theorem eMod7_level_of_runit_add {m x y z h : ℕ}
    (hxy : residueRelOf x y = residueRel.same)
    (hyz : residueRelOf y z = residueRel.same)
    (hxz : residueRelOf x z = residueRel.same)
    (hxy0 : eMod7 m x y ≠ 0) (hyz0 : eMod7 m y z ≠ 0)
    (hxyν : padicValNat 7 (eMod7 m x y) = h)
    (hyzν : padicValNat 7 (eMod7 m y z) = h) (hm : h ≤ m)
    (hr : runit7 (eMod7 m x y) + runit7 (eMod7 m y z) ≠ 0) :
    eMod7 m x z ≠ 0 ∧ padicValNat 7 (eMod7 m x z) = h ∧
      runit7 (eMod7 m x z)
        = runit7 (eMod7 m x y) + runit7 (eMod7 m y z) := by
  have hblk := eMod7_add_block hxy hyz hxz hxy0 hyz0 hxyν hyzν hm
  have hs : 0 < (runit7 (eMod7 m x y) + runit7 (eMod7 m y z)).val := by
    rcases Nat.eq_zero_or_pos
        (runit7 (eMod7 m x y) + runit7 (eMod7 m y z)).val with h0 | h0
    · exfalso
      rw [ZMod.val_eq_zero] at h0
      exact hr h0
    · exact h0
  have hs7 : (runit7 (eMod7 m x y) + runit7 (eMod7 m y z)).val < 7 :=
    ZMod.val_lt _
  obtain ⟨hw0, hνw, hrw⟩ := level_of_mod_block hblk hs hs7
  rw [ZMod.natCast_zmod_val] at hrw
  exact ⟨hw0, hνw, hrw⟩

/-- Min-level rule: if `e_{xy}` has level `h < min(ν(e_{yz}), m+1)`
(i.e. `7^{h+1} ∣ e_{yz}` or `e_{yz} = 0`), then `e_{xz}` has level `h`
and unit `r(e_{xy})`. -/
private theorem eMod7_level_min {m x y z h : ℕ}
    (hxy : residueRelOf x y = residueRel.same)
    (hyz : residueRelOf y z = residueRel.same)
    (hxz : residueRelOf x z = residueRel.same)
    (hxy0 : eMod7 m x y ≠ 0)
    (hxyν : padicValNat 7 (eMod7 m x y) = h) (hm : h ≤ m)
    (hyz_dvd : eMod7 m y z = 0 ∨ 7 ^ (h + 1) ∣ eMod7 m y z) :
    eMod7 m x z ≠ 0 ∧ padicValNat 7 (eMod7 m x z) = h ∧
      runit7 (eMod7 m x z) = runit7 (eMod7 m x y) := by
  have hblk0 : eMod7 m x z % 7 ^ (h + 1)
      = (runit7 (eMod7 m x y)).val * 7 ^ h := by
    have hub := nat_mod_pow_succ_of_padic hxy0 hxyν
    have hcast : ((eMod7 m x z : ℕ) : ZMod (7 ^ (h + 1)))
        = (eMod7 m x y : ZMod _) := by
      have hcast' : ((eMod7 m x z : ℕ) : ZMod (7 ^ (h + 1)))
          = ((eMod7 m x y + eMod7 m y z : ℕ) : ZMod _) := by
        have hcongr : eMod7 m x z % 7 ^ (h + 1)
            = (eMod7 m x y + eMod7 m y z) % 7 ^ (h + 1) := by
          rw [eMod7_add_eq hxy hyz hxz]
          exact Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 7 (by omega))
        exact (ZMod.natCast_eq_natCast_iff' _ _ _).mpr hcongr
      rw [hcast', Nat.cast_add]
      rcases hyz_dvd with h0 | hd
      · rw [h0, Nat.cast_zero, add_zero]
      · have : (eMod7 m y z : ZMod (7 ^ (h + 1))) = 0 :=
          (ZMod.natCast_eq_zero_iff _ _).mpr hd
        rw [this, add_zero]
    rw [(ZMod.natCast_eq_natCast_iff' _ _ _).mp hcast, hub]
  have hs : 0 < (runit7 (eMod7 m x y)).val := by
    rcases Nat.eq_zero_or_pos (runit7 (eMod7 m x y)).val with h0 | h0
    · exfalso
      rw [ZMod.val_eq_zero] at h0
      exact runit7_ne_zero (Nat.pos_of_ne_zero hxy0) h0
    · exact h0
  obtain ⟨hw0, hνw, hrw⟩ := level_of_mod_block hblk0 hs (ZMod.val_lt _)
  rw [ZMod.natCast_zmod_val] at hrw
  exact ⟨hw0, hνw, hrw⟩

/-! ### §0.5 `elevel7` — the effective level of a difference residue -/

/-- Effective level: `padicValNat` of the residue, but `m + 1` when the
residue vanishes (the true difference is then `≡ 0 mod 7^{m+1}`, i.e.
level `≥ m + 1`; the raw `padicValNat 7 0 = 0` would read it as level
`0` — the source of the `lemma11` countermodel). -/
def elevel7 (m x y : ℕ) : ℕ :=
  if eMod7 m x y = 0 then m + 1 else padicValNat 7 (eMod7 m x y)

theorem elevel7_of_ne {m x y : ℕ} (h : eMod7 m x y ≠ 0) :
    elevel7 m x y = padicValNat 7 (eMod7 m x y) := if_neg h

theorem elevel7_of_eq {m x y : ℕ} (h : eMod7 m x y = 0) :
    elevel7 m x y = m + 1 := if_pos h

theorem elevel7_le {m x y : ℕ} : elevel7 m x y ≤ m + 1 := by
  unfold elevel7
  split_ifs with h
  · omega
  · have h' : padicValNat 7 (eMod7 m x y) ≤ m := enu7_le_of_ne h
    omega

theorem elevel7_sym {m x y : ℕ}
    (hxy : residueRelOf x y = residueRel.same)
    (hyx : residueRelOf y x = residueRel.same) :
    elevel7 m y x = elevel7 m x y := by
  unfold elevel7
  by_cases h : eMod7 m x y = 0
  · have h' : eMod7 m y x = 0 := by
      rw [eMod7_neg_eq hxy hyx, h, Nat.sub_zero, Nat.mod_self]
    rw [if_pos h, if_pos h']
  · have h' : eMod7 m y x ≠ 0 := by
      intro hc
      rw [eMod7_neg_eq hxy hyx] at hc
      have hlt := eMod7_lt m x y
      rcases Nat.lt_or_ge (7 ^ (m + 1) - eMod7 m x y) (7 ^ (m + 1)) with h2 | h2
      · rw [Nat.mod_eq_of_lt h2] at hc
        omega
      · omega
    rw [if_neg h, if_neg h']
    exact enu7_sym hxy hyx

/-- `elevel7 m x y = m + 1` iff the residue vanishes. -/
theorem elevel7_eq_succ {m x y : ℕ} :
    elevel7 m x y = m + 1 ↔ eMod7 m x y = 0 := by
  constructor
  · intro h
    by_cases h0 : eMod7 m x y = 0
    · exact h0
    · exfalso
      rw [elevel7_of_ne h0] at h
      have hle := enu7_le_of_ne h0
      unfold enu7 at hle
      omega
  · exact elevel7_of_eq

/-- Ultrametric bound for `elevel7`: the level of `e_{xz}` is at least the
minimum of the two levels. -/
private theorem elevel7_add_ge {m x y z : ℕ}
    (hxy : residueRelOf x y = residueRel.same)
    (hyz : residueRelOf y z = residueRel.same)
    (hxz : residueRelOf x z = residueRel.same) :
    min (elevel7 m x y) (elevel7 m y z) ≤ elevel7 m x z := by
  set l := min (elevel7 m x y) (elevel7 m y z)
  by_cases hz : eMod7 m x y = 0
  · have hzl : elevel7 m x z = elevel7 m y z := by
      have hxz0 : eMod7 m x z = eMod7 m y z := by
        rw [eMod7_add_eq hxy hyz hxz, hz, zero_add]
        exact Nat.mod_eq_of_lt (eMod7_lt m y z)
      rw [elevel7, elevel7, hxz0]
    rw [hzl]
    exact Nat.min_le_right _ _
  · have hxyν : padicValNat 7 (eMod7 m x y) = elevel7 m x y := by
      rw [elevel7_of_ne hz]
    by_cases hz2 : eMod7 m y z = 0
    · have hxzl : elevel7 m x z = elevel7 m x y := by
        have hxz0 : eMod7 m x z = eMod7 m x y := by
          rw [eMod7_add_eq hxy hyz hxz, hz2, add_zero]
          exact Nat.mod_eq_of_lt (eMod7_lt m x y)
        rw [elevel7, elevel7, hxz0]
      rw [hxzl]
      exact Nat.min_le_left _ _
    · have hyzν : padicValNat 7 (eMod7 m y z) = elevel7 m y z := by
        rw [elevel7_of_ne hz2]
      have hlm : l ≤ m := by
        have h1 : elevel7 m x y ≤ m := by
          rw [elevel7_of_ne hz]; exact enu7_le_of_ne hz
        have := Nat.min_le_left (elevel7 m x y) (elevel7 m y z)
        omega
      have hd1 : 7 ^ l ∣ eMod7 m x y :=
        (Nat.pow_dvd_iff_le_padicValNat (by norm_num) hz).mpr (by
          rw [hxyν]; exact Nat.min_le_left _ _)
      have hd2 : 7 ^ l ∣ eMod7 m y z :=
        (Nat.pow_dvd_iff_le_padicValNat (by norm_num) hz2).mpr (by
          rw [hyzν]; exact Nat.min_le_right _ _)
      have hN : 7 ^ l ∣ 7 ^ (m + 1) := Nat.pow_dvd_pow 7 (by omega)
      have hdz : 7 ^ l ∣ eMod7 m x z := by
        have hmod : eMod7 m x z % 7 ^ l = 0 := by
          rw [eMod7_add_eq hxy hyz hxz, Nat.mod_mod_of_dvd _ hN]
          exact Nat.dvd_iff_mod_eq_zero.mp (Nat.dvd_add hd1 hd2)
        exact Nat.dvd_iff_mod_eq_zero.mpr hmod
      rcases eq_or_ne (eMod7 m x z) 0 with h0 | h0
      · rw [elevel7_of_eq h0]
        omega
      · rw [elevel7_of_ne h0]
        exact (Nat.pow_dvd_iff_le_padicValNat (by norm_num) h0).mp hdz

/-- Strict ultrametric equality: when the two levels differ, the third level
equals the smaller one. -/
private theorem elevel7_add_eq_of_lt {m x y z : ℕ}
    (hxy : residueRelOf x y = residueRel.same)
    (hyz : residueRelOf y z = residueRel.same)
    (hxz : residueRelOf x z = residueRel.same)
    (h : elevel7 m x y < elevel7 m y z) :
    elevel7 m x z = elevel7 m x y := by
  have hz : eMod7 m x y ≠ 0 := by
    intro h0
    rw [elevel7_of_eq h0] at h
    have := elevel7_le (m := m) (x := y) (y := z)
    omega
  have hxyν : padicValNat 7 (eMod7 m x y) = elevel7 m x y := by
    rw [elevel7_of_ne hz]
  have hlm : elevel7 m x y ≤ m := by
    rw [elevel7_of_ne hz]; exact enu7_le_of_ne hz
  have hdvd : eMod7 m y z = 0 ∨ 7 ^ (elevel7 m x y + 1) ∣ eMod7 m y z := by
    rcases eq_or_ne (eMod7 m y z) 0 with h0 | h0
    · exact Or.inl h0
    · right
      have hyzν : padicValNat 7 (eMod7 m y z) = elevel7 m y z := by
        rw [elevel7_of_ne h0]
      exact (Nat.pow_dvd_iff_le_padicValNat (by norm_num) h0).mpr (by
        rw [hyzν]; omega)
  obtain ⟨h0, hν, _⟩ := eMod7_level_min hxy hyz hxz hz hxyν hlm hdvd
  rw [elevel7_of_ne h0, hν]

/-! ### §1 Lemma 11 — numbering a three-element set -/

set_option synthInstance.maxSize 16384 in
/-- Finite unit-ratio core of Lemma 11: writing `uac = uab + ubc` for the
third unit difference, some ordering `(d1,d2,d3)` of the three points makes
`r13` a `2`-multiple of `r23`, or a `3`-multiple with `r13 = ±s`.  The twelve
disjuncts correspond to the six permutations × (ratio-2 | ratio-3). -/
private theorem lemma11_units :
    ∀ uab ubc s : ZMod 7, uab ≠ 0 → ubc ≠ 0 → uab + ubc ≠ 0 → s ≠ 0 →
      (uab + ubc = 2 * ubc) ∨ (uab = -2 * ubc) ∨
      (ubc = 2 * (uab + ubc)) ∨ (uab = 2 * (uab + ubc)) ∨
      (-ubc = 2 * uab) ∨ (uab + ubc = 2 * uab) ∨
      ((uab + ubc = 3 * ubc) ∧ (uab + ubc = s ∨ uab + ubc = -s)) ∨
      ((uab = -3 * ubc) ∧ (uab = s ∨ uab = -s)) ∨
      ((ubc = 3 * (uab + ubc)) ∧ (ubc = s ∨ ubc = -s)) ∨
      ((uab = 3 * (uab + ubc)) ∧ (uab = s ∨ uab = -s)) ∨
      ((-ubc = 3 * uab) ∧ (ubc = s ∨ ubc = -s)) ∨
      ((uab + ubc = 3 * uab) ∧ (uab + ubc = s ∨ uab + ubc = -s)) := by
  decide

/-- `runit7` of a zero residue is `0`. -/
private theorem runit7_zero : runit7 0 = 0 := by
  simp [runit7]

set_option maxHeartbeats 6400000 in
/-- Paper Lemma 11: three elements of a `same`-class set with common unit
residue `s` can be numbered `d1,d2,d3` so that either the level pattern is
`l13 > l23 = l12` (an unequal-level case) or `l13 = l23` and the unit ratio
`r13/r23` is `2`, or `3` with `r13 = ±s`.  Levels are measured by `elevel7`
(effective level `m + 1` on zero residues) — the raw `padicValNat`
formulation is false on collision cases. -/
theorem lemma11 {m : ℕ} {A1 : Finset ℕ} (hcard : A1.card = 3) (s : ZMod 7)
    (hpos : ∀ d ∈ A1, 0 < d) (hunit : ∀ d ∈ A1, padicValNat 7 d = 0)
    (hsame : ∀ d ∈ A1, runit7 d = s) :
    ∃ d1 ∈ A1, ∃ d2 ∈ A1, ∃ d3 ∈ A1,
      A1 = {d1, d2, d3} ∧
      ((elevel7 m d1 d3 > elevel7 m d2 d3 ∧
          elevel7 m d2 d3 = elevel7 m d1 d2) ∨
        (elevel7 m d1 d3 = elevel7 m d2 d3 ∧
          (runit7 (eMod7 m d1 d3) = 2 * runit7 (eMod7 m d2 d3) ∨
            (runit7 (eMod7 m d1 d3) = 3 * runit7 (eMod7 m d2 d3) ∧
              (runit7 (eMod7 m d1 d3) = s ∨ runit7 (eMod7 m d1 d3) = -s))))) := by
  obtain ⟨a, b, c, hab, hac, hbc, hA⟩ := Finset.card_eq_three.mp hcard
  have ha : a ∈ A1 := by rw [hA]; simp
  have hb : b ∈ A1 := by rw [hA]; simp
  have hc : c ∈ A1 := by rw [hA]; simp
  have hpa := hpos a ha; have hpb := hpos b hb; have hpc := hpos c hc
  -- all six pair-relations are `same`
  have rab : residueRelOf a b = residueRel.same :=
    rel_same (by rw [hsame a ha, hsame b hb]) (ne_of_gt hpb)
  have rba : residueRelOf b a = residueRel.same :=
    rel_same (by rw [hsame b hb, hsame a ha]) (ne_of_gt hpa)
  have rac : residueRelOf a c = residueRel.same :=
    rel_same (by rw [hsame a ha, hsame c hc]) (ne_of_gt hpc)
  have rca : residueRelOf c a = residueRel.same :=
    rel_same (by rw [hsame c hc, hsame a ha]) (ne_of_gt hpa)
  have rbc : residueRelOf b c = residueRel.same :=
    rel_same (by rw [hsame b hb, hsame c hc]) (ne_of_gt hpc)
  have rcb : residueRelOf c b = residueRel.same :=
    rel_same (by rw [hsame c hc, hsame b hb]) (ne_of_gt hpb)
  have hset : ∀ d1 d2 d3 : ℕ,
      ({a, b, c} : Finset ℕ) = {d1, d2, d3} → A1 = {d1, d2, d3} := by
    intro d1 d2 d3 h; rw [hA, h]
  have sabc : ({a, b, c} : Finset ℕ) = {a, b, c} := rfl
  have sacb : ({a, b, c} : Finset ℕ) = {a, c, b} := by
    ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  have sbac : ({a, b, c} : Finset ℕ) = {b, a, c} := by
    ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  have sbca : ({a, b, c} : Finset ℕ) = {b, c, a} := by
    ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  have scab : ({a, b, c} : Finset ℕ) = {c, a, b} := by
    ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  have scba : ({a, b, c} : Finset ℕ) = {c, b, a} := by
    ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  rcases lt_trichotomy (elevel7 m a b) (elevel7 m b c) with hlt | heq | hgt
  · -- Lab < Lbc: then Lac = Lab; number (b,a,c): l13 = Lbc > Lac = l23 = Lab = l12
    have hLac : elevel7 m a c = elevel7 m a b :=
      elevel7_add_eq_of_lt rab rbc rac hlt
    refine ⟨b, hb, a, ha, c, hc, hset b a c sbac, Or.inl ⟨?_, ?_⟩⟩
    · rw [hLac]; exact hlt
    · rw [hLac]; exact (elevel7_sym rab rba).symm
  · -- Lab = Lbc = l
    have hge : elevel7 m a b ≤ elevel7 m a c := by
      have hge' := elevel7_add_ge (m := m) rab rbc rac
      rwa [min_eq_left (le_of_eq heq)] at hge'
    rcases eq_or_lt_of_le hge with heq' | hgt'
    · -- heq' : elevel7 a b = elevel7 a c; all three levels equal l := Lab
      have hl : elevel7 m a b = elevel7 m a c := heq'
      have hcl : elevel7 m a c = elevel7 m b c := heq'.symm.trans heq
      by_cases hz : eMod7 m a c = 0
      · -- collision: all residues zero, ratio-2 holds trivially
        have hzab : eMod7 m a b = 0 := by
          have h1 : elevel7 m a b = m + 1 := by
            rw [heq', elevel7_eq_succ]; exact hz
          exact elevel7_eq_succ.mp h1
        have hzbc : eMod7 m b c = 0 := by
          have h1 : elevel7 m b c = m + 1 := by
            rw [← heq, heq', elevel7_eq_succ]; exact hz
          exact elevel7_eq_succ.mp h1
        refine ⟨a, ha, b, hb, c, hc, hset a b c rfl, Or.inr ⟨hcl, Or.inl ?_⟩⟩
        rw [hz, hzbc, runit7_zero, mul_zero]
      · -- all nonzero: unit analysis
        have h0ab : eMod7 m a b ≠ 0 := by
          intro h0
          rw [elevel7_of_eq h0] at hl
          rw [elevel7_of_ne hz] at hl
          have hnu := enu7_le_of_ne hz
          unfold enu7 at hnu
          omega
        have h0bc : eMod7 m b c ≠ 0 := by
          intro h0
          rw [elevel7_of_eq h0] at heq
          rw [elevel7_of_ne h0ab] at heq
          have hnu := enu7_le_of_ne h0ab
          unfold enu7 at hnu
          omega
        have hlm : elevel7 m a b ≤ m := by
          rw [elevel7_of_ne h0ab]; exact enu7_le_of_ne h0ab
        have hνab : padicValNat 7 (eMod7 m a b) = elevel7 m a b :=
          (elevel7_of_ne h0ab).symm
        have hνbc : padicValNat 7 (eMod7 m b c) = elevel7 m a b := by
          rw [heq]; exact (elevel7_of_ne h0bc).symm
        have hνac : padicValNat 7 (eMod7 m a c) = elevel7 m a b := by
          rw [hl]; exact (elevel7_of_ne hz).symm
        -- uac = uab + ubc ≠ 0
        have hne : runit7 (eMod7 m a b) + runit7 (eMod7 m b c) ≠ 0 := by
          intro hsum
          obtain hz2 | hlt2 := eMod7_level_gt_of_runit_add
              rab rbc rac h0ab h0bc hνab hνbc hlm hsum
          · exact hz hz2
          · rw [hνac] at hlt2; omega
        obtain ⟨_, _, hruv⟩ := eMod7_level_of_runit_add
            rab rbc rac h0ab h0bc hνab hνbc hlm hne
        have hub0 : runit7 (eMod7 m a b) ≠ 0 :=
          runit7_ne_zero (Nat.pos_of_ne_zero h0ab)
        have huc0 : runit7 (eMod7 m b c) ≠ 0 :=
          runit7_ne_zero (Nat.pos_of_ne_zero h0bc)
        have hs0 : s ≠ 0 := by
          rw [← hsame a ha]
          exact runit7_ne_zero hpa
        -- reversed unit values
        have huba : runit7 (eMod7 m b a) = -runit7 (eMod7 m a b) :=
          runit7_eMod7_neg rab rba
        have hucb : runit7 (eMod7 m c b) = -runit7 (eMod7 m b c) :=
          runit7_eMod7_neg rbc rcb
        have huca : runit7 (eMod7 m c a) = -runit7 (eMod7 m a c) :=
          runit7_eMod7_neg rac rca
        have hubc' : elevel7 m b c = elevel7 m a b := heq.symm
        have hucb' : elevel7 m c b = elevel7 m a b := by
          rw [elevel7_sym rbc rcb]; exact hubc'
        have huba' : elevel7 m b a = elevel7 m a b := elevel7_sym rab rba
        have huca' : elevel7 m c a = elevel7 m a b := by
          rw [elevel7_sym rac rca]; exact heq'.symm
        rcases lemma11_units (runit7 (eMod7 m a b)) (runit7 (eMod7 m b c)) s
          hub0 huc0 hne hs0 with
          h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1
        · -- perm (a,b,c): r13 = uac = 2·ubc
          rw [← hruv] at h1
          exact ⟨a, ha, b, hb, c, hc, hset a b c rfl,
            Or.inr ⟨hcl, Or.inl h1⟩⟩
        · -- perm (a,c,b): uab = −2·ubc → r13 = uab = 2·(−ubc) = 2·r23
          refine ⟨a, ha, c, hc, b, hb, hset a c b sacb, Or.inr ⟨?_, Or.inl ?_⟩⟩
          · rw [elevel7_sym rbc rcb]; exact heq
          · rw [hucb, h1]; ring
        · -- perm (b,a,c): ubc = 2·uac → r13 = ubc = 2·r23
          rw [← hruv] at h1
          refine ⟨b, hb, a, ha, c, hc, hset b a c sbac, Or.inr ⟨?_, Or.inl ?_⟩⟩
          · rw [hubc']; exact heq'
          · rw [h1]
        · -- perm (b,c,a): uab = 2·uac → −uab = 2·(−uac)
          rw [← hruv] at h1
          refine ⟨b, hb, c, hc, a, ha, hset b c a sbca, Or.inr ⟨?_, Or.inl ?_⟩⟩
          · rw [huba', huca']
          · rw [huba, huca, h1]; ring
        · -- perm (c,a,b): −ubc = 2·uab
          refine ⟨c, hc, a, ha, b, hb, hset c a b scab, Or.inr ⟨?_, Or.inl ?_⟩⟩
          · rw [hucb']
          · rw [hucb]; exact h1
        · -- perm (c,b,a): uac = 2·uab → −uac = 2·(−uab)
          rw [← hruv] at h1
          refine ⟨c, hc, b, hb, a, ha, hset c b a scba, Or.inr ⟨?_, Or.inl ?_⟩⟩
          · rw [huca', huba']
          · rw [huca, huba, h1]; ring
        · -- perm (a,b,c) ratio-3
          obtain ⟨hr, hsgn⟩ := h1; rw [← hruv] at hr hsgn
          exact ⟨a, ha, b, hb, c, hc, hset a b c rfl,
            Or.inr ⟨hcl, Or.inr ⟨hr, hsgn⟩⟩⟩
        · -- perm (a,c,b) ratio-3: uab = −3·ubc, r13 = uab = ±s
          obtain ⟨hr, hsgn⟩ := h1
          refine ⟨a, ha, c, hc, b, hb, hset a c b sacb, Or.inr ⟨?_, Or.inr ⟨?_, ?_⟩⟩⟩
          · rw [elevel7_sym rbc rcb]; exact heq
          · rw [hucb, hr]; ring
          · exact hsgn
        · -- perm (b,a,c) ratio-3: ubc = 3·uac, r13 = ubc = ±s
          obtain ⟨hr, hsgn⟩ := h1; rw [← hruv] at hr
          refine ⟨b, hb, a, ha, c, hc, hset b a c sbac, Or.inr ⟨?_, Or.inr ⟨?_, ?_⟩⟩⟩
          · rw [hubc']; exact heq'
          · rw [hr]
          · exact hsgn
        · -- perm (b,c,a) ratio-3: uab = 3·uac → −uab = 3·(−uac); r13 = −uab
          obtain ⟨hr, hsgn⟩ := h1; rw [← hruv] at hr
          refine ⟨b, hb, c, hc, a, ha, hset b c a sbca, Or.inr ⟨?_, Or.inr ⟨?_, ?_⟩⟩⟩
          · rw [huba', huca']
          · rw [huba, huca, hr]; ring
          · rcases hsgn with hsgn | hsgn
            · right; rw [huba, hsgn]
            · left; rw [huba, hsgn, neg_neg]
        · -- perm (c,a,b) ratio-3: −ubc = 3·uab; r13 = −ubc = ±s
          obtain ⟨hr, hsgn⟩ := h1
          refine ⟨c, hc, a, ha, b, hb, hset c a b scab, Or.inr ⟨?_, Or.inr ⟨?_, ?_⟩⟩⟩
          · rw [hucb']
          · rw [hucb]; exact hr
          · rcases hsgn with hsgn | hsgn
            · right; rw [hucb, hsgn]
            · left; rw [hucb, hsgn, neg_neg]
        · -- perm (c,b,a) ratio-3: uac = 3·uab → −uac = 3·(−uab); r13 = −uac
          obtain ⟨hr, hsgn⟩ := h1; rw [← hruv] at hr hsgn
          refine ⟨c, hc, b, hb, a, ha, hset c b a scba, Or.inr ⟨?_, Or.inr ⟨?_, ?_⟩⟩⟩
          · rw [huca', huba']
          · rw [huca, huba, hr]; ring
          · rcases hsgn with hsgn | hsgn
            · right; rw [huca, hsgn]
            · left; rw [huca, hsgn, neg_neg]
    · -- Lac > Lab: number (a,b,c): l13 = Lac > Lbc = l23; l23 = Lbc = Lab = l12
      refine ⟨a, ha, b, hb, c, hc, hset a b c rfl, Or.inl ⟨?_, ?_⟩⟩
      · rw [← heq]; exact hgt'
      · exact heq.symm
  · -- Lab > Lbc: then Lac = Lbc; number (a,c,b): l13 = Lab > Lbc = Lcb = l23;
    -- l23 = Lcb = Lbc = Lac = l12
    have hLac : elevel7 m a c = elevel7 m b c := by
      have h' : elevel7 m c b < elevel7 m b a := by
        rw [elevel7_sym rbc rcb, elevel7_sym rab rba]; exact hgt
      have h := elevel7_add_eq_of_lt rcb rba rca h'
      rw [elevel7_sym rac rca] at h
      rw [h, elevel7_sym rbc rcb]
    refine ⟨a, ha, c, hc, b, hb, hset a c b sacb, Or.inl ⟨?_, ?_⟩⟩
    · rw [elevel7_sym rbc rcb]; exact hgt
    · rw [elevel7_sym rbc rcb]; exact hLac.symm

/-! ### §2 Lemma 10 — numbering a four-element subset -/

set_option synthInstance.maxSize 16384 in
/-- Finite unit-ratio core of Lemma 10: for the cocycle `u_{ij} = w_i − w_j`
(`w_0 = 0`) of edge-units on four points (all edges nonzero ⇒ `w_i` nonzero
and pairwise distinct), some numbering `(d1,d2,d3,d4)` of the four points
satisfies `u_{d3,d1} = 2·u_{d2,d1}` and `u_{d4,d1} ∈ {3,4}·u_{d2,d1}`.
The 24 disjuncts enumerate the permutations of `(0,1,2,3)`. -/
private theorem lemma10_units :
    ∀ w1 w2 w3 : ZMod 7, w1 ≠ 0 → w2 ≠ 0 → w3 ≠ 0 →
      w1 ≠ w2 → w1 ≠ w3 → w2 ≠ w3 →
    (w2 = 2 * w1 ∧ (w3 = 3 * w1 ∨ w3 = 4 * w1)) ∨
      (w3 = 2 * w1 ∧ (w2 = 3 * w1 ∨ w2 = 4 * w1)) ∨
      (w1 = 2 * w2 ∧ (w3 = 3 * w2 ∨ w3 = 4 * w2)) ∨
      (w3 = 2 * w2 ∧ (w1 = 3 * w2 ∨ w1 = 4 * w2)) ∨
      (w1 = 2 * w3 ∧ (w2 = 3 * w3 ∨ w2 = 4 * w3)) ∨
      (w2 = 2 * w3 ∧ (w1 = 3 * w3 ∨ w1 = 4 * w3)) ∨
      ((w2 - w1) = 2 * (-w1) ∧ ((w3 - w1) = 3 * (-w1) ∨ (w3 - w1) = 4 * (-w1))) ∨
      ((w3 - w1) = 2 * (-w1) ∧ ((w2 - w1) = 3 * (-w1) ∨ (w2 - w1) = 4 * (-w1))) ∨
      ((-w1) = 2 * (w2 - w1) ∧ ((w3 - w1) = 3 * (w2 - w1) ∨ (w3 - w1) = 4 * (w2 - w1))) ∨
      ((w3 - w1) = 2 * (w2 - w1) ∧ ((-w1) = 3 * (w2 - w1) ∨ (-w1) = 4 * (w2 - w1))) ∨
      ((-w1) = 2 * (w3 - w1) ∧ ((w2 - w1) = 3 * (w3 - w1) ∨ (w2 - w1) = 4 * (w3 - w1))) ∨
      ((w2 - w1) = 2 * (w3 - w1) ∧ ((-w1) = 3 * (w3 - w1) ∨ (-w1) = 4 * (w3 - w1))) ∨
      ((w1 - w2) = 2 * (-w2) ∧ ((w3 - w2) = 3 * (-w2) ∨ (w3 - w2) = 4 * (-w2))) ∨
      ((w3 - w2) = 2 * (-w2) ∧ ((w1 - w2) = 3 * (-w2) ∨ (w1 - w2) = 4 * (-w2))) ∨
      ((-w2) = 2 * (w1 - w2) ∧ ((w3 - w2) = 3 * (w1 - w2) ∨ (w3 - w2) = 4 * (w1 - w2))) ∨
      ((w3 - w2) = 2 * (w1 - w2) ∧ ((-w2) = 3 * (w1 - w2) ∨ (-w2) = 4 * (w1 - w2))) ∨
      ((-w2) = 2 * (w3 - w2) ∧ ((w1 - w2) = 3 * (w3 - w2) ∨ (w1 - w2) = 4 * (w3 - w2))) ∨
      ((w1 - w2) = 2 * (w3 - w2) ∧ ((-w2) = 3 * (w3 - w2) ∨ (-w2) = 4 * (w3 - w2))) ∨
      ((w1 - w3) = 2 * (-w3) ∧ ((w2 - w3) = 3 * (-w3) ∨ (w2 - w3) = 4 * (-w3))) ∨
      ((w2 - w3) = 2 * (-w3) ∧ ((w1 - w3) = 3 * (-w3) ∨ (w1 - w3) = 4 * (-w3))) ∨
      ((-w3) = 2 * (w1 - w3) ∧ ((w2 - w3) = 3 * (w1 - w3) ∨ (w2 - w3) = 4 * (w1 - w3))) ∨
      ((w2 - w3) = 2 * (w1 - w3) ∧ ((-w3) = 3 * (w1 - w3) ∨ (-w3) = 4 * (w1 - w3))) ∨
      ((-w3) = 2 * (w2 - w3) ∧ ((w1 - w3) = 3 * (w2 - w3) ∨ (w1 - w3) = 4 * (w2 - w3))) ∨
      ((w1 - w3) = 2 * (w2 - w3) ∧ ((-w3) = 3 * (w2 - w3) ∨ (-w3) = 4 * (w2 - w3))) := by
  decide

/-- Paper Lemma 10: any four distinct elements of a unit-`s` class admit a
numbering `(d1,d2,d3,d4)` with either an unequal-level pair of differences
at `d1` (`ν(e_{d2,d1}) > ν(e_{d3,d1})`), or a uniform nonzero-difference
level `h` together with the unit-ratio pattern
`r(e_{d3,d1}) = 2·r(e_{d2,d1})`, `r(e_{d4,d1}) ∈ {3,4}·r(e_{d2,d1})`.

NOTE (deviation): the spec's `hsame` quantified only
`residueRelOf d d' = same` for `d ≠ d'` — that form is FALSE
(`A1 = {1, 50, 99, 3}` at `m = 1`: all edge levels `0`, so no strict
asymmetry, and the edge-units `{0,2,5}` admit no ratio pattern).  The
hypothesis is strengthened to the paper's class hypothesis `runit7 d = s`,
matching `lemma11` and the §6 case hypotheses — see
`_reports/lrc7-sec6-l91011.md`. -/
theorem lemma10 {m : ℕ} {A1 : Finset ℕ} (hcard : 4 ≤ A1.card)
    (hpos : ∀ d ∈ A1, 0 < d) (hunit : ∀ d ∈ A1, padicValNat 7 d = 0)
    (s : ZMod 7) (hsame : ∀ d ∈ A1, runit7 d = s) :
    ∃ d1 ∈ A1, ∃ d2 ∈ A1, ∃ d3 ∈ A1, ∃ d4 ∈ A1,
      d1 ≠ d2 ∧ d1 ≠ d3 ∧ d1 ≠ d4 ∧ d2 ≠ d3 ∧ d2 ≠ d4 ∧ d3 ≠ d4 ∧
      (padicValNat 7 (eMod7 m d2 d1) > padicValNat 7 (eMod7 m d3 d1) ∨
        (∃ h : ℕ,
          (∀ x ∈ A1, ∀ y ∈ A1, x ≠ y → eMod7 m x y ≠ 0 →
            padicValNat 7 (eMod7 m x y) = h) ∧
          runit7 (eMod7 m d3 d1) = 2 * runit7 (eMod7 m d2 d1) ∧
          (runit7 (eMod7 m d4 d1) = 3 * runit7 (eMod7 m d2 d1) ∨
            runit7 (eMod7 m d4 d1) = 4 * runit7 (eMod7 m d2 d1)))) := by
  classical
  -- Four distinct elements via repeated `erase`.
  obtain ⟨p0, hp0⟩ := Finset.card_pos.mp (by omega : 0 < A1.card)
  have hA1 : (A1.erase p0).card = A1.card - 1 := Finset.card_erase_of_mem hp0
  obtain ⟨p1, hp1e⟩ := Finset.card_pos.mp (by omega : 0 < (A1.erase p0).card)
  have hp1' : p1 ∈ A1.erase p0 := hp1e
  have hp1 : p1 ∈ A1 := Finset.mem_of_mem_erase hp1'
  have hp10 : p1 ≠ p0 := Finset.ne_of_mem_erase hp1'
  have hA2 : ((A1.erase p0).erase p1).card = A1.card - 2 := by
    rw [Finset.card_erase_of_mem hp1e, hA1]; omega
  obtain ⟨p2, hp2e⟩ := Finset.card_pos.mp
    (by omega : 0 < ((A1.erase p0).erase p1).card)
  have hp2' : p2 ∈ A1.erase p0 := Finset.mem_of_mem_erase hp2e
  have hp2 : p2 ∈ A1 := Finset.mem_of_mem_erase hp2'
  have hp21 : p2 ≠ p1 := Finset.ne_of_mem_erase hp2e
  have hp20 : p2 ≠ p0 := Finset.ne_of_mem_erase hp2'
  have hA3 : (((A1.erase p0).erase p1).erase p2).card = A1.card - 3 := by
    rw [Finset.card_erase_of_mem hp2e, hA2]; omega
  obtain ⟨p3, hp3e⟩ := Finset.card_pos.mp
    (by omega : 0 < (((A1.erase p0).erase p1).erase p2).card)
  have hp3'' : p3 ∈ (A1.erase p0).erase p1 := Finset.mem_of_mem_erase hp3e
  have hp3' : p3 ∈ A1.erase p0 := Finset.mem_of_mem_erase hp3''
  have hp3 : p3 ∈ A1 := Finset.mem_of_mem_erase hp3'
  have hp32 : p3 ≠ p2 := Finset.ne_of_mem_erase hp3e
  have hp31 : p3 ≠ p1 := Finset.ne_of_mem_erase hp3''
  have hp30 : p3 ≠ p0 := Finset.ne_of_mem_erase hp3'
  have hp01 : p0 ≠ p1 := hp10.symm
  have hp02 : p0 ≠ p2 := hp20.symm
  have hp03 : p0 ≠ p3 := hp30.symm
  have hp12 : p1 ≠ p2 := hp21.symm
  have hp13 : p1 ≠ p3 := hp31.symm
  have hp23 : p2 ≠ p3 := hp32.symm
  -- `same`-relations and the level symmetry of edges.
  have hrel : ∀ x y : ℕ, x ∈ A1 → y ∈ A1 → x ≠ y →
      residueRelOf x y = residueRel.same := fun x y hx hy hxy =>
    rel_same (by rw [hsame x hx, hsame y hy]) (ne_of_gt (hpos y hy))
  have hLs : ∀ x y : ℕ, x ∈ A1 → y ∈ A1 → x ≠ y →
      padicValNat 7 (eMod7 m x y) = padicValNat 7 (eMod7 m y x) :=
    fun x y hx hy hxy =>
      (enu7_sym (hrel x y hx hy hxy) (hrel y x hy hx hxy.symm)).symm
  -- Vertex-local uniformity ⇒ global uniformity (the edge-adjacency graph
  -- of `A1` is connected).
  by_cases huni : ∀ a ∈ A1, ∀ b ∈ A1, ∀ c ∈ A1,
      a ≠ b → a ≠ c → b ≠ c →
        padicValNat 7 (eMod7 m a b) = padicValNat 7 (eMod7 m a c)
  swap
  · -- Case (i): two edges at one vertex with different levels.
    push_neg at huni
    obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc, hne⟩ := huni
    have hsub3 : ({a, b, c} : Finset ℕ) ⊆ A1 := by
      intro x hx
      rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> assumption
    have hcard3 : ({a, b, c} : Finset ℕ).card = 3 := by
      rw [Finset.card_insert_of_notMem _, Finset.card_insert_of_notMem _,
        Finset.card_singleton]
      · rw [Finset.mem_singleton]; exact hbc
      · rw [Finset.mem_insert, Finset.mem_singleton]; push_neg; exact ⟨hab, hac⟩
    have hne4 : (A1 \ {a, b, c}).Nonempty := by
      rw [← Finset.card_pos, Finset.card_sdiff_of_subset hsub3, hcard3]
      omega
    obtain ⟨d4, hd4⟩ := hne4
    have hd4A : d4 ∈ A1 := (Finset.mem_sdiff.mp hd4).1
    have hd4nin : d4 ∉ ({a, b, c} : Finset ℕ) := (Finset.mem_sdiff.mp hd4).2
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hd4nin
    push_neg at hd4nin
    obtain ⟨hd4a, hd4b, hd4c⟩ := hd4nin
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact ⟨a, ha, c, hc, b, hb, d4, hd4A, hac, hab, hd4a.symm, hbc.symm,
        hd4c.symm, hd4b.symm, Or.inl (by
          rw [← enu7_sym (hrel c a hc ha hac.symm) (hrel a c ha hc hac),
            ← enu7_sym (hrel b a hb ha hab.symm) (hrel a b ha hb hab)]
          exact hlt)⟩
    · exact ⟨a, ha, b, hb, c, hc, d4, hd4A, hab, hac, hd4a.symm, hbc,
        hd4b.symm, hd4c.symm, Or.inl (by
          rw [← enu7_sym (hrel b a hb ha hab.symm) (hrel a b ha hb hab),
            ← enu7_sym (hrel c a hc ha hac.symm) (hrel a c ha hc hac)]
          exact hgt)⟩
  · -- Case (ii): all edge levels equal.
    have huni2 : ∀ x ∈ A1, ∀ y ∈ A1, ∀ u ∈ A1, ∀ v ∈ A1,
        x ≠ y → u ≠ v →
        padicValNat 7 (eMod7 m x y) = padicValNat 7 (eMod7 m u v) := by
      intro x hx y hy u hu v hv hxy huv
      rcases eq_or_ne x u with rfl | hxu
      · rcases eq_or_ne y v with rfl | hyv
        · rfl
        · exact huni x hx y hy v hv hxy huv hyv
      · rcases eq_or_ne x v with rfl | hxv
        · rcases eq_or_ne y u with rfl | hyu
          · exact hLs x y hx hy hxy
          · rw [huni x hx y hy u hu hxy hxu hyu]
            exact hLs x u hx hu hxu
        · rcases eq_or_ne y u with rfl | hyu
          · rw [hLs x y hx hy hxy]
            exact huni y hy x hx v hv hxy.symm huv hxv
          · rcases eq_or_ne y v with rfl | hyv
            · rw [hLs x y hx hy hxy, hLs u y hu hy huv]
              exact huni y hy x hx u hu hxy.symm hyu hxu
            · rw [huni x hx y hy u hu hxy hxu hyu, hLs x u hx hu hxu]
              exact huni u hu x hx v hv hxu.symm huv hxv
    set h := padicValNat 7 (eMod7 m p1 p0) with hh
    have hall : ∀ x ∈ A1, ∀ y ∈ A1, x ≠ y →
        padicValNat 7 (eMod7 m x y) = h := fun x hx y hy hxy =>
      huni2 x hx y hy p1 hp1 p0 hp0 hxy hp10
    by_cases hzero : ∀ x ∈ A1, ∀ y ∈ A1, x ≠ y → eMod7 m x y = 0
    · -- All pairs collide mod `7^{m+1}`: uniform condition vacuous, all
      -- units `0`, ratio pattern trivial.
      refine ⟨p0, hp0, p1, hp1, p2, hp2, p3, hp3,
        hp01, hp02, hp03, hp12, hp13, hp23, Or.inr ⟨0, ?_, ?_, ?_⟩⟩
      · intro x hx y hy hxy he
        exact absurd (hzero x hx y hy hxy) he
      · rw [hzero p2 hp2 p0 hp0 hp20, hzero p1 hp1 p0 hp0 hp10, runit7_zero,
          mul_zero]
      · left
        rw [hzero p3 hp3 p0 hp0 hp30, hzero p1 hp1 p0 hp0 hp10, runit7_zero,
          mul_zero]
    · push_neg at hzero
      obtain ⟨x0, hx0, y0, hy0, hxy0, he0⟩ := hzero
      -- `x0 ≡ y0 (mod 7)` (common runit `s`, level `0` elements), so the
      -- nonzero residue `e_{x0,y0}` is divisible by `7`: `h ≥ 1`.
      have hdiv7 : 7 ∣ eMod7 m x0 y0 := by
        have hcast : ((eMod7 m x0 y0 : ℕ) : ZMod 7)
            = (x0 : ZMod 7) - (y0 : ZMod 7) := by
          have hz := eMod7_zmod_cast_same (m := m) (hrel x0 y0 hx0 hy0 hxy0)
          have h7d : (7 : ℕ) ∣ 7 ^ (m + 1) := by simp
          have h2 := congrArg
            (ZMod.castHom h7d (ZMod 7)) hz
          simp only [map_natCast, map_sub] at h2
          exact h2
        have hx0' : (x0 : ZMod 7) = s := by
          have h := hsame x0 hx0
          unfold runit7 at h
          rwa [hunit x0 hx0, pow_zero, Nat.div_one] at h
        have hy0' : (y0 : ZMod 7) = s := by
          have h := hsame y0 hy0
          unfold runit7 at h
          rwa [hunit y0 hy0, pow_zero, Nat.div_one] at h
        rw [hx0', hy0', sub_self] at hcast
        exact (ZMod.natCast_eq_zero_iff _ _).mp hcast
      have hpos' : 0 < h := by
        rw [← hall x0 hx0 y0 hy0 hxy0]
        exact (Nat.pow_dvd_iff_le_padicValNat (by norm_num) he0).mp
          (by rwa [pow_one] : 7 ^ 1 ∣ eMod7 m x0 y0)
      -- Hence every edge is nonzero.
      have hne0 : ∀ x ∈ A1, ∀ y ∈ A1, x ≠ y → eMod7 m x y ≠ 0 := by
        intro x hx y hy hxy hcon
        have h1 := hall x hx y hy hxy
        rw [hcon, padicValNat_zero_right] at h1
        omega
      have hm : h ≤ m := by
        rw [← hall x0 hx0 y0 hy0 hxy0]
        exact enu7_le_of_ne he0
      -- edge levels and nonzero units
      have hν10 : padicValNat 7 (eMod7 m p1 p0) = h := hall p1 hp1 p0 hp0 hp10
      have hν20 : padicValNat 7 (eMod7 m p2 p0) = h := hall p2 hp2 p0 hp0 hp20
      have hν30 : padicValNat 7 (eMod7 m p3 p0) = h := hall p3 hp3 p0 hp0 hp30
      have hν12 : padicValNat 7 (eMod7 m p1 p2) = h := hall p1 hp1 p2 hp2 hp12
      have hν13 : padicValNat 7 (eMod7 m p1 p3) = h := hall p1 hp1 p3 hp3 hp13
      have hν23 : padicValNat 7 (eMod7 m p2 p3) = h := hall p2 hp2 p3 hp3 hp23
      set w1 := runit7 (eMod7 m p1 p0) with hw1
      set w2 := runit7 (eMod7 m p2 p0) with hw2
      set w3 := runit7 (eMod7 m p3 p0) with hw3
      have hw1n : w1 ≠ 0 := by
        rw [hw1]; exact runit7_ne_zero
          (Nat.pos_of_ne_zero (hne0 p1 hp1 p0 hp0 hp10))
      have hw2n : w2 ≠ 0 := by
        rw [hw2]; exact runit7_ne_zero
          (Nat.pos_of_ne_zero (hne0 p2 hp2 p0 hp0 hp20))
      have hw3n : w3 ≠ 0 := by
        rw [hw3]; exact runit7_ne_zero
          (Nat.pos_of_ne_zero (hne0 p3 hp3 p0 hp0 hp30))
      have hw12 : w1 ≠ w2 := by
        intro heq
        rcases eMod7_level_gt_of_runit_eq
            (hrel p1 p0 hp1 hp0 hp10) (hrel p2 p0 hp2 hp0 hp20)
            (hrel p1 p2 hp1 hp2 hp12)
            (hne0 p1 hp1 p0 hp0 hp10) (hne0 p2 hp2 p0 hp0 hp20)
            hν10 hν20 hm heq with h0 | hgt
        · exact hne0 p1 hp1 p2 hp2 hp12 h0
        · rw [hν12] at hgt; omega
      have hw13 : w1 ≠ w3 := by
        intro heq
        rcases eMod7_level_gt_of_runit_eq
            (hrel p1 p0 hp1 hp0 hp10) (hrel p3 p0 hp3 hp0 hp30)
            (hrel p1 p3 hp1 hp3 hp13)
            (hne0 p1 hp1 p0 hp0 hp10) (hne0 p3 hp3 p0 hp0 hp30)
            hν10 hν30 hm heq with h0 | hgt
        · exact hne0 p1 hp1 p3 hp3 hp13 h0
        · rw [hν13] at hgt; omega
      have hw23 : w2 ≠ w3 := by
        intro heq
        rcases eMod7_level_gt_of_runit_eq
            (hrel p2 p0 hp2 hp0 hp20) (hrel p3 p0 hp3 hp0 hp30)
            (hrel p2 p3 hp2 hp3 hp23)
            (hne0 p2 hp2 p0 hp0 hp20) (hne0 p3 hp3 p0 hp0 hp30)
            hν20 hν30 hm heq with h0 | hgt
        · exact hne0 p2 hp2 p3 hp3 hp23 h0
        · rw [hν23] at hgt; omega
      -- the cocycle: `r(e_{p_i,p_j}) = w_i − w_j`, `r(e_{p_0,p_i}) = −w_i`
      have u10 : runit7 (eMod7 m p1 p0) = w1 := hw1.symm
      have u20 : runit7 (eMod7 m p2 p0) = w2 := hw2.symm
      have u30 : runit7 (eMod7 m p3 p0) = w3 := hw3.symm
      have u12 : runit7 (eMod7 m p1 p2) = w1 - w2 :=
        (eMod7_level_of_runit_ne (hrel p1 p0 hp1 hp0 hp10)
          (hrel p2 p0 hp2 hp0 hp20) (hrel p1 p2 hp1 hp2 hp12)
          (hne0 p1 hp1 p0 hp0 hp10) (hne0 p2 hp2 p0 hp0 hp20)
          hν10 hν20 hm hw12).2.2
      have u21 : runit7 (eMod7 m p2 p1) = w2 - w1 :=
        (eMod7_level_of_runit_ne (hrel p2 p0 hp2 hp0 hp20)
          (hrel p1 p0 hp1 hp0 hp10) (hrel p2 p1 hp2 hp1 hp21)
          (hne0 p2 hp2 p0 hp0 hp20) (hne0 p1 hp1 p0 hp0 hp10)
          hν20 hν10 hm (Ne.symm hw12)).2.2
      have u13 : runit7 (eMod7 m p1 p3) = w1 - w3 :=
        (eMod7_level_of_runit_ne (hrel p1 p0 hp1 hp0 hp10)
          (hrel p3 p0 hp3 hp0 hp30) (hrel p1 p3 hp1 hp3 hp13)
          (hne0 p1 hp1 p0 hp0 hp10) (hne0 p3 hp3 p0 hp0 hp30)
          hν10 hν30 hm hw13).2.2
      have u31 : runit7 (eMod7 m p3 p1) = w3 - w1 :=
        (eMod7_level_of_runit_ne (hrel p3 p0 hp3 hp0 hp30)
          (hrel p1 p0 hp1 hp0 hp10) (hrel p3 p1 hp3 hp1 hp31)
          (hne0 p3 hp3 p0 hp0 hp30) (hne0 p1 hp1 p0 hp0 hp10)
          hν30 hν10 hm (Ne.symm hw13)).2.2
      have u23 : runit7 (eMod7 m p2 p3) = w2 - w3 :=
        (eMod7_level_of_runit_ne (hrel p2 p0 hp2 hp0 hp20)
          (hrel p3 p0 hp3 hp0 hp30) (hrel p2 p3 hp2 hp3 hp23)
          (hne0 p2 hp2 p0 hp0 hp20) (hne0 p3 hp3 p0 hp0 hp30)
          hν20 hν30 hm hw23).2.2
      have u32 : runit7 (eMod7 m p3 p2) = w3 - w2 :=
        (eMod7_level_of_runit_ne (hrel p3 p0 hp3 hp0 hp30)
          (hrel p2 p0 hp2 hp0 hp20) (hrel p3 p2 hp3 hp2 hp32)
          (hne0 p3 hp3 p0 hp0 hp30) (hne0 p2 hp2 p0 hp0 hp20)
          hν30 hν20 hm (Ne.symm hw23)).2.2
      have u01 : runit7 (eMod7 m p0 p1) = -w1 := by
        rw [hw1]; exact runit7_eMod7_neg (hrel p1 p0 hp1 hp0 hp10)
          (hrel p0 p1 hp0 hp1 hp01)
      have u02 : runit7 (eMod7 m p0 p2) = -w2 := by
        rw [hw2]; exact runit7_eMod7_neg (hrel p2 p0 hp2 hp0 hp20)
          (hrel p0 p2 hp0 hp2 hp02)
      have u03 : runit7 (eMod7 m p0 p3) = -w3 := by
        rw [hw3]; exact runit7_eMod7_neg (hrel p3 p0 hp3 hp0 hp30)
          (hrel p0 p3 hp0 hp3 hp03)
      have huniform : ∀ x ∈ A1, ∀ y ∈ A1, x ≠ y → eMod7 m x y ≠ 0 →
          padicValNat 7 (eMod7 m x y) = h :=
        fun x hx y hy hxy _ => hall x hx y hy hxy
      obtain hd := lemma10_units w1 w2 w3 hw1n hw2n hw3n hw12 hw13 hw23
      rcases hd with hd | hd | hd | hd | hd | hd | hd | hd | hd | hd | hd | hd
        | hd | hd | hd | hd | hd | hd | hd | hd | hd | hd | hd | hd
      · -- perm (0,1,2,3)
        refine ⟨p0, hp0, p1, hp1, p2, hp2, p3, hp3,
          hp01, hp02, hp03, hp12, hp13, hp23, Or.inr ⟨h, huniform, ?_, ?_⟩⟩
        · rw [u20, u10]; exact hd.1
        · rw [u30, u10]; exact hd.2
      · -- perm (0,1,3,2)
        refine ⟨p0, hp0, p1, hp1, p3, hp3, p2, hp2,
          hp01, hp03, hp02, hp13, hp12, hp32, Or.inr ⟨h, huniform, ?_, ?_⟩⟩
        · rw [u30, u10]; exact hd.1
        · rw [u20, u10]; exact hd.2
      · -- perm (0,2,1,3)
        refine ⟨p0, hp0, p2, hp2, p1, hp1, p3, hp3,
          hp02, hp01, hp03, hp21, hp23, hp13, Or.inr ⟨h, huniform, ?_, ?_⟩⟩
        · rw [u10, u20]; exact hd.1
        · rw [u30, u20]; exact hd.2
      · -- perm (0,2,3,1)
        refine ⟨p0, hp0, p2, hp2, p3, hp3, p1, hp1,
          hp02, hp03, hp01, hp23, hp21, hp31, Or.inr ⟨h, huniform, ?_, ?_⟩⟩
        · rw [u30, u20]; exact hd.1
        · rw [u10, u20]; exact hd.2
      · -- perm (0,3,1,2)
        refine ⟨p0, hp0, p3, hp3, p1, hp1, p2, hp2,
          hp03, hp01, hp02, hp31, hp32, hp12, Or.inr ⟨h, huniform, ?_, ?_⟩⟩
        · rw [u10, u30]; exact hd.1
        · rw [u20, u30]; exact hd.2
      · -- perm (0,3,2,1)
        refine ⟨p0, hp0, p3, hp3, p2, hp2, p1, hp1,
          hp03, hp02, hp01, hp32, hp31, hp21, Or.inr ⟨h, huniform, ?_, ?_⟩⟩
        · rw [u20, u30]; exact hd.1
        · rw [u10, u30]; exact hd.2
      · -- perm (1,0,2,3): r(e_{p2,p1}) = 2·r(e_{p0,p1}) etc.
        refine ⟨p1, hp1, p0, hp0, p2, hp2, p3, hp3,
          hp10, hp12, hp13, hp02, hp03, hp23, Or.inr ⟨h, huniform, ?_, ?_⟩⟩
        · rw [u21, u01]; exact hd.1
        · rw [u31, u01]; exact hd.2
      · -- perm (1,0,3,2)
        refine ⟨p1, hp1, p0, hp0, p3, hp3, p2, hp2,
          hp10, hp13, hp12, hp03, hp02, hp32, Or.inr ⟨h, huniform, ?_, ?_⟩⟩
        · rw [u31, u01]; exact hd.1
        · rw [u21, u01]; exact hd.2
      · -- perm (1,2,0,3)
        refine ⟨p1, hp1, p2, hp2, p0, hp0, p3, hp3,
          hp12, hp10, hp13, hp20, hp23, hp03, Or.inr ⟨h, huniform, ?_, ?_⟩⟩
        · rw [u01, u21]; exact hd.1
        · rw [u31, u21]; exact hd.2
      · -- perm (1,2,3,0)
        refine ⟨p1, hp1, p2, hp2, p3, hp3, p0, hp0,
          hp12, hp13, hp10, hp23, hp20, hp30, Or.inr ⟨h, huniform, ?_, ?_⟩⟩
        · rw [u31, u21]; exact hd.1
        · rw [u01, u21]; exact hd.2
      · -- perm (1,3,0,2)
        refine ⟨p1, hp1, p3, hp3, p0, hp0, p2, hp2,
          hp13, hp10, hp12, hp30, hp32, hp02, Or.inr ⟨h, huniform, ?_, ?_⟩⟩
        · rw [u01, u31]; exact hd.1
        · rw [u21, u31]; exact hd.2
      · -- perm (1,3,2,0)
        refine ⟨p1, hp1, p3, hp3, p2, hp2, p0, hp0,
          hp13, hp12, hp10, hp32, hp30, hp20, Or.inr ⟨h, huniform, ?_, ?_⟩⟩
        · rw [u21, u31]; exact hd.1
        · rw [u01, u31]; exact hd.2
      · -- perm (2,0,1,3)
        refine ⟨p2, hp2, p0, hp0, p1, hp1, p3, hp3,
          hp20, hp21, hp23, hp01, hp03, hp13, Or.inr ⟨h, huniform, ?_, ?_⟩⟩
        · rw [u12, u02]; exact hd.1
        · rw [u32, u02]; exact hd.2
      · -- perm (2,0,3,1)
        refine ⟨p2, hp2, p0, hp0, p3, hp3, p1, hp1,
          hp20, hp23, hp21, hp03, hp01, hp31, Or.inr ⟨h, huniform, ?_, ?_⟩⟩
        · rw [u32, u02]; exact hd.1
        · rw [u12, u02]; exact hd.2
      · -- perm (2,1,0,3)
        refine ⟨p2, hp2, p1, hp1, p0, hp0, p3, hp3,
          hp21, hp20, hp23, hp10, hp13, hp03, Or.inr ⟨h, huniform, ?_, ?_⟩⟩
        · rw [u02, u12]; exact hd.1
        · rw [u32, u12]; exact hd.2
      · -- perm (2,1,3,0)
        refine ⟨p2, hp2, p1, hp1, p3, hp3, p0, hp0,
          hp21, hp23, hp20, hp13, hp10, hp30, Or.inr ⟨h, huniform, ?_, ?_⟩⟩
        · rw [u32, u12]; exact hd.1
        · rw [u02, u12]; exact hd.2
      · -- perm (2,3,0,1)
        refine ⟨p2, hp2, p3, hp3, p0, hp0, p1, hp1,
          hp23, hp20, hp21, hp30, hp31, hp01, Or.inr ⟨h, huniform, ?_, ?_⟩⟩
        · rw [u02, u32]; exact hd.1
        · rw [u12, u32]; exact hd.2
      · -- perm (2,3,1,0)
        refine ⟨p2, hp2, p3, hp3, p1, hp1, p0, hp0,
          hp23, hp21, hp20, hp31, hp30, hp10, Or.inr ⟨h, huniform, ?_, ?_⟩⟩
        · rw [u12, u32]; exact hd.1
        · rw [u02, u32]; exact hd.2
      · -- perm (3,0,1,2)
        refine ⟨p3, hp3, p0, hp0, p1, hp1, p2, hp2,
          hp30, hp31, hp32, hp01, hp02, hp12, Or.inr ⟨h, huniform, ?_, ?_⟩⟩
        · rw [u13, u03]; exact hd.1
        · rw [u23, u03]; exact hd.2
      · -- perm (3,0,2,1)
        refine ⟨p3, hp3, p0, hp0, p2, hp2, p1, hp1,
          hp30, hp32, hp31, hp02, hp01, hp21, Or.inr ⟨h, huniform, ?_, ?_⟩⟩
        · rw [u23, u03]; exact hd.1
        · rw [u13, u03]; exact hd.2
      · -- perm (3,1,0,2)
        refine ⟨p3, hp3, p1, hp1, p0, hp0, p2, hp2,
          hp31, hp30, hp32, hp10, hp12, hp02, Or.inr ⟨h, huniform, ?_, ?_⟩⟩
        · rw [u03, u13]; exact hd.1
        · rw [u23, u13]; exact hd.2
      · -- perm (3,1,2,0)
        refine ⟨p3, hp3, p1, hp1, p2, hp2, p0, hp0,
          hp31, hp32, hp30, hp12, hp10, hp20, Or.inr ⟨h, huniform, ?_, ?_⟩⟩
        · rw [u23, u13]; exact hd.1
        · rw [u03, u13]; exact hd.2
      · -- perm (3,2,0,1)
        refine ⟨p3, hp3, p2, hp2, p0, hp0, p1, hp1,
          hp32, hp30, hp31, hp20, hp21, hp01, Or.inr ⟨h, huniform, ?_, ?_⟩⟩
        · rw [u03, u23]; exact hd.1
        · rw [u13, u23]; exact hd.2
      · -- perm (3,2,1,0)
        refine ⟨p3, hp3, p2, hp2, p1, hp1, p0, hp0,
          hp32, hp31, hp30, hp21, hp20, hp10, Or.inr ⟨h, huniform, ?_, ?_⟩⟩
        · rw [u13, u23]; exact hd.1
        · rw [u03, u23]; exact hd.2

/-! ### §5 Lemma 9(ii) — helpers -/

/-- `q`-digit of a `ZMod N`-difference `w ≡ A − B` (`qdig_smul_eMod_eq`
at `lam = 1`). -/
private theorem qdig7_of_sub_cast {m w A B : ℕ}
    (hcast : ((w : ℕ) : ZMod (7 ^ (m + 1))) = (A : ZMod _) - (B : ZMod _)) :
    qdig7 m w = qdig7 m A - qdig7 m B
      - if A % 7 ^ m < B % 7 ^ m then (1 : ZMod 7) else 0 := by
  have h := qdig_smul_eMod_eq (m := m) (lam := 1) (e := w) (A := A) (B := B)
    (by simpa using hcast)
  rwa [one_mul] at h

/-- `q(7^m) = 1`. -/
private theorem qdig7_pow_self (m : ℕ) : qdig7 m (7 ^ m) = 1 := by
  unfold qdig7
  rw [Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self m))]
  rw [Nat.div_self (Nat.pow_pos (by norm_num) : 0 < 7 ^ m)]
  exact Nat.cast_one

/-- A `Λ_j`-multiplier preserves the `mod 7^m` part of a `7^j`-divisible
element (`7^{m−j}·w` is a multiple of `7^m`). -/
private theorem multLow_low {m j k w : ℕ} (hjm : j ≤ m) (hw : 7 ^ j ∣ w) :
    ((1 + k * 7 ^ (m - j)) * w) % 7 ^ m = w % 7 ^ m := by
  obtain ⟨u, rfl⟩ := hw
  rw [add_mul, one_mul]
  have hP : k * 7 ^ (m - j) * (7 ^ j * u) = 7 ^ m * (k * u) := by
    have e : k * 7 ^ (m - j) * (7 ^ j * u) = k * u * (7 ^ (m - j) * 7 ^ j) := by
      ring
    rw [e, ← pow_add, Nat.sub_add_cancel hjm]
    ring
  rw [hP, Nat.add_mul_mod_self_left]

/-- A `ZMod 7` element of `val < 2` is `0` or `1`. -/
private theorem zmod7_of_val_lt_two {s : ZMod 7} (h : s.val < 2) :
    s = 0 ∨ s = 1 := by
  have hv : s.val = 0 ∨ s.val = 1 := by omega
  rcases hv with h0 | h1
  · refine Or.inl ?_
    rw [← ZMod.natCast_zmod_val s, h0]
    exact Nat.cast_zero
  · refine Or.inr ?_
    rw [← ZMod.natCast_zmod_val s, h1]
    exact Nat.cast_one

/-- Negation preserves `{0,1,6} ⊆ ZMod 7`. -/
private theorem neg_mem_016 {s : ZMod 7}
    (h : s ∈ ({0, 1, 6} : Finset (ZMod 7))) :
    -s ∈ ({0, 1, 6} : Finset (ZMod 7)) := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at h ⊢
  rcases h with rfl | rfl | rfl <;> decide

/-- `−s − 1` for `s ∈ {0,1,5,6}` stays in `{0,1,5,6}` (`{6,5,1,0}`). -/
private theorem neg_sub_one_mem_0156 {s : ZMod 7}
    (h : s ∈ ({0, 1, 5, 6} : Finset (ZMod 7))) :
    -s - 1 ∈ ({0, 1, 5, 6} : Finset (ZMod 7)) := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at h ⊢
  rcases h with rfl | rfl | rfl | rfl <;> decide

/-- `−s − 1` for `s ∈ {0,5,6}` stays in `{0,1,5,6}` (`{6,1,0}`). -/
private theorem neg_sub_one_mem_056 {s : ZMod 7}
    (h : s ∈ ({0, 5, 6} : Finset (ZMod 7))) :
    -s - 1 ∈ ({0, 1, 5, 6} : Finset (ZMod 7)) := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at h ⊢
  rcases h with rfl | rfl | rfl <;> decide

/-- `−s − 1` for `s ∈ {0,6}` stays in `{0,6}` (`{6,0}`). -/
private theorem neg_sub_one_mem_06 {s : ZMod 7}
    (h : s ∈ ({0, 6} : Finset (ZMod 7))) :
    -s - 1 ∈ ({0, 6} : Finset (ZMod 7)) := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at h ⊢
  rcases h with rfl | rfl <;> decide

/-- `s − δ` for `s ∈ {0,1,6}`, `δ ∈ {0,1}` stays in `{0,1,5,6}`. -/
private theorem sub_borrow_mem_0156 {s d : ZMod 7}
    (hs : s ∈ ({0, 1, 6} : Finset (ZMod 7))) (hd : d = 0 ∨ d = 1) :
    s - d ∈ ({0, 1, 5, 6} : Finset (ZMod 7)) := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hs ⊢
  rcases hs with rfl | rfl | rfl <;> rcases hd with rfl | rfl <;> decide

/-- `etd7` on a `twoX` pair (`r(v) = 2r(u)`). -/
private theorem etd7_eq_twoX {m u v : ℕ} (h : runit7 v = 2 * runit7 u) :
    etd7 m u v = 2 * qdig7 m u - qdig7 m v := by
  unfold etd7
  rw [if_pos h]

/-- **Pure-block `ẽ`-bound**: `e(u,v) = 7^m` forces `ẽ = 2q(u) − q(v) ∈ {0,1}`.
`v ≡ 2u − 7^m` gives `q(v) = q(2u) − 1` (the `B % 7^m = 0` borrow vanishes);
the carry bound `q(2u) − 2q(u) ∈ {0,1}` finishes `ẽ = 1 − γ ∈ {0,1}`. -/
private theorem etd7_of_pure_block {m u v : ℕ}
    (hrel : runit7 v = 2 * runit7 u) (he : eMod7 m u v = 7 ^ m) :
    etd7 m u v ∈ ({0, 1} : Finset (ZMod 7)) := by
  have hcast : ((v : ℕ) : ZMod (7 ^ (m + 1)))
      = ((2 * u : ℕ) : ZMod _) - ((7 ^ m : ℕ) : ZMod _) := by
    have h1 : ((eMod7 m u v : ℕ) : ZMod (7 ^ (m + 1)))
        = 2 * (u : ZMod _) - (v : ZMod _) := by
      rw [eMod7_zmod_cast, if_pos hrel]
    rw [he] at h1
    push_cast at h1 ⊢
    linear_combination h1
  have hqv : qdig7 m v = qdig7 m (2 * u) - 1 := by
    have h := qdig7_of_sub_cast (m := m) (w := v) (A := 2 * u) (B := 7 ^ m) hcast
    rw [qdig7_pow_self] at h
    have hδ : ¬ 2 * u % 7 ^ m < (7 ^ m) % 7 ^ m := by
      rw [Nat.mod_self]
      exact Nat.not_lt_zero _
    rw [if_neg hδ] at h
    simpa using h
  have hcarry := qdig7_smul_carry (m := m) (c := 2) (x := u) (by norm_num)
    (by norm_num)
  rw [etd7_eq_twoX hrel, hqv]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  rcases zmod7_of_val_lt_two hcarry with hγ | hγ
  · have hq2 : qdig7 m (2 * u) = 2 * qdig7 m u := eq_of_sub_eq_zero hγ
    rw [hq2]
    right
    ring
  · have hq2 : qdig7 m (2 * u) = 2 * qdig7 m u + 1 := by
      have h := sub_eq_iff_eq_add.mp hγ
      rwa [add_comm] at h
    rw [hq2]
    left
    ring

/-- The `j = 3` multiplier table: for all `qx qy : ZMod 7` some
`t ∈ {0,5,6}` gives `q(λx) = qx + 2qy + 5t ∈ {0,1,5,6}` and
`q(λx) − q(λy) = qx + 2qy + 4t ∈ {0,1,6}` (the `u = 5(t − qy)` shift of
`qdig7_multLow`). -/
private theorem lemma9_ii_table3 :
    ∀ qx qy : ZMod 7, ∃ t : ZMod 7,
      t ∈ ({0, 5, 6} : Finset (ZMod 7)) ∧
      (qx + 2 * qy + 5 * t) ∈ ({0, 1, 5, 6} : Finset (ZMod 7)) ∧
      (qx + 2 * qy + 4 * t) ∈ ({0, 1, 6} : Finset (ZMod 7)) := by
  decide

/-- `apLen ≤ 3` when all pairwise differences lie in `{0,±1,±2}`
(`{0,1,2,5,6}`) — the `remark8_ii` variant used by `lemma9_ii` (`j=3`),
whose residue-digit condition only yields `{0,1,5,6}+{0,1}`. -/
private theorem remark8_ii'_dec :
    ∀ B : Finset (ZMod 7),
      (∀ x ∈ B, ∀ y ∈ B, x - y ∈ ({0, 1, 2, 5, 6} : Finset (ZMod 7))) →
      apLen B ≤ 3 := by
  set_option maxRecDepth 16384 in
  decide

private theorem remark8_ii' {B : Finset (ZMod 7)}
    (hB : ∀ x ∈ B, ∀ y ∈ B, x - y ∈ ({0, 1, 2, 5, 6} : Finset (ZMod 7))) :
    apLen B ≤ 3 := remark8_ii'_dec B hB

/-- Bridge for `remark8_ii'` (`lemma9_ii` `j = 3` route): pair-residue
digits in `{0,1,5,6}` yield `q`-differences in `{0,1,2,5,6}` via
`qdig_eMod_sub` (`q(e) − (qx−qy) ∈ {0,6}`). -/
private theorem remark8_ii_int {m : ℕ} {B : Finset ℕ}
    (hsame : ∀ x ∈ B, ∀ y ∈ B, residueRelOf x y = residueRel.same)
    (hB : ∀ x ∈ B, ∀ y ∈ B,
      qdig7 m (eMod7 m x y) ∈ ({0, 1, 5, 6} : Finset (ZMod 7))) :
    ∀ a ∈ B.image (qdig7 m), ∀ b ∈ B.image (qdig7 m),
      a - b ∈ ({0, 1, 2, 5, 6} : Finset (ZMod 7)) := by
  intro a ha b hb
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hb
  have hsame' := hsame x hx y hy
  have hsub := qdig_eMod_sub (m := m) hsame'
  have hq := hB x hx y hy
  simp only [Finset.mem_insert, Finset.mem_singleton] at hq hsub ⊢
  rcases hq with hq | hq | hq | hq <;> rcases hsub with hsub | hsub <;>
    rw [hq] at hsub <;>
    (have e : qdig7 m x - qdig7 m y
        = qdig7 m (eMod7 m x y)
          - (qdig7 m (eMod7 m x y) - (qdig7 m x - qdig7 m y)) := by ring
     rw [e, hq, hsub]
     decide)

/-- **Lemma 9(ii)** (paper §3.5): three unit-multiples `b₁,b₂,b₃` of `x`
with `r(b₁) = r(b₂) = r(b₃)`, equal levels `h := ν(e(b₁,b₃)) = ν(e(b₂,b₃))
< m`, and residue ratio `r(e₂₃) = j·r(e₁₃)` with `j ∈ {2,3}` admit a `Λ`
multiplier with `q(e(λb₂,λb₃)) ∈ {0,5,6}` and `apLen (q(λB)) ≤ j`.

* `j = 3`: a single `Λ_h` multiplier `1 + k·7^{m−h}`; the digit table
  `lemma9_ii_table3` puts `q(λy) ∈ {0,5,6}`, `q(λx) ∈ {0,1,5,6}` and
  `q(λ(x−y)) ∈ {0,1,6}` (`u = 5·(t−q(y))` shift), all pair-digits in
  `{0,1,5,6}`, hence `q`-differences in `{0,±1,±2}` (`remark8_ii'`).
* `j = 2`: two-stage — a first unit `λ₁ ∈ {1, c, Λ_{ν(E)}}`
  (`exists_top_scalar_set`/`exists_multLow_set_qdig` on `E := e(x,y)`)
  normalizes `q(λ₁E) ∈ {0,1}` with `ẽ₁ := 2q(λ₁x) − q(λ₁y) ∈ {0,1,6}`
  (pure-block `q(λ₁E) = 1` forces `ẽ₁ ∈ {0,1}`); then `Λ_h` sets
  `q(λx) = c_x ∈ {0,6}` with `c_x = 0` unless `ẽ₁ = 6`.  Every pair then
  evaluates via `eval` to `{0,6}`, giving `apLen ≤ 2` (`remark8_i`).
* `x = 0` (hence `y = 0`): all residues vanish, `λ = 1`. -/
private theorem subset0156_06 :
    ({0, 6} : Finset (ZMod 7)) ⊆ ({0, 1, 5, 6} : Finset (ZMod 7)) := by
  decide

theorem lemma9_ii {m : ℕ} {b1 b2 b3 : ℕ}
    (hpos : 0 < b1 ∧ 0 < b2 ∧ 0 < b3)
    (_hunit : padicValNat 7 b1 = 0 ∧
      padicValNat 7 b2 = 0 ∧
      padicValNat 7 b3 = 0)
    (hsame : runit7 b1 = runit7 b2 ∧
      runit7 b2 = runit7 b3)
    (h : padicValNat 7 (eMod7 m b1 b3) =
      padicValNat 7 (eMod7 m b2 b3))
    (hm' : padicValNat 7 (eMod7 m b2 b3) < m)
    {j : ℕ} (hj : j = 2 ∨ j = 3)
    (hr : runit7 (eMod7 m b2 b3) =
      (j : ZMod 7) * runit7 (eMod7 m b1 b3)) :
    ∃ lam : ℕ, ¬ 7 ∣ lam ∧
      qdig7 m (eMod7 m (lam*b2) (lam*b3)) ∈
        ({0,5,6} : Finset (ZMod 7)) ∧
      (∀ x ∈ ({b1,b2,b3} : Finset ℕ), ∀ y ∈ ({b1,b2,b3} : Finset ℕ),
        qdig7 m (eMod7 m (lam*x) (lam*y)) ∈
          ({0,1,5,6} : Finset (ZMod 7))) ∧
      (j = 2 → ∀ x ∈ ({b1,b2,b3} : Finset ℕ), ∀ y ∈ ({b1,b2,b3} : Finset ℕ),
        qdig7 m (eMod7 m (lam*x) (lam*y)) ∈
          ({0,6} : Finset (ZMod 7))) ∧
      apLen (({b1,b2,b3} : Finset ℕ).image
        (fun d => qdig7 m (lam*d))) ≤ j := by
  classical
  set x := eMod7 m b1 b3 with hx
  set y := eMod7 m b2 b3 with hy
  have hb1 : b1 ∈ ({b1, b2, b3} : Finset ℕ) := by simp
  have hb2 : b2 ∈ ({b1, b2, b3} : Finset ℕ) := by simp
  have hb3 : b3 ∈ ({b1, b2, b3} : Finset ℕ) := by simp
  have hposB : ∀ d ∈ ({b1, b2, b3} : Finset ℕ), 0 < d := by
    intro d hd
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl | rfl
    · exact hpos.1
    · exact hpos.2.1
    · exact hpos.2.2
  have hr_all : ∀ d ∈ ({b1, b2, b3} : Finset ℕ), runit7 d = runit7 b3 := by
    intro d hd
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl | rfl
    · exact hsame.1.trans hsame.2
    · exact hsame.2
    · rfl
  have hsameB : ∀ u ∈ ({b1, b2, b3} : Finset ℕ),
      ∀ v ∈ ({b1, b2, b3} : Finset ℕ),
      residueRelOf u v = residueRel.same := fun u hu v hv =>
    rel_same ((hr_all u hu).trans (hr_all v hv).symm) (ne_of_gt (hposB v hv))
  -- ZMod-N casts of the four off-diagonal residues
  have hc12 : ((eMod7 m b1 b2 : ℕ) : ZMod (7 ^ (m + 1)))
      = (x : ZMod _) - (y : ZMod _) :=
    eMod7_cast_sub (hsameB b1 hb1 b3 hb3) (hsameB b2 hb2 b3 hb3)
      (hsameB b1 hb1 b2 hb2)
  have hc21 : ((eMod7 m b2 b1 : ℕ) : ZMod (7 ^ (m + 1)))
      = (y : ZMod _) - (x : ZMod _) :=
    eMod7_cast_sub (hsameB b2 hb2 b3 hb3) (hsameB b1 hb1 b3 hb3)
      (hsameB b2 hb2 b1 hb1)
  have hc31 : ((eMod7 m b3 b1 : ℕ) : ZMod (7 ^ (m + 1)))
      = -(x : ZMod _) := by
    have hh := eMod7_cast_sub (m := m) (hsameB b3 hb3 b3 hb3)
      (hsameB b1 hb1 b3 hb3) (hsameB b3 hb3 b1 hb1)
    rw [eMod7_self] at hh
    rwa [Nat.cast_zero, zero_sub] at hh
  have hc32 : ((eMod7 m b3 b2 : ℕ) : ZMod (7 ^ (m + 1)))
      = -(y : ZMod _) := by
    have hh := eMod7_cast_sub (m := m) (hsameB b3 hb3 b3 hb3)
      (hsameB b2 hb2 b3 hb3) (hsameB b3 hb3 b2 hb2)
    rw [eMod7_self] at hh
    rwa [Nat.cast_zero, zero_sub] at hh
  rcases eq_or_ne x 0 with hx0 | hx0
  · -- x = 0 ⇒ r(y) = j·r(x) = 0 ⇒ y = 0: all residues vanish, λ = 1
    have hy0 : y = 0 := by
      by_contra hne
      have hry : runit7 y ≠ 0 := runit7_ne_zero (Nat.pos_of_ne_zero hne)
      rw [hx0, runit7_zero] at hr
      simp at hr
      exact hry hr
    have hAll03 : ∀ u ∈ ({b1, b2, b3} : Finset ℕ), eMod7 m u b3 = 0 := by
      intro u hu
      rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with h | h | h
      · rw [h]; exact hx0
      · rw [h]; exact hy0
      · rw [h]; exact eMod7_self _ _
    have hAll0 : ∀ u ∈ ({b1, b2, b3} : Finset ℕ),
        ∀ v ∈ ({b1, b2, b3} : Finset ℕ), eMod7 m u v = 0 := by
      intro u hu v hv
      rw [eMod7_sub_eq (hsameB u hu b3 hb3) (hsameB v hv b3 hb3)
          (hsameB u hu v hv),
        hAll03 u hu, hAll03 v hv, Nat.zero_add, Nat.sub_zero, Nat.mod_self]
    refine ⟨1, by decide, ?_, ?_, ?_, ?_⟩
    · rw [eMod7_smul (runit7_ne_zero (by norm_num : (0 : ℕ) < 1)),
        hAll0 b2 hb2 b3 hb3, one_mul, Nat.zero_mod, qdig7_zero]
      exact Finset.mem_insert_self _ _
    · intro x' hx' y' hy'
      rw [eMod7_smul (runit7_ne_zero (by norm_num : (0 : ℕ) < 1)),
        hAll0 x' hx' y' hy', one_mul, Nat.zero_mod, qdig7_zero]
      exact Finset.mem_insert_self _ _
    · intro _ x' hx' y' hy'
      rw [eMod7_smul (runit7_ne_zero (by norm_num : (0 : ℕ) < 1)),
        hAll0 x' hx' y' hy', one_mul, Nat.zero_mod, qdig7_zero]
      exact Finset.mem_insert_self _ _
    · set BL : Finset ℕ := ({b1, b2, b3} : Finset ℕ).image (1 * ·)
        with hBLdef
      have hBLsame : ∀ u ∈ BL, ∀ v ∈ BL,
          residueRelOf u v = residueRel.same := by
        intro u hu v hv
        obtain ⟨u', hu', rfl⟩ := Finset.mem_image.mp hu
        obtain ⟨v', hv', rfl⟩ := Finset.mem_image.mp hv
        apply rel_same _
          (mul_ne_zero (by norm_num : (1 : ℕ) ≠ 0) (ne_of_gt (hposB v' hv')))
        rw [runit7_mul, runit7_mul,
          runit7_eq_one_of_mod7 (by norm_num : (1 : ℕ) % 7 = 1), one_mul,
          one_mul, hr_all u' hu', hr_all v' hv']
      have hBL : ∀ u ∈ BL, ∀ v ∈ BL,
          qdig7 m (eMod7 m u v) ∈ ({0, 6} : Finset (ZMod 7)) := by
        intro u hu v hv
        obtain ⟨u', hu', rfl⟩ := Finset.mem_image.mp hu
        obtain ⟨v', hv', rfl⟩ := Finset.mem_image.mp hv
        rw [eMod7_smul (runit7_ne_zero (by norm_num : (0 : ℕ) < 1)),
          hAll0 u' hu' v' hv', one_mul, Nat.zero_mod, qdig7_zero]
        exact Finset.mem_insert_self _ _
      have hdiff := remark8_i_int hBLsame hBL
      have hlen : apLen (BL.image (qdig7 m)) ≤ 2 := by
        have hh := remark8_i hdiff (k := 1) (by decide)
        simp only [mul_one] at hh
        rw [Finset.image_id'] at hh
        have h1 : (1 : ZMod 7).val = 1 := by decide
        rw [h1] at hh
        exact hh
      have himg : BL.image (qdig7 m)
          = ({b1, b2, b3} : Finset ℕ).image (fun d => qdig7 m (1 * d)) := by
        rw [hBLdef, Finset.image_image]
        exact Finset.image_congr fun d _ => rfl
      rw [himg] at hlen
      exact hlen.trans (by rcases hj with rfl | rfl <;> decide)
  · -- x ≠ 0 ⇒ y ≠ 0 (j·r(x) ≠ 0 for j ∈ {2,3})
    have hy0 : y ≠ 0 := by
      intro hc
      rw [hc, runit7_zero] at hr
      have hjx : (j : ZMod 7) * runit7 x = 0 := hr.symm
      have hxr : runit7 x = 0 := by
        rcases hj with rfl | rfl
        · have h2 : ((2 : ℕ) : ZMod 7) ≠ 0 := by decide
          rcases mul_eq_zero.mp hjx with h0 | h0
          · exact absurd h0 h2
          · exact h0
        · have h3 : ((3 : ℕ) : ZMod 7) ≠ 0 := by decide
          rcases mul_eq_zero.mp hjx with h0 | h0
          · exact absurd h0 h3
          · exact h0
      have : x = 0 := by
        by_contra hne
        exact runit7_ne_zero (Nat.pos_of_ne_zero hne) hxr
      exact hx0 this
    set hν := padicValNat 7 x with hνdef
    have hxν : padicValNat 7 x = hν := rfl
    have hyν : padicValNat 7 y = hν := h.symm
    have hνm : hν < m := by rwa [hyν] at hm'
    have hrx : runit7 x ≠ 0 := runit7_ne_zero (Nat.pos_of_ne_zero hx0)
    rcases hj with rfl | rfl
    · -------------------------------------------------------------
      -- j = 2: two-stage λ = λ₂·λ₁
      -------------------------------------------------------------
      push_cast at hr
      set E := eMod7 m x y with hE
      have hEcast : ((E : ℕ) : ZMod (7 ^ (m + 1)))
          = 2 * (x : ZMod _) - (y : ZMod _) := by
        rw [hE, eMod7_zmod_cast, if_pos hr]
      -- `E % 7^{h+1} = 0`: the `2x − y` blocks `r·7^h` cancel mod `7^{h+1}`
      have h2v : (2 * (runit7 x).val) % 7 = (runit7 y).val % 7 := by
        have hcongr : ((2 * (runit7 x).val : ℕ) : ZMod 7)
            = ((runit7 y).val : ZMod 7) := by
          rw [Nat.cast_mul, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val,
            Nat.cast_ofNat]
          exact hr.symm
        exact (ZMod.natCast_eq_natCast_iff' _ _ _).mp hcongr
      have hEmod : E % 7 ^ (hν + 1) = 0 := by
        rw [hE]
        have hunf : eMod7 m x y
            = (2 * (x % 7 ^ (m + 1)) + 7 ^ (m + 1) - y % 7 ^ (m + 1))
              % 7 ^ (m + 1) := by
          unfold eMod7
          rw [if_pos hr]
        rw [hunf,
          Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 7 (by omega : hν + 1 ≤ m + 1)),
          wrap_sub_mod_gen (Nat.pow_pos (by norm_num) : 0 < 7 ^ (hν + 1))
            (Nat.pow_dvd_pow 7 (by omega : hν + 1 ≤ m + 1))
            (by have := Nat.mod_lt y (Nat.pow_pos (by norm_num) :
                  0 < 7 ^ (m + 1)); omega),
          Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 7 (by omega : hν + 1 ≤ m + 1))]
        have ha : (2 * (x % 7 ^ (m + 1))) % 7 ^ (hν + 1)
            = (runit7 y).val * 7 ^ hν := by
          rw [Nat.mul_mod,
            Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 7 (by omega : hν + 1 ≤ m + 1)),
            nat_mod_pow_succ_of_padic hx0 hxν]
          have h2P : (2 : ℕ) < 7 ^ (hν + 1) := by
            have h1 : (7 : ℕ) ^ 1 ≤ 7 ^ (hν + 1) :=
              Nat.pow_le_pow_right (by norm_num) (by omega : 1 ≤ hν + 1)
            rw [pow_one] at h1
            omega
          rw [Nat.mod_eq_of_lt h2P, ← mul_assoc]
          have h2w : 2 * (runit7 x).val
              = (runit7 y).val + 7 * ((2 * (runit7 x).val) / 7) := by
            have hdiv := Nat.div_add_mod (2 * (runit7 x).val) 7
            rw [h2v, Nat.mod_eq_of_lt (ZMod.val_lt _)] at hdiv
            omega
          rw [h2w, add_mul]
          have hw7 : (7 * ((2 * (runit7 x).val) / 7)) * 7 ^ hν
              = ((2 * (runit7 x).val) / 7) * 7 ^ (hν + 1) := by
            rw [pow_succ']; ring
          rw [hw7, Nat.add_mul_mod_self_right]
          exact Nat.mod_eq_of_lt (by
            rw [pow_succ']
            exact Nat.mul_lt_mul_of_pos_right (ZMod.val_lt _)
              (Nat.pow_pos (by norm_num)))
        rw [ha, nat_mod_pow_succ_of_padic hy0 hyν]
        have hsim : (runit7 y).val * 7 ^ hν + 7 ^ (hν + 1)
            - (runit7 y).val * 7 ^ hν = 7 ^ (hν + 1) := by omega
        rw [hsim, Nat.mod_self]
      have hνE : E = 0 ∨ hν < padicValNat 7 E := by
        rcases eq_or_ne E 0 with hE0 | hE0
        · exact Or.inl hE0
        · exact Or.inr ((Nat.pow_dvd_iff_le_padicValNat (by norm_num) hE0).mp
            (Nat.dvd_of_mod_eq_zero hEmod))
      have hνE' : E ≠ 0 → hν < padicValNat 7 E := by
        intro hE0
        rcases hνE with h0 | hlt
        · exact absurd h0 hE0
        · exact hlt
      -- λ₁: normalize `q(λ₁E)` to `0`, or to `1` with `λ₁E ≡ 7^m` (pure block)
      obtain ⟨lam1, hlam1u, hlam17, hq1E⟩ :
          ∃ lam1 : ℕ, runit7 lam1 ≠ 0 ∧ ¬ 7 ∣ lam1 ∧
            (qdig7 m (lam1 * E) = 0 ∨ (lam1 * E) % 7 ^ (m + 1) = 7 ^ m) := by
        rcases hνE with hE0 | hνE
        · refine ⟨1, runit7_ne_zero (by norm_num), by decide, Or.inl ?_⟩
          rw [one_mul, hE0]
          exact qdig7_zero m
        · have hE0' : E ≠ 0 := by
            intro hE0
            rw [hE0] at hνE
            have h00 : padicValNat 7 (0 : ℕ) = 0 := by simp [padicValNat]
            rw [h00] at hνE
            exact Nat.not_lt_zero _ hνE
          have hνEm : padicValNat 7 E ≤ m := enu7_le_of_ne hE0'
          by_cases htop : padicValNat 7 E = m
          · obtain ⟨c, hc0, hc7, hcN, _hcq⟩ :=
              exists_top_scalar_set htop hE0' (t := 1) (by decide)
            have h1v : (1 : ZMod 7).val = 1 := by decide
            refine ⟨c, runit7_ne_zero hc0, ?_, Or.inr ?_⟩
            · intro hd
              have h0 : c = 0 := Nat.eq_zero_of_dvd_of_lt hd hc7
              omega
            · rw [h1v, one_mul] at hcN
              exact hcN
          · have hνElt : padicValNat 7 E < m := by omega
            obtain ⟨k, _hk7, hkset⟩ := exists_multLow_set_qdig hνElt rfl hE0' 0
            exact ⟨1 + k * 7 ^ (m - padicValNat 7 E),
              by rw [runit7_multLow hνElt]; decide,
              multLow_not_dvd hνElt, Or.inl hkset⟩
      have hlam1ne : lam1 ≠ 0 := by
        intro h0
        rw [h0, runit7_zero] at hlam1u
        exact hlam1u rfl
      have h1x0 : lam1 * x ≠ 0 := mul_ne_zero hlam1ne hx0
      have h1y0 : lam1 * y ≠ 0 := mul_ne_zero hlam1ne hy0
      have hν1x : padicValNat 7 (lam1 * x) = hν := by
        rw [padicValNat_mul_seven hlam17 hx0]
      have hν1y : padicValNat 7 (lam1 * y) = hν := by
        rw [padicValNat_mul_seven hlam17 hy0]; exact hyν
      have hrel1 : runit7 (lam1 * y) = 2 * runit7 (lam1 * x) := by
        rw [runit7_mul, runit7_mul, hr]; ring
      have he1 : qdig7 m (eMod7 m (lam1 * x) (lam1 * y))
          = qdig7 m (lam1 * E) := by
        rw [eMod7_smul hlam1u, ← hE]
        exact qdig7_congr (Nat.mod_mod _ _)
      -- `ẽ₁ := etd7(λ₁x,λ₁y) = 2q(λ₁x) − q(λ₁y)` ∈ {0,1} or `= 6`
      have hep16 : etd7 m (lam1 * x) (lam1 * y) ∈ ({0, 1, 6} : Finset (ZMod 7)) := by
        rcases hq1E with hq0 | hN1
        · have hqe : qdig7 m (eMod7 m (lam1 * x) (lam1 * y)) = 0 := by
            rw [he1]; exact hq0
          have hsub := qdig_eMod_sub_etd7 (m := m) (x := lam1 * x)
            (y := lam1 * y)
          rw [hqe, zero_sub] at hsub
          rw [← neg_neg (etd7 m (lam1 * x) (lam1 * y))]
          exact neg_mem_016 hsub
        · have hN : eMod7 m (lam1 * x) (lam1 * y) = 7 ^ m := by
            rw [eMod7_smul hlam1u, ← hE]; exact hN1
          have hmem := etd7_of_pure_block hrel1 hN
          simp only [Finset.mem_insert, Finset.mem_singleton] at hmem ⊢
          rcases hmem with h0 | h1
          · rw [h0]; decide
          · rw [h1]; decide
      have hep1 : etd7 m (lam1 * x) (lam1 * y) ∈ ({0, 1} : Finset (ZMod 7))
          ∨ etd7 m (lam1 * x) (lam1 * y) = 6 := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hep16
        rcases hep16 with h0 | h1 | h6
        · left; rw [h0]; decide
        · left; rw [h1]; decide
        · right; exact h6
      -- `c_x := 6` iff `ẽ₁ = 6`, else `0` (forces `q(λy) ∈ {0,6}`)
      set cx : ZMod 7 := if etd7 m (lam1 * x) (lam1 * y) = 6 then 6 else 0
        with hcxdef
      have hcx_mem : cx ∈ ({0, 6} : Finset (ZMod 7)) := by
        rw [hcxdef]
        by_cases h : etd7 m (lam1 * x) (lam1 * y) = 6
        · rw [if_pos h]; decide
        · rw [if_neg h]; decide
      have hcx_of6 : etd7 m (lam1 * x) (lam1 * y) = 6 → cx = 6 := fun hh => by
        rw [hcxdef, if_pos hh]
      have hcx_of01 : etd7 m (lam1 * x) (lam1 * y) ≠ 6 → cx = 0 := fun hh => by
        rw [hcxdef, if_neg hh]
      -- λ₂ = 1 + k·7^{m−h} sets `q(λx) = c_x`
      obtain ⟨k, _hk7, hset⟩ := exists_multLow_set_qdig hνm hν1x h1x0 cx
      set lam2 : ℕ := 1 + k * 7 ^ (m - hν) with hlam2def
      set lam : ℕ := lam2 * lam1 with hlamdef
      have hlam2u : runit7 lam2 = 1 := by
        rw [hlam2def]; exact runit7_multLow hνm
      have hlamu : runit7 lam ≠ 0 := by
        rw [hlamdef, runit7_mul, hlam2u, one_mul]
        exact hlam1u
      have hlam7 : ¬ 7 ∣ lam := by
        intro hd
        rcases (Nat.Prime.dvd_mul (show Nat.Prime 7 by norm_num)).mp hd
          with hdvd | hdvd
        · rw [hlam2def] at hdvd; exact multLow_not_dvd hνm hdvd
        · exact hlam17 hdvd
      have hlamne : lam ≠ 0 := by
        intro h0
        rw [h0] at hlam7
        exact hlam7 (dvd_zero 7)
      -- endpoint digits
      have hqx : qdig7 m (lam * x) = cx := by
        rw [hlamdef, mul_assoc, hlam2def]
        exact hset
      have hqy : qdig7 m (lam * y)
          = 2 * cx - etd7 m (lam1 * x) (lam1 * y) := by
        rw [hlamdef, mul_assoc, hlam2def]
        have h1 := qdig7_multLow hνm hν1y (k := k)
        rw [h1]
        have hkrx : (k : ZMod 7) * runit7 (lam1 * x)
            = cx - qdig7 m (lam1 * x) := by
          have h2 := qdig7_multLow hνm hν1x (k := k)
          rw [hset] at h2
          have h3 : (k : ZMod 7) * runit7 (lam1 * x) + qdig7 m (lam1 * x)
              = cx := by
            rw [add_comm]; exact h2.symm
          exact eq_sub_iff_add_eq.mpr h3
        have hk2 : (k : ZMod 7) * runit7 (lam1 * y)
            = 2 * ((k : ZMod 7) * runit7 (lam1 * x)) := by
          rw [hrel1]; ring
        have hep : etd7 m (lam1 * x) (lam1 * y)
            = 2 * qdig7 m (lam1 * x) - qdig7 m (lam1 * y) :=
          etd7_eq_twoX hrel1
        rw [hep, hk2, hkrx]
        ring
      have hmodElam : (lam * E) % 7 ^ (m + 1) = (lam1 * E) % 7 ^ (m + 1) := by
        rcases eq_or_ne E 0 with hE0 | hE0
        · rw [hE0, mul_zero, mul_zero]
        · have hEν1 : hν < padicValNat 7 (lam1 * E) := by
            rw [padicValNat_mul_seven hlam17 hE0]; exact hνE' hE0
          have hres := residN_multLow7 (k := k) hνm hEν1
          rw [hlamdef, mul_assoc, hlam2def]
          exact hres
      have hqElam : qdig7 m (lam * E) = qdig7 m (lam1 * E) :=
        qdig7_congr hmodElam
      have hlowElam : (lam * E) % 7 ^ m = (lam1 * E) % 7 ^ m := by
        have h1 : (lam * E) % 7 ^ m = ((lam * E) % 7 ^ (m + 1)) % 7 ^ m :=
          (Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 7 (Nat.le_succ m))).symm
        have h2 : (lam1 * E) % 7 ^ m = ((lam1 * E) % 7 ^ (m + 1)) % 7 ^ m :=
          (Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 7 (Nat.le_succ m))).symm
        rw [h1, h2, hmodElam]
      have hdv1x : 7 ^ hν ∣ lam1 * x :=
        (Nat.pow_dvd_iff_le_padicValNat (by norm_num) h1x0).mpr
          (le_of_eq hν1x.symm)
      have hdv1y : 7 ^ hν ∣ lam1 * y :=
        (Nat.pow_dvd_iff_le_padicValNat (by norm_num) h1y0).mpr
          (le_of_eq hν1y.symm)
      have hlowx : (lam * x) % 7 ^ m = (lam1 * x) % 7 ^ m := by
        rw [hlamdef, mul_assoc, hlam2def]
        exact multLow_low hνm.le hdv1x
      have hlowy : (lam * y) % 7 ^ m = (lam1 * y) % 7 ^ m := by
        rw [hlamdef, mul_assoc, hlam2def]
        exact multLow_low hνm.le hdv1y
      have hlowx0 : (lam * x) % 7 ^ m ≠ 0 := by
        rw [hlowx]
        intro hc
        have hd : 7 ^ m ∣ lam1 * x := Nat.dvd_of_mod_eq_zero hc
        have hle : m ≤ padicValNat 7 (lam1 * x) :=
          (Nat.pow_dvd_iff_le_padicValNat (by norm_num) h1x0).mp hd
        rw [hν1x] at hle
        omega
      have hlowy0 : (lam * y) % 7 ^ m ≠ 0 := by
        rw [hlowy]
        intro hc
        have hd : 7 ^ m ∣ lam1 * y := Nat.dvd_of_mod_eq_zero hc
        have hle : m ≤ padicValNat 7 (lam1 * y) :=
          (Nat.pow_dvd_iff_le_padicValNat (by norm_num) h1y0).mp hd
        rw [hν1y] at hle
        omega
      -- `q(λy) ∈ {0,6}`: `ẽ ∈ {0,1} ⇒ 2·0−ẽ ∈ {0,6}`; `ẽ = 6 ⇒ 2·6−6 = 6`
      have hqy_mem : qdig7 m (lam * y) ∈ ({0, 6} : Finset (ZMod 7)) := by
        rw [hqy]
        rcases hep1 with h01 | h6
        · simp only [Finset.mem_insert, Finset.mem_singleton] at h01 ⊢
          rcases h01 with h0 | h1
          · rw [hcx_of01 (by rw [h0]; decide), h0]; decide
          · rw [hcx_of01 (by rw [h1]; decide), h1]; decide
        · simp only [Finset.mem_insert, Finset.mem_singleton]
          rw [hcx_of6 h6, h6]; decide
      -- the pair evaluator
      have eval : ∀ {u v A B : ℕ},
          ((lam * eMod7 m u v : ℕ) : ZMod (7 ^ (m + 1)))
            = (A : ZMod _) - (B : ZMod _) →
          qdig7 m (eMod7 m (lam * u) (lam * v))
            = qdig7 m A - qdig7 m B
              - if A % 7 ^ m < B % 7 ^ m then (1 : ZMod 7) else 0 := by
        intro u v A B hcast
        rw [eMod7_smul hlamu, qdig7_congr (Nat.mod_mod _ _)]
        exact qdig_smul_eMod_eq hcast
      have key : ∀ u ∈ ({b1, b2, b3} : Finset ℕ),
          ∀ v ∈ ({b1, b2, b3} : Finset ℕ),
          qdig7 m (eMod7 m (lam * u) (lam * v))
            ∈ ({0, 6} : Finset (ZMod 7)) := by
        intro u hu v hv
        rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hu hv
        rcases hu with hu' | hu' | hu' <;> rcases hv with hv' | hv' | hv' <;>
          rw [hu', hv']
        · rw [eMod7_self, qdig7_zero]; decide
        · -- (b1,b2): `λE − λx` (c_x = 0) or `λx − λy` (c_x = 6)
          rcases hep1 with h01 | h6
          · have hcast : ((lam * eMod7 m b1 b2 : ℕ) : ZMod (7 ^ (m + 1)))
                = ((lam * E : ℕ) : ZMod _) - ((lam * x : ℕ) : ZMod _) := by
              simp only [Nat.cast_mul]
              rw [hc12, hEcast]
              ring
            have hne6 : etd7 m (lam1 * x) (lam1 * y) ≠ 6 := by
              simp only [Finset.mem_insert, Finset.mem_singleton] at h01
              rcases h01 with h0 | h1
              · rw [h0]; decide
              · rw [h1]; decide
            rw [eval hcast, hqElam, hqx, hcx_of01 hne6]
            rcases hq1E with hq0 | hN1
            · rw [hq0]
              by_cases hδ : lam * E % 7 ^ m < lam * x % 7 ^ m
              · rw [if_pos hδ]; decide
              · rw [if_neg hδ]; decide
            · have hqE1 : qdig7 m (lam1 * E) = 1 := by
                have hlt : (7 : ℕ) ^ m < 7 ^ (m + 1) :=
                  Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self m)
                rw [qdig7_congr (hN1.trans (Nat.mod_eq_of_lt hlt).symm)]
                exact qdig7_pow_self m
              rw [hqE1]
              have hδ : lam * E % 7 ^ m < lam * x % 7 ^ m := by
                rw [hlowElam]
                have h0 : (lam1 * E) % 7 ^ m = 0 := by
                  have hh : (lam1 * E) % 7 ^ m
                      = ((lam1 * E) % 7 ^ (m + 1)) % 7 ^ m :=
                    (Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 7 (Nat.le_succ m))).symm
                  rw [hh, hN1, Nat.mod_self]
                rw [h0]
                exact Nat.pos_of_ne_zero hlowx0
              rw [if_pos hδ]; decide
          · have hcast : ((lam * eMod7 m b1 b2 : ℕ) : ZMod (7 ^ (m + 1)))
                = ((lam * x : ℕ) : ZMod _) - ((lam * y : ℕ) : ZMod _) := by
              simp only [Nat.cast_mul]
              rw [hc12]; ring
            rw [eval hcast, hqx, hqy, hcx_of6 h6, h6]
            by_cases hδ : lam * x % 7 ^ m < lam * y % 7 ^ m
            · rw [if_pos hδ]; decide
            · rw [if_neg hδ]; decide
        · -- (b1,b3): `q(λx) = c_x`
          rw [eMod7_smul hlamu, qdig7_congr (Nat.mod_mod _ _), ← hx, hqx]
          exact hcx_mem
        · -- (b2,b1): `λx − λE` (c_x = 0) or `λy − λx` (c_x = 6)
          rcases hep1 with h01 | h6
          · have hcast : ((lam * eMod7 m b2 b1 : ℕ) : ZMod (7 ^ (m + 1)))
                = ((lam * x : ℕ) : ZMod _) - ((lam * E : ℕ) : ZMod _) := by
              simp only [Nat.cast_mul]
              rw [hc21, hEcast]
              ring
            have hne6 : etd7 m (lam1 * x) (lam1 * y) ≠ 6 := by
              simp only [Finset.mem_insert, Finset.mem_singleton] at h01
              rcases h01 with h0 | h1
              · rw [h0]; decide
              · rw [h1]; decide
            rw [eval hcast, hqx, hqElam, hcx_of01 hne6]
            rcases hq1E with hq0 | hN1
            · rw [hq0]
              by_cases hδ : lam * x % 7 ^ m < lam * E % 7 ^ m
              · rw [if_pos hδ]; decide
              · rw [if_neg hδ]; decide
            · have hqE1 : qdig7 m (lam1 * E) = 1 := by
                have hlt : (7 : ℕ) ^ m < 7 ^ (m + 1) :=
                  Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self m)
                rw [qdig7_congr (hN1.trans (Nat.mod_eq_of_lt hlt).symm)]
                exact qdig7_pow_self m
              rw [hqE1]
              have hδ : ¬ lam * x % 7 ^ m < lam * E % 7 ^ m := by
                rw [hlowElam]
                have h0 : (lam1 * E) % 7 ^ m = 0 := by
                  have hh : (lam1 * E) % 7 ^ m
                      = ((lam1 * E) % 7 ^ (m + 1)) % 7 ^ m :=
                    (Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 7 (Nat.le_succ m))).symm
                  rw [hh, hN1, Nat.mod_self]
                rw [h0]
                exact Nat.not_lt_zero _
              rw [if_neg hδ]; decide
          · have hcast : ((lam * eMod7 m b2 b1 : ℕ) : ZMod (7 ^ (m + 1)))
                = ((lam * y : ℕ) : ZMod _) - ((lam * x : ℕ) : ZMod _) := by
              simp only [Nat.cast_mul]
              rw [hc21]; ring
            rw [eval hcast, hqy, hqx, hcx_of6 h6, h6]
            by_cases hδ : lam * y % 7 ^ m < lam * x % 7 ^ m
            · rw [if_pos hδ]; decide
            · rw [if_neg hδ]; decide
        · rw [eMod7_self, qdig7_zero]; decide
        · -- (b2,b3): `q(λy) ∈ {0,6}`
          rw [eMod7_smul hlamu, qdig7_congr (Nat.mod_mod _ _), ← hy]
          exact hqy_mem
        · -- (b3,b1): `−λx`, borrow forced by `(λx) % 7^m ≠ 0`
          have hcast : ((lam * eMod7 m b3 b1 : ℕ) : ZMod (7 ^ (m + 1)))
              = ((0 : ℕ) : ZMod _) - ((lam * x : ℕ) : ZMod _) := by
            simp only [Nat.cast_mul, Nat.cast_zero]
            rw [hc31]; ring
          rw [eval hcast, qdig7_zero, Nat.zero_mod,
            if_pos (Nat.pos_of_ne_zero hlowx0), hqx]
          have hsimp : (0 : ZMod 7) - cx - 1 = -cx - 1 := by ring
          rw [hsimp]
          exact neg_sub_one_mem_06 hcx_mem
        · -- (b3,b2): `−λy`
          have hcast : ((lam * eMod7 m b3 b2 : ℕ) : ZMod (7 ^ (m + 1)))
              = ((0 : ℕ) : ZMod _) - ((lam * y : ℕ) : ZMod _) := by
            simp only [Nat.cast_mul, Nat.cast_zero]
            rw [hc32]; ring
          rw [eval hcast, qdig7_zero, Nat.zero_mod,
            if_pos (Nat.pos_of_ne_zero hlowy0)]
          have hsimp : (0 : ZMod 7) - qdig7 m (lam * y) - 1
              = -qdig7 m (lam * y) - 1 := by ring
          rw [hsimp]
          exact neg_sub_one_mem_06 hqy_mem
        · rw [eMod7_self, qdig7_zero]; decide
      set BL : Finset ℕ := ({b1, b2, b3} : Finset ℕ).image (lam * ·)
        with hBLdef
      have hBLsame : ∀ u ∈ BL, ∀ v ∈ BL,
          residueRelOf u v = residueRel.same := by
        intro u hu v hv
        obtain ⟨u', hu', rfl⟩ := Finset.mem_image.mp hu
        obtain ⟨v', hv', rfl⟩ := Finset.mem_image.mp hv
        apply rel_same _ (mul_ne_zero hlamne (ne_of_gt (hposB v' hv')))
        rw [runit7_mul lam u', runit7_mul lam v', hr_all u' hu', hr_all v' hv']
      have hBL : ∀ u ∈ BL, ∀ v ∈ BL,
          qdig7 m (eMod7 m u v) ∈ ({0, 6} : Finset (ZMod 7)) := by
        intro u hu v hv
        obtain ⟨u', hu', rfl⟩ := Finset.mem_image.mp hu
        obtain ⟨v', hv', rfl⟩ := Finset.mem_image.mp hv
        exact key u' hu' v' hv'
      have hdiff := remark8_i_int hBLsame hBL
      have hlen : apLen (BL.image (qdig7 m)) ≤ 2 := by
        have hh := remark8_i hdiff (k := 1) (by decide)
        simp only [mul_one] at hh
        rw [Finset.image_id'] at hh
        have h1 : (1 : ZMod 7).val = 1 := by decide
        rw [h1] at hh
        exact hh
      have himg : BL.image (qdig7 m)
          = ({b1, b2, b3} : Finset ℕ).image (fun d => qdig7 m (lam * d)) := by
        rw [hBLdef, Finset.image_image]
        exact Finset.image_congr fun d _ => rfl
      refine ⟨lam, hlam7, ?_, ?_, ?_, ?_⟩
      · rw [eMod7_smul hlamu, qdig7_congr (Nat.mod_mod _ _), ← hy]
        simp only [Finset.mem_insert, Finset.mem_singleton] at hqy_mem ⊢
        rcases hqy_mem with h0 | h6
        · rw [h0]; decide
        · rw [h6]; decide
      · intro x' hx' y' hy'
        exact subset0156_06 (hBL _ (Finset.mem_image.mpr ⟨x', hx', rfl⟩)
          _ (Finset.mem_image.mpr ⟨y', hy', rfl⟩))
      · intro _ x' hx' y' hy'
        exact hBL _ (Finset.mem_image.mpr ⟨x', hx', rfl⟩)
          _ (Finset.mem_image.mpr ⟨y', hy', rfl⟩)
      · rw [himg] at hlen
        exact hlen
    · -------------------------------------------------------------
      -- j = 3: single Λ_h multiplier λ = 1 + k·7^{m−h}
      -------------------------------------------------------------
      push_cast at hr
      obtain ⟨t, ht, htx, hdxy⟩ := lemma9_ii_table3 (qdig7 m x) (qdig7 m y)
      obtain ⟨k, _hk7, hset⟩ := exists_multLow_set_qdig hνm hyν hy0 t
      set lam : ℕ := 1 + k * 7 ^ (m - hν) with hlamdef
      have hlam1 : runit7 lam = 1 := by
        rw [hlamdef]; exact runit7_multLow hνm
      have hlam0 : runit7 lam ≠ 0 := by rw [hlam1]; decide
      have hlam7 : ¬ 7 ∣ lam := by rw [hlamdef]; exact multLow_not_dvd hνm
      have hlamne : lam ≠ 0 := by
        intro h0
        rw [h0] at hlam7
        exact hlam7 (dvd_zero 7)
      -- `(k)·r(x) = 5·(t − qy)` via `3·u = v ⇒ u = 5v`
      have hkry : (k : ZMod 7) * runit7 y = t - qdig7 m y := by
        have h1 := qdig7_multLow hνm hyν (k := k)
        rw [hset] at h1
        have h2 : (k : ZMod 7) * runit7 y + qdig7 m y = t := by
          rw [add_comm]; exact h1.symm
        exact eq_sub_iff_add_eq.mpr h2
      have hkqx : (k : ZMod 7) * runit7 x = 5 * (t - qdig7 m y) := by
        have h3 : (3 : ZMod 7) * ((k : ZMod 7) * runit7 x)
            = t - qdig7 m y := by
          have e : (3 : ZMod 7) * ((k : ZMod 7) * runit7 x)
              = (k : ZMod 7) * runit7 y := by
            rw [hr]; ring
          rw [e]; exact hkry
        calc (k : ZMod 7) * runit7 x
            = 5 * (3 * ((k : ZMod 7) * runit7 x)) := by
              have h15 : (5 : ZMod 7) * 3 = 1 := by decide
              rw [← mul_assoc, h15, one_mul]
        _ = 5 * (t - qdig7 m y) := by rw [h3]
      have hqx : qdig7 m (lam * x)
          = qdig7 m x + 2 * qdig7 m y + 5 * t := by
        have h1 := qdig7_multLow hνm hxν (k := k)
        rw [← hlamdef] at h1
        rw [h1, hkqx]
        have hsub5 : (5 : ZMod 7) * (t - qdig7 m y) = 5 * t + 2 * qdig7 m y := by
          have h5 : (-5 : ZMod 7) = 2 := by decide
          rw [mul_sub, sub_eq_add_neg, ← neg_mul, h5]
        rw [hsub5]; ring
      have hqy : qdig7 m (lam * y) = t := hset
      have hqxy : qdig7 m (lam * x) - qdig7 m (lam * y)
          ∈ ({0, 1, 6} : Finset (ZMod 7)) := by
        rw [hqx, hqy]
        have e : qdig7 m x + 2 * qdig7 m y + 5 * t - t
            = qdig7 m x + 2 * qdig7 m y + 4 * t := by ring
        rw [e]; exact hdxy
      have hdvx : 7 ^ hν ∣ x :=
        (Nat.pow_dvd_iff_le_padicValNat (by norm_num) hx0).mpr
          (le_of_eq hxν.symm)
      have hdvy : 7 ^ hν ∣ y :=
        (Nat.pow_dvd_iff_le_padicValNat (by norm_num) hy0).mpr
          (le_of_eq hyν.symm)
      have hlowx : (lam * x) % 7 ^ m = x % 7 ^ m := by
        rw [hlamdef]; exact multLow_low hνm.le hdvx
      have hlowy : (lam * y) % 7 ^ m = y % 7 ^ m := by
        rw [hlamdef]; exact multLow_low hνm.le hdvy
      have hlowx0 : (lam * x) % 7 ^ m ≠ 0 := by
        rw [hlowx]
        intro hc
        have hd : 7 ^ m ∣ x := Nat.dvd_of_mod_eq_zero hc
        have hle : m ≤ padicValNat 7 x :=
          (Nat.pow_dvd_iff_le_padicValNat (by norm_num) hx0).mp hd
        rw [hxν] at hle
        omega
      have hlowy0 : (lam * y) % 7 ^ m ≠ 0 := by
        rw [hlowy]
        intro hc
        have hd : 7 ^ m ∣ y := Nat.dvd_of_mod_eq_zero hc
        have hle : m ≤ padicValNat 7 y :=
          (Nat.pow_dvd_iff_le_padicValNat (by norm_num) hy0).mp hd
        rw [hyν] at hle
        omega
      have eval : ∀ {u v A B : ℕ},
          ((lam * eMod7 m u v : ℕ) : ZMod (7 ^ (m + 1)))
            = (A : ZMod _) - (B : ZMod _) →
          qdig7 m (eMod7 m (lam * u) (lam * v))
            = qdig7 m A - qdig7 m B
              - if A % 7 ^ m < B % 7 ^ m then (1 : ZMod 7) else 0 := by
        intro u v A B hcast
        rw [eMod7_smul hlam0, qdig7_congr (Nat.mod_mod _ _)]
        exact qdig_smul_eMod_eq hcast
      have key : ∀ u ∈ ({b1, b2, b3} : Finset ℕ),
          ∀ v ∈ ({b1, b2, b3} : Finset ℕ),
          qdig7 m (eMod7 m (lam * u) (lam * v))
            ∈ ({0, 1, 5, 6} : Finset (ZMod 7)) := by
        intro u hu v hv
        rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hu hv
        rcases hu with hu' | hu' | hu' <;> rcases hv with hv' | hv' | hv' <;>
          rw [hu', hv']
        · rw [eMod7_self, qdig7_zero]; decide
        · -- (b1,b2): `λx − λy` — `qx+2qy+4t ∈ {0,1,6}` minus borrow
          have hcast : ((lam * eMod7 m b1 b2 : ℕ) : ZMod (7 ^ (m + 1)))
              = ((lam * x : ℕ) : ZMod _) - ((lam * y : ℕ) : ZMod _) := by
            simp only [Nat.cast_mul]
            rw [hc12]; ring
          rw [eval hcast, hqx, hqy]
          have hsimp : qdig7 m x + 2 * qdig7 m y + 5 * t - t
              = qdig7 m x + 2 * qdig7 m y + 4 * t := by ring
          rw [hsimp]
          by_cases hδ : lam * x % 7 ^ m < lam * y % 7 ^ m
          · rw [if_pos hδ]
            exact sub_borrow_mem_0156 hdxy (Or.inr rfl)
          · rw [if_neg hδ]
            exact sub_borrow_mem_0156 hdxy (Or.inl rfl)
        · -- (b1,b3): `q(λx) = qx+2qy+5t ∈ {0,1,5,6}`
          rw [eMod7_smul hlam0, qdig7_congr (Nat.mod_mod _ _), ← hx, hqx]
          exact htx
        · -- (b2,b1): `λy − λx` — `−(qx+2qy+4t) ∈ {0,1,6}` minus borrow
          have hcast : ((lam * eMod7 m b2 b1 : ℕ) : ZMod (7 ^ (m + 1)))
              = ((lam * y : ℕ) : ZMod _) - ((lam * x : ℕ) : ZMod _) := by
            simp only [Nat.cast_mul]
            rw [hc21]; ring
          rw [eval hcast, hqy, hqx]
          have hsimp : t - (qdig7 m x + 2 * qdig7 m y + 5 * t)
              = -(qdig7 m x + 2 * qdig7 m y + 4 * t) := by ring
          rw [hsimp]
          by_cases hδ : lam * y % 7 ^ m < lam * x % 7 ^ m
          · rw [if_pos hδ]
            exact sub_borrow_mem_0156 (neg_mem_016 hdxy) (Or.inr rfl)
          · rw [if_neg hδ]
            exact sub_borrow_mem_0156 (neg_mem_016 hdxy) (Or.inl rfl)
        · rw [eMod7_self, qdig7_zero]; decide
        · -- (b2,b3): `q(λy) = t ∈ {0,5,6} ⊆ {0,1,5,6}`
          rw [eMod7_smul hlam0, qdig7_congr (Nat.mod_mod _ _), ← hy, hqy]
          simp only [Finset.mem_insert, Finset.mem_singleton] at ht ⊢
          rcases ht with rfl | rfl | rfl <;> decide
        · -- (b3,b1): `−λx`, borrow forced
          have hcast : ((lam * eMod7 m b3 b1 : ℕ) : ZMod (7 ^ (m + 1)))
              = ((0 : ℕ) : ZMod _) - ((lam * x : ℕ) : ZMod _) := by
            simp only [Nat.cast_mul, Nat.cast_zero]
            rw [hc31]; ring
          rw [eval hcast, qdig7_zero, Nat.zero_mod,
            if_pos (Nat.pos_of_ne_zero hlowx0), hqx]
          have hsimp : (0 : ZMod 7) - (qdig7 m x + 2 * qdig7 m y + 5 * t) - 1
              = -(qdig7 m x + 2 * qdig7 m y + 5 * t) - 1 := by ring
          rw [hsimp]
          exact neg_sub_one_mem_0156 htx
        · -- (b3,b2): `−λy`
          have hcast : ((lam * eMod7 m b3 b2 : ℕ) : ZMod (7 ^ (m + 1)))
              = ((0 : ℕ) : ZMod _) - ((lam * y : ℕ) : ZMod _) := by
            simp only [Nat.cast_mul, Nat.cast_zero]
            rw [hc32]; ring
          rw [eval hcast, qdig7_zero, Nat.zero_mod,
            if_pos (Nat.pos_of_ne_zero hlowy0), hqy]
          have hsimp : (0 : ZMod 7) - t - 1 = -t - 1 := by ring
          rw [hsimp]
          exact neg_sub_one_mem_056 ht
        · rw [eMod7_self, qdig7_zero]; decide
      set BL : Finset ℕ := ({b1, b2, b3} : Finset ℕ).image (lam * ·)
        with hBLdef
      have hBLsame : ∀ u ∈ BL, ∀ v ∈ BL,
          residueRelOf u v = residueRel.same := by
        intro u hu v hv
        obtain ⟨u', hu', rfl⟩ := Finset.mem_image.mp hu
        obtain ⟨v', hv', rfl⟩ := Finset.mem_image.mp hv
        apply rel_same _ (mul_ne_zero hlamne (ne_of_gt (hposB v' hv')))
        rw [runit7_mul, runit7_mul, hlam1, one_mul, one_mul,
          hr_all u' hu', hr_all v' hv']
      have hBL : ∀ u ∈ BL, ∀ v ∈ BL,
          qdig7 m (eMod7 m u v) ∈ ({0, 1, 5, 6} : Finset (ZMod 7)) := by
        intro u hu v hv
        obtain ⟨u', hu', rfl⟩ := Finset.mem_image.mp hu
        obtain ⟨v', hv', rfl⟩ := Finset.mem_image.mp hv
        exact key u' hu' v' hv'
      have hdiff := remark8_ii_int hBLsame hBL
      have hlen : apLen (BL.image (qdig7 m)) ≤ 3 := remark8_ii' hdiff
      have himg : BL.image (qdig7 m)
          = ({b1, b2, b3} : Finset ℕ).image (fun d => qdig7 m (lam * d)) := by
        rw [hBLdef, Finset.image_image]
        exact Finset.image_congr fun d _ => rfl
      refine ⟨lam, hlam7, ?_, ?_, ?_, ?_⟩
      · rw [eMod7_smul hlam0, qdig7_congr (Nat.mod_mod _ _), ← hy, hqy]
        exact ht
      · intro x' hx' y' hy'
        exact hBL _ (Finset.mem_image.mpr ⟨x', hx', rfl⟩)
          _ (Finset.mem_image.mpr ⟨y', hy', rfl⟩)
      · intro hj2
        omega
      · rw [himg] at hlen
        exact hlen

/-- **`lemma9_ii` specialised to `j = 3` with the `Λ_h`-form of the
multiplier exposed**: returns the shift `k` together with
`lam = 1 + k·7^{m−h}` (where `h = ν(e(b₁,b₃))`), so callers can transport
residues of level `> h` verbatim (`residN_multLow7`-style arguments).
Requires `x := e(b₁,b₃) ≠ 0` (the zero case is trivial anyway). -/
theorem lemma9_ii3 {m : ℕ} {b1 b2 b3 : ℕ}
    (hpos : 0 < b1 ∧ 0 < b2 ∧ 0 < b3)
    (hsame : runit7 b1 = runit7 b2 ∧ runit7 b2 = runit7 b3)
    (hx0 : eMod7 m b1 b3 ≠ 0)
    (h : padicValNat 7 (eMod7 m b1 b3) =
      padicValNat 7 (eMod7 m b2 b3))
    (hm' : padicValNat 7 (eMod7 m b2 b3) < m)
    (hr : runit7 (eMod7 m b2 b3) =
      ((3 : ℕ) : ZMod 7) * runit7 (eMod7 m b1 b3)) :
    ∃ k lam : ℕ, k < 7 ∧ ¬ 7 ∣ lam ∧
      lam = 1 + k * 7 ^ (m - padicValNat 7 (eMod7 m b1 b3)) ∧
      qdig7 m (eMod7 m (lam * b2) (lam * b3)) ∈
        ({0, 5, 6} : Finset (ZMod 7)) ∧
      (∀ x ∈ ({b1, b2, b3} : Finset ℕ), ∀ y ∈ ({b1, b2, b3} : Finset ℕ),
        qdig7 m (eMod7 m (lam * x) (lam * y)) ∈
          ({0, 1, 5, 6} : Finset (ZMod 7))) ∧
      apLen (({b1, b2, b3} : Finset ℕ).image
        (fun d => qdig7 m (lam * d))) ≤ 3 := by
  classical
  set x := eMod7 m b1 b3 with hx
  set y := eMod7 m b2 b3 with hy
  have hb1 : b1 ∈ ({b1, b2, b3} : Finset ℕ) := by simp
  have hb2 : b2 ∈ ({b1, b2, b3} : Finset ℕ) := by simp
  have hb3 : b3 ∈ ({b1, b2, b3} : Finset ℕ) := by simp
  have hposB : ∀ d ∈ ({b1, b2, b3} : Finset ℕ), 0 < d := by
    intro d hd
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl | rfl
    · exact hpos.1
    · exact hpos.2.1
    · exact hpos.2.2
  have hr_all : ∀ d ∈ ({b1, b2, b3} : Finset ℕ),
      runit7 d = runit7 b3 := by
    intro d hd
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl | rfl
    · exact hsame.1.trans hsame.2
    · exact hsame.2
    · rfl
  have hsameB : ∀ u ∈ ({b1, b2, b3} : Finset ℕ),
      ∀ v ∈ ({b1, b2, b3} : Finset ℕ),
      residueRelOf u v = residueRel.same := fun u hu v hv =>
    rel_same ((hr_all u hu).trans (hr_all v hv).symm)
      (ne_of_gt (hposB v hv))
  have hc12 : ((eMod7 m b1 b2 : ℕ) : ZMod (7 ^ (m + 1)))
      = (x : ZMod _) - (y : ZMod _) :=
    eMod7_cast_sub (hsameB b1 hb1 b3 hb3) (hsameB b2 hb2 b3 hb3)
      (hsameB b1 hb1 b2 hb2)
  have hc21 : ((eMod7 m b2 b1 : ℕ) : ZMod (7 ^ (m + 1)))
      = (y : ZMod _) - (x : ZMod _) :=
    eMod7_cast_sub (hsameB b2 hb2 b3 hb3) (hsameB b1 hb1 b3 hb3)
      (hsameB b2 hb2 b1 hb1)
  have hc31 : ((eMod7 m b3 b1 : ℕ) : ZMod (7 ^ (m + 1)))
      = -(x : ZMod _) := by
    have hh := eMod7_cast_sub (m := m) (hsameB b3 hb3 b3 hb3)
      (hsameB b1 hb1 b3 hb3) (hsameB b3 hb3 b1 hb1)
    rw [eMod7_self] at hh
    rwa [Nat.cast_zero, zero_sub] at hh
  have hc32 : ((eMod7 m b3 b2 : ℕ) : ZMod (7 ^ (m + 1)))
      = -(y : ZMod _) := by
    have hh := eMod7_cast_sub (m := m) (hsameB b3 hb3 b3 hb3)
      (hsameB b2 hb2 b3 hb3) (hsameB b3 hb3 b2 hb2)
    rw [eMod7_self] at hh
    rwa [Nat.cast_zero, zero_sub] at hh
  -- `x ≠ 0` given; `y ≠ 0` follows from `r(y) = 3·r(x)`.
  have hy0 : y ≠ 0 := by
    intro hc
    rw [hc, runit7_zero] at hr
    rcases mul_eq_zero.mp hr.symm with h30 | hxr
    · exact absurd h30 (by decide : ((3 : ℕ) : ZMod 7) ≠ 0)
    · exact runit7_ne_zero (Nat.pos_of_ne_zero hx0) hxr
  set hν := padicValNat 7 x with hνdef
  have hxν : padicValNat 7 x = hν := rfl
  have hyν : padicValNat 7 y = hν := h.symm
  have hνm : hν < m := by rwa [hyν] at hm'
  push_cast at hr
  obtain ⟨t, ht, htx, hdxy⟩ := lemma9_ii_table3 (qdig7 m x) (qdig7 m y)
  obtain ⟨k, hk7, hset⟩ := exists_multLow_set_qdig hνm hyν hy0 t
  set lam : ℕ := 1 + k * 7 ^ (m - hν) with hlamdef
  have hlam1 : runit7 lam = 1 := by
    rw [hlamdef]; exact runit7_multLow hνm
  have hlam0 : runit7 lam ≠ 0 := by rw [hlam1]; decide
  have hlam7 : ¬ 7 ∣ lam := by rw [hlamdef]; exact multLow_not_dvd hνm
  have hlamne : lam ≠ 0 := by
    intro h0
    rw [h0] at hlam7
    exact hlam7 (dvd_zero 7)
  have hkry : (k : ZMod 7) * runit7 y = t - qdig7 m y := by
    have h1 := qdig7_multLow hνm hyν (k := k)
    rw [hset] at h1
    have h2 : (k : ZMod 7) * runit7 y + qdig7 m y = t := by
      rw [add_comm]; exact h1.symm
    exact eq_sub_iff_add_eq.mpr h2
  have hkqx : (k : ZMod 7) * runit7 x = 5 * (t - qdig7 m y) := by
    have h3 : (3 : ZMod 7) * ((k : ZMod 7) * runit7 x)
        = t - qdig7 m y := by
      have e : (3 : ZMod 7) * ((k : ZMod 7) * runit7 x)
          = (k : ZMod 7) * runit7 y := by
        rw [hr]; ring
      rw [e]; exact hkry
    calc (k : ZMod 7) * runit7 x
        = 5 * (3 * ((k : ZMod 7) * runit7 x)) := by
          have h15 : (5 : ZMod 7) * 3 = 1 := by decide
          rw [← mul_assoc, h15, one_mul]
    _ = 5 * (t - qdig7 m y) := by rw [h3]
  have hqx : qdig7 m (lam * x)
      = qdig7 m x + 2 * qdig7 m y + 5 * t := by
    have h1 := qdig7_multLow hνm hxν (k := k)
    rw [← hlamdef] at h1
    rw [h1, hkqx]
    have hsub5 : (5 : ZMod 7) * (t - qdig7 m y)
        = 5 * t + 2 * qdig7 m y := by
      have h5 : (-5 : ZMod 7) = 2 := by decide
      rw [mul_sub, sub_eq_add_neg, ← neg_mul, h5]
    rw [hsub5]; ring
  have hqy : qdig7 m (lam * y) = t := hset
  have hdvx : 7 ^ hν ∣ x :=
    (Nat.pow_dvd_iff_le_padicValNat (by norm_num) hx0).mpr
      (le_of_eq hxν.symm)
  have hdvy : 7 ^ hν ∣ y :=
    (Nat.pow_dvd_iff_le_padicValNat (by norm_num) hy0).mpr
      (le_of_eq hyν.symm)
  have hlowx : (lam * x) % 7 ^ m = x % 7 ^ m := by
    rw [hlamdef]; exact multLow_low hνm.le hdvx
  have hlowy : (lam * y) % 7 ^ m = y % 7 ^ m := by
    rw [hlamdef]; exact multLow_low hνm.le hdvy
  have hlowx0 : (lam * x) % 7 ^ m ≠ 0 := by
    rw [hlowx]
    intro hc
    have hd : 7 ^ m ∣ x := Nat.dvd_of_mod_eq_zero hc
    have hle : m ≤ padicValNat 7 x :=
      (Nat.pow_dvd_iff_le_padicValNat (by norm_num) hx0).mp hd
    rw [hxν] at hle
    omega
  have hlowy0 : (lam * y) % 7 ^ m ≠ 0 := by
    rw [hlowy]
    intro hc
    have hd : 7 ^ m ∣ y := Nat.dvd_of_mod_eq_zero hc
    have hle : m ≤ padicValNat 7 y :=
      (Nat.pow_dvd_iff_le_padicValNat (by norm_num) hy0).mp hd
    rw [hyν] at hle
    omega
  have eval : ∀ {u v A B : ℕ},
      ((lam * eMod7 m u v : ℕ) : ZMod (7 ^ (m + 1)))
        = (A : ZMod _) - (B : ZMod _) →
      qdig7 m (eMod7 m (lam * u) (lam * v))
        = qdig7 m A - qdig7 m B
          - if A % 7 ^ m < B % 7 ^ m then (1 : ZMod 7) else 0 := by
    intro u v A B hcast
    rw [eMod7_smul hlam0, qdig7_congr (Nat.mod_mod _ _)]
    exact qdig_smul_eMod_eq hcast
  have key : ∀ u ∈ ({b1, b2, b3} : Finset ℕ),
      ∀ v ∈ ({b1, b2, b3} : Finset ℕ),
      qdig7 m (eMod7 m (lam * u) (lam * v))
        ∈ ({0, 1, 5, 6} : Finset (ZMod 7)) := by
    intro u hu v hv
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton]
      at hu hv
    rcases hu with hu' | hu' | hu' <;> rcases hv with hv' | hv' | hv' <;>
      rw [hu', hv']
    · rw [eMod7_self, qdig7_zero]; decide
    · -- (b1,b2): `λx − λy` — `qx+2qy+4t ∈ {0,1,6}` minus borrow
      have hcast : ((lam * eMod7 m b1 b2 : ℕ) : ZMod (7 ^ (m + 1)))
          = ((lam * x : ℕ) : ZMod _) - ((lam * y : ℕ) : ZMod _) := by
        simp only [Nat.cast_mul]
        rw [hc12]; ring
      rw [eval hcast, hqx, hqy]
      have hsimp : qdig7 m x + 2 * qdig7 m y + 5 * t - t
          = qdig7 m x + 2 * qdig7 m y + 4 * t := by ring
      rw [hsimp]
      by_cases hδ : lam * x % 7 ^ m < lam * y % 7 ^ m
      · rw [if_pos hδ]
        exact sub_borrow_mem_0156 hdxy (Or.inr rfl)
      · rw [if_neg hδ]
        exact sub_borrow_mem_0156 hdxy (Or.inl rfl)
    · -- (b1,b3): `q(λx) = qx+2qy+5t ∈ {0,1,5,6}`
      rw [eMod7_smul hlam0, qdig7_congr (Nat.mod_mod _ _), ← hx, hqx]
      exact htx
    · -- (b2,b1): `λy − λx` — `−(qx+2qy+4t)` minus borrow
      have hcast : ((lam * eMod7 m b2 b1 : ℕ) : ZMod (7 ^ (m + 1)))
          = ((lam * y : ℕ) : ZMod _) - ((lam * x : ℕ) : ZMod _) := by
        simp only [Nat.cast_mul]
        rw [hc21]; ring
      rw [eval hcast, hqy, hqx]
      have hsimp : t - (qdig7 m x + 2 * qdig7 m y + 5 * t)
          = -(qdig7 m x + 2 * qdig7 m y + 4 * t) := by ring
      rw [hsimp]
      by_cases hδ : lam * y % 7 ^ m < lam * x % 7 ^ m
      · rw [if_pos hδ]
        exact sub_borrow_mem_0156 (neg_mem_016 hdxy) (Or.inr rfl)
      · rw [if_neg hδ]
        exact sub_borrow_mem_0156 (neg_mem_016 hdxy) (Or.inl rfl)
    · rw [eMod7_self, qdig7_zero]; decide
    · -- (b2,b3): `q(λy) = t ∈ {0,5,6} ⊆ {0,1,5,6}`
      rw [eMod7_smul hlam0, qdig7_congr (Nat.mod_mod _ _), ← hy, hqy]
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht ⊢
      rcases ht with rfl | rfl | rfl <;> decide
    · -- (b3,b1): `−λx`, borrow forced
      have hcast : ((lam * eMod7 m b3 b1 : ℕ) : ZMod (7 ^ (m + 1)))
          = ((0 : ℕ) : ZMod _) - ((lam * x : ℕ) : ZMod _) := by
        simp only [Nat.cast_mul, Nat.cast_zero]
        rw [hc31]; ring
      rw [eval hcast, qdig7_zero, Nat.zero_mod,
        if_pos (Nat.pos_of_ne_zero hlowx0), hqx]
      have hsimp : (0 : ZMod 7) - (qdig7 m x + 2 * qdig7 m y + 5 * t) - 1
          = -(qdig7 m x + 2 * qdig7 m y + 5 * t) - 1 := by ring
      rw [hsimp]
      exact neg_sub_one_mem_0156 htx
    · -- (b3,b2): `−λy`
      have hcast : ((lam * eMod7 m b3 b2 : ℕ) : ZMod (7 ^ (m + 1)))
          = ((0 : ℕ) : ZMod _) - ((lam * y : ℕ) : ZMod _) := by
        simp only [Nat.cast_mul, Nat.cast_zero]
        rw [hc32]; ring
      rw [eval hcast, qdig7_zero, Nat.zero_mod,
        if_pos (Nat.pos_of_ne_zero hlowy0), hqy]
      have hsimp : (0 : ZMod 7) - t - 1 = -t - 1 := by ring
      rw [hsimp]
      exact neg_sub_one_mem_056 ht
    · rw [eMod7_self, qdig7_zero]; decide
  set BL : Finset ℕ := ({b1, b2, b3} : Finset ℕ).image (lam * ·)
    with hBLdef
  have hBLsame : ∀ u ∈ BL, ∀ v ∈ BL,
      residueRelOf u v = residueRel.same := by
    intro u hu v hv
    obtain ⟨u', hu', rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨v', hv', rfl⟩ := Finset.mem_image.mp hv
    apply rel_same _ (mul_ne_zero hlamne (ne_of_gt (hposB v' hv')))
    rw [runit7_mul, runit7_mul, hlam1, one_mul, one_mul,
      hr_all u' hu', hr_all v' hv']
  have hBL : ∀ u ∈ BL, ∀ v ∈ BL,
      qdig7 m (eMod7 m u v) ∈ ({0, 1, 5, 6} : Finset (ZMod 7)) := by
    intro u hu v hv
    obtain ⟨u', hu', rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨v', hv', rfl⟩ := Finset.mem_image.mp hv
    exact key u' hu' v' hv'
  have hdiff := remark8_ii_int hBLsame hBL
  have hlen : apLen (BL.image (qdig7 m)) ≤ 3 := remark8_ii' hdiff
  have himg : BL.image (qdig7 m)
      = ({b1, b2, b3} : Finset ℕ).image
        (fun d => qdig7 m (lam * d)) := by
    rw [hBLdef, Finset.image_image]
    exact Finset.image_congr fun d _ => rfl
  refine ⟨k, lam, hk7, hlam7, hlamdef, ?_, ?_, ?_⟩
  · rw [eMod7_smul hlam0, qdig7_congr (Nat.mod_mod _ _), ← hy, hqy]
    exact ht
  · intro x' hx' y' hy'
    exact hBL _ (Finset.mem_image.mpr ⟨x', hx', rfl⟩)
      _ (Finset.mem_image.mpr ⟨y', hy', rfl⟩)
  · rw [himg] at hlen
    exact hlen

end LRC7L10

