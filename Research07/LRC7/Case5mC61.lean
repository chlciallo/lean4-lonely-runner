/-
Copyright (c) 2026 Research07 contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Research07 contributors
-/
import Research07.LRC7.Case5mTop
import Research07.LRC7.Case5mL9b

/-!
# Paper §6.1 — the single-class case (Barajas–Serra)

For `A` a five-element `Finset ℕ` of positive `7`-adic units all sharing one
residue class `runit7 d = s ∈ {1,2,4}`, some `7`-unit multiplier `λ` is
`good7` (every scaled leading digit avoids `{0,6}`).

Lemma 10 (the four-element labelling) and Lemma 9(ii) (the equal-level
3-compression) are taken as *hypotheses* `h10`, `h9ii` — they are proven
elsewhere; this file only assembles them.

## Structure

* `case61_dichot_nat` — the `×3` carry dichotomy on the *real* low parts
  `fᵢ = (λ'bᵢ) % 7^m < 7^m`.  The existing `case61_dichot`/`'` are stated on
  normalized `f : ZMod 7` (the `m = 1` model); for `m ≥ 2` the real borrow
  compares `fᵢ < fⱼ` on naturals, so a fresh `ℕ`-valued version is proved
  (same two-alternative proof; numerically verified for `m = 1, 2`
  exhaustively, `m = 3` sampled).
* `case61_tail` — given a compressed triple `{b1,b2,b3} ⊆ A` (pairwise
  `eMod7`-digits in `{0,1,6}` and `apLen ≤ 2` after `lam₁`), produce the good
  multiplier: Λ₀-shift into `{0,6}` (`exists_lambda0_qdig_06`), pair digits
  verbatim under `Λ₀` (their `e` is divisible by `7`), then either
  `apLen_pair06_le` (`{q₄,q₅} ≠ {2,4}`) or the `×3` dichotomy
  (`{q₄,q₅} = {2,4}`), closing via `good7_of_smul_apLen`.
* `case61` — `case61_caseB` for the top-level alternative; otherwise `h10`
  gives `(d1,d2,d3,d4)` with either `ν(e21) > ν(e31)` (Lemma 9(i′), or a
  direct `Λ`/`scalar` normalization when `e31 = 0`) or the uniform-level
  ratio configuration (Lemma 9(ii) at `j = 2`, or the collapse `e21 = 0`
  where `d2,d3,d4 ≡ d1` and `e51` carries the sub-`m` level).
-/

private instance : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩

/-! ### Private clones of low-level helpers -/

/-- `(a·7^m + b) / 7^m = a` when `b < 7^m` (local copy). -/
private theorem mul_pow_add_div {a b m : ℕ} (hb : b < 7 ^ m) :
    (a * 7 ^ m + b) / 7 ^ m = a := by
  have hP : 0 < 7 ^ m := Nat.pow_pos (by norm_num)
  rw [add_comm (a * 7 ^ m) b, mul_comm a (7 ^ m),
    Nat.add_mul_div_left _ _ hP, Nat.div_eq_of_lt hb, zero_add]

/-- Decompose `x % 7^{m+1}` as `q·7^m + f` with `q < 7`, `f < 7^m`
(local copy). -/
private theorem residue_decomp {m x : ℕ} :
    ∃ q f : ℕ, x % 7 ^ (m + 1) = q * 7 ^ m + f ∧ q < 7 ∧ f < 7 ^ m := by
  refine ⟨(x % 7 ^ (m + 1)) / 7 ^ m, (x % 7 ^ (m + 1)) % 7 ^ m, ?_, ?_,
    Nat.mod_lt _ (Nat.pow_pos (by norm_num))⟩
  · rw [mul_comm, Nat.div_add_mod]
  · rw [Nat.div_lt_iff_lt_mul (Nat.pow_pos (by norm_num)), ← pow_succ']
    exact Nat.mod_lt _ (Nat.pow_pos (by norm_num))

/-- Cast a truncated-subtraction digit expression into `ZMod 7`
(local copy). -/
private theorem natCast_sub_add {a b c : ℕ} (h : c ≤ a + b) :
    ((a + b - c : ℕ) : ZMod 7) = (a : ZMod 7) + b - c := by
  have hcast : ((a + b - c : ℕ) : ZMod 7)
      = (((a + b - c : ℕ) : ℤ) : ZMod 7) := by simp
  rw [hcast, Int.ofNat_sub h]
  push_cast
  ring

/-- **Exact borrow formula** (local copy of `Case5mL9.qdig7_sub_resid`):
`q((a%N + N − b%N)) = q(a) − q(b) − (f_a < f_b ? 1 : 0)`. -/
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
  · have hexp : (q1 + 6 - q2) * 7 ^ m = q1 * 7 ^ m + 6 * 7 ^ m - q2 * 7 ^ m := by
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
    rw [ite_eq_left (by rwa [hf1e, hf2e] : a % 7 ^ m < b % 7 ^ m)]
  · have hge : f2 ≤ f1 := Nat.le_of_not_gt hb
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
    rw [ite_eq_right (by rwa [hf1e, hf2e] : ¬ a % 7 ^ m < b % 7 ^ m)]
    ring

/-- `eMod7` is bounded by the modulus. -/
private theorem eMod7_lt (m x y : ℕ) : eMod7 m x y < 7 ^ (m + 1) := by
  unfold eMod7
  split_ifs <;> exact Nat.mod_lt _ (Nat.pow_pos (by norm_num))

/-- `eMod7 m x x = 0` for positive `x`. -/
private theorem eMod7_self {m x : ℕ} (hx : 0 < x) : eMod7 m x x = 0 := by
  have hr : runit7 x ≠ 0 := runit7_ne_zero hx
  have hne : runit7 x ≠ 2 * runit7 x := by
    intro hcon
    apply hr
    have e : runit7 x - 2 * runit7 x = 0 := sub_eq_zero.mpr hcon
    have e2 : runit7 x - 2 * runit7 x = - runit7 x := by ring
    rw [e2] at e
    exact neg_eq_zero.mp e
  unfold eMod7
  rw [if_neg hne, if_neg hne, Nat.add_sub_cancel_left, Nat.mod_self]

/-- `runit7 0 = 0`. -/
private theorem runit7_zero : runit7 0 = 0 := by
  unfold runit7
  simp

/-- `runit7 x = 0` forces `x = 0`. -/
private theorem eq_zero_of_runit7_eq_zero {x : ℕ} (h : runit7 x = 0) : x = 0 := by
  rcases Nat.eq_zero_or_pos x with h0 | h0
  · exact h0
  · exact absurd h (runit7_ne_zero h0)

/-- Equal `runit7` forces the `same` branch (nonzero `runit7`). -/
private theorem rel_same {u v : ℕ} (h : runit7 u = runit7 v) (hv : runit7 v ≠ 0) :
    residueRelOf u v = residueRel.same := by
  rw [residueRelOf_eq_same]
  refine ⟨?_, ?_⟩ <;> intro hcon <;> rw [h] at hcon <;>
    · have hz : runit7 v = 0 := by
        have e : runit7 v - 2 * runit7 v = 0 := sub_eq_zero.mpr hcon
        have e2 : runit7 v - 2 * runit7 v = - runit7 v := by ring
        rw [e2] at e
        exact neg_eq_zero.mp e
      exact hv hz

/-- In the `same` branch, `eMod7` is the wrapped difference. -/
private theorem eMod7_same_eq {m x y : ℕ}
    (h : residueRelOf x y = residueRel.same) :
    eMod7 m x y
      = (x % 7 ^ (m + 1) + 7 ^ (m + 1) - y % 7 ^ (m + 1)) % 7 ^ (m + 1) := by
  obtain ⟨h1, h2⟩ := (residueRelOf_eq_same).mp h
  unfold eMod7
  rw [if_neg h1, if_neg h2]

/-- `qdig7` of a reduced residue is the unreduced digit (mod invariance). -/
private theorem qdig7_mod' {m w : ℕ} :
    qdig7 m (w % 7 ^ (m + 1)) = qdig7 m w :=
  qdig7_congr (Nat.mod_mod _ _)

/-- In the `same` branch, the `eMod7`-digit is `q(u) − q(v) − borrow`. -/
private theorem qdig7_eMod_same {m u v : ℕ}
    (h : residueRelOf u v = residueRel.same) :
    qdig7 m (eMod7 m u v) = qdig7 m u - qdig7 m v
      - (if u % 7 ^ m < v % 7 ^ m then (1 : ZMod 7) else 0) := by
  rw [eMod7_same_eq h, qdig7_mod']
  exact qdig7_sub_resid

/-- `eMod7` casts to the plain difference in `ZMod 7` (same branch). -/
private theorem eMod7_zmod7_same {m u v : ℕ}
    (h : residueRelOf u v = residueRel.same) :
    ((eMod7 m u v : ℕ) : ZMod 7) = (u : ZMod 7) - v := by
  obtain ⟨h1, h2⟩ := (residueRelOf_eq_same).mp h
  have h7N : (7 : ℕ) ∣ 7 ^ (m + 1) := pow_dvd_pow 7 (Nat.succ_le_succ (Nat.zero_le m))
  have hcast : ∀ a : ℕ, ((a % 7 ^ (m + 1) : ℕ) : ZMod 7) = (a : ZMod 7) := by
    intro a
    rw [ZMod.natCast_eq_natCast_iff']
    exact Nat.mod_mod_of_dvd a h7N
  unfold eMod7
  rw [if_neg h1, if_neg h2, hcast]
  rw [Nat.cast_sub (by
    have : v % 7 ^ (m + 1) < 7 ^ (m + 1) := Nat.mod_lt _ (Nat.pow_pos (by norm_num))
    omega)]
  rw [Nat.cast_add, hcast, hcast]
  have hN : ((7 ^ (m + 1) : ℕ) : ZMod 7) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr h7N
  rw [hN, add_zero]

/-- For a `same` pair with equal `ZMod 7` images, `7 ∣ eMod7`. -/
private theorem dvd7_eMod7_of_same {m x y : ℕ}
    (hrel : residueRelOf x y = residueRel.same)
    (hxy : (x : ZMod 7) = (y : ZMod 7)) : 7 ∣ eMod7 m x y := by
  have hcast := eMod7_zmod7_same (m := m) hrel
  rw [hxy, sub_self] at hcast
  exact (ZMod.natCast_eq_zero_iff _ _).mp hcast

/-- `Λ₀`-multiplication is verbatim on `eMod7` when `7 ∣ e` (same-class
pairs always satisfy this, since `e ≡ x − y ≡ 0 (mod 7)`). -/
private theorem eMod7_multLow0 {m k x y : ℕ} (hm : 0 < m)
    (hd : 7 ∣ eMod7 m x y) :
    eMod7 m ((1 + k * 7 ^ m) * x) ((1 + k * 7 ^ m) * y) = eMod7 m x y := by
  have h1 : runit7 (1 + k * 7 ^ m) = 1 := by
    have h := runit7_multLow (m := m) (j := 0) (k := k) hm
    rwa [Nat.sub_zero] at h
  rw [eMod7_mul h1]
  obtain ⟨e', he'⟩ := hd
  have hlt : eMod7 m x y < 7 ^ (m + 1) := eMod7_lt _ _ _
  have hdec : (1 + k * 7 ^ m) * eMod7 m x y
      = eMod7 m x y + (k * e') * 7 ^ (m + 1) := by
    rw [he', pow_succ' 7 m]
    ring
  rw [hdec]
  exact (Nat.add_mul_mod_self_right _ _ _).trans (Nat.mod_eq_of_lt hlt)

/-- `eMod7 = 0` in the `same` branch forces equal residues. -/
private theorem eq_resid_of_eMod7_eq_zero {m x y : ℕ}
    (h : eMod7 m x y = 0) (hrel : residueRelOf x y = residueRel.same) :
    x % 7 ^ (m + 1) = y % 7 ^ (m + 1) := by
  rw [eMod7_same_eq hrel] at h
  have hx : x % 7 ^ (m + 1) < 7 ^ (m + 1) := Nat.mod_lt _ (Nat.pow_pos (by norm_num))
  have hy : y % 7 ^ (m + 1) < 7 ^ (m + 1) := Nat.mod_lt _ (Nat.pow_pos (by norm_num))
  have hdvd : 7 ^ (m + 1) ∣
      x % 7 ^ (m + 1) + 7 ^ (m + 1) - y % 7 ^ (m + 1) :=
    Nat.dvd_of_mod_eq_zero h
  obtain ⟨k, hk⟩ := hdvd
  have hk1 : k = 1 := by
    have h1 : 0 < x % 7 ^ (m + 1) + 7 ^ (m + 1) - y % 7 ^ (m + 1) := by omega
    have h2 : x % 7 ^ (m + 1) + 7 ^ (m + 1) - y % 7 ^ (m + 1) <
        2 * 7 ^ (m + 1) := by omega
    rw [hk] at h1 h2
    rcases k with _ | _ | k
    · simp at h1
    · rfl
    · have : 7 ^ (m + 1) * (k + 1 + 1) ≥ 7 ^ (m + 1) * 2 := by
        apply Nat.mul_le_mul_left; omega
      omega
  rw [hk1, mul_one] at hk
  omega

/-- `eMod7` is insensitive to `y`'s exact value given its residue and
`runit7`. -/
private theorem eMod7_congr_right {m x y z : ℕ}
    (hres : y % 7 ^ (m + 1) = z % 7 ^ (m + 1)) (hr : runit7 y = runit7 z) :
    eMod7 m x y = eMod7 m x z := by
  unfold eMod7
  rw [hr, hres]

/-- `eMod7` is insensitive to `x`'s exact value given its residue and
`runit7`. -/
private theorem eMod7_congr_left {m x y z : ℕ}
    (hres : y % 7 ^ (m + 1) = z % 7 ^ (m + 1)) (hr : runit7 y = runit7 z) :
    eMod7 m y x = eMod7 m z x := by
  unfold eMod7
  rw [hr, hres]

/-- Exact `×3` carry formula: `q(3x) = 3·q(x) + ⌊3f/7^m⌋` where
`f = x % 7^m`. -/
private theorem qdig7_three_mul {m x : ℕ} :
    qdig7 m (3 * x)
      = 3 * qdig7 m x + ((3 * (x % 7 ^ m) / 7 ^ m : ℕ) : ZMod 7) := by
  have hP : 0 < 7 ^ m := Nat.pow_pos (by norm_num)
  have hx : 3 * x = 3 * (x % 7 ^ m) + 7 ^ m * (3 * (x / 7 ^ m)) := by
    conv_lhs => rw [← Nat.div_add_mod x (7 ^ m)]
    ring
  rw [qdig7_eq_cast_div, hx, Nat.add_mul_div_left _ _ hP, qdig7_eq_cast_div]
  push_cast
  ring

/-- `qdig7 m 0 = 0`. -/
private theorem qdig7_zero (m : ℕ) : qdig7 m 0 = 0 := by
  unfold qdig7
  simp

/-! ### Small `ZMod 7` finite facts (decide) -/

private theorem mem016_of_mem06 {q : ZMod 7}
    (h : q ∈ ({0, 6} : Finset (ZMod 7))) :
    q ∈ ({0, 1, 6} : Finset (ZMod 7)) := by
  have hsub : ({0, 6} : Finset (ZMod 7)) ⊆ ({0, 1, 6} : Finset (ZMod 7)) := by
    decide
  exact hsub h

private theorem sub06_back {z : ZMod 7}
    (h : (6 : ZMod 7) - z ∈ ({0, 6} : Finset (ZMod 7))) :
    z ∈ ({0, 6} : Finset (ZMod 7)) := by
  revert z h
  decide

private theorem neg06_mem01 {z : ZMod 7}
    (h : z ∈ ({0, 6} : Finset (ZMod 7))) :
    -z ∈ ({0, 1} : Finset (ZMod 7)) := by
  revert z h
  decide

private theorem add016 {a b : ZMod 7} (ha : a ∈ ({0, 1} : Finset (ZMod 7)))
    (hb : b ∈ ({0, 6} : Finset (ZMod 7))) :
    a + b ∈ ({0, 1, 6} : Finset (ZMod 7)) := by
  revert a b ha hb
  decide

private theorem val_lt2_of_mem01 {q : ZMod 7}
    (h : q ∈ ({0, 1} : Finset (ZMod 7))) : q.val < 2 := by
  revert q h
  decide

/-- A `{2,4}`-digit times 3 plus carry `< 3` lands in `{0,1,5,6}`. -/
private theorem mem24_carry {q : ZMod 7} {c : ℕ}
    (hq : q ∈ ({2, 4} : Finset (ZMod 7))) (hc : c < 3) :
    3 * q + (c : ZMod 7) ∈ ({0, 1, 5, 6} : Finset (ZMod 7)) := by
  rcases Finset.mem_insert.mp hq with rfl | h4
  · interval_cases c <;> decide
  · rw [Finset.mem_singleton] at h4
    subst h4
    interval_cases c <;> decide

/-- `{0,1,2,5,6}` fits in a `5`-interval (misses `{3,4}`). -/
private theorem apLen_T1 : apLen ({0, 1, 2, 5, 6} : Finset (ZMod 7)) ≤ 5 := by
  decide

/-- `{0,1,4,5,6}` fits in a `5`-interval (misses `{2,3}`). -/
private theorem apLen_T2 : apLen ({0, 1, 4, 5, 6} : Finset (ZMod 7)) ≤ 5 := by
  decide

/-- `apLen` never exceeds `7`. -/
private theorem apLen_le7 (X : Finset (ZMod 7)) : apLen X ≤ 7 := by
  refine (apLen_le_iff X 7 le_rfl).mpr ⟨0, fun x _ => ?_⟩
  rw [mem_cycIv, sub_zero]
  exact ZMod.val_lt x

/-- `apLen` is monotone under inclusion. -/
private theorem apLen_mono' {X Y : Finset (ZMod 7)} (hXY : X ⊆ Y) :
    apLen X ≤ apLen Y := by
  have h7 := apLen_le7 Y
  obtain ⟨i, hi⟩ := (apLen_le_iff Y (apLen Y) h7).mp le_rfl
  exact (apLen_le_iff X (apLen Y) h7).mpr ⟨i, hXY.trans hi⟩

/-! ### The `×3` dichotomy on real low parts -/

/-- First alternative element bound: `q ∈ {0,6}` with `c := ⌊3f/7^m⌋`,
`c < 3`, and `q = 6 → c ≥ 1` implies `3q + c ∈ {0,1,2,5,6}`. -/
private theorem case61_mem_t1_nat {q : ZMod 7} {c : ℕ}
    (hq : q ∈ ({0, 6} : Finset (ZMod 7))) (hc : c < 3)
    (h6 : q = 6 → 1 ≤ c) :
    3 * q + (c : ZMod 7) ∈ ({0, 1, 2, 5, 6} : Finset (ZMod 7)) := by
  rcases Finset.mem_insert.mp hq with rfl | h6m
  · rw [mul_zero, zero_add]
    interval_cases c <;> decide
  · rw [Finset.mem_singleton] at h6m
    subst h6m
    have hc1 := h6 rfl
    interval_cases c <;> decide

/-- Second alternative element bound: `q ∈ {0,6}` with `c < 3` and
`q = 0 → c = 0` implies `3q + c ∈ {0,1,4,5,6}`. -/
private theorem case61_mem_t2_nat {q : ZMod 7} {c : ℕ}
    (hq : q ∈ ({0, 6} : Finset (ZMod 7))) (hc : c < 3)
    (h0 : q = 0 → c = 0) :
    3 * q + (c : ZMod 7) ∈ ({0, 1, 4, 5, 6} : Finset (ZMod 7)) := by
  rcases Finset.mem_insert.mp hq with rfl | h6m
  · rw [h0 rfl]
    decide
  · rw [Finset.mem_singleton] at h6m
    subst h6m
    interval_cases c <;> decide

/-- The `×3` dichotomy on real low parts: for three `qᵢ ∈ {0,6}` whose low
parts `fᵢ < 7^m` satisfy all six ordered pair-difference constraints
`qᵢ − qⱼ − (fᵢ < fⱼ ? 1 : 0) ∈ {0,1,6}`, the scaled digits
`3qᵢ + ⌊3fᵢ/7^m⌋` all lie in `{0,1,2,5,6}` or all in `{0,1,4,5,6}`.

Constraint content: a `(6,0)`-pair forces `f₀ ≤ f₆` (the borrow must be `0`
since `6 − 1 = 5 ∉ {0,1,6}`).  If every `6`-digit has `3f ≥ 7^m` (carry `≥1`)
the first alternative holds; otherwise a `6`-digit witness `3fⱼ < 7^m` forces
every `0`-digit `fᵢ ≤ fⱼ`, hence carry `0`. -/
private theorem case61_dichot_nat {m : ℕ} {q₁ q₂ q₃ : ZMod 7} {f₁ f₂ f₃ : ℕ}
    (hf₁ : f₁ < 7 ^ m) (hf₂ : f₂ < 7 ^ m) (hf₃ : f₃ < 7 ^ m)
    (hq₁ : q₁ ∈ ({0, 6} : Finset (ZMod 7)))
    (hq₂ : q₂ ∈ ({0, 6} : Finset (ZMod 7)))
    (hq₃ : q₃ ∈ ({0, 6} : Finset (ZMod 7)))
    (h₁₂ : q₁ - q₂ - (if f₁ < f₂ then (1 : ZMod 7) else 0)
      ∈ ({0, 1, 6} : Finset (ZMod 7)))
    (h₁₃ : q₁ - q₃ - (if f₁ < f₃ then (1 : ZMod 7) else 0)
      ∈ ({0, 1, 6} : Finset (ZMod 7)))
    (h₂₁ : q₂ - q₁ - (if f₂ < f₁ then (1 : ZMod 7) else 0)
      ∈ ({0, 1, 6} : Finset (ZMod 7)))
    (h₂₃ : q₂ - q₃ - (if f₂ < f₃ then (1 : ZMod 7) else 0)
      ∈ ({0, 1, 6} : Finset (ZMod 7)))
    (h₃₁ : q₃ - q₁ - (if f₃ < f₁ then (1 : ZMod 7) else 0)
      ∈ ({0, 1, 6} : Finset (ZMod 7)))
    (h₃₂ : q₃ - q₂ - (if f₃ < f₂ then (1 : ZMod 7) else 0)
      ∈ ({0, 1, 6} : Finset (ZMod 7))) :
    (3 * q₁ + ((3 * f₁ / 7 ^ m : ℕ) : ZMod 7) ∈ ({0, 1, 2, 5, 6} : Finset (ZMod 7)) ∧
     3 * q₂ + ((3 * f₂ / 7 ^ m : ℕ) : ZMod 7) ∈ ({0, 1, 2, 5, 6} : Finset (ZMod 7)) ∧
     3 * q₃ + ((3 * f₃ / 7 ^ m : ℕ) : ZMod 7) ∈ ({0, 1, 2, 5, 6} : Finset (ZMod 7))) ∨
    (3 * q₁ + ((3 * f₁ / 7 ^ m : ℕ) : ZMod 7) ∈ ({0, 1, 4, 5, 6} : Finset (ZMod 7)) ∧
     3 * q₂ + ((3 * f₂ / 7 ^ m : ℕ) : ZMod 7) ∈ ({0, 1, 4, 5, 6} : Finset (ZMod 7)) ∧
     3 * q₃ + ((3 * f₃ / 7 ^ m : ℕ) : ZMod 7) ∈ ({0, 1, 4, 5, 6} : Finset (ZMod 7))) := by
  have hP : 0 < 7 ^ m := Nat.pow_pos (by norm_num)
  have hc₁ : 3 * f₁ / 7 ^ m < 3 :=
    Nat.div_lt_of_lt_mul (by
      have h := Nat.mul_lt_mul_of_pos_left hf₁ (show (0 : ℕ) < 3 by norm_num)
      omega)
  have hc₂ : 3 * f₂ / 7 ^ m < 3 :=
    Nat.div_lt_of_lt_mul (by
      have h := Nat.mul_lt_mul_of_pos_left hf₂ (show (0 : ℕ) < 3 by norm_num)
      omega)
  have hc₃ : 3 * f₃ / 7 ^ m < 3 :=
    Nat.div_lt_of_lt_mul (by
      have h := Nat.mul_lt_mul_of_pos_left hf₃ (show (0 : ℕ) < 3 by norm_num)
      omega)
  -- `(6,0)`-pair forces `f₀ ≤ f₆`.
  have key : ∀ {a b : ℕ} {qa qb : ZMod 7}, qa = 6 → qb = 0 →
      qa - qb - (if a < b then (1 : ZMod 7) else 0)
        ∈ ({0, 1, 6} : Finset (ZMod 7)) → b ≤ a := by
    intro a b qa qb hqa hqb h
    rw [hqa, hqb] at h
    by_contra hlt
    rw [if_pos (not_le.mp hlt)] at h
    exact absurd h (by decide)
  have h6bound : ∀ (q : ZMod 7) (f : ℕ), q = 6 → 7 ^ m ≤ 3 * f →
      1 ≤ 3 * f / 7 ^ m := fun q f _ hf => by
    exact (Nat.le_div_iff_mul_le hP).mpr (by simpa using hf)
  by_cases hall : (q₁ = 6 → 7 ^ m ≤ 3 * f₁) ∧ (q₂ = 6 → 7 ^ m ≤ 3 * f₂) ∧
      (q₃ = 6 → 7 ^ m ≤ 3 * f₃)
  · left
    exact ⟨case61_mem_t1_nat hq₁ hc₁ (fun h => h6bound q₁ f₁ h (hall.1 h)),
      case61_mem_t1_nat hq₂ hc₂ (fun h => h6bound q₂ f₂ h (hall.2.1 h)),
      case61_mem_t1_nat hq₃ hc₃ (fun h => h6bound q₃ f₃ h (hall.2.2 h))⟩
  · right
    have hall' : ¬ (q₁ = 6 → 7 ^ m ≤ 3 * f₁) ∨
        ¬ (q₂ = 6 → 7 ^ m ≤ 3 * f₂) ∨ ¬ (q₃ = 6 → 7 ^ m ≤ 3 * f₃) := by
      by_contra hcon
      push_neg at hcon
      exact hall ⟨hcon.1, hcon.2.1, hcon.2.2⟩
    rcases hall' with h | h | h
    · obtain ⟨hq6, hf⟩ := not_imp.mp h
      have hf' : 3 * f₁ < 7 ^ m := not_le.mp hf
      refine ⟨case61_mem_t2_nat hq₁ hc₁ (fun h0 => absurd (h0 ▸ hq6) (by decide)),
        case61_mem_t2_nat hq₂ hc₂ (fun h0 => ?_),
        case61_mem_t2_nat hq₃ hc₃ (fun h0 => ?_)⟩
      · have hle : f₂ ≤ f₁ := key hq6 h0 h₁₂
        exact Nat.div_eq_of_lt (by omega)
      · have hle : f₃ ≤ f₁ := key hq6 h0 h₁₃
        exact Nat.div_eq_of_lt (by omega)
    · obtain ⟨hq6, hf⟩ := not_imp.mp h
      have hf' : 3 * f₂ < 7 ^ m := not_le.mp hf
      refine ⟨case61_mem_t2_nat hq₁ hc₁ (fun h0 => ?_),
        case61_mem_t2_nat hq₂ hc₂ (fun h0 => absurd (h0 ▸ hq6) (by decide)),
        case61_mem_t2_nat hq₃ hc₃ (fun h0 => ?_)⟩
      · have hle : f₁ ≤ f₂ := key hq6 h0 h₂₁
        exact Nat.div_eq_of_lt (by omega)
      · have hle : f₃ ≤ f₂ := key hq6 h0 h₂₃
        exact Nat.div_eq_of_lt (by omega)
    · obtain ⟨hq6, hf⟩ := not_imp.mp h
      have hf' : 3 * f₃ < 7 ^ m := not_le.mp hf
      refine ⟨case61_mem_t2_nat hq₁ hc₁ (fun h0 => ?_),
        case61_mem_t2_nat hq₂ hc₂ (fun h0 => ?_),
        case61_mem_t2_nat hq₃ hc₃ (fun h0 => absurd (h0 ▸ hq6) (by decide))⟩
      · have hle : f₁ ≤ f₃ := key hq6 h0 h₃₁
        exact Nat.div_eq_of_lt (by omega)
      · have hle : f₂ ≤ f₃ := key hq6 h0 h₃₂
        exact Nat.div_eq_of_lt (by omega)

/-! ### The tail: compressed triple → good multiplier -/

/-- Given `B = {b1,b2,b3} ⊆ A` compressed by `lam₁` (all pair `eMod7`
digits in `{0,1,6}`, `apLen ≤ 2` on the scaled digit image) and
`A ⊆ {b1,b2,b3,d4,d5}`, produce `∃ lam, ¬ 7 ∣ lam ∧ good7 m lam A`.

Steps: Λ₀-shift the triple digits into `{0,6}` (`exists_lambda0_qdig_06`);
pairwise `eMod7`s are verbatim under `Λ₀` (their values are `7`-divisible),
so the six borrow constraints survive; then `{q₄,q₅} ≠ {2,4}` finishes via
`apLen_pair06_le`, while `{2,4}` needs the `×3` dichotomy. -/
private theorem case61_tail {m : ℕ} (hm : 0 < m) {A : Finset ℕ}
    (hpos : ∀ d ∈ A, 0 < d) (hunit : ∀ d ∈ A, padicValNat 7 d = 0)
    {s : ZMod 7} (hs : s ≠ 0) (hcls : ∀ d ∈ A, runit7 d = s)
    {b1 b2 b3 d4 d5 : ℕ}
    (hb1 : b1 ∈ A) (hb2 : b2 ∈ A) (hb3 : b3 ∈ A)
    (hcover : A ⊆ ({b1, b2, b3, d4, d5} : Finset ℕ))
    {lam₁ : ℕ} (hlam₁ : ¬ 7 ∣ lam₁)
    (hpair : ∀ x ∈ ({b1, b2, b3} : Finset ℕ), ∀ y ∈ ({b1, b2, b3} : Finset ℕ),
      qdig7 m (eMod7 m (lam₁ * x) (lam₁ * y)) ∈ ({0, 1, 6} : Finset (ZMod 7)))
    (hap : apLen (({b1, b2, b3} : Finset ℕ).image (fun d => qdig7 m (lam₁ * d)))
      ≤ 2) :
    ∃ lam : ℕ, ¬ 7 ∣ lam ∧ good7 m lam A := by
  classical
  have hlam₁0 : lam₁ ≠ 0 := fun h => hlam₁ (h ▸ dvd_zero 7)
  have htriple : ∀ d ∈ ({b1, b2, b3} : Finset ℕ), d ∈ A := by
    intro d hd
    rcases Finset.mem_insert.mp hd with rfl | hd'
    · exact hb1
    rcases Finset.mem_insert.mp hd' with rfl | hd''
    · exact hb2
    rw [Finset.mem_singleton] at hd''
    exact hd'' ▸ hb3
  set B : Finset ℕ := ({b1, b2, b3} : Finset ℕ).image (fun d => lam₁ * d)
    with hB
  set s' : ZMod 7 := runit7 lam₁ * s with hs'
  have hs'0 : s' ≠ 0 :=
    mul_ne_zero (runit7_ne_zero (Nat.pos_of_ne_zero hlam₁0)) hs
  have hunitB : ∀ d' ∈ B, padicValNat 7 d' = 0 := by
    intro d' hd'
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hd'
    rw [padicValNat_mul_unit7 hlam₁0 (Nat.ne_of_gt (hpos d (htriple d hd)))
      hlam₁, hunit d (htriple d hd)]
  have hclsB : ∀ d' ∈ B, runit7 d' = s' := by
    intro d' hd'
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hd'
    rw [hs', runit7_mul, hcls d (htriple d hd)]
  have hapB : apLen (B.image (qdig7 m)) ≤ 2 := by
    rw [hB, Finset.image_image]
    exact hap
  obtain ⟨lam₀, hlam₀mem, hq06⟩ := exists_lambda0_qdig_06 hunitB hs'0 hclsB hapB
  have hlam₀nd : ¬ 7 ∣ lam₀ := not_dvd_of_mem_multLow7_zero hm hlam₀mem
  obtain ⟨K, hK7, hK⟩ := Finset.mem_image.mp hlam₀mem
  have hKlt : K < 7 := Finset.mem_range.mp hK7
  have hlam₀eq : lam₀ = 1 + K * 7 ^ m := by rw [← hK, Nat.sub_zero]
  have hr0 : runit7 lam₀ = 1 := by
    have h := runit7_multLow (m := m) (j := 0) (k := K) hm
    rw [Nat.sub_zero] at h
    rw [hlam₀eq]
    exact h
  set lam' := lam₀ * lam₁ with hlam'
  have hlam'nd : ¬ 7 ∣ lam' := by
    rw [hlam']
    exact Nat.Prime.not_dvd_mul Nat.prime_seven hlam₀nd hlam₁
  have hlam'0 : 0 < lam' := Nat.pos_of_ne_zero (fun h => hlam'nd (h ▸ dvd_zero 7))
  -- triple membership facts
  have hb1' : b1 ∈ ({b1, b2, b3} : Finset ℕ) := Finset.mem_insert_self _ _
  have hb2' : b2 ∈ ({b1, b2, b3} : Finset ℕ) :=
    Finset.mem_insert.mpr (Or.inr (Finset.mem_insert_self _ _))
  have hb3' : b3 ∈ ({b1, b2, b3} : Finset ℕ) :=
    Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr
      (Or.inr (Finset.mem_singleton_self _))))
  -- residueRelOf is `same` on scaled pairs of A-elements
  have hrel' : ∀ x ∈ A, ∀ y ∈ A,
      residueRelOf (lam' * x) (lam' * y) = residueRel.same := by
    intro x hx y hy
    apply rel_same _ (runit7_ne_zero (Nat.mul_pos hlam'0 (hpos y hy)))
    rw [runit7_mul lam' x, runit7_mul lam' y, hcls x hx, hcls y hy]
  -- the verbatim transport: pair digits survive `lam₀`
  have hpair' : ∀ x ∈ ({b1, b2, b3} : Finset ℕ), ∀ y ∈ ({b1, b2, b3} : Finset ℕ),
      qdig7 m (eMod7 m (lam' * x) (lam' * y)) ∈ ({0, 1, 6} : Finset (ZMod 7)) := by
    intro x hx y hy
    have hxpos : 0 < lam₁ * x := Nat.mul_pos (Nat.pos_of_ne_zero hlam₁0)
      (hpos x (htriple x hx))
    have hypos : 0 < lam₁ * y := Nat.mul_pos (Nat.pos_of_ne_zero hlam₁0)
      (hpos y (htriple y hy))
    have hrel : residueRelOf (lam₁ * x) (lam₁ * y) = residueRel.same := by
      apply rel_same _ (runit7_ne_zero hypos)
      rw [runit7_mul, runit7_mul, hcls x (htriple x hx), hcls y (htriple y hy)]
    have hxs : (x : ZMod 7) = s := by
      have h := hcls x (htriple x hx)
      unfold runit7 at h
      rw [hunit x (htriple x hx), pow_zero, Nat.div_one] at h
      exact h
    have hys : (y : ZMod 7) = s := by
      have h := hcls y (htriple y hy)
      unfold runit7 at h
      rw [hunit y (htriple y hy), pow_zero, Nat.div_one] at h
      exact h
    have h7e : 7 ∣ eMod7 m (lam₁ * x) (lam₁ * y) := by
      apply dvd7_eMod7_of_same hrel
      rw [Nat.cast_mul, Nat.cast_mul, hxs, hys]
    have hverb : eMod7 m (lam' * x) (lam' * y) = eMod7 m (lam₁ * x) (lam₁ * y) := by
      rw [hlam', mul_assoc lam₀ lam₁ x, mul_assoc lam₀ lam₁ y]
      rw [hlam₀eq]
      exact eMod7_multLow0 hm h7e
    rw [hverb]
    exact hpair x hx y hy
  -- the three digits and three low parts
  set q₁ := qdig7 m (lam' * b1) with hq₁def
  set q₂ := qdig7 m (lam' * b2) with hq₂def
  set q₃ := qdig7 m (lam' * b3) with hq₃def
  set f₁ := (lam' * b1) % 7 ^ m with hf₁def
  set f₂ := (lam' * b2) % 7 ^ m with hf₂def
  set f₃ := (lam' * b3) % 7 ^ m with hf₃def
  have hP : 0 < 7 ^ m := Nat.pow_pos (by norm_num)
  have hf₁lt : f₁ < 7 ^ m := hf₁def ▸ Nat.mod_lt _ hP
  have hf₂lt : f₂ < 7 ^ m := hf₂def ▸ Nat.mod_lt _ hP
  have hf₃lt : f₃ < 7 ^ m := hf₃def ▸ Nat.mod_lt _ hP
  have hq₁ : q₁ ∈ ({0, 6} : Finset (ZMod 7)) := by
    have hmem : lam₁ * b1 ∈ B :=
      Finset.mem_image.mpr ⟨b1, hb1', rfl⟩
    have h := hq06 _ hmem
    rw [hq₁def, hlam', mul_assoc]
    exact h
  have hq₂ : q₂ ∈ ({0, 6} : Finset (ZMod 7)) := by
    have hmem : lam₁ * b2 ∈ B :=
      Finset.mem_image.mpr ⟨b2, hb2', rfl⟩
    have h := hq06 _ hmem
    rw [hq₂def, hlam', mul_assoc]
    exact h
  have hq₃ : q₃ ∈ ({0, 6} : Finset (ZMod 7)) := by
    have hmem : lam₁ * b3 ∈ B :=
      Finset.mem_image.mpr ⟨b3, hb3', rfl⟩
    have h := hq06 _ hmem
    rw [hq₃def, hlam', mul_assoc]
    exact h
  -- the six borrow constraints
  have hcon : ∀ x ∈ ({b1, b2, b3} : Finset ℕ), ∀ y ∈ ({b1, b2, b3} : Finset ℕ),
      qdig7 m (lam' * x) - qdig7 m (lam' * y)
        - (if (lam' * x) % 7 ^ m < (lam' * y) % 7 ^ m then (1 : ZMod 7) else 0)
        ∈ ({0, 1, 6} : Finset (ZMod 7)) := by
    intro x hx y hy
    have hrel : residueRelOf (lam' * x) (lam' * y) = residueRel.same :=
      hrel' x (htriple x hx) y (htriple y hy)
    rw [← qdig7_eMod_same hrel]
    exact hpair' x hx y hy
  have h₁₂ := hcon b1 hb1' b2 hb2'
  have h₁₃ := hcon b1 hb1' b3 hb3'
  have h₂₁ := hcon b2 hb2' b1 hb1'
  have h₂₃ := hcon b2 hb2' b3 hb3'
  have h₃₁ := hcon b3 hb3' b1 hb1'
  have h₃₂ := hcon b3 hb3' b2 hb2'
  rw [← hq₁def, ← hq₂def, ← hf₁def, ← hf₂def] at h₁₂
  rw [← hq₁def, ← hq₃def, ← hf₁def, ← hf₃def] at h₁₃
  rw [← hq₂def, ← hq₁def, ← hf₂def, ← hf₁def] at h₂₁
  rw [← hq₂def, ← hq₃def, ← hf₂def, ← hf₃def] at h₂₃
  rw [← hq₃def, ← hq₁def, ← hf₃def, ← hf₁def] at h₃₁
  rw [← hq₃def, ← hq₂def, ← hf₃def, ← hf₂def] at h₃₂
  -- the two free digits
  set q₄ := qdig7 m (lam' * d4) with hq₄def
  set q₅ := qdig7 m (lam' * d5) with hq₅def
  -- the image bound reduces to the 5-element digit set
  have himg : ∀ (lam'' : ℕ), (A.image (fun d => lam'' * d)).image (qdig7 m)
      ⊆ ({qdig7 m (lam'' * b1), qdig7 m (lam'' * b2), qdig7 m (lam'' * b3),
        qdig7 m (lam'' * d4), qdig7 m (lam'' * d5)} : Finset (ZMod 7)) := by
    intro lam'' q hq
    obtain ⟨d', hd', rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨d, hdA, rfl⟩ := Finset.mem_image.mp hd'
    have hd5 := hcover hdA
    rcases Finset.mem_insert.mp hd5 with rfl | hd'
    · exact Finset.mem_insert_self _ _
    rcases Finset.mem_insert.mp hd' with rfl | hd''
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert_self _ _))
    rcases Finset.mem_insert.mp hd'' with rfl | hd'''
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr
        (Or.inr (Finset.mem_insert_self _ _))))
    rcases Finset.mem_insert.mp hd''' with rfl | hd''''
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr
        (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert_self _ _))))))
    rw [Finset.mem_singleton] at hd''''
    subst hd''''
    exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr
      (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr
        (Or.inr (Finset.mem_singleton_self _))))))))
  by_cases h24 : (q₄ = 2 ∧ q₅ = 4) ∨ (q₄ = 4 ∧ q₅ = 2)
  · -- the exceptional pair `{q₄,q₅} = {2,4}`: multiply by 3 and dichotomize
    have hq4 : q₄ ∈ ({2, 4} : Finset (ZMod 7)) := by
      rcases h24 with ⟨h, -⟩ | ⟨h, -⟩
      · exact Finset.mem_insert.mpr (Or.inl h)
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr h))
    have hq5 : q₅ ∈ ({2, 4} : Finset (ZMod 7)) := by
      rcases h24 with ⟨-, h⟩ | ⟨-, h⟩
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr h))
      · exact Finset.mem_insert.mpr (Or.inl h)
    -- ×3 digit formula and carry bound, unconditional on `d ∈ A`
    have hdig : ∀ d : ℕ, qdig7 m ((3 * lam') * d)
        = 3 * qdig7 m (lam' * d)
          + ((3 * ((lam' * d) % 7 ^ m) / 7 ^ m : ℕ) : ZMod 7) := by
      intro d
      rw [mul_assoc]
      exact qdig7_three_mul
    have hcarry : ∀ d : ℕ, 3 * ((lam' * d) % 7 ^ m) / 7 ^ m < 3 := fun d =>
      (Nat.div_lt_iff_lt_mul hP).mpr (by
        have h := Nat.mul_lt_mul_of_pos_left (Nat.mod_lt (lam' * d) hP)
          (show (0 : ℕ) < 3 by norm_num)
        omega)
    -- dichotomy gives a common target T for the triple
    have hcase :
        (3 * q₁ + ((3 * f₁ / 7 ^ m : ℕ) : ZMod 7) ∈
            ({0, 1, 2, 5, 6} : Finset (ZMod 7)) ∧
          3 * q₂ + ((3 * f₂ / 7 ^ m : ℕ) : ZMod 7) ∈
            ({0, 1, 2, 5, 6} : Finset (ZMod 7)) ∧
          3 * q₃ + ((3 * f₃ / 7 ^ m : ℕ) : ZMod 7) ∈
            ({0, 1, 2, 5, 6} : Finset (ZMod 7))) ∨
        (3 * q₁ + ((3 * f₁ / 7 ^ m : ℕ) : ZMod 7) ∈
            ({0, 1, 4, 5, 6} : Finset (ZMod 7)) ∧
          3 * q₂ + ((3 * f₂ / 7 ^ m : ℕ) : ZMod 7) ∈
            ({0, 1, 4, 5, 6} : Finset (ZMod 7)) ∧
          3 * q₃ + ((3 * f₃ / 7 ^ m : ℕ) : ZMod 7) ∈
            ({0, 1, 4, 5, 6} : Finset (ZMod 7))) :=
      case61_dichot_nat hf₁lt hf₂lt hf₃lt hq₁ hq₂ hq₃ h₁₂ h₁₃ h₂₁ h₂₃ h₃₁ h₃₂
    -- `{2,4}`-digits land in `{0,1,5,6}` after ×3
    have hd4' : qdig7 m ((3 * lam') * d4) ∈ ({0, 1, 5, 6} : Finset (ZMod 7)) := by
      rw [hdig d4, ← hq₄def]
      exact mem24_carry hq4 (hcarry d4)
    have hd5' : qdig7 m ((3 * lam') * d5) ∈ ({0, 1, 5, 6} : Finset (ZMod 7)) := by
      rw [hdig d5, ← hq₅def]
      exact mem24_carry hq5 (hcarry d5)
    have ht1 : qdig7 m ((3 * lam') * b1)
        = 3 * q₁ + ((3 * f₁ / 7 ^ m : ℕ) : ZMod 7) := by
      rw [hdig b1, ← hq₁def, ← hf₁def]
    have ht2 : qdig7 m ((3 * lam') * b2)
        = 3 * q₂ + ((3 * f₂ / 7 ^ m : ℕ) : ZMod 7) := by
      rw [hdig b2, ← hq₂def, ← hf₂def]
    have ht3 : qdig7 m ((3 * lam') * b3)
        = 3 * q₃ + ((3 * f₃ / 7 ^ m : ℕ) : ZMod 7) := by
      rw [hdig b3, ← hq₃def, ← hf₃def]
    -- subset transports for the two target sets
    have hsub56T1 : ({0, 1, 5, 6} : Finset (ZMod 7)) ⊆
        ({0, 1, 2, 5, 6} : Finset (ZMod 7)) := by decide
    have hsub56T2 : ({0, 1, 5, 6} : Finset (ZMod 7)) ⊆
        ({0, 1, 4, 5, 6} : Finset (ZMod 7)) := by decide
    -- the whole image lands in T1 or T2
    have hap5 : apLen ((A.image (fun d => (3 * lam') * d)).image (qdig7 m))
        ≤ 5 := by
      rcases hcase with ⟨t1, t2, t3⟩ | ⟨t1, t2, t3⟩
      · have hsub : (A.image (fun d => (3 * lam') * d)).image (qdig7 m)
            ⊆ ({0, 1, 2, 5, 6} : Finset (ZMod 7)) := by
          intro q hq
          obtain ⟨d', hd', rfl⟩ := Finset.mem_image.mp hq
          obtain ⟨d, hdA, rfl⟩ := Finset.mem_image.mp hd'
          have hd5 := hcover hdA
          rcases Finset.mem_insert.mp hd5 with rfl | hd'
          · rw [ht1]
            exact t1
          rcases Finset.mem_insert.mp hd' with rfl | hd''
          · rw [ht2]
            exact t2
          rcases Finset.mem_insert.mp hd'' with rfl | hd'''
          · rw [ht3]
            exact t3
          rcases Finset.mem_insert.mp hd''' with rfl | hd''''
          · exact hsub56T1 hd4'
          rw [Finset.mem_singleton] at hd''''
          subst hd''''
          exact hsub56T1 hd5'
        exact le_trans (apLen_mono' hsub) apLen_T1
      · have hsub : (A.image (fun d => (3 * lam') * d)).image (qdig7 m)
            ⊆ ({0, 1, 4, 5, 6} : Finset (ZMod 7)) := by
          intro q hq
          obtain ⟨d', hd', rfl⟩ := Finset.mem_image.mp hq
          obtain ⟨d, hdA, rfl⟩ := Finset.mem_image.mp hd'
          have hd5 := hcover hdA
          rcases Finset.mem_insert.mp hd5 with rfl | hd'
          · rw [ht1]
            exact t1
          rcases Finset.mem_insert.mp hd' with rfl | hd''
          · rw [ht2]
            exact t2
          rcases Finset.mem_insert.mp hd'' with rfl | hd'''
          · rw [ht3]
            exact t3
          rcases Finset.mem_insert.mp hd''' with rfl | hd''''
          · exact hsub56T2 hd4'
          rw [Finset.mem_singleton] at hd''''
          subst hd''''
          exact hsub56T2 hd5'
        exact le_trans (apLen_mono' hsub) apLen_T2
    have h3nd : ¬ 7 ∣ 3 * lam' :=
      Nat.Prime.not_dvd_mul Nat.prime_seven (by norm_num) hlam'nd
    exact good7_of_smul_apLen hm hpos hunit hs hcls h3nd hap5
  · -- generic pair: `{0,6,q₄,q₅}` already has `apLen ≤ 5`
    push_neg at h24
    have hmem06 : ∀ z : ZMod 7, z ∈ ({0, 6} : Finset (ZMod 7)) →
        z ∈ ({0, 6, q₄, q₅} : Finset (ZMod 7)) := by
      intro z hz
      rcases Finset.mem_insert.mp hz with h | h
      · exact Finset.mem_insert.mpr (Or.inl h)
      · rw [Finset.mem_singleton] at h
        exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl h)))
    have hsub : (A.image (fun d => lam' * d)).image (qdig7 m)
        ⊆ ({0, 6, q₄, q₅} : Finset (ZMod 7)) := by
      intro q hq
      have hq' := himg lam' hq
      rcases Finset.mem_insert.mp hq' with h | hq'
      · -- q = qdig7 m (lam' * b1)
        subst h
        exact hmem06 _ hq₁
      rcases Finset.mem_insert.mp hq' with h | hq'
      · subst h
        exact hmem06 _ hq₂
      rcases Finset.mem_insert.mp hq' with h | hq'
      · subst h
        exact hmem06 _ hq₃
      rcases Finset.mem_insert.mp hq' with h | hq'
      · subst h
        exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr
          (Or.inr (Finset.mem_insert.mpr (Or.inl rfl)))))
      rw [Finset.mem_singleton] at hq'
      subst hq'
      exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr
        (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self _))))))
    have hap5 : apLen ((A.image (fun d => lam' * d)).image (qdig7 m)) ≤ 5 :=
      le_trans (apLen_mono' hsub) (apLen_pair06_le
        ⟨fun ⟨h2, h4⟩ => h24.1 h2 h4, fun ⟨h4, h2⟩ => h24.2 h4 h2⟩)
    exact good7_of_smul_apLen hm hpos hunit hs hcls hlam'nd hap5

set_option maxHeartbeats 3000000 in
/-- Case A(i), sub-case `e31 = 0`: `d3 ≡ d1 (mod 7^{m+1})`, so `e21` alone is
normalized (Λ-shift or top scalar) and the compressed triple `{d1,d2,d3}`
finishes via `case61_tail`. Extracted for heartbeat budget. -/
private theorem case61_iA {m : ℕ} (hm0 : 0 < m) {A : Finset ℕ}
    (hpos : ∀ d ∈ A, 0 < d) (hunit : ∀ d ∈ A, padicValNat 7 d = 0)
    {s : ZMod 7} (hs0 : s ≠ 0) (hcls : ∀ d ∈ A, runit7 d = s)
    {d1 d2 d3 d4 d5 : ℕ}
    (hd1A : d1 ∈ A) (hd2A : d2 ∈ A) (hd3A : d3 ∈ A)
    (hcover : A ⊆ ({d1, d2, d3, d4, d5} : Finset ℕ))
    (h13 : d1 ≠ d3)
    (hsame : ∀ d ∈ A, ∀ d' ∈ A, d ≠ d' →
      residueRelOf d d' = residueRel.same)
    (huneq : padicValNat 7 (eMod7 m d2 d1) >
      padicValNat 7 (eMod7 m d3 d1))
    (he31 : eMod7 m d3 d1 = 0) :
    ∃ lam : ℕ, ¬ 7 ∣ lam ∧ good7 m lam A := by
  have he21 : eMod7 m d2 d1 ≠ 0 := fun h0 => by
    rw [h0] at huneq
    simp at huneq
  have hd3res : d3 % 7 ^ (m + 1) = d1 % 7 ^ (m + 1) :=
    eq_resid_of_eMod7_eq_zero he31 (hsame d3 hd3A d1 hd1A h13.symm)
  have hν21 : padicValNat 7 (eMod7 m d2 d1) ≤ m := enu7_le_of_ne he21
  obtain ⟨lam₁, hlam₁nd, hlam₁r, hkdig, hscale⟩ :
      ∃ lam₁ : ℕ, ¬ 7 ∣ lam₁ ∧ runit7 lam₁ ≠ 0 ∧
        qdig7 m (lam₁ * eMod7 m d2 d1) = 6 ∧
        (∀ x y : ℕ, eMod7 m (lam₁ * x) (lam₁ * y)
          = (lam₁ * eMod7 m x y) % 7 ^ (m + 1)) := by
    rcases lt_or_eq_of_le hν21 with hlt | heq
    · obtain ⟨k, -, hk⟩ :=
        exists_multLow_set_qdig hlt rfl he21 (6 : ZMod 7)
      exact ⟨1 + k * 7 ^ (m - padicValNat 7 (eMod7 m d2 d1)),
        multLow_not_dvd hlt, by
          rw [runit7_multLow hlt]; exact one_ne_zero, hk,
        fun x y => eMod7_mul (runit7_multLow hlt)⟩
    · obtain ⟨c, hc0, hc7, -, hk⟩ :=
        exists_top_scalar_set heq he21 (t := 6) (by decide)
      have hc7' : ¬ 7 ∣ c := fun hd =>
        Nat.ne_of_gt hc0 (Nat.eq_zero_of_dvd_of_lt hd hc7)
      have hrc : runit7 c = (c : ZMod 7) := by
        unfold runit7
        rw [padicValNat.eq_zero_of_not_dvd hc7', pow_zero, Nat.div_one]
      have hrc0 : runit7 c ≠ 0 := by
        rw [hrc]
        intro h0
        rw [ZMod.natCast_eq_zero_iff] at h0
        exact hc7' h0
      exact ⟨c, hc7', hrc0, hk, fun x y => eMod7_smul hrc0⟩
  have hL10 : lam₁ ≠ 0 := fun h => hlam₁nd (h ▸ dvd_zero 7)
  have hLpos : ∀ d ∈ A, 0 < lam₁ * d := fun d hd =>
    Nat.mul_pos (Nat.pos_of_ne_zero hL10) (hpos d hd)
  have hLr : ∀ d ∈ A, runit7 (lam₁ * d) = runit7 lam₁ * s := fun d hd => by
    rw [runit7_mul, hcls d hd]
  have hLd3 : (lam₁ * d3) % 7 ^ (m + 1) = (lam₁ * d1) % 7 ^ (m + 1) :=
    Nat.ModEq.mul (Nat.ModEq.refl _) hd3res
  have hLd3r : runit7 (lam₁ * d3) = runit7 (lam₁ * d1) := by
    rw [hLr d3 hd3A, hLr d1 hd1A]
  have hLrel : ∀ x ∈ A, ∀ y ∈ A,
      residueRelOf (lam₁ * x) (lam₁ * y) = residueRel.same := by
    intro x hx y hy
    apply rel_same _ (runit7_ne_zero (hLpos y hy))
    rw [hLr x hx, hLr y hy]
  have hd21 : qdig7 m (eMod7 m (lam₁ * d2) (lam₁ * d1)) = 6 := by
    rw [hscale, qdig7_mod']
    exact hkdig
  have hd33 : eMod7 m (lam₁ * d3) (lam₁ * d1) = 0 :=
    (eMod7_congr_left hLd3 hLd3r).trans (eMod7_self (hLpos d1 hd1A))
  have hd13 : eMod7 m (lam₁ * d1) (lam₁ * d3) = 0 :=
    (eMod7_congr_right hLd3 hLd3r).trans (eMod7_self (hLpos d1 hd1A))
  have hd23 : eMod7 m (lam₁ * d2) (lam₁ * d3)
      = eMod7 m (lam₁ * d2) (lam₁ * d1) :=
    eMod7_congr_right hLd3 hLd3r
  have hd32 : eMod7 m (lam₁ * d3) (lam₁ * d2)
      = eMod7 m (lam₁ * d1) (lam₁ * d2) :=
    eMod7_congr_left hLd3 hLd3r
  have hq12 : qdig7 m (lam₁ * d1) - qdig7 m (lam₁ * d2)
      ∈ ({0, 1} : Finset (ZMod 7)) := by
    have hsub := qdig_eMod_sub (m := m) (hLrel d2 hd2A d1 hd1A)
    rw [hd21] at hsub
    have h := neg06_mem01 (sub06_back hsub)
    rwa [neg_sub] at h
  have hd12 : qdig7 m (eMod7 m (lam₁ * d1) (lam₁ * d2))
      ∈ ({0, 1, 6} : Finset (ZMod 7)) := by
    have hsub := qdig_eMod_sub (m := m) (hLrel d1 hd1A d2 hd2A)
    have hE : qdig7 m (eMod7 m (lam₁ * d1) (lam₁ * d2))
        = (qdig7 m (lam₁ * d1) - qdig7 m (lam₁ * d2))
          + (qdig7 m (eMod7 m (lam₁ * d1) (lam₁ * d2))
              - (qdig7 m (lam₁ * d1) - qdig7 m (lam₁ * d2))) := by ring
    rw [hE]
    exact add016 hq12 hsub
  have hpair1 : ∀ x ∈ ({d1, d2, d3} : Finset ℕ),
      ∀ y ∈ ({d1, d2, d3} : Finset ℕ),
      qdig7 m (eMod7 m (lam₁ * x) (lam₁ * y))
        ∈ ({0, 1, 6} : Finset (ZMod 7)) := by
    have h0mem : (0 : ZMod 7) ∈ ({0, 1, 6} : Finset (ZMod 7)) :=
      Finset.mem_insert_self _ _
    have h6mem : (6 : ZMod 7) ∈ ({0, 1, 6} : Finset (ZMod 7)) :=
      Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr
        (Or.inr (Finset.mem_singleton_self _))))
    intro x hx y hy
    rcases Finset.mem_insert.mp hx with rfl | hx'
    · rcases Finset.mem_insert.mp hy with rfl | hy'
      · rw [eMod7_self (hLpos _ hd1A), qdig7_zero]; exact h0mem
      rcases Finset.mem_insert.mp hy' with rfl | hy''
      · exact hd12
      rw [Finset.mem_singleton] at hy''
      subst hy''
      rw [hd13, qdig7_zero]; exact h0mem
    rcases Finset.mem_insert.mp hx' with rfl | hx''
    · rcases Finset.mem_insert.mp hy with rfl | hy'
      · rw [hd21]; exact h6mem
      rcases Finset.mem_insert.mp hy' with rfl | hy''
      · rw [eMod7_self (hLpos _ hd2A), qdig7_zero]; exact h0mem
      rw [Finset.mem_singleton] at hy''
      subst hy''
      rw [hd23, hd21]; exact h6mem
    rw [Finset.mem_singleton] at hx''
    subst hx''
    rcases Finset.mem_insert.mp hy with rfl | hy'
    · rw [hd33, qdig7_zero]; exact h0mem
    rcases Finset.mem_insert.mp hy' with rfl | hy''
    · rw [hd32]; exact hd12
    rw [Finset.mem_singleton] at hy''
    subst hy''
    rw [eMod7_self (hLpos _ hd3A), qdig7_zero]; exact h0mem
  have hap1 : apLen (({d1, d2, d3} : Finset ℕ).image
      (fun d => qdig7 m (lam₁ * d))) ≤ 2 := by
    have hq3 : qdig7 m (lam₁ * d3) = qdig7 m (lam₁ * d1) :=
      qdig7_congr hLd3
    rw [Finset.image_insert, Finset.image_insert, Finset.image_singleton,
      hq3]
    have hmem : qdig7 m (lam₁ * d1)
        ∈ insert (qdig7 m (lam₁ * d2)) {qdig7 m (lam₁ * d1)} :=
      Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self _))
    rw [Finset.insert_eq_of_mem hmem]
    refine (apLen_le_iff _ 2 (by norm_num)).mpr
      ⟨qdig7 m (lam₁ * d2), ?_⟩
    intro z hz
    rw [mem_cycIv]
    rcases Finset.mem_insert.mp hz with rfl | hz'
    · rw [sub_self]; decide
    rw [Finset.mem_singleton] at hz'
    subst hz'
    exact val_lt2_of_mem01 hq12
  exact case61_tail hm0 hpos hunit hs0 hcls hd1A hd2A hd3A hcover
    hlam₁nd hpair1 hap1

set_option maxHeartbeats 3000000 in
/-- Case A(ii): uniform level `ℓ` with `r(e31) = 2·r(e21)`,
`r(e41) ∈ {3,4}·r(e21)` (Lemma 10 second alternative). Two sub-branches:
`e21 = 0` collapses `d2,d3,d4 ≡ d1` and normalizes `e51`; `e21 ≠ 0` feeds
`h9ii` at `j = 2`. Extracted for heartbeat budget. -/
private theorem case61_ii {m : ℕ} (hm0 : 0 < m) {A : Finset ℕ}
    (hpos : ∀ d ∈ A, 0 < d) (hunit : ∀ d ∈ A, padicValNat 7 d = 0)
    {s : ZMod 7} (hs0 : s ≠ 0) (hcls : ∀ d ∈ A, runit7 d = s)
    {d1 d2 d3 d4 d5 u v : ℕ}
    (hd1A : d1 ∈ A) (hd2A : d2 ∈ A) (hd3A : d3 ∈ A) (hd4A : d4 ∈ A)
    (hd5A : d5 ∈ A)
    (h12 : d1 ≠ d2) (h13 : d1 ≠ d3) (h14 : d1 ≠ d4) (hd5n1 : d5 ≠ d1)
    (huA : u ∈ A) (hvA : v ∈ A) (huv : u ≠ v)
    (huv0 : eMod7 m u v ≠ 0) (huvm : padicValNat 7 (eMod7 m u v) ≠ m)
    (hcover : A ⊆ ({d1, d2, d3, d4, d5} : Finset ℕ))
    (hsame : ∀ d ∈ A, ∀ d' ∈ A, d ≠ d' →
      residueRelOf d d' = residueRel.same)
    (htopneg : ¬ ∀ x ∈ A, ∀ y ∈ A, x ≠ y →
      eMod7 m x y = 0 ∨ padicValNat 7 (eMod7 m x y) = m)
    (h10out' : ∃ ℓ : ℕ,
      (∀ x ∈ A, ∀ y ∈ A, x ≠ y → eMod7 m x y ≠ 0 →
        padicValNat 7 (eMod7 m x y) = ℓ) ∧
      runit7 (eMod7 m d3 d1) = 2 * runit7 (eMod7 m d2 d1) ∧
      (runit7 (eMod7 m d4 d1) = 3 * runit7 (eMod7 m d2 d1) ∨
        runit7 (eMod7 m d4 d1) = 4 * runit7 (eMod7 m d2 d1)))
    (h9ii : ∀ {b1 b2 b3 : ℕ}, (0 < b1 ∧ 0 < b2 ∧ 0 < b3) →
      (padicValNat 7 b1 = 0 ∧ padicValNat 7 b2 = 0 ∧
        padicValNat 7 b3 = 0) →
      (runit7 b1 = runit7 b2 ∧ runit7 b2 = runit7 b3) →
      padicValNat 7 (eMod7 m b1 b3) = padicValNat 7 (eMod7 m b2 b3) →
      padicValNat 7 (eMod7 m b2 b3) < m →
      ∀ {j : ℕ}, (j = 2 ∨ j = 3) →
      runit7 (eMod7 m b2 b3) =
        ((j : ℕ) : ZMod 7) * runit7 (eMod7 m b1 b3) →
      ∃ lam : ℕ, ¬ 7 ∣ lam ∧
        qdig7 m (eMod7 m (lam * b2) (lam * b3))
          ∈ ({0, 5, 6} : Finset (ZMod 7)) ∧
        (∀ x ∈ ({b1, b2, b3} : Finset ℕ), ∀ y ∈ ({b1, b2, b3} : Finset ℕ),
          qdig7 m (eMod7 m (lam * x) (lam * y))
            ∈ ({0, 1, 5, 6} : Finset (ZMod 7))) ∧
        (j = 2 → ∀ x ∈ ({b1, b2, b3} : Finset ℕ),
          ∀ y ∈ ({b1, b2, b3} : Finset ℕ),
          qdig7 m (eMod7 m (lam * x) (lam * y))
            ∈ ({0, 6} : Finset (ZMod 7))) ∧
        apLen (({b1, b2, b3} : Finset ℕ).image
          (fun d => qdig7 m (lam * d))) ≤ j) :
    ∃ lam : ℕ, ¬ 7 ∣ lam ∧ good7 m lam A := by
  obtain ⟨hℓ, hunif, hr31, hr41⟩ := h10out'
  by_cases he21 : eMod7 m d2 d1 = 0
  · -- collapse: `r(e31) = r(e41) = 0` → `e31 = e41 = 0`; `d2,d3,d4 ≡ d1`.
    have he21r : runit7 (eMod7 m d2 d1) = 0 := by
      rw [he21]
      exact runit7_zero
    have he31 : eMod7 m d3 d1 = 0 := by
      apply eq_zero_of_runit7_eq_zero
      rw [hr31, he21r, mul_zero]
    have he41 : eMod7 m d4 d1 = 0 := by
      apply eq_zero_of_runit7_eq_zero
      rcases hr41 with h | h <;> rw [h, he21r, mul_zero]
    have hd2res : d2 % 7 ^ (m + 1) = d1 % 7 ^ (m + 1) :=
      eq_resid_of_eMod7_eq_zero he21 (hsame d2 hd2A d1 hd1A h12.symm)
    have hd3res : d3 % 7 ^ (m + 1) = d1 % 7 ^ (m + 1) :=
      eq_resid_of_eMod7_eq_zero he31 (hsame d3 hd3A d1 hd1A h13.symm)
    have hd4res : d4 % 7 ^ (m + 1) = d1 % 7 ^ (m + 1) :=
      eq_resid_of_eMod7_eq_zero he41 (hsame d4 hd4A d1 hd1A h14.symm)
    -- `e51 ≠ 0`: else every pair difference vanishes, contradicting `¬htop`.
    have he51 : eMod7 m d5 d1 ≠ 0 := by
      intro h0
      have hd5res : d5 % 7 ^ (m + 1) = d1 % 7 ^ (m + 1) :=
        eq_resid_of_eMod7_eq_zero h0 (hsame d5 hd5A d1 hd1A hd5n1)
      have Pall : ∀ x ∈ A, ∀ y ∈ A, x ≠ y →
          eMod7 m x y = 0 ∨ padicValNat 7 (eMod7 m x y) = m := by
        intro x hx y hy _
        left
        have hxres : x % 7 ^ (m + 1) = d1 % 7 ^ (m + 1) := by
          have hxx := hcover hx
          rcases Finset.mem_insert.mp hxx with rfl | hx'
          · rfl
          rcases Finset.mem_insert.mp hx' with rfl | hx''
          · exact hd2res
          rcases Finset.mem_insert.mp hx'' with rfl | hx'''
          · exact hd3res
          rcases Finset.mem_insert.mp hx''' with rfl | hx''''
          · exact hd4res
          rw [Finset.mem_singleton] at hx''''
          subst hx''''
          exact hd5res
        have hyres : y % 7 ^ (m + 1) = d1 % 7 ^ (m + 1) := by
          have hyy := hcover hy
          rcases Finset.mem_insert.mp hyy with rfl | hy'
          · rfl
          rcases Finset.mem_insert.mp hy' with rfl | hy''
          · exact hd2res
          rcases Finset.mem_insert.mp hy'' with rfl | hy'''
          · exact hd3res
          rcases Finset.mem_insert.mp hy''' with rfl | hy''''
          · exact hd4res
          rw [Finset.mem_singleton] at hy''''
          subst hy''''
          exact hd5res
        have hrel : residueRelOf x y = residueRel.same :=
          rel_same (by rw [hcls x hx, hcls y hy])
            (by rw [hcls y hy]; exact hs0)
        rw [eMod7_same_eq hrel]
        have heq : x % 7 ^ (m + 1) = y % 7 ^ (m + 1) := by rw [hxres, hyres]
        rw [heq]
        have hN0 : y % 7 ^ (m + 1) + 7 ^ (m + 1) - y % 7 ^ (m + 1)
            = 7 ^ (m + 1) := by omega
        rw [hN0, Nat.mod_self]
      exact htopneg Pall
    have hν51 : padicValNat 7 (eMod7 m d5 d1) = hℓ :=
      hunif d5 hd5A d1 hd1A hd5n1 he51
    have hℓm : hℓ < m := by
      have h1 := hunif u huA v hvA huv huv0
      have h2 : padicValNat 7 (eMod7 m u v) < m :=
        lt_of_le_of_ne (enu7_le_of_ne huv0) huvm
      rwa [h1] at h2
    obtain ⟨k, -, hkdig⟩ :=
      exists_multLow_set_qdig hℓm hν51 he51 (6 : ZMod 7)
    set lam₁ := 1 + k * 7 ^ (m - hℓ) with hlam₁def
    have hlam₁nd : ¬ 7 ∣ lam₁ := multLow_not_dvd hℓm
    have hlam₁r : runit7 lam₁ = 1 := runit7_multLow hℓm
    have hlam₁pos : 0 < lam₁ :=
      Nat.pos_of_ne_zero (fun h => hlam₁nd (h ▸ dvd_zero 7))
    have hLr : ∀ d ∈ A, runit7 (lam₁ * d) = runit7 lam₁ * s := fun d hd => by
      rw [runit7_mul, hcls d hd]
    have hLrel : ∀ x ∈ A, ∀ y ∈ A,
        residueRelOf (lam₁ * x) (lam₁ * y) = residueRel.same := by
      intro x hx y hy
      apply rel_same _ (runit7_ne_zero (Nat.mul_pos hlam₁pos (hpos y hy)))
      rw [hLr x hx, hLr y hy]
    have hd51 : qdig7 m (eMod7 m (lam₁ * d5) (lam₁ * d1)) = 6 := by
      rw [eMod7_mul hlam₁r, qdig7_mod']
      exact hkdig
    have hq51 : qdig7 m (lam₁ * d5) - qdig7 m (lam₁ * d1)
        ∈ ({0, 6} : Finset (ZMod 7)) := by
      have hsub := qdig_eMod_sub (m := m) (hLrel d5 hd5A d1 hd1A)
      rw [hd51] at hsub
      exact sub06_back hsub
    have hq15 : qdig7 m (lam₁ * d1) - qdig7 m (lam₁ * d5)
        ∈ ({0, 1} : Finset (ZMod 7)) := by
      have h := neg06_mem01 hq51
      rwa [neg_sub] at h
    have hqdi : ∀ d : ℕ, d % 7 ^ (m + 1) = d1 % 7 ^ (m + 1) →
        qdig7 m (lam₁ * d) = qdig7 m (lam₁ * d1) :=
      fun d hd => qdig7_congr (Nat.ModEq.mul (Nat.ModEq.refl _) hd)
    have himg2 : (A.image (fun d => lam₁ * d)).image (qdig7 m)
        ⊆ ({qdig7 m (lam₁ * d1), qdig7 m (lam₁ * d5)} : Finset (ZMod 7)) := by
      intro q hq
      obtain ⟨d', hd', rfl⟩ := Finset.mem_image.mp hq
      obtain ⟨d, hdA, rfl⟩ := Finset.mem_image.mp hd'
      have hd5 := hcover hdA
      rcases Finset.mem_insert.mp hd5 with rfl | hd5'
      · exact Finset.mem_insert.mpr (Or.inl rfl)
      rcases Finset.mem_insert.mp hd5' with hd2e | hd5''
      · rw [hd2e, hqdi d2 hd2res]
        exact Finset.mem_insert.mpr (Or.inl rfl)
      rcases Finset.mem_insert.mp hd5'' with hd3e | hd5'''
      · rw [hd3e, hqdi d3 hd3res]
        exact Finset.mem_insert.mpr (Or.inl rfl)
      rcases Finset.mem_insert.mp hd5''' with hd4e | hd5''''
      · rw [hd4e, hqdi d4 hd4res]
        exact Finset.mem_insert.mpr (Or.inl rfl)
      rw [Finset.mem_singleton] at hd5''''
      subst hd5''''
      exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self _))
    have hap2 : apLen ((A.image (fun d => lam₁ * d)).image (qdig7 m)) ≤ 2 := by
      refine le_trans (apLen_mono' himg2) ?_
      refine (apLen_le_iff _ 2 (by norm_num)).mpr
        ⟨qdig7 m (lam₁ * d5), ?_⟩
      intro z hz
      rw [mem_cycIv]
      rcases Finset.mem_insert.mp hz with rfl | hz'
      · exact val_lt2_of_mem01 hq15
      rw [Finset.mem_singleton] at hz'
      subst hz'
      rw [sub_self]; decide
    exact good7_of_smul_apLen hm0 hpos hunit hs0 hcls hlam₁nd
      (le_trans hap2 (by norm_num))
  · -- `e21 ≠ 0`: `r(e31) = 2·r(e21)` gives `e31 ≠ 0`; `h9ii` at `j = 2`.
    have he31 : eMod7 m d3 d1 ≠ 0 := by
      intro h0
      have hr0 : runit7 (eMod7 m d3 d1) = 0 := by
        rw [h0]
        exact runit7_zero
      rw [hr31] at hr0
      rcases mul_eq_zero.mp hr0 with h2 | h2
      · exact absurd h2 (by decide)
      · exact he21 (eq_zero_of_runit7_eq_zero h2)
    have hν21 : padicValNat 7 (eMod7 m d2 d1) = hℓ :=
      hunif d2 hd2A d1 hd1A h12.symm he21
    have hν31 : padicValNat 7 (eMod7 m d3 d1) = hℓ :=
      hunif d3 hd3A d1 hd1A h13.symm he31
    have hℓm : hℓ < m := by
      have h1 := hunif u huA v hvA huv huv0
      have h2 : padicValNat 7 (eMod7 m u v) < m :=
        lt_of_le_of_ne (enu7_le_of_ne huv0) huvm
      rwa [h1] at h2
    obtain ⟨lam₁, hlam₁, -, -, hp6, hap9⟩ := h9ii
      ⟨hpos d2 hd2A, hpos d3 hd3A, hpos d1 hd1A⟩
      ⟨hunit d2 hd2A, hunit d3 hd3A, hunit d1 hd1A⟩
      ⟨by rw [hcls d2 hd2A, hcls d3 hd3A], by rw [hcls d3 hd3A, hcls d1 hd1A]⟩
      (by rw [hν21, hν31]) (by rw [hν31]; exact hℓm)
      (j := 2) (Or.inl rfl)
      (by rw [Nat.cast_ofNat]; exact hr31)
    have hset : ({d2, d3, d1} : Finset ℕ) = ({d1, d2, d3} : Finset ℕ) := by
      ext x
      rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton,
        Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro (rfl | rfl | rfl)
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr rfl)
        · exact Or.inl rfl
      · rintro (rfl | rfl | rfl)
        · exact Or.inr (Or.inr rfl)
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
    rw [hset] at hp6 hap9
    have hp9 : ∀ x ∈ ({d1, d2, d3} : Finset ℕ),
        ∀ y ∈ ({d1, d2, d3} : Finset ℕ),
        qdig7 m (eMod7 m (lam₁ * x) (lam₁ * y))
          ∈ ({0, 1, 6} : Finset (ZMod 7)) :=
      fun x hx y hy => mem016_of_mem06 (hp6 rfl x hx y hy)
    exact case61_tail hm0 hpos hunit hs0 hcls hd1A hd2A hd3A hcover
      hlam₁ hp9 hap9


/-! ### §6.1 — main theorem -/

set_option maxHeartbeats 3000000 in
/-- **Paper §6.1** (single-class case): a five-element `Finset` of positive
`7`-adic units sharing one residue class `s ∈ {1,2,4}` admits a `7`-unit
`good7` multiplier.

Lemma 10 (`h10`) and Lemma 9(ii) (`h9ii`) are parameters so that this file
does not depend on their (in-progress) theorem names. -/
theorem case61 {m : ℕ} (hm : 2 ≤ m) {A : Finset ℕ} (hcard : A.card = 5)
    (hpos : ∀ d ∈ A, 0 < d) (hunit : ∀ d ∈ A, padicValNat 7 d = 0)
    {s : ZMod 7} (hs : s ∈ ({1, 2, 4} : Finset (ZMod 7)))
    (hcls : ∀ d ∈ A, runit7 d = s)
    (h10 : ∀ {A1 : Finset ℕ}, 4 ≤ A1.card → (∀ d ∈ A1, 0 < d) →
      (∀ d ∈ A1, padicValNat 7 d = 0) → ∀ (s : ZMod 7),
      (∀ d ∈ A1, runit7 d = s) →
      ∃ d1 ∈ A1, ∃ d2 ∈ A1, ∃ d3 ∈ A1, ∃ d4 ∈ A1,
        d1 ≠ d2 ∧ d1 ≠ d3 ∧ d1 ≠ d4 ∧ d2 ≠ d3 ∧ d2 ≠ d4 ∧ d3 ≠ d4 ∧
        (padicValNat 7 (eMod7 m d2 d1) > padicValNat 7 (eMod7 m d3 d1) ∨
          (∃ ℓ : ℕ, (∀ x ∈ A1, ∀ y ∈ A1, x ≠ y → eMod7 m x y ≠ 0 →
              padicValNat 7 (eMod7 m x y) = ℓ) ∧
            runit7 (eMod7 m d3 d1) = 2 * runit7 (eMod7 m d2 d1) ∧
            (runit7 (eMod7 m d4 d1) = 3 * runit7 (eMod7 m d2 d1) ∨
              runit7 (eMod7 m d4 d1) = 4 * runit7 (eMod7 m d2 d1)))))
    (h9ii : ∀ {b1 b2 b3 : ℕ}, (0 < b1 ∧ 0 < b2 ∧ 0 < b3) →
      (padicValNat 7 b1 = 0 ∧ padicValNat 7 b2 = 0 ∧ padicValNat 7 b3 = 0) →
      (runit7 b1 = runit7 b2 ∧ runit7 b2 = runit7 b3) →
      padicValNat 7 (eMod7 m b1 b3) = padicValNat 7 (eMod7 m b2 b3) →
      padicValNat 7 (eMod7 m b2 b3) < m →
      ∀ {j : ℕ}, (j = 2 ∨ j = 3) →
      runit7 (eMod7 m b2 b3) = ((j : ℕ) : ZMod 7) * runit7 (eMod7 m b1 b3) →
      ∃ lam : ℕ, ¬ 7 ∣ lam ∧
        qdig7 m (eMod7 m (lam * b2) (lam * b3)) ∈ ({0, 5, 6} : Finset (ZMod 7)) ∧
        (∀ x ∈ ({b1, b2, b3} : Finset ℕ), ∀ y ∈ ({b1, b2, b3} : Finset ℕ),
          qdig7 m (eMod7 m (lam * x) (lam * y))
            ∈ ({0, 1, 5, 6} : Finset (ZMod 7))) ∧
        (j = 2 → ∀ x ∈ ({b1, b2, b3} : Finset ℕ), ∀ y ∈ ({b1, b2, b3} : Finset ℕ),
          qdig7 m (eMod7 m (lam * x) (lam * y)) ∈ ({0, 6} : Finset (ZMod 7))) ∧
        apLen (({b1, b2, b3} : Finset ℕ).image (fun d => qdig7 m (lam * d))) ≤ j) :
    ∃ lam : ℕ, ¬ 7 ∣ lam ∧ good7 m lam A := by
  classical
  have hm0 : 0 < m := by omega
  have hs0 : s ≠ 0 := by
    intro h0
    rw [h0] at hs
    exact absurd hs (by decide)
  -- every same-class pair is in the `same` residue branch
  have hsame : ∀ d ∈ A, ∀ d' ∈ A, d ≠ d' →
      residueRelOf d d' = residueRel.same := by
    intro d hd d' hd' _
    exact rel_same (by rw [hcls d hd, hcls d' hd'])
      (by rw [hcls d' hd']; exact hs0)
  by_cases htop : ∀ x ∈ A, ∀ y ∈ A, x ≠ y →
      eMod7 m x y = 0 ∨ padicValNat 7 (eMod7 m x y) = m
  · -- Case B (paper's `ν(E) = {m}` — the second `≠` in the paper is a typo):
    -- every nonzero difference is at level `m`.
    exact case61_caseB hm0 hcard.le hpos hunit hs0 hcls htop
  · -- Case A: some difference has level `< m`.
    have htopneg := htop
    push_neg at htop
    obtain ⟨u, huA, v, hvA, huv, huv0, huvm⟩ := htop
    -- Lemma 10 picks the four-element set.
    obtain ⟨d1, hd1A', d2, hd2A', d3, hd3A', d4, hd4A',
      h12, h13, h14, h23, h24, h34, h10out⟩ :=
      h10 (by rw [hcard]; norm_num) hpos hunit s hcls
    have hTsub : ({d1, d2, d3, d4} : Finset ℕ) ⊆ A := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx'
      · exact hd1A'
      rcases Finset.mem_insert.mp hx' with rfl | hx''
      · exact hd2A'
      rcases Finset.mem_insert.mp hx'' with rfl | hx'''
      · exact hd3A'
      rw [Finset.mem_singleton] at hx'''
      exact hx''' ▸ hd4A'
    have hTcard : ({d1, d2, d3, d4} : Finset ℕ).card = 4 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_insert_of_notMem, Finset.card_singleton]
      · simp only [Finset.mem_singleton, Ne]
        exact h34
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨h23, h24⟩
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨h12, h13, h14⟩
    obtain ⟨d5, hd5⟩ : ∃ d5 : ℕ, A \ ({d1, d2, d3, d4} : Finset ℕ) = {d5} := by
      apply Finset.card_eq_one.mp
      rw [Finset.card_sdiff_of_subset hTsub, hcard, hTcard]
    have hd5mem : d5 ∈ A \ ({d1, d2, d3, d4} : Finset ℕ) := by
      rw [hd5]
      exact Finset.mem_singleton_self _
    have hd5A : d5 ∈ A := (Finset.mem_sdiff.mp hd5mem).1
    have hd5T : d5 ∉ ({d1, d2, d3, d4} : Finset ℕ) :=
      (Finset.mem_sdiff.mp hd5mem).2
    have hd5n1 : d5 ≠ d1 := fun h => hd5T (by rw [h]; simp)
    have hd1A : d1 ∈ A := hTsub (by simp)
    have hd2A : d2 ∈ A := hTsub (by simp)
    have hd3A : d3 ∈ A := hTsub (by simp)
    have hd4A : d4 ∈ A := hTsub (by simp)
    have hcover : A ⊆ ({d1, d2, d3, d4, d5} : Finset ℕ) := by
      intro x hx
      by_cases hxT : x ∈ ({d1, d2, d3, d4} : Finset ℕ)
      · rcases Finset.mem_insert.mp hxT with rfl | hxT'
        · exact Finset.mem_insert_self _ _
        rcases Finset.mem_insert.mp hxT' with rfl | hxT''
        · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert_self _ _))
        rcases Finset.mem_insert.mp hxT'' with rfl | hxT'''
        · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr
            (Or.inr (Finset.mem_insert_self _ _))))
        rw [Finset.mem_singleton] at hxT'''
        subst hxT'''
        exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr
          (Or.inr (Finset.mem_insert.mpr (Or.inr
            (Finset.mem_insert.mpr (Or.inl rfl)))))))
      · have hxd : x ∈ A \ ({d1, d2, d3, d4} : Finset ℕ) :=
          Finset.mem_sdiff.mpr ⟨hx, hxT⟩
        rw [hd5, Finset.mem_singleton] at hxd
        subst hxd
        exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr
          (Or.inr (Finset.mem_insert.mpr (Or.inr
            (Finset.mem_insert.mpr (Or.inr
              (Finset.mem_singleton_self _))))))))
    rcases h10out with huneq | h10out'
    · -- (i) `ν(e21) > ν(e31)`.
      by_cases he31 : eMod7 m d3 d1 = 0
      · -- `e31 = 0`: `d3 ≡ d1 (mod 7^{m+1})`; normalize `e21` alone.
        exact case61_iA hm0 hpos hunit hs0 hcls hd1A hd2A hd3A hcover
          h13 hsame huneq he31
      · -- `e31 ≠ 0`: `lemma9_i'` on the triple `(d2, d3, d1)`.
        have he21 : eMod7 m d2 d1 ≠ 0 := fun h0 => by
          rw [h0] at huneq
          simp at huneq
        obtain ⟨lam₁, hlam₁, hp9, hap9⟩ := lemma9_i'
          ⟨hpos d2 hd2A, hpos d3 hd3A, hpos d1 hd1A⟩
          ⟨hunit d2 hd2A, hunit d3 hd3A, hunit d1 hd1A⟩
          ⟨by rw [hcls d2 hd2A, hcls d3 hd3A], by rw [hcls d3 hd3A, hcls d1 hd1A]⟩
          (ne_of_gt huneq) ⟨he21, he31⟩
        have hset5 : ({d2, d3, d1, d4, d5} : Finset ℕ)
            = ({d1, d2, d3, d4, d5} : Finset ℕ) := by
          rw [Finset.insert_comm d3 d1, Finset.insert_comm d2 d1]
        exact case61_tail hm0 hpos hunit hs0 hcls hd2A hd3A hd1A
          (hset5.symm ▸ hcover) hlam₁ hp9 hap9
    · -- (ii) uniform level `ℓ` with the residue-ratio structure.
      exact case61_ii hm0 hpos hunit hs0 hcls hd1A hd2A hd3A hd4A hd5A
        h12 h13 h14 hd5n1 huA hvA huv huv0 huvm hcover hsame htopneg
        h10out' h9ii