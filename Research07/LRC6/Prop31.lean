/-
Copyright (c) 2026 Research07 contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Research07 contributors
-/
import Mathlib
import Research07.LRC6.Setup
import Research07.LRC6.Extremize
import Research07.LRC6.Driver
import Research07.LRC6.Reduction

/-!
# Renault Proposition 3.1 (two speeds are multiples of 3)

`prop3_1`: five positive integer speeds, exactly two of them multiples of 3, and
`hfail` (no all-safe time) — contradiction.

Renault's argument (renault.txt §3):

* `arg1` — if the two multiples of 3 are safe at `t` and at least two other
  runners are unsafe, some `l/3`-shift (`l ∈ {0,1,2}`) makes everybody safe.
* `arg2` — if the two multiples of 3 are safe at `t` and some non-multiple sits
  on `{1/6,1/2,5/6}`, some `l/3`-shift makes everybody safe.
* `boundary_le` — for `w` a non-multiple of 3 and `th` maximizing
  `min {circ (v₁·t), circ (v₂·t)}` over the discrete set `T_w = {x_w = 5/6}`,
  every time `s` with `x_w(s) ∈ {1/6,1/2,5/6}` has `min ≤ min th` (a third-shift
  moves `s` into `T_w` without moving the multiples of 3).
* `anchor_eq_zero` — the casework: at the maximizer the nearer multiple of 3
  sits at `0`.
* `key_per_w` — for every non-multiple `w`, `6w` divides one of the multiples.
* finish — pigeonhole + Lemma 2.2 inequalities + `t̄ = 1/(6v₁)`, `s = 5/(6v₁)`.
-/

noncomputable section

open Int

/-- `circ x = 0` iff `fract x = 0`. -/
theorem circ_eq_zero_iff (x : ℝ) : circ x = 0 ↔ Int.fract x = 0 := by
  rw [circ_eq, abs_sub_round_eq_min]
  have h1 := Int.fract_nonneg x
  have h2 := Int.fract_lt_one x
  constructor
  · intro h
    rcases lt_or_ge (Int.fract x) (1 - Int.fract x) with hlt | hge
    · rwa [min_eq_left hlt.le] at h
    · rw [min_eq_right hge] at h; linarith
  · intro h
    rw [h]
    norm_num [min_eq_left]

/-- `circ x = |x|` for `|x| ≤ 1/2`. -/
theorem circ_eq_abs_of_abs_le_half {x : ℝ} (h : |x| ≤ 1 / 2) : circ x = |x| := by
  rw [circ_eq, abs_sub_round_eq_min]
  rcases le_total 0 x with hx | hx
  · rw [Int.fract_eq_self.mpr ⟨hx, by linarith [abs_le.mp h]⟩]
    rw [abs_of_nonneg hx]
    rcases abs_le.mp h with ⟨-, h2⟩
    exact min_eq_left (by linarith)
  · rcases eq_or_lt_of_le hx with rfl | hlt
    · simp
    · rw [abs_of_nonpos hx]
      have hfx : Int.fract x = x + 1 := by
        rw [Int.fract_eq_iff]
        refine ⟨by linarith [abs_le.mp h], by linarith, -1, by push_cast; ring⟩
      rw [hfx]
      rcases abs_le.mp h with ⟨h1, -⟩
      rw [show (1 : ℝ) - (x + 1) = -x by ring]
      exact min_eq_right (by linarith)

/-- For `0 < circ x < 1/6`, multiplying by `k ∈ {2,…,5}` strictly increases the
distance: `circ (k·x) > circ x`. -/
theorem circ_lt_circ_nat_mul {x : ℝ} (h0 : 0 < circ x) (h : circ x < 1 / 6) {k : ℕ}
    (h2 : 2 ≤ k) (h5 : k ≤ 5) : circ x < circ ((k : ℝ) * x) := by
  set z := x - (round x : ℝ) with hz
  have hzabs : |z| = circ x := by rw [hz, circ_eq]
  have hkz : circ ((k : ℝ) * x) = circ ((k : ℝ) * z) := by
    have heq : (k : ℝ) * x = (k : ℝ) * z + (((k : ℤ) * round x : ℤ) : ℝ) := by
      push_cast; rw [hz]; ring
    rw [heq, circ_add_int]
  rw [hkz]
  have hk0 : (0 : ℝ) ≤ k := by positivity
  have hzk : |z| * (k : ℝ) < 5 / 6 := by
    have h5' : (k : ℝ) ≤ 5 := by exact_mod_cast h5
    calc |z| * (k : ℝ) ≤ |z| * 5 := by
          apply mul_le_mul_of_nonneg_left h5' (abs_nonneg _)
      _ < 5 / 6 := by nlinarith [hzabs]
  have hkzabs : |(k : ℝ) * z| = (k : ℝ) * |z| := by
    rw [abs_mul, abs_of_nonneg hk0]
  -- `circ (k z) = min (k|z|, 1 − k|z|)`: `kz ∈ (−5/6,5/6)` has `fract ∈ {kz, kz+1}`.
  have hmin : circ ((k : ℝ) * z) = min ((k : ℝ) * |z|) (1 - (k : ℝ) * |z|) := by
    rw [circ_eq, abs_sub_round_eq_min]
    rcases lt_or_ge z 0 with hz0 | hz0
    · have hneg : (k : ℝ) * z < 0 :=
        mul_neg_of_pos_of_neg (by exact_mod_cast (by omega : 0 < k)) hz0
      rw [abs_of_neg hz0]
      have hfx : Int.fract ((k : ℝ) * z) = (k : ℝ) * z + 1 := by
        rw [Int.fract_eq_iff]
        have hgt : -1 < (k : ℝ) * z := by
          have h2 := neg_le_abs ((k : ℝ) * z)
          linarith [hzk, hkzabs]
        refine ⟨by linarith, by linarith, -1, by push_cast; ring⟩
      rw [hfx]
      rw [show (1 : ℝ) - ((k : ℝ) * z + 1) = -((k : ℝ) * z) by ring]
      rw [show (k : ℝ) * -z = -((k : ℝ) * z) by ring]
      rw [show (1 : ℝ) - -((k : ℝ) * z) = (k : ℝ) * z + 1 by ring]
      exact min_comm _ _
    · have hpos : 0 ≤ (k : ℝ) * z := mul_nonneg hk0 hz0
      rw [abs_of_nonneg hz0]
      have hlt : (k : ℝ) * z < 1 := by
        have h2 := le_abs_self ((k : ℝ) * z)
        linarith [hzk, hkzabs]
      rw [Int.fract_eq_self.mpr ⟨hpos, hlt⟩]
  rw [hmin]
  have h2' : (2 : ℝ) ≤ k := by exact_mod_cast h2
  have hzpos : 0 < |z| := by rw [hzabs]; exact h0
  refine lt_min ?_ ?_
  · rw [← hzabs]; nlinarith
  · rw [← hzabs]; linarith

/-- `circ` only sees the fractional part: `circ (fract x) = circ x`. -/
theorem circ_fract (x : ℝ) : circ (Int.fract x) = circ x := by
  have h : Int.fract x = x + ((-⌊x⌋ : ℤ) : ℝ) := by
    have h2 := Int.self_sub_floor x
    push_cast
    linarith
  rw [h, circ_add_int]

/-- `circ` is unchanged under `l/3`-shifts for multiples of 3. -/
theorem circ_third_shift_of_dvd {d : ℕ} (hd : 3 ∣ d) (t : ℝ) (l : ℕ) :
    circ ((d : ℝ) * (t + (l : ℝ) / 3)) = circ ((d : ℝ) * t) := by
  obtain ⟨k, hk⟩ := hd
  have heq : (d : ℝ) * (t + (l : ℝ) / 3) =
      (d : ℝ) * t + (((k * l : ℤ)) : ℝ) := by
    rw [show (d : ℝ) = 3 * (k : ℝ) by exact_mod_cast hk]
    push_cast
    ring
  rw [heq, circ_add_int]

/-- `fract (u + s) = fract (u + fract s)`. -/
theorem fract_add_eq_fract_add_fract (u s : ℝ) :
    Int.fract (u + s) = Int.fract (u + Int.fract s) := by
  have h : u + s = (u + Int.fract s) + (⌊s⌋ : ℝ) := by
    have h2 := Int.self_sub_fract s
    linarith
  rw [h, Int.fract_add_intCast]

/-- `fract x = x - K` when `x ∈ [K, K+1)`. -/
theorem fract_eq_of_floor {x : ℝ} {K : ℤ} (h0 : (K : ℝ) ≤ x) (h1 : x < (K : ℝ) + 1) :
    Int.fract x = x - (K : ℝ) := by
  rw [Int.fract_eq_iff]
  refine ⟨by linarith, by linarith, K, by ring⟩

/-- A strictly unsafe point shifted by `s` with `fract s ∈ {1/3,1/2,2/3}` lands
strictly inside `(1/6,5/6)`.  Copied from `Prop41` (`unsafe_add_shift_Ioo`). -/
theorem unsafe_add_shift_Ioo {u s : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
    (hu : u ∉ Set.Icc (1 / 6) (5 / 6))
    (hs : Int.fract s = 1 / 3 ∨ Int.fract s = 1 / 2 ∨ Int.fract s = 2 / 3) :
    Int.fract (u + s) ∈ Set.Ioo (1 / 6) (5 / 6) := by
  have huo : u < 1 / 6 ∨ 5 / 6 < u := by
    rw [Set.mem_Icc, not_and_or] at hu
    rcases hu with h | h
    · exact Or.inl (not_le.mp h)
    · exact Or.inr (not_le.mp h)
  rw [fract_add_eq_fract_add_fract]
  have wrap : ∀ c : ℝ, 1 / 3 ≤ c → c ≤ 2 / 3 → 5 / 6 < u →
      Int.fract (u + c) = u + c - 1 := by
    intro c hc1 hc2 hhi
    rw [Int.fract_eq_iff]
    refine ⟨by linarith, by linarith, 1, by ring⟩
  rcases huo with hlo | hhi <;>
    rcases hs with hs | hs | hs <;> rw [hs]
  · rw [Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩]
    exact Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩
  · rw [Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩]
    exact Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩
  · rw [Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩]
    exact Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩
  · rw [wrap _ (by norm_num) (by norm_num) hhi]
    exact Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩
  · rw [wrap _ (by norm_num) (by norm_num) hhi]
    exact Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩
  · rw [wrap _ (by norm_num) (by norm_num) hhi]
    exact Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩

/-- For `circ x ≤ 1/4`, doubling doubles the distance: `circ (2x) = 2 circ x`. -/
theorem circ_two_mul_of_quarter {x : ℝ} (h : circ x ≤ 1 / 4) :
    circ ((2 : ℝ) * x) = 2 * circ x := by
  set z := x - (round x : ℝ) with hz
  have hzabs : |z| = circ x := by rw [hz, circ_eq]
  have heq : (2 : ℝ) * x = (2 : ℝ) * z + (((2 * round x : ℤ)) : ℝ) := by
    push_cast
    rw [hz]
    ring
  rw [heq, circ_add_int]
  have hz4 : |z| ≤ 1 / 4 := by rw [hzabs]; exact h
  have h2z : |(2 : ℝ) * z| ≤ 1 / 2 := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    linarith
  rw [circ_eq_abs_of_abs_le_half h2z, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2),
    ← hzabs]

/-- `circ` of a doubled point: `circ (2x) = 2 circ x` for `circ x ≤ 1/4`,
`fract`-form corollary used for the `λ = 2` improving moves. -/
theorem circ_two_mul_fract {x : ℝ} (h : circ x ≤ 1 / 4) :
    circ ((2 : ℝ) * Int.fract x) = 2 * circ x := by
  rw [← circ_fract x] at h ⊢
  exact circ_two_mul_of_quarter h

/-- `fract (d·l/3) = (d·l % 3)/3`. -/
theorem fract_mul_div_three (d l : ℕ) :
    Int.fract ((d : ℝ) * (l : ℝ) / 3) = (((d * l) % 3 : ℕ) : ℝ) / 3 := by
  have h : (d : ℝ) * (l : ℝ) / 3 = ((d * l : ℕ) : ℝ) / ((3 : ℕ) : ℝ) := by
    push_cast; ring
  rw [h, Int.fract_div_natCast_eq_div_natCast_mod]
  norm_num

/-- For `3 ∤ w`, a boundary position `x_w ∈ {1/6,1/2,5/6}` stays safe under
every `l/3`-shift (`l < 3`): the shifted positions are again
`{1/6,1/2,5/6}`.  This is the engine of Renault's Argument 2. -/
theorem safe6_third_shift_boundary {w : ℕ} (_hw : ¬ 3 ∣ w) (t : ℝ)
    (hx : Int.fract ((w : ℝ) * t) = 1 / 6 ∨ Int.fract ((w : ℝ) * t) = 1 / 2 ∨
      Int.fract ((w : ℝ) * t) = 5 / 6)
    {l : ℕ} (_hl : l < 3) :
    safe6 w (t + (l : ℝ) / 3) := by
  rw [safe6, fract_third_shift]
  set x := Int.fract ((w : ℝ) * t)
  have hmod : (w * l) % 3 < 3 := Nat.mod_lt _ (by norm_num)
  have hfr : Int.fract (x + (w : ℝ) * (l : ℝ) / 3) =
      Int.fract (x + (((w * l) % 3 : ℕ) : ℝ) / 3) := by
    rw [← fract_mul_div_three, fract_add_eq_fract_add_fract]
  rw [hfr]
  interval_cases h : (w * l) % 3 <;> rcases hx with hx | hx | hx <;>
    (rw [hx]; push_cast; norm_num [Int.fract])

/-- For `3 ∤ w`, every boundary position `x_w(s) ∈ {1/6,1/2,5/6}` has a
`l/3`-shift (`l < 3`) putting runner `w` exactly on `5/6`. -/
theorem third_shift_to_five_six {w : ℕ} (hw : ¬ 3 ∣ w) (s : ℝ)
    (hx : Int.fract ((w : ℝ) * s) = 1 / 6 ∨ Int.fract ((w : ℝ) * s) = 1 / 2 ∨
      Int.fract ((w : ℝ) * s) = 5 / 6) :
    ∃ l : ℕ, l < 3 ∧ Int.fract ((w : ℝ) * (s + (l : ℝ) / 3)) = 5 / 6 := by
  set x := Int.fract ((w : ℝ) * s)
  have hw3 : w % 3 ≠ 0 := fun h => hw (Nat.dvd_of_mod_eq_zero h)
  have hshift : ∀ l : ℕ, Int.fract ((w : ℝ) * (s + (l : ℝ) / 3)) =
      Int.fract (x + (((w * l) % 3 : ℕ) : ℝ) / 3) := by
    intro l
    rw [fract_third_shift, ← fract_mul_div_three, fract_add_eq_fract_add_fract]
  rcases hx with hx | hx | hx
  · -- `x = 1/6`: need `(w·l) % 3 = 2`
    by_cases hw1 : w % 3 = 1
    · refine ⟨2, by norm_num, ?_⟩
      rw [hshift]
      have h2 : (w * 2) % 3 = 2 := by
        rw [Nat.mul_mod, hw1]
      rw [h2, hx]
      push_cast
      rw [Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩]
      norm_num
    · have hw2 : w % 3 = 2 := by omega
      refine ⟨1, by norm_num, ?_⟩
      rw [hshift]
      have h1 : (w * 1) % 3 = 2 := by
        rw [Nat.mul_mod, hw2]
      rw [h1, hx]
      push_cast
      rw [Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩]
      norm_num
  · -- `x = 1/2`: need `(w·l) % 3 = 1`
    by_cases hw1 : w % 3 = 1
    · refine ⟨1, by norm_num, ?_⟩
      rw [hshift]
      have h1 : (w * 1) % 3 = 1 := by
        rw [Nat.mul_mod, hw1]
      rw [h1, hx]
      push_cast
      rw [Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩]
      norm_num
    · have hw2 : w % 3 = 2 := by omega
      refine ⟨2, by norm_num, ?_⟩
      rw [hshift]
      have h2 : (w * 2) % 3 = 1 := by
        rw [Nat.mul_mod, hw2]
      rw [h2, hx]
      push_cast
      rw [Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩]
      norm_num
  · -- `x = 5/6`: `l = 0` works
    refine ⟨0, by norm_num, ?_⟩
    rw [hshift]
    simp only [Nat.mul_zero, Nat.zero_mod, Nat.cast_zero, zero_div, add_zero]
    rw [hx]
    exact Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩

/-- An odd runner is safe at `t` or `t + 1/2`: the two positions differ by
exactly `1/2`, too far apart to share the length-`1/3` unsafe arc. -/
theorem exists_good_half {d : ℕ} (hd : ¬ 2 ∣ d) (t : ℝ) :
    safe6 d t ∨ safe6 d (t + 1 / 2) := by
  by_contra hb
  push Not at hb
  obtain ⟨hb1, hb2⟩ := hb
  obtain ⟨j, hj⟩ : ∃ j : ℕ, d = 2 * j + 1 := by
    rcases Nat.even_or_odd d with h | h
    · exact absurd (even_iff_two_dvd.mp h) hd
    · exact h
  have hpos : Int.fract ((d : ℝ) * (t + 1 / 2)) =
      Int.fract (Int.fract ((d : ℝ) * t) + (d : ℝ) / 2) := by
    have h := fract_add_shift d t (1 / 2 : ℝ)
    rwa [← mul_div_assoc, mul_one] at h
  have hd2 : (d : ℝ) / 2 = (j : ℝ) + 1 / 2 := by
    rw [hj]; push_cast; ring
  have hpos' : Int.fract ((d : ℝ) * (t + 1 / 2)) =
      Int.fract (Int.fract ((d : ℝ) * t) + 1 / 2) := by
    rw [hpos, hd2]
    rw [show Int.fract ((d : ℝ) * t) + ((j : ℝ) + 1 / 2) =
        (Int.fract ((d : ℝ) * t) + 1 / 2) + (j : ℝ) by ring]
    exact Int.fract_add_natCast _ _
  have habs : |Int.fract ((d : ℝ) * (t + 1 / 2)) - Int.fract ((d : ℝ) * t)| = 1 / 2 := by
    rw [hpos']
    rcases lt_or_ge (Int.fract ((d : ℝ) * t)) (1 / 2) with h | h
    · rw [Int.fract_eq_self.mpr ⟨by linarith [Int.fract_nonneg ((d:ℝ)*t)], by linarith⟩]
      rw [abs_of_pos (by linarith : (0:ℝ) < Int.fract ((d:ℝ)*t) + 1/2 - Int.fract ((d:ℝ)*t))]
      ring
    · have hx1 := Int.fract_lt_one ((d : ℝ) * t)
      have hfr : Int.fract (Int.fract ((d : ℝ) * t) + 1 / 2) =
          Int.fract ((d : ℝ) * t) - 1 / 2 := by
        rw [Int.fract_eq_iff]
        refine ⟨by linarith, by linarith, 1, by ring⟩
      rw [hfr, abs_of_neg (by linarith)]
      ring
  rcases unsafe_pair_abs hb1 hb2 with h | h
  · rw [abs_sub_comm] at h; linarith
  · rw [abs_sub_comm] at h; linarith

/-- Even runners are unchanged by `1/2`-shifts. -/
theorem safe6_half_shift_of_dvd {d : ℕ} (hd : 2 ∣ d) (t : ℝ) :
    safe6 d (t + 1 / 2) ↔ safe6 d t := by
  obtain ⟨k, hk⟩ := hd
  have heq : (d : ℝ) * (t + 1 / 2) = (d : ℝ) * t + ((k : ℤ) : ℝ) := by
    rw [show (d : ℝ) = 2 * (k : ℝ) by exact_mod_cast hk]
    push_cast
    ring
  unfold safe6
  rw [heq, Int.fract_add_intCast]

/-- Lemma 2.1, the `≤ 3` direction for `l = 2`: with `gcd = 1` and `hfail`, at
most three speeds are even. -/
theorem mult2_le_three {D : Finset ℕ} (hpos : ∀ d ∈ D, 0 < d) (hcard : D.card ≤ 5)
    (hgcd : D.gcd id = 1) (hf : hfail D) :
    (D.filter fun d => 2 ∣ d).card ≤ 3 := by
  classical
  by_contra hcon
  push Not at hcon
  set S := D.filter fun d => 2 ∣ d with hS
  have hSsub : S ⊆ D := Finset.filter_subset _ _
  obtain ⟨T, hTS, hTcard⟩ := Finset.le_card_iff_exists_subset_card.mp hcon
  have hTsub : T ⊆ D := fun x hx => hSsub (hTS hx)
  have hrest : (D \ T).card ≤ 1 := by
    have := Finset.card_sdiff_add_card_eq_card hTsub
    omega
  obtain ⟨t₀, -, ht₀⟩ := lrc5_int T
    (fun d hd => hpos d (hTsub hd)) (by omega : T.card ≤ 4)
  have ht₀' : ∀ d ∈ T, safe6 d t₀ :=
    fun d hd => safe6_of_circ_ge_fifth (ht₀ d hd)
  have gcd_contra : (∀ d ∈ D, 2 ∣ d) → False := fun hall => by
    have hdg : 2 ∣ D.gcd id := Finset.dvd_gcd (fun d hd => hall d hd)
    rw [hgcd] at hdg
    exact absurd hdg (by norm_num)
  rcases Nat.eq_zero_or_pos (D \ T).card with h0 | hposR
  · have hDT : D \ T = ∅ := Finset.card_eq_zero.mp h0
    have hDeq : D = T := Finset.Subset.antisymm
      (Finset.sdiff_eq_empty_iff_subset.mp hDT) hTsub
    exact gcd_contra (fun d hd => (Finset.mem_filter.mp (hTS (hDeq ▸ hd))).2)
  · have h1 : (D \ T).card = 1 := by omega
    obtain ⟨i, hi⟩ := Finset.card_eq_one.mp h1
    have hiD : i ∈ D := by
      have : i ∈ D \ T := by simp [hi]
      exact (Finset.mem_sdiff.mp this).1
    by_cases h2i : 2 ∣ i
    · exact gcd_contra (fun d hd => by
        by_cases hdT : d ∈ T
        · exact (Finset.mem_filter.mp (hTS hdT)).2
        · have hdieq : d = i := by
            have : d ∈ D \ T := Finset.mem_sdiff.mpr ⟨hd, hdT⟩
            rwa [hi, Finset.mem_singleton] at this
          rwa [hdieq])
    · rcases exists_good_half h2i t₀ with hli | hli
      · obtain ⟨w, hwD, hwbad⟩ := hf t₀
        by_cases hwT : w ∈ T
        · exact hwbad (ht₀' w hwT)
        · have hwi : w = i := by
            have : w ∈ D \ T := Finset.mem_sdiff.mpr ⟨hwD, hwT⟩
            rwa [hi, Finset.mem_singleton] at this
          rw [hwi] at hwbad
          exact hwbad hli
      · obtain ⟨w, hwD, hwbad⟩ := hf (t₀ + 1 / 2)
        by_cases hwT : w ∈ T
        · exact hwbad ((safe6_half_shift_of_dvd
            (Finset.mem_filter.mp (hTS hwT)).2 t₀).mpr (ht₀' w hwT))
        · have hwi : w = i := by
            have : w ∈ D \ T := Finset.mem_sdiff.mpr ⟨hwD, hwT⟩
            rwa [hi, Finset.mem_singleton] at this
          rw [hwi] at hwbad
          exact hwbad hli

/-- All five runners safe at `s` contradicts `hfail` on the explicit 5-set. -/
theorem all_safe5_contra {a b c d e : ℕ} {s : ℝ}
    (h1 : safe6 a s) (h2 : safe6 b s) (h3 : safe6 c s)
    (h4 : safe6 d s) (h5 : safe6 e s)
    (hf : hfail {a, b, c, d, e}) : False := by
  obtain ⟨x, hxD, hxbad⟩ := hf s
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxD
  rcases hxD with rfl | rfl | rfl | rfl | rfl
  · exact hxbad h1
  · exact hxbad h2
  · exact hxbad h3
  · exact hxbad h4
  · exact hxbad h5

/-- **Argument 1** (Renault §3): if the two multiples of 3 are safe at `t` and
two other runners `u, u'` are unsafe, some `l/3`-shift makes everybody safe —
contradicting `hfail`.  The third runner `z` is arbitrary. -/
theorem arg1 {a b u u' z : ℕ} {t : ℝ}
    (h3a : 3 ∣ a) (h3b : 3 ∣ b) (h3u : ¬ 3 ∣ u) (h3u' : ¬ 3 ∣ u') (h3z : ¬ 3 ∣ z)
    (hsa : safe6 a t) (hsb : safe6 b t)
    (hu : ¬ safe6 u t) (hu' : ¬ safe6 u' t)
    (hf : hfail {a, b, u, u', z}) : False := by
  have h0 : ∀ (v : ℕ) (τ : ℝ), τ + ((0 : ℕ) : ℝ) / 3 = τ := by
    intro v τ; simp
  -- `u, u'` bad at `l = 0` ⇒ safe at `l = 1` and `l = 2`
  have hu1 : safe6 u (t + ((1 : ℕ) : ℝ) / 3) := by
    rcases bad_third_le_one h3u t (l₁ := 0) (l₂ := 1) (by norm_num) (by norm_num)
        (by norm_num) with h | h
    · rw [h0 u t] at h; exact absurd h hu
    · exact h
  have hu2 : safe6 u (t + ((2 : ℕ) : ℝ) / 3) := by
    rcases bad_third_le_one h3u t (l₁ := 0) (l₂ := 2) (by norm_num) (by norm_num)
        (by norm_num) with h | h
    · rw [h0 u t] at h; exact absurd h hu
    · exact h
  have hu'1 : safe6 u' (t + ((1 : ℕ) : ℝ) / 3) := by
    rcases bad_third_le_one h3u' t (l₁ := 0) (l₂ := 1) (by norm_num) (by norm_num)
        (by norm_num) with h | h
    · rw [h0 u' t] at h; exact absurd h hu'
    · exact h
  have hu'2 : safe6 u' (t + ((2 : ℕ) : ℝ) / 3) := by
    rcases bad_third_le_one h3u' t (l₁ := 0) (l₂ := 2) (by norm_num) (by norm_num)
        (by norm_num) with h | h
    · rw [h0 u' t] at h; exact absurd h hu'
    · exact h
  -- choose `l ∈ {1,2}` good for `z`
  by_cases hz0 : safe6 z t
  · rcases bad_third_le_one h3z t (l₁ := 1) (l₂ := 2) (by norm_num) (by norm_num)
        (by norm_num) with h | h
    · exact all_safe5_contra
        ((safe6_third_shift_of_dvd h3a t 1).mpr hsa)
        ((safe6_third_shift_of_dvd h3b t 1).mpr hsb)
        hu1 hu'1 h hf
    · exact all_safe5_contra
        ((safe6_third_shift_of_dvd h3a t 2).mpr hsa)
        ((safe6_third_shift_of_dvd h3b t 2).mpr hsb)
        hu2 hu'2 h hf
  · have hz1 : safe6 z (t + ((1 : ℕ) : ℝ) / 3) := by
      rcases bad_third_le_one h3z t (l₁ := 0) (l₂ := 1) (by norm_num) (by norm_num)
          (by norm_num) with h | h
      · rw [h0 z t] at h; exact absurd h hz0
      · exact h
    exact all_safe5_contra
      ((safe6_third_shift_of_dvd h3a t 1).mpr hsa)
      ((safe6_third_shift_of_dvd h3b t 1).mpr hsb)
      hu1 hu'1 hz1 hf

/-- **Argument 2** (Renault §3): if the two multiples of 3 are safe at `t` and
some non-multiple `w` sits on `{1/6,1/2,5/6}`, some `l/3`-shift makes
everybody safe — contradicting `hfail`. -/
theorem arg2 {a b w d e : ℕ} {t : ℝ}
    (h3a : 3 ∣ a) (h3b : 3 ∣ b) (h3w : ¬ 3 ∣ w) (h3d : ¬ 3 ∣ d) (h3e : ¬ 3 ∣ e)
    (hsa : safe6 a t) (hsb : safe6 b t)
    (hxw : Int.fract ((w : ℝ) * t) = 1 / 6 ∨ Int.fract ((w : ℝ) * t) = 1 / 2 ∨
      Int.fract ((w : ℝ) * t) = 5 / 6)
    (hf : hfail {a, b, w, d, e}) : False := by
  obtain ⟨l, hl3, hld, hle⟩ := exists_common_good_third h3d h3e t
  have hwl : safe6 w (t + (l : ℝ) / 3) :=
    safe6_third_shift_boundary h3w t hxw hl3
  exact all_safe5_contra
    ((safe6_third_shift_of_dvd h3a t l).mpr hsa)
    ((safe6_third_shift_of_dvd h3b t l).mpr hsb)
    hwl hld hle hf

/-- `hfail` is invariant under dividing all speeds by a common positive
factor `g`: `(d/g)·s = d·(s/g)`.  Used to reduce to the `gcd = 1` case. -/
theorem hfail_div {D : Finset ℕ} {g : ℕ} (hg : 0 < g) (hdvd : ∀ d ∈ D, g ∣ d)
    (hf : hfail D) : hfail (D.image (· / g)) := by
  intro s
  obtain ⟨d, hdD, hd⟩ := hf (s / (g : ℝ))
  refine ⟨d / g, Finset.mem_image.mpr ⟨d, hdD, rfl⟩, ?_⟩
  rw [safe6] at hd ⊢
  have hg' : (g : ℝ) ≠ 0 := by exact_mod_cast hg.ne'
  have hcast : ((d / g : ℕ) : ℝ) = (d : ℝ) / g := by
    rw [eq_div_iff_mul_eq hg']
    exact_mod_cast Nat.div_mul_cancel (hdvd d hdD)
  rw [hcast, show (d : ℝ) / g * s = (d : ℝ) * (s / (g : ℝ)) by ring]
  exact hd

/-- The discrete maximizer: `T = {t : x_w(t) = 5/6}` is the lattice
`t = (k + 5/6)/w`, so `min (circ (v₁ t)) (circ (v₂ t))` takes only `w`
distinct values on `T` (`k ↦ k mod w`); hence a maximum exists. -/
theorem exists_min_circ_max {v₁ v₂ w : ℕ} (hw : 0 < w) :
    ∃ th : ℝ, Int.fract ((w : ℝ) * th) = 5 / 6 ∧
      ∀ t : ℝ, Int.fract ((w : ℝ) * t) = 5 / 6 →
        min (circ ((v₁ : ℝ) * t)) (circ ((v₂ : ℝ) * t)) ≤
        min (circ ((v₁ : ℝ) * th)) (circ ((v₂ : ℝ) * th)) := by
  classical
  set τ : ℕ → ℝ := fun k => ((k : ℝ) + 5 / 6) / (w : ℝ) with hτ
  have hw' : (w : ℝ) ≠ 0 := by exact_mod_cast hw.ne'
  have hval : ∀ k : ℕ, Int.fract ((w : ℝ) * τ k) = 5 / 6 := by
    intro k
    have h1 : (w : ℝ) * τ k = (k : ℝ) + 5 / 6 := by
      rw [hτ]
      field_simp
    rw [h1, show (k : ℝ) + 5 / 6 = 5 / 6 + ((k : ℤ) : ℝ) by push_cast; ring,
      Int.fract_add_intCast]
    exact Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩
  set F : ℕ → ℝ := fun k =>
    min (circ ((v₁ : ℝ) * τ k)) (circ ((v₂ : ℝ) * τ k)) with hF
  obtain ⟨kh, hkhr, hkh⟩ := Finset.exists_max_image (Finset.range w) F
    (Finset.nonempty_range_iff.mpr hw.ne')
  refine ⟨τ kh, hval kh, fun t ht => ?_⟩
  -- `w·t = n + 5/6` with `n = ⌊w·t⌋`; reduce `n` modulo `w`
  set n := ⌊(w : ℝ) * t⌋ with hn
  have hnt : (w : ℝ) * t = (n : ℝ) + 5 / 6 := by
    have h := Int.self_sub_fract ((w : ℝ) * t)
    rw [ht] at h
    linarith
  set k' := (n % (w : ℤ)).toNat with hk'
  have hk'mem : k' ∈ Finset.range w := by
    rw [Finset.mem_range]
    have h1 : 0 ≤ n % (w : ℤ) :=
      Int.emod_nonneg n (by exact_mod_cast hw.ne')
    have h2 : n % (w : ℤ) < (w : ℤ) :=
      Int.emod_lt n (by exact_mod_cast hw.ne')
    omega
  have hk'eq : (k' : ℤ) = n % (w : ℤ) := by
    rw [hk']
    exact Int.toNat_of_nonneg (Int.emod_nonneg _
      (show (w : ℤ) ≠ 0 by exact_mod_cast hw.ne'))
  -- `circ (v·t) = circ (v·τ k')`: the difference is `v`-times an integer
  have hper : ∀ v : ℕ, circ ((v : ℝ) * t) = circ ((v : ℝ) * τ k') := by
    intro v
    -- `↑k' = n - w·(n/w)` as a real equation
    have hk'r : (k' : ℝ) =
        (n : ℝ) - (w : ℝ) * ((n / (w : ℤ) : ℤ) : ℝ) := by
      have h2 := Int.mul_ediv_add_emod n (w : ℤ)
      rw [← hk'eq] at h2
      have h3 : (k' : ℤ) = n - (w : ℤ) * (n / (w : ℤ)) := by linarith
      have h3r : ((k' : ℤ) : ℝ) =
          ((n - (w : ℤ) * (n / (w : ℤ)) : ℤ) : ℝ) := congrArg Int.cast h3
      push_cast at h3r
      exact h3r
    have hvt : (v : ℝ) * t = ((v : ℝ) * ((w : ℝ) * t)) / (w : ℝ) := by
      rw [eq_div_iff_mul_eq hw']
      ring
    have heq : (v : ℝ) * t = (v : ℝ) * τ k' +
        (((v : ℤ) * (n / (w : ℤ)) : ℤ) : ℝ) := by
      rw [hvt, hnt]
      simp only [hτ]
      rw [hk'r]
      push_cast
      field_simp
      ring
    rw [heq, circ_add_int]
  have hle : F k' ≤ F kh := hkh k' hk'mem
  show min (circ ((v₁ : ℝ) * t)) (circ ((v₂ : ℝ) * t)) ≤
    min (circ ((v₁ : ℝ) * τ kh)) (circ ((v₂ : ℝ) * τ kh))
  rw [hper v₁, hper v₂]
  exact hle

/-- The maximality propagates to every boundary time: if `x_w(s)` is
`1/6`, `1/2` or `5/6`, a `l/3`-shift lands on `5/6` (where `min ≤ m`)
without changing the multiples' positions. -/
theorem boundary_min_le {v₁ v₂ w : ℕ} (h3₁ : 3 ∣ v₁) (h3₂ : 3 ∣ v₂)
    (h3w : ¬ 3 ∣ w) {m : ℝ}
    (hmax : ∀ t : ℝ, Int.fract ((w : ℝ) * t) = 5 / 6 →
      min (circ ((v₁ : ℝ) * t)) (circ ((v₂ : ℝ) * t)) ≤ m)
    {s : ℝ} (hs : Int.fract ((w : ℝ) * s) = 1 / 6 ∨
      Int.fract ((w : ℝ) * s) = 1 / 2 ∨ Int.fract ((w : ℝ) * s) = 5 / 6) :
    min (circ ((v₁ : ℝ) * s)) (circ ((v₂ : ℝ) * s)) ≤ m := by
  obtain ⟨l, hl, hsw⟩ := third_shift_to_five_six h3w s hs
  have hle := hmax (s + (l : ℝ) / 3) hsw
  rwa [circ_third_shift_of_dvd h3₁ s l, circ_third_shift_of_dvd h3₂ s l] at hle

/-! ### Interval arithmetic for the extremal argument -/

/-- `fract x = x - n` on a floor window `x ∈ [n, n+1)`. -/
theorem fract_of_between {x : ℝ} {n : ℤ} (h0 : (n : ℝ) ≤ x)
    (h1 : x < (n : ℝ) + 1) : Int.fract x = x - (n : ℝ) := by
  have hfl : ⌊x⌋ = n := Int.floor_eq_iff.mpr ⟨h0, h1⟩
  rw [Int.fract, hfl]

/-- `circ x = min (x - n) (1 - (x - n))` on a floor window. -/
theorem circ_eq_of_between {x : ℝ} {n : ℤ} (h0 : (n : ℝ) ≤ x)
    (h1 : x < (n : ℝ) + 1) :
    circ x = min (x - (n : ℝ)) (1 - (x - (n : ℝ))) := by
  rw [circ_eq, abs_sub_round_eq_min, fract_of_between h0 h1]

/-- Renault's "computations before Claim 2.4": `y ∈ (0,1)` with `3y`, `5y` both
unsafe (`circ < 1/6`) lies in
`(0,1/30) ∪ (29/30,1) ∪ (11/30,7/18) ∪ (11/18,19/30)`. -/
theorem unsafe35_union {y : ℝ} (hy0 : 0 < y) (hy1 : y < 1)
    (h3 : circ (3 * y) < 1 / 6) (h5 : circ (5 * y) < 1 / 6) :
    (0 < y ∧ y < 1 / 30) ∨ (29 / 30 < y ∧ y < 1) ∨
      (11 / 30 < y ∧ y < 7 / 18) ∨ (11 / 18 < y ∧ y < 19 / 30) := by
  have hf3n := Int.fract_nonneg (3 * y)
  have hf5n := Int.fract_nonneg (5 * y)
  have hf3t := Int.fract_lt_one (3 * y)
  have hf5t := Int.fract_lt_one (5 * y)
  have hfl3 := Int.self_sub_fract (3 * y)
  have hfl5 := Int.self_sub_fract (5 * y)
  rw [circ_eq, abs_sub_round_eq_min, min_lt_iff] at h3 h5
  have hlo3 : (0 : ℤ) ≤ ⌊3 * y⌋ := Int.floor_nonneg.mpr (by linarith)
  have hhi3 : ⌊3 * y⌋ < 3 := by
    rw [Int.floor_lt]; push_cast; linarith
  have hlo5 : (0 : ℤ) ≤ ⌊5 * y⌋ := Int.floor_nonneg.mpr (by linarith)
  have hhi5 : ⌊5 * y⌋ < 5 := by
    rw [Int.floor_lt]; push_cast; linarith
  interval_cases h3k : ⌊3 * y⌋ <;>
    interval_cases h5k : ⌊5 * y⌋ <;>
    (push_cast at hfl3 hfl5) <;>
    rcases h3 with h3l | h3r <;> rcases h5 with h5l | h5r <;>
    first
      | exact Or.inl ⟨by linarith, by linarith⟩
      | exact Or.inr (Or.inl ⟨by linarith, by linarith⟩)
      | exact Or.inr (Or.inr (Or.inl ⟨by linarith, by linarith⟩))
      | exact Or.inr (Or.inr (Or.inr ⟨by linarith, by linarith⟩))

/-- The surviving runner-2 windows
`x₂ ∈ (11/30,7/18) ∪ (11/18,19/30)` give all the shift data used below. -/
theorem runner2_facts {y : ℝ}
    (hy : (11 / 30 < y ∧ y < 7 / 18) ∨ (11 / 18 < y ∧ y < 19 / 30)) :
    (11 / 30 < circ y ∧ circ y < 7 / 18) ∧
    (2 / 9 < circ (2 * y) ∧ circ (2 * y) < 4 / 15) ∧
    (7 / 30 < circ (2 * y + 1 / 2) ∧ circ (2 * y + 1 / 2) < 5 / 18) ∧
    (1 / 3 < circ (3 * y + 1 / 2) ∧ circ (3 * y + 1 / 2) < 2 / 5) ∧
    Int.fract (2 * y) ∈ Set.Icc (1 / 6) (5 / 6) ∧
    Int.fract (4 * y) ∈ Set.Icc (1 / 6) (5 / 6) ∧
    (Int.fract (3 * y) ∈ Set.Ioo (1 / 10) (1 / 6) ∨
      Int.fract (3 * y) ∈ Set.Ioo (5 / 6) (9 / 10)) := by
  rcases hy with ⟨hyl, hyu⟩ | ⟨hyl, hyu⟩
  · -- `y ∈ (11/30, 7/18)`
    have hc1 : circ y = y := by
      rw [circ_eq_of_between (n := 0) (by push_cast; linarith) (by push_cast; linarith)]
      rw [min_eq_left (by push_cast; linarith)]; push_cast; ring
    have hc2 : circ (2 * y) = 1 - 2 * y := by
      rw [circ_eq_of_between (n := 0) (by push_cast; linarith) (by push_cast; linarith)]
      rw [min_eq_right (by push_cast; linarith)]; push_cast; ring
    have hc2h : circ (2 * y + 1 / 2) = 2 * y - 1 / 2 := by
      rw [circ_eq_of_between (n := 1) (by push_cast; linarith) (by push_cast; linarith)]
      rw [min_eq_left (by push_cast; linarith)]; push_cast; ring
    have hc3h : circ (3 * y + 1 / 2) = 3 / 2 - 3 * y := by
      rw [circ_eq_of_between (n := 1) (by push_cast; linarith) (by push_cast; linarith)]
      rw [min_eq_right (by push_cast; linarith)]; push_cast; ring
    have hf2 : Int.fract (2 * y) = 2 * y := by
      rw [fract_of_between (n := 0) (by push_cast; linarith) (by push_cast; linarith)]
      push_cast; ring
    have hf4 : Int.fract (4 * y) = 4 * y - 1 := by
      rw [fract_of_between (n := 1) (by push_cast; linarith) (by push_cast; linarith)]
      push_cast; ring
    have hf3 : Int.fract (3 * y) = 3 * y - 1 := by
      rw [fract_of_between (n := 1) (by push_cast; linarith) (by push_cast; linarith)]
      push_cast; ring
    refine ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩,
      ⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩,
      ⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩,
      Or.inl ⟨by linarith, by linarith⟩⟩
  · -- `y ∈ (11/18, 19/30)`
    have hc1 : circ y = 1 - y := by
      rw [circ_eq_of_between (n := 0) (by push_cast; linarith) (by push_cast; linarith)]
      rw [min_eq_right (by push_cast; linarith)]; push_cast; ring
    have hc2 : circ (2 * y) = 2 * y - 1 := by
      rw [circ_eq_of_between (n := 1) (by push_cast; linarith) (by push_cast; linarith)]
      rw [min_eq_left (by push_cast; linarith)]; push_cast; ring
    have hc2h : circ (2 * y + 1 / 2) = 3 / 2 - 2 * y := by
      rw [circ_eq_of_between (n := 1) (by push_cast; linarith) (by push_cast; linarith)]
      rw [min_eq_right (by push_cast; linarith)]; push_cast; ring
    have hc3h : circ (3 * y + 1 / 2) = 3 * y - 3 / 2 := by
      rw [circ_eq_of_between (n := 2) (by push_cast; linarith) (by push_cast; linarith)]
      rw [min_eq_left (by push_cast; linarith)]; push_cast; ring
    have hf2 : Int.fract (2 * y) = 2 * y - 1 := by
      rw [fract_of_between (n := 1) (by push_cast; linarith) (by push_cast; linarith)]
      push_cast; ring
    have hf4 : Int.fract (4 * y) = 4 * y - 2 := by
      rw [fract_of_between (n := 2) (by push_cast; linarith) (by push_cast; linarith)]
      push_cast; ring
    have hf3 : Int.fract (3 * y) = 3 * y - 1 := by
      rw [fract_of_between (n := 1) (by push_cast; linarith) (by push_cast; linarith)]
      push_cast; ring
    refine ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩,
      ⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩,
      ⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩,
      Or.inr ⟨by linarith, by linarith⟩⟩

/-- Runner 1's windows `x₁ ∈ (1/10,1/6) ∪ (5/6,9/10)`: the doubled-shift
facts (`e₁ = 0` gives `circ (2x₁) = 2δ`, `e₁ = 3` shifts by `1/2`) plus
safety at `2y`, `4y`. -/
theorem runner1_facts {y : ℝ}
    (hy : (1 / 10 < y ∧ y < 1 / 6) ∨ (5 / 6 < y ∧ y < 9 / 10)) :
    circ (2 * y) = 2 * circ y ∧
    (1 / 6 < circ (2 * y + 1 / 2) ∧ circ (2 * y + 1 / 2) < 3 / 10) ∧
    (1 / 3 < circ (y + 1 / 2) ∧ circ (y + 1 / 2) < 2 / 5) ∧
    Int.fract (2 * y) ∈ Set.Icc (1 / 6) (5 / 6) ∧
    Int.fract (4 * y) ∈ Set.Icc (1 / 6) (5 / 6) := by
  rcases hy with ⟨hyl, hyu⟩ | ⟨hyl, hyu⟩
  · -- `y ∈ (1/10, 1/6)`
    have hc : circ y = y := by
      rw [circ_eq_of_between (n := 0) (by push_cast; linarith) (by push_cast; linarith)]
      rw [min_eq_left (by push_cast; linarith)]; push_cast; ring
    have hc2 : circ (2 * y) = 2 * y := by
      rw [circ_eq_of_between (n := 0) (by push_cast; linarith) (by push_cast; linarith)]
      rw [min_eq_left (by push_cast; linarith)]; push_cast; ring
    have hc2h : circ (2 * y + 1 / 2) = 1 / 2 - 2 * y := by
      rw [circ_eq_of_between (n := 0) (by push_cast; linarith) (by push_cast; linarith)]
      rw [min_eq_right (by push_cast; linarith)]; push_cast; ring
    have hc1h : circ (y + 1 / 2) = 1 / 2 - y := by
      rw [circ_eq_of_between (n := 0) (by push_cast; linarith) (by push_cast; linarith)]
      rw [min_eq_right (by push_cast; linarith)]; push_cast; ring
    have hf2 : Int.fract (2 * y) = 2 * y := by
      rw [fract_of_between (n := 0) (by push_cast; linarith) (by push_cast; linarith)]
      push_cast; ring
    have hf4 : Int.fract (4 * y) = 4 * y := by
      rw [fract_of_between (n := 0) (by push_cast; linarith) (by push_cast; linarith)]
      push_cast; ring
    refine ⟨?_, ⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩,
      ⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
    rw [hc2, hc]
  · -- `y ∈ (5/6, 9/10)`
    have hc : circ y = 1 - y := by
      rw [circ_eq_of_between (n := 0) (by push_cast; linarith) (by push_cast; linarith)]
      rw [min_eq_right (by push_cast; linarith)]; push_cast; ring
    have hc2 : circ (2 * y) = 2 - 2 * y := by
      rw [circ_eq_of_between (n := 1) (by push_cast; linarith) (by push_cast; linarith)]
      rw [min_eq_right (by push_cast; linarith)]; push_cast; ring
    have hc2h : circ (2 * y + 1 / 2) = 2 * y - 3 / 2 := by
      rw [circ_eq_of_between (n := 2) (by push_cast; linarith) (by push_cast; linarith)]
      rw [min_eq_left (by push_cast; linarith)]; push_cast; ring
    have hc1h : circ (y + 1 / 2) = y - 1 / 2 := by
      rw [circ_eq_of_between (n := 1) (by push_cast; linarith) (by push_cast; linarith)]
      rw [min_eq_left (by push_cast; linarith)]; push_cast; ring
    have hf2 : Int.fract (2 * y) = 2 * y - 1 := by
      rw [fract_of_between (n := 1) (by push_cast; linarith) (by push_cast; linarith)]
      push_cast; ring
    have hf4 : Int.fract (4 * y) = 4 * y - 3 := by
      rw [fract_of_between (n := 3) (by push_cast; linarith) (by push_cast; linarith)]
      push_cast; ring
    refine ⟨?_, ⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩,
      ⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
    rw [hc2, hc]; ring

/-- `circ y ∈ (1/10,1/6)` for `y ∈ [0,1)` forces `y` into runner 1's windows. -/
theorem runner1_interval {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y < 1)
    (h : 1 / 10 < circ y) (h' : circ y < 1 / 6) :
    (1 / 10 < y ∧ y < 1 / 6) ∨ (5 / 6 < y ∧ y < 9 / 10) := by
  rw [circ_eq, abs_sub_round_eq_min] at h h'
  have hf : Int.fract y = y := Int.fract_eq_self.mpr ⟨hy0, hy1⟩
  rw [hf] at h h'
  rw [lt_min_iff] at h
  rw [min_lt_iff] at h'
  rcases h' with h'l | h'r
  · exact Or.inl ⟨h.1, h'l⟩
  · exact Or.inr ⟨by linarith, by linarith⟩

/-! ### Signed-shift position bookkeeping -/

/-- `circ (k·fract x) = circ (k·x)` for `k : ℕ`. -/
private theorem circ_nat_mul_fract (k : ℕ) (x : ℝ) :
    circ ((k : ℝ) * Int.fract x) = circ ((k : ℝ) * x) := by
  have h : (k : ℝ) * x = (k : ℝ) * Int.fract x +
      (((k : ℤ) * ⌊x⌋ : ℤ) : ℝ) := by
    have h2 := Int.self_sub_fract x
    push_cast
    linear_combination (k : ℝ) * h2
  rw [h, circ_add_int]

/-- `fract (k·x) = fract (k·fract x)` for `k : ℕ`. -/
private theorem fract_nat_mul_left (k : ℕ) (x : ℝ) :
    Int.fract ((k : ℝ) * x) = Int.fract ((k : ℝ) * Int.fract x) := by
  have h : (k : ℝ) * x = (k : ℝ) * Int.fract x +
      (((k : ℤ) * ⌊x⌋ : ℤ) : ℝ) := by
    have h2 := Int.self_sub_fract x
    push_cast
    linear_combination (k : ℝ) * h2
  rw [h, Int.fract_add_intCast]

/-- Signed `λt + sh/6` position: `x_d(λt + sh/6) = ⟨λ·x_d(t) + e·sh/6⟩` for
`d ≡ e (mod 6)`.  Covers `2t̂ ± 1/6`, `3t̂ ± 1/6`, `t̂ ± 1/6`. -/
private theorem fract_lambda_signed {d : ℕ} {e : ℤ} (hde : (d : ℤ) ≡ e [ZMOD 6])
    (t : ℝ) (lam : ℕ) (sh : ℤ) :
    Int.fract ((d : ℝ) * ((lam : ℝ) * t + (sh : ℝ) / 6)) =
      Int.fract ((lam : ℝ) * Int.fract ((d : ℝ) * t) +
        (e : ℝ) * (sh : ℝ) / 6) := by
  obtain ⟨k, hk⟩ := Int.modEq_iff_dvd.mp hde
  have hd : (d : ℝ) = (e : ℝ) - 6 * (k : ℝ) := by
    have h2 : (d : ℤ) = e - 6 * k := by linarith [hk]
    calc (d : ℝ) = ((d : ℤ) : ℝ) := by simp
      _ = ((e - 6 * k : ℤ) : ℝ) := by rw [h2]
      _ = (e : ℝ) - 6 * (k : ℝ) := by push_cast; ring
  have hfloor : (d : ℝ) * t =
      Int.fract ((d : ℝ) * t) + (⌊(d : ℝ) * t⌋ : ℝ) := by
    have h3 := Int.self_sub_fract ((d : ℝ) * t)
    linarith
  have h1 : (d : ℝ) * ((lam : ℝ) * t + (sh : ℝ) / 6) =
      ((lam : ℝ) * Int.fract ((d : ℝ) * t) + (e : ℝ) * (sh : ℝ) / 6) +
        (((lam : ℤ) * ⌊(d : ℝ) * t⌋ - k * sh : ℤ) : ℝ) := by
    push_cast
    linear_combination (lam : ℝ) * hfloor + ((sh : ℝ) / 6) * hd
  rw [h1, Int.fract_add_intCast]

/-- `circ` version of `fract_lambda_signed`. -/
private theorem circ_lambda_signed {d : ℕ} {e : ℤ} (hde : (d : ℤ) ≡ e [ZMOD 6])
    (t : ℝ) (lam : ℕ) (sh : ℤ) :
    circ ((d : ℝ) * ((lam : ℝ) * t + (sh : ℝ) / 6)) =
      circ ((lam : ℝ) * Int.fract ((d : ℝ) * t) +
        (e : ℝ) * (sh : ℝ) / 6) := by
  obtain ⟨k, hk⟩ := Int.modEq_iff_dvd.mp hde
  have hd : (d : ℝ) = (e : ℝ) - 6 * (k : ℝ) := by
    have h2 : (d : ℤ) = e - 6 * k := by linarith [hk]
    calc (d : ℝ) = ((d : ℤ) : ℝ) := by simp
      _ = ((e - 6 * k : ℤ) : ℝ) := by rw [h2]
      _ = (e : ℝ) - 6 * (k : ℝ) := by push_cast; ring
  have hfloor : (d : ℝ) * t =
      Int.fract ((d : ℝ) * t) + (⌊(d : ℝ) * t⌋ : ℝ) := by
    have h3 := Int.self_sub_fract ((d : ℝ) * t)
    linarith
  have h1 : (d : ℝ) * ((lam : ℝ) * t + (sh : ℝ) / 6) =
      ((lam : ℝ) * Int.fract ((d : ℝ) * t) + (e : ℝ) * (sh : ℝ) / 6) +
        (((lam : ℤ) * ⌊(d : ℝ) * t⌋ - k * sh : ℤ) : ℝ) := by
    push_cast
    linear_combination (lam : ℝ) * hfloor + ((sh : ℝ) / 6) * hd
  rw [h1, circ_add_int]

/-! ### Improving moves: `s = λ·th + α/6` bookkeeping -/

/-- For `d ≡ 3 (mod 6)` (i.e. `3∣d`, `6∤d`) and odd `α`, the improving move
lands on `λ·x_d + 1/2` since `d·α/6 = ⌊dα/6⌋ + 1/2`. -/
theorem fract_move_of_three {d : ℕ} (h3 : 3 ∣ d) (h6 : ¬ 6 ∣ d) {al : ℕ}
    (hal : al = 1 ∨ al = 3 ∨ al = 5) (th : ℝ) (lam : ℕ) :
    Int.fract ((d : ℝ) * ((lam : ℝ) * th + (al : ℝ) / 6)) =
      Int.fract ((lam : ℝ) * Int.fract ((d : ℝ) * th) + 1 / 2) := by
  rw [fract_improve]
  have hd6 : d % 6 = 3 := by
    obtain ⟨k, hk⟩ := h3
    have h3k : ¬ 2 ∣ k := fun ⟨j, hj⟩ => h6 ⟨j, by rw [hk, hj]; ring⟩
    omega
  have hdal : (d * al) % 6 = 3 := by
    rw [Nat.mul_mod, hd6]
    rcases hal with rfl | rfl | rfl <;> norm_num
  have hdiv : (d : ℝ) * (al : ℝ) / 6 =
      (((d * al) / 6 : ℕ) : ℝ) + 1 / 2 := by
    have hmod := Nat.div_add_mod (d * al) 6
    rw [hdal] at hmod
    have hwal : ((d * al : ℕ) : ℝ) =
        6 * (((d * al) / 6 : ℕ) : ℝ) + 3 := by exact_mod_cast hmod.symm
    rw [← Nat.cast_mul, hwal]
    field_simp
    ring
  rw [hdiv]
  rw [show (lam : ℝ) * Int.fract ((d : ℝ) * th) +
        ((((d * al) / 6 : ℕ) : ℝ) + 1 / 2) =
      ((lam : ℝ) * Int.fract ((d : ℝ) * th) + 1 / 2) +
        (((d * al) / 6 : ℕ) : ℝ) by ring]
  rw [Int.fract_add_natCast]

/-- `circ` version for `6 ∣ d`: `x_d(λth+α/6) ↦ λ·x_d`. -/
theorem circ_move_dvd {d : ℕ} (h6 : 6 ∣ d) (th : ℝ) (lam al : ℕ) :
    circ ((d : ℝ) * ((lam : ℝ) * th + (al : ℝ) / 6)) =
      circ ((lam : ℝ) * Int.fract ((d : ℝ) * th)) := by
  rw [← circ_fract, fract_improve_anchor h6 lam al th, circ_fract]

/-- `circ` version for `d ≡ 3 (mod 6)`, odd `α`: `x_d ↦ λ·x_d + 1/2`. -/
theorem circ_move_three {d : ℕ} (h3 : 3 ∣ d) (h6 : ¬ 6 ∣ d) {al : ℕ}
    (hal : al = 1 ∨ al = 3 ∨ al = 5) (th : ℝ) (lam : ℕ) :
    circ ((d : ℝ) * ((lam : ℝ) * th + (al : ℝ) / 6)) =
      circ ((lam : ℝ) * Int.fract ((d : ℝ) * th) + 1 / 2) := by
  rw [← circ_fract, fract_move_of_three h3 h6 hal th lam, circ_fract]

/-- Position of the anchor runner `w` at `λth + α/6`: `w·α/6 ≡ (wα mod 6)/6`,
so a single literal `fract` computation decides whether `s ∈ T`. -/
theorem wpos_eval {w : ℕ} {th : ℝ} (hth : Int.fract ((w : ℝ) * th) = 5 / 6)
    (lam al : ℕ) {c : ℝ}
    (h : Int.fract ((lam : ℝ) * (5 / 6 : ℝ) +
      (((w * al) % 6 : ℕ) : ℝ) / 6) = c) :
    Int.fract ((w : ℝ) * ((lam : ℝ) * th + (al : ℝ) / 6)) = c := by
  rw [fract_improve, hth]
  have hmod := Nat.div_add_mod (w * al) 6
  have hdiv : (w : ℝ) * (al : ℝ) / 6 =
      (((w * al) % 6 : ℕ) : ℝ) / 6 + (((w * al) / 6 : ℕ) : ℝ) := by
    have hwal : ((w * al : ℕ) : ℝ) =
        6 * (((w * al) / 6 : ℕ) : ℝ) + (((w * al) % 6 : ℕ) : ℝ) := by
      exact_mod_cast hmod.symm
    rw [← Nat.cast_mul, hwal]
    field_simp
    ring
  rw [hdiv, ← add_assoc, Int.fract_add_natCast]
  exact h

/-- An odd runner unsafe at `t` is safe at `t + 1/2` (the `+1/2` flip maps the
unsafe arc onto `(1/3,2/3)`). -/
theorem fract_half_shift_odd {d : ℕ} (hd : ¬ 2 ∣ d) (t : ℝ) :
    Int.fract ((d : ℝ) * (t + 1 / 2)) =
      Int.fract (Int.fract ((d : ℝ) * t) + 1 / 2) := by
  rw [fract_add_shift]
  have hmod2 : d % 2 = 1 := by omega
  obtain ⟨k, hk⟩ : Odd d := ⟨d / 2, by omega⟩
  have hd2 : (d : ℝ) * (1 / 2) = (k : ℝ) + 1 / 2 := by
    rw [hk]; push_cast; ring
  rw [hd2, show Int.fract ((d : ℝ) * t) + ((k : ℝ) + 1 / 2) =
      (Int.fract ((d : ℝ) * t) + 1 / 2) + (k : ℝ) by ring, Int.fract_add_natCast]

theorem unsafe_flip {d : ℕ} (hd : ¬ 2 ∣ d) (t : ℝ) (h : ¬ safe6 d t) :
    safe6 d (t + 1 / 2) := by
  rw [safe6] at h ⊢
  rw [fract_half_shift_odd hd]
  rw [Set.mem_Icc] at h
  have h2 : Int.fract ((d : ℝ) * t) < 1 / 6 ∨ 5 / 6 < Int.fract ((d : ℝ) * t) := by
    by_contra hc
    push Not at hc
    exact h hc
  have h0 := Int.fract_nonneg ((d : ℝ) * t)
  have h1 := Int.fract_lt_one ((d : ℝ) * t)
  rcases h2 with h2 | h2
  · rw [fract_of_between (n := 0) (by push_cast; linarith) (by push_cast; linarith)]
    constructor <;> push_cast <;> linarith
  · rw [fract_of_between (n := 1) (by push_cast; linarith) (by push_cast; linarith)]
    constructor <;> push_cast <;> linarith

/-- `⟨2y + 1/2⟩` is safe when `y` sits on the unsafe arc `[0,1/6) ∪ (5/6,1)` —
this is why the `4th + 1/2` runner `z` is safe in the parity subcase. -/
theorem safe_double_half_of_unsafe {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y < 1)
    (h : y < 1 / 6 ∨ 5 / 6 < y) :
    Int.fract (2 * y + 1 / 2) ∈ Set.Icc (1 / 6) (5 / 6) := by
  rcases h with hl | hr
  · rw [fract_of_between (n := 0) (by push_cast; linarith) (by push_cast; linarith)]
    constructor <;> push_cast <;> linarith
  · rw [fract_of_between (n := 2) (by push_cast; linarith) (by push_cast; linarith)]
    constructor <;> push_cast <;> linarith

/-- `⟨2y + 1/2⟩` is safe when `y ∈ (1/3,2/3)` — the `z'` runner at `4th+1/2`. -/
theorem safe_double_half_of_third {y : ℝ} (h : 1 / 3 < y ∧ y < 2 / 3) :
    Int.fract (2 * y + 1 / 2) ∈ Set.Icc (1 / 6) (5 / 6) := by
  rw [fract_of_between (n := 1) (by push_cast; linarith) (by push_cast; linarith)]
  constructor <;> push_cast <;> linarith

/-- `⟨y + 1/2⟩` unsafe pulls `y ∈ [0,1)` back into `(1/3,2/3)`. -/
theorem third_of_unsafe_half {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y < 1)
    (h : Int.fract (y + 1 / 2) ∉ Set.Icc (1 / 6) (5 / 6)) :
    1 / 3 < y ∧ y < 2 / 3 := by
  rw [Set.mem_Icc] at h
  have h2 := not_and_or.mp h
  rw [not_le, not_le] at h2
  by_cases hy5 : y < 1 / 2
  · rw [fract_of_between (n := 0) (by push_cast; linarith) (by push_cast; linarith)] at h2
    push_cast at h2
    rcases h2 with h2 | h2
    · linarith
    · constructor <;> linarith
  · push Not at hy5
    rw [fract_of_between (n := 1) (by push_cast; linarith) (by push_cast; linarith)] at h2
    push_cast at h2
    rcases h2 with h2 | h2
    · constructor <;> linarith
    · linarith

/-! ### The anchor: the maximizer has `circ (x₁ t̂) = 0` -/

/-- `circ (k·x) = circ (k·fract x)` — the direction used below. -/
private theorem circ_mul_eq_circ_mul_fract (k : ℕ) (x : ℝ) :
    circ ((k : ℝ) * x) = circ ((k : ℝ) * Int.fract x) :=
  (circ_nat_mul_fract k x).symm


/-- Renault's §3 extremal argument, ordered version: `a` is the min-achieving
multiple of 3 and `b` the other one.  If `th` maximizes `min circ` over the
`x_w = 5/6` lattice and `circ (a·th) ≤ circ (b·th)`, then `circ (a·th) = 0`:
the runner `a` sits exactly at the origin. -/
theorem anchor_ordered {a b w u u' : ℕ}
    (h3a : 3 ∣ a) (h3b : 3 ∣ b) (h3w : ¬ 3 ∣ w) (h3u : ¬ 3 ∣ u) (h3u' : ¬ 3 ∣ u')
    (hpos : ∀ d ∈ ({a, b, w, u, u'} : Finset ℕ), 0 < d)
    (hdist : a ≠ b ∧ a ≠ w ∧ b ≠ w ∧ a ≠ u ∧ b ≠ u ∧ w ≠ u ∧
      a ≠ u' ∧ b ≠ u' ∧ w ≠ u')
    (hgcd : ({a, b, w, u, u'} : Finset ℕ).gcd id = 1)
    (hf : hfail {a, b, w, u, u'})
    (h6dvd : 6 ∣ a ∨ 6 ∣ b)
    {th : ℝ} (hth : Int.fract ((w : ℝ) * th) = 5 / 6)
    (hmax : ∀ t : ℝ, Int.fract ((w : ℝ) * t) = 5 / 6 →
      min (circ ((a : ℝ) * t)) (circ ((b : ℝ) * t)) ≤
        min (circ ((a : ℝ) * th)) (circ ((b : ℝ) * th)))
    (hab : circ ((a : ℝ) * th) ≤ circ ((b : ℝ) * th)) :
    circ ((a : ℝ) * th) = 0 := by
  obtain ⟨nab, naw, nbw, nau, nbu, nwu, nau', nbu', nwu'⟩ := hdist
  set δ := circ ((a : ℝ) * th) with hδ
  have hmin : min (circ ((a : ℝ) * th)) (circ ((b : ℝ) * th)) = δ := min_eq_left hab
  -- Argument 2 at `th`: the two multiples cannot both be safe.
  have hns : ¬ (safe6 a th ∧ safe6 b th) := fun ⟨hsa, hsb⟩ =>
    arg2 h3a h3b h3w h3u h3u' hsa hsb (Or.inr (Or.inr hth)) hf
  have hδlt : δ < 1 / 6 := by
    have hm : min (circ ((a : ℝ) * th)) (circ ((b : ℝ) * th)) < 1 / 6 := by
      rcases not_and_or.mp hns with hnsa | hnsb
      · exact min_lt_iff.mpr (Or.inl
          (not_le.mp (mt (safe6_iff a th).mpr hnsa)))
      · exact min_lt_iff.mpr (Or.inr
          (not_le.mp (mt (safe6_iff b th).mpr hnsb)))
    rwa [hmin] at hm
  by_contra hδ0
  have hδpos : 0 < δ :=
    lt_of_le_of_ne' (by rw [hδ, circ_eq]; exact abs_nonneg _) hδ0
  -- boundary times `3·th`, `5·th`: `x_w` is `1/2` resp. `1/6`, so the min
  -- bound propagates; runner `a` improves, hence runner `b` is small.
  have hw3 : Int.fract ((w : ℝ) * (((3 : ℕ) : ℝ) * th)) = 1 / 2 := by
    rw [fract_nat_mul, hth]
    rw [fract_of_between (n := 2) (by push_cast; norm_num) (by push_cast; norm_num)]
    push_cast; norm_num
  have hbd3 := boundary_min_le h3a h3b h3w hmax (Or.inr (Or.inl hw3))
  rw [hmin] at hbd3
  have ha3 : δ < circ ((a : ℝ) * (((3 : ℕ) : ℝ) * th)) := by
    rw [show (a : ℝ) * (((3 : ℕ) : ℝ) * th) = ((3 : ℕ) : ℝ) * ((a : ℝ) * th) by ring]
    exact circ_lt_circ_nat_mul hδpos hδlt (k := 3) (by norm_num) (by norm_num)
  have hb3 : circ (((3 : ℕ) : ℝ) * Int.fract ((b : ℝ) * th)) ≤ δ := by
    rcases min_le_iff.mp hbd3 with h | h
    · linarith [ha3]
    · have e : circ ((b : ℝ) * (((3 : ℕ) : ℝ) * th)) =
          circ (((3 : ℕ) : ℝ) * ((b : ℝ) * th)) := by congr 1; ring
      rw [e, circ_mul_eq_circ_mul_fract] at h
      exact h
  have hw5 : Int.fract ((w : ℝ) * (((5 : ℕ) : ℝ) * th)) = 1 / 6 := by
    rw [fract_nat_mul, hth]
    rw [fract_of_between (n := 4) (by push_cast; norm_num) (by push_cast; norm_num)]
    push_cast; norm_num
  have hbd5 := boundary_min_le h3a h3b h3w hmax (Or.inl hw5)
  rw [hmin] at hbd5
  have ha5 : δ < circ ((a : ℝ) * (((5 : ℕ) : ℝ) * th)) := by
    rw [show (a : ℝ) * (((5 : ℕ) : ℝ) * th) = ((5 : ℕ) : ℝ) * ((a : ℝ) * th) by ring]
    exact circ_lt_circ_nat_mul hδpos hδlt (k := 5) (by norm_num) (by norm_num)
  have hb5 : circ (((5 : ℕ) : ℝ) * Int.fract ((b : ℝ) * th)) ≤ δ := by
    rcases min_le_iff.mp hbd5 with h | h
    · linarith [ha5]
    · have e : circ ((b : ℝ) * (((5 : ℕ) : ℝ) * th)) =
          circ (((5 : ℕ) : ℝ) * ((b : ℝ) * th)) := by congr 1; ring
      rw [e, circ_mul_eq_circ_mul_fract] at h
      exact h
  -- runner 2 (`b`) sits in the two surviving windows
  push_cast at hb3 hb5
  have hcy2 : circ (Int.fract ((b : ℝ) * th)) = circ ((b : ℝ) * th) := circ_fract _
  have hy2I0 := Int.fract_nonneg ((b : ℝ) * th)
  have hy2I1 := Int.fract_lt_one ((b : ℝ) * th)
  have hy2pos : 0 < Int.fract ((b : ℝ) * th) := by
    rcases eq_or_lt_of_le hy2I0 with h0 | h0
    · exfalso
      have hc0 : circ ((b : ℝ) * th) = 0 := by
        rw [← hcy2, ← h0, circ_eq]; simp
      linarith
    · exact h0
  have hb3' : circ (3 * Int.fract ((b : ℝ) * th)) < 1 / 6 := by linarith
  have hb5' : circ (5 * Int.fract ((b : ℝ) * th)) < 1 / 6 := by linarith
  have hU' := unsafe35_union hy2pos hy2I1 hb3' hb5'
  have hsurv : (11 / 30 < Int.fract ((b : ℝ) * th) ∧
      Int.fract ((b : ℝ) * th) < 7 / 18) ∨
      (11 / 18 < Int.fract ((b : ℝ) * th) ∧ Int.fract ((b : ℝ) * th) < 19 / 30) := by
    rcases hU' with hU | hU | hU | hU
    · exfalso
      have hcy : circ (Int.fract ((b : ℝ) * th)) = Int.fract ((b : ℝ) * th) := by
        rw [circ_eq_of_between (n := 0) (by push_cast; linarith) (by push_cast; linarith)]
        rw [min_eq_left (by push_cast; linarith)]; push_cast; ring
      have hg : δ < circ (3 * Int.fract ((b : ℝ) * th)) := by
        have h := circ_lt_circ_nat_mul (x := Int.fract ((b : ℝ) * th))
          (by linarith) (by linarith) (k := 3) (by norm_num) (by norm_num)
        push_cast at h
        linarith
      linarith
    · exfalso
      have hcy : circ (Int.fract ((b : ℝ) * th)) = 1 - Int.fract ((b : ℝ) * th) := by
        rw [circ_eq_of_between (n := 0) (by push_cast; linarith) (by push_cast; linarith)]
        rw [min_eq_right (by push_cast; linarith)]; push_cast; ring
      have hg : δ < circ (3 * Int.fract ((b : ℝ) * th)) := by
        have h := circ_lt_circ_nat_mul (x := Int.fract ((b : ℝ) * th))
          (by linarith) (by linarith) (k := 3) (by norm_num) (by norm_num)
        push_cast at h
        linarith
      linarith
    · exact Or.inl hU
    · exact Or.inr hU
  obtain hf2 := runner2_facts hsurv
  -- `circ (3·x₂) ≤ δ` and `fract (3·x₂) ∈ (1/10,1/6) ∪ (5/6,9/10)` give `δ > 1/10`
  have hδ10 : 1 / 10 < δ := by
    have hfn := Int.fract_nonneg (3 * Int.fract ((b : ℝ) * th))
    have hft := Int.fract_lt_one (3 * Int.fract ((b : ℝ) * th))
    have hc3 : 1 / 10 < circ (3 * Int.fract ((b : ℝ) * th)) := by
      rcases hf2.2.2.2.2.2.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [← circ_fract (3 * Int.fract ((b : ℝ) * th))]
        rw [circ_eq_of_between (n := 0) (by push_cast; linarith) (by push_cast; linarith)]
        rw [min_eq_left (by push_cast; linarith)]
        push_cast; linarith
      · rw [← circ_fract (3 * Int.fract ((b : ℝ) * th))]
        rw [circ_eq_of_between (n := 0) (by push_cast; linarith) (by push_cast; linarith)]
        rw [min_eq_right (by push_cast; linarith)]
        push_cast; linarith
    linarith
  -- runner 1 (`a`) lands in its own two windows
  have hcy1 : circ (Int.fract ((a : ℝ) * th)) = δ := by
    rw [hδ]; exact circ_fract _
  have hy1 := runner1_interval (y := Int.fract ((a : ℝ) * th))
      (Int.fract_nonneg _) (Int.fract_lt_one _) (by linarith) (by linarith)
  obtain hf1 := runner1_facts hy1
  -- `w mod 6 ∈ {1,2,4,5}`
  have hmw : w % 6 = 1 ∨ w % 6 = 2 ∨ w % 6 = 4 ∨ w % 6 = 5 := by
    have h6 : w % 6 = 0 ∨ w % 6 = 1 ∨ w % 6 = 2 ∨ w % 6 = 3 ∨ w % 6 = 4 ∨
        w % 6 = 5 := by omega
    rcases h6 with h | h | h | h | h | h
    · exact absurd ⟨2 * (w / 6), by omega⟩ h3w
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact absurd ⟨2 * (w / 6) + 1, by omega⟩ h3w
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  -- generic closer: a `T`-time where both runners beat `δ` is impossible
  have contra_of {s : ℝ} (hsT : Int.fract ((w : ℝ) * s) = 5 / 6)
      (ha : δ < circ ((a : ℝ) * s)) (hb : δ < circ ((b : ℝ) * s)) : False := by
    have hm := hmax s hsT
    rw [hmin] at hm
    rcases min_le_iff.mp hm with h | h
    · linarith
    · linarith
  by_cases h6a : 6 ∣ a
  · by_cases h6b : 6 ∣ b
    · -- `(e₁,e₂) = (0,0)`: `λ = 2` for `e_w ∈ {1,5}`, parity argument for `e_w ∈ {2,4}`
      rcases hmw with hw | hw | hw | hw
      · have hsT : Int.fract ((w : ℝ) * (((2 : ℕ) : ℝ) * th + ((1 : ℕ) : ℝ) / 6)) =
            5 / 6 := by
          apply wpos_eval hth 2 1
          rw [show (w * 1) % 6 = 1 by rw [Nat.mul_mod, hw]]
          rw [fract_of_between (n := 1) (by push_cast; norm_num) (by push_cast; norm_num)]
          push_cast; norm_num
        have hca : circ ((a : ℝ) * (((2 : ℕ) : ℝ) * th + ((1 : ℕ) : ℝ) / 6)) =
            circ (2 * Int.fract ((a : ℝ) * th)) := by
          have h := circ_move_dvd h6a th 2 1
          push_cast at h ⊢; exact h
        have hcb : circ ((b : ℝ) * (((2 : ℕ) : ℝ) * th + ((1 : ℕ) : ℝ) / 6)) =
            circ (2 * Int.fract ((b : ℝ) * th)) := by
          have h := circ_move_dvd h6b th 2 1
          push_cast at h ⊢; exact h
        exact contra_of hsT (by rw [hca, hf1.1, hcy1]; linarith)
          (by rw [hcb]; linarith [hf2.2.1.1])
      · -- `e_w = 2`: the parity subcase, both other runners odd
        have hw2 : 2 ∣ w := ⟨3 * (w / 6) + 1, by omega⟩
        have h2a : 2 ∣ a := by obtain ⟨k, hk⟩ := h6a; exact ⟨3 * k, by rw [hk]; ring⟩
        have h2b : 2 ∣ b := by obtain ⟨k, hk⟩ := h6b; exact ⟨3 * k, by rw [hk]; ring⟩
        have hcard5 : ({a, b, w, u, u'} : Finset ℕ).card ≤ 5 := by
          have h1 := Finset.card_insert_le a ({b, w, u, u'} : Finset ℕ)
          have h2 := Finset.card_insert_le b ({w, u, u'} : Finset ℕ)
          have h3 := Finset.card_insert_le w ({u, u'} : Finset ℕ)
          have h4 := Finset.card_insert_le u ({u'} : Finset ℕ)
          have h5 : ({u'} : Finset ℕ).card = 1 := Finset.card_singleton _
          omega
        have hfl := mult2_le_three hpos hcard5 hgcd hf
        have habw : a ∉ ({b, w} : Finset ℕ) := by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨nab, naw⟩
        have h3c : ({a, b, w} : Finset ℕ).card = 3 := by
          rw [Finset.card_insert_of_notMem habw,
            Finset.card_insert_of_notMem (by simp [nbw]), Finset.card_singleton]
        have hodd {x : ℕ} (hxD : x ∈ ({a, b, w, u, u'} : Finset ℕ))
            (hx : x ∉ ({a, b, w} : Finset ℕ)) : ¬ 2 ∣ x := by
          intro h2x
          have hsub4 : (insert x {a, b, w} : Finset ℕ) ⊆
              ({a, b, w, u, u'} : Finset ℕ).filter fun d => 2 ∣ d := by
            intro y hy
            simp only [Finset.mem_insert] at hy
            rw [Finset.mem_filter]
            rcases hy with rfl | hy
            · exact ⟨hxD, h2x⟩
            · simp only [Finset.mem_singleton] at hy
              rcases hy with rfl | rfl | rfl
              · exact ⟨by simp, h2a⟩
              · exact ⟨by simp, h2b⟩
              · exact ⟨by simp, hw2⟩
          have hc4 : (insert x {a, b, w} : Finset ℕ).card = 4 := by
            rw [Finset.card_insert_of_notMem hx, h3c]
          have := Finset.card_le_card hsub4
          rw [hc4] at this
          omega
        have hu_odd : ¬ 2 ∣ u :=
          hodd (by simp) (by
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨nau.symm, nbu.symm, nwu.symm⟩)
        have hu'_odd : ¬ 2 ∣ u' :=
          hodd (by simp) (by
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨nau'.symm, nbu'.symm, nwu'.symm⟩)
        -- safety at `2·th`
        have hws2 : safe6 w (((2 : ℕ) : ℝ) * th) := by
          rw [safe6, fract_nat_mul, hth]
          rw [fract_of_between (n := 1) (by push_cast; norm_num) (by push_cast; norm_num)]
          push_cast
          constructor <;> norm_num
        have has2 : safe6 a (((2 : ℕ) : ℝ) * th) := by
          rw [safe6, fract_nat_mul]
          push_cast
          exact hf1.2.2.2.1
        have hbs2 : safe6 b (((2 : ℕ) : ℝ) * th) := by
          rw [safe6, fract_nat_mul]
          push_cast
          exact hf2.2.2.2.2.1
        obtain ⟨z, hzD, hzbad⟩ := hf (((2 : ℕ) : ℝ) * th)
        have hzmem : z = u ∨ z = u' := by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hzD
          rcases hzD with rfl | rfl | rfl | rfl | rfl
          · exact absurd has2 hzbad
          · exact absurd hbs2 hzbad
          · exact absurd hws2 hzbad
          · exact Or.inl rfl
          · exact Or.inr rfl
        have hyz : Int.fract ((z : ℝ) * (((2 : ℕ) : ℝ) * th)) < 1 / 6 ∨
            5 / 6 < Int.fract ((z : ℝ) * (((2 : ℕ) : ℝ) * th)) := by
          have h := hzbad
          rw [safe6, Set.mem_Icc] at h
          have h2 := not_and_or.mp h
          rwa [not_le, not_le] at h2
        have hodd_z : ¬ 2 ∣ z := by
          rcases hzmem with rfl | rfl; exacts [hu_odd, hu'_odd]
        -- safety at `2·th + 1/2`
        have hws2' : safe6 w (((2 : ℕ) : ℝ) * th + 1 / 2) :=
          (safe6_half_shift_of_dvd hw2 _).mpr hws2
        have has2' : safe6 a (((2 : ℕ) : ℝ) * th + 1 / 2) :=
          (safe6_half_shift_of_dvd h2a _).mpr has2
        have hbs2' : safe6 b (((2 : ℕ) : ℝ) * th + 1 / 2) :=
          (safe6_half_shift_of_dvd h2b _).mpr hbs2
        obtain ⟨z', hz'D, hz'bad⟩ := hf (((2 : ℕ) : ℝ) * th + 1 / 2)
        have hz'mem : z' = u ∨ z' = u' := by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz'D
          rcases hz'D with rfl | rfl | rfl | rfl | rfl
          · exact absurd has2' hz'bad
          · exact absurd hbs2' hz'bad
          · exact absurd hws2' hz'bad
          · exact Or.inl rfl
          · exact Or.inr rfl
        have hodd_z' : ¬ 2 ∣ z' := by
          rcases hz'mem with rfl | rfl; exacts [hu_odd, hu'_odd]
        have hzz' : z ≠ z' := by
          rintro rfl
          exact hz'bad (unsafe_flip hodd_z _ hzbad)
        have hyz' : 1 / 3 < Int.fract ((z' : ℝ) * (((2 : ℕ) : ℝ) * th)) ∧
            Int.fract ((z' : ℝ) * (((2 : ℕ) : ℝ) * th)) < 2 / 3 := by
          have h := hz'bad
          rw [safe6] at h
          rw [fract_half_shift_odd hodd_z'] at h
          exact third_of_unsafe_half (Int.fract_nonneg _) (Int.fract_lt_one _) h
        -- all safe at `4·th + 1/2`
        have has4 : safe6 a (((4 : ℕ) : ℝ) * th + 1 / 2) := by
          rw [safe6]
          have he : Int.fract ((a : ℝ) * (((4 : ℕ) : ℝ) * th + 1 / 2)) =
              Int.fract (4 * Int.fract ((a : ℝ) * th)) := by
            rw [fract_add_shift]
            obtain ⟨m, hm⟩ := h2a
            rw [show (a : ℝ) * (1 / 2) = (m : ℝ) by rw [hm]; push_cast; ring]
            rw [Int.fract_add_natCast, Int.fract_fract, fract_nat_mul]
            push_cast
            try ring_nf
          rw [he]
          exact hf1.2.2.2.2
        have hbs4 : safe6 b (((4 : ℕ) : ℝ) * th + 1 / 2) := by
          rw [safe6]
          have he : Int.fract ((b : ℝ) * (((4 : ℕ) : ℝ) * th + 1 / 2)) =
              Int.fract (4 * Int.fract ((b : ℝ) * th)) := by
            rw [fract_add_shift]
            obtain ⟨m, hm⟩ := h2b
            rw [show (b : ℝ) * (1 / 2) = (m : ℝ) by rw [hm]; push_cast; ring]
            rw [Int.fract_add_natCast, Int.fract_fract, fract_nat_mul]
            push_cast
            try ring_nf
          rw [he]
          exact hf2.2.2.2.2.2.1
        have hws4 : safe6 w (((4 : ℕ) : ℝ) * th + 1 / 2) := by
          rw [safe6]
          have he : Int.fract ((w : ℝ) * (((4 : ℕ) : ℝ) * th + 1 / 2)) = 1 / 3 := by
            rw [fract_add_shift]
            obtain ⟨m, hm⟩ := hw2
            rw [show (w : ℝ) * (1 / 2) = (m : ℝ) by rw [hm]; push_cast; ring]
            rw [Int.fract_add_natCast, Int.fract_fract, fract_nat_mul, hth]
            rw [fract_of_between (n := 3) (by push_cast; norm_num)
                (by push_cast; norm_num)]
            push_cast; norm_num
          rw [he]
          constructor <;> norm_num
        have hzs4 : safe6 z (((4 : ℕ) : ℝ) * th + 1 / 2) := by
          rw [safe6]
          have he : Int.fract ((z : ℝ) * (((4 : ℕ) : ℝ) * th + 1 / 2)) =
              Int.fract (2 * Int.fract ((z : ℝ) * (((2 : ℕ) : ℝ) * th)) + 1 / 2) := by
            rw [fract_half_shift_odd hodd_z]
            rw [show ((4 : ℕ) : ℝ) * th = ((2 : ℕ) : ℝ) * (((2 : ℕ) : ℝ) * th) by
              push_cast; ring]
            rw [fract_nat_mul, Int.fract_fract_add]
            push_cast
            try ring_nf
          rw [he]
          exact safe_double_half_of_unsafe (Int.fract_nonneg _) (Int.fract_lt_one _) hyz
        have hz's4 : safe6 z' (((4 : ℕ) : ℝ) * th + 1 / 2) := by
          rw [safe6]
          have he : Int.fract ((z' : ℝ) * (((4 : ℕ) : ℝ) * th + 1 / 2)) =
              Int.fract (2 * Int.fract ((z' : ℝ) * (((2 : ℕ) : ℝ) * th)) + 1 / 2) := by
            rw [fract_half_shift_odd hodd_z']
            rw [show ((4 : ℕ) : ℝ) * th = ((2 : ℕ) : ℝ) * (((2 : ℕ) : ℝ) * th) by
              push_cast; ring]
            rw [fract_nat_mul, Int.fract_fract_add]
            push_cast
            try ring_nf
          rw [he]
          exact safe_double_half_of_third hyz'
        have hcover : z = u ∧ z' = u' ∨ z = u' ∧ z' = u := by
          rcases hzmem with rfl | rfl <;> rcases hz'mem with rfl | rfl
          · exact absurd rfl hzz'
          · exact Or.inl ⟨rfl, rfl⟩
          · exact Or.inr ⟨rfl, rfl⟩
          · exact absurd rfl hzz'
        rcases hcover with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact all_safe5_contra has4 hbs4 hws4 hzs4 hz's4 hf
        · exact all_safe5_contra has4 hbs4 hws4 hz's4 hzs4 hf
      · -- `e_w = 4`: the parity subcase again
        have hw2 : 2 ∣ w := ⟨3 * (w / 6) + 2, by omega⟩
        have h2a : 2 ∣ a := by obtain ⟨k, hk⟩ := h6a; exact ⟨3 * k, by rw [hk]; ring⟩
        have h2b : 2 ∣ b := by obtain ⟨k, hk⟩ := h6b; exact ⟨3 * k, by rw [hk]; ring⟩
        have hcard5 : ({a, b, w, u, u'} : Finset ℕ).card ≤ 5 := by
          have h1 := Finset.card_insert_le a ({b, w, u, u'} : Finset ℕ)
          have h2 := Finset.card_insert_le b ({w, u, u'} : Finset ℕ)
          have h3 := Finset.card_insert_le w ({u, u'} : Finset ℕ)
          have h4 := Finset.card_insert_le u ({u'} : Finset ℕ)
          have h5 : ({u'} : Finset ℕ).card = 1 := Finset.card_singleton _
          omega
        have hfl := mult2_le_three hpos hcard5 hgcd hf
        have habw : a ∉ ({b, w} : Finset ℕ) := by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨nab, naw⟩
        have h3c : ({a, b, w} : Finset ℕ).card = 3 := by
          rw [Finset.card_insert_of_notMem habw,
            Finset.card_insert_of_notMem (by simp [nbw]), Finset.card_singleton]
        have hodd {x : ℕ} (hxD : x ∈ ({a, b, w, u, u'} : Finset ℕ))
            (hx : x ∉ ({a, b, w} : Finset ℕ)) : ¬ 2 ∣ x := by
          intro h2x
          have hsub4 : (insert x {a, b, w} : Finset ℕ) ⊆
              ({a, b, w, u, u'} : Finset ℕ).filter fun d => 2 ∣ d := by
            intro y hy
            simp only [Finset.mem_insert] at hy
            rw [Finset.mem_filter]
            rcases hy with rfl | hy
            · exact ⟨hxD, h2x⟩
            · simp only [Finset.mem_singleton] at hy
              rcases hy with rfl | rfl | rfl
              · exact ⟨by simp, h2a⟩
              · exact ⟨by simp, h2b⟩
              · exact ⟨by simp, hw2⟩
          have hc4 : (insert x {a, b, w} : Finset ℕ).card = 4 := by
            rw [Finset.card_insert_of_notMem hx, h3c]
          have := Finset.card_le_card hsub4
          rw [hc4] at this
          omega
        have hu_odd : ¬ 2 ∣ u :=
          hodd (by simp) (by
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨nau.symm, nbu.symm, nwu.symm⟩)
        have hu'_odd : ¬ 2 ∣ u' :=
          hodd (by simp) (by
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨nau'.symm, nbu'.symm, nwu'.symm⟩)
        have hws2 : safe6 w (((2 : ℕ) : ℝ) * th) := by
          rw [safe6, fract_nat_mul, hth]
          rw [fract_of_between (n := 1) (by push_cast; norm_num) (by push_cast; norm_num)]
          push_cast
          constructor <;> norm_num
        have has2 : safe6 a (((2 : ℕ) : ℝ) * th) := by
          rw [safe6, fract_nat_mul]
          push_cast
          exact hf1.2.2.2.1
        have hbs2 : safe6 b (((2 : ℕ) : ℝ) * th) := by
          rw [safe6, fract_nat_mul]
          push_cast
          exact hf2.2.2.2.2.1
        obtain ⟨z, hzD, hzbad⟩ := hf (((2 : ℕ) : ℝ) * th)
        have hzmem : z = u ∨ z = u' := by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hzD
          rcases hzD with rfl | rfl | rfl | rfl | rfl
          · exact absurd has2 hzbad
          · exact absurd hbs2 hzbad
          · exact absurd hws2 hzbad
          · exact Or.inl rfl
          · exact Or.inr rfl
        have hyz : Int.fract ((z : ℝ) * (((2 : ℕ) : ℝ) * th)) < 1 / 6 ∨
            5 / 6 < Int.fract ((z : ℝ) * (((2 : ℕ) : ℝ) * th)) := by
          have h := hzbad
          rw [safe6, Set.mem_Icc] at h
          have h2 := not_and_or.mp h
          rwa [not_le, not_le] at h2
        have hodd_z : ¬ 2 ∣ z := by
          rcases hzmem with rfl | rfl; exacts [hu_odd, hu'_odd]
        have hws2' : safe6 w (((2 : ℕ) : ℝ) * th + 1 / 2) :=
          (safe6_half_shift_of_dvd hw2 _).mpr hws2
        have has2' : safe6 a (((2 : ℕ) : ℝ) * th + 1 / 2) :=
          (safe6_half_shift_of_dvd h2a _).mpr has2
        have hbs2' : safe6 b (((2 : ℕ) : ℝ) * th + 1 / 2) :=
          (safe6_half_shift_of_dvd h2b _).mpr hbs2
        obtain ⟨z', hz'D, hz'bad⟩ := hf (((2 : ℕ) : ℝ) * th + 1 / 2)
        have hz'mem : z' = u ∨ z' = u' := by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz'D
          rcases hz'D with rfl | rfl | rfl | rfl | rfl
          · exact absurd has2' hz'bad
          · exact absurd hbs2' hz'bad
          · exact absurd hws2' hz'bad
          · exact Or.inl rfl
          · exact Or.inr rfl
        have hodd_z' : ¬ 2 ∣ z' := by
          rcases hz'mem with rfl | rfl; exacts [hu_odd, hu'_odd]
        have hzz' : z ≠ z' := by
          rintro rfl
          exact hz'bad (unsafe_flip hodd_z _ hzbad)
        have hyz' : 1 / 3 < Int.fract ((z' : ℝ) * (((2 : ℕ) : ℝ) * th)) ∧
            Int.fract ((z' : ℝ) * (((2 : ℕ) : ℝ) * th)) < 2 / 3 := by
          have h := hz'bad
          rw [safe6] at h
          rw [fract_half_shift_odd hodd_z'] at h
          exact third_of_unsafe_half (Int.fract_nonneg _) (Int.fract_lt_one _) h
        have has4 : safe6 a (((4 : ℕ) : ℝ) * th + 1 / 2) := by
          rw [safe6]
          have he : Int.fract ((a : ℝ) * (((4 : ℕ) : ℝ) * th + 1 / 2)) =
              Int.fract (4 * Int.fract ((a : ℝ) * th)) := by
            rw [fract_add_shift]
            obtain ⟨m, hm⟩ := h2a
            rw [show (a : ℝ) * (1 / 2) = (m : ℝ) by rw [hm]; push_cast; ring]
            rw [Int.fract_add_natCast, Int.fract_fract, fract_nat_mul]
            push_cast
            try ring_nf
          rw [he]
          exact hf1.2.2.2.2
        have hbs4 : safe6 b (((4 : ℕ) : ℝ) * th + 1 / 2) := by
          rw [safe6]
          have he : Int.fract ((b : ℝ) * (((4 : ℕ) : ℝ) * th + 1 / 2)) =
              Int.fract (4 * Int.fract ((b : ℝ) * th)) := by
            rw [fract_add_shift]
            obtain ⟨m, hm⟩ := h2b
            rw [show (b : ℝ) * (1 / 2) = (m : ℝ) by rw [hm]; push_cast; ring]
            rw [Int.fract_add_natCast, Int.fract_fract, fract_nat_mul]
            push_cast
            try ring_nf
          rw [he]
          exact hf2.2.2.2.2.2.1
        have hws4 : safe6 w (((4 : ℕ) : ℝ) * th + 1 / 2) := by
          rw [safe6]
          have he : Int.fract ((w : ℝ) * (((4 : ℕ) : ℝ) * th + 1 / 2)) = 1 / 3 := by
            rw [fract_add_shift]
            obtain ⟨m, hm⟩ := hw2
            rw [show (w : ℝ) * (1 / 2) = (m : ℝ) by rw [hm]; push_cast; ring]
            rw [Int.fract_add_natCast, Int.fract_fract, fract_nat_mul, hth]
            rw [fract_of_between (n := 3) (by push_cast; norm_num)
                (by push_cast; norm_num)]
            push_cast; norm_num
          rw [he]
          constructor <;> norm_num
        have hzs4 : safe6 z (((4 : ℕ) : ℝ) * th + 1 / 2) := by
          rw [safe6]
          have he : Int.fract ((z : ℝ) * (((4 : ℕ) : ℝ) * th + 1 / 2)) =
              Int.fract (2 * Int.fract ((z : ℝ) * (((2 : ℕ) : ℝ) * th)) + 1 / 2) := by
            rw [fract_half_shift_odd hodd_z]
            rw [show ((4 : ℕ) : ℝ) * th = ((2 : ℕ) : ℝ) * (((2 : ℕ) : ℝ) * th) by
              push_cast; ring]
            rw [fract_nat_mul, Int.fract_fract_add]
            push_cast
            try ring_nf
          rw [he]
          exact safe_double_half_of_unsafe (Int.fract_nonneg _) (Int.fract_lt_one _) hyz
        have hz's4 : safe6 z' (((4 : ℕ) : ℝ) * th + 1 / 2) := by
          rw [safe6]
          have he : Int.fract ((z' : ℝ) * (((4 : ℕ) : ℝ) * th + 1 / 2)) =
              Int.fract (2 * Int.fract ((z' : ℝ) * (((2 : ℕ) : ℝ) * th)) + 1 / 2) := by
            rw [fract_half_shift_odd hodd_z']
            rw [show ((4 : ℕ) : ℝ) * th = ((2 : ℕ) : ℝ) * (((2 : ℕ) : ℝ) * th) by
              push_cast; ring]
            rw [fract_nat_mul, Int.fract_fract_add]
            push_cast
            try ring_nf
          rw [he]
          exact safe_double_half_of_third hyz'
        have hcover : z = u ∧ z' = u' ∨ z = u' ∧ z' = u := by
          rcases hzmem with rfl | rfl <;> rcases hz'mem with rfl | rfl
          · exact absurd rfl hzz'
          · exact Or.inl ⟨rfl, rfl⟩
          · exact Or.inr ⟨rfl, rfl⟩
          · exact absurd rfl hzz'
        rcases hcover with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact all_safe5_contra has4 hbs4 hws4 hzs4 hz's4 hf
        · exact all_safe5_contra has4 hbs4 hws4 hz's4 hzs4 hf
      · have hsT : Int.fract ((w : ℝ) * (((2 : ℕ) : ℝ) * th + ((5 : ℕ) : ℝ) / 6)) =
            5 / 6 := by
          apply wpos_eval hth 2 5
          rw [show (w * 5) % 6 = 1 by rw [Nat.mul_mod, hw]]
          rw [fract_of_between (n := 1) (by push_cast; norm_num) (by push_cast; norm_num)]
          push_cast; norm_num
        have hca : circ ((a : ℝ) * (((2 : ℕ) : ℝ) * th + ((5 : ℕ) : ℝ) / 6)) =
            circ (2 * Int.fract ((a : ℝ) * th)) := by
          have h := circ_move_dvd h6a th 2 5
          push_cast at h ⊢; exact h
        have hcb : circ ((b : ℝ) * (((2 : ℕ) : ℝ) * th + ((5 : ℕ) : ℝ) / 6)) =
            circ (2 * Int.fract ((b : ℝ) * th)) := by
          have h := circ_move_dvd h6b th 2 5
          push_cast at h ⊢; exact h
        exact contra_of hsT (by rw [hca, hf1.1, hcy1]; linarith)
          (by rw [hcb]; linarith [hf2.2.1.1])

    · -- `(e₁,e₂) = (0,3)`: `λ = 2` for `e_w ∈ {1,5}`, `λ = 3` for `e_w ∈ {2,4}`
      have hn6b : ¬ 6 ∣ b := h6b
      rcases hmw with hw | hw | hw | hw
      · have hsT : Int.fract ((w : ℝ) * (((2 : ℕ) : ℝ) * th + ((1 : ℕ) : ℝ) / 6)) =
            5 / 6 := by
          apply wpos_eval hth 2 1
          rw [show (w * 1) % 6 = 1 by rw [Nat.mul_mod, hw]]
          rw [fract_of_between (n := 1) (by push_cast; norm_num) (by push_cast; norm_num)]
          push_cast; norm_num
        have hca : circ ((a : ℝ) * (((2 : ℕ) : ℝ) * th + ((1 : ℕ) : ℝ) / 6)) =
            circ (2 * Int.fract ((a : ℝ) * th)) := by
          have h := circ_move_dvd h6a th 2 1
          push_cast at h ⊢; exact h
        have hcb : circ ((b : ℝ) * (((2 : ℕ) : ℝ) * th + ((1 : ℕ) : ℝ) / 6)) =
            circ (2 * Int.fract ((b : ℝ) * th) + 1 / 2) := by
          have h := circ_move_three h3b hn6b (Or.inl rfl) th 2
          push_cast at h ⊢; exact h
        exact contra_of hsT (by rw [hca, hf1.1, hcy1]; linarith)
          (by rw [hcb]; linarith [hf2.2.2.1.1])
      · have hsT : Int.fract ((w : ℝ) * (((3 : ℕ) : ℝ) * th + ((1 : ℕ) : ℝ) / 6)) =
            5 / 6 := by
          apply wpos_eval hth 3 1
          rw [show (w * 1) % 6 = 2 by rw [Nat.mul_mod, hw]]
          rw [fract_of_between (n := 2) (by push_cast; norm_num) (by push_cast; norm_num)]
          push_cast; norm_num
        have hca : circ ((a : ℝ) * (((3 : ℕ) : ℝ) * th + ((1 : ℕ) : ℝ) / 6)) =
            circ (3 * Int.fract ((a : ℝ) * th)) := by
          have h := circ_move_dvd h6a th 3 1
          push_cast at h ⊢; exact h
        have hcb : circ ((b : ℝ) * (((3 : ℕ) : ℝ) * th + ((1 : ℕ) : ℝ) / 6)) =
            circ (3 * Int.fract ((b : ℝ) * th) + 1 / 2) := by
          have h := circ_move_three h3b hn6b (Or.inl rfl) th 3
          push_cast at h ⊢; exact h
        have hgt : δ < circ (3 * Int.fract ((a : ℝ) * th)) := by
          rw [← hcy1]
          exact circ_lt_circ_nat_mul (x := Int.fract ((a : ℝ) * th))
            (by rw [hcy1]; exact hδpos) (by rw [hcy1]; exact hδlt)
            (k := 3) (by norm_num) (by norm_num)
        exact contra_of hsT (by rwa [hca]) (by rw [hcb]; linarith [hf2.2.2.2.1.1])
      · have hsT : Int.fract ((w : ℝ) * (((3 : ℕ) : ℝ) * th + ((5 : ℕ) : ℝ) / 6)) =
            5 / 6 := by
          apply wpos_eval hth 3 5
          rw [show (w * 5) % 6 = 2 by rw [Nat.mul_mod, hw]]
          rw [fract_of_between (n := 2) (by push_cast; norm_num) (by push_cast; norm_num)]
          push_cast; norm_num
        have hca : circ ((a : ℝ) * (((3 : ℕ) : ℝ) * th + ((5 : ℕ) : ℝ) / 6)) =
            circ (3 * Int.fract ((a : ℝ) * th)) := by
          have h := circ_move_dvd h6a th 3 5
          push_cast at h ⊢; exact h
        have hcb : circ ((b : ℝ) * (((3 : ℕ) : ℝ) * th + ((5 : ℕ) : ℝ) / 6)) =
            circ (3 * Int.fract ((b : ℝ) * th) + 1 / 2) := by
          have h := circ_move_three h3b hn6b (Or.inr (Or.inr rfl)) th 3
          push_cast at h ⊢; exact h
        have hgt : δ < circ (3 * Int.fract ((a : ℝ) * th)) := by
          rw [← hcy1]
          exact circ_lt_circ_nat_mul (x := Int.fract ((a : ℝ) * th))
            (by rw [hcy1]; exact hδpos) (by rw [hcy1]; exact hδlt)
            (k := 3) (by norm_num) (by norm_num)
        exact contra_of hsT (by rwa [hca]) (by rw [hcb]; linarith [hf2.2.2.2.1.1])
      · have hsT : Int.fract ((w : ℝ) * (((2 : ℕ) : ℝ) * th + ((5 : ℕ) : ℝ) / 6)) =
            5 / 6 := by
          apply wpos_eval hth 2 5
          rw [show (w * 5) % 6 = 1 by rw [Nat.mul_mod, hw]]
          rw [fract_of_between (n := 1) (by push_cast; norm_num) (by push_cast; norm_num)]
          push_cast; norm_num
        have hca : circ ((a : ℝ) * (((2 : ℕ) : ℝ) * th + ((5 : ℕ) : ℝ) / 6)) =
            circ (2 * Int.fract ((a : ℝ) * th)) := by
          have h := circ_move_dvd h6a th 2 5
          push_cast at h ⊢; exact h
        have hcb : circ ((b : ℝ) * (((2 : ℕ) : ℝ) * th + ((5 : ℕ) : ℝ) / 6)) =
            circ (2 * Int.fract ((b : ℝ) * th) + 1 / 2) := by
          have h := circ_move_three h3b hn6b (Or.inr (Or.inr rfl)) th 2
          push_cast at h ⊢; exact h
        exact contra_of hsT (by rw [hca, hf1.1, hcy1]; linarith)
          (by rw [hcb]; linarith [hf2.2.2.1.1])

  · by_cases h6b : 6 ∣ b
    · -- `(e₁,e₂) = (3,0)`: `λ = 2` for `e_w ∈ {1,5}`, `λ = 1` for `e_w ∈ {2,4}`
      have hn6a : ¬ 6 ∣ a := h6a
      rcases hmw with hw | hw | hw | hw
      · have hsT : Int.fract ((w : ℝ) * (((2 : ℕ) : ℝ) * th + ((1 : ℕ) : ℝ) / 6)) =
            5 / 6 := by
          apply wpos_eval hth 2 1
          rw [show (w * 1) % 6 = 1 by rw [Nat.mul_mod, hw]]
          rw [fract_of_between (n := 1) (by push_cast; norm_num) (by push_cast; norm_num)]
          push_cast; norm_num
        have hca : circ ((a : ℝ) * (((2 : ℕ) : ℝ) * th + ((1 : ℕ) : ℝ) / 6)) =
            circ (2 * Int.fract ((a : ℝ) * th) + 1 / 2) := by
          have h := circ_move_three h3a hn6a (Or.inl rfl) th 2
          push_cast at h ⊢; exact h
        have hcb : circ ((b : ℝ) * (((2 : ℕ) : ℝ) * th + ((1 : ℕ) : ℝ) / 6)) =
            circ (2 * Int.fract ((b : ℝ) * th)) := by
          have h := circ_move_dvd h6b th 2 1
          push_cast at h ⊢; exact h
        exact contra_of hsT (by rw [hca]; linarith [hf1.2.1.1])
          (by rw [hcb]; linarith [hf2.2.1.1])
      · have hsT : Int.fract ((w : ℝ) * (((1 : ℕ) : ℝ) * th + ((3 : ℕ) : ℝ) / 6)) =
            5 / 6 := by
          apply wpos_eval hth 1 3
          rw [show (w * 3) % 6 = 0 by rw [Nat.mul_mod, hw]]
          rw [fract_of_between (n := 0) (by push_cast; norm_num) (by push_cast; norm_num)]
          push_cast; norm_num
        have hca : circ ((a : ℝ) * (((1 : ℕ) : ℝ) * th + ((3 : ℕ) : ℝ) / 6)) =
            circ (Int.fract ((a : ℝ) * th) + 1 / 2) := by
          have h := circ_move_three h3a hn6a (Or.inr (Or.inl rfl)) th 1
          push_cast at h ⊢; simpa using h
        have hcb : circ ((b : ℝ) * (((1 : ℕ) : ℝ) * th + ((3 : ℕ) : ℝ) / 6)) =
            circ (Int.fract ((b : ℝ) * th)) := by
          have h := circ_move_dvd h6b th 1 3
          push_cast at h ⊢; simpa using h
        exact contra_of hsT (by rw [hca]; linarith [hf1.2.2.1.1])
          (by rw [hcb]; linarith [hf2.1.1])
      · have hsT : Int.fract ((w : ℝ) * (((1 : ℕ) : ℝ) * th + ((3 : ℕ) : ℝ) / 6)) =
            5 / 6 := by
          apply wpos_eval hth 1 3
          rw [show (w * 3) % 6 = 0 by rw [Nat.mul_mod, hw]]
          rw [fract_of_between (n := 0) (by push_cast; norm_num) (by push_cast; norm_num)]
          push_cast; norm_num
        have hca : circ ((a : ℝ) * (((1 : ℕ) : ℝ) * th + ((3 : ℕ) : ℝ) / 6)) =
            circ (Int.fract ((a : ℝ) * th) + 1 / 2) := by
          have h := circ_move_three h3a hn6a (Or.inr (Or.inl rfl)) th 1
          push_cast at h ⊢; simpa using h
        have hcb : circ ((b : ℝ) * (((1 : ℕ) : ℝ) * th + ((3 : ℕ) : ℝ) / 6)) =
            circ (Int.fract ((b : ℝ) * th)) := by
          have h := circ_move_dvd h6b th 1 3
          push_cast at h ⊢; simpa using h
        exact contra_of hsT (by rw [hca]; linarith [hf1.2.2.1.1])
          (by rw [hcb]; linarith [hf2.1.1])
      · have hsT : Int.fract ((w : ℝ) * (((2 : ℕ) : ℝ) * th + ((5 : ℕ) : ℝ) / 6)) =
            5 / 6 := by
          apply wpos_eval hth 2 5
          rw [show (w * 5) % 6 = 1 by rw [Nat.mul_mod, hw]]
          rw [fract_of_between (n := 1) (by push_cast; norm_num) (by push_cast; norm_num)]
          push_cast; norm_num
        have hca : circ ((a : ℝ) * (((2 : ℕ) : ℝ) * th + ((5 : ℕ) : ℝ) / 6)) =
            circ (2 * Int.fract ((a : ℝ) * th) + 1 / 2) := by
          have h := circ_move_three h3a hn6a (Or.inr (Or.inr rfl)) th 2
          push_cast at h ⊢; exact h
        have hcb : circ ((b : ℝ) * (((2 : ℕ) : ℝ) * th + ((5 : ℕ) : ℝ) / 6)) =
            circ (2 * Int.fract ((b : ℝ) * th)) := by
          have h := circ_move_dvd h6b th 2 5
          push_cast at h ⊢; exact h
        exact contra_of hsT (by rw [hca]; linarith [hf1.2.1.1])
          (by rw [hcb]; linarith [hf2.2.1.1])

    · exact absurd h6dvd (by push Not; exact ⟨h6a, h6b⟩)

/-- `key_per_w`, applied to each non-multiple `w` of 3.  At `t = -1/(6w)`
runner `w` sits at `5/6`; maximality forces `min = 0`, so one of the two
multiples of 3 is at `0` there — i.e. `6w` divides it. -/
theorem six_mul_dvd {a b w u u' : ℕ}
    (h3a : 3 ∣ a) (h3b : 3 ∣ b) (h3w : ¬ 3 ∣ w) (h3u : ¬ 3 ∣ u) (h3u' : ¬ 3 ∣ u')
    (hpos : ∀ d ∈ ({a, b, w, u, u'} : Finset ℕ), 0 < d)
    (hdist : a ≠ b ∧ a ≠ w ∧ b ≠ w ∧ a ≠ u ∧ b ≠ u ∧ w ≠ u ∧
      a ≠ u' ∧ b ≠ u' ∧ w ≠ u')
    (hgcd : ({a, b, w, u, u'} : Finset ℕ).gcd id = 1)
    (hf : hfail {a, b, w, u, u'})
    (h6dvd : 6 ∣ a ∨ 6 ∣ b) :
    (6 * w) ∣ a ∨ (6 * w) ∣ b := by
  have hw : 0 < w := hpos w (by simp)
  obtain ⟨th, hth, hmax⟩ := exists_min_circ_max (v₁ := a) (v₂ := b) (w := w) hw
  -- at the maximizer the nearer multiple of 3 sits at `0`
  have hmin0 : min (circ ((a : ℝ) * th)) (circ ((b : ℝ) * th)) = 0 := by
    rcases le_total (circ ((a : ℝ) * th)) (circ ((b : ℝ) * th)) with hab | hba
    · rw [min_eq_left hab]
      exact anchor_ordered h3a h3b h3w h3u h3u' hpos hdist hgcd hf h6dvd hth hmax
        hab
    · have hswap : ({b, a, w, u, u'} : Finset ℕ) = {a, b, w, u, u'} :=
        Finset.insert_comm _ _ _
      have hpos' : ∀ d ∈ ({b, a, w, u, u'} : Finset ℕ), 0 < d := by
        rw [hswap]; exact hpos
      obtain ⟨nab, naw, nbw, nau, nbu, nwu, nau', nbu', nwu'⟩ := hdist
      have hdist' : b ≠ a ∧ b ≠ w ∧ a ≠ w ∧ b ≠ u ∧ a ≠ u ∧ w ≠ u ∧
          b ≠ u' ∧ a ≠ u' ∧ w ≠ u' :=
        ⟨nab.symm, nbw, naw, nbu, nau, nwu, nbu', nau', nwu'⟩
      have hgcd' : ({b, a, w, u, u'} : Finset ℕ).gcd id = 1 := by
        rw [hswap]; exact hgcd
      have hf' : hfail {b, a, w, u, u'} := by rw [hswap]; exact hf
      have hmax' : ∀ t : ℝ, Int.fract ((w : ℝ) * t) = 5 / 6 →
          min (circ ((b : ℝ) * t)) (circ ((a : ℝ) * t)) ≤
            min (circ ((b : ℝ) * th)) (circ ((a : ℝ) * th)) := by
        intro t ht
        rw [min_comm (circ ((b : ℝ) * t)), min_comm (circ ((b : ℝ) * th))]
        exact hmax t ht
      rw [min_eq_right hba]
      exact anchor_ordered h3b h3a h3w h3u h3u' hpos' hdist' hgcd' hf'
        h6dvd.symm hth hmax' hba
  -- evaluate at `t₀ = -1/(6w)`: `x_w = -1/6 ≡ 5/6`, so `min ≤ 0`
  have hw' : (0 : ℝ) < w := by exact_mod_cast hw
  have hw6 : (0 : ℝ) < 6 * (w : ℝ) := by positivity
  set t0 : ℝ := -1 / (6 * (w : ℝ)) with ht0
  have hxt : Int.fract ((w : ℝ) * t0) = 5 / 6 := by
    have e : (w : ℝ) * t0 = -1 / 6 := by rw [ht0]; field_simp
    rw [e]
    rw [fract_of_between (n := -1) (by push_cast; norm_num)
      (by push_cast; norm_num)]
    push_cast; norm_num
  have hmin0' : min (circ ((a : ℝ) * t0)) (circ ((b : ℝ) * t0)) = 0 := by
    apply le_antisymm
    · have h := hmax t0 hxt
      rwa [hmin0] at h
    · exact le_min (by rw [circ_eq]; exact abs_nonneg _)
        (by rw [circ_eq]; exact abs_nonneg _)
  -- `circ (v·t₀) = 0` unfolds to `6w ∣ v`
  have key : ∀ v : ℕ, 0 < v → circ ((v : ℝ) * t0) = 0 → (6 * w) ∣ v := by
    intro v hv hc
    have e : (v : ℝ) * t0 = -((v : ℝ) / (6 * (w : ℝ))) := by
      rw [ht0]; field_simp
    rw [e, circ_neg] at hc
    rw [circ_eq_zero_iff, Int.fract_eq_zero_iff] at hc
    obtain ⟨n, hn⟩ := hc
    have hEq : (v : ℝ) = (n : ℝ) * (6 * (w : ℝ)) := by
      rw [eq_div_iff hw6.ne'] at hn
      linarith [hn]
    have hn0 : 0 ≤ n := by
      rcases lt_or_ge n 0 with h | h
      · exfalso
        have hneg : (n : ℝ) * (6 * (w : ℝ)) < 0 :=
          mul_neg_of_neg_of_pos (by exact_mod_cast h) hw6
        rw [← hEq] at hneg
        exact absurd hneg (not_lt.mpr (by exact_mod_cast hv.le))
      · exact h
    refine ⟨n.toNat, ?_⟩
    have h1 : (v : ℤ) = n * (6 * (w : ℤ)) := by exact_mod_cast hEq
    have h2 : (v : ℤ) = (6 * (w : ℤ)) * (n.toNat : ℤ) := by
      rw [Int.toNat_of_nonneg hn0, h1]; ring
    exact_mod_cast h2
  rcases min_choice (circ ((a : ℝ) * t0)) (circ ((b : ℝ) * t0)) with hm | hm
  · exact Or.inl (key a (hpos a (by simp)) (by rwa [← hm]))
  · exact Or.inr (key b (hpos b (by simp)) (by rwa [← hm]))

/-- If `6z ≤ a`, runner `z` at `λ/(6a)` (`1 ≤ λ ≤ 5`) sits in `(0, 1/6)`. -/
theorem sixth_lt_of_dvd {a z lam : ℕ} (ha : 0 < a) (hz : 0 < z)
    (h : 6 * z ≤ a) (h1 : 1 ≤ lam) (h5 : lam ≤ 5) {tt : ℝ}
    (ht : tt = 1 / (6 * (a : ℝ))) :
    Int.fract ((z : ℝ) * ((lam : ℝ) * tt)) ∈ Set.Ioo (0 : ℝ) (1 / 6) := by
  have hapos : (0 : ℝ) < a := by exact_mod_cast ha
  have hzpos : (0 : ℝ) < z := by exact_mod_cast hz
  rw [ht]
  have hval : (z : ℝ) * ((lam : ℝ) / (6 * (a : ℝ))) =
      (lam : ℝ) * (z : ℝ) / (6 * (a : ℝ)) := by ring
  have hlt : (lam : ℝ) * (z : ℝ) / (6 * (a : ℝ)) < 1 / 6 := by
    have h1' : (lam : ℝ) * (z : ℝ) < (a : ℝ) := by
      have h1 : (lam : ℝ) * (z : ℝ) ≤ 5 * (z : ℝ) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast h5) (le_of_lt hzpos)
      have h2 : (6 : ℝ) * (z : ℝ) ≤ (a : ℝ) := by exact_mod_cast h
      linarith [h1, h2]
    rw [div_lt_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 6) hapos)]
    have hr : (1 / 6 : ℝ) * (6 * (a : ℝ)) = a := by ring
    linarith [h1', hr]
  have hpos : 0 < (lam : ℝ) * (z : ℝ) / (6 * (a : ℝ)) :=
    div_pos (mul_pos (by exact_mod_cast (by omega : 0 < lam)) hzpos)
      (mul_pos (by norm_num : (0 : ℝ) < 6) hapos)
  rw [mul_one_div, hval, Int.fract_eq_self.mpr ⟨le_of_lt hpos, by linarith [hlt]⟩]
  exact ⟨hpos, hlt⟩

/-- The endgame (renault.txt L92–93): a multiple `m` of 3 is hit twice by
`6u ∣ m`, `6u' ∣ m`, and the leftover non-multiple `z` hits `m` or `n`.
Lemma 2.2 yields `m < 5n` and `n < 5m`.  At `t̄ = 1/(6m)`, runner `m` sits at
`1/6` while `u, u'` lie in `(0, 1/36]`; runner `n` is either safe there
(Argument 1 at `t̄`) or lands in `(1/30, 1/6)`, in which case `s = 5t̄` makes
`m, n` safe and `u, u'` unsafe (Argument 1 at `s`). -/
theorem endgame {D : Finset ℕ} {m n u u' z : ℕ}
    (h3m : 3 ∣ m) (h3n : 3 ∣ n)
    (h3z : ¬ 3 ∣ z) (h3u : ¬ 3 ∣ u) (h3u' : ¬ 3 ∣ u')
    (hset : ({m, n, u, u', z} : Finset ℕ) = D)
    (hpos : ∀ d ∈ D, 0 < d) (hf : hfail D)
    (hu : 6 * u ∣ m) (hu' : 6 * u' ∣ m)
    (hz : 6 * z ∣ m ∨ 6 * z ∣ n) : False := by
  have hf5 : hfail {m, n, u, u', z} := by rw [hset]; exact hf
  have hpos5 : ∀ d ∈ ({m, n, u, u', z} : Finset ℕ), 0 < d := by
    rw [hset]; exact hpos
  have hcard : D.card ≤ 5 := by
    rw [← hset]
    have h1 := Finset.card_insert_le m ({n, u, u', z} : Finset ℕ)
    have h2 := Finset.card_insert_le n ({u, u', z} : Finset ℕ)
    have h3 := Finset.card_insert_le u ({u', z} : Finset ℕ)
    have h4 := Finset.card_insert_le u' ({z} : Finset ℕ)
    rw [Finset.card_singleton] at h4
    omega
  have hm_pos : 0 < m := hpos5 m (Finset.mem_insert_self _ _)
  have hn_pos : 0 < n := hpos5 n (by simp)
  have hu_pos : 0 < u := hpos5 u (by simp)
  have hu'_pos : 0 < u' := hpos5 u' (by simp)
  have hz_pos : 0 < z := hpos5 z (by simp)
  have hmu : 6 * u ≤ m := Nat.le_of_dvd hm_pos hu
  have hmu' : 6 * u' ≤ m := Nat.le_of_dvd hm_pos hu'
  have hmz : 6 * z ≤ m ∨ 6 * z ≤ n :=
    hz.imp (Nat.le_of_dvd hm_pos) (Nat.le_of_dvd hn_pos)
  -- Lemma 2.2: `m < 5n` and `n < 5m`.
  have hmn : m < 5 * n := by
    obtain ⟨j, hjD, hjne, hjlt⟩ := lemma2_2 hpos hcard hf (i := m)
      (by rw [← hset]; exact Finset.mem_insert_self m _)
    rw [← hset] at hjD
    simp only [Finset.mem_insert, Finset.mem_singleton] at hjD
    rcases hjD with rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl hjne
    · exact hjlt
    · exfalso; omega
    · exfalso; omega
    · rcases hmz with h | h
      · exfalso; omega
      · omega
  have hnm : n < 5 * m := by
    obtain ⟨j, hjD, hjne, hjlt⟩ := lemma2_2 hpos hcard hf (i := n)
      (by rw [← hset]; exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert_self n _)))
    rw [← hset] at hjD
    simp only [Finset.mem_insert, Finset.mem_singleton] at hjD
    rcases hjD with rfl | rfl | rfl | rfl | rfl
    · exact hjlt
    · exact absurd rfl hjne
    · omega
    · omega
    · rcases hmz with h | h
      · omega
      · exfalso; omega
  -- the anchor time `t̄ = 1/(6m)`
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm_pos
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn_pos
  have huR : (0 : ℝ) < u := by exact_mod_cast hu_pos
  have hu'R : (0 : ℝ) < u' := by exact_mod_cast hu'_pos
  set tb : ℝ := 1 / (6 * (m : ℝ)) with htb
  have hanch : ∀ lam : ℕ, 1 ≤ lam → lam ≤ 5 → safe6 m ((lam : ℝ) * tb) := by
    intro lam h1 h5
    have e : (m : ℝ) * ((lam : ℝ) * tb) = (lam : ℝ) / 6 := by
      rw [htb]; field_simp
    rw [safe6, e]
    exact alpha_Icc h1 h5
  have hubad : ∀ lam : ℕ, 1 ≤ lam → lam ≤ 5 → ¬ safe6 u ((lam : ℝ) * tb) := by
    intro lam h1 h5 hs
    have hI := sixth_lt_of_dvd hm_pos hu_pos hmu h1 h5 htb
    rw [safe6, Set.mem_Icc] at hs
    linarith [hI.2, hs.1]
  have hubad' : ∀ lam : ℕ, 1 ≤ lam → lam ≤ 5 → ¬ safe6 u' ((lam : ℝ) * tb) := by
    intro lam h1 h5 hs
    have hI := sixth_lt_of_dvd hm_pos hu'_pos hmu' h1 h5 htb
    rw [safe6, Set.mem_Icc] at hs
    linarith [hI.2, hs.1]
  -- `xₙ(t̄) = n/(6m) ∈ (1/30, 5/6)`
  have hntb : (n : ℝ) * tb = (n : ℝ) / (6 * (m : ℝ)) := by
    rw [htb, mul_one_div]
  have hn30 : (1 : ℝ) / 30 < (n : ℝ) / (6 * (m : ℝ)) := by
    rw [lt_div_iff₀ (by positivity : (0 : ℝ) < 6 * m)]
    have h : (m : ℝ) < 5 * n := by exact_mod_cast hmn
    linarith
  have hn56 : (n : ℝ) / (6 * (m : ℝ)) < 5 / 6 := by
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 6 * m)]
    have h : (n : ℝ) < 5 * m := by exact_mod_cast hnm
    linarith
  have hnpos : (0 : ℝ) < (n : ℝ) / (6 * (m : ℝ)) := div_pos hnR (by positivity)
  by_cases hsn : safe6 n tb
  · -- runner `n` safe at `t̄`: Argument 1 applies directly
    exact arg1 h3m h3n h3u h3u' h3z
      (by simpa using hanch 1 le_rfl (by norm_num)) hsn
      (by simpa using hubad 1 le_rfl (by norm_num))
      (by simpa using hubad' 1 le_rfl (by norm_num)) hf5
  · -- `xₙ(t̄) ∈ (1/30, 1/6)`; at `s = 5t̄` runners `m, n` are safe, `u, u'` not
    have hn16 : (n : ℝ) / (6 * (m : ℝ)) < 1 / 6 := by
      have hfr : Int.fract ((n : ℝ) * tb) = (n : ℝ) / (6 * (m : ℝ)) := by
        rw [hntb]
        exact Int.fract_eq_self.mpr ⟨hnpos.le, by linarith⟩
      rw [safe6, hfr] at hsn
      rcases lt_or_ge ((n : ℝ) / (6 * (m : ℝ))) (1 / 6) with h | h
      · exact h
      · exact absurd (Set.mem_Icc.mpr ⟨h, by linarith⟩) hsn
    have hns : safe6 n ((5 : ℝ) * tb) := by
      have e : (n : ℝ) * ((5 : ℝ) * tb) = 5 * ((n : ℝ) / (6 * (m : ℝ))) := by
        rw [show (n : ℝ) * ((5 : ℝ) * tb) = 5 * ((n : ℝ) * tb) by ring, hntb]
      have hfr : Int.fract ((n : ℝ) * ((5 : ℝ) * tb)) =
          5 * ((n : ℝ) / (6 * (m : ℝ))) := by
        rw [e]
        exact Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
      rw [safe6, hfr]
      exact Set.mem_Icc.mpr ⟨by linarith, by linarith⟩
    exact arg1 h3m h3n h3u h3u' h3z (hanch 5 (by norm_num) le_rfl) hns
      (hubad 5 (by norm_num) le_rfl) (hubad' 5 (by norm_num) le_rfl) hf5

/-- Five explicit distinct speeds, `v₁, v₂` the multiples of 3, gcd 1:
pigeonhole on `key_per_w` puts two of the `6vᵢ` divisibilities on the same
multiple, then `endgame` finishes. -/
theorem prop31_five {v₁ v₂ v₃ v₄ v₅ : ℕ}
    (h3₁ : 3 ∣ v₁) (h3₂ : 3 ∣ v₂)
    (h3₃ : ¬ 3 ∣ v₃) (h3₄ : ¬ 3 ∣ v₄) (h3₅ : ¬ 3 ∣ v₅)
    (hpos : ∀ d ∈ ({v₁, v₂, v₃, v₄, v₅} : Finset ℕ), 0 < d)
    (hdist : v₁ ≠ v₂ ∧ v₁ ≠ v₃ ∧ v₁ ≠ v₄ ∧ v₁ ≠ v₅ ∧ v₂ ≠ v₃ ∧ v₂ ≠ v₄ ∧
      v₂ ≠ v₅ ∧ v₃ ≠ v₄ ∧ v₃ ≠ v₅ ∧ v₄ ≠ v₅)
    (hgcd : ({v₁, v₂, v₃, v₄, v₅} : Finset ℕ).gcd id = 1)
    (hf : hfail {v₁, v₂, v₃, v₄, v₅}) : False := by
  obtain ⟨n12, n13, n14, n15, n23, n24, n25, n34, n35, n45⟩ := hdist
  -- Lemma 2.1 at `l = 6`: `6 ∣ v₁` or `6 ∣ v₂`
  have h6dvd : 6 ∣ v₁ ∨ 6 ∣ v₂ := by
    obtain ⟨d, hdD, hd6⟩ := hfail_exists_dvd hf (l := 6) (by norm_num)
      (by norm_num)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hdD
    rcases hdD with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl hd6
    · exact Or.inr hd6
    · exact absurd (dvd_trans (by norm_num : (3 : ℕ) ∣ 6) hd6) h3₃
    · exact absurd (dvd_trans (by norm_num : (3 : ℕ) ∣ 6) hd6) h3₄
    · exact absurd (dvd_trans (by norm_num : (3 : ℕ) ∣ 6) hd6) h3₅
  have key3 := six_mul_dvd (a := v₁) (b := v₂) (w := v₃) (u := v₄) (u' := v₅)
    h3₁ h3₂ h3₃ h3₄ h3₅ hpos
    ⟨n12, n13, n23, n14, n24, n34, n15, n25, n35⟩ hgcd hf h6dvd
  have hperm4 : ({v₁, v₂, v₄, v₃, v₅} : Finset ℕ) = {v₁, v₂, v₃, v₄, v₅} := by
    ext x; simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor <;> rintro (rfl | rfl | rfl | rfl | rfl) <;> simp
  have hperm5 : ({v₁, v₂, v₅, v₃, v₄} : Finset ℕ) = {v₁, v₂, v₃, v₄, v₅} := by
    ext x; simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor <;> rintro (rfl | rfl | rfl | rfl | rfl) <;> simp
  have key4 := six_mul_dvd (a := v₁) (b := v₂) (w := v₄) (u := v₃) (u' := v₅)
    h3₁ h3₂ h3₄ h3₃ h3₅
    (by rw [hperm4]; exact hpos)
    ⟨n12, n14, n24, n13, n23, n34.symm, n15, n25, n45⟩
    (by rw [hperm4]; exact hgcd) (by rw [hperm4]; exact hf) h6dvd
  have key5 := six_mul_dvd (a := v₁) (b := v₂) (w := v₅) (u := v₃) (u' := v₄)
    h3₁ h3₂ h3₅ h3₃ h3₄
    (by rw [hperm5]; exact hpos)
    ⟨n12, n15, n25, n13, n23, n35.symm, n14, n24, n45.symm⟩
    (by rw [hperm5]; exact hgcd) (by rw [hperm5]; exact hf) h6dvd
  rcases key3 with h3L | h3R <;> rcases key4 with h4L | h4R <;>
    rcases key5 with h5L | h5R
  · exact endgame h3₁ h3₂ h3₅ h3₃ h3₄ rfl hpos hf h3L h4L (Or.inl h5L)
  · exact endgame h3₁ h3₂ h3₅ h3₃ h3₄ rfl hpos hf h3L h4L (Or.inr h5R)
  · exact endgame h3₁ h3₂ h3₄ h3₃ h3₅
      (show ({v₁, v₂, v₃, v₅, v₄} : Finset ℕ) = {v₁, v₂, v₃, v₄, v₅} by
        ext x; simp only [Finset.mem_insert, Finset.mem_singleton]
        constructor <;> rintro (rfl | rfl | rfl | rfl | rfl) <;> simp)
      hpos hf h3L h5L (Or.inr h4R)
  · exact endgame h3₂ h3₁ h3₃ h3₄ h3₅
      (show ({v₂, v₁, v₄, v₅, v₃} : Finset ℕ) = {v₁, v₂, v₃, v₄, v₅} by
        ext x; simp only [Finset.mem_insert, Finset.mem_singleton]
        constructor <;> rintro (rfl | rfl | rfl | rfl | rfl) <;> simp)
      hpos hf h4R h5R (Or.inr h3L)
  · exact endgame h3₁ h3₂ h3₃ h3₄ h3₅
      (show ({v₁, v₂, v₄, v₅, v₃} : Finset ℕ) = {v₁, v₂, v₃, v₄, v₅} by
        ext x; simp only [Finset.mem_insert, Finset.mem_singleton]
        constructor <;> rintro (rfl | rfl | rfl | rfl | rfl) <;> simp)
      hpos hf h4L h5L (Or.inr h3R)
  · exact endgame h3₂ h3₁ h3₄ h3₃ h3₅
      (show ({v₂, v₁, v₃, v₅, v₄} : Finset ℕ) = {v₁, v₂, v₃, v₄, v₅} by
        ext x; simp only [Finset.mem_insert, Finset.mem_singleton]
        constructor <;> rintro (rfl | rfl | rfl | rfl | rfl) <;> simp)
      hpos hf h3R h5R (Or.inr h4L)
  · exact endgame h3₂ h3₁ h3₅ h3₃ h3₄
      (show ({v₂, v₁, v₃, v₄, v₅} : Finset ℕ) = {v₁, v₂, v₃, v₄, v₅} by
        ext x; simp only [Finset.mem_insert, Finset.mem_singleton]
        constructor <;> rintro (rfl | rfl | rfl | rfl | rfl) <;> simp)
      hpos hf h3R h4R (Or.inr h5L)
  · exact endgame h3₂ h3₁ h3₅ h3₃ h3₄
      (show ({v₂, v₁, v₃, v₄, v₅} : Finset ℕ) = {v₁, v₂, v₃, v₄, v₅} by
        ext x; simp only [Finset.mem_insert, Finset.mem_singleton]
        constructor <;> rintro (rfl | rfl | rfl | rfl | rfl) <;> simp)
      hpos hf h3R h4R (Or.inl h5R)

/-- **Renault's Proposition 3.1**: five positive speeds with exactly two
multiples of 3 cannot form a failing set.  Extract the elements, divide out
the gcd (positivity, distinctness, 3-divisibility and `hfail` all transport),
then apply `prop31_five`. -/
theorem prop3_1 {D : Finset ℕ} (hpos : ∀ d ∈ D, 0 < d) (hcard : D.card = 5)
    (h3two : (D.filter (fun d => 3 ∣ d)).card = 2) (hf : hfail D) : False := by
  classical
  set T := D.filter (fun d => 3 ∣ d) with hT
  -- extract the two multiples of 3
  obtain ⟨v₁, T₁, hv₁T₁, hins1, hc1⟩ := Finset.card_eq_succ.mp h3two
  obtain ⟨v₂, hT₁eq⟩ := Finset.card_eq_one.mp hc1
  have hTv : T = {v₁, v₂} := by rw [← hins1, hT₁eq]
  have h12 : v₁ ≠ v₂ := by
    rw [hT₁eq] at hv₁T₁
    exact fun h => hv₁T₁ (Finset.mem_singleton.mpr h)
  have hTD : T ⊆ D := Finset.filter_subset _ _
  have hv₁T : v₁ ∈ T := hTv.symm ▸ Finset.mem_insert_self _ _
  have hv₂T : v₂ ∈ T := hTv.symm ▸ by simp
  have hv₁D : v₁ ∈ D := hTD hv₁T
  have hv₂D : v₂ ∈ D := hTD hv₂T
  have h3v₁ : 3 ∣ v₁ := (Finset.mem_filter.mp hv₁T).2
  have h3v₂ : 3 ∣ v₂ := (Finset.mem_filter.mp hv₂T).2
  -- the three non-multiples `R = D \ T`
  set R := D \ T with hR
  have hRc : R.card = 3 := by
    have hsplit := Finset.card_sdiff_add_card_eq_card hTD
    rw [← hR] at hsplit
    omega
  obtain ⟨v₃, R₃, hv₃R₃, hins3, hc3⟩ := Finset.card_eq_succ.mp hRc
  obtain ⟨v₄, R₄, hv₄R₄, hins4, hc4⟩ := Finset.card_eq_succ.mp hc3
  obtain ⟨v₅, hR₄eq⟩ := Finset.card_eq_one.mp hc4
  have hRv : R = {v₃, v₄, v₅} := by rw [← hins3, ← hins4, hR₄eq]
  have hv₃R : v₃ ∈ R := by rw [hRv]; simp
  have hv₄R : v₄ ∈ R := by rw [hRv]; simp
  have hv₅R : v₅ ∈ R := by rw [hRv]; simp
  have hv₃D : v₃ ∈ D := (Finset.mem_sdiff.mp hv₃R).1
  have hv₄D : v₄ ∈ D := (Finset.mem_sdiff.mp hv₄R).1
  have hv₅D : v₅ ∈ D := (Finset.mem_sdiff.mp hv₅R).1
  have hv₃nT : v₃ ∉ T := (Finset.mem_sdiff.mp hv₃R).2
  have hv₄nT : v₄ ∉ T := (Finset.mem_sdiff.mp hv₄R).2
  have hv₅nT : v₅ ∉ T := (Finset.mem_sdiff.mp hv₅R).2
  have h3v₃ : ¬ 3 ∣ v₃ := fun h => hv₃nT (Finset.mem_filter.mpr ⟨hv₃D, h⟩)
  have h3v₄ : ¬ 3 ∣ v₄ := fun h => hv₄nT (Finset.mem_filter.mpr ⟨hv₄D, h⟩)
  have h3v₅ : ¬ 3 ∣ v₅ := fun h => hv₅nT (Finset.mem_filter.mpr ⟨hv₅D, h⟩)
  -- distinctness
  have hv₄R₃ : v₄ ∈ R₃ := by
    rw [← hins4]; exact Finset.mem_insert_self _ _
  have hv₅R₃ : v₅ ∈ R₃ := by rw [← hins4, hR₄eq]; simp
  have h34 : v₃ ≠ v₄ := fun h => hv₃R₃ (h ▸ hv₄R₃)
  have h35 : v₃ ≠ v₅ := fun h => hv₃R₃ (h ▸ hv₅R₃)
  have h45 : v₄ ≠ v₅ := by
    have h4 : v₄ ∉ ({v₅} : Finset ℕ) := hR₄eq ▸ hv₄R₄
    exact fun h => h4 (Finset.mem_singleton.mpr h)
  have h13 : v₁ ≠ v₃ := fun h => hv₃nT (h ▸ hv₁T)
  have h14 : v₁ ≠ v₄ := fun h => hv₄nT (h ▸ hv₁T)
  have h15 : v₁ ≠ v₅ := fun h => hv₅nT (h ▸ hv₁T)
  have h23 : v₂ ≠ v₃ := fun h => hv₃nT (h ▸ hv₂T)
  have h24 : v₂ ≠ v₄ := fun h => hv₄nT (h ▸ hv₂T)
  have h25 : v₂ ≠ v₅ := fun h => hv₅nT (h ▸ hv₂T)
  have hD : D = {v₁, v₂, v₃, v₄, v₅} := by
    have hunion : R ∪ T = D := Finset.sdiff_union_of_subset hTD
    rw [← hunion, hRv, hTv]
    ext x
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    tauto
  -- gcd reduction: `g ∤ 3` else every speed would be a multiple of 3
  set g := D.gcd id with hg
  have hgpos : 0 < g :=
    Nat.pos_of_dvd_of_pos (Finset.gcd_dvd (f := id) hv₁D) (hpos v₁ hv₁D)
  have h3g : ¬ 3 ∣ g := by
    intro h3gd
    have hall : ∀ d ∈ D, 3 ∣ d := fun d hd =>
      dvd_trans h3gd (Finset.gcd_dvd (f := id) hd)
    have hTD' : T = D := by
      ext d
      simp only [hT, Finset.mem_filter]
      exact ⟨fun h => h.1, fun hd => ⟨hd, hall d hd⟩⟩
    rw [hTD', hcard] at h3two
    norm_num at h3two
  have hcop : Nat.Coprime 3 g :=
    (Nat.prime_three.coprime_iff_not_dvd).mpr h3g
  -- `3 ∣ d/g ↔ 3 ∣ d`
  have hq3 : ∀ d ∈ D, (3 ∣ d / g ↔ 3 ∣ d) := by
    intro d hd
    have hgd : g ∣ d := Finset.gcd_dvd (f := id) hd
    constructor
    · intro h
      have h2 : 3 ∣ g * (d / g) := dvd_mul_of_dvd_right h g
      rwa [Nat.mul_div_cancel' hgd] at h2
    · intro h
      have : 3 ∣ g * (d / g) := by rwa [Nat.mul_div_cancel' hgd]
      exact hcop.dvd_of_dvd_mul_left this
  -- quotient data
  have hdiv : ∀ v ∈ D, 0 < v / g := fun v hv =>
    Nat.div_pos (Nat.le_of_dvd (hpos v hv) (Finset.gcd_dvd (f := id) hv)) hgpos
  have hneq : ∀ {x y : ℕ}, x ∈ D → y ∈ D → x ≠ y → x / g ≠ y / g := by
    intro x y hx hy hxy h
    apply hxy
    have hxd : g ∣ x := Finset.gcd_dvd (f := id) hx
    have hyd : g ∣ y := Finset.gcd_dvd (f := id) hy
    have e : g * (x / g) = g * (y / g) := by rw [h]
    rwa [Nat.mul_div_cancel' hxd, Nat.mul_div_cancel' hyd] at e
  have hgcd_q : ({v₁ / g, v₂ / g, v₃ / g, v₄ / g, v₅ / g} : Finset ℕ).gcd id
      = 1 := by
    set g' := ({v₁ / g, v₂ / g, v₃ / g, v₄ / g, v₅ / g} : Finset ℕ).gcd id
      with hg'
    have hdvd : ∀ d ∈ D, g * g' ∣ d := by
      intro d hd
      have hgd : g ∣ d := Finset.gcd_dvd (f := id) hd
      rw [hD] at hd
      simp only [Finset.mem_insert, Finset.mem_singleton] at hd
      rcases hd with rfl | rfl | rfl | rfl | rfl <;>
        rw [← Nat.mul_div_cancel' hgd] <;>
        exact mul_dvd_mul_left g (Finset.gcd_dvd (f := id) (by simp))
    have hgg : g * g' ∣ g := by
      have h := Finset.dvd_gcd (f := id) (s := D) hdvd
      rwa [← hg] at h
    have hge : g ∣ g * g' := dvd_mul_right g g'
    have heq : g * g' = g := Nat.dvd_antisymm hgg hge
    have h1 : g * g' = g * 1 := by rwa [mul_one]
    exact mul_left_cancel₀ hgpos.ne' h1
  have hf_q : hfail {v₁ / g, v₂ / g, v₃ / g, v₄ / g, v₅ / g} := by
    have hf' : hfail (D.image (· / g)) :=
      hfail_div hgpos (fun d hd => Finset.gcd_dvd (f := id) hd) hf
    have himg : D.image (· / g) = {v₁ / g, v₂ / g, v₃ / g, v₄ / g, v₅ / g} := by
      rw [hD]; simp [Finset.image_insert]
    exact himg ▸ hf'
  have hpos_q : ∀ d ∈ ({v₁ / g, v₂ / g, v₃ / g, v₄ / g, v₅ / g} : Finset ℕ),
      0 < d := by
    intro d hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl <;>
      exact hdiv _ (by rw [hD]; simp)
  exact prop31_five
    ((hq3 v₁ hv₁D).mpr h3v₁) ((hq3 v₂ hv₂D).mpr h3v₂)
    (fun h => h3v₃ ((hq3 v₃ hv₃D).mp h))
    (fun h => h3v₄ ((hq3 v₄ hv₄D).mp h))
    (fun h => h3v₅ ((hq3 v₅ hv₅D).mp h))
    hpos_q
    ⟨hneq hv₁D hv₂D h12, hneq hv₁D hv₃D h13, hneq hv₁D hv₄D h14,
      hneq hv₁D hv₅D h15, hneq hv₂D hv₃D h23, hneq hv₂D hv₄D h24,
      hneq hv₂D hv₅D h25, hneq hv₃D hv₄D h34, hneq hv₃D hv₅D h35,
      hneq hv₄D hv₅D h45⟩
    hgcd_q hf_q

end

