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
# Renault Proposition 4.1 (three even speeds)

Setup: `v₁` is the multiple of 6, `v₂ v₃` have residue `e = ±2` (the other even
speeds) and `v₄ v₅` have residue `e = ±1` (odd speeds).  Under `hfail` we derive
a contradiction along Renault's four steps:

* `arg_zero_pm2` / `arg_zero_pm1` — the two `l/6`-shift paragraphs of §4:
  if an odd runner `z` sits at `0` while the anchor is safe and one more runner
  is in the closed unsafe arc, some `l/6`-shift makes everybody safe.
* `combine_zero` — at every `t` with `x_z(t) = 0` and the anchor safe, the two
  `±2` runners are strictly inside `(1/6,5/6)` and the other odd runner lies in
  `(1/3,2/3)` (otherwise `t + 1/2` is a safe time).
* `six_mul_dvd` — the divisibility step `6·z ∣ v₁` for each odd runner `z`.
* finish — at `λ·tt = λ/(6v₁)` runners `z y` are unsafe while the anchor is
  safe, so `arg3` forces `x_{v₂}, x_{v₃}` into `(1/6,5/6)` for every
  `λ ∈ {1,…,5}` — impossible by `claim2_4`.
-/

noncomputable section

/-- `fract (n·fract x) = fract (n·x)` for `n : ℤ` — the integer version of
`fract_nat_mul`, needed for negative multipliers `λ` in the divisibility step. -/
theorem fract_int_mul (n : ℤ) (x : ℝ) :
    Int.fract ((n : ℝ) * Int.fract x) = Int.fract ((n : ℝ) * x) := by
  have h2 : (n : ℝ) * x = (n : ℝ) * Int.fract x + ((n * ⌊x⌋ : ℤ) : ℝ) := by
    have h3 := Int.self_sub_fract x
    push_cast
    linear_combination (n : ℝ) * h3
  rw [h2, Int.fract_add_intCast]

/-- `fract (u + s) = fract (u + fract s)`. -/
theorem fract_add_eq_fract_add_fract (u s : ℝ) :
    Int.fract (u + s) = Int.fract (u + Int.fract s) := by
  have h : u + s = (u + Int.fract s) + (⌊s⌋ : ℝ) := by
    have h2 := Int.self_sub_fract s
    linarith
  rw [h, Int.fract_add_intCast]

/-- A point of `[0,1)` outside the open safe band `(1/6,5/6)` lies in the closed
unsafe arc `[0,1/6] ∪ [5/6,1)`. -/
theorem closed_unsafe_arc {u : ℝ} (_hu0 : 0 ≤ u) (_hu1 : u < 1)
    (hu : u ∉ Set.Ioo (1 / 6) (5 / 6)) :
    u ≤ 1 / 6 ∨ 5 / 6 ≤ u := by
  rw [Set.mem_Ioo, not_and_or] at hu
  rcases hu with h | h
  · exact Or.inl (not_lt.mp h)
  · exact Or.inr (not_lt.mp h)

/-- A point outside the closed safe band `[1/6,5/6]` lies in the open
unsafe arc `(-∞,1/6) ∪ (5/6,∞)`. -/
theorem open_unsafe_arc {u : ℝ} (hu : u ∉ Set.Icc (1 / 6) (5 / 6)) :
    u < 1 / 6 ∨ 5 / 6 < u := by
  rw [Set.mem_Icc, not_and_or] at hu
  rcases hu with h | h
  · exact Or.inl (not_le.mp h)
  · exact Or.inr (not_le.mp h)

/-- Shifting a closed-arc position by `s` with `fract s ∈ {1/3,1/2,2/3}` lands
inside the closed safe band.  This is the workhorse behind both `l/6`-shift
paragraphs: an `e = ±2` runner moves by `±l/3`, an `e = ±1` runner by `±l/6`. -/
theorem unsafe_add_shift_Icc {u s : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
    (hu : u ∉ Set.Ioo (1 / 6) (5 / 6))
    (hs : Int.fract s = 1 / 3 ∨ Int.fract s = 1 / 2 ∨ Int.fract s = 2 / 3) :
    Int.fract (u + s) ∈ Set.Icc (1 / 6) (5 / 6) := by
  rw [fract_add_eq_fract_add_fract]
  have wrap : ∀ c : ℝ, 1 / 3 ≤ c → c ≤ 2 / 3 → 5 / 6 ≤ u →
      Int.fract (u + c) = u + c - 1 := by
    intro c hc1 hc2 hhi
    rw [Int.fract_eq_iff]
    refine ⟨by linarith, by linarith, 1, by ring⟩
  rcases closed_unsafe_arc hu0 hu1 hu with hlo | hhi <;>
    rcases hs with hs | hs | hs <;> rw [hs]
  · rw [Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩]
    exact Set.mem_Icc.mpr ⟨by linarith, by linarith⟩
  · rw [Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩]
    exact Set.mem_Icc.mpr ⟨by linarith, by linarith⟩
  · rw [Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩]
    exact Set.mem_Icc.mpr ⟨by linarith, by linarith⟩
  · rw [wrap _ (by norm_num) (by norm_num) hhi]
    exact Set.mem_Icc.mpr ⟨by linarith, by linarith⟩
  · rw [wrap _ (by norm_num) (by norm_num) hhi]
    exact Set.mem_Icc.mpr ⟨by linarith, by linarith⟩
  · rw [wrap _ (by norm_num) (by norm_num) hhi]
    exact Set.mem_Icc.mpr ⟨by linarith, by linarith⟩

/-- Shifting a strictly unsafe position (`∉ [1/6,5/6]`) by `s` with
`fract s ∈ {1/3,1/2,2/3}` lands strictly inside `(1/6,5/6)` — the pairwise
exclusion behind every "bad set has at most one element, or two at distance 3"
count in the paper. -/
theorem unsafe_add_shift_Ioo {u s : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
    (hu : u ∉ Set.Icc (1 / 6) (5 / 6))
    (hs : Int.fract s = 1 / 3 ∨ Int.fract s = 1 / 2 ∨ Int.fract s = 2 / 3) :
    Int.fract (u + s) ∈ Set.Ioo (1 / 6) (5 / 6) := by
  rw [fract_add_eq_fract_add_fract]
  have wrap : ∀ c : ℝ, 1 / 3 ≤ c → c ≤ 2 / 3 → 5 / 6 < u →
      Int.fract (u + c) = u + c - 1 := by
    intro c hc1 hc2 hhi
    rw [Int.fract_eq_iff]
    refine ⟨by linarith, by linarith, 1, by ring⟩
  rcases open_unsafe_arc hu with hlo | hhi <;>
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

/-- `fract (e·l/6)` reduces to the `ℤ`-residue `(e·l mod 6)/6`. -/
theorem fract_mul_div_six_int (e l : ℤ) :
    Int.fract ((e : ℝ) * (l : ℝ) / 6) = (((e * l) % 6 : ℤ) : ℝ) / 6 := by
  have h : (e : ℝ) * (l : ℝ) / 6 = (((e * l : ℤ)) : ℝ) / 6 := by push_cast; ring
  rw [h, fract_intCast_div_six]

/-- Pairwise exclusion for `l/6`-shifts: if `fract (e·(b-a)/6)` is a nonzero
third or a half, runner `d ≡ e (mod 6)` cannot be strictly unsafe at both
`t + a/6` and `t + b/6`.  Positions at the two times differ by `e·(b-a)/6`. -/
theorem unsafe_pair_sixth {d : ℕ} {e : ℤ} (hde : (d : ℤ) ≡ e [ZMOD 6])
    (t : ℝ) (a b : ℤ)
    (hs : Int.fract ((e : ℝ) * ((b : ℝ) - (a : ℝ)) / 6) = 1 / 3 ∨
          Int.fract ((e : ℝ) * ((b : ℝ) - (a : ℝ)) / 6) = 1 / 2 ∨
          Int.fract ((e : ℝ) * ((b : ℝ) - (a : ℝ)) / 6) = 2 / 3) :
    safe6 d (t + (a : ℝ) / 6) ∨ safe6 d (t + (b : ℝ) / 6) := by
  by_contra hboth
  push Not at hboth
  obtain ⟨ha, hb⟩ := hboth
  -- position at `b` equals position at `a` shifted by `e·(b-a)/6`
  obtain ⟨k, hk⟩ := Int.modEq_iff_dvd.mp hde
  have hpos : Int.fract ((d : ℝ) * (t + (b : ℝ) / 6)) =
      Int.fract (Int.fract ((d : ℝ) * (t + (a : ℝ) / 6)) +
        (e : ℝ) * ((b : ℝ) - (a : ℝ)) / 6) := by
    have hsplit : (d : ℝ) * (t + (b : ℝ) / 6) =
        (Int.fract ((d : ℝ) * (t + (a : ℝ) / 6)) +
          (e : ℝ) * ((b : ℝ) - (a : ℝ)) / 6) +
          ((⌊(d : ℝ) * (t + (a : ℝ) / 6)⌋ - k * (b - a) : ℤ) : ℝ) := by
      have hd : (d : ℝ) = (e : ℝ) - 6 * (k : ℝ) := by
        have h2 : (d : ℤ) = e - 6 * k := by linarith [hk]
        calc (d : ℝ) = ((d : ℤ) : ℝ) := by simp
          _ = ((e - 6 * k : ℤ) : ℝ) := by rw [h2]
          _ = (e : ℝ) - 6 * (k : ℝ) := by push_cast; ring
      have hfloor := Int.self_sub_fract ((d : ℝ) * (t + (a : ℝ) / 6))
      push_cast
      linear_combination hfloor + (((b : ℝ) - (a : ℝ)) / 6) * hd
    rw [hsplit, Int.fract_add_intCast]
  rw [safe6] at ha hb
  have hsafe := unsafe_add_shift_Ioo
    (Int.fract_nonneg _) (Int.fract_lt_one _) ha hs
  rw [← hpos] at hsafe
  exact hb (Set.Ioo_subset_Icc_self hsafe)

/-- For `e = ±2` the shift over `Δl = 3` is an integer (`e·3/6 = ±1`), so the
position at `t + (l+3)/6` equals the position at `t + l/6`: the "distance-3
pair" of the paper. -/
theorem mirror_sixth {d : ℕ} {e : ℤ} (hde : (d : ℤ) ≡ e [ZMOD 6])
    (he : e = 2 ∨ e = -2) (t : ℝ) (l : ℤ) :
    Int.fract ((d : ℝ) * (t + ((l + 3 : ℤ) : ℝ) / 6)) =
      Int.fract ((d : ℝ) * (t + (l : ℝ) / 6)) := by
  rw [fract_signed_shift hde t (l + 3), fract_signed_shift hde t l]
  have he3 : (e : ℝ) * (((l + 3 : ℤ)) : ℝ) / 6 =
      (e : ℝ) * (l : ℝ) / 6 + (e : ℝ) / 2 := by
    push_cast; ring
  have hehalf : (e : ℝ) / 2 = ((e / 2 : ℤ) : ℝ) := by
    rcases he with rfl | rfl <;> norm_num
  rw [he3]
  rw [show Int.fract ((d : ℝ) * t) + ((e : ℝ) * (l : ℝ) / 6 + (e : ℝ) / 2)
      = (Int.fract ((d : ℝ) * t) + (e : ℝ) * (l : ℝ) / 6) + ((e / 2 : ℤ) : ℝ) by
      rw [← hehalf]; ring]
  rw [Int.fract_add_intCast]

/-- The multiple-of-6 anchor is unchanged by `l/6`-shifts. -/
theorem safe6_sixth_shift_anchor {a : ℕ} (ha : (a : ℤ) ≡ 0 [ZMOD 6])
    (t : ℝ) (l : ℤ) :
    safe6 a (t + (l : ℝ) / 6) ↔ safe6 a t := by
  have h := fract_signed_shift ha t l
  simp only [Int.cast_zero, zero_mul, zero_div, add_zero] at h
  have hff : Int.fract (Int.fract ((a : ℝ) * t)) = Int.fract ((a : ℝ) * t) :=
    Int.fract_eq_self.mpr ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
  rw [hff] at h
  simp only [safe6, h]

/-- A `±1` runner sitting at `0` is safe at every `t + l/6`, `1 ≤ l ≤ 5`:
`x(t + l/6) = ⟨0 + e·l/6⟩ ∈ [1/6,5/6]`. -/
theorem safe6_sixth_shift_zero {z : ℕ} {e : ℤ} (hde : (z : ℤ) ≡ e [ZMOD 6])
    (he : e = 1 ∨ e = -1) {t : ℝ}
    (hz0 : Int.fract ((z : ℝ) * t) = 0) {l : ℤ} (h1 : 1 ≤ l) (h5 : l ≤ 5) :
    safe6 z (t + (l : ℝ) / 6) := by
  rw [safe6, fract_signed_shift hde t l, hz0, zero_add]
  have hln : ∃ n : ℕ, (n : ℤ) = l := ⟨l.toNat, Int.toNat_of_nonneg (by omega)⟩
  obtain ⟨n, rfl⟩ := hln
  have hn1 : 1 ≤ n := by exact_mod_cast h1
  have hn5 : n ≤ 5 := by exact_mod_cast h5
  rw [show (e : ℝ) * ((n : ℤ) : ℝ) / 6 = (e : ℝ) * (n : ℝ) / 6 by push_cast; ring]
  exact signed_alpha_Icc he hn1 hn5

/-- `fract (e·Δ/6)` is a nonzero third or a half whenever `e·Δ mod 6 ∈ {2,3,4}`. -/
theorem sixth_shift_thirds {e Δ : ℤ}
    (h : (e * Δ) % 6 = 2 ∨ (e * Δ) % 6 = 3 ∨ (e * Δ) % 6 = 4) :
    Int.fract ((e : ℝ) * (Δ : ℝ) / 6) = 1 / 3 ∨
      Int.fract ((e : ℝ) * (Δ : ℝ) / 6) = 1 / 2 ∨
      Int.fract ((e : ℝ) * (Δ : ℝ) / 6) = 2 / 3 := by
  have h2 : (e : ℝ) * (Δ : ℝ) / 6 = ((e * Δ : ℤ) : ℝ) / 6 := by push_cast; ring
  rw [h2, fract_intCast_div_six]
  rcases h with h | h | h <;> rw [h] <;> norm_num

/-- `unsafe_pair_sixth` with the shift condition packaged as a `mod 6` fact. -/
theorem unsafe_pair_sixth' {d : ℕ} {e : ℤ} (hde : (d : ℤ) ≡ e [ZMOD 6])
    (t : ℝ) (a b : ℤ)
    (hΔ : (e * (b - a)) % 6 = 2 ∨ (e * (b - a)) % 6 = 3 ∨ (e * (b - a)) % 6 = 4) :
    safe6 d (t + (a : ℝ) / 6) ∨ safe6 d (t + (b : ℝ) / 6) := by
  apply unsafe_pair_sixth hde t a b
  rw [← Int.cast_sub]
  exact sixth_shift_thirds hΔ

/-- For `e = ±2`, every `l ∈ {1,2,4,5}` shift is a nonzero third. -/
theorem pm2_shift_thirds {e : ℤ} (he : e = 2 ∨ e = -2) {l : ℤ}
    (hl : l ∈ ({1, 2, 4, 5} : Finset ℤ)) :
    Int.fract ((e : ℝ) * (l : ℝ) / 6) = 1 / 3 ∨
      Int.fract ((e : ℝ) * (l : ℝ) / 6) = 1 / 2 ∨
      Int.fract ((e : ℝ) * (l : ℝ) / 6) = 2 / 3 := by
  rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert,
    Finset.mem_singleton] at hl
  rcases hl with rfl | rfl | rfl | rfl <;>
    rcases he with rfl | rfl <;>
    exact sixth_shift_thirds (by norm_num)

/-- For `e = ±1`, every `l ∈ {2,3,4}` shift is a nonzero third or a half. -/
theorem pm1_mid_shift_thirds {e : ℤ} (he : e = 1 ∨ e = -1) {l : ℤ}
    (hl : l ∈ ({2, 3, 4} : Finset ℤ)) :
    Int.fract ((e : ℝ) * (l : ℝ) / 6) = 1 / 3 ∨
      Int.fract ((e : ℝ) * (l : ℝ) / 6) = 1 / 2 ∨
      Int.fract ((e : ℝ) * (l : ℝ) / 6) = 2 / 3 := by
  rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hl
  rcases hl with rfl | rfl | rfl <;>
    rcases he with rfl | rfl <;>
    exact sixth_shift_thirds (by norm_num)

/-- Residues `e ∈ {±1, ±2}` force `3 ∤ d`. -/
theorem not_three_dvd_of_mod6 {d : ℕ} {e : ℤ} (hde : (d : ℤ) ≡ e [ZMOD 6])
    (he : e = 1 ∨ e = -1 ∨ e = 2 ∨ e = -2) : ¬ 3 ∣ d := by
  intro h3
  obtain ⟨k, hk⟩ := Int.modEq_iff_dvd.mp hde
  obtain ⟨m, hm⟩ := h3
  have hd3 : (d : ℤ) = 3 * (m : ℤ) := by exact_mod_cast hm
  have h3e : (3 : ℤ) ∣ e := ⟨m + 2 * k, by linarith⟩
  rcases he with rfl | rfl | rfl | rfl <;> norm_num at h3e

/-- Residue `e = ±2` forces `2 ∣ d`. -/
theorem two_dvd_of_pm2 {d : ℕ} {e : ℤ} (hde : (d : ℤ) ≡ e [ZMOD 6])
    (he : e = 2 ∨ e = -2) : 2 ∣ d := by
  obtain ⟨k, hk⟩ := Int.modEq_iff_dvd.mp hde
  have h2 : (2 : ℤ) ∣ (d : ℤ) := by
    rcases he with rfl | rfl
    · exact ⟨1 - 3 * k, by linarith⟩
    · exact ⟨-1 - 3 * k, by linarith⟩
  exact_mod_cast h2

/-- Residue `e = ±1` forces `2 ∤ d`. -/
theorem not_two_dvd_of_pm1 {d : ℕ} {e : ℤ} (hde : (d : ℤ) ≡ e [ZMOD 6])
    (he : e = 1 ∨ e = -1) : ¬ 2 ∣ d := by
  intro h2
  obtain ⟨k, hk⟩ := Int.modEq_iff_dvd.mp hde
  obtain ⟨m, hm⟩ := h2
  have hd2 : (d : ℤ) = 2 * (m : ℤ) := by exact_mod_cast hm
  have h2e : (2 : ℤ) ∣ e := ⟨m + 3 * k, by linarith⟩
  rcases he with rfl | rfl <;> norm_num at h2e

/-- `(d : ℤ) ≡ 0 [ZMOD 6]` gives `6 ∣ d`. -/
theorem six_dvd_of_modEq_zero {d : ℕ} (h : (d : ℤ) ≡ 0 [ZMOD 6]) : 6 ∣ d := by
  have h6 : (6 : ℤ) ∣ (d : ℤ) := Int.modEq_zero_iff_dvd.mp h
  exact_mod_cast h6

/-- A closed-arc runner shifted by a sixth in `{1/3,1/2,2/3}` lands safe. -/
theorem safe6_sixth_shift_arc {d : ℕ} {e : ℤ} (hde : (d : ℤ) ≡ e [ZMOD 6])
    (t : ℝ) (l : ℤ)
    (hpos : Int.fract ((d : ℝ) * t) ∉ Set.Ioo (1 / 6) (5 / 6))
    (hs : Int.fract ((e : ℝ) * (l : ℝ) / 6) = 1 / 3 ∨
      Int.fract ((e : ℝ) * (l : ℝ) / 6) = 1 / 2 ∨
      Int.fract ((e : ℝ) * (l : ℝ) / 6) = 2 / 3) :
    safe6 d (t + (l : ℝ) / 6) := by
  rw [safe6, fract_signed_shift hde t l]
  exact unsafe_add_shift_Icc (Int.fract_nonneg _) (Int.fract_lt_one _) hpos hs

/-- For `3 ∤ d` the `l/3`-shifts (`l ∈ {1,2}`) are nonzero thirds. -/
theorem third_shift_thirds {d : ℕ} (hd : ¬ 3 ∣ d) {l : ℕ} (hl : l = 1 ∨ l = 2) :
    Int.fract ((d : ℝ) * (l : ℝ) / 3) = 1 / 3 ∨
      Int.fract ((d : ℝ) * (l : ℝ) / 3) = 2 / 3 := by
  have hd3 : d % 3 = 1 ∨ d % 3 = 2 := by
    have hlt : d % 3 < 3 := Nat.mod_lt d (by norm_num)
    have hne : d % 3 ≠ 0 := fun h => hd (Nat.dvd_of_mod_eq_zero h)
    omega
  have hsplit : (d : ℝ) * (l : ℝ) / 3 =
      ((d % 3 : ℕ) : ℝ) * (l : ℝ) / 3 + ((d / 3 * l : ℕ) : ℝ) := by
    have h2 : (d : ℝ) = 3 * ((d / 3 : ℕ) : ℝ) + ((d % 3 : ℕ) : ℝ) := by
      exact_mod_cast (Nat.div_add_mod d 3).symm
    calc (d : ℝ) * (l : ℝ) / 3
        = (3 * ((d / 3 : ℕ) : ℝ) + ((d % 3 : ℕ) : ℝ)) * (l : ℝ) / 3 := by rw [h2]
      _ = ((d % 3 : ℕ) : ℝ) * (l : ℝ) / 3 + ((d / 3 * l : ℕ) : ℝ) := by
          push_cast; field_simp; ring
  rw [hsplit, Int.fract_add_natCast]
  rcases hd3 with hd3 | hd3 <;> rcases hl with rfl | rfl <;> rw [hd3]
  · left
    rw [show ((1 : ℕ) : ℝ) * ((1 : ℕ) : ℝ) / 3 = (1 : ℝ) / 3 by norm_num]
    exact Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩
  · right
    rw [show ((1 : ℕ) : ℝ) * ((2 : ℕ) : ℝ) / 3 = (2 : ℝ) / 3 by norm_num]
    exact Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩
  · right
    rw [show ((2 : ℕ) : ℝ) * ((1 : ℕ) : ℝ) / 3 = (2 : ℝ) / 3 by norm_num]
    exact Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩
  · left
    rw [show ((2 : ℕ) : ℝ) * ((2 : ℕ) : ℝ) / 3 = (1 : ℝ) / 3 + (1 : ℤ) by norm_num]
    rw [Int.fract_add_intCast]
    exact Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩

/-- A closed-arc runner is safe at `t + 1/3` and `t + 2/3` (Renault's Argument 3
mechanism: the closed unsafe arc `1/3`-shifted always lands in the band). -/
theorem safe6_third_shift_arc {d : ℕ} (hd : ¬ 3 ∣ d) (t : ℝ) {l : ℕ}
    (hpos : Int.fract ((d : ℝ) * t) ∉ Set.Ioo (1 / 6) (5 / 6))
    (hl : l = 1 ∨ l = 2) :
    safe6 d (t + (l : ℝ) / 3) := by
  rw [safe6, fract_third_shift d l t]
  rcases third_shift_thirds hd hl with h | h
  · exact unsafe_add_shift_Icc (Int.fract_nonneg _) (Int.fract_lt_one _) hpos
      (Or.inl h)
  · exact unsafe_add_shift_Icc (Int.fract_nonneg _) (Int.fract_lt_one _) hpos
      (Or.inr (Or.inr h))

/-- An even runner is unchanged by a `1/2`-shift. -/
theorem fract_add_half_of_two_dvd {d : ℕ} (hd : 2 ∣ d) (t : ℝ) :
    Int.fract ((d : ℝ) * (t + 1 / 2)) = Int.fract ((d : ℝ) * t) := by
  rw [fract_add_shift]
  obtain ⟨k, hk⟩ := hd
  have hk2 : (d : ℝ) * (1 / 2) = (k : ℝ) := by rw [hk]; push_cast; ring
  rw [hk2, Int.fract_add_natCast, Int.fract_fract]

/-- An odd runner's shift by `1/2` moves any position by `1/2`. -/
theorem fract_add_half_of_odd {d : ℕ} (hd : ¬ 2 ∣ d) (x : ℝ) :
    Int.fract (x + (d : ℝ) / 2) = Int.fract (x + 1 / 2) := by
  have hd1 : d % 2 = 1 := by
    rcases Nat.mod_two_eq_zero_or_one d with h | h
    · exfalso; exact hd (Nat.dvd_of_mod_eq_zero h)
    · exact h
  have hsplit : (d : ℝ) / 2 = ((d / 2 : ℕ) : ℝ) + 1 / 2 := by
    have h2 : (d : ℝ) = 2 * ((d / 2 : ℕ) : ℝ) + 1 := by
      have h3 : d = 2 * (d / 2) + 1 := by
        have h4 := Nat.div_add_mod d 2
        omega
      exact_mod_cast h3
    linarith [h2]
  have hrw : x + (d : ℝ) / 2 = (x + 1 / 2) + ((d / 2 : ℕ) : ℝ) := by
    rw [hsplit]; ring
  rw [hrw, Int.fract_add_natCast]

/-- `u ∈ (1/6,5/6) ∖ (1/3,2/3)` shifted by `1/2` lands in the safe band — the
`t + 1/2` finisher of the `x₄ = 0` paragraph. -/
theorem fract_add_half_mem_Icc {u : ℝ} (hI : u ∈ Set.Ioo (1 / 6) (5 / 6))
    (hN : u ∉ Set.Ioo (1 / 3) (2 / 3)) :
    Int.fract (u + 1 / 2) ∈ Set.Icc (1 / 6) (5 / 6) := by
  rw [Set.mem_Ioo] at hI
  rw [Set.mem_Ioo, not_and_or] at hN
  rcases hN with hN | hN
  · have hu : u ≤ 1 / 3 := not_lt.mp hN
    rw [Int.fract_eq_self.mpr ⟨by linarith [hI.1], by linarith⟩]
    exact Set.mem_Icc.mpr ⟨by linarith, by linarith⟩
  · have hu : 2 / 3 ≤ u := not_lt.mp hN
    have hf : Int.fract (u + 1 / 2) = u - 1 / 2 := by
      rw [Int.fract_eq_iff]
      exact ⟨by linarith, by linarith [hI.2], ⟨1, by ring⟩⟩
    rw [hf]
    exact Set.mem_Icc.mpr ⟨by linarith, by linarith⟩

/-- Doubling `u ∈ (1/3,2/3)` leaves `(1/3,2/3)` — the impossibility used at the
end of the `v₄ ∣ v₁` paragraph (`x₅(4s) = ⟨2·x₅(2s)⟩`). -/
theorem fract_two_Ioo {u : ℝ} (hu : u ∈ Set.Ioo (1 / 3) (2 / 3)) :
    Int.fract (2 * u) ∉ Set.Ioo (1 / 3) (2 / 3) := by
  rw [Set.mem_Ioo] at hu
  rcases lt_trichotomy u (1 / 2 : ℝ) with h | h | h
  · have hf : Int.fract (2 * u) = 2 * u :=
      Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
    rw [Set.mem_Ioo]
    rintro ⟨h1, h2⟩
    rw [hf] at h2
    linarith
  · have hf : Int.fract (2 * u) = 0 := by
      rw [h, show (2 : ℝ) * (1 / 2) = 1 by norm_num]
      exact Int.fract_one
    rw [Set.mem_Ioo]
    rintro ⟨h1, -⟩
    rw [hf] at h1
    linarith
  · have hf : Int.fract (2 * u) = 2 * u - 1 := by
      rw [Int.fract_eq_iff]
      exact ⟨by linarith, by linarith, ⟨1, by ring⟩⟩
    rw [Set.mem_Ioo]
    rintro ⟨h1, -⟩
    rw [hf] at h1
    linarith

/-- Claim 2.4 in closed-arc form: `x ∈ [1/6,5/6]` has some `λ ∈ {2,3,4,5}` with
`⟨λx⟩` in the closed unsafe arc.  Boundary points are handled by `λ = 5`. -/
theorem claim2_4_closed {x : ℝ} (hx : x ∈ Set.Icc (1 / 6) (5 / 6)) :
    ∃ lam : ℕ, lam ∈ Finset.Icc 2 5 ∧
      Int.fract ((lam : ℝ) * x) ∉ Set.Ioo (1 / 6) (5 / 6) := by
  rw [Set.mem_Icc] at hx
  rcases eq_or_lt_of_le hx.1 with h1 | h1
  · refine ⟨5, by decide, ?_⟩
    rw [← h1]
    have hf : Int.fract (((5 : ℕ) : ℝ) * (1 / 6)) = 5 / 6 := by
      rw [show ((5 : ℕ) : ℝ) * (1 / 6) = (5 : ℝ) / 6 by push_cast; norm_num]
      exact Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩
    rw [hf]
    intro hmem
    rw [Set.mem_Ioo] at hmem
    linarith [hmem.2]
  · rcases eq_or_lt_of_le hx.2 with h2 | h2
    · refine ⟨5, by decide, ?_⟩
      rw [h2]
      have hf : Int.fract (((5 : ℕ) : ℝ) * (5 / 6)) = 1 / 6 := by
        rw [show ((5 : ℕ) : ℝ) * (5 / 6) = (1 / 6 : ℝ) + ((4 : ℤ) : ℝ) by
          push_cast; norm_num]
        rw [Int.fract_add_intCast]
        exact Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩
      rw [hf]
      intro hmem
      rw [Set.mem_Ioo] at hmem
      linarith [hmem.1]
    · obtain ⟨lam, hlam, hb⟩ := claim2_4 ⟨h1, h2⟩
      exact ⟨lam, hlam, fun h => hb (Set.Ioo_subset_Icc_self h)⟩

/-- Multiples of a small nonzero `u < 1/6` hit the band `[1/12,1/6]`: the first
`n` with `n·u ≥ 1/12` overshoots by less than `u ≤ 1/12`. -/
theorem exists_nat_mul_band {u : ℝ} (hu : u ∈ Set.Ioo (0 : ℝ) (1 / 6)) :
    ∃ n : ℕ, (n : ℝ) * u ∈ Set.Icc (1 / 12) (1 / 6) := by
  classical
  have hex : ∃ n : ℕ, (1 / 12 : ℝ) ≤ (n : ℝ) * u := by
    obtain ⟨n, hn⟩ := exists_nat_gt (1 / (12 * u))
    refine ⟨n, le_of_lt ?_⟩
    have hu0' : u ≠ 0 := ne_of_gt hu.1
    calc (1 / 12 : ℝ) = (1 / (12 * u)) * u := by field_simp
      _ < (n : ℝ) * u := mul_lt_mul_of_pos_right hn hu.1
  set n := Nat.find hex with hn
  have hspec : (1 / 12 : ℝ) ≤ (n : ℝ) * u := Nat.find_spec hex
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · exfalso
      rw [h] at hspec
      simp at hspec
      norm_num at hspec
    · exact h
  have hmin : ¬ (1 / 12 : ℝ) ≤ ((n - 1 : ℕ) : ℝ) * u := by
    intro hle
    have hle' : n ≤ n - 1 := Nat.find_min' hex hle
    omega
  have hup : (n : ℝ) * u < 1 / 6 := by
    have hlt : ((n - 1 : ℕ) : ℝ) * u < 1 / 12 := not_le.mp hmin
    rcases eq_or_lt_of_le hn1 with h1 | h2
    · have hn1' : (n : ℝ) = 1 := by exact_mod_cast h1.symm
      rw [hn1']
      linarith [hu.2]
    · have hu12 : u < 1 / 12 := by
        have hge : (u : ℝ) ≤ ((n - 1 : ℕ) : ℝ) * u := by
          have h1le : (1 : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by
            exact_mod_cast (by omega : 1 ≤ n - 1)
          calc u = 1 * u := by ring
            _ ≤ ((n - 1 : ℕ) : ℝ) * u := by
                apply mul_le_mul_of_nonneg_right h1le (le_of_lt hu.1)
        linarith [hge]
      have hsplit : (n : ℝ) * u = ((n - 1 : ℕ) : ℝ) * u + u := by
        have hn1r : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega : 1 ≤ n)]
          push_cast; ring
        rw [hn1r]; ring
      linarith [hsplit, hlt, hu12]
  exact ⟨n, Set.mem_Icc.mpr ⟨hspec, le_of_lt hup⟩⟩

/-- The band lemma: `u ∈ (0,1/6) ∪ (5/6,1)` has an integer multiple in
`[1/12,1/6]` — Renault's "there exists an integer `λ` such that
`⟨λ·x₁⟩ ∈ [1/12,1/6]`". -/
theorem exists_int_mul_Ioo_band {u : ℝ}
    (hu : u ∈ Set.Ioo (0 : ℝ) (1 / 6) ∪ Set.Ioo (5 / 6) 1) :
    ∃ lam : ℤ, Int.fract ((lam : ℝ) * u) ∈ Set.Icc (1 / 12) (1 / 6) := by
  rcases hu with hu | hu
  · obtain ⟨n, hn⟩ := exists_nat_mul_band hu
    refine ⟨(n : ℤ), ?_⟩
    have hself : Int.fract ((n : ℝ) * u) = (n : ℝ) * u :=
      Int.fract_eq_self.mpr ⟨by linarith [hn.1], by linarith [hn.2]⟩
    rw [Int.cast_natCast, hself]
    exact hn
  · have hw : 1 - u ∈ Set.Ioo (0 : ℝ) (1 / 6) := ⟨by linarith [hu.2], by linarith [hu.1]⟩
    obtain ⟨n, hn⟩ := exists_nat_mul_band hw
    refine ⟨-(n : ℤ), ?_⟩
    have heq : (↑(-(n : ℤ)) : ℝ) * u = (n : ℝ) * (1 - u) + (↑(-(n : ℤ)) : ℝ) := by
      push_cast; ring
    rw [heq, Int.fract_add_intCast]
    have hself : Int.fract ((n : ℝ) * (1 - u)) = (n : ℝ) * (1 - u) :=
      Int.fract_eq_self.mpr ⟨by linarith [hn.1], by linarith [hn.2]⟩
    rw [hself]
    exact hn

/-- Rescale a nonzero closed-arc point into the band: `u ∈ (0,1/6] ∪ [5/6,1)`
has an integer multiple in `[1/12,1/6]` (boundary points use `λ = ±1`). -/
theorem rescale_to_band {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
    (hune : u ≠ 0) (hu : u ∉ Set.Ioo (1 / 6) (5 / 6)) :
    ∃ lam : ℤ, Int.fract ((lam : ℝ) * u) ∈ Set.Icc (1 / 12) (1 / 6) := by
  rcases closed_unsafe_arc hu0 hu1 hu with hlo | hhi
  · rcases eq_or_lt_of_le hlo with heq | hlt
    · refine ⟨1, ?_⟩
      rw [heq]
      rw [Int.cast_one, one_mul]
      rw [Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩]
      exact Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩
    · have hpos : 0 < u := lt_of_le_of_ne hu0 (Ne.symm hune)
      exact exists_int_mul_Ioo_band (Or.inl ⟨hpos, hlt⟩)
  · rcases eq_or_lt_of_le hhi with heq | hlt
    · refine ⟨-1, ?_⟩
      rw [← heq]
      have hrw : (↑(-(1 : ℤ)) : ℝ) * (5 / 6) = (1 / 6 : ℝ) + (↑(-(1 : ℤ)) : ℝ) := by
        push_cast; ring
      rw [hrw, Int.fract_add_intCast]
      rw [Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩]
      exact Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩
    · exact exists_int_mul_Ioo_band (Or.inr ⟨hlt, hu1⟩)

/-- Turning `safe6`-contradictions into `False` via `hfail` on the 5-set. -/
theorem all_safe_contra {a b c z y : ℕ} {s : ℝ}
    (h1 : safe6 a s) (h2 : safe6 b s) (h3 : safe6 c s)
    (h4 : safe6 z s) (h5 : safe6 y s)
    (hf : hfail {a, b, c, z, y}) : False := by
  obtain ⟨d, hd, hdbad⟩ := hf s
  rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert, Finset.mem_insert,
    Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl
  · exact hdbad h1
  · exact hdbad h2
  · exact hdbad h3
  · exact hdbad h4
  · exact hdbad h5

/-- Renault's Argument 3: if the anchor (`3 ∣ a`) is safe at `t` and three other
runners `p q r` sit in the closed unsafe arc `[5/6,1/6]`, then some
`t + l/3` (`l ∈ {0,1,2}`) is a fully safe time — contradicting `hfail`.

The three arc-runners are automatically safe at `t + 1/3` and `t + 2/3`; the
fourth runner `s` is safe at one of those two shifts by `bad_third_le_one`. -/
theorem arg3 {a p q r s : ℕ}
    (ha : 3 ∣ a) (hp : ¬ 3 ∣ p) (hq : ¬ 3 ∣ q) (hr : ¬ 3 ∣ r) (hs : ¬ 3 ∣ s)
    {t : ℝ} (hsafe : safe6 a t)
    (hparc : Int.fract ((p : ℝ) * t) ∉ Set.Ioo (1 / 6) (5 / 6))
    (hqarc : Int.fract ((q : ℝ) * t) ∉ Set.Ioo (1 / 6) (5 / 6))
    (hrarc : Int.fract ((r : ℝ) * t) ∉ Set.Ioo (1 / 6) (5 / 6))
    (hf : hfail {a, p, q, r, s}) : False := by
  have hp1 := safe6_third_shift_arc hp t hparc (Or.inl rfl)
  have hp2 := safe6_third_shift_arc hp t hparc (Or.inr rfl)
  have hq1 := safe6_third_shift_arc hq t hqarc (Or.inl rfl)
  have hq2 := safe6_third_shift_arc hq t hqarc (Or.inr rfl)
  have hr1 := safe6_third_shift_arc hr t hrarc (Or.inl rfl)
  have hr2 := safe6_third_shift_arc hr t hrarc (Or.inr rfl)
  rcases bad_third_le_one hs t (by norm_num : (1 : ℕ) < 3)
      (by norm_num : (2 : ℕ) < 3) (by norm_num : (1 : ℕ) < 2) with hss | hss
  · exact all_safe_contra ((safe6_third_shift_of_dvd ha t 1).mpr hsafe)
      hp1 hq1 hr1 hss hf
  · exact all_safe_contra ((safe6_third_shift_of_dvd ha t 2).mpr hsafe)
      hp2 hq2 hr2 hss hf

/-- Renault §4 PARA1: if the anchor is safe at `t`, the `±2`-runner `u` is in
the closed unsafe arc and the `±1`-runner `z` sits at `0`, then some
`l ∈ {1,2,4,5}` makes `t + l/6` fully safe — contradicting `hfail`.

Runners `a u z` are safe at every `l ∈ {1,2,4,5}`; the bad set of `w` (`±2`)
avoids distance `∈ {1,2,4}` pairs, the bad set of `y` (`±1`) avoids distance
`≥ 2` pairs, and the four slots can't all be covered. -/
theorem arg_zero_pm2 {a u w z y : ℕ} {eu ew ez ey : ℤ}
    (ha : (a : ℤ) ≡ 0 [ZMOD 6])
    (hu : (u : ℤ) ≡ eu [ZMOD 6]) (heu : eu = 2 ∨ eu = -2)
    (hw : (w : ℤ) ≡ ew [ZMOD 6]) (hew : ew = 2 ∨ ew = -2)
    (hz : (z : ℤ) ≡ ez [ZMOD 6]) (hez : ez = 1 ∨ ez = -1)
    (hy : (y : ℤ) ≡ ey [ZMOD 6]) (hey : ey = 1 ∨ ey = -1)
    {t : ℝ} (hsafe : safe6 a t)
    (huarc : Int.fract ((u : ℝ) * t) ∉ Set.Ioo (1 / 6) (5 / 6))
    (hz0 : Int.fract ((z : ℝ) * t) = 0)
    (hf : hfail {a, u, w, z, y}) : False := by
  have key : ∃ l : ℤ, l ∈ ({1, 2, 4, 5} : Finset ℤ) ∧
      safe6 w (t + (l : ℝ) / 6) ∧ safe6 y (t + (l : ℝ) / 6) := by
    by_contra hcon
    have bad_of_safe : ∀ l : ℤ, l ∈ ({1, 2, 4, 5} : Finset ℤ) →
        safe6 w (t + (l : ℝ) / 6) → ¬ safe6 y (t + (l : ℝ) / 6) :=
      fun l hl hws hys => hcon ⟨l, hl, hws, hys⟩
    have pw12 := unsafe_pair_sixth' hw t 1 2
      (by rcases hew with rfl | rfl <;> norm_num)
    have pw15 := unsafe_pair_sixth' hw t 1 5
      (by rcases hew with rfl | rfl <;> norm_num)
    have pw24 := unsafe_pair_sixth' hw t 2 4
      (by rcases hew with rfl | rfl <;> norm_num)
    have pw45 := unsafe_pair_sixth' hw t 4 5
      (by rcases hew with rfl | rfl <;> norm_num)
    have py14 := unsafe_pair_sixth' hy t 1 4
      (by rcases hey with rfl | rfl <;> norm_num)
    have py25 := unsafe_pair_sixth' hy t 2 5
      (by rcases hey with rfl | rfl <;> norm_num)
    by_cases hw1 : safe6 w (t + ((1 : ℤ) : ℝ) / 6)
    · by_cases hw2 : safe6 w (t + ((2 : ℤ) : ℝ) / 6)
      · by_cases hw4 : safe6 w (t + ((4 : ℤ) : ℝ) / 6)
        · by_cases _hw5 : safe6 w (t + ((5 : ℤ) : ℝ) / 6)
          · -- `w` safe at all four slots: `y` bad at 1 and 4.
            have hy1 := bad_of_safe 1 (by decide) hw1
            have hy4 := bad_of_safe 4 (by decide) hw4
            rcases py14 with h | h
            · exact hy1 h
            · exact hy4 h
          · -- `w` bad at 5, safe at 1 and 4: `y` bad at 1 and 4.
            have hy1 := bad_of_safe 1 (by decide) hw1
            have hy4 := bad_of_safe 4 (by decide) hw4
            rcases py14 with h | h
            · exact hy1 h
            · exact hy4 h
        · -- `w` bad at 4: safe at 5 via the (4,5) pair; `y` bad at 2 and 5.
          have hw5 := pw45.resolve_left hw4
          have hy2 := bad_of_safe 2 (by decide) hw2
          have hy5 := bad_of_safe 5 (by decide) hw5
          rcases py25 with h | h
          · exact hy2 h
          · exact hy5 h
      · -- `w` bad at 2: safe at 4 via the (2,4) pair; `y` bad at 1 and 4.
        have hw4 := pw24.resolve_left hw2
        have hy1 := bad_of_safe 1 (by decide) hw1
        have hy4 := bad_of_safe 4 (by decide) hw4
        rcases py14 with h | h
        · exact hy1 h
        · exact hy4 h
    · -- `w` bad at 1: safe at 2 and 5; `y` bad at 2 and 5.
      have hw2 := pw12.resolve_left hw1
      have hw5 := pw15.resolve_left hw1
      have hy2 := bad_of_safe 2 (by decide) hw2
      have hy5 := bad_of_safe 5 (by decide) hw5
      rcases py25 with h | h
      · exact hy2 h
      · exact hy5 h
  obtain ⟨l, hlmem, hws, hys⟩ := key
  have hlb : 1 ≤ l ∧ l ≤ 5 := by
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert,
      Finset.mem_singleton] at hlmem
    rcases hlmem with rfl | rfl | rfl | rfl <;> norm_num
  have hsafea : safe6 a (t + (l : ℝ) / 6) :=
    (safe6_sixth_shift_anchor ha t l).mpr hsafe
  have hsafeu : safe6 u (t + (l : ℝ) / 6) :=
    safe6_sixth_shift_arc hu t l huarc (pm2_shift_thirds heu hlmem)
  have hsafez : safe6 z (t + (l : ℝ) / 6) :=
    safe6_sixth_shift_zero hz hez hz0 hlb.1 hlb.2
  exact all_safe_contra hsafea hsafeu hws hsafez hys hf

/-- Renault §4 PARA2: if the anchor is safe at `t`, the `±1`-runner `y` is in
the closed unsafe arc and the `±1`-runner `z` sits at `0`, then some
`l ∈ {1,…,5}` makes `t + l/6` fully safe — contradicting `hfail`.

Here `y` is automatically safe at every `l ∈ {2,3,4}` (its shift is a nonzero
third or half), so only the three middle slots need covering by the two `±2`
runners `u w` — each bad set has at most one element among `{2,3,4}`, since
all pairs there are at distance `≤ 2`. -/
theorem arg_zero_pm1 {a u w z y : ℕ} {eu ew ez ey : ℤ}
    (ha : (a : ℤ) ≡ 0 [ZMOD 6])
    (hu : (u : ℤ) ≡ eu [ZMOD 6]) (heu : eu = 2 ∨ eu = -2)
    (hw : (w : ℤ) ≡ ew [ZMOD 6]) (hew : ew = 2 ∨ ew = -2)
    (hz : (z : ℤ) ≡ ez [ZMOD 6]) (hez : ez = 1 ∨ ez = -1)
    (hy : (y : ℤ) ≡ ey [ZMOD 6]) (hey : ey = 1 ∨ ey = -1)
    {t : ℝ} (hsafe : safe6 a t)
    (hyarc : Int.fract ((y : ℝ) * t) ∉ Set.Ioo (1 / 6) (5 / 6))
    (hz0 : Int.fract ((z : ℝ) * t) = 0)
    (hf : hfail {a, u, w, z, y}) : False := by
  have key : ∃ l : ℤ, l ∈ ({2, 3, 4} : Finset ℤ) ∧
      safe6 u (t + (l : ℝ) / 6) ∧ safe6 w (t + (l : ℝ) / 6) := by
    by_contra hcon
    have bad_of_safe : ∀ l : ℤ, l ∈ ({2, 3, 4} : Finset ℤ) →
        safe6 u (t + (l : ℝ) / 6) → ¬ safe6 w (t + (l : ℝ) / 6) :=
      fun l hl hus hws => hcon ⟨l, hl, hus, hws⟩
    have pu23 := unsafe_pair_sixth' hu t 2 3
      (by rcases heu with rfl | rfl <;> norm_num)
    have pu24 := unsafe_pair_sixth' hu t 2 4
      (by rcases heu with rfl | rfl <;> norm_num)
    have pu34 := unsafe_pair_sixth' hu t 3 4
      (by rcases heu with rfl | rfl <;> norm_num)
    have pw23 := unsafe_pair_sixth' hw t 2 3
      (by rcases hew with rfl | rfl <;> norm_num)
    have pw24 := unsafe_pair_sixth' hw t 2 4
      (by rcases hew with rfl | rfl <;> norm_num)
    have pw34 := unsafe_pair_sixth' hw t 3 4
      (by rcases hew with rfl | rfl <;> norm_num)
    by_cases hu2 : safe6 u (t + ((2 : ℤ) : ℝ) / 6)
    · by_cases hu3 : safe6 u (t + ((3 : ℤ) : ℝ) / 6)
      · by_cases _hu4 : safe6 u (t + ((4 : ℤ) : ℝ) / 6)
        · -- `u` safe at 2,3,4: `w` bad at 2 and 3.
          have hw2 := bad_of_safe 2 (by decide) hu2
          have hw3 := bad_of_safe 3 (by decide) hu3
          rcases pw23 with h | h
          · exact hw2 h
          · exact hw3 h
        · -- `u` bad at 4, safe at 2 and 3: `w` bad at 2 and 3.
          have hw2 := bad_of_safe 2 (by decide) hu2
          have hw3 := bad_of_safe 3 (by decide) hu3
          rcases pw23 with h | h
          · exact hw2 h
          · exact hw3 h
      · -- `u` bad at 3: safe at 4 via the (3,4) pair; `w` bad at 2 and 4.
        have hu4 := pu34.resolve_left hu3
        have hw2 := bad_of_safe 2 (by decide) hu2
        have hw4 := bad_of_safe 4 (by decide) hu4
        rcases pw24 with h | h
        · exact hw2 h
        · exact hw4 h
    · -- `u` bad at 2: safe at 3 and 4; `w` bad at 3 and 4.
      have hu3 := pu23.resolve_left hu2
      have hu4 := pu24.resolve_left hu2
      have hw3 := bad_of_safe 3 (by decide) hu3
      have hw4 := bad_of_safe 4 (by decide) hu4
      rcases pw34 with h | h
      · exact hw3 h
      · exact hw4 h
  obtain ⟨l, hlmem, hus, hws⟩ := key
  have hlb : 1 ≤ l ∧ l ≤ 5 := by
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hlmem
    rcases hlmem with rfl | rfl | rfl <;> norm_num
  have hmemy : l ∈ ({2, 3, 4} : Finset ℤ) := hlmem
  have hsafea : safe6 a (t + (l : ℝ) / 6) :=
    (safe6_sixth_shift_anchor ha t l).mpr hsafe
  have hsafez : safe6 z (t + (l : ℝ) / 6) :=
    safe6_sixth_shift_zero hz hez hz0 hlb.1 hlb.2
  have hsfey : safe6 y (t + (l : ℝ) / 6) :=
    safe6_sixth_shift_arc hy t l hyarc (pm1_mid_shift_thirds hey hmemy)
  exact all_safe_contra hsafea hus hws hsafez hsfey hf

/-- Renault's "summing up" paragraph: whenever `z` (`e = ±1`) sits at `0` and the
anchor is safe, the two `±2` runners are strictly inside `(1/6,5/6)` and the
other `±1` runner lies in `(1/3,2/3)` — otherwise one of the shift arguments
above produces a fully safe time. -/
theorem combine_zero {a u w z y : ℕ} {eu ew ez ey : ℤ}
    (ha : (a : ℤ) ≡ 0 [ZMOD 6])
    (hu : (u : ℤ) ≡ eu [ZMOD 6]) (heu : eu = 2 ∨ eu = -2)
    (hw : (w : ℤ) ≡ ew [ZMOD 6]) (hew : ew = 2 ∨ ew = -2)
    (hz : (z : ℤ) ≡ ez [ZMOD 6]) (hez : ez = 1 ∨ ez = -1)
    (hy : (y : ℤ) ≡ ey [ZMOD 6]) (hey : ey = 1 ∨ ey = -1)
    (hf : hfail {a, u, w, z, y})
    {t : ℝ} (hsafe : safe6 a t) (hz0 : Int.fract ((z : ℝ) * t) = 0) :
    Int.fract ((u : ℝ) * t) ∈ Set.Ioo (1 / 6) (5 / 6) ∧
      Int.fract ((w : ℝ) * t) ∈ Set.Ioo (1 / 6) (5 / 6) ∧
      Int.fract ((y : ℝ) * t) ∈ Set.Ioo (1 / 3) (2 / 3) := by
  have huI : Int.fract ((u : ℝ) * t) ∈ Set.Ioo (1 / 6) (5 / 6) := by
    by_contra h
    exact arg_zero_pm2 ha hu heu hw hew hz hez hy hey hsafe h hz0 hf
  have hwI : Int.fract ((w : ℝ) * t) ∈ Set.Ioo (1 / 6) (5 / 6) := by
    by_contra h
    have hf' : hfail {a, w, u, z, y} := by
      have hset : ({a, w, u, z, y} : Finset ℕ) = {a, u, w, z, y} := by
        rw [Finset.insert_comm w u]
      rw [hset]; exact hf
    exact arg_zero_pm2 ha hw hew hu heu hz hez hy hey hsafe h hz0 hf'
  have hyI : Int.fract ((y : ℝ) * t) ∈ Set.Ioo (1 / 6) (5 / 6) := by
    by_contra h
    exact arg_zero_pm1 ha hu heu hw hew hz hez hy hey hsafe h hz0 hf
  have hyM : Int.fract ((y : ℝ) * t) ∈ Set.Ioo (1 / 3) (2 / 3) := by
    by_contra h
    have h2a : 2 ∣ a := dvd_trans (by norm_num : (2 : ℕ) ∣ 6) (six_dvd_of_modEq_zero ha)
    have h2u : 2 ∣ u := two_dvd_of_pm2 hu heu
    have h2w : 2 ∣ w := two_dvd_of_pm2 hw hew
    have hoz : ¬ 2 ∣ z := not_two_dvd_of_pm1 hz hez
    have hoy : ¬ 2 ∣ y := not_two_dvd_of_pm1 hy hey
    have has : safe6 a (t + 1 / 2) := by
      rw [safe6, fract_add_half_of_two_dvd h2a t]
      exact hsafe
    have hus : safe6 u (t + 1 / 2) := by
      rw [safe6, fract_add_half_of_two_dvd h2u t]
      exact Set.Ioo_subset_Icc_self huI
    have hws : safe6 w (t + 1 / 2) := by
      rw [safe6, fract_add_half_of_two_dvd h2w t]
      exact Set.Ioo_subset_Icc_self hwI
    have hzs : safe6 z (t + 1 / 2) := by
      rw [safe6, fract_add_shift z t (1 / 2)]
      rw [show (z : ℝ) * (1 / 2) = (z : ℝ) / 2 by ring, fract_add_half_of_odd hoz]
      rw [hz0, zero_add, Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩]
      exact Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩
    have hys : safe6 y (t + 1 / 2) := by
      rw [safe6, fract_add_shift y t (1 / 2)]
      rw [show (y : ℝ) * (1 / 2) = (y : ℝ) / 2 by ring, fract_add_half_of_odd hoy]
      exact fract_add_half_mem_Icc hyI h
    exact all_safe_contra has hus hws hzs hys hf
  exact ⟨huI, hwI, hyM⟩

/-- The divisibility step: each odd runner `z` divides the anchor `a`.

Paper argument: if `z ∤ a`, then at `t₀ = 1/z` we have `x_z = 0` and
`x_a = ⟨a/z⟩ ≠ 0`.  Either `x_a` is already in the open unsafe arc (band lemma
rescaled into `[1/12,1/6]`), or `x_a ∈ [1/6,5/6]` where Claim 2.4 pushes it back
to the closed arc; the `⟨5x_a⟩ = 0` subcase gives `x_a = m/5`, whence some
`⟨μ·x_a⟩ = 1/5`.  In all cases some `s` has `x_z(s) = 0` and
`x_a(s) ∈ [1/12,1/6] ∪ {1/5}`.  At `2s` and `4s` the anchor is still safe and
`x_z = 0`, so `combine_zero` gives `x_y(2s), x_y(4s) ∈ (1/3,2/3)` — impossible
because `x_y(4s) = ⟨2·x_y(2s)⟩`. -/
theorem dvd_of_odd_runner {a u w z y : ℕ} {eu ew ez ey : ℤ}
    (_hpa : 0 < a) (_hpu : 0 < u) (_hpw : 0 < w) (hpz : 0 < z) (_hpy : 0 < y)
    (ha : (a : ℤ) ≡ 0 [ZMOD 6])
    (hu : (u : ℤ) ≡ eu [ZMOD 6]) (heu : eu = 2 ∨ eu = -2)
    (hw : (w : ℤ) ≡ ew [ZMOD 6]) (hew : ew = 2 ∨ ew = -2)
    (hz : (z : ℤ) ≡ ez [ZMOD 6]) (hez : ez = 1 ∨ ez = -1)
    (hy : (y : ℤ) ≡ ey [ZMOD 6]) (hey : ey = 1 ∨ ey = -1)
    (hf : hfail {a, u, w, z, y}) : z ∣ a := by
  by_contra hzdvd
  set t₀ : ℝ := 1 / (z : ℝ) with ht₀
  have hzpos : (0 : ℝ) < z := by exact_mod_cast hpz
  have hzne : (z : ℝ) ≠ 0 := ne_of_gt hzpos
  have hz0 : Int.fract ((z : ℝ) * t₀) = 0 := by
    rw [ht₀, mul_one_div_cancel hzne]
    exact Int.fract_one
  set x := Int.fract ((a : ℝ) * t₀) with hx
  have hxb : 0 ≤ x ∧ x < 1 := ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
  have hx0 : x ≠ 0 := by
    intro h0
    rw [hx, Int.fract_eq_zero_iff] at h0
    obtain ⟨k, hk⟩ := h0
    -- `a / z = k`, so `z ∣ a`, contradiction.
    have h2 : (a : ℝ) * t₀ = (k : ℝ) := hk.symm
    rw [ht₀] at h2
    have h3 : (a : ℤ) = k * (z : ℤ) := by
      have h4 : (a : ℝ) = (k : ℝ) * (z : ℝ) := by
        have h2z : (a : ℝ) * (1 / (z : ℝ)) * (z : ℝ) = (k : ℝ) * (z : ℝ) := by
          rw [h2]
        rwa [mul_assoc, one_div_mul_cancel hzne, mul_one] at h2z
      have h5 : ((a : ℤ) : ℝ) = ((k * z : ℤ) : ℝ) := by push_cast; linarith [h4]
      exact_mod_cast h5
    have hkpos : 0 < k := by
      by_contra hkc
      push Not at hkc
      have hle : (a : ℤ) ≤ 0 := by
        rw [h3]
        exact mul_nonpos_of_nonpos_of_nonneg hkc (by exact_mod_cast hpz.le)
      exact absurd hle (by exact_mod_cast (not_le_of_gt _hpa))
    have hkdvd : z ∣ a := by
      refine ⟨k.toNat, ?_⟩
      have h1 : (k.toNat : ℤ) = k := Int.toNat_of_nonneg (le_of_lt hkpos)
      have h2' : ((z * k.toNat : ℕ) : ℤ) = (a : ℤ) := by
        push_cast; rw [h1]; linarith [h3]
      exact_mod_cast h2'.symm
    exact hzdvd hkdvd
  have hxp : 0 < x := lt_of_le_of_ne hxb.1 (Ne.symm hx0)
  -- If `fract (m·x)` lands in the band, `s = m·t₀` has `x_z(s)=0`,
  -- `x_a(s) ∈ [1/12,1/6]`.
  have refine_s : ∀ m : ℤ, Int.fract ((m : ℝ) * x) ∈ Set.Icc (1 / 12) (1 / 6) →
      Int.fract ((z : ℝ) * ((m : ℝ) * t₀)) = 0 ∧
        Int.fract ((a : ℝ) * ((m : ℝ) * t₀)) ∈ Set.Icc (1 / 12) (1 / 6) := by
    intro m hm
    constructor
    · rw [show (z : ℝ) * ((m : ℝ) * t₀) = (m : ℝ) * ((z : ℝ) * t₀) by ring]
      rw [← fract_int_mul, hz0, mul_zero]
      exact Int.fract_zero
    · rw [show (a : ℝ) * ((m : ℝ) * t₀) = (m : ℝ) * ((a : ℝ) * t₀) by ring]
      rw [← fract_int_mul, ← hx]
      exact hm
  -- `z` is coprime to `2,3,4` (it is odd and not a multiple of 3).
  have hzodd : ¬ 2 ∣ z := not_two_dvd_of_pm1 hz hez
  have hz3 : ¬ 3 ∣ z := not_three_dvd_of_mod6 hz
    (by rcases hez with h | h <;> simp [h])
  have hcop2 : Nat.Coprime z 2 :=
    Nat.coprime_comm.mp ((Nat.prime_two.coprime_iff_not_dvd).mpr hzodd)
  have hcop3 : Nat.Coprime z 3 :=
    Nat.coprime_comm.mp ((Nat.prime_three.coprime_iff_not_dvd).mpr hz3)
  have hcop4 : Nat.Coprime z 4 := by
    have h := hcop2.pow_right 2
    norm_num at h ⊢
    exact h
  -- `⟨m·x⟩ = 0` with `m ∈ {2,3,4}` gives `z ∣ m·a`, hence `z ∣ a`.
  have zdvd_of_lam_zero : ∀ m : ℕ, m ∈ ({2, 3, 4} : Finset ℕ) →
      Int.fract ((m : ℝ) * x) = 0 → z ∣ a := by
    intro m hm h0
    have h0' : Int.fract ((a : ℝ) * ((m : ℝ) * t₀)) = 0 := by
      have e2 : (m : ℝ) * ((a : ℝ) * t₀) = (a : ℝ) * ((m : ℝ) * t₀) := by ring
      have e1 : Int.fract ((m : ℝ) * x) =
          Int.fract ((m : ℝ) * ((a : ℝ) * t₀)) := by
        rw [hx, e2]
        exact (fract_nat_mul a m t₀).symm
      rw [e1, e2] at h0
      exact h0
    rw [Int.fract_eq_zero_iff] at h0'
    obtain ⟨k, hk⟩ := h0'
    have h2 : (a : ℝ) * ((m : ℝ) * t₀) = (k : ℝ) := hk.symm
    rw [ht₀] at h2
    have h3 : (m : ℤ) * (a : ℤ) = k * (z : ℤ) := by
      have h4 : ((m * a : ℕ) : ℝ) = (k : ℝ) * (z : ℝ) := by
        push_cast
        rw [show (m : ℝ) * (a : ℝ) = (a : ℝ) * ((m : ℝ) * (1 / (z : ℝ))) * (z : ℝ) by
          rw [mul_assoc, mul_assoc (m : ℝ) (1 / (z : ℝ)) (z : ℝ),
            one_div_mul_cancel hzne, mul_one, mul_comm (m : ℝ) (a : ℝ)], h2]
      exact_mod_cast h4
    have hzmd : (z : ℤ) ∣ (m : ℤ) * (a : ℤ) := ⟨k, by linarith [h3]⟩
    have hzmd' : z ∣ m * a := by
      have h5 : ((m * a : ℕ) : ℤ) = (m : ℤ) * (a : ℤ) := by push_cast; ring
      rw [← Int.natCast_dvd_natCast, h5]
      exact hzmd
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl | rfl
    · exact hcop2.dvd_of_dvd_mul_left hzmd'
    · exact hcop3.dvd_of_dvd_mul_left hzmd'
    · exact hcop4.dvd_of_dvd_mul_left hzmd'
  -- If `fract (m·x) = 1/5`, `s = m·t₀` has `x_z(s)=0`, `x_a(s) = 1/5`.
  have refine_s5 : ∀ m : ℤ, Int.fract ((m : ℝ) * x) = 1 / 5 →
      Int.fract ((z : ℝ) * ((m : ℝ) * t₀)) = 0 ∧
        Int.fract ((a : ℝ) * ((m : ℝ) * t₀)) = 1 / 5 := by
    intro m hm
    constructor
    · rw [show (z : ℝ) * ((m : ℝ) * t₀) = (m : ℝ) * ((z : ℝ) * t₀) by ring]
      rw [← fract_int_mul, hz0, mul_zero]
      exact Int.fract_zero
    · rw [show (a : ℝ) * ((m : ℝ) * t₀) = (m : ℝ) * ((a : ℝ) * t₀) by ring]
      rw [← fract_int_mul, ← hx]
      exact hm
  -- find `s` with `x_z(s) = 0` and `x_a(s) ∈ [1/12,1/6] ∪ {1/5}`
  obtain ⟨s, hz0s, hsband⟩ : ∃ s : ℝ, Int.fract ((z : ℝ) * s) = 0 ∧
      (Int.fract ((a : ℝ) * s) ∈ Set.Icc (1 / 12) (1 / 6) ∨
        Int.fract ((a : ℝ) * s) = 1 / 5) := by
    by_cases hcase : x ∈ Set.Icc (1 / 6) (5 / 6)
    · obtain ⟨lam, hlam, hbad⟩ := claim2_4_closed hcase
      by_cases hz' : Int.fract ((lam : ℝ) * x) = 0
      · -- `⟨λx⟩ = 0` forces `λ = 5` (the other `λ` are coprime to `z`).
        have hlam5 : lam = 5 := by
          have hmem : lam = 2 ∨ lam = 3 ∨ lam = 4 ∨ lam = 5 := by
            rw [Finset.mem_Icc] at hlam
            omega
          rcases hmem with rfl | rfl | rfl | rfl
          · exact absurd (zdvd_of_lam_zero 2 (by decide) hz') hzdvd
          · exact absurd (zdvd_of_lam_zero 3 (by decide) hz') hzdvd
          · exact absurd (zdvd_of_lam_zero 4 (by decide) hz') hzdvd
          · rfl
        -- `x = kk/5` with `kk ∈ {1,2,3,4}`; pick `μ` with `μ·kk ≡ 1 (mod 5)`.
        rw [hlam5] at hz'
        rw [Int.fract_eq_zero_iff] at hz'
        obtain ⟨kk, hkk⟩ := hz'
        have h5 : (5 : ℝ) * x = (kk : ℝ) := by
          have h := hkk
          push_cast at h ⊢
          linarith [h]
        have hkkr : 1 ≤ kk ∧ kk ≤ 4 := by
          have hp1 : (0 : ℝ) < (kk : ℝ) := by rw [← h5]; linarith [hxp]
          have hp2 : (kk : ℝ) < 5 := by rw [← h5]; linarith [hxb.2]
          have hp1' : 0 < kk := by exact_mod_cast hp1
          have hp2' : kk < 5 := by exact_mod_cast hp2
          omega
        obtain ⟨hkk1, hkk4⟩ := hkkr
        interval_cases kk
        · -- `x = 1/5`, `μ = 1`.
          push_cast at h5
          have e : Int.fract (((1 : ℤ) : ℝ) * x) = 1 / 5 := by
            rw [Int.cast_one, one_mul]
            rw [show x = (1 / 5 : ℝ) by linarith [h5]]
            exact Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩
          exact ⟨(1 : ℤ) * t₀, (refine_s5 1 e).1, Or.inr (refine_s5 1 e).2⟩
        · -- `x = 2/5`, `μ = 3`.
          push_cast at h5
          have e : Int.fract (((3 : ℤ) : ℝ) * x) = 1 / 5 := by
            rw [show ((3 : ℤ) : ℝ) * x = (1 / 5 : ℝ) + ((1 : ℤ) : ℝ) by
              push_cast; linarith [h5]]
            rw [Int.fract_add_intCast]
            exact Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩
          exact ⟨(3 : ℤ) * t₀, (refine_s5 3 e).1, Or.inr (refine_s5 3 e).2⟩
        · -- `x = 3/5`, `μ = 2`.
          push_cast at h5
          have e : Int.fract (((2 : ℤ) : ℝ) * x) = 1 / 5 := by
            rw [show ((2 : ℤ) : ℝ) * x = (1 / 5 : ℝ) + ((1 : ℤ) : ℝ) by
              push_cast; linarith [h5]]
            rw [Int.fract_add_intCast]
            exact Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩
          exact ⟨(2 : ℤ) * t₀, (refine_s5 2 e).1, Or.inr (refine_s5 2 e).2⟩
        · -- `x = 4/5`, `μ = 4`.
          push_cast at h5
          have e : Int.fract (((4 : ℤ) : ℝ) * x) = 1 / 5 := by
            rw [show ((4 : ℤ) : ℝ) * x = (1 / 5 : ℝ) + ((3 : ℤ) : ℝ) by
              push_cast; linarith [h5]]
            rw [Int.fract_add_intCast]
            exact Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩
          exact ⟨(4 : ℤ) * t₀, (refine_s5 4 e).1, Or.inr (refine_s5 4 e).2⟩
      · -- `⟨λx⟩ ≠ 0` in the closed arc: rescale into the band.
        obtain ⟨mu, hmu⟩ := rescale_to_band (Int.fract_nonneg _)
          (Int.fract_lt_one _) hz' hbad
        have e : Int.fract ((((mu * (lam : ℤ)) : ℤ) : ℝ) * x) ∈
            Set.Icc (1 / 12) (1 / 6) := by
          have e2 : (((mu * (lam : ℤ)) : ℤ) : ℝ) * x =
              (mu : ℝ) * ((lam : ℝ) * x) := by push_cast; ring
          rw [e2, ← fract_int_mul]
          exact hmu
        exact ⟨((mu * (lam : ℤ)) : ℤ) * t₀, (refine_s _ e).1,
          Or.inl (refine_s _ e).2⟩
    · -- `x` is already in the open unsafe arc: the band lemma applies.
      rcases open_unsafe_arc hcase with hlo | hhi
      · obtain ⟨lam, hlam⟩ := exists_int_mul_Ioo_band (Or.inl ⟨hxp, hlo⟩)
        exact ⟨(lam : ℝ) * t₀, (refine_s lam hlam).1,
          Or.inl (refine_s lam hlam).2⟩
      · obtain ⟨lam, hlam⟩ := exists_int_mul_Ioo_band (Or.inr ⟨hhi, hxb.2⟩)
        exact ⟨(lam : ℝ) * t₀, (refine_s lam hlam).1,
          Or.inl (refine_s lam hlam).2⟩
  -- At `2s` and `4s`: anchor safe, `x_z = 0` ⇒ `x_y ∈ (1/3,2/3)` — contradiction.
  have hsa2 : safe6 a (2 * s) := by
    have e : Int.fract ((a : ℝ) * (2 * s)) =
        Int.fract ((2 : ℝ) * Int.fract ((a : ℝ) * s)) := by
      simpa using fract_nat_mul a 2 s
    rw [safe6, e]
    rcases hsband with hband | hfifth
    · rw [Set.mem_Icc] at hband
      have h2 : Int.fract ((2 : ℝ) * Int.fract ((a : ℝ) * s)) =
          (2 : ℝ) * Int.fract ((a : ℝ) * s) :=
        Int.fract_eq_self.mpr ⟨by linarith [hband.1], by linarith [hband.2]⟩
      rw [h2]
      exact Set.mem_Icc.mpr ⟨by linarith, by linarith⟩
    · rw [hfifth]
      rw [show (2 : ℝ) * (1 / 5) = (2 / 5 : ℝ) by norm_num]
      rw [Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩]
      exact Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩
  have hsa4 : safe6 a (4 * s) := by
    have e : Int.fract ((a : ℝ) * (4 * s)) =
        Int.fract ((4 : ℝ) * Int.fract ((a : ℝ) * s)) := by
      simpa using fract_nat_mul a 4 s
    rw [safe6, e]
    rcases hsband with hband | hfifth
    · rw [Set.mem_Icc] at hband
      have h2 : Int.fract ((4 : ℝ) * Int.fract ((a : ℝ) * s)) =
          (4 : ℝ) * Int.fract ((a : ℝ) * s) :=
        Int.fract_eq_self.mpr ⟨by linarith [hband.1], by linarith [hband.2]⟩
      rw [h2]
      exact Set.mem_Icc.mpr ⟨by linarith, by linarith⟩
    · rw [hfifth]
      rw [show (4 : ℝ) * (1 / 5) = (4 / 5 : ℝ) by norm_num]
      rw [Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩]
      exact Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩
  have hz02 : Int.fract ((z : ℝ) * (2 * s)) = 0 := by
    have e : Int.fract ((z : ℝ) * (2 * s)) =
        Int.fract ((2 : ℝ) * Int.fract ((z : ℝ) * s)) := by
      simpa using fract_nat_mul z 2 s
    rw [e, hz0s, mul_zero]
    exact Int.fract_zero
  have hz04 : Int.fract ((z : ℝ) * (4 * s)) = 0 := by
    have e : Int.fract ((z : ℝ) * (4 * s)) =
        Int.fract ((4 : ℝ) * Int.fract ((z : ℝ) * s)) := by
      simpa using fract_nat_mul z 4 s
    rw [e, hz0s, mul_zero]
    exact Int.fract_zero
  obtain ⟨-, -, hy2⟩ := combine_zero ha hu heu hw hew hz hez hy hey hf hsa2 hz02
  obtain ⟨-, -, hy4⟩ := combine_zero ha hu heu hw hew hz hez hy hey hf hsa4 hz04
  have h4eq : Int.fract ((y : ℝ) * (4 * s)) =
      Int.fract (2 * Int.fract ((y : ℝ) * (2 * s))) := by
    have e : (y : ℝ) * (4 * s) = (y : ℝ) * (((2 : ℕ) : ℝ) * (2 * s)) := by
      push_cast; ring
    rw [e, fract_nat_mul]
    simp only [Nat.cast_ofNat]
  rw [h4eq] at hy4
  exact fract_two_Ioo hy2 hy4

/-- `z ∣ a` upgrades to `6·z ∣ a`: since `a ≡ 0` and `z ≡ ±1 (mod 6)`, the
quotient `a/z` is itself a multiple of `6`. -/
theorem six_mul_dvd_of_odd_runner {a z : ℕ} {e : ℤ}
    (ha : (a : ℤ) ≡ 0 [ZMOD 6]) (hz : (z : ℤ) ≡ e [ZMOD 6])
    (he : e = 1 ∨ e = -1) (hzd : z ∣ a) : 6 * z ∣ a := by
  obtain ⟨m, hm⟩ := hzd
  have hmz : (m : ℤ) ≡ 0 [ZMOD 6] := by
    have h1 : (z : ℤ) * (m : ℤ) ≡ e * (m : ℤ) [ZMOD 6] :=
      hz.mul (Int.ModEq.refl m)
    have h2 : e * (m : ℤ) ≡ 0 [ZMOD 6] := by
      have h3 : ((z : ℤ) * (m : ℤ)) ≡ 0 [ZMOD 6] := by
        have ham : (a : ℤ) = (z : ℤ) * (m : ℤ) := by exact_mod_cast hm
        rw [← ham]
        exact ha
      exact h1.symm.trans h3
    rcases he with rfl | rfl
    · simpa using h2
    · have h4 : (-m : ℤ) ≡ 0 [ZMOD 6] := by simpa using h2
      rw [Int.modEq_zero_iff_dvd] at h4 ⊢
      exact Int.dvd_neg.mp h4
  have h6m : 6 ∣ m := by
    have h : (6 : ℤ) ∣ (m : ℤ) := Int.modEq_zero_iff_dvd.mp hmz
    exact_mod_cast h
  obtain ⟨k, hk⟩ := h6m
  exact ⟨k, by rw [hm, hk]; ring⟩

/-- At `tt = 1/(6a)`, runner `z` with `6z ≤ a` has `x_z(λtt) = λz/(6a) ∈ (0,1/6)`
for `λ ∈ {1,…,5}` — strictly unsafe. -/
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

/-- **Renault's Proposition 4.1**: three even speeds force `D ≠ ∅`. -/
theorem prop4_1 {v₁ v₂ v₃ v₄ v₅ : ℕ}
    (hp1 : 0 < v₁) (hp2 : 0 < v₂) (hp3 : 0 < v₃) (hp4 : 0 < v₄) (hp5 : 0 < v₅)
    (hv1 : (v₁ : ℤ) ≡ 0 [ZMOD 6])
    {e₂ e₃ e₄ e₅ : ℤ}
    (hv2 : (v₂ : ℤ) ≡ e₂ [ZMOD 6]) (hv3 : (v₃ : ℤ) ≡ e₃ [ZMOD 6])
    (hv4 : (v₄ : ℤ) ≡ e₄ [ZMOD 6]) (hv5 : (v₅ : ℤ) ≡ e₅ [ZMOD 6])
    (he2 : e₂ = 2 ∨ e₂ = -2) (he3 : e₃ = 2 ∨ e₃ = -2)
    (he4 : e₄ = 1 ∨ e₄ = -1) (he5 : e₅ = 1 ∨ e₅ = -1)
    (hf : hfail {v₁, v₂, v₃, v₄, v₅}) : False := by
  have h6v1 : 6 ∣ v₁ := six_dvd_of_modEq_zero hv1
  have h3v1 : 3 ∣ v₁ := dvd_trans (by norm_num : (3 : ℕ) ∣ 6) h6v1
  have h41 : v₄ ∣ v₁ :=
    dvd_of_odd_runner hp1 hp2 hp3 hp4 hp5 hv1 hv2 he2 hv3 he3 hv4 he4 hv5 he5 hf
  have h51 : v₅ ∣ v₁ := by
    have hf' : hfail {v₁, v₂, v₃, v₅, v₄} := by
      intro t
      obtain ⟨d, hd, hns⟩ := hf t
      refine ⟨d, ?_, hns⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at hd ⊢
      rcases hd with rfl | rfl | rfl | rfl | rfl <;> simp
    exact dvd_of_odd_runner hp1 hp2 hp3 hp5 hp4 hv1 hv2 he2 hv3 he3 hv5 he5 hv4
      he4 hf'
  have hsix4 : 6 * v₄ ∣ v₁ := six_mul_dvd_of_odd_runner hv1 hv4 he4 h41
  have hsix5 : 6 * v₅ ∣ v₁ := six_mul_dvd_of_odd_runner hv1 hv5 he5 h51
  have hv14 : 6 * v₄ ≤ v₁ := Nat.le_of_dvd hp1 hsix4
  have hv15 : 6 * v₅ ≤ v₁ := Nat.le_of_dvd hp1 hsix5
  set tt : ℝ := 1 / (6 * (v₁ : ℝ)) with htt
  have hv1pos : (0 : ℝ) < v₁ := by exact_mod_cast hp1
  have hanch : ∀ lam : ℕ, 1 ≤ lam → lam ≤ 5 → safe6 v₁ ((lam : ℝ) * tt) := by
    intro lam h1 h5
    have hv1ne : (v₁ : ℝ) ≠ 0 := ne_of_gt hv1pos
    have e : (v₁ : ℝ) * ((lam : ℝ) * tt) = (lam : ℝ) / 6 := by
      rw [htt]; field_simp
    rw [safe6, e]
    exact alpha_Icc h1 h5
  have h4arc : ∀ lam : ℕ, 1 ≤ lam → lam ≤ 5 →
      Int.fract ((v₄ : ℝ) * ((lam : ℝ) * tt)) ∉ Set.Ioo (1 / 6) (5 / 6) := by
    intro lam h1 h5
    have h2 := sixth_lt_of_dvd hp1 hp4 hv14 h1 h5 htt
    intro hmem
    rw [Set.mem_Ioo] at hmem
    linarith [hmem.1, h2.2]
  have h5arc : ∀ lam : ℕ, 1 ≤ lam → lam ≤ 5 →
      Int.fract ((v₅ : ℝ) * ((lam : ℝ) * tt)) ∉ Set.Ioo (1 / 6) (5 / 6) := by
    intro lam h1 h5
    have h2 := sixth_lt_of_dvd hp1 hp5 hv15 h1 h5 htt
    intro hmem
    rw [Set.mem_Ioo] at hmem
    linarith [hmem.1, h2.2]
  have h23 : ¬ 3 ∣ v₂ := not_three_dvd_of_mod6 hv2
    (by rcases he2 with h | h <;> simp [h])
  have h33 : ¬ 3 ∣ v₃ := not_three_dvd_of_mod6 hv3
    (by rcases he3 with h | h <;> simp [h])
  have h43 : ¬ 3 ∣ v₄ := not_three_dvd_of_mod6 hv4
    (by rcases he4 with h | h <;> simp [h])
  have h53 : ¬ 3 ∣ v₅ := not_three_dvd_of_mod6 hv5
    (by rcases he5 with h | h <;> simp [h])
  -- Argument 3 contrapositive: `x₂(λtt) ∈ (1/6,5/6)` for all `λ ∈ {1,…,5}`.
  have hI2 : ∀ lam : ℕ, 1 ≤ lam → lam ≤ 5 →
      Int.fract ((v₂ : ℝ) * ((lam : ℝ) * tt)) ∈ Set.Ioo (1 / 6) (5 / 6) := by
    intro lam h1 h5
    by_contra hcon
    have hf' : hfail {v₁, v₂, v₄, v₅, v₃} := by
      intro t
      obtain ⟨d, hd, hns⟩ := hf t
      refine ⟨d, ?_, hns⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at hd ⊢
      rcases hd with rfl | rfl | rfl | rfl | rfl <;> simp
    exact arg3 h3v1 h23 h43 h53 h33 (hanch lam h1 h5) hcon
      (h4arc lam h1 h5) (h5arc lam h1 h5) hf'
  -- Claim 2.4 kills it: some `λ ∈ {2,…,5}` makes `⟨λ·x₂(tt)⟩` unsafe.
  have hx2 : Int.fract ((v₂ : ℝ) * tt) ∈ Set.Ioo (1 / 6) (5 / 6) := by
    have h := hI2 1 (by norm_num) (by norm_num)
    simpa using h
  obtain ⟨lam, hlam, hbad⟩ := claim2_4 hx2
  rw [Finset.mem_Icc] at hlam
  have heq : Int.fract ((v₂ : ℝ) * ((lam : ℝ) * tt)) =
      Int.fract ((lam : ℝ) * Int.fract ((v₂ : ℝ) * tt)) :=
    fract_nat_mul v₂ lam tt
  have hsafe : Int.fract ((lam : ℝ) * Int.fract ((v₂ : ℝ) * tt)) ∈
      Set.Icc (1 / 6) (5 / 6) := by
    rw [← heq]
    exact Set.Ioo_subset_Icc_self (hI2 lam (by omega) hlam.2)
  exact hbad hsafe

end
