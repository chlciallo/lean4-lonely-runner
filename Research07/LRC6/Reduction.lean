/-
Copyright (c) 2026 Research07 contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Research07 contributors
-/
import Mathlib
import Research07.LRC6.Setup
import Research07.LRC5.IntCase

/-!
# Renault §2 reductions

Renault's Section 2 preliminaries for the six-runner theorem.  We work with the
guard-safe / failing-time formulation matching `lrc6_int`:

* `safe6 d t` — runner `d` is safe at time `t`: `⟨t·d⟩ ∈ [1/6, 5/6]`
  (equivalently `circ (t·d) ≥ 1/6`).
* `hfail D` — Renault's `D = ∅`: no time makes every runner safe.

The lemmas here mirror Renault's Lemma 2.1 (counting multiples), Lemma 2.2
(a `≥ 5×` speed), Lemma 2.3 (three multiples of 3) and Claim 2.4 (a small
multiplier always escapes the safe band).
-/

noncomputable section

/-- Runner `d` is safe at time `t` when its fractional position lies in the
sixth-gap arc `[1/6, 5/6]` — Renault's "`xᵢ(t) ∈ [1/6,5/6]`". -/
def safe6 (d : ℕ) (t : ℝ) : Prop :=
  Int.fract ((d : ℝ) * t) ∈ Set.Icc (1 / 6) (5 / 6)

/-- `safe6` is equivalent to `circ ≥ 1/6`. -/
theorem safe6_iff (d : ℕ) (t : ℝ) :
    safe6 d t ↔ (1 / 6 : ℝ) ≤ circ ((d : ℝ) * t) := by
  rw [safe6, ← circ_ge_sixth_fract]

/-- Renault's `D = ∅`: at every time some runner is unsafe. -/
def hfail (D : Finset ℕ) : Prop :=
  ∀ t : ℝ, ∃ d ∈ D, ¬ safe6 d t

/-- `¬ hfail D` is exactly the existence of a fully-safe time. -/
theorem not_hfail_iff {D : Finset ℕ} :
    ¬ hfail D ↔ ∃ t : ℝ, ∀ d ∈ D, safe6 d t := by
  unfold hfail
  push Not
  rfl

/-- Lemma 2.1, the `≥ 1` direction: under `hfail`, every `l ∈ {2,…,6}` divides
some speed.  At `t = 1/l`, a non-multiple of `l` lands on `{1/l,…,(l-1)/l}`,
which is a safe arc for `l ≤ 6`. -/
theorem hfail_exists_dvd {D : Finset ℕ} (hf : hfail D) {l : ℕ}
    (hl2 : 2 ≤ l) (hl6 : l ≤ 6) : ∃ d ∈ D, l ∣ d := by
  classical
  by_contra hcon
  push Not at hcon
  -- at `t = 1/l` every runner is safe, contradicting `hfail`
  obtain ⟨d, hd, hdu⟩ := hf (1 / (l : ℝ))
  have hlpos : (0 : ℝ) < l := by exact_mod_cast (by omega : 0 < l)
  have hdpos : (0:ℝ) < d := by
    -- `d ∈ D`; positivity needed for `fract (d/l)` computation below
    rcases eq_or_ne d 0 with rfl | hd0
    · exfalso; exact hcon 0 hd (dvd_zero _)
    · exact_mod_cast Nat.pos_of_ne_zero hd0
  have hnot : ¬ l ∣ d := hcon d hd
  -- `fract (d * (1/l)) = (d % l)/l`, which lies in `[1/l, (l-1)/l] ⊆ [1/6,5/6]`.
  have hfr : Int.fract ((d : ℝ) * (1 / (l : ℝ))) = ((d % l : ℕ) : ℝ) / l := by
    have hdl : (d : ℝ) * (1 / (l : ℝ)) = ((d % l : ℕ) : ℝ) / l + (d / l : ℕ) := by
      have hlne : (l : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have h2 : (d : ℝ) = (l : ℝ) * ((d / l : ℕ) : ℝ) + ((d % l : ℕ) : ℝ) := by
        exact_mod_cast (Nat.div_add_mod d l).symm
      rw [h2]
      field_simp
      ring
    rw [hdl, Int.fract_add_natCast, Int.fract_eq_self.mpr]
    · constructor
      · positivity
      · have : (d % l : ℕ) < l := Nat.mod_lt d (by omega : 0 < l)
        have : ((d % l : ℕ) : ℝ) < l := by exact_mod_cast this
        rw [div_lt_one hlpos]; linarith
  -- `(d % l)/l ∈ [1/6, 5/6]`
  have hrange : ((d % l : ℕ) : ℝ) / l ∈ Set.Icc (1 / 6) (5 / 6) := by
    have hm : (1 : ℝ) ≤ (d % l : ℕ) := by
      have h0 : 1 ≤ d % l := by
        rcases Nat.eq_zero_or_pos (d % l) with h | h
        · exfalso; exact hnot (Nat.dvd_of_mod_eq_zero h)
        · exact h
      exact_mod_cast h0
    have hlt : d % l + 1 ≤ l := by
      have h1 : d % l < l := Nat.mod_lt d (by omega : 0 < l)
      omega
    have hl6r : (l : ℝ) ≤ 6 := by exact_mod_cast hl6
    have h1l : (1 : ℝ) / 6 ≤ 1 / (l : ℝ) := by
      rw [div_le_div_iff₀ (by norm_num) hlpos]
      linarith
    constructor
    · calc (1 : ℝ) / 6 ≤ 1 / (l : ℝ) := h1l
        _ ≤ ((d % l : ℕ) : ℝ) / l := by gcongr
    · have hle : ((d % l : ℕ) : ℝ) ≤ (l : ℝ) - 1 := by
        have h1 : ((d % l : ℕ) : ℝ) + 1 ≤ (l : ℝ) := by exact_mod_cast hlt
        linarith
      calc ((d % l : ℕ) : ℝ) / l ≤ ((l : ℝ) - 1) / l := by gcongr
        _ = 1 - 1 / (l : ℝ) := by field_simp
        _ ≤ 1 - 1 / 6 := by linarith
        _ = 5 / 6 := by norm_num
  rw [safe6, hfr] at hdu
  exact hdu hrange

/-- A point outside the safe band `[1/6,5/6]` lies in `(5/6,1) ∪ [0,1/6)`. -/
theorem unsafe_arc {x : ℝ} (h : Int.fract x ∉ Set.Icc (1 / 6) (5 / 6)) :
    Int.fract x < 1 / 6 ∨ 5 / 6 < Int.fract x := by
  rw [Set.mem_Icc, not_and_or] at h
  rcases h with h | h
  · exact Or.inl (not_le.mp h)
  · exact Or.inr (not_le.mp h)

/-- Two unsafe positions have `|u − v| < 1/6` (same side) or `> 2/3`
(opposite sides).  The unsafe arc has length `1/3`, so two distinct unsafe
points `1/3`-separated cannot coexist — this is the pigeonhole behind
Renault's shift-by-`l/l` arguments. -/
theorem unsafe_pair_abs {u v : ℝ}
    (hu : Int.fract u ∉ Set.Icc (1 / 6) (5 / 6))
    (hv : Int.fract v ∉ Set.Icc (1 / 6) (5 / 6)) :
    |Int.fract u - Int.fract v| < 1 / 6 ∨ 2 / 3 < |Int.fract u - Int.fract v| := by
  have hu0 := Int.fract_nonneg u
  have hu1 := Int.fract_lt_one u
  have hv0 := Int.fract_nonneg v
  have hv1 := Int.fract_lt_one v
  rcases unsafe_arc hu with hu | hu <;> rcases unsafe_arc hv with hv | hv
  · -- both `< 1/6`: `|u − v| < 1/6`
    left; rw [abs_lt]; constructor <;> linarith
  · -- `u < 1/6`, `v > 5/6`: `v − u > 2/3`
    right; rw [abs_of_neg (by linarith : Int.fract u - Int.fract v < 0)]
    linarith
  · -- `u > 5/6`, `v < 1/6`: `u − v > 2/3`
    right; rw [abs_of_pos (by linarith : 0 < Int.fract u - Int.fract v)]
    linarith
  · -- both `> 5/6`: `|u − v| < 1/6`
    left; rw [abs_lt]; constructor <;> linarith

/-- `fract (d·(t + l/3))` shifts runner `d`'s position by `d·l/3` modulo `1`. -/
theorem fract_third_shift (d l : ℕ) (t : ℝ) :
    Int.fract ((d : ℝ) * (t + (l : ℝ) / 3)) =
      Int.fract (Int.fract ((d : ℝ) * t) + (d : ℝ) * (l : ℝ) / 3) := by
  have h1 : (d : ℝ) * (t + (l : ℝ) / 3) =
      Int.fract ((d : ℝ) * t) + (d : ℝ) * (l : ℝ) / 3 + ((⌊(d : ℝ) * t⌋ : ℤ) : ℝ) := by
    have h2 := Int.self_sub_fract ((d : ℝ) * t)
    linear_combination h2
  rw [h1, Int.fract_add_intCast]

/-- The positions `⟨u + d·l/3⟩` for `l ∈ {0,1,2}`, `3 ∤ d`, form a `1/3`-coset.
`fract` of `u + s` for `s ∈ (0,1)` lands in `{u+s, u+s-1}`. -/
theorem fract_add_small {u s : ℝ} (hu : 0 ≤ u) (hu1 : u < 1) (hs0 : 0 < s) (hs1 : s < 1) :
    Int.fract (u + s) = u + s ∨ Int.fract (u + s) = u + s - 1 := by
  by_cases h : u + s < 1
  · left; exact Int.fract_eq_self.mpr ⟨by linarith, h⟩
  · right
    have : Int.fract (u + s) = u + s - 1 := by
      rw [Int.fract_eq_iff]
      refine ⟨by linarith, by linarith, 1, by ring⟩
    exact this

/-- The `1/3`-shift pigeonhole: for `3 ∤ d`, among `t, t+1/3, t+2/3` at most one
shift is unsafe for runner `d`.  Stated pairwise: two distinct shifts cannot
both be unsafe. -/
theorem bad_third_le_one {d : ℕ} (hd : ¬ 3 ∣ d) (t : ℝ) {l₁ l₂ : ℕ}
    (h₁ : l₁ < 3) (h₂ : l₂ < 3) (hne : l₁ < l₂) :
    safe6 d (t + (l₁ : ℝ) / 3) ∨ safe6 d (t + (l₂ : ℝ) / 3) := by
  by_contra hb
  push Not at hb
  obtain ⟨hb1, hb2⟩ := hb
  set u := Int.fract ((d : ℝ) * t) with hu
  set p₁ := Int.fract ((d : ℝ) * (t + (l₁ : ℝ) / 3)) with hp₁
  set p₂ := Int.fract ((d : ℝ) * (t + (l₂ : ℝ) / 3)) with hp₂
  have hp₁' : p₁ = Int.fract (u + (d : ℝ) * (l₁ : ℝ) / 3) := by
    rw [hp₁, fract_third_shift, hu]
  have hp₂' : p₂ = Int.fract (u + (d : ℝ) * (l₂ : ℝ) / 3) := by
    rw [hp₂, fract_third_shift, hu]
  -- `p₂ − p₁ ≡ d(l₂−l₁)/3 (mod 1)` and `fract(d(l₂−l₁)/3) ∈ {1/3,2/3}`
  have hd3 : d % 3 ≠ 0 := fun h => hd (Nat.dvd_of_mod_eq_zero h)
  have hq : (d * (l₂ - l₁)) % 3 = 1 ∨ (d * (l₂ - l₁)) % 3 = 2 := by
    have hk : l₂ - l₁ = 1 ∨ l₂ - l₁ = 2 := by omega
    rcases hk with h | h
    · rw [h, Nat.mul_one]
      omega
    · have h2 : d * (l₂ - l₁) = d * 2 := by rw [h]
      rw [h2]
      have : ¬ 3 ∣ d * 2 := by
        intro hcon
        apply hd
        rcases (Nat.prime_three.dvd_mul).mp hcon with h3 | h3
        · exact h3
        · norm_num at h3
      omega
  -- `q = d(l₂−l₁)`; `fract (q/3) = (q%3)/3 ∈ {1/3, 2/3}`
  set q := d * (l₂ - l₁) with hqdef
  have hq4 : Int.fract ((q : ℝ) / 3) = ((q % 3 : ℕ) : ℝ) / 3 := by
    have hde : (q : ℝ) / 3 = ((q % 3 : ℕ) : ℝ) / 3 + ((q / 3 : ℕ) : ℝ) := by
      have h' : (q : ℝ) = ((q % 3 : ℕ) : ℝ) + 3 * ((q / 3 : ℕ) : ℝ) := by
        exact_mod_cast (Nat.mod_add_div q 3).symm
      field_simp
      linarith [h']
    rw [hde, Int.fract_add_natCast]
    have hqle : ((q % 3 : ℕ) : ℝ) < 3 := by
      have hlt : q % 3 < 3 := Nat.mod_lt q (by norm_num)
      exact_mod_cast hlt
    exact Int.fract_eq_self.mpr ⟨by positivity, by linarith⟩
  -- `fract (u + d·l₂/3) = fract (p₁ + q/3)`
  have hfr : Int.fract (u + (d : ℝ) * (l₂ : ℝ) / 3) =
      Int.fract (p₁ + (q : ℝ) / 3) := by
    have hqcast : (d : ℝ) * ((l₂ : ℝ) - (l₁ : ℝ)) = (q : ℝ) := by
      rw [hqdef, ← Nat.cast_sub hne.le, Nat.cast_mul]
    have hw : u + (d : ℝ) * (l₂ : ℝ) / 3 =
        (u + (d : ℝ) * (l₁ : ℝ) / 3) + (q : ℝ) / 3 := by
      linear_combination hqcast / 3
    rw [hw]
    have hself : (u + (d : ℝ) * (l₁ : ℝ) / 3) + (q : ℝ) / 3 =
        (Int.fract (u + (d : ℝ) * (l₁ : ℝ) / 3) + (q : ℝ) / 3) +
          ((⌊u + (d : ℝ) * (l₁ : ℝ) / 3⌋ : ℤ) : ℝ) := by
      have h2 := Int.self_sub_fract (u + (d : ℝ) * (l₁ : ℝ) / 3)
      linear_combination h2
    rw [hself, Int.fract_add_intCast]
    rw [hp₁']
  -- `fract (p₁ + q/3) = fract (p₁ + fract (q/3))`
  have hdrop : Int.fract (p₁ + (q : ℝ) / 3) =
      Int.fract (p₁ + Int.fract ((q : ℝ) / 3)) := by
    have hself : p₁ + (q : ℝ) / 3 =
        (p₁ + Int.fract ((q : ℝ) / 3)) + ((⌊(q : ℝ) / 3⌋ : ℤ) : ℝ) := by
      have h2 := Int.self_sub_fract ((q : ℝ) / 3)
      linear_combination h2
    rw [hself, Int.fract_add_intCast]
  -- `p₂ = fract (p₁ + r)` with `r = (q%3)/3`
  have hp2 : p₂ = Int.fract (p₁ + ((q % 3 : ℕ) : ℝ) / 3) := by
    rw [hp₂', hfr, hdrop, hq4]
  -- `fract (p₁ + r) ∈ {p₁+r, p₁+r−1}` gives `|p₂ − p₁| ∈ {1/3, 2/3}`
  have hbnd : (1 : ℝ) / 3 ≤ |p₂ - p₁| ∧ |p₂ - p₁| ≤ 2 / 3 := by
    have hr0 : (0 : ℝ) < ((q % 3 : ℕ) : ℝ) / 3 ∧ ((q % 3 : ℕ) : ℝ) / 3 < 1 := by
      rcases hq with hqm | hqm <;> rw [hqm] <;> norm_num
    have hr3 : ((q % 3 : ℕ) : ℝ) / 3 ∈ Set.Icc (1 / 3) (2 / 3) := by
      rcases hq with hqm | hqm <;> rw [hqm] <;> refine ⟨?_, ?_⟩ <;> norm_num
    rcases @fract_add_small p₁ (((q % 3 : ℕ) : ℝ) / 3)
        (Int.fract_nonneg _) (Int.fract_lt_one _) hr0.1 hr0.2
        with hcase | hcase <;> rw [hp2, hcase]
    · rw [abs_of_pos (by linarith [hr0.1] : (0 : ℝ) < p₁ + ((q % 3 : ℕ) : ℝ) / 3 - p₁)]
      constructor <;> linarith [hr3.1, hr3.2]
    · rw [abs_of_neg (by linarith [hr0.2] : p₁ + ((q % 3 : ℕ) : ℝ) / 3 - 1 - p₁ < 0)]
      constructor <;> linarith [hr3.1, hr3.2]
  rcases unsafe_pair_abs hb1 hb2 with h | h
  · rw [abs_sub_comm] at h; linarith [hbnd.1]
  · rw [abs_sub_comm] at h; linarith [hbnd.2]

/-- For `3 ∤ d`, some shift among `t, t+1/3, t+2/3` is safe for runner `d`. -/
theorem exists_good_third {d : ℕ} (hd : ¬ 3 ∣ d) (t : ℝ) :
    ∃ l : ℕ, l < 3 ∧ safe6 d (t + (l : ℝ) / 3) := by
  rcases bad_third_le_one hd t (by norm_num) (by norm_num) (by norm_num : (0:ℕ) < 1) with h | h
  · exact ⟨0, by norm_num, h⟩
  · exact ⟨1, by norm_num, h⟩

/-- For two non-multiples of 3, the shifts where each is unsafe cover at most
one `l` each — so some `l ∈ {0,1,2}` is safe for both. -/
theorem exists_common_good_third {d e : ℕ} (hd : ¬ 3 ∣ d) (he : ¬ 3 ∣ e) (t : ℝ) :
    ∃ l : ℕ, l < 3 ∧ safe6 d (t + (l : ℝ) / 3) ∧ safe6 e (t + (l : ℝ) / 3) := by
  by_cases hd0 : safe6 d (t + ((0 : ℕ) : ℝ) / 3)
  · by_cases he0 : safe6 e (t + ((0 : ℕ) : ℝ) / 3)
    · exact ⟨0, by norm_num, hd0, he0⟩
    · -- `e` bad at 0 → good at 1 and 2; `d` good at one of {1,2}.
      rcases bad_third_le_one hd t (by norm_num) (by norm_num) (by norm_num : (1:ℕ) < 2) with h1 | h2
      · exact ⟨1, by norm_num, h1, Or.resolve_left
          (bad_third_le_one he t (by norm_num) (by norm_num) (by norm_num : (0:ℕ) < 1)) he0⟩
      · exact ⟨2, by norm_num, h2, Or.resolve_left
          (bad_third_le_one he t (by norm_num) (by norm_num) (by norm_num : (0:ℕ) < 2)) he0⟩
  · by_cases he0 : safe6 e (t + ((0 : ℕ) : ℝ) / 3)
    · rcases bad_third_le_one he t (by norm_num) (by norm_num) (by norm_num : (1:ℕ) < 2) with h1 | h2
      · exact ⟨1, by norm_num, Or.resolve_left
          (bad_third_le_one hd t (by norm_num) (by norm_num) (by norm_num : (0:ℕ) < 1)) hd0, h1⟩
      · exact ⟨2, by norm_num, Or.resolve_left
          (bad_third_le_one hd t (by norm_num) (by norm_num) (by norm_num : (0:ℕ) < 2)) hd0, h2⟩
    · -- both bad at 0 → both good at 1
      exact ⟨1, by norm_num,
        Or.resolve_left (bad_third_le_one hd t (by norm_num) (by norm_num)
          (by norm_num : (0:ℕ) < 1)) hd0,
        Or.resolve_left (bad_third_le_one he t (by norm_num) (by norm_num)
          (by norm_num : (0:ℕ) < 1)) he0⟩

/-- `circ ≥ 1/5` implies `safe6` (the fifth-gap arc sits inside the sixth-gap
arc): the bridge from `lrc5_int` (the `K = 4` seed) to `safe6`. -/
theorem safe6_of_circ_ge_fifth {d : ℕ} {t : ℝ}
    (h : (1 / 5 : ℝ) ≤ circ (t * (d : ℝ))) : safe6 d t := by
  rw [safe6]
  rw [mul_comm] at h
  have h' := (circ_ge_fifth_fract _).mp h
  rw [Set.mem_Icc] at h' ⊢
  constructor <;> linarith

/-- A multiple of 3 keeps the same position under `l/3`-shifts. -/
theorem safe6_third_shift_of_dvd {d : ℕ} (hd : 3 ∣ d) (t : ℝ) (l : ℕ) :
    safe6 d (t + (l : ℝ) / 3) ↔ safe6 d t := by
  obtain ⟨k, hk⟩ := hd
  have hk' : (d : ℝ) = 3 * (k : ℝ) := by exact_mod_cast hk
  have heq : (d : ℝ) * (t + (l : ℝ) / 3) =
      (d : ℝ) * t + ((k * l : ℤ) : ℝ) := by
    rw [hk']; push_cast; ring
  unfold safe6
  rw [heq, Int.fract_add_intCast]

/-- Renault's Lemma 2.3: exactly three multiples of 3 gives a safe time, so
`hfail` rules it out. -/
theorem lemma2_3 {D : Finset ℕ} (hpos : ∀ d ∈ D, 0 < d) (hcard : D.card ≤ 5)
    (hf : hfail D) (hm : (D.filter fun d => 3 ∣ d).card = 3) : False := by
  classical
  set S := D.filter fun d => 3 ∣ d with hS
  set R := D \ S with hR
  have hSsub : S ⊆ D := Finset.filter_subset _ _
  have hRcard : R.card ≤ 2 := by
    have := Finset.card_sdiff_add_card_eq_card hSsub
    rw [← hR] at this
    omega
  -- A time `t₀` where the three multiples of 3 are safe (lonely runner, K = 4).
  obtain ⟨t₀, -, ht₀⟩ := lrc5_int S
    (fun d hd => hpos d (hSsub hd)) (by omega : S.card ≤ 4)
  have ht₀' : ∀ d ∈ S, safe6 d t₀ :=
    fun d hd => safe6_of_circ_ge_fifth (ht₀ d hd)
  -- Multiples stay safe under `l/3` shifts; the ≤ 2 others get a common good `l`.
  obtain ⟨l, hl3, hgood⟩ : ∃ l : ℕ, l < 3 ∧
      ∀ d ∈ R, safe6 d (t₀ + (l : ℝ) / 3) := by
    interval_cases hRc : R.card
    · exact ⟨0, by norm_num, fun d hd =>
        absurd hd (by simp [Finset.card_eq_zero.mp hRc])⟩
    · obtain ⟨e, he⟩ := Finset.card_eq_one.mp hRc
      have heR : e ∈ R := by simp [he]
      have heD : e ∈ D := (Finset.mem_sdiff.mp heR).1
      have he3 : ¬ 3 ∣ e := by
        have := (Finset.mem_sdiff.mp heR).2
        simp only [hS, Finset.mem_filter, not_and] at this
        exact this heD
      obtain ⟨l, hl, hle⟩ := exists_good_third he3 t₀
      exact ⟨l, hl, fun d hd => by
        rw [he, Finset.mem_singleton] at hd; rwa [hd]⟩
    · obtain ⟨a, b, hab, hab'⟩ := Finset.card_eq_two.mp hRc
      have haR : a ∈ R := by simp [hab']
      have hbR : b ∈ R := by simp [hab']
      have h3_of : ∀ x ∈ R, ¬ 3 ∣ x := fun x hx => by
        have hxD : x ∈ D := (Finset.mem_sdiff.mp hx).1
        have := (Finset.mem_sdiff.mp hx).2
        simp only [hS, Finset.mem_filter, not_and] at this
        exact this hxD
      obtain ⟨l, hl, hla, hlb⟩ := exists_common_good_third (h3_of a haR) (h3_of b hbR) t₀
      exact ⟨l, hl, fun d hd => by
        rw [hab'] at hd
        rcases Finset.mem_insert.mp hd with rfl | hd2
        · exact hla
        · rw [Finset.mem_singleton] at hd2; rwa [hd2]⟩
  -- Every runner is safe at `t₀ + l/3`, contradicting `hfail`.
  obtain ⟨w, hwD, hwbad⟩ := hf (t₀ + (l : ℝ) / 3)
  have hmem : w ∈ S ∨ w ∈ R := by
    have : w ∈ S ∪ R := by
      rwa [Finset.union_sdiff_of_subset hSsub]
    exact Finset.mem_union.mp this
  rcases hmem with hwS | hwR
  · have h3 : 3 ∣ w := (Finset.mem_filter.mp hwS).2
    exact hwbad ((safe6_third_shift_of_dvd h3 t₀ l).mpr (ht₀' w hwS))
  · exact hwbad (hgood w hwR)

/-- Lemma 2.1, the `≤ 3` direction for `l = 3`: with `gcd = 1` and `hfail`,
at most three speeds are multiples of 3.  Four multiples stay safe under
`l/3`-shifts while the remaining runner finds a good shift. -/
theorem mult3_le_three {D : Finset ℕ} (hpos : ∀ d ∈ D, 0 < d) (hcard : D.card ≤ 5)
    (hgcd : D.gcd id = 1) (hf : hfail D) :
    (D.filter fun d => 3 ∣ d).card ≤ 3 := by
  classical
  by_contra hcon
  push Not at hcon
  set S := D.filter fun d => 3 ∣ d with hS
  have hSsub : S ⊆ D := Finset.filter_subset _ _
  obtain ⟨T, hTS, hTcard⟩ := Finset.le_card_iff_exists_subset_card.mp hcon
  -- `D \ T` has at most one element.
  have hTsub : T ⊆ D := fun x hx => hSsub (hTS hx)
  have hrest : (D \ T).card ≤ 1 := by
    have := Finset.card_sdiff_add_card_eq_card hTsub
    omega
  -- `T`'s four multiples are simultaneously safe at some `t₀`.
  obtain ⟨t₀, -, ht₀⟩ := lrc5_int T
    (fun d hd => hpos d (hTsub hd)) (by omega : T.card ≤ 4)
  have ht₀' : ∀ d ∈ T, safe6 d t₀ :=
    fun d hd => safe6_of_circ_ge_fifth (ht₀ d hd)
  -- If all of `D` is divisible by 3, `gcd ≥ 3` contradicts `hgcd`.
  have gcd_contra : (∀ d ∈ D, 3 ∣ d) → False := fun hall => by
    have hdg : 3 ∣ D.gcd id := Finset.dvd_gcd (fun d hd => hall d hd)
    rw [hgcd] at hdg
    exact absurd hdg (by norm_num)
  rcases Nat.eq_zero_or_pos (D \ T).card with h0 | hposR
  · -- `D \ T = ∅` gives `D = T`, all multiples of 3.
    have hDT : D \ T = ∅ := Finset.card_eq_zero.mp h0
    have hDeq : D = T := Finset.Subset.antisymm
      (Finset.sdiff_eq_empty_iff_subset.mp hDT) hTsub
    exact gcd_contra (fun d hd => (Finset.mem_filter.mp (hTS (hDeq ▸ hd))).2)
  · have h1 : (D \ T).card = 1 := by omega
    obtain ⟨i, hi⟩ := Finset.card_eq_one.mp h1
    have hiD : i ∈ D := by
      have : i ∈ D \ T := by simp [hi]
      exact (Finset.mem_sdiff.mp this).1
    by_cases h3i : 3 ∣ i
    · exact gcd_contra (fun d hd => by
        by_cases hdT : d ∈ T
        · exact (Finset.mem_filter.mp (hTS hdT)).2
        · have hdieq : d = i := by
            have : d ∈ D \ T := Finset.mem_sdiff.mpr ⟨hd, hdT⟩
            rwa [hi, Finset.mem_singleton] at this
          rwa [hdieq])
    · obtain ⟨l, hl, hli⟩ := exists_good_third h3i t₀
      obtain ⟨w, hwD, hwbad⟩ := hf (t₀ + (l : ℝ) / 3)
      by_cases hwT : w ∈ T
      · exact hwbad ((safe6_third_shift_of_dvd
          (Finset.mem_filter.mp (hTS hwT)).2 t₀ l).mpr (ht₀' w hwT))
      · have hwi : w = i := by
          have : w ∈ D \ T := Finset.mem_sdiff.mpr ⟨hwD, hwT⟩
          rwa [hi, Finset.mem_singleton] at this
        rw [hwi] at hwbad
        exact hwbad hli

/-- Renault's Lemma 2.2: if some speed `i` satisfies `i ≥ 5 j` for every other
speed, then a safe time exists — so under `hfail` every speed has some other
speed within a factor of 5.  The proof pushes runner `i` exactly onto `1/6`
while each other runner (in `[1/5,4/5]` by `K = 4`) drifts at most `1/30`. -/
theorem lemma2_2 {D : Finset ℕ} (hpos : ∀ d ∈ D, 0 < d) (hcard : D.card ≤ 5)
    (hf : hfail D) {i : ℕ} (hi : i ∈ D) :
    ∃ j ∈ D, j ≠ i ∧ i < 5 * j := by
  classical
  by_contra h
  push Not at h
  -- `h : ∀ j ∈ D, j ≠ i → 5 * j ≤ i`
  set R := D \ {i} with hR
  have hRcard : R.card ≤ 4 := by
    have hs : ({i} : Finset ℕ) ⊆ D := Finset.singleton_subset_iff.mpr hi
    have := Finset.card_sdiff_add_card_eq_card hs
    rw [Finset.card_singleton] at this
    rw [← hR] at this
    omega
  obtain ⟨t, -, ht⟩ := lrc5_int R
    (fun d hd => hpos d (Finset.mem_sdiff.mp hd).1) hRcard
  have ht' : ∀ d ∈ R, Int.fract ((d : ℝ) * t) ∈ Set.Icc (1 / 5) (4 / 5) :=
    fun d hd => by
      have hcd := (circ_ge_fifth_fract _).mp (ht d hd)
      rwa [mul_comm] at hcd
  have hipos : (0 : ℝ) < i := by exact_mod_cast hpos i hi
  -- Adjust the time so runner `i` sits in `[0, 1/6)`: use `t` or `−t`.
  by_cases hxsafe : safe6 i t
  · -- all runners already safe at `t`
    obtain ⟨w, hwD, hwbad⟩ := hf t
    by_cases hwi : w = i
    · rw [hwi] at hwbad; exact hwbad hxsafe
    · have hwR : w ∈ R := Finset.mem_sdiff.mpr ⟨hwD, by simp [hwi]⟩
      have := (ht' w hwR)
      rw [Set.mem_Icc] at this
      exact hwbad (by rw [safe6, Set.mem_Icc]; constructor <;> linarith)
  · -- `fract (i·t)` is in `[0,1/6) ∪ (5/6,1)`; pick `t' = t` or `−t`.
    rw [safe6, Set.mem_Icc] at hxsafe
    push Not at hxsafe
    have hxlt : Int.fract ((i : ℝ) * t) < 1 / 6 ∨ 5 / 6 < Int.fract ((i : ℝ) * t) := by
      rcases lt_or_ge (Int.fract ((i : ℝ) * t)) (1 / 6) with hlt | hge
      · exact Or.inl hlt
      · exact Or.inr (hxsafe hge)
    -- `t'` and its runner-data `x' ∈ [0,1/6)`, others still in `[1/5,4/5]`.
    obtain ⟨t', ht'', hx'⟩ : ∃ t' : ℝ,
        (∀ d ∈ R, Int.fract ((d : ℝ) * t') ∈ Set.Icc (1 / 5) (4 / 5)) ∧
        Int.fract ((i : ℝ) * t') ∈ Set.Ico 0 (1 / 6) := by
      rcases hxlt with hlo | hhi
      · exact ⟨t, ht', by
          rw [Set.mem_Ico]; exact ⟨Int.fract_nonneg _, hlo⟩⟩
      · refine ⟨-t, ?_, ?_⟩
        · intro d hd
          have h0 : Int.fract ((d : ℝ) * t) ≠ 0 := by
            have := (ht' d hd); rw [Set.mem_Icc] at this
            intro h0; linarith
          rw [mul_neg, Int.fract_neg h0]
          have := (ht' d hd); rw [Set.mem_Icc] at this
          rw [Set.mem_Icc]; constructor <;> linarith
        · have h0 : Int.fract ((i : ℝ) * t) ≠ 0 := by
            have h1 := Int.fract_nonneg ((i : ℝ) * t)
            intro h0; linarith
          rw [mul_neg, Int.fract_neg h0]
          have h1 := Int.fract_lt_one ((i : ℝ) * t)
          rw [Set.mem_Ico]; constructor <;> linarith
    -- The explicit push: `s = (1/6 − x')/i` lands runner `i` on `1/6`.
    set x' := Int.fract ((i : ℝ) * t') with hxdef
    set s := (1 / 6 - x') / (i : ℝ) with hs
    have hs0 : 0 ≤ s := by
      have : 0 ≤ 1 / 6 - x' := by
        have := hx'; rw [Set.mem_Ico] at this; linarith
      exact div_nonneg this (le_of_lt hipos)
    obtain ⟨w, hwD, hwbad⟩ := hf (t' + s)
    rw [safe6, Set.mem_Icc] at hwbad
    push Not at hwbad
    by_cases hwi : w = i
    · -- runner `i` lands exactly on `1/6`
      have hpos' : Int.fract ((i : ℝ) * (t' + s)) = 1 / 6 := by
        have hine : (i : ℝ) ≠ 0 := ne_of_gt hipos
        have hstep : (i : ℝ) * (t' + s) = 1 / 6 + ((i : ℝ) * t' - x') := by
          rw [hs]; field_simp; ring
        rw [hstep]
        have hint : (i : ℝ) * t' - x' = (⌊(i : ℝ) * t'⌋ : ℤ) := by
          rw [hxdef]; exact Int.self_sub_fract _
        rw [hint]
        exact (Int.fract_add_intCast _ _).trans
          (Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩)
      rw [hwi] at hwbad
      rw [hpos'] at hwbad
      exact absurd (hwbad (by norm_num)) (by norm_num)
    · have hwR : w ∈ R := Finset.mem_sdiff.mpr ⟨hwD, by simp [hwi]⟩
      have hw5 : 5 * w ≤ i := h w hwD hwi
      have hp := ht'' w hwR
      rw [Set.mem_Icc] at hp
      -- `w`'s drift `w·s ≤ 1/30`, so `p + w·s` stays in the safe arc.
      have hws : (w : ℝ) * s ≤ 1 / 30 := by
        have hine : (i : ℝ) ≠ 0 := ne_of_gt hipos
        have hw5' : (5 : ℝ) * w ≤ i := by exact_mod_cast hw5
        have hwi' : (w : ℝ) / i ≤ 1 / 5 := by
          rw [div_le_iff₀ hipos]; linarith
        have hxd : 0 ≤ 1 / 6 - x' := by
          have := hx'; rw [Set.mem_Ico] at this; linarith
        have hxd2 : 1 / 6 - x' ≤ 1 / 6 := by
          have := hx'; rw [Set.mem_Ico] at this; linarith
        calc (w : ℝ) * s = (w / i) * (1 / 6 - x') := by
              rw [hs]; field_simp
          _ ≤ (1 / 5) * (1 / 6) := by
              have h15 : (0 : ℝ) ≤ 1 / 5 := by norm_num
              exact mul_le_mul hwi' hxd2 hxd h15
          _ = 1 / 30 := by norm_num
      have hws0 : 0 ≤ (w : ℝ) * s := mul_nonneg (by positivity) hs0
      set p := Int.fract ((w : ℝ) * t') with hpdef
      have hstep : Int.fract ((w : ℝ) * (t' + s)) = p + (w : ℝ) * s := by
        have heq : (w : ℝ) * (t' + s) = p + (w : ℝ) * s +
            ((⌊(w : ℝ) * t'⌋ : ℤ) : ℝ) := by
          have h2 := Int.self_sub_fract ((w : ℝ) * t')
          rw [← hpdef] at h2
          linear_combination h2
        rw [heq, Int.fract_add_intCast]
        exact Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
      rw [hstep] at hwbad
      have hle : 1 / 6 ≤ p + (w : ℝ) * s := by linarith
      have hb := hwbad hle
      linarith

/-- Renault's Claim 2.4: every `x ∈ (1/6, 5/6)` is pushed out of the safe band
by some multiplier `λ ∈ {2,3,4,5}`.  Contrapositive form: if all four
`fract (λ·x)` stay in `[1/6,5/6]`, then `x ∉ (1/6,5/6)`.  The proof writes
`λx = ⌊λx⌋ + ⟨λx⟩`, giving `x ∈ [(k+1/6)/λ, (k+5/6)/λ]` for an integer `k`
in a bounded range; all integer combinations are then ruled out linearly. -/
theorem claim2_4 {x : ℝ} (hx : x ∈ Set.Ioo (1 / 6) (5 / 6)) :
    ∃ lam : ℕ, lam ∈ Finset.Icc 2 5 ∧
      Int.fract ((lam : ℝ) * x) ∉ Set.Icc (1 / 6) (5 / 6) := by
  rw [Set.mem_Ioo] at hx
  by_contra hcon
  push Not at hcon
  -- `hcon : ∀ lam ∈ Icc 2 5, fract (lam·x) ∈ Icc (1/6) (5/6)`
  have key : ∀ lam : ℕ, lam ∈ Finset.Icc 2 5 →
      ∃ k : ℤ, 0 ≤ k ∧ k ≤ (lam : ℤ) - 1 ∧
        (lam : ℝ) * x - k ∈ Set.Icc (1 / 6) (5 / 6) := by
    intro lam hlam
    have hmem := hcon lam hlam
    have hl2 : (2 : ℝ) ≤ lam := by
      have := (Finset.mem_Icc.mp hlam).1
      exact_mod_cast this
    have hpos : 0 < (lam : ℝ) * x :=
      mul_pos (by linarith) (by linarith)
    refine ⟨⌊(lam : ℝ) * x⌋, Int.floor_nonneg.mpr (le_of_lt hpos), ?_, ?_⟩
    · have hlt : ⌊(lam : ℝ) * x⌋ < (lam : ℤ) := by
        rw [Int.floor_lt]
        have h2 : (lam : ℝ) * x < lam := by nlinarith
        exact_mod_cast h2
      omega
    · have h2 := Int.self_sub_fract ((lam : ℝ) * x)
      have hfe : (lam : ℝ) * x - ⌊(lam : ℝ) * x⌋ =
          Int.fract ((lam : ℝ) * x) := by
        linear_combination h2
      rwa [hfe]
  obtain ⟨k2, hk2l, hk2u, hk2⟩ := key 2 (by decide)
  obtain ⟨k3, hk3l, hk3u, hk3⟩ := key 3 (by decide)
  obtain ⟨k4, hk4l, hk4u, hk4⟩ := key 4 (by decide)
  obtain ⟨k5, hk5l, hk5u, hk5⟩ := key 5 (by decide)
  rw [Set.mem_Icc] at hk2 hk3 hk4 hk5
  have hk2' : k2 ≤ 1 := by omega
  have hk3' : k3 ≤ 2 := by omega
  have hk4' : k4 ≤ 3 := by omega
  have hk5' : k5 ≤ 4 := by omega
  interval_cases k2 <;> interval_cases k3 <;> interval_cases k4 <;>
    interval_cases k5 <;> push_cast at hk2 hk3 hk4 hk5 ⊢ <;> linarith

end
