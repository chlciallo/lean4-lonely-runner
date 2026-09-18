/-
Copyright (c) 2026 Research07 contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Research07 contributors
-/
import Mathlib
import Research07.LRC6.Setup

/-!
# Renault Lemma 6.1 (combinatorial core, two-even case)

Renault's Lemma 6.1: for three positions `x₂, x₄, x₅ ∈ [0,1)`, either some
`(λ,α)` with `λ ∈ {2,…,5}`, `α ∈ {1,…,5}` puts `⟨λxᵢ + α/6⟩` (i = 4,5) and
`⟨λx₂ + 2α/6⟩` in `[1/6,5/6]`, or some `α ∈ {1,2,3,4}` puts them all in the open
`(1/6,5/6)`.  Runner 2 carries a doubled shift `2α/6` because `|e₂| = 2`.

Self-contained interval-covering lemma over `ℝ`/`Int.fract`.
-/

noncomputable section

/-! ## Helper lemmas -/

/-- `fract z = z - k` when `z ∈ [k, k+1)`. -/
theorem fract_eq_of_floor {z : ℝ} {k : ℤ} (h1 : (k : ℝ) ≤ z) (h2 : z < (k : ℝ) + 1) :
    Int.fract z = z - (k : ℝ) := by
  rw [Int.fract_eq_iff]
  refine ⟨by linarith, by linarith, k, ?_⟩
  ring

/-- `fract (k · fract y) = fract (k · y)` for `k : ℕ`. -/
theorem fract_mul_nat' (k : ℕ) (y : ℝ) :
    Int.fract ((k : ℝ) * Int.fract y) = Int.fract ((k : ℝ) * y) := by
  have h2 : (k : ℝ) * y = (k : ℝ) * Int.fract y + (((k : ℤ) * ⌊y⌋ : ℤ) : ℝ) := by
    have h3 := Int.self_sub_fract y
    push_cast
    linear_combination (k : ℝ) * h3
  rw [h2, Int.fract_add_intCast]

/-- `fract z = z - 1` when `z ∈ [1,2)`. -/
theorem fract_eq_sub_one {z : ℝ} (h1 : 1 ≤ z) (h2 : z < 2) :
    Int.fract z = z - 1 := by
  rw [Int.fract_eq_iff]
  refine ⟨by linarith, by linarith, 1, ?_⟩
  push_cast
  ring

/-- For `u ∈ [0,1)` and `s ∈ [1/6, 5/6]`, `fract (u+s)` misses the closed band
`[1/6,5/6]` iff `u` lies in the open arc `((5/6)-s, (7/6)-s)`. -/
theorem bad_Icc_iff {u s : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
    (hs0 : (1 : ℝ) / 6 ≤ s) (hs1 : s ≤ 5 / 6) :
    Int.fract (u + s) ∉ Set.Icc (1 / 6) (5 / 6) ↔
      u ∈ Set.Ioo (5 / 6 - s) (7 / 6 - s) := by
  by_cases h : u + s < 1
  · rw [Int.fract_eq_self.mpr ⟨by linarith, h⟩]
    constructor
    · intro hbad
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at hbad
      rcases hbad with hbad | hbad
      · linarith
      · exact ⟨by linarith, by linarith⟩
    · intro hmem
      rw [Set.mem_Icc, not_and_or, not_le, not_le]
      right
      linarith [hmem.1]
  · have h1 : Int.fract (u + s) = u + s - 1 :=
      fract_eq_sub_one (by linarith) (by linarith)
    rw [h1]
    constructor
    · intro hbad
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at hbad
      rcases hbad with hbad | hbad
      · exact ⟨by linarith, by linarith⟩
      · linarith
    · intro hmem
      rw [Set.mem_Icc, not_and_or, not_le, not_le]
      left
      linarith [hmem.2]

/-- For `u ∈ [0,1)` and `s ∈ [1/6, 5/6]`, `fract (u+s)` misses the open band
`(1/6,5/6)` iff `u` lies in the closed arc `[(5/6)-s, (7/6)-s]` (plus the
exceptional `u = 0, s = 1/6` boundary). -/
theorem bad_Ioo_iff {u s : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
    (hs0 : (1 : ℝ) / 6 ≤ s) (hs1 : s ≤ 5 / 6) :
    Int.fract (u + s) ∉ Set.Ioo (1 / 6) (5 / 6) ↔
      u ∈ Set.Icc (5 / 6 - s) (7 / 6 - s) ∨ (u = 0 ∧ s = 1 / 6) := by
  by_cases h : u + s < 1
  · rw [Int.fract_eq_self.mpr ⟨by linarith, h⟩]
    constructor
    · intro hbad
      rw [Set.mem_Ioo, not_and_or, not_lt, not_lt] at hbad
      rcases hbad with hbad | hbad
      · right
        exact ⟨by linarith, by linarith⟩
      · left
        exact ⟨by linarith, by linarith⟩
    · intro hmem
      rw [Set.mem_Ioo, not_and_or, not_lt, not_lt]
      rcases hmem with hmem | hmem
      · right
        linarith [hmem.1]
      · left
        linarith [hmem.1, hmem.2]
  · have h1 : Int.fract (u + s) = u + s - 1 :=
      fract_eq_sub_one (by linarith) (by linarith)
    rw [h1]
    constructor
    · intro hbad
      rw [Set.mem_Ioo, not_and_or, not_lt, not_lt] at hbad
      rcases hbad with hbad | hbad
      · left
        exact ⟨by linarith, by linarith⟩
      · linarith
    · intro hmem
      rw [Set.mem_Ioo, not_and_or, not_lt, not_lt]
      rcases hmem with hmem | hmem
      · left
        linarith [hmem.2]
      · left
        linarith [hmem.1, hmem.2]

/-- `fract z ∈ (1/6,5/6)` iff `z` lies in a unit-translate of the band. -/
theorem mem_Ioo_fract_iff {z : ℝ} :
    Int.fract z ∈ Set.Ioo (1 / 6) (5 / 6) ↔
      ∃ k : ℤ, z ∈ Set.Ioo ((k : ℝ) + 1 / 6) ((k : ℝ) + 5 / 6) := by
  constructor
  · intro h
    refine ⟨⌊z⌋, ?_, ?_⟩
    · have h1 := Int.self_sub_floor z
      have h2 := h.1
      linarith
    · have h1 := Int.self_sub_floor z
      have h2 := h.2
      linarith
  · rintro ⟨k, h1, h2⟩
    have hfr : Int.fract z = z - (k : ℝ) :=
      fract_eq_of_floor (k := k) (z := z) (by linarith) (by linarith)
    rw [hfr]
    exact ⟨by linarith, by linarith⟩

/-- `fract (2x)` for `x ∈ [0,1)` is `2x` or `2x - 1`. -/
theorem fract_two_mul {x : ℝ} (hx : x ∈ Set.Ico 0 1) :
    Int.fract (2 * x) = 2 * x ∨ Int.fract (2 * x) = 2 * x - 1 := by
  rcases lt_or_ge (2 * x) 1 with h | h
  · left
    exact Int.fract_eq_self.mpr ⟨by linarith [hx.1], h⟩
  · right
    exact fract_eq_sub_one h (by linarith [hx.2])

/-- Claim 2.4: every `u ∈ (1/6,5/6)` has a multiplier `λ ∈ {2,3,4,5}` pushing it
out of the open band. -/
theorem claim24 {u : ℝ} (hu : u ∈ Set.Ioo (1 / 6) (5 / 6)) :
    Int.fract (2 * u) ∉ Set.Ioo (1 / 6) (5 / 6) ∨
      Int.fract (3 * u) ∉ Set.Ioo (1 / 6) (5 / 6) ∨
        Int.fract (4 * u) ∉ Set.Ioo (1 / 6) (5 / 6) ∨
          Int.fract (5 * u) ∉ Set.Ioo (1 / 6) (5 / 6) := by
  by_contra hc
  push Not at hc
  obtain ⟨h2u, h3u, h4u, h5u⟩ := hc
  obtain ⟨k2, hk2⟩ := mem_Ioo_fract_iff.mp h2u
  obtain ⟨k3, hk3⟩ := mem_Ioo_fract_iff.mp h3u
  obtain ⟨k4, hk4⟩ := mem_Ioo_fract_iff.mp h4u
  obtain ⟨k5, hk5⟩ := mem_Ioo_fract_iff.mp h5u
  obtain ⟨hk2l, hk2r⟩ := hk2
  obtain ⟨hk3l, hk3r⟩ := hk3
  obtain ⟨hk4l, hk4r⟩ := hk4
  obtain ⟨hk5l, hk5r⟩ := hk5
  obtain ⟨hul, hur⟩ := hu
  -- bound the integers
  have hb2 : k2 = 0 ∨ k2 = 1 := by
    have e1 : k2 < 2 := by
      have : (k2 : ℝ) < 2 := by linarith
      exact_mod_cast this
    have e2 : -1 < k2 := by
      have : (-1 : ℝ) < k2 := by linarith
      exact_mod_cast this
    omega
  have hb3 : k3 = 0 ∨ k3 = 1 ∨ k3 = 2 := by
    have e1 : k3 < 3 := by
      have : (k3 : ℝ) < 3 := by linarith
      exact_mod_cast this
    have e2 : -1 < k3 := by
      have : (-1 : ℝ) < k3 := by linarith
      exact_mod_cast this
    omega
  have hb4 : k4 = 0 ∨ k4 = 1 ∨ k4 = 2 ∨ k4 = 3 := by
    have e1 : k4 < 4 := by
      have : (k4 : ℝ) < 4 := by linarith
      exact_mod_cast this
    have e2 : -1 < k4 := by
      have : (-1 : ℝ) < k4 := by linarith
      exact_mod_cast this
    omega
  have hb5 : k5 = 1 ∨ k5 = 2 ∨ k5 = 3 := by
    have e1 : k5 < 4 := by
      have : (k5 : ℝ) < 4 := by linarith
      exact_mod_cast this
    have e2 : 0 < k5 := by
      have : (0 : ℝ) < k5 := by linarith
      exact_mod_cast this
    omega
  rcases hb2 with rfl | rfl <;>
    rcases hb3 with rfl | rfl | rfl <;>
    rcases hb4 with rfl | rfl | rfl | rfl <;>
    rcases hb5 with rfl | rfl | rfl <;>
    linarith

/-- Step 1: if every `α ∈ {1,…,5}` is bad for `u`, `v` or `w` (with the
`J`-intervals for the single-shift runners and `K`-intervals for the doubled
runner), then `u` and `v` are `> 1/6` apart on the circle. -/
theorem step1 {u v w : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (hv0 : 0 ≤ v) (hv1 : v < 1)
    (_hw0 : 0 ≤ w) (hw1 : w < 1)
    (d1 : u ∈ Set.Ioo (2 / 3) 1 ∨ v ∈ Set.Ioo (2 / 3) 1 ∨ w ∈ Set.Ioo (1 / 2) (5 / 6))
    (d2 : u ∈ Set.Ioo (1 / 2) (5 / 6) ∨ v ∈ Set.Ioo (1 / 2) (5 / 6) ∨
      w ∈ Set.Ioo (1 / 6) (1 / 2))
    (d3 : u ∈ Set.Ioo (1 / 3) (2 / 3) ∨ v ∈ Set.Ioo (1 / 3) (2 / 3) ∨
      w ∉ Set.Icc (1 / 6) (5 / 6))
    (d4 : u ∈ Set.Ioo (1 / 6) (1 / 2) ∨ v ∈ Set.Ioo (1 / 6) (1 / 2) ∨
      w ∈ Set.Ioo (1 / 2) (5 / 6))
    (d5 : u ∈ Set.Ioo 0 (1 / 3) ∨ v ∈ Set.Ioo 0 (1 / 3) ∨ w ∈ Set.Ioo (1 / 6) (1 / 2)) :
    (1 / 6 : ℝ) < |u - v| ∧ |u - v| < 5 / 6 := by
  by_contra hc
  rw [not_and_or, not_lt, not_lt] at hc
  by_cases hwc : w ∈ Set.Ioo (1 / 2) (5 / 6)
  · -- `w ∈ (1/2,5/6)`: `d₂,d₃,d₅` reduce to `u,v` coverage of `J₂,J₃,J₅`
    have hwI : w ∈ Set.Icc (1 / 6) (5 / 6) := ⟨by linarith [hwc.1], by linarith [hwc.2]⟩
    have d2' : u ∈ Set.Ioo (1 / 2) (5 / 6) ∨ v ∈ Set.Ioo (1 / 2) (5 / 6) := by
      rcases d2 with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exfalso; linarith [h.2, hwc.1]
    have d3' : u ∈ Set.Ioo (1 / 3) (2 / 3) ∨ v ∈ Set.Ioo (1 / 3) (2 / 3) := by
      rcases d3 with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exfalso; exact h hwI
    have d5' : u ∈ Set.Ioo 0 (1 / 3) ∨ v ∈ Set.Ioo 0 (1 / 3) := by
      rcases d5 with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exfalso; linarith [h.2, hwc.1]
    rcases d5' with h5 | h5
    · -- `u ∈ (0,1/3)`, so `v` covers `J₃∩J₂ = (1/2,2/3)`
      have hv2 : v ∈ Set.Ioo (1 / 2) (5 / 6) := by
        rcases d2' with h | h
        · exfalso; linarith [h.1, h5.2]
        · exact h
      have hv3 : v ∈ Set.Ioo (1 / 3) (2 / 3) := by
        rcases d3' with h | h
        · exfalso; linarith [h.1, h5.2]
        · exact h
      have hneg : u - v < 0 := by linarith [h5.2, hv2.1]
      rw [abs_of_neg hneg] at hc
      rcases hc with hc | hc
      · linarith [hv2.1, h5.2]
      · linarith [hv3.2, h5.1]
    · -- `v ∈ (0,1/3)`, so `u` covers `J₃∩J₂`
      have hu2 : u ∈ Set.Ioo (1 / 2) (5 / 6) := by
        rcases d2' with h | h
        · exact h
        · exfalso; linarith [h.1, h5.2]
      have hu3 : u ∈ Set.Ioo (1 / 3) (2 / 3) := by
        rcases d3' with h | h
        · exact h
        · exfalso; linarith [h.1, h5.2]
      have hpos : 0 < u - v := by linarith [hu2.1, h5.2]
      rw [abs_of_pos hpos] at hc
      rcases hc with hc | hc
      · linarith [hu2.1, h5.2]
      · linarith [hu3.2, h5.1]
  · by_cases hwc2 : w ∈ Set.Ioo (1 / 6) (1 / 2)
    · -- `w ∈ (1/6,1/2)`: `d₁,d₃,d₄` reduce to `u,v` coverage of `J₁,J₃,J₄`
      have hwI : w ∈ Set.Icc (1 / 6) (5 / 6) := ⟨by linarith [hwc2.1], by linarith [hwc2.2]⟩
      have d1' : u ∈ Set.Ioo (2 / 3) 1 ∨ v ∈ Set.Ioo (2 / 3) 1 := by
        rcases d1 with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · exfalso; linarith [h.1, hwc2.2]
      have d3' : u ∈ Set.Ioo (1 / 3) (2 / 3) ∨ v ∈ Set.Ioo (1 / 3) (2 / 3) := by
        rcases d3 with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · exfalso; exact h hwI
      have d4' : u ∈ Set.Ioo (1 / 6) (1 / 2) ∨ v ∈ Set.Ioo (1 / 6) (1 / 2) := by
        rcases d4 with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · exfalso; linarith [h.1, hwc2.2]
      rcases d1' with h1 | h1
      · -- `u ∈ (2/3,1)`, so `v` covers `J₃∩J₄ = (1/3,1/2)`
        have hv3 : v ∈ Set.Ioo (1 / 3) (2 / 3) := by
          rcases d3' with h | h
          · exfalso; linarith [h.2, h1.1]
          · exact h
        have hv4 : v ∈ Set.Ioo (1 / 6) (1 / 2) := by
          rcases d4' with h | h
          · exfalso; linarith [h.2, h1.1]
          · exact h
        have hpos : 0 < u - v := by linarith [h1.1, hv3.2]
        rw [abs_of_pos hpos] at hc
        rcases hc with hc | hc
        · linarith [h1.1, hv4.2]
        · linarith [h1.2, hv4.1]
      · -- `v ∈ (2/3,1)`, so `u` covers `J₃∩J₄`
        have hu3 : u ∈ Set.Ioo (1 / 3) (2 / 3) := by
          rcases d3' with h | h
          · exact h
          · exfalso; linarith [h.2, h1.1]
        have hu4 : u ∈ Set.Ioo (1 / 6) (1 / 2) := by
          rcases d4' with h | h
          · exact h
          · exfalso; linarith [h.2, h1.1]
        have hneg : u - v < 0 := by linarith [h1.1, hu3.2]
        rw [abs_of_neg hneg] at hc
        rcases hc with hc | hc
        · linarith [h1.1, hu4.2]
        · linarith [h1.2, hu4.1]
    · by_cases hw3 : w < 1 / 6 ∨ 5 / 6 < w
      · -- `w` in the wrap arc: `d₁,d₂,d₄,d₅` reduce to `u,v` covering `J₁,J₂,J₄,J₅`
        have d1' : u ∈ Set.Ioo (2 / 3) 1 ∨ v ∈ Set.Ioo (2 / 3) 1 := by
          rcases d1 with h | h | h
          · exact Or.inl h
          · exact Or.inr h
          · exfalso
            rcases hw3 with hw3 | hw3
            · linarith [h.1, hw3]
            · linarith [h.2, hw3]
        have d2' : u ∈ Set.Ioo (1 / 2) (5 / 6) ∨ v ∈ Set.Ioo (1 / 2) (5 / 6) := by
          rcases d2 with h | h | h
          · exact Or.inl h
          · exact Or.inr h
          · exfalso
            rcases hw3 with hw3 | hw3
            · linarith [h.1, hw3]
            · linarith [h.2, hw3]
        have d4' : u ∈ Set.Ioo (1 / 6) (1 / 2) ∨ v ∈ Set.Ioo (1 / 6) (1 / 2) := by
          rcases d4 with h | h | h
          · exact Or.inl h
          · exact Or.inr h
          · exfalso
            rcases hw3 with hw3 | hw3
            · linarith [h.1, hw3]
            · linarith [h.2, hw3]
        have d5' : u ∈ Set.Ioo 0 (1 / 3) ∨ v ∈ Set.Ioo 0 (1 / 3) := by
          rcases d5 with h | h | h
          · exact Or.inl h
          · exact Or.inr h
          · exfalso
            rcases hw3 with hw3 | hw3
            · linarith [h.1, hw3]
            · linarith [h.2, hw3]
        -- the `J₅`-point must also cover `J₄`, the `J₁`-point `J₂`
        rcases d5' with h5 | h5
        · rcases d1' with h1 | h1
          · exfalso; linarith [h1.1, h5.2]
          · have hu4 : u ∈ Set.Ioo (1 / 6) (1 / 2) := by
              rcases d4' with h | h
              · exact h
              · exfalso; linarith [h.2, h1.1]
            have hv2 : v ∈ Set.Ioo (1 / 2) (5 / 6) := by
              rcases d2' with h | h
              · exfalso; linarith [h.1, h5.2]
              · exact h
            have hneg : u - v < 0 := by linarith [h5.2, h1.1]
            rw [abs_of_neg hneg] at hc
            rcases hc with hc | hc
            · linarith [h1.1, hu4.2]
            · linarith [hv2.2, hu4.1]
        · rcases d1' with h1 | h1
          · have hv4 : v ∈ Set.Ioo (1 / 6) (1 / 2) := by
              rcases d4' with h | h
              · exfalso; linarith [h.2, h1.1]
              · exact h
            have hu2 : u ∈ Set.Ioo (1 / 2) (5 / 6) := by
              rcases d2' with h | h
              · exact h
              · exfalso; linarith [h.1, h5.2]
            have hpos : 0 < u - v := by linarith [h1.1, h5.2]
            rw [abs_of_pos hpos] at hc
            rcases hc with hc | hc
            · linarith [h1.1, hv4.2]
            · linarith [hu2.2, hv4.1]
          · exfalso; linarith [h1.1, h5.2]
      · -- `w ∈ {1/6,1/2,5/6}`: all five `d`'s reduce to `u,v`; `J₃` is uncovered
        have hwI : w ∈ Set.Icc (1 / 6) (5 / 6) := by
          push Not at hw3
          exact hw3
        have d1' : u ∈ Set.Ioo (2 / 3) 1 ∨ v ∈ Set.Ioo (2 / 3) 1 := by
          rcases d1 with h | h | h
          · exact Or.inl h
          · exact Or.inr h
          · exfalso; exact hwc h
        have d2' : u ∈ Set.Ioo (1 / 2) (5 / 6) ∨ v ∈ Set.Ioo (1 / 2) (5 / 6) := by
          rcases d2 with h | h | h
          · exact Or.inl h
          · exact Or.inr h
          · exfalso; exact hwc2 h
        have d3' : u ∈ Set.Ioo (1 / 3) (2 / 3) ∨ v ∈ Set.Ioo (1 / 3) (2 / 3) := by
          rcases d3 with h | h | h
          · exact Or.inl h
          · exact Or.inr h
          · exfalso; exact h hwI
        have d4' : u ∈ Set.Ioo (1 / 6) (1 / 2) ∨ v ∈ Set.Ioo (1 / 6) (1 / 2) := by
          rcases d4 with h | h | h
          · exact Or.inl h
          · exact Or.inr h
          · exfalso; exact hwc h
        have d5' : u ∈ Set.Ioo 0 (1 / 3) ∨ v ∈ Set.Ioo 0 (1 / 3) := by
          rcases d5 with h | h | h
          · exact Or.inl h
          · exact Or.inr h
          · exfalso; exact hwc2 h
        rcases d5' with h5 | h5
        · rcases d1' with h1 | h1
          · exfalso; linarith [h1.1, h5.2]
          · rcases d3' with h3 | h3
            · exfalso; linarith [h3.1, h5.2]
            · exfalso; linarith [h3.2, h1.1]
        · rcases d1' with h1 | h1
          · rcases d3' with h3 | h3
            · exfalso; linarith [h3.2, h1.1]
            · exfalso; linarith [h3.1, h5.2]
          · exfalso; linarith [h1.1, h5.2]

/-- Step 2 (`λ = 2`): the same covering hypotheses, together with
`|u − v| ∈ (1/6,1/3) ∪ (2/3,5/6)`, force one of the two four-consecutive-`α`
configurations of Renault's Lemma 6.1 (with either role assignment). -/
theorem step2 {u v w : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (hv0 : 0 ≤ v) (hv1 : v < 1)
    (_hw0 : 0 ≤ w) (hw1 : w < 1)
    (hd : ((1 / 6 : ℝ) < |u - v| ∧ |u - v| < 1 / 3) ∨
      (2 / 3 < |u - v| ∧ |u - v| < 5 / 6))
    (d1 : u ∈ Set.Ioo (2 / 3) 1 ∨ v ∈ Set.Ioo (2 / 3) 1 ∨ w ∈ Set.Ioo (1 / 2) (5 / 6))
    (d2 : u ∈ Set.Ioo (1 / 2) (5 / 6) ∨ v ∈ Set.Ioo (1 / 2) (5 / 6) ∨
      w ∈ Set.Ioo (1 / 6) (1 / 2))
    (d3 : u ∈ Set.Ioo (1 / 3) (2 / 3) ∨ v ∈ Set.Ioo (1 / 3) (2 / 3) ∨
      w ∉ Set.Icc (1 / 6) (5 / 6))
    (d4 : u ∈ Set.Ioo (1 / 6) (1 / 2) ∨ v ∈ Set.Ioo (1 / 6) (1 / 2) ∨
      w ∈ Set.Ioo (1 / 2) (5 / 6))
    (d5 : u ∈ Set.Ioo 0 (1 / 3) ∨ v ∈ Set.Ioo 0 (1 / 3) ∨ w ∈ Set.Ioo (1 / 6) (1 / 2)) :
    (w ∈ Set.Ioo (1 / 6) (1 / 2) ∧
        ((u ∈ Set.Ioo (2 / 3) (5 / 6) ∧ v ∈ Set.Ioo (1 / 3) (1 / 2)) ∨
          (v ∈ Set.Ioo (2 / 3) (5 / 6) ∧ u ∈ Set.Ioo (1 / 3) (1 / 2))))
      ∨ (w ∈ Set.Ioo (1 / 2) (5 / 6) ∧
        ((u ∈ Set.Ioo (1 / 2) (2 / 3) ∧ v ∈ Set.Ioo (1 / 6) (1 / 3)) ∨
          (v ∈ Set.Ioo (1 / 2) (2 / 3) ∧ u ∈ Set.Ioo (1 / 6) (1 / 3)))) := by
  by_cases hwc : w ∈ Set.Ioo (1 / 2) (5 / 6)
  · -- Case B: `w ∈ (1/2,5/6)`
    have hwI : w ∈ Set.Icc (1 / 6) (5 / 6) := ⟨by linarith [hwc.1], by linarith [hwc.2]⟩
    have d2' : u ∈ Set.Ioo (1 / 2) (5 / 6) ∨ v ∈ Set.Ioo (1 / 2) (5 / 6) := by
      rcases d2 with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exfalso; linarith [h.2, hwc.1]
    have d3' : u ∈ Set.Ioo (1 / 3) (2 / 3) ∨ v ∈ Set.Ioo (1 / 3) (2 / 3) := by
      rcases d3 with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exfalso; exact h hwI
    have d5' : u ∈ Set.Ioo 0 (1 / 3) ∨ v ∈ Set.Ioo 0 (1 / 3) := by
      rcases d5 with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exfalso; linarith [h.2, hwc.1]
    rcases d5' with h5 | h5
    · -- `u ∈ J₅`; `v` covers `J₃∩J₂ = (1/2,2/3)`; need `u ∈ (1/6,1/3)`
      have hv2 : v ∈ Set.Ioo (1 / 2) (5 / 6) := by
        rcases d2' with h | h
        · exfalso; linarith [h.1, h5.2]
        · exact h
      have hv3 : v ∈ Set.Ioo (1 / 3) (2 / 3) := by
        rcases d3' with h | h
        · exfalso; linarith [h.1, h5.2]
        · exact h
      by_cases hu4 : u ∈ Set.Ioo (1 / 6) (1 / 2)
      · right
        exact ⟨hwc, Or.inr ⟨⟨hv2.1, hv3.2⟩, ⟨hu4.1, h5.2⟩⟩⟩
      · -- `u ≤ 1/6`: then `v - u ∈ (1/3,2/3)`, contradicting `hd`
        rw [Set.mem_Ioo, not_and_or, not_lt, not_lt] at hu4
        have hu6 : u ≤ 1 / 6 := by
          rcases hu4 with h | h
          · exact h
          · linarith [h5.2, h]
        have hneg : u - v < 0 := by linarith [h5.2, hv2.1]
        rw [abs_of_neg hneg] at hd
        rcases hd with ⟨hd1, hd2⟩ | ⟨hd1, hd2⟩
        · linarith [hv2.1, hu6]
        · linarith [hv3.2, h5.1]
    · -- `v ∈ J₅`; `u` covers `J₃∩J₂`; need `v ∈ (1/6,1/3)`
      have hu2 : u ∈ Set.Ioo (1 / 2) (5 / 6) := by
        rcases d2' with h | h
        · exact h
        · exfalso; linarith [h.1, h5.2]
      have hu3 : u ∈ Set.Ioo (1 / 3) (2 / 3) := by
        rcases d3' with h | h
        · exact h
        · exfalso; linarith [h.1, h5.2]
      by_cases hv4 : v ∈ Set.Ioo (1 / 6) (1 / 2)
      · right
        exact ⟨hwc, Or.inl ⟨⟨hu2.1, hu3.2⟩, ⟨hv4.1, h5.2⟩⟩⟩
      · rw [Set.mem_Ioo, not_and_or, not_lt, not_lt] at hv4
        have hv6 : v ≤ 1 / 6 := by
          rcases hv4 with h | h
          · exact h
          · linarith [h5.2, h]
        have hpos : 0 < u - v := by linarith [hu2.1, h5.2]
        rw [abs_of_pos hpos] at hd
        rcases hd with ⟨hd1, hd2⟩ | ⟨hd1, hd2⟩
        · linarith [hu2.1, hv6]
        · linarith [hu3.2, h5.1]
  · by_cases hwc2 : w ∈ Set.Ioo (1 / 6) (1 / 2)
    · -- Case A: `w ∈ (1/6,1/2)`
      have hwI : w ∈ Set.Icc (1 / 6) (5 / 6) := ⟨by linarith [hwc2.1], by linarith [hwc2.2]⟩
      have d1' : u ∈ Set.Ioo (2 / 3) 1 ∨ v ∈ Set.Ioo (2 / 3) 1 := by
        rcases d1 with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · exfalso; linarith [h.1, hwc2.2]
      have d3' : u ∈ Set.Ioo (1 / 3) (2 / 3) ∨ v ∈ Set.Ioo (1 / 3) (2 / 3) := by
        rcases d3 with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · exfalso; exact h hwI
      have d4' : u ∈ Set.Ioo (1 / 6) (1 / 2) ∨ v ∈ Set.Ioo (1 / 6) (1 / 2) := by
        rcases d4 with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · exfalso; linarith [h.1, hwc2.2]
      rcases d1' with h1 | h1
      · -- `u ∈ J₁`; `v` covers `J₃∩J₄`; need `u < 5/6`
        have hv3 : v ∈ Set.Ioo (1 / 3) (2 / 3) := by
          rcases d3' with h | h
          · exfalso; linarith [h.2, h1.1]
          · exact h
        have hv4 : v ∈ Set.Ioo (1 / 6) (1 / 2) := by
          rcases d4' with h | h
          · exfalso; linarith [h.2, h1.1]
          · exact h
        by_cases hu2 : u ∈ Set.Ioo (2 / 3) (5 / 6)
        · left
          exact ⟨hwc2, Or.inl ⟨hu2, ⟨hv3.1, hv4.2⟩⟩⟩
        · -- `u ≥ 5/6`: `u - v ∈ (1/3,2/3)`, contradicting `hd`
          rw [Set.mem_Ioo, not_and_or, not_lt, not_lt] at hu2
          have hu56 : 5 / 6 ≤ u := by
            rcases hu2 with h | h
            · linarith [h1.1, h]
            · exact h
          have hpos : 0 < u - v := by linarith [h1.1, hv3.2]
          rw [abs_of_pos hpos] at hd
          rcases hd with ⟨hd1, hd2⟩ | ⟨hd1, hd2⟩
          · linarith [hu56, hv4.2]
          · linarith [h1.2, hv3.1]
      · -- `v ∈ J₁`; `u` covers `J₃∩J₄`; need `v < 5/6`
        have hu3 : u ∈ Set.Ioo (1 / 3) (2 / 3) := by
          rcases d3' with h | h
          · exact h
          · exfalso; linarith [h.2, h1.1]
        have hu4 : u ∈ Set.Ioo (1 / 6) (1 / 2) := by
          rcases d4' with h | h
          · exact h
          · exfalso; linarith [h.2, h1.1]
        by_cases hv2 : v ∈ Set.Ioo (2 / 3) (5 / 6)
        · left
          exact ⟨hwc2, Or.inr ⟨hv2, ⟨hu3.1, hu4.2⟩⟩⟩
        · rw [Set.mem_Ioo, not_and_or, not_lt, not_lt] at hv2
          have hv56 : 5 / 6 ≤ v := by
            rcases hv2 with h | h
            · linarith [h1.1, h]
            · exact h
          have hneg : u - v < 0 := by linarith [h1.1, hu3.2]
          rw [abs_of_neg hneg] at hd
          rcases hd with ⟨hd1, hd2⟩ | ⟨hd1, hd2⟩
          · linarith [hv56, hu4.2]
          · linarith [h1.2, hu3.1]
    · -- `w` in wrap arc or on boundaries: impossible (as in `step1`)
      by_cases hw3 : w < 1 / 6 ∨ 5 / 6 < w
      · have d1' : u ∈ Set.Ioo (2 / 3) 1 ∨ v ∈ Set.Ioo (2 / 3) 1 := by
          rcases d1 with h | h | h
          · exact Or.inl h
          · exact Or.inr h
          · exfalso
            rcases hw3 with hw3 | hw3
            · linarith [h.1, hw3]
            · linarith [h.2, hw3]
        have d2' : u ∈ Set.Ioo (1 / 2) (5 / 6) ∨ v ∈ Set.Ioo (1 / 2) (5 / 6) := by
          rcases d2 with h | h | h
          · exact Or.inl h
          · exact Or.inr h
          · exfalso
            rcases hw3 with hw3 | hw3
            · linarith [h.1, hw3]
            · linarith [h.2, hw3]
        have d4' : u ∈ Set.Ioo (1 / 6) (1 / 2) ∨ v ∈ Set.Ioo (1 / 6) (1 / 2) := by
          rcases d4 with h | h | h
          · exact Or.inl h
          · exact Or.inr h
          · exfalso
            rcases hw3 with hw3 | hw3
            · linarith [h.1, hw3]
            · linarith [h.2, hw3]
        have d5' : u ∈ Set.Ioo 0 (1 / 3) ∨ v ∈ Set.Ioo 0 (1 / 3) := by
          rcases d5 with h | h | h
          · exact Or.inl h
          · exact Or.inr h
          · exfalso
            rcases hw3 with hw3 | hw3
            · linarith [h.1, hw3]
            · linarith [h.2, hw3]
        rcases d5' with h5 | h5
        · rcases d1' with h1 | h1
          · exfalso; linarith [h1.1, h5.2]
          · have hu4 : u ∈ Set.Ioo (1 / 6) (1 / 2) := by
              rcases d4' with h | h
              · exact h
              · exfalso; linarith [h.2, h1.1]
            have hv2 : v ∈ Set.Ioo (1 / 2) (5 / 6) := by
              rcases d2' with h | h
              · exfalso; linarith [h.1, h5.2]
              · exact h
            have hneg : u - v < 0 := by linarith [h5.2, h1.1]
            rw [abs_of_neg hneg] at hd
            rcases hd with hd | hd
            · linarith [h1.1, h5.2]
            · linarith [hv2.2, hu4.1]
        · rcases d1' with h1 | h1
          · have hv4 : v ∈ Set.Ioo (1 / 6) (1 / 2) := by
              rcases d4' with h | h
              · exfalso; linarith [h.2, h1.1]
              · exact h
            have hu2 : u ∈ Set.Ioo (1 / 2) (5 / 6) := by
              rcases d2' with h | h
              · exact h
              · exfalso; linarith [h.1, h5.2]
            have hpos : 0 < u - v := by linarith [h1.1, h5.2]
            rw [abs_of_pos hpos] at hd
            rcases hd with hd | hd
            · linarith [h1.1, h5.2]
            · linarith [hu2.2, hv4.1]
          · exfalso; linarith [h1.1, h5.2]
      · have hwI : w ∈ Set.Icc (1 / 6) (5 / 6) := by
          push Not at hw3
          exact hw3
        have d1' : u ∈ Set.Ioo (2 / 3) 1 ∨ v ∈ Set.Ioo (2 / 3) 1 := by
          rcases d1 with h | h | h
          · exact Or.inl h
          · exact Or.inr h
          · exfalso; exact hwc h
        have d2' : u ∈ Set.Ioo (1 / 2) (5 / 6) ∨ v ∈ Set.Ioo (1 / 2) (5 / 6) := by
          rcases d2 with h | h | h
          · exact Or.inl h
          · exact Or.inr h
          · exfalso; exact hwc2 h
        have d3' : u ∈ Set.Ioo (1 / 3) (2 / 3) ∨ v ∈ Set.Ioo (1 / 3) (2 / 3) := by
          rcases d3 with h | h | h
          · exact Or.inl h
          · exact Or.inr h
          · exfalso; exact h hwI
        have d4' : u ∈ Set.Ioo (1 / 6) (1 / 2) ∨ v ∈ Set.Ioo (1 / 6) (1 / 2) := by
          rcases d4 with h | h | h
          · exact Or.inl h
          · exact Or.inr h
          · exfalso; exact hwc h
        have d5' : u ∈ Set.Ioo 0 (1 / 3) ∨ v ∈ Set.Ioo 0 (1 / 3) := by
          rcases d5 with h | h | h
          · exact Or.inl h
          · exact Or.inr h
          · exfalso; exact hwc2 h
        rcases d5' with h5 | h5
        · rcases d1' with h1 | h1
          · exfalso; linarith [h1.1, h5.2]
          · rcases d3' with h3 | h3
            · exfalso; linarith [h3.1, h5.2]
            · exfalso; linarith [h3.2, h1.1]
        · rcases d1' with h1 | h1
          · rcases d3' with h3 | h3
            · exfalso; linarith [h3.2, h1.1]
            · exfalso; linarith [h3.1, h5.2]
          · exfalso; linarith [h1.1, h5.2]

/-- For `d ∈ (−1,1)`, `fract d` is `|d|` or `1 − |d|`. -/
theorem fract_abs_cases {d : ℝ} (hd0 : -1 < d) (hd1 : d < 1) :
    Int.fract d = |d| ∨ Int.fract d = 1 - |d| := by
  rcases lt_or_ge d 0 with h | h
  · right
    rw [abs_of_neg h]
    have e : Int.fract d = d + 1 := by
      rw [Int.fract_eq_iff]
      refine ⟨by linarith, by linarith, -1, ?_⟩
      push_cast
      ring
    rw [e]
    ring
  · left
    rw [abs_of_nonneg h]
    exact Int.fract_eq_self.mpr ⟨h, hd1⟩

/-- If `|d| ∈ (1/6,5/6)` then `fract d ∈ (1/6,5/6)` (the band is symmetric). -/
theorem fract_mem_Ioo_of_abs {d : ℝ} (hd0 : -1 < d) (hd1 : d < 1)
    (h : (1 / 6 : ℝ) < |d| ∧ |d| < 5 / 6) : Int.fract d ∈ Set.Ioo (1 / 6) (5 / 6) := by
  obtain ⟨h1, h2⟩ := h
  rcases fract_abs_cases hd0 hd1 with e | e <;> rw [e]
  · exact ⟨h1, h2⟩
  · exact ⟨by linarith, by linarith⟩

/-- If `fract d` lies in the symmetric pair `(1/6,1/3) ∪ (2/3,5/6)`, so does
`|d|`. -/
theorem abs_mem_of_fract {d : ℝ} (hd0 : -1 < d) (hd1 : d < 1)
    (h : Int.fract d ∈ Set.Ioo (1 / 6) (1 / 3) ∨ Int.fract d ∈ Set.Ioo (2 / 3) (5 / 6)) :
    ((1 / 6 : ℝ) < |d| ∧ |d| < 1 / 3) ∨ (2 / 3 < |d| ∧ |d| < 5 / 6) := by
  rcases fract_abs_cases hd0 hd1 with e | e <;> rw [e] at h
  · exact h
  · rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inr ⟨by linarith, by linarith⟩
    · exact Or.inl ⟨by linarith, by linarith⟩

/-- `fract (fract (λx) − fract (λy)) = fract (λ(x−y))`. -/
theorem fract_sub_fract (lam : ℕ) (x y : ℝ) :
    Int.fract (Int.fract ((lam : ℝ) * x) - Int.fract ((lam : ℝ) * y)) =
      Int.fract ((lam : ℝ) * (x - y)) := by
  have e : Int.fract ((lam : ℝ) * x) - Int.fract ((lam : ℝ) * y) =
      (lam : ℝ) * (x - y) - (((⌊(lam : ℝ) * x⌋ - ⌊(lam : ℝ) * y⌋ : ℤ)) : ℝ) := by
    have h1 := Int.self_sub_fract ((lam : ℝ) * x)
    have h2 := Int.self_sub_fract ((lam : ℝ) * y)
    push_cast
    linear_combination h2 - h1
  rw [e, Int.fract_sub_intCast]

/-- Halving: `fract (2x) ∈ Ioo a b` pulls back to two half-intervals. -/
theorem fract_two_mul_Ioo {x : ℝ} (hx : x ∈ Set.Ico 0 1) {a b : ℝ}
    (h : Int.fract (2 * x) ∈ Set.Ioo a b) :
    x ∈ Set.Ioo (a / 2) (b / 2) ∨ x ∈ Set.Ioo ((a + 1) / 2) ((b + 1) / 2) := by
  rcases fract_two_mul hx with e | e <;> rw [e] at h
  · exact Or.inl ⟨by linarith [h.1], by linarith [h.2]⟩
  · exact Or.inr ⟨by linarith [h.1], by linarith [h.2]⟩

/-- `fract z ∈ Ioo(1/6,5/6)` when `z` lies strictly inside a translated band
`(k+1/6, k+5/6)`.  The real bounds `a b` are what linarith-friendly hypotheses
look like; `ha hb` tie them to the integer translate. -/
theorem mem_Ioo_fract' {z : ℝ} (a b : ℝ) (k : ℤ)
    (ha : a = (k : ℝ) + 1 / 6) (hb : b = (k : ℝ) + 5 / 6)
    (h1 : a < z) (h2 : z < b) : Int.fract z ∈ Set.Ioo (1 / 6) (5 / 6) := by
  have e : Int.fract z = z - (k : ℝ) :=
    fract_eq_of_floor (k := k) (by linarith) (by linarith)
  rw [e]
  exact ⟨by linarith, by linarith⟩

/-- Closed-band version of `mem_Ioo_fract'`. -/
theorem mem_Icc_fract' {z : ℝ} (a b : ℝ) (k : ℤ)
    (ha : a = (k : ℝ) + 1 / 6) (hb : b = (k : ℝ) + 5 / 6)
    (h1 : a ≤ z) (h2 : z ≤ b) : Int.fract z ∈ Set.Icc (1 / 6) (5 / 6) := by
  have e : Int.fract z = z - (k : ℝ) :=
    fract_eq_of_floor (k := k) (by linarith) (by linarith)
  rw [e]
  exact ⟨by linarith, by linarith⟩

/-- Convert a badness disjunct `fract (λx + s) ∉ Icc` (with `s ∈ [1/6,5/6]`)
into the `J`-interval `fract (λx) ∈ Ioo a b`. -/
theorem d_of_bad {lam : ℕ} {x : ℝ} (s a b : ℝ)
    (hs0 : (1 : ℝ) / 6 ≤ s) (hs1 : s ≤ 5 / 6)
    (ha : 5 / 6 - s = a) (hb : 7 / 6 - s = b)
    (e : Int.fract ((lam : ℝ) * x + s) ∉ Set.Icc (1 / 6) (5 / 6)) :
    Int.fract ((lam : ℝ) * x) ∈ Set.Ioo a b := by
  rw [fract_self_add] at e
  rw [bad_Icc_iff (Int.fract_nonneg _) (Int.fract_lt_one _) hs0 hs1, ha, hb] at e
  exact e

/-- Same conversion when the shift `s = 1 + s'` wraps around the circle. -/
theorem d_of_bad_sub {lam : ℕ} {x : ℝ} (s s' a b : ℝ)
    (hs : s = 1 + s') (hs0 : (1 : ℝ) / 6 ≤ s') (hs1 : s' ≤ 5 / 6)
    (ha : 5 / 6 - s' = a) (hb : 7 / 6 - s' = b)
    (e : Int.fract ((lam : ℝ) * x + s) ∉ Set.Icc (1 / 6) (5 / 6)) :
    Int.fract ((lam : ℝ) * x) ∈ Set.Ioo a b := by
  rw [fract_self_add, hs] at e
  rw [show Int.fract ((lam : ℝ) * x) + (1 + s') =
      (Int.fract ((lam : ℝ) * x) + s') + ((1 : ℤ) : ℝ) by push_cast; ring,
    Int.fract_add_intCast] at e
  rw [bad_Icc_iff (Int.fract_nonneg _) (Int.fract_lt_one _) hs0 hs1, ha, hb] at e
  exact e

/-- The degenerate case `s = 1`: `fract (λx + 1) = fract (λx)` directly. -/
theorem d_of_bad_one {lam : ℕ} {x : ℝ} (s : ℝ) (hs : s = 1)
    (e : Int.fract ((lam : ℝ) * x + s) ∉ Set.Icc (1 / 6) (5 / 6)) :
    Int.fract ((lam : ℝ) * x) ∉ Set.Icc (1 / 6) (5 / 6) := by
  rw [fract_self_add, hs] at e
  rwa [show Int.fract ((lam : ℝ) * x) + 1 =
      Int.fract ((lam : ℝ) * x) + ((1 : ℤ) : ℝ) by push_cast; ring,
    Int.fract_add_intCast,
    Int.fract_eq_self.mpr ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩] at e

/-- For a fixed multiplier `λ`, the failure of option (1) at each `α ∈ {1,…,5}`
gives the five covering disjunctions `d₁,…,d₅` of `step1`/`step2`. -/
theorem dlist {x₂ x₄ x₅ : ℝ} (lam : ℕ)
    (bad : ∀ al : ℕ, 1 ≤ al → al ≤ 5 →
      Int.fract ((lam : ℝ) * x₄ + (al : ℝ) / 6) ∉ Set.Icc (1 / 6) (5 / 6) ∨
        Int.fract ((lam : ℝ) * x₅ + (al : ℝ) / 6) ∉ Set.Icc (1 / 6) (5 / 6) ∨
          Int.fract ((lam : ℝ) * x₂ + 2 * (al : ℝ) / 6) ∉ Set.Icc (1 / 6) (5 / 6)) :
    (Int.fract ((lam : ℝ) * x₄) ∈ Set.Ioo (2 / 3) 1 ∨
        Int.fract ((lam : ℝ) * x₅) ∈ Set.Ioo (2 / 3) 1 ∨
          Int.fract ((lam : ℝ) * x₂) ∈ Set.Ioo (1 / 2) (5 / 6)) ∧
      (Int.fract ((lam : ℝ) * x₄) ∈ Set.Ioo (1 / 2) (5 / 6) ∨
          Int.fract ((lam : ℝ) * x₅) ∈ Set.Ioo (1 / 2) (5 / 6) ∨
            Int.fract ((lam : ℝ) * x₂) ∈ Set.Ioo (1 / 6) (1 / 2)) ∧
        (Int.fract ((lam : ℝ) * x₄) ∈ Set.Ioo (1 / 3) (2 / 3) ∨
            Int.fract ((lam : ℝ) * x₅) ∈ Set.Ioo (1 / 3) (2 / 3) ∨
              Int.fract ((lam : ℝ) * x₂) ∉ Set.Icc (1 / 6) (5 / 6)) ∧
          (Int.fract ((lam : ℝ) * x₄) ∈ Set.Ioo (1 / 6) (1 / 2) ∨
              Int.fract ((lam : ℝ) * x₅) ∈ Set.Ioo (1 / 6) (1 / 2) ∨
                Int.fract ((lam : ℝ) * x₂) ∈ Set.Ioo (1 / 2) (5 / 6)) ∧
            (Int.fract ((lam : ℝ) * x₄) ∈ Set.Ioo 0 (1 / 3) ∨
                Int.fract ((lam : ℝ) * x₅) ∈ Set.Ioo 0 (1 / 3) ∨
                  Int.fract ((lam : ℝ) * x₂) ∈ Set.Ioo (1 / 6) (1 / 2)) := by
  have d1 : Int.fract ((lam : ℝ) * x₄) ∈ Set.Ioo (2 / 3) 1 ∨
      Int.fract ((lam : ℝ) * x₅) ∈ Set.Ioo (2 / 3) 1 ∨
        Int.fract ((lam : ℝ) * x₂) ∈ Set.Ioo (1 / 2) (5 / 6) := by
    rcases bad 1 le_rfl (by norm_num) with e | e | e
    · exact Or.inl (d_of_bad (((1 : ℕ) : ℝ) / 6) (2 / 3) 1
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) e)
    · exact Or.inr (Or.inl (d_of_bad (((1 : ℕ) : ℝ) / 6) (2 / 3) 1
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) e))
    · exact Or.inr (Or.inr (d_of_bad (2 * ((1 : ℕ) : ℝ) / 6) (1 / 2) (5 / 6)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) e))
  have d2 : Int.fract ((lam : ℝ) * x₄) ∈ Set.Ioo (1 / 2) (5 / 6) ∨
      Int.fract ((lam : ℝ) * x₅) ∈ Set.Ioo (1 / 2) (5 / 6) ∨
        Int.fract ((lam : ℝ) * x₂) ∈ Set.Ioo (1 / 6) (1 / 2) := by
    rcases bad 2 (by norm_num) (by norm_num) with e | e | e
    · exact Or.inl (d_of_bad (((2 : ℕ) : ℝ) / 6) (1 / 2) (5 / 6)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) e)
    · exact Or.inr (Or.inl (d_of_bad (((2 : ℕ) : ℝ) / 6) (1 / 2) (5 / 6)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) e))
    · exact Or.inr (Or.inr (d_of_bad (2 * ((2 : ℕ) : ℝ) / 6) (1 / 6) (1 / 2)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) e))
  have d3 : Int.fract ((lam : ℝ) * x₄) ∈ Set.Ioo (1 / 3) (2 / 3) ∨
      Int.fract ((lam : ℝ) * x₅) ∈ Set.Ioo (1 / 3) (2 / 3) ∨
        Int.fract ((lam : ℝ) * x₂) ∉ Set.Icc (1 / 6) (5 / 6) := by
    rcases bad 3 (by norm_num) (by norm_num) with e | e | e
    · exact Or.inl (d_of_bad (((3 : ℕ) : ℝ) / 6) (1 / 3) (2 / 3)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) e)
    · exact Or.inr (Or.inl (d_of_bad (((3 : ℕ) : ℝ) / 6) (1 / 3) (2 / 3)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) e))
    · exact Or.inr (Or.inr (d_of_bad_one (2 * ((3 : ℕ) : ℝ) / 6) (by norm_num) e))
  have d4 : Int.fract ((lam : ℝ) * x₄) ∈ Set.Ioo (1 / 6) (1 / 2) ∨
      Int.fract ((lam : ℝ) * x₅) ∈ Set.Ioo (1 / 6) (1 / 2) ∨
        Int.fract ((lam : ℝ) * x₂) ∈ Set.Ioo (1 / 2) (5 / 6) := by
    rcases bad 4 (by norm_num) (by norm_num) with e | e | e
    · exact Or.inl (d_of_bad (((4 : ℕ) : ℝ) / 6) (1 / 6) (1 / 2)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) e)
    · exact Or.inr (Or.inl (d_of_bad (((4 : ℕ) : ℝ) / 6) (1 / 6) (1 / 2)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) e))
    · exact Or.inr (Or.inr (d_of_bad_sub (2 * ((4 : ℕ) : ℝ) / 6) (2 / 6) (1 / 2) (5 / 6)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) e))
  have d5 : Int.fract ((lam : ℝ) * x₄) ∈ Set.Ioo 0 (1 / 3) ∨
      Int.fract ((lam : ℝ) * x₅) ∈ Set.Ioo 0 (1 / 3) ∨
        Int.fract ((lam : ℝ) * x₂) ∈ Set.Ioo (1 / 6) (1 / 2) := by
    rcases bad 5 (by norm_num) (by norm_num) with e | e | e
    · exact Or.inl (d_of_bad (((5 : ℕ) : ℝ) / 6) 0 (1 / 3)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) e)
    · exact Or.inr (Or.inl (d_of_bad (((5 : ℕ) : ℝ) / 6) 0 (1 / 3)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) e))
    · exact Or.inr (Or.inr (d_of_bad_sub (2 * ((5 : ℕ) : ℝ) / 6) (4 / 6) (1 / 6) (1 / 2)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) e))
  exact ⟨d1, d2, d3, d4, d5⟩

/-- `step1` instantiated: under option-(1) failure, every `λ ∈ {2,…,5}` puts the
two positions `> 1/6` apart on the circle. -/
theorem step1_pre {x₂ x₄ x₅ : ℝ} (lam : ℕ)
    (bad : ∀ al : ℕ, 1 ≤ al → al ≤ 5 →
      Int.fract ((lam : ℝ) * x₄ + (al : ℝ) / 6) ∉ Set.Icc (1 / 6) (5 / 6) ∨
        Int.fract ((lam : ℝ) * x₅ + (al : ℝ) / 6) ∉ Set.Icc (1 / 6) (5 / 6) ∨
          Int.fract ((lam : ℝ) * x₂ + 2 * (al : ℝ) / 6) ∉ Set.Icc (1 / 6) (5 / 6)) :
    (1 / 6 : ℝ) < |Int.fract ((lam : ℝ) * x₄) - Int.fract ((lam : ℝ) * x₅)| ∧
      |Int.fract ((lam : ℝ) * x₄) - Int.fract ((lam : ℝ) * x₅)| < 5 / 6 := by
  obtain ⟨d1, d2, d3, d4, d5⟩ := dlist lam bad
  exact step1 (Int.fract_nonneg _) (Int.fract_lt_one _) (Int.fract_nonneg _)
    (Int.fract_lt_one _) (Int.fract_nonneg _) (Int.fract_lt_one _) d1 d2 d3 d4 d5

/-- `δ = fract (x₄−x₅)` lies in `(1/12,1/6) ∪ (5/6,11/12)`: the endpoints are
killed by the `λ = 5` fact. -/
theorem delta_range {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (h2f : Int.fract (2 * δ) ∈ Set.Ioo (1 / 6) (5 / 6))
    (h5f : Int.fract (5 * δ) ∈ Set.Ioo (1 / 6) (5 / 6))
    (hδ : δ ∉ Set.Ioo (1 / 6) (5 / 6)) :
    (1 / 12 < δ ∧ δ < 1 / 6) ∨ (5 / 6 < δ ∧ δ < 11 / 12) := by
  rw [Set.mem_Ioo, not_and_or, not_lt, not_lt] at hδ
  obtain ⟨h2l, h2u⟩ := h2f
  obtain ⟨h5l, h5u⟩ := h5f
  rcases hδ with hδ | hδ
  · left
    have e2 : Int.fract (2 * δ) = 2 * δ := Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
    refine ⟨by linarith [e2 ▸ h2l], ?_⟩
    by_contra hlt
    push Not at hlt
    have hδe : δ = 1 / 6 := le_antisymm hδ hlt
    have e5 : Int.fract (5 * δ) = 5 * δ := Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
    linarith [e5 ▸ h5u, hδe]
  · right
    have e2 : Int.fract (2 * δ) = 2 * δ - 1 := fract_eq_sub_one (by linarith) (by linarith)
    refine ⟨?_, by linarith [e2 ▸ h2u]⟩
    by_contra hgt
    push Not at hgt
    have hδe : δ = 5 / 6 := le_antisymm hgt hδ
    have e5 : Int.fract (5 * δ) = 5 * δ - ((4 : ℤ) : ℝ) :=
      fract_eq_of_floor (k := 4) (by push_cast; linarith) (by push_cast; linarith)
    push_cast at e5
    linarith [e5 ▸ h5l, hδe]

/-- `|x−y|` inherits the `(1/12,1/6) ∪ (5/6,11/12)` range from `fract (x−y)`. -/
theorem abs_diff_range {x y : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (hy0 : 0 ≤ y) (hy1 : y < 1)
    (h : (1 / 12 < Int.fract (x - y) ∧ Int.fract (x - y) < 1 / 6) ∨
      (5 / 6 < Int.fract (x - y) ∧ Int.fract (x - y) < 11 / 12)) :
    (1 / 12 < |x - y| ∧ |x - y| < 1 / 6) ∨ (5 / 6 < |x - y| ∧ |x - y| < 11 / 12) := by
  rcases fract_abs_cases (d := x - y) (by linarith) (by linarith) with e | e <;> rw [e] at h
  · exact h
  · rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inr ⟨by linarith, by linarith⟩
    · exact Or.inl ⟨by linarith, by linarith⟩

/-- From the `δ` range, `fract (2δ)` lies in `(1/6,1/3) ∪ (2/3,5/6)`. -/
theorem fract_two_delta {δ : ℝ}
    (h : (1 / 12 < δ ∧ δ < 1 / 6) ∨ (5 / 6 < δ ∧ δ < 11 / 12)) :
    Int.fract (2 * δ) ∈ Set.Ioo (1 / 6) (1 / 3) ∨ Int.fract (2 * δ) ∈ Set.Ioo (2 / 3) (5 / 6) := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left
    have e : Int.fract (2 * δ) = 2 * δ := Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
    rw [e]
    exact ⟨by linarith, by linarith⟩
  · right
    have e : Int.fract (2 * δ) = 2 * δ - 1 := fract_eq_sub_one (by linarith) (by linarith)
    rw [e]
    exact ⟨by linarith, by linarith⟩

/-- Case A tail: `⟨2x₂⟩ ∈ (1/6,1/2)`, `⟨2xu⟩ ∈ (2/3,5/6)` and `⟨2xv⟩ ∈ (1/3,1/2)`
(up to swapping `u ↔ v`): every sub-configuration yields an option-(2) witness,
contradiction. -/
theorem caseA {xu xv x₂ : ℝ} (hxu0 : 0 ≤ xu) (hxu1 : xu < 1) (hxv0 : 0 ≤ xv)
    (hxv1 : xv < 1) (hx₂0 : 0 ≤ x₂) (hx₂1 : x₂ < 1)
    (hadiff : (1 / 12 < |xu - xv| ∧ |xu - xv| < 1 / 6) ∨
      (5 / 6 < |xu - xv| ∧ |xu - xv| < 11 / 12))
    (hu : Int.fract (2 * xu) ∈ Set.Ioo (2 / 3) (5 / 6))
    (hv : Int.fract (2 * xv) ∈ Set.Ioo (1 / 3) (1 / 2))
    (hw : Int.fract (2 * x₂) ∈ Set.Ioo (1 / 6) (1 / 2))
    (wit : ∀ al : ℕ, (al = 1 ∨ al = 2 ∨ al = 3 ∨ al = 4) →
      Int.fract (xu + (al : ℝ) / 6) ∈ Set.Ioo (1 / 6) (5 / 6) →
        Int.fract (xv + (al : ℝ) / 6) ∈ Set.Ioo (1 / 6) (5 / 6) →
          Int.fract (x₂ + 2 * (al : ℝ) / 6) ∈ Set.Ioo (1 / 6) (5 / 6) → False) : False := by
  rcases fract_two_mul_Ioo (Set.mem_Ico.mpr ⟨hxv0, hxv1⟩) hv with ⟨hxvl, hxvu⟩ | ⟨hxvl, hxvu⟩
  · -- `xv ∈ (1/6,1/4)`: forces `xu ∈ (1/3,5/12)`
    rcases fract_two_mul_Ioo (Set.mem_Ico.mpr ⟨hxu0, hxu1⟩) hu with ⟨hxul, hxuu⟩ | ⟨hxul, hxuu⟩
    · -- `xu ∈ (1/3,5/12)`: consistent pair
      rcases fract_two_mul_Ioo (Set.mem_Ico.mpr ⟨hx₂0, hx₂1⟩) hw with ⟨hx₂l, hx₂u⟩ | ⟨hx₂l, hx₂u⟩
      · -- `x₂ ∈ (1/12,1/4)`: `α = 1` witness
        exact wit 1 (Or.inl rfl)
          (mem_Ioo_fract' (1 / 6) (5 / 6) 0 (by norm_num) (by norm_num)
            (by push_cast; linarith) (by push_cast; linarith))
          (mem_Ioo_fract' (1 / 6) (5 / 6) 0 (by norm_num) (by norm_num)
            (by push_cast; linarith) (by push_cast; linarith))
          (mem_Ioo_fract' (1 / 6) (5 / 6) 0 (by norm_num) (by norm_num)
            (by push_cast; linarith) (by push_cast; linarith))
      · -- `x₂ ∈ (7/12,3/4)`: `α = 2` witness
        exact wit 2 (Or.inr (Or.inl rfl))
          (mem_Ioo_fract' (1 / 6) (5 / 6) 0 (by norm_num) (by norm_num)
            (by push_cast; linarith) (by push_cast; linarith))
          (mem_Ioo_fract' (1 / 6) (5 / 6) 0 (by norm_num) (by norm_num)
            (by push_cast; linarith) (by push_cast; linarith))
          (mem_Ioo_fract' (7 / 6) (11 / 6) 1 (by norm_num) (by norm_num)
            (by push_cast; linarith) (by push_cast; linarith))
    · -- `xu ∈ (5/6,11/12)`: `|xu−xv| ∈ (7/12,3/4)`, contradicting `hadiff`
      exfalso
      rcases hadiff with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hpos : 0 < xu - xv := by linarith
        rw [abs_of_pos hpos] at h1 h2
        linarith
      · have hpos : 0 < xu - xv := by linarith
        rw [abs_of_pos hpos] at h1 h2
        linarith
  · -- `xv ∈ (2/3,3/4)`: forces `xu ∈ (5/6,11/12)`
    rcases fract_two_mul_Ioo (Set.mem_Ico.mpr ⟨hxu0, hxu1⟩) hu with ⟨hxul, hxuu⟩ | ⟨hxul, hxuu⟩
    · -- `xu ∈ (1/3,5/12)`: `|xu−xv| ∈ (1/4,5/12)`, contradicting `hadiff`
      exfalso
      rcases hadiff with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hneg : xu - xv < 0 := by linarith
        rw [abs_of_neg hneg] at h1 h2
        linarith
      · have hneg : xu - xv < 0 := by linarith
        rw [abs_of_neg hneg] at h1 h2
        linarith
    · -- `xu ∈ (5/6,11/12)`: consistent pair
      rcases fract_two_mul_Ioo (Set.mem_Ico.mpr ⟨hx₂0, hx₂1⟩) hw with ⟨hx₂l, hx₂u⟩ | ⟨hx₂l, hx₂u⟩
      · -- `x₂ ∈ (1/12,1/4)`: `α = 4` witness
        exact wit 4 (Or.inr (Or.inr (Or.inr rfl)))
          (mem_Ioo_fract' (7 / 6) (11 / 6) 1 (by norm_num) (by norm_num)
            (by push_cast; linarith) (by push_cast; linarith))
          (mem_Ioo_fract' (7 / 6) (11 / 6) 1 (by norm_num) (by norm_num)
            (by push_cast; linarith) (by push_cast; linarith))
          (mem_Ioo_fract' (7 / 6) (11 / 6) 1 (by norm_num) (by norm_num)
            (by push_cast; linarith) (by push_cast; linarith))
      · -- `x₂ ∈ (7/12,3/4)`: `α = 3` witness
        exact wit 3 (Or.inr (Or.inr (Or.inl rfl)))
          (mem_Ioo_fract' (7 / 6) (11 / 6) 1 (by norm_num) (by norm_num)
            (by push_cast; linarith) (by push_cast; linarith))
          (mem_Ioo_fract' (7 / 6) (11 / 6) 1 (by norm_num) (by norm_num)
            (by push_cast; linarith) (by push_cast; linarith))
          (mem_Ioo_fract' (7 / 6) (11 / 6) 1 (by norm_num) (by norm_num)
            (by push_cast; linarith) (by push_cast; linarith))

/-- Case B tail: `⟨2x₂⟩ ∈ (1/2,5/6)`, `⟨2xu⟩ ∈ (1/2,2/3)` and `⟨2xv⟩ ∈ (1/6,1/3)`
(up to swapping `u ↔ v`): every sub-configuration yields an option-(2) witness,
except the last one, which yields the `λ = 4, α = 1` option-(1) witness. -/
theorem caseB {xu xv x₂ : ℝ} (hxu0 : 0 ≤ xu) (hxu1 : xu < 1) (hxv0 : 0 ≤ xv)
    (hxv1 : xv < 1) (hx₂0 : 0 ≤ x₂) (hx₂1 : x₂ < 1)
    (hadiff : (1 / 12 < |xu - xv| ∧ |xu - xv| < 1 / 6) ∨
      (5 / 6 < |xu - xv| ∧ |xu - xv| < 11 / 12))
    (hu : Int.fract (2 * xu) ∈ Set.Ioo (1 / 2) (2 / 3))
    (hv : Int.fract (2 * xv) ∈ Set.Ioo (1 / 6) (1 / 3))
    (hw : Int.fract (2 * x₂) ∈ Set.Ioo (1 / 2) (5 / 6))
    (wit : ∀ al : ℕ, (al = 1 ∨ al = 2 ∨ al = 3 ∨ al = 4) →
      Int.fract (xu + (al : ℝ) / 6) ∈ Set.Ioo (1 / 6) (5 / 6) →
        Int.fract (xv + (al : ℝ) / 6) ∈ Set.Ioo (1 / 6) (5 / 6) →
          Int.fract (x₂ + 2 * (al : ℝ) / 6) ∈ Set.Ioo (1 / 6) (5 / 6) → False)
    (wic : ∀ lam al : ℕ, 2 ≤ lam → lam ≤ 5 → 1 ≤ al → al ≤ 5 →
      Int.fract ((lam : ℝ) * xu + (al : ℝ) / 6) ∈ Set.Icc (1 / 6) (5 / 6) →
        Int.fract ((lam : ℝ) * xv + (al : ℝ) / 6) ∈ Set.Icc (1 / 6) (5 / 6) →
          Int.fract ((lam : ℝ) * x₂ + 2 * (al : ℝ) / 6) ∈ Set.Icc (1 / 6) (5 / 6) →
            False) : False := by
  rcases fract_two_mul_Ioo (Set.mem_Ico.mpr ⟨hxu0, hxu1⟩) hu with ⟨hxul, hxuu⟩ | ⟨hxul, hxuu⟩
  · -- `xu ∈ (1/4,1/3)`: forces `xv ∈ (1/12,1/6)`
    rcases fract_two_mul_Ioo (Set.mem_Ico.mpr ⟨hxv0, hxv1⟩) hv with ⟨hxvl, hxvu⟩ | ⟨hxvl, hxvu⟩
    · -- `xv ∈ (1/12,1/6)`: consistent pair
      rcases fract_two_mul_Ioo (Set.mem_Ico.mpr ⟨hx₂0, hx₂1⟩) hw with ⟨hx₂l, hx₂u⟩ | ⟨hx₂l, hx₂u⟩
      · -- `x₂ ∈ (1/4,5/12)`: `α = 3` witness
        exact wit 3 (Or.inr (Or.inr (Or.inl rfl)))
          (mem_Ioo_fract' (1 / 6) (5 / 6) 0 (by norm_num) (by norm_num)
            (by push_cast; linarith) (by push_cast; linarith))
          (mem_Ioo_fract' (1 / 6) (5 / 6) 0 (by norm_num) (by norm_num)
            (by push_cast; linarith) (by push_cast; linarith))
          (mem_Ioo_fract' (7 / 6) (11 / 6) 1 (by norm_num) (by norm_num)
            (by push_cast; linarith) (by push_cast; linarith))
      · -- `x₂ ∈ (3/4,11/12)`: `α = 2` witness
        exact wit 2 (Or.inr (Or.inl rfl))
          (mem_Ioo_fract' (1 / 6) (5 / 6) 0 (by norm_num) (by norm_num)
            (by push_cast; linarith) (by push_cast; linarith))
          (mem_Ioo_fract' (1 / 6) (5 / 6) 0 (by norm_num) (by norm_num)
            (by push_cast; linarith) (by push_cast; linarith))
          (mem_Ioo_fract' (7 / 6) (11 / 6) 1 (by norm_num) (by norm_num)
            (by push_cast; linarith) (by push_cast; linarith))
    · -- `xv ∈ (7/12,2/3)`: `|xu−xv| ∈ (1/4,5/12)`, contradicting `hadiff`
      exfalso
      rcases hadiff with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hneg : xu - xv < 0 := by linarith
        rw [abs_of_neg hneg] at h1 h2
        linarith
      · have hneg : xu - xv < 0 := by linarith
        rw [abs_of_neg hneg] at h1 h2
        linarith
  · -- `xu ∈ (3/4,5/6)`: forces `xv ∈ (7/12,2/3)`
    rcases fract_two_mul_Ioo (Set.mem_Ico.mpr ⟨hxv0, hxv1⟩) hv with ⟨hxvl, hxvu⟩ | ⟨hxvl, hxvu⟩
    · -- `xv ∈ (1/12,1/6)`: `|xu−xv| ∈ (7/12,3/4)`, contradicting `hadiff`
      exfalso
      rcases hadiff with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hpos : 0 < xu - xv := by linarith
        rw [abs_of_pos hpos] at h1 h2
        linarith
      · have hpos : 0 < xu - xv := by linarith
        rw [abs_of_pos hpos] at h1 h2
        linarith
    · -- `xv ∈ (7/12,2/3)`: `α = 4` squeeze, then `λ = 4, α = 1` finish
      have m4 : Int.fract (xu + ((4 : ℕ) : ℝ) / 6) ∈ Set.Ioo (1 / 6) (5 / 6) :=
        mem_Ioo_fract' (7 / 6) (11 / 6) 1 (by norm_num) (by norm_num)
          (by push_cast; linarith) (by push_cast; linarith)
      have m5 : Int.fract (xv + ((4 : ℕ) : ℝ) / 6) ∈ Set.Ioo (1 / 6) (5 / 6) :=
        mem_Ioo_fract' (7 / 6) (11 / 6) 1 (by norm_num) (by norm_num)
          (by push_cast; linarith) (by push_cast; linarith)
      have hα4 : Int.fract (x₂ + 2 * ((4 : ℕ) : ℝ) / 6) ∉ Set.Ioo (1 / 6) (5 / 6) :=
        fun h => wit 4 (Or.inr (Or.inr (Or.inr rfl))) m4 m5 h
      rcases fract_two_mul_Ioo (Set.mem_Ico.mpr ⟨hx₂0, hx₂1⟩) hw with ⟨hx₂l, hx₂u⟩ | ⟨hx₂l, hx₂u⟩
      · -- `x₂ ∈ (1/4,5/12)`: `⟨x₂ + 4/3⟩ ∈ (7/12,3/4) ⊆ Ioo` — contradiction
        exact absurd
          (mem_Ioo_fract' (7 / 6) (11 / 6) 1 (by norm_num) (by norm_num)
            (by push_cast; linarith) (by push_cast; linarith)) hα4
      · -- `x₂ ∈ (3/4,11/12)`: `hα4` forces `x₂ ≤ 5/6`
        have e : Int.fract (x₂ + 2 * ((4 : ℕ) : ℝ) / 6) = x₂ - 2 / 3 := by
          have h := fract_eq_of_floor (k := 2) (z := x₂ + 2 * ((4 : ℕ) : ℝ) / 6)
            (by push_cast; linarith) (by push_cast; linarith)
          push_cast at h
          push_cast
          linarith [h]
        rw [e, Set.mem_Ioo, not_and_or, not_lt, not_lt] at hα4
        have hx₂u' : x₂ ≤ 5 / 6 := by
          rcases hα4 with g | g
          · linarith
          · linarith
        exact wic 4 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          (mem_Icc_fract' (19 / 6) (23 / 6) 3 (by norm_num) (by norm_num)
            (by push_cast; linarith) (by push_cast; linarith))
          (mem_Icc_fract' (13 / 6) (17 / 6) 2 (by norm_num) (by norm_num)
            (by push_cast; linarith) (by push_cast; linarith))
          (mem_Icc_fract' (19 / 6) (23 / 6) 3 (by norm_num) (by norm_num)
            (by push_cast; linarith) (by push_cast; linarith))

/-- Renault Lemma 6.1. -/
theorem lemma6_1 {x₂ x₄ x₅ : ℝ}
    (h2 : x₂ ∈ Set.Ico 0 1) (h4 : x₄ ∈ Set.Ico 0 1) (h5 : x₅ ∈ Set.Ico 0 1) :
    (∃ lam al : ℕ, 2 ≤ lam ∧ lam ≤ 5 ∧ 1 ≤ al ∧ al ≤ 5 ∧
        Int.fract ((lam : ℝ) * x₄ + (al : ℝ) / 6) ∈ Set.Icc (1 / 6) (5 / 6) ∧
        Int.fract ((lam : ℝ) * x₅ + (al : ℝ) / 6) ∈ Set.Icc (1 / 6) (5 / 6) ∧
        Int.fract ((lam : ℝ) * x₂ + 2 * (al : ℝ) / 6) ∈ Set.Icc (1 / 6) (5 / 6))
    ∨
    (∃ al : ℕ, (al = 1 ∨ al = 2 ∨ al = 3 ∨ al = 4) ∧
        Int.fract (x₄ + (al : ℝ) / 6) ∈ Set.Ioo (1 / 6) (5 / 6) ∧
        Int.fract (x₅ + (al : ℝ) / 6) ∈ Set.Ioo (1 / 6) (5 / 6) ∧
        Int.fract (x₂ + 2 * (al : ℝ) / 6) ∈ Set.Ioo (1 / 6) (5 / 6)) := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hc1, hc2⟩ := hcon
  obtain ⟨hx₂0, hx₂1⟩ := h2
  obtain ⟨hx₄0, hx₄1⟩ := h4
  obtain ⟨hx₅0, hx₅1⟩ := h5
  have wit : ∀ al : ℕ, (al = 1 ∨ al = 2 ∨ al = 3 ∨ al = 4) →
      Int.fract (x₄ + (al : ℝ) / 6) ∈ Set.Ioo (1 / 6) (5 / 6) →
        Int.fract (x₅ + (al : ℝ) / 6) ∈ Set.Ioo (1 / 6) (5 / 6) →
          Int.fract (x₂ + 2 * (al : ℝ) / 6) ∈ Set.Ioo (1 / 6) (5 / 6) → False :=
    fun al spec m4 m5 m2 => hc2 ⟨al, spec, m4, m5, m2⟩
  have wic : ∀ lam al : ℕ, 2 ≤ lam → lam ≤ 5 → 1 ≤ al → al ≤ 5 →
      Int.fract ((lam : ℝ) * x₄ + (al : ℝ) / 6) ∈ Set.Icc (1 / 6) (5 / 6) →
        Int.fract ((lam : ℝ) * x₅ + (al : ℝ) / 6) ∈ Set.Icc (1 / 6) (5 / 6) →
          Int.fract ((lam : ℝ) * x₂ + 2 * (al : ℝ) / 6) ∈ Set.Icc (1 / 6) (5 / 6) → False :=
    fun lam al hl1 hl2 ha1 ha2 m4 m5 m2 => hc1 ⟨lam, al, hl1, hl2, ha1, ha2, m4, m5, m2⟩
  -- Failure of option (1): every `(λ,α)` is bad for at least one runner.
  have bad : ∀ lam al : ℕ, 2 ≤ lam → lam ≤ 5 → 1 ≤ al → al ≤ 5 →
      Int.fract ((lam : ℝ) * x₄ + (al : ℝ) / 6) ∉ Set.Icc (1 / 6) (5 / 6) ∨
        Int.fract ((lam : ℝ) * x₅ + (al : ℝ) / 6) ∉ Set.Icc (1 / 6) (5 / 6) ∨
          Int.fract ((lam : ℝ) * x₂ + 2 * (al : ℝ) / 6) ∉ Set.Icc (1 / 6) (5 / 6) := by
    intro lam al hl1 hl2 ha1 ha2
    by_contra hbad
    rw [not_or, not_or] at hbad
    simp only [not_not] at hbad
    exact wic lam al hl1 hl2 ha1 ha2 hbad.1 hbad.2.1 hbad.2.2
  -- Step 1: `|⟨λx₄⟩ − ⟨λx₅⟩| ∈ (1/6,5/6)` for every `λ ∈ {2,3,4,5}`.
  have s1 : ∀ lam : ℕ, 2 ≤ lam → lam ≤ 5 →
      (1 / 6 : ℝ) < |Int.fract ((lam : ℝ) * x₄) - Int.fract ((lam : ℝ) * x₅)| ∧
        |Int.fract ((lam : ℝ) * x₄) - Int.fract ((lam : ℝ) * x₅)| < 5 / 6 :=
    fun lam hl1 hl2 => step1_pre lam (fun al ha1 ha2 => bad lam al hl1 hl2 ha1 ha2)
  -- Hence `⟨λ·δ⟩ ∈ (1/6,5/6)` for `δ = ⟨x₄ − x₅⟩`.
  set δ := Int.fract (x₄ - x₅) with hδdef
  have key : ∀ lam : ℕ, 2 ≤ lam → lam ≤ 5 →
      Int.fract ((lam : ℝ) * δ) ∈ Set.Ioo (1 / 6) (5 / 6) := by
    intro lam hl1 hl2
    obtain ⟨g1, g2⟩ := s1 lam hl1 hl2
    have hfp : Int.fract (Int.fract ((lam : ℝ) * x₄) - Int.fract ((lam : ℝ) * x₅)) ∈
        Set.Ioo (1 / 6) (5 / 6) :=
      fract_mem_Ioo_of_abs
        (by linarith [Int.fract_nonneg ((lam : ℝ) * x₄), Int.fract_lt_one ((lam : ℝ) * x₅)])
        (by linarith [Int.fract_lt_one ((lam : ℝ) * x₄), Int.fract_nonneg ((lam : ℝ) * x₅)])
        ⟨g1, g2⟩
    rw [fract_sub_fract] at hfp
    rw [← fract_mul_nat'] at hfp
    rw [hδdef]
    exact hfp
  -- Claim 2.4 (contrapositive): `δ ∉ (1/6,5/6)`.
  have hδout : δ ∉ Set.Ioo (1 / 6) (5 / 6) := by
    intro hδI
    rcases claim24 hδI with h | h | h | h
    · exact h (by exact_mod_cast key 2 (by norm_num) (by norm_num))
    · exact h (by exact_mod_cast key 3 (by norm_num) (by norm_num))
    · exact h (by exact_mod_cast key 4 (by norm_num) (by norm_num))
    · exact h (by exact_mod_cast key 5 (by norm_num) (by norm_num))
  -- `δ ∈ (1/12,1/6) ∪ (5/6,11/12)`; the endpoints die at `λ = 5`.
  have hδr : (1 / 12 < δ ∧ δ < 1 / 6) ∨ (5 / 6 < δ ∧ δ < 11 / 12) :=
    delta_range (Int.fract_nonneg _) (Int.fract_lt_one _)
      (by exact_mod_cast key 2 (by norm_num) (by norm_num))
      (by exact_mod_cast key 5 (by norm_num) (by norm_num)) hδout
  have hδr' : (1 / 12 < Int.fract (x₄ - x₅) ∧ Int.fract (x₄ - x₅) < 1 / 6) ∨
      (5 / 6 < Int.fract (x₄ - x₅) ∧ Int.fract (x₄ - x₅) < 11 / 12) := by
    rw [← hδdef]
    exact hδr
  have hadiff : (1 / 12 < |x₄ - x₅| ∧ |x₄ - x₅| < 1 / 6) ∨
      (5 / 6 < |x₄ - x₅| ∧ |x₄ - x₅| < 11 / 12) :=
    abs_diff_range hx₄0 hx₄1 hx₅0 hx₅1 hδr'
  -- Step 2 (`λ = 2`): `|⟨2x₄⟩ − ⟨2x₅⟩| ∈ (1/6,1/3) ∪ (2/3,5/6)`.
  have hf2 : Int.fract (Int.fract (((2 : ℕ) : ℝ) * x₄) -
        Int.fract (((2 : ℕ) : ℝ) * x₅)) ∈ Set.Ioo (1 / 6) (1 / 3) ∨
      Int.fract (Int.fract (((2 : ℕ) : ℝ) * x₄) -
        Int.fract (((2 : ℕ) : ℝ) * x₅)) ∈ Set.Ioo (2 / 3) (5 / 6) := by
    have e1 : Int.fract (Int.fract (((2 : ℕ) : ℝ) * x₄) -
        Int.fract (((2 : ℕ) : ℝ) * x₅)) =
        Int.fract (((2 : ℕ) : ℝ) * (x₄ - x₅)) := by
      rw [fract_sub_fract, mul_sub]
    rw [e1, ← fract_mul_nat', ← hδdef, Nat.cast_ofNat]
    exact fract_two_delta hδr
  have hd2 : ((1 / 6 : ℝ) < |Int.fract (((2 : ℕ) : ℝ) * x₄) -
        Int.fract (((2 : ℕ) : ℝ) * x₅)| ∧
      |Int.fract (((2 : ℕ) : ℝ) * x₄) - Int.fract (((2 : ℕ) : ℝ) * x₅)| < 1 / 3) ∨
        (2 / 3 < |Int.fract (((2 : ℕ) : ℝ) * x₄) - Int.fract (((2 : ℕ) : ℝ) * x₅)| ∧
          |Int.fract (((2 : ℕ) : ℝ) * x₄) - Int.fract (((2 : ℕ) : ℝ) * x₅)| < 5 / 6) :=
    by
    refine abs_mem_of_fract ?_ ?_ hf2
    · linarith [Int.fract_nonneg (((2 : ℕ) : ℝ) * x₄), Int.fract_lt_one (((2 : ℕ) : ℝ) * x₅)]
    · linarith [Int.fract_lt_one (((2 : ℕ) : ℝ) * x₄), Int.fract_nonneg (((2 : ℕ) : ℝ) * x₅)]
  obtain ⟨d1, d2, d3, d4, d5⟩ :=
    dlist 2 (fun al ha1 ha2 => bad 2 al (by norm_num) (by norm_num) ha1 ha2)
  have res := step2 (Int.fract_nonneg _) (Int.fract_lt_one _) (Int.fract_nonneg _)
    (Int.fract_lt_one _) (Int.fract_nonneg _) (Int.fract_lt_one _) hd2 d1 d2 d3 d4 d5
  -- The four surviving configurations; `u ↔ v` symmetry covers the mirror cases.
  rcases res with ⟨hw, hor⟩ | ⟨hw, hor⟩
  · rcases hor with ⟨hu, hv⟩ | ⟨hv, hu⟩
    · -- Case A: `⟨2x₄⟩` high, `⟨2x₅⟩` low
      simp only [Nat.cast_ofNat] at hu hv hw
      exact caseA hx₄0 hx₄1 hx₅0 hx₅1 hx₂0 hx₂1 hadiff hu hv hw wit
    · -- Case A mirrored
      simp only [Nat.cast_ofNat] at hu hv hw
      have hadiff' : (1 / 12 < |x₅ - x₄| ∧ |x₅ - x₄| < 1 / 6) ∨
          (5 / 6 < |x₅ - x₄| ∧ |x₅ - x₄| < 11 / 12) := by
        rw [abs_sub_comm]
        exact hadiff
      exact caseA hx₅0 hx₅1 hx₄0 hx₄1 hx₂0 hx₂1 hadiff' hv hu hw
        (fun al spec m5 m4 m2 => wit al spec m4 m5 m2)
  · rcases hor with ⟨hu, hv⟩ | ⟨hv, hu⟩
    · -- Case B: `⟨2x₄⟩` mid-high, `⟨2x₅⟩` mid-low
      simp only [Nat.cast_ofNat] at hu hv hw
      exact caseB hx₄0 hx₄1 hx₅0 hx₅1 hx₂0 hx₂1 hadiff hu hv hw wit wic
    · -- Case B mirrored
      simp only [Nat.cast_ofNat] at hu hv hw
      have hadiff' : (1 / 12 < |x₅ - x₄| ∧ |x₅ - x₄| < 1 / 6) ∨
          (5 / 6 < |x₅ - x₄| ∧ |x₅ - x₄| < 11 / 12) := by
        rw [abs_sub_comm]
        exact hadiff
      exact caseB hx₅0 hx₅1 hx₄0 hx₄1 hx₂0 hx₂1 hadiff' hv hu hw
        (fun al spec m5 m4 m2 => wit al spec m4 m5 m2)
        (fun lam al h1 h2 h3 h4 m5 m4 m2 => wic lam al h1 h2 h3 h4 m4 m5 m2)

end
