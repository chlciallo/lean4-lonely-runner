/-
Copyright (c) 2026 Research07 contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Research07 contributors
-/
import Research07.LRC3.Covering

/-!
# Two moving runners

The reduced form of the three-runner case: for positive real speeds `a, b`
there is a positive time `t` at which both `t·a` and `t·b` are at distance
`≥ 1/3` from the nearest integer.

Proof sketch (Wills 1967 / Cusick-style elementary argument):
* if `a = b`, take `t = 1/(2a)`;
* else assume `b < a`. If `a ≤ 2b`, then `t = 1/(3b)` works directly
  (`t·b = 1/3`, `t·a ∈ (1/3, 2/3]`); if `a > 2b`, then throughout
  `t ∈ [1/(3b), 2/(3b)]` we have `t·b ∈ [1/3, 2/3]`, while `t·a` sweeps an
  interval of length `a/(3b) > 2/3`, which contains a middle-third point by
  `covering`.
-/

/-- On the window `t ∈ [1/(3b), 2/(3b)]`, runner `b` stays lonely. -/
theorem lonely_on_window {b : ℝ} (hb : 0 < b) :
    ∀ t ∈ Set.Icc (1 / (3 * b)) (2 / (3 * b)), 1 / 3 ≤ circ (t * b) := by
  intro t ht
  have hb' : (b : ℝ) ≠ 0 := ne_of_gt hb
  have e1 : (1 : ℝ) / (3 * b) * b = 1 / 3 := by field_simp
  have e2 : (2 : ℝ) / (3 * b) * b = 2 / 3 := by field_simp
  rw [Set.mem_Icc] at ht
  rw [circ_ge_third_iff]
  refine ⟨0, ?_⟩
  simp only [Int.cast_zero, zero_add, Set.mem_Icc]
  exact ⟨by rw [← e1]; exact mul_le_mul_of_nonneg_right ht.1 hb.le,
         by rw [← e2]; exact mul_le_mul_of_nonneg_right ht.2 hb.le⟩

/-- Ordered case of `two_moving`: if `0 < b < a`, a common lonely time exists. -/
private theorem two_moving_ordered {a b : ℝ} (hb : 0 < b) (hba : b < a) :
    ∃ t, 0 < t ∧ 1 / 3 ≤ circ (t * a) ∧ 1 / 3 ≤ circ (t * b) := by
  have ha : 0 < a := lt_trans hb hba
  have ha' : (a : ℝ) ≠ 0 := ne_of_gt ha
  have hb' : (b : ℝ) ≠ 0 := ne_of_gt hb
  have h3b : (0 : ℝ) < 3 * b := by positivity
  rcases lt_or_ge (2 * b) a with h | h
  · -- `2b < a`: `t·a` sweeps an interval of length `a/(3b) > 2/3`; apply `covering`.
    have hL : (2 : ℝ) / 3 < a / (3 * b) := by
      rw [lt_div_iff₀ h3b]; nlinarith [h]
    obtain ⟨ξ, hξI, hξ⟩ := covering (x := a / (3 * b)) (L := a / (3 * b)) hL
    rw [Set.mem_Icc] at hξI
    have hξpos : 0 < ξ := lt_of_lt_of_le (div_pos ha h3b) hξI.1
    refine ⟨ξ / a, div_pos hξpos ha, ?_, ?_⟩
    · rw [div_mul_cancel₀ _ ha']; exact hξ
    · apply lonely_on_window hb
      rw [Set.mem_Icc]
      constructor
      · rw [le_div_iff₀ ha, show (1 : ℝ) / (3 * b) * a = a / (3 * b) by ring]
        exact hξI.1
      · rw [div_le_iff₀ ha, show (2 : ℝ) / (3 * b) * a = a / (3 * b) + a / (3 * b) by ring]
        exact hξI.2
  · -- `b < a ≤ 2b`: `t = 1/(3b)` gives `t·b = 1/3` and `t·a ∈ (1/3, 2/3]`.
    have hb3 : (1 : ℝ) / (3 * b) * b = 1 / 3 := by field_simp
    refine ⟨1 / (3 * b), by positivity, ?_, ?_⟩
    · rw [circ_ge_third_iff]
      refine ⟨0, ?_⟩
      simp only [Int.cast_zero, zero_add, Set.mem_Icc]
      have e : (1 : ℝ) / (3 * b) * a = a / (3 * b) := by ring
      rw [e]
      constructor
      · rw [le_div_iff₀ h3b]; nlinarith [hba]
      · rw [div_le_iff₀ h3b]; nlinarith [h]
    · rw [hb3, circ_ge_third_iff]
      exact ⟨0, by norm_num [Set.mem_Icc]⟩

/-- The two-moving-runner theorem: a common lonely time always exists. -/
theorem two_moving {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∃ t, 0 < t ∧ 1 / 3 ≤ circ (t * a) ∧ 1 / 3 ≤ circ (t * b) := by
  have ha' : (a : ℝ) ≠ 0 := ne_of_gt ha
  rcases eq_or_ne a b with rfl | hne
  · -- `a = b`: take `t = 1/(2a)`, so `t·a = t·b = 1/2`.
    have e : (1 : ℝ) / (2 * a) * a = 1 / 2 := by field_simp
    exact ⟨1 / (2 * a), by positivity,
      by rw [e, circ_half]; norm_num, by rw [e, circ_half]; norm_num⟩
  · rcases lt_or_gt_of_ne hne with hab | hba
    · obtain ⟨t, ht, htb, hta⟩ := two_moving_ordered ha hab
      exact ⟨t, ht, hta, htb⟩
    · obtain ⟨t, ht, hta, htb⟩ := two_moving_ordered hb hba
      exact ⟨t, ht, hta, htb⟩
