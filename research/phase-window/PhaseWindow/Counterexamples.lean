import PhaseWindow.Sharpness
import Mathlib.Tactic.IntervalCases

namespace PhaseWindow

/-- The small-threshold radius `2d/a` does not extend to `d=1/5`. -/
theorem one_fifth_obstruction :
    ¬ ∃ s : ℝ, |s| ≤ 2 / 5 ∧ Safe (1 / 5) s ∧ Safe (1 / 5) (5 / 3 * s + 1 / 2) := by
  apply bridge_obstruction <;> norm_num

/-- Relative separation at just the initial time is insufficient without drift allowance. -/
theorem drift_allowance_needed :
    ¬ ∃ s : ℝ, |s - 1 / 2| ≤ 1 / 12 ∧
      Safe (1 / 6) (2 * s) ∧ Safe (1 / 6) (5 * s) := by
  rintro ⟨s,hs,hsa,hsb⟩
  have hsl := (abs_le.mp hs).1
  have hsr := (abs_le.mp hs).2
  have ha := hsa 1
  norm_num only [Int.cast_one] at ha
  rw [le_abs] at ha
  rcases ha with hp | hn
  · have hb := hsb 3
    norm_num only [Int.cast_ofNat] at hb
    rw [le_abs] at hb
    rcases hb with hb | hb <;> linarith
  · have hb := hsb 2
    norm_num only [Int.cast_ofNat] at hb
    rw [le_abs] at hb
    rcases hb with hb | hb <;> linarith

/-- A short relation and a maximally safe core phase do not imply a fibre lift.
    This quantifies over ALL real times with 8t equal to a half-integer. -/
theorem frozen_phase_counterexample (t : ℝ) (z : ℤ) (ht : 8 * t = z + 1 / 2) :
    ¬ (Safe (1 / 4) (3 * t) ∧ Safe (1 / 4) (5 * t)) := by
  intro hs
  have hz : z = z % 8 + 8 * (z / 8) := by omega
  have hzR : (z : ℝ) = (z % 8 : ℤ) + 8 * (z / 8 : ℤ) := by exact_mod_cast hz
  have hr0 : 0 ≤ z % 8 := Int.emod_nonneg _ (by norm_num)
  have hr8 : z % 8 < 8 := Int.emod_lt_of_pos _ (by norm_num)
  interval_cases h : z % 8
  · norm_num [h] at hzR
    have hn := hs.1 (3 * (z / 8)); push_cast at hn
    rw [le_abs] at hn; rcases hn with hn | hn <;> linarith
  · norm_num [h] at hzR
    have hn := hs.2 (5 * (z / 8) + 1); push_cast at hn
    rw [le_abs] at hn; rcases hn with hn | hn <;> linarith
  · norm_num [h] at hzR
    have hn := hs.1 (3 * (z / 8) + 1); push_cast at hn
    rw [le_abs] at hn; rcases hn with hn | hn <;> linarith
  · norm_num [h] at hzR
    have hn := hs.2 (5 * (z / 8) + 2); push_cast at hn
    rw [le_abs] at hn; rcases hn with hn | hn <;> linarith
  · norm_num [h] at hzR
    have hn := hs.2 (5 * (z / 8) + 3); push_cast at hn
    rw [le_abs] at hn; rcases hn with hn | hn <;> linarith
  · norm_num [h] at hzR
    have hn := hs.1 (3 * (z / 8) + 2); push_cast at hn
    rw [le_abs] at hn; rcases hn with hn | hn <;> linarith
  · norm_num [h] at hzR
    have hn := hs.2 (5 * (z / 8) + 4); push_cast at hn
    rw [le_abs] at hn; rcases hn with hn | hn <;> linarith
  · norm_num [h] at hzR
    have hn := hs.1 (3 * (z / 8) + 3); push_cast at hn
    rw [le_abs] at hn; rcases hn with hn | hn <;> linarith

end PhaseWindow
