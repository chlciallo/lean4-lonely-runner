/-
Copyright (c) 2026 Research07 contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Research07 contributors
-/
import Mathlib

/-!
# Circle distance API

`circ x` is the distance from `x : ℝ` to the nearest integer, i.e. the norm on
`UnitAddCircle = ℝ ⧸ ℤ`. All lonely-runner statements are phrased in terms of
`circ` on `ℝ`; the bridge to `UnitAddCircle.dist` happens in `Main.lean`.
-/

/-- Distance from `x` to the nearest integer: the norm on `ℝ ⧸ ℤ`. -/
noncomputable def circ (x : ℝ) : ℝ := ‖(x : UnitAddCircle)‖

/-- `circ` unfolds to distance to the nearest integer. -/
theorem circ_eq (x : ℝ) : circ x = |x - round x| := UnitAddCircle.norm_eq

/-- `circ` is nonnegative. -/
theorem circ_nonneg (x : ℝ) : 0 ≤ circ x := by
  rw [circ_eq]
  exact abs_nonneg _

/-- `circ` never exceeds half a period. -/
theorem circ_le_half (x : ℝ) : circ x ≤ 1 / 2 := by
  rw [circ_eq]
  exact abs_sub_round x

/-- `circ` is periodic with integer period. -/
theorem circ_add_int (x : ℝ) (n : ℤ) : circ (x + n) = circ x := by
  rw [circ_eq, circ_eq, round_add_intCast, Int.cast_add]
  congr 1
  ring

/-- `circ` is even. -/
theorem circ_neg (x : ℝ) : circ (-x) = circ x := by
  unfold circ
  rw [AddCircle.coe_neg, norm_neg]

/-- `circ` is invariant under `|·|`. -/
theorem circ_abs (x : ℝ) : circ |x| = circ x := by
  rcases le_total 0 x with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_nonpos h, circ_neg]

/-- The half-integer point has distance `1/2`. -/
theorem circ_half : circ (1 / 2 : ℝ) = 1 / 2 := by
  change ‖((1 / 2 : ℝ) : UnitAddCircle)‖ = 1 / 2
  simpa using AddCircle.norm_half_period_eq (1 : ℝ)

/-- `circ x ≥ 1/3` iff `x` lies in some middle-third arc `[k + 1/3, k + 2/3]`. -/
theorem circ_ge_third_iff (x : ℝ) :
    1 / 3 ≤ circ x ↔ ∃ k : ℤ, x ∈ Set.Icc ((k : ℝ) + 1 / 3) ((k : ℝ) + 2 / 3) := by
  constructor
  · -- Forward: with `r = round x`, `|x - r| ≥ 1/3` and `|x - r| ≤ 1/2`
    -- place `x` in `[r + 1/3, r + 2/3]` or `[(r - 1) + 1/3, (r - 1) + 2/3]`.
    intro h
    rw [circ_eq] at h
    have hle : |x - (round x : ℝ)| ≤ 1 / 2 := abs_sub_round x
    rcases le_total 0 (x - (round x : ℝ)) with hpos | hneg
    · rw [abs_of_nonneg hpos] at h hle
      exact ⟨round x, Set.mem_Icc.mpr ⟨by linarith, by linarith⟩⟩
    · rw [abs_of_nonpos hneg] at h hle
      refine ⟨round x - 1, Set.mem_Icc.mpr ⟨?_, ?_⟩⟩ <;>
        · push_cast
          linarith
  · -- Backward: `circ x = circ (x - k)` and `x - k ∈ [1/3, 2/3]`, whose round is
    -- `0` or `1`; in both cases `|x - k - round (x - k)| ≥ 1/3`.
    rintro ⟨k, hk⟩
    obtain ⟨hk1, hk2⟩ := Set.mem_Icc.mp hk
    have h1 : circ x = circ (x - (k : ℝ)) := by
      have h2 := circ_add_int (x - (k : ℝ)) k
      rwa [sub_add_cancel] at h2
    have hy1 : 1 / 3 ≤ x - (k : ℝ) := by linarith
    have hy2 : x - (k : ℝ) ≤ 2 / 3 := by linarith
    rw [h1, circ_eq]
    set y := x - (k : ℝ) with hy
    rcases lt_or_ge y (1 / 2) with hylt | hyge
    · have hr0 : round y = 0 := by
        rw [round_eq_zero_iff]
        exact Set.mem_Ico.mpr ⟨by linarith, hylt⟩
      rw [hr0, Int.cast_zero, sub_zero, abs_of_nonneg (by linarith : (0 : ℝ) ≤ y)]
      exact hy1
    · have hr1 : round y = 1 := by
        rw [round_eq_iff]
        refine Set.mem_Ico.mpr ⟨?_, ?_⟩ <;> push_cast <;> linarith
      rw [hr1, Int.cast_one, abs_of_nonpos (by linarith : y - 1 ≤ (0 : ℝ))]
      linarith
