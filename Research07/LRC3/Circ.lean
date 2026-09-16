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
theorem circ_nonneg (x : ℝ) : 0 ≤ circ x := by sorry

/-- `circ` never exceeds half a period. -/
theorem circ_le_half (x : ℝ) : circ x ≤ 1 / 2 := by sorry

/-- `circ` is periodic with integer period. -/
theorem circ_add_int (x : ℝ) (n : ℤ) : circ (x + n) = circ x := by sorry

/-- `circ` is even. -/
theorem circ_neg (x : ℝ) : circ (-x) = circ x := by sorry

/-- `circ` is invariant under `|·|`. -/
theorem circ_abs (x : ℝ) : circ |x| = circ x := by sorry

/-- The half-integer point has distance `1/2`. -/
theorem circ_half : circ (1 / 2 : ℝ) = 1 / 2 := by sorry

/-- `circ x ≥ 1/3` iff `x` lies in some middle-third arc `[k + 1/3, k + 2/3]`. -/
theorem circ_ge_third_iff (x : ℝ) :
    1 / 3 ≤ circ x ↔ ∃ k : ℤ, x ∈ Set.Icc ((k : ℝ) + 1 / 3) ((k : ℝ) + 2 / 3) := by
  sorry
