/-
Copyright (c) 2026 Research07 contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Research07 contributors
-/
import Research07.LRC3.TwoMoving

/-!
# Lonely Runner Conjecture, three runners

The main theorem: for three pairwise-distinct real speeds, every runner is
eventually at circular distance `≥ 1/3` from both others. This is the `n = 3`
case of the Lonely Runner Conjecture (Wills 1967; convention: `n` counts total
runners, threshold `1/n`).

Reduction: for runner `i`, the circular distance to runner `j` at time `t`
equals `circ (t * (v j - v i))`. The two other runners have difference speeds
`a, b > 0` (injectivity), and `two_moving` supplies a common lonely time.
-/

/-- Circle distance between embedded reals is `circ` of the difference. -/
theorem dist_unitAddCircle_eq_circ (x y : ℝ) :
    dist (x : UnitAddCircle) (y : UnitAddCircle) = circ (x - y) := by
  rw [dist_eq_norm, ← AddCircle.coe_sub]
  rfl

/-- For `t ≥ 0`, the circle distance between `t * x` and `t * y` equals
`circ` of `t` times the absolute difference `|y - x|`. -/
private theorem dist_eq_circ_abs (t x y : ℝ) (ht : 0 ≤ t) :
    dist ((t * x : ℝ) : UnitAddCircle) ((t * y : ℝ) : UnitAddCircle)
      = circ (t * |y - x|) := by
  rw [dist_unitAddCircle_eq_circ]
  have h : t * x - t * y = -(t * (y - x)) := by ring
  rw [h, circ_neg, ← circ_abs, abs_mul, abs_of_nonneg ht]

/-- **Lonely Runner Conjecture, `n = 3`** (Wills 1967): three runners on the
unit circle with pairwise distinct speeds each become lonely. -/
theorem lonely_runner_three (v : Fin 3 → ℝ) (hv : Function.Injective v) :
    ∀ i : Fin 3, ∃ t ≥ 0, ∀ j : Fin 3, j ≠ i →
      (1 / 3 : ℝ) ≤ dist ((t * v i : ℝ) : UnitAddCircle) ((t * v j : ℝ) : UnitAddCircle) := by
  -- Injectivity gives nonzero difference speeds for `j ≠ i`.
  have hne : ∀ i j : Fin 3, j ≠ i → v j - v i ≠ 0 :=
    fun i j hij ↦ sub_ne_zero.mpr (fun e ↦ hij (hv e))
  intro i
  fin_cases i
  · -- `i = 0`; the other runners are `1, 2`.
    obtain ⟨t, ht, h1, h2⟩ := two_moving
      (abs_pos.mpr (hne 0 1 (by decide))) (abs_pos.mpr (hne 0 2 (by decide)))
    refine ⟨t, ht.le, fun j hj ↦ ?_⟩
    fin_cases j
    · exact (hj rfl).elim
    · rw [dist_eq_circ_abs _ _ _ ht.le]; exact h1
    · rw [dist_eq_circ_abs _ _ _ ht.le]; exact h2
  · -- `i = 1`; the other runners are `0, 2`.
    obtain ⟨t, ht, h1, h2⟩ := two_moving
      (abs_pos.mpr (hne 1 0 (by decide))) (abs_pos.mpr (hne 1 2 (by decide)))
    refine ⟨t, ht.le, fun j hj ↦ ?_⟩
    fin_cases j
    · rw [dist_eq_circ_abs _ _ _ ht.le]; exact h1
    · exact (hj rfl).elim
    · rw [dist_eq_circ_abs _ _ _ ht.le]; exact h2
  · -- `i = 2`; the other runners are `0, 1`.
    obtain ⟨t, ht, h1, h2⟩ := two_moving
      (abs_pos.mpr (hne 2 0 (by decide))) (abs_pos.mpr (hne 2 1 (by decide)))
    refine ⟨t, ht.le, fun j hj ↦ ?_⟩
    fin_cases j
    · rw [dist_eq_circ_abs _ _ _ ht.le]; exact h1
    · rw [dist_eq_circ_abs _ _ _ ht.le]; exact h2
    · exact (hj rfl).elim
