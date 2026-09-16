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
  sorry

/-- **Lonely Runner Conjecture, `n = 3`** (Wills 1967): three runners on the
unit circle with pairwise distinct speeds each become lonely. -/
theorem lonely_runner_three (v : Fin 3 → ℝ) (hv : Function.Injective v) :
    ∀ i : Fin 3, ∃ t ≥ 0, ∀ j : Fin 3, j ≠ i →
      (1 / 3 : ℝ) ≤ dist ((t * v i : ℝ) : UnitAddCircle) ((t * v j : ℝ) : UnitAddCircle) := by
  sorry
