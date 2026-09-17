/-
Copyright (c) 2026 Research07 contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Research07 contributors
-/

import Mathlib
import Research07.LRC3.Circ
import Research07.LRC5.Main
import Research07.LRC4.Main
import Research07.M3.BHK

/-!# W10 — Final assembly: `lonely_runner_five` for real speeds (FROZEN STATEMENTS)

Case split on the four relative speeds: all-rational → `lrc5_int` via denominators;
some irrational ratio → `lrc5_real_of_irrational_ratio` (BHK Lemma 8, n=5).

Frozen contract for agent W10. Prove every `sorry`; do not change statements.
-/

noncomputable section

/-- Four nonzero real relative speeds: ∃ t > 0 with all `circ (t·wᵢ) ≥ 1/5`. -/
theorem lrc5_rel_real (w : Fin 4 → ℝ) (hw : ∀ i, w i ≠ 0) :
    ∃ t : ℝ, 0 < t ∧ ∀ i, (1 / 5 : ℝ) ≤ circ (t * w i) := by
  sorry

/-- **The Lonely Runner Conjecture for five runners** (real speeds): for every
injective speed tuple `v : Fin 5 → ℝ` and every runner `i`, there is a time `t ≥ 0`
at which `i` is at circular distance `≥ 1/5` from every other runner. -/
theorem lonely_runner_five (v : Fin 5 → ℝ) (hv : Function.Injective v) :
    ∀ i : Fin 5, ∃ t : ℝ, 0 ≤ t ∧
      ∀ j : Fin 5, j ≠ i →
        (1 / 5 : ℝ) ≤
          dist ((t * (v i : ℝ) : UnitAddCircle) : UnitAddCircle)
               ((t * (v j : ℝ) : UnitAddCircle) : UnitAddCircle) := by
  sorry

end
