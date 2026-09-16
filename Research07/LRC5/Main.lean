/-
Copyright (c) 2026 Research07 contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Research07 contributors
-/
import Research07.LRC5.IntCase
import Research07.LRC3.Main

/-!
# Lonely Runner Conjecture, five runners with rational speeds

The `n = 5` case of the Lonely Runner Conjecture (Cusick–Pomerance 1984,
simplified by Bienia et al. 1998 and by Barajas–Serra 2008) for rational
speeds: five pairwise-distinct rational speeds, every runner eventually at
circular distance `≥ 1/5` from all others.

Reduction: relative speeds `v j − v i` are nonzero rationals; clearing the
common denominator reduces to `lrc5_int` (integer speeds, threshold `1/5`).
The full real-speeds statement needs the BHK reduction (Kronecker density
on the orbit closure) and is left to phase two.
-/

/-- Four nonzero rational relative speeds admit a common lonely time.
Write `w i = b i / c` with `b i` positive integers and `c > 0` the common
denominator; the integer case gives `t₀` for `(b i)` and `t = c·t₀` works. -/
theorem lrc5_rel_rat (w : Fin 4 → ℚ) (hw : ∀ i, w i ≠ 0) :
    ∃ t : ℝ, 0 < t ∧ ∀ i, (1 / 5 : ℝ) ≤ circ (t * (w i : ℝ)) := by
  sorry

/-- **Lonely Runner Conjecture, `n = 5`, rational speeds.** -/
theorem lonely_runner_five_rat (v : Fin 5 → ℚ) (hv : Function.Injective v) :
    ∀ i : Fin 5, ∃ t : ℝ, 0 ≤ t ∧ ∀ j : Fin 5, j ≠ i →
      (1 / 5 : ℝ) ≤ dist ((t * (v i : ℝ) : UnitAddCircle) :
        UnitAddCircle) ((t * (v j : ℝ) : UnitAddCircle) : UnitAddCircle) := by
  sorry
