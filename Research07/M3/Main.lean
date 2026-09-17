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
  -- Work with the positive speeds `|w i|`; `circ` forgets the sign of `w i`.
  have hupos : ∀ i, 0 < |w i| := fun i => abs_pos.mpr (hw i)
  have hcirc : ∀ t : ℝ, 0 ≤ t → ∀ i, circ (t * w i) = circ (t * |w i|) := by
    intro t ht i
    rw [← circ_abs, abs_mul, abs_of_nonneg ht]
  -- Dichotomy: either `|w|` is a real multiple of a rational tuple, or not.
  by_cases hrat : ∃ c : ℝ, ∀ i, ∃ q : ℚ, |w i| = c * q
  · -- Rational case: `|w i| = c * q i` with `c ≠ 0`; if `s` is the rational lonely
    -- time for `q`, then `t = s / |c|` works — `circ` absorbs the sign of `c`.
    obtain ⟨c, hc⟩ := hrat
    choose q hq using hc
    have hc0 : c ≠ 0 := by
      intro h0
      have h := hupos 0
      rw [hq 0, h0, zero_mul] at h
      exact h.ne rfl
    have hq0 : ∀ i, q i ≠ 0 := by
      intro i h0
      have h := hupos i
      rw [hq i, h0, Rat.cast_zero, mul_zero] at h
      exact h.ne rfl
    obtain ⟨s, hs, hsv⟩ := lrc5_rel_rat q hq0
    -- `|s / |c| * c| = s`, so `|t * |w i|| = |s * q i|`.
    have hsc : |s / |c| * c| = s := by
      rw [abs_mul, abs_div, abs_of_pos hs, abs_abs]
      exact div_mul_cancel₀ s (abs_ne_zero.mpr hc0)
    have habs : ∀ i, abs (s / |c| * |w i|) = |s * (q i : ℝ)| := by
      intro i
      rw [hq i, ← mul_assoc, abs_mul, hsc, abs_mul, abs_of_pos hs]
    have key : ∀ i, circ (s / |c| * |w i|) = circ (s * (q i : ℝ)) := by
      intro i
      rw [← circ_abs (s / |c| * |w i|), ← circ_abs (s * (q i : ℝ)), habs i]
    refine ⟨s / |c|, div_pos hs (abs_pos.mpr hc0), fun i => ?_⟩
    rw [hcirc _ (div_pos hs (abs_pos.mpr hc0)).le i, key i]
    exact hsv i
  · -- Irrational case: BHK Lemma 8 at `n = 5`, using `lrc4` on ≤3 rationals.
    obtain ⟨t, ht, hwt⟩ := lrc5_real_of_irrational_ratio lrc4_rat_finset hupos hrat
    exact ⟨t, ht, fun i => by rw [hcirc t ht.le i]; exact (hwt i).le⟩

/-- **The Lonely Runner Conjecture for five runners** (real speeds): for every
injective speed tuple `v : Fin 5 → ℝ` and every runner `i`, there is a time `t ≥ 0`
at which `i` is at circular distance `≥ 1/5` from every other runner. -/
theorem lonely_runner_five (v : Fin 5 → ℝ) (hv : Function.Injective v) :
    ∀ i : Fin 5, ∃ t : ℝ, 0 ≤ t ∧
      ∀ j : Fin 5, j ≠ i →
        (1 / 5 : ℝ) ≤
          dist ((t * (v i : ℝ) : UnitAddCircle) : UnitAddCircle)
               ((t * (v j : ℝ) : UnitAddCircle) : UnitAddCircle) := by
  intro i
  -- The four relative speeds `v j − v i` for `j ≠ i`, indexed by `Fin 4`.
  have hwnz : ∀ j' : Fin 4, v (i.succAbove j') - v i ≠ 0 := fun j' =>
    sub_ne_zero.mpr fun e => Fin.succAbove_ne i j' (hv e)
  obtain ⟨t, ht, hwt⟩ := lrc5_rel_real (fun j' => v (i.succAbove j') - v i) hwnz
  refine ⟨t, ht.le, fun j hj => ?_⟩
  obtain ⟨j', rfl⟩ := Fin.exists_succAbove_eq hj
  rw [dist_unitAddCircle_eq_circ]
  have hsub : t * v i - t * v (i.succAbove j')
      = -(t * (v (i.succAbove j') - v i)) := by ring
  rw [hsub, circ_neg]
  exact hwt j'

end
