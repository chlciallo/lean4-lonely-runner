/-
Copyright (c) 2026 Research07 contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Research07 contributors
-/
import Research07.LRC6.IntCase
import Research07.LRC5.Main

/-!
# Lonely Runner Conjecture, six runners with rational speeds

The `n = 6` case of the Lonely Runner Conjecture (proved by Renault 2004) for
rational speeds: five pairwise-distinct relative rational speeds, every runner
eventually at circular distance `≥ 1/6` from all others.

Reduction: relative speeds `w i` are nonzero rationals; clearing the common
denominator reduces to `lrc6_int` (integer speeds, threshold `1/6`), which is
proved in `IntCase.lean` via Renault's parity/residue case split
(Sections 3–6 of the paper).
-/

/-- Five nonzero rational relative speeds admit a common lonely time.
Write `w i = b i / c` with `b i` integers and `c > 0` the common denominator;
the integer case gives `t₀` for `(|b i|)` and `t = c·t₀` works. -/
theorem lrc6_rel_rat (w : Fin 5 → ℚ) (hw : ∀ i, w i ≠ 0) :
    ∃ t : ℝ, 0 < t ∧ ∀ i, (1 / 6 : ℝ) ≤ circ (t * (w i : ℝ)) := by
  set B : ℕ := ∏ i, (w i).den with hB
  have hBpos : 0 < B := Finset.prod_pos fun i _ => (w i).den_pos
  have hdvd : ∀ i, (w i).den ∣ B :=
    fun i => Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  set a : Fin 5 → ℤ := fun i => (w i).num * ((B / (w i).den : ℕ) : ℤ) with ha
  have hqa : ∀ i : Fin 5, w i * (B : ℚ) = (a i : ℚ) := by
    intro i
    obtain ⟨k, hk⟩ := hdvd i
    have hdiv : B / (w i).den = k := by
      rw [hk]; exact Nat.mul_div_cancel_left _ (w i).den_pos
    simp only [ha, hdiv]
    rw [hk]
    push_cast
    rw [← mul_assoc, Rat.mul_den_eq_num]
  have hane : ∀ i : Fin 5, a i ≠ 0 := by
    intro i
    simp only [ha]
    refine mul_ne_zero (Rat.num_ne_zero.mpr (hw i)) (Nat.cast_ne_zero.mpr ?_)
    exact (Nat.div_pos (Nat.le_of_dvd hBpos (hdvd i)) (w i).den_pos).ne'
  set D : Finset ℕ := Finset.univ.image (fun i => (a i).natAbs) with hD
  have hDpos : ∀ d ∈ D, 0 < d := by
    intro d hd
    rw [hD, Finset.mem_image] at hd
    obtain ⟨i, -, rfl⟩ := hd
    exact Int.natAbs_pos.mpr (hane i)
  have hDcard : D.card ≤ 5 := by
    rw [hD]
    exact Finset.card_image_le.trans (by simp)
  obtain ⟨t₀, ht₀, hDt⟩ := lrc6_int D hDpos hDcard
  refine ⟨t₀ * (B : ℝ), mul_pos ht₀ (by exact_mod_cast hBpos), fun i => ?_⟩
  have hcast : (w i : ℝ) * (B : ℝ) = (a i : ℝ) := by
    exact_mod_cast hqa i
  have hmem : (a i).natAbs ∈ D := by
    rw [hD]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  have hsign : circ (t₀ * (a i : ℝ)) = circ (t₀ * ((a i).natAbs : ℝ)) := by
    conv_lhs => rw [← circ_abs, abs_mul, abs_of_pos ht₀, ← Int.cast_abs,
      ← Nat.cast_natAbs]
  rw [show t₀ * (B : ℝ) * (w i : ℝ) = t₀ * ((w i : ℝ) * (B : ℝ)) from by ring,
    hcast, hsign]
  exact hDt _ hmem

/-- **Lonely Runner Conjecture, `n = 6`, rational speeds.** -/
theorem lonely_runner_six_rat (v : Fin 6 → ℚ) (hv : Function.Injective v) :
    ∀ i : Fin 6, ∃ t : ℝ, 0 ≤ t ∧ ∀ j : Fin 6, j ≠ i →
      (1 / 6 : ℝ) ≤ dist ((t * (v i : ℝ) : UnitAddCircle) :
        UnitAddCircle) ((t * (v j : ℝ) : UnitAddCircle) : UnitAddCircle) := by
  intro i
  have hwnz : ∀ j' : Fin 5, v (i.succAbove j') - v i ≠ 0 := fun j' =>
    sub_ne_zero.mpr fun e => Fin.succAbove_ne i j' (hv e)
  obtain ⟨t, ht, hwt⟩ := lrc6_rel_rat (fun j' => v (i.succAbove j') - v i) hwnz
  refine ⟨t, ht.le, fun j hj => ?_⟩
  obtain ⟨j', rfl⟩ := Fin.exists_succAbove_eq hj
  rw [dist_unitAddCircle_eq_circ]
  have hsub : t * (v i : ℝ) - t * (v (i.succAbove j') : ℝ)
      = -(t * ((v (i.succAbove j') - v i : ℚ) : ℝ)) := by
    push_cast
    ring
  rw [hsub, circ_neg]
  exact hwt j'
