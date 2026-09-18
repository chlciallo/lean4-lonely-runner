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
  -- `B`, the product of the denominators, clears every `w i` to an integer.
  set B : ℕ := ∏ i, (w i).den with hB
  have hBpos : 0 < B := Finset.prod_pos fun i _ => (w i).den_pos
  have hdvd : ∀ i, (w i).den ∣ B :=
    fun i => Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  -- `a i` is the integer `w i * B`.
  set a : Fin 4 → ℤ := fun i => (w i).num * ((B / (w i).den : ℕ) : ℤ) with ha
  -- Integrality: `w i * B = a i` in `ℚ`.
  have hqa : ∀ i : Fin 4, w i * (B : ℚ) = (a i : ℚ) := by
    intro i
    obtain ⟨k, hk⟩ := hdvd i
    have hdiv : B / (w i).den = k := by
      rw [hk]; exact Nat.mul_div_cancel_left _ (w i).den_pos
    simp only [ha, hdiv]
    rw [hk]
    push_cast
    rw [← mul_assoc, Rat.mul_den_eq_num]
  -- These integers are nonzero.
  have hane : ∀ i : Fin 4, a i ≠ 0 := by
    intro i
    simp only [ha]
    refine mul_ne_zero (Rat.num_ne_zero.mpr (hw i)) (Nat.cast_ne_zero.mpr ?_)
    exact (Nat.div_pos (Nat.le_of_dvd hBpos (hdvd i)) (w i).den_pos).ne'
  -- Integer speeds: the absolute values of the `a i`.
  set D : Finset ℕ := Finset.univ.image (fun i => (a i).natAbs) with hD
  have hDpos : ∀ d ∈ D, 0 < d := by
    intro d hd
    rw [hD, Finset.mem_image] at hd
    obtain ⟨i, -, rfl⟩ := hd
    exact Int.natAbs_pos.mpr (hane i)
  have hDcard : D.card ≤ 4 := by
    rw [hD]
    exact Finset.card_image_le.trans (by simp)
  obtain ⟨t₀, ht₀, hDt⟩ := lrc5_int D hDpos hDcard
  refine ⟨t₀ * (B : ℝ), mul_pos ht₀ (by exact_mod_cast hBpos), fun i => ?_⟩
  -- `t₀·B·w i = t₀·a i`, and `circ` removes the sign of `a i`.
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

/-- Finset form (≤4 positive rationals) — the shape `LRC6/RealCase.lean`
consumes as the `n − 1 = 5` rational input of the BHK reduction. -/
theorem lrc5_rat_finset (S : Finset ℚ) (hpos : ∀ q ∈ S, 0 < q) (hcard : S.card ≤ 4) :
    ∃ t : ℝ, 0 < t ∧ ∀ q ∈ S, (1 / 5 : ℝ) ≤ circ (t * q) := by
  -- `B`, the product of the denominators over `S`, clears every `q ∈ S`.
  set B : ℕ := ∏ q ∈ S, q.den with hB
  have hBpos : 0 < B := Finset.prod_pos fun q _ => q.den_pos
  have hdvd : ∀ q ∈ S, q.den ∣ B := fun q hq => Finset.dvd_prod_of_mem _ hq
  -- `n q` is the natural number `q * B` (positive since `q > 0`).
  set n : ℚ → ℕ := fun q => q.num.natAbs * (B / q.den) with hn
  have hqa : ∀ q ∈ S, q * (B : ℚ) = (n q : ℚ) := by
    intro q hq
    obtain ⟨k, hk⟩ := hdvd q hq
    have hdiv : B / q.den = k := by
      rw [hk]; exact Nat.mul_div_cancel_left _ q.den_pos
    simp only [hn, hdiv]
    rw [hk]
    push_cast
    rw [Nat.cast_natAbs, Int.cast_abs,
      abs_of_pos (show (0 : ℚ) < q.num by
        exact_mod_cast Rat.num_pos.mpr (hpos q hq)),
      ← mul_assoc, Rat.mul_den_eq_num]
  have hnpos : ∀ q ∈ S, 0 < n q := by
    intro q hq
    simp only [hn]
    exact Nat.mul_pos (Int.natAbs_pos.mpr (Rat.num_ne_zero.mpr (hpos q hq).ne'))
      (Nat.div_pos (Nat.le_of_dvd hBpos (hdvd q hq)) q.den_pos)
  set D : Finset ℕ := S.image n with hD
  have hDpos : ∀ d ∈ D, 0 < d := by
    intro d hd
    rw [hD, Finset.mem_image] at hd
    obtain ⟨q, hq, rfl⟩ := hd
    exact hnpos q hq
  have hDcard : D.card ≤ 4 := Finset.card_image_le.trans hcard
  obtain ⟨t₀, ht₀, hDt⟩ := lrc5_int D hDpos hDcard
  refine ⟨t₀ * (B : ℝ), mul_pos ht₀ (by exact_mod_cast hBpos), fun q hq => ?_⟩
  have hmem : n q ∈ D := Finset.mem_image.mpr ⟨q, hq, rfl⟩
  have hcast : (q : ℝ) * (B : ℝ) = (n q : ℝ) := by
    exact_mod_cast hqa q hq
  rw [show t₀ * (B : ℝ) * (q : ℝ) = t₀ * ((q : ℝ) * (B : ℝ)) from by ring,
    hcast]
  exact hDt _ hmem

/-- **Lonely Runner Conjecture, `n = 5`, rational speeds.** -/
theorem lonely_runner_five_rat (v : Fin 5 → ℚ) (hv : Function.Injective v) :
    ∀ i : Fin 5, ∃ t : ℝ, 0 ≤ t ∧ ∀ j : Fin 5, j ≠ i →
      (1 / 5 : ℝ) ≤ dist ((t * (v i : ℝ) : UnitAddCircle) :
        UnitAddCircle) ((t * (v j : ℝ) : UnitAddCircle) : UnitAddCircle) := by
  intro i
  -- The four relative speeds `v j − v i` for `j ≠ i`, indexed by `Fin 4`.
  have hwnz : ∀ j' : Fin 4, v (i.succAbove j') - v i ≠ 0 := fun j' =>
    sub_ne_zero.mpr fun e => Fin.succAbove_ne i j' (hv e)
  obtain ⟨t, ht, hwt⟩ := lrc5_rel_rat (fun j' => v (i.succAbove j') - v i) hwnz
  refine ⟨t, ht.le, fun j hj => ?_⟩
  obtain ⟨j', rfl⟩ := Fin.exists_succAbove_eq hj
  rw [dist_unitAddCircle_eq_circ]
  have hsub : t * (v i : ℝ) - t * (v (i.succAbove j') : ℝ)
      = -(t * ((v (i.succAbove j') - v i : ℚ) : ℝ)) := by
    push_cast
    ring
  rw [hsub, circ_neg]
  exact hwt j'
