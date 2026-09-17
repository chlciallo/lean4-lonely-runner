/-
Copyright (c) 2026 Research07 contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Research07 contributors
-/

import Mathlib
import Research07.LRC3.Circ
import Research07.LRC4.IntCase

/-!# W5 — LRC(4) rational corollaries (FROZEN STATEMENTS)

Owned by agent W5 — fill the `sorry`s.
-/

noncomputable section

/-- Three nonzero rational relative speeds admit `t > 0` with all `circ (t·wᵢ) ≥ 1/4`.
Write `w i = b i / c` with `b i` nonzero integers and `c > 0` the common
denominator; the integer case gives `t₀` for `(|b i|)` and `t = c·t₀` works. -/
theorem lrc4_rel_rat (w : Fin 3 → ℚ) (hw : ∀ i, w i ≠ 0) :
    ∃ t : ℝ, 0 < t ∧ ∀ i, (1 / 4 : ℝ) ≤ circ (t * w i) := by
  -- `B`, the product of the denominators, clears every `w i` to an integer.
  set B : ℕ := ∏ i, (w i).den with hB
  have hBpos : 0 < B := Finset.prod_pos fun i _ => (w i).den_pos
  have hdvd : ∀ i, (w i).den ∣ B :=
    fun i => Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  -- `a i` is the integer `w i * B`.
  set a : Fin 3 → ℤ := fun i => (w i).num * ((B / (w i).den : ℕ) : ℤ) with ha
  -- Integrality: `w i * B = a i` in `ℚ`.
  have hqa : ∀ i : Fin 3, w i * (B : ℚ) = (a i : ℚ) := by
    intro i
    obtain ⟨k, hk⟩ := hdvd i
    have hdiv : B / (w i).den = k := by
      rw [hk]; exact Nat.mul_div_cancel_left _ (w i).den_pos
    simp only [ha, hdiv]
    rw [hk]
    push_cast
    rw [← mul_assoc, Rat.mul_den_eq_num]
  -- These integers are nonzero.
  have hane : ∀ i : Fin 3, a i ≠ 0 := by
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
  have hDcard : D.card ≤ 3 := Finset.card_image_le.trans (by simp)
  obtain ⟨t₀, ht₀, hDt⟩ := lrc4_int D hDpos hDcard
  refine ⟨t₀ * (B : ℝ), mul_pos ht₀ (by exact_mod_cast hBpos), fun i => ?_⟩
  -- `t₀·B·w i = t₀·a i`, and `circ` removes the sign of `a i`.
  have hcast : (w i : ℝ) * (B : ℝ) = (a i : ℝ) := by
    exact_mod_cast hqa i
  have hmem : (a i).natAbs ∈ D :=
    Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  have hsign : circ (t₀ * (a i : ℝ)) = circ (t₀ * ((a i).natAbs : ℝ)) := by
    conv_lhs => rw [← circ_abs, abs_mul, abs_of_pos ht₀, ← Int.cast_abs,
      ← Nat.cast_natAbs]
  rw [show t₀ * (B : ℝ) * (w i : ℝ) = t₀ * ((w i : ℝ) * (B : ℝ)) from by ring,
    hcast, hsign]
  exact hDt _ hmem

/-- Finset form (≤3 positive rationals) — the shape `BHK.lean` consumes. -/
theorem lrc4_rat_finset (S : Finset ℚ) (hpos : ∀ q ∈ S, 0 < q) (hcard : S.card ≤ 3) :
    ∃ t : ℝ, 0 < t ∧ ∀ q ∈ S, (1 / 4 : ℝ) ≤ circ (t * q) := by
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
  have hDcard : D.card ≤ 3 := Finset.card_image_le.trans hcard
  obtain ⟨t₀, ht₀, hDt⟩ := lrc4_int D hDpos hDcard
  refine ⟨t₀ * (B : ℝ), mul_pos ht₀ (by exact_mod_cast hBpos), fun q hq => ?_⟩
  have hmem : n q ∈ D := Finset.mem_image.mpr ⟨q, hq, rfl⟩
  have hcast : (q : ℝ) * (B : ℝ) = (n q : ℝ) := by
    exact_mod_cast hqa q hq
  rw [show t₀ * (B : ℝ) * (q : ℝ) = t₀ * ((q : ℝ) * (B : ℝ)) from by ring,
    hcast]
  exact hDt _ hmem

end
