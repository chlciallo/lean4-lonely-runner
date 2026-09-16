/-
Copyright (c) 2026 Research07 contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Research07 contributors
-/
import Research07.LRC3.Circ

/-!
# The covering lemma

Every real interval of length `> 2/3` contains a point at distance `≥ 1/3`
from the nearest integer. Proof sketch (Phase-0 literature): with
`k₀ = ⌈x − 2/3⌉`, the point `ξ = max (k₀ + 1/3) x` lies in
`[x, x + L] ∩ [k₀ + 1/3, k₀ + 2/3]`.
-/

/-- Covering lemma: `[x, x + L]` with `L > 2/3` meets `{ξ | 1/3 ≤ circ ξ}`. -/
theorem covering {x L : ℝ} (hL : 2 / 3 < L) :
    ∃ ξ ∈ Set.Icc x (x + L), 1 / 3 ≤ circ ξ := by
  -- Take `k₀ = ⌈x - 2/3⌉`, so `x - 2/3 ≤ k₀` and `k₀ < x - 2/3 + 1 = x + 1/3`.
  obtain ⟨k₀, hk₀⟩ : ∃ k : ℤ, x - 2 / 3 ≤ (k : ℝ) ∧ (k : ℝ) < x - 2 / 3 + 1 :=
    ⟨⌈x - 2 / 3⌉, Int.le_ceil _, Int.ceil_lt_add_one _⟩
  -- The witness is `ξ = max (k₀ + 1/3) x`.
  refine ⟨max ((k₀ : ℝ) + 1 / 3) x, ⟨le_max_right _ _, ?_⟩, ?_⟩
  · -- `ξ ≤ x + L`: `k₀ + 1/3 < x + 2/3 < x + L` and `x ≤ x + L`.
    rw [max_le_iff]
    exact ⟨by linarith [hk₀.2], by linarith⟩
  · -- `ξ ∈ Icc (k₀ + 1/3) (k₀ + 2/3)`, hence `1/3 ≤ circ ξ`.
    rw [circ_ge_third_iff]
    exact ⟨k₀, ⟨le_max_left _ _, max_le (by linarith) (by linarith [hk₀.1])⟩⟩
