/-
Copyright (c) 2026 Research07 contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Research07 contributors
-/
import Research07.LRC3.Covering

/-!
# Two moving runners

The reduced form of the three-runner case: for positive real speeds `a, b`
there is a positive time `t` at which both `t·a` and `t·b` are at distance
`≥ 1/3` from the nearest integer.

Proof sketch (Wills 1967 / Cusick-style elementary argument):
* if `a = b`, take `t = 1/(2a)`;
* else assume `b < a`. If `a ≤ 2b`, then `t = 1/(3b)` works directly
  (`t·b = 1/3`, `t·a ∈ (1/3, 2/3]`); if `a > 2b`, then throughout
  `t ∈ [1/(3b), 2/(3b)]` we have `t·b ∈ [1/3, 2/3]`, while `t·a` sweeps an
  interval of length `a/(3b) > 2/3`, which contains a middle-third point by
  `covering`.
-/

/-- On the window `t ∈ [1/(3b), 2/(3b)]`, runner `b` stays lonely. -/
theorem lonely_on_window {b : ℝ} (hb : 0 < b) :
    ∀ t ∈ Set.Icc (1 / (3 * b)) (2 / (3 * b)), 1 / 3 ≤ circ (t * b) := by
  sorry

/-- The two-moving-runner theorem: a common lonely time always exists. -/
theorem two_moving {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∃ t, 0 < t ∧ 1 / 3 ≤ circ (t * a) ∧ 1 / 3 ≤ circ (t * b) := by
  sorry
