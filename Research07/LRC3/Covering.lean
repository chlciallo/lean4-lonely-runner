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
  sorry
