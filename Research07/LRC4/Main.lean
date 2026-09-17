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

/-- Three nonzero rational relative speeds admit `t > 0` with all `circ (t·wᵢ) ≥ 1/4`. -/
theorem lrc4_rel_rat (w : Fin 3 → ℚ) (hw : ∀ i, w i ≠ 0) :
    ∃ t : ℝ, 0 < t ∧ ∀ i, (1 / 4 : ℝ) ≤ circ (t * w i) := by
  sorry

/-- Finset form (≤3 positive rationals) — the shape `BHK.lean` consumes. -/
theorem lrc4_rat_finset (S : Finset ℚ) (hpos : ∀ q ∈ S, 0 < q) (hcard : S.card ≤ 3) :
    ∃ t : ℝ, 0 < t ∧ ∀ q ∈ S, (1 / 4 : ℝ) ≤ circ (t * q) := by
  sorry

end
