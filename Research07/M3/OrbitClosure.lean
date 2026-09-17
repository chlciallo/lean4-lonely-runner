/-
Copyright (c) 2026 Research07 contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Research07 contributors
-/
import Mathlib
import Research07.M3.Relations
import Research07.M3.Subtorus
import Research07.M3.FlowDense

/-!
# W8 — Orbit-closure density, `⊇` direction (FROZEN STATEMENT)

Every point of the annihilator subtorus is a limit of orbit points `t·u mod ℤⁿ`:
pull `flow_orbit_dense` back through `subtorusMap` (basis of `kerSpanInt u`,
coordinates `c` of `u` are `ℚ`-independent by `kernel_coords_linearIndependent`).
Owned by agent W8 — fill the `sorry`s.
-/

noncomputable section

/-- Every annihilator point is approximable by the real orbit of `u`. -/
theorem orbit_dense_annihilator {n : ℕ} (u : Fin n → ℝ) :
    annihilator u ⊆
      closure (Set.range fun t : ℝ => fun i => ((t * u i : ℝ) : UnitAddCircle)) := by
  sorry

end
