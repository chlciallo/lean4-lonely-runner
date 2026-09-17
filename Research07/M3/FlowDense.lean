/-
Copyright (c) 2026 Research07 contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Research07 contributors
-/
import Mathlib
import Research07.M3.Dirichlet
import Research07.M3.Relations

/-!
# W7c — Flow Kronecker, the analytic core (FROZEN STATEMENT)

A one-parameter orbit `t ↦ (t·c₁, …, t·c_d)` on `T^d` is dense iff the direction
`c` is `ℚ`-linearly independent. Owned by agent W7c — fill the `sorry`s.

May use `Research07.M3.Dirichlet` (simultaneous Dirichlet, agent W7b) for the
return-time argument.
-/

noncomputable section

/-- **Flow Kronecker.** If `c : Fin d → ℝ` is `ℚ`-linearly independent, the
one-parameter orbit `t ↦ (t·c₁, …, t·c_d)` is dense in `T^d`. -/
theorem flow_orbit_dense {d : ℕ} {c : Fin d → ℝ} (hc : LinearIndependent ℚ c) :
    Dense (Set.range fun t : ℝ => fun i => ((t * c i : ℝ) : UnitAddCircle)) := by
  sorry

end
