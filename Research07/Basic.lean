/-
Copyright (c) 2026 Research07 contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Research07 contributors
-/
import Mathlib

/-!
# Basic sanity-check results

A first small theorem to verify the Lean 4 + Mathlib toolchain end to end.
-/

/-- 前 n 个奇数之和等于 n² -/
theorem sum_odd_eq_sq (n : ℕ) :
    ∑ i ∈ Finset.range n, (2 * i + 1) = n ^ 2 := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    ring

-- 公理检查:只允许出现 propext / Classical.choice / Quot.sound
#print axioms sum_odd_eq_sq
