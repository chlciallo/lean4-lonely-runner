/-
Copyright (c) 2026 Research07 contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Research07 contributors
-/
import Research07.LRC5.Filtering

/-!
# The integer case: four speeds, threshold `1/5`

Assembly of the Barajas–Serra argument (arXiv:0710.4495, §3) into the
integer-speeds theorem `lrc5_int`.

Level dichotomy for `|D| = 4`, `gcd D = 1`: `D(0)` and `D(m)` are nonempty,
so a middle level with `≥ 3` elements is impossible, and a low level with
`≥ 3` elements forces the residual shape `|D(0)| = 3`, `|D(m)| = 1` (with
no elements elsewhere). Generic shape → `filtered_multiplier` with `i₀ = m`.
Residual shape → the `ZMod 5` digit chase of `residual_case`.
-/

/-- **Residual case**: three units `A` plus one top-level element `d₄`.
Via sign flips `d ↦ N − d` (which preserve `|λd|_N`) we may assume the units
land in residue classes `{1,2}` mod 5; the `ZMod 5` digit chase of
Barajas–Serra §3 then produces `λ = j·(1 + k·5^m)` with all digits in
`{1,2,3}`, while `d₄` stays good automatically. -/
theorem residual_case {D : Finset ℕ} (hpos : ∀ d ∈ D, 0 < d) {m : ℕ}
    (hm : 0 < m) (h0 : (level D 0).card = 3) (hmtop : (level D m).card = 1)
    (hall : ∀ d ∈ D, padicValNat 5 d = 0 ∨ padicValNat 5 d = m) :
    ∃ lam : ℕ, ¬ 5 ∣ lam ∧
      ∀ d ∈ D, 5 ^ m ≤ absModN (lam * d) (5 ^ (m + 1)) := by
  sorry

/-- **Multiplier existence** for four coprime positive integers: some `λ`
coprime to `5` puts every element at circular distance `≥ 5^m` in `ℤ/N`,
`N = 5^{m+1}`, `m = max ν₅(D)`. Equivalent to `χ_r(N, D) ≤ 5`. -/
theorem exists_multiplier4 (D : Finset ℕ) (hpos : ∀ d ∈ D, 0 < d)
    (hgcd : D.gcd id = 1) (hcard : D.card = 4) :
    ∃ lam : ℕ, ¬ 5 ∣ lam ∧ ∀ d ∈ D,
      5 ^ (D.sup (padicValNat 5)) ≤
        absModN (lam * d) (5 ^ (D.sup (padicValNat 5) + 1)) := by
  sorry

/-- **Lonely runner, integer speeds, `|D| ≤ 4`**: any set of at most four
positive integers has a common lonely time `t > 0` at distance `≥ 1/5`.
(Pad `D` to four elements, divide out the gcd, apply `exists_multiplier4`,
bridge `t = λ/(g·5^{m+1})`.) -/
theorem lrc5_int (D : Finset ℕ) (hpos : ∀ d ∈ D, 0 < d) (hcard : D.card ≤ 4) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ D, (1 / 5 : ℝ) ≤ circ (t * d) := by
  sorry
