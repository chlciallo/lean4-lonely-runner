/-
Copyright (c) 2026 Research07 contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Research07 contributors
-/

import Mathlib
import Research07.LRC3.Circ
import Research07.M3.Relations
import Research07.M3.OrbitClosure

/-!# W9 — BHK Lemma 8 for n=5 (FROZEN STATEMENTS)

Equal-coordinates construction: `w ∈ Ker(A) ∩ ℚⁿ` with `wᵢ = −wⱼ`, all coordinates
nonzero; the (n−1)-runner rational hypothesis (`lrc4`) puts `t·w` in the open cube
`(δ,1−δ)ⁿ` with `δ ∈ (1/5, 1/4)`; `orbit_dense_annihilator` approximates by an orbit point.

Frozen contract for agent W9. Prove every `sorry`; do not change statements.
-/

noncomputable section

/-- **The equal-coordinates vector.** Given positive rational `r` and rational `s`
(not parallel to `r`), with `i` minimizing `sₖ/rₖ` and `j` maximizing it:
`w = (rᵢ+rⱼ)·s − (sᵢ+sⱼ)·r` satisfies `wᵢ = −wⱼ` and `wₖ ≠ 0` for all `k`. -/
theorem bhk_w_mem_kerSpanRat {n : ℕ} {u : Fin n → ℝ} {r s : Fin n → ℚ}
    (hr : r ∈ kerSpanRat u) (hs : s ∈ kerSpanRat u) {i j : Fin n} :
    ((r i + r j : ℚ) • s - (s i + s j : ℚ) • r) ∈ kerSpanRat u := by
  sorry

theorem bhk_w_eq_neg {n : ℕ} {r s : Fin n → ℚ} {i j : Fin n} :
    ((r i + r j : ℚ) • s - (s i + s j : ℚ) • r) i =
      -(((r i + r j : ℚ) • s - (s i + s j : ℚ) • r) j) := by
  sorry

theorem bhk_w_ne_zero {n : ℕ} {u : Fin n → ℝ} {r s : Fin n → ℚ}
    {i j : Fin n} (hrpos : ∀ k, 0 < r k)
    (hi : ∀ k, s k / r k ≤ s i / r i) (hj : ∀ k, s j / r j ≤ s k / r k)
    (hij : s i / r i < s j / r j) (k : Fin n) :
    ((r i + r j : ℚ) • s - (s i + s j : ℚ) • r) k ≠ 0 := by
  sorry

/-- **BHK Lemma 8 instantiated at n = 5.** If every ≤3-element set of positive
rationals admits a `1/4`-lonely time, then any 4 positive real speeds with an
irrational ratio admit a `t` with all `circ (t·uᵢ) > 1/5` (strict — slack from
`δ ∈ (1/5, 1/4)`). -/
theorem lrc5_real_of_irrational_ratio
    (hlrc4 : ∀ S : Finset ℚ, (∀ q ∈ S, 0 < q) → S.card ≤ 3 →
      ∃ t : ℝ, 0 < t ∧ ∀ q ∈ S, (1 / 4 : ℝ) ≤ circ (t * q))
    {u : Fin 4 → ℝ} (hpos : ∀ i, 0 < u i)
    (hirr : ¬ ∃ c : ℝ, ∀ i, ∃ q : ℚ, u i = c * q) :
    ∃ t : ℝ, 0 < t ∧ ∀ i, (1 / 5 : ℝ) < circ (t * u i) := by
  sorry

end
