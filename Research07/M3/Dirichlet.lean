/-
Copyright (c) 2026 Research07 contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Research07 contributors
-/
import Mathlib

/-!
# Simultaneous Dirichlet approximation on the torus

The classical **box-pigeonhole** form of Dirichlet's simultaneous approximation
theorem, packaged on the torus `𝕋ᵈ = (ℝ ⧸ ℤ)ᵈ = Fin d → UnitAddCircle`. Downstream
consumer: the flow–Kronecker density lemma (return-time argument) of phase M3.

The pigeonhole core is ported (and adapted) from
`_external/five-distance-sharp/ThreeGap/SimultaneousDirichlet.lean`
(© Vico Bonfioli, Apache 2.0) and the defect API `rem`/`delta` from
`ThreeGap/SimultaneousApprox.lean` (same licence); the `delta`/`rem` API is kept
for downstream use. Among the `Q^d + 1` points `{i • α mod ℤᵈ : 0 ≤ i ≤ Q^d}`,
two share one of the `Q^d` sub-boxes of side `1/Q`; their index difference `q`
has all coordinates within `1/Q` of an integer.

* `SimDirichlet.exists_delta_lt_inv` / `SimDirichlet.exists_delta_lt`: the
  real-vector Dirichlet theorem, in terms of the defect
  `SimDirichlet.delta α q = ⨅ p : Fin d → ℤ, ‖rem α q p‖` (sup norm).
* `SimDirichlet.norm_zsmul_le_delta`: the bridge — for `x i = ↑(α i)` the circle
  norm `‖(q : ℤ) • x i‖ = |q·αᵢ − round (q·αᵢ)|` is bounded by every integer
  translate `|rem α q p i|`, hence by `delta α q`.
* `exists_forall_norm_zsmul_lt`, `exists_forall_norm_zsmul_lt_inv`: the two
  packaged torus statements.
-/

namespace SimDirichlet

variable {d : ℕ}

/-! ## The approximation defect `delta` (ported from `ThreeGap.SimultaneousApprox`) -/

/-- The integer-vector translate of `q • α` by `p`, as an element of `Fin d → ℝ`.
Its norm over all `p ∈ ℤᵈ` is minimised at the best simultaneous approximation. -/
noncomputable def rem (α : Fin d → ℝ) (q : ℤ) (p : Fin d → ℤ) : Fin d → ℝ :=
  (q : ℝ) • α - (fun k => (p k : ℝ))

/-- The **approximation defect** `δ_q = inf_{p ∈ ℤᵈ} ‖q • α − p‖`. -/
noncomputable def delta (α : Fin d → ℝ) (q : ℤ) : ℝ :=
  ⨅ p : Fin d → ℤ, ‖rem α q p‖

/-- The range of `p ↦ ‖rem α q p‖` is bounded below (by `0`), so the infimum is genuine. -/
theorem bddBelow_rem (α : Fin d → ℝ) (q : ℤ) :
    BddBelow (Set.range fun p : Fin d → ℤ => ‖rem α q p‖) :=
  ⟨0, by rintro _ ⟨p, rfl⟩; exact norm_nonneg _⟩

/-- `δ_q` is a lower bound for every concrete approximation: `δ_q ≤ ‖q • α − p‖`. -/
theorem delta_le (α : Fin d → ℝ) (q : ℤ) (p : Fin d → ℤ) : delta α q ≤ ‖rem α q p‖ :=
  ciInf_le (bddBelow_rem α q) p

/-- `δ_q ≥ 0`. -/
theorem delta_nonneg (α : Fin d → ℝ) (q : ℤ) : 0 ≤ delta α q :=
  le_ciInf fun _p => norm_nonneg _

/-! ## Dirichlet via the box pigeonhole (ported from `ThreeGap.SimultaneousDirichlet`) -/

/-- The box index of the point `i • α` in direction `k`, at resolution `Q`:
`⌊{i αₖ}·Q⌋ ∈ {0,…,Q−1}`, packaged as `Fin Q`. -/
noncomputable def box (α : Fin d → ℝ) (Q : ℕ) (hQ : 1 ≤ Q) (i : ℕ) : Fin d → Fin Q :=
  fun k => ⟨(⌊Int.fract ((i : ℝ) * α k) * Q⌋).toNat, by
    have hfr : Int.fract ((i : ℝ) * α k) < 1 := Int.fract_lt_one _
    have hfr0 : 0 ≤ Int.fract ((i : ℝ) * α k) := Int.fract_nonneg _
    have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQ
    have hlt : Int.fract ((i : ℝ) * α k) * Q < Q := by nlinarith
    have hub : ⌊Int.fract ((i : ℝ) * α k) * Q⌋ < (Q : ℤ) := by
      exact_mod_cast lt_of_le_of_lt (Int.floor_le _) hlt
    have hge : 0 ≤ ⌊Int.fract ((i : ℝ) * α k) * Q⌋ :=
      Int.floor_nonneg.mpr (mul_nonneg (Int.fract_nonneg _) (by positivity))
    omega⟩

/-- **Dirichlet's simultaneous approximation theorem (inverse-resolution form).** For `Q ≥ 1`
there is a denominator `1 ≤ q ≤ Q^d` with `delta α q < 1/Q`. -/
theorem exists_delta_lt_inv (α : Fin d → ℝ) (Q : ℕ) (hQ : 1 ≤ Q) :
    ∃ q : ℕ, 1 ≤ q ∧ q ≤ Q ^ d ∧ delta α q < 1 / Q := by
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQ
  -- pigeonhole: two of the Q^d + 1 points share a box
  have hcard : (Finset.univ : Finset (Fin d → Fin Q)).card < (Finset.range (Q ^ d + 1)).card := by
    rw [Finset.card_range, Finset.card_univ, Fintype.card_pi]
    simp only [Fintype.card_fin, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact Nat.lt_succ_self _
  obtain ⟨i₀, hi₀, j₀, hj₀, hij, hbox₀⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard
      (fun a _ => Finset.mem_univ (box α Q hQ a))
  rw [Finset.mem_range] at hi₀ hj₀
  -- orient the pair so that `i < j`
  obtain ⟨i, j, hlt, hjQd, hbox⟩ :
      ∃ i j, i < j ∧ j ≤ Q ^ d ∧ box α Q hQ i = box α Q hQ j := by
    rcases lt_or_gt_of_ne hij with h | h
    · exact ⟨i₀, j₀, h, Nat.lt_succ_iff.mp hj₀, hbox₀⟩
    · exact ⟨j₀, i₀, h, Nat.lt_succ_iff.mp hi₀, hbox₀.symm⟩
  -- the integer translate: M k = ⌊j αₖ⌋ − ⌊i αₖ⌋
  set q : ℕ := j - i with hq
  refine ⟨q, by omega, le_trans (Nat.sub_le j i) hjQd, ?_⟩
  set M : Fin d → ℤ := fun k => ⌊(j : ℝ) * α k⌋ - ⌊(i : ℝ) * α k⌋ with hM
  -- each coordinate of the remainder is the fractional-part difference, hence `< 1/Q`
  have hcoord : ∀ k, |rem α (q : ℤ) M k| < 1 / Q := by
    intro k
    have hboxk : (box α Q hQ i k : ℕ) = (box α Q hQ j k : ℕ) := by rw [hbox]
    simp only [box] at hboxk
    have hfloor : ⌊Int.fract ((i : ℝ) * α k) * Q⌋ = ⌊Int.fract ((j : ℝ) * α k) * Q⌋ := by
      have hi0 : 0 ≤ ⌊Int.fract ((i : ℝ) * α k) * Q⌋ :=
        Int.floor_nonneg.mpr (mul_nonneg (Int.fract_nonneg _) (by positivity))
      have hj0 : 0 ≤ ⌊Int.fract ((j : ℝ) * α k) * Q⌋ :=
        Int.floor_nonneg.mpr (mul_nonneg (Int.fract_nonneg _) (by positivity))
      omega
    have habs : |Int.fract ((i : ℝ) * α k) * Q - Int.fract ((j : ℝ) * α k) * Q| < 1 :=
      Int.abs_sub_lt_one_of_floor_eq_floor hfloor
    -- rem coordinate = fract(j αₖ) − fract(i αₖ)
    have hrem : rem α (q : ℤ) M k = Int.fract ((j : ℝ) * α k) - Int.fract ((i : ℝ) * α k) := by
      simp only [rem, hM, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Int.fract]
      rw [hq, Nat.cast_sub hlt.le]
      push_cast
      ring
    -- |fract(j) − fract(i)| = (1/Q)·|fract(i)·Q − fract(j)·Q| < 1/Q
    have heq : |Int.fract ((i : ℝ) * α k) * Q - Int.fract ((j : ℝ) * α k) * Q|
        = (Q : ℝ) * |Int.fract ((j : ℝ) * α k) - Int.fract ((i : ℝ) * α k)| := by
      rw [← sub_mul, abs_mul, abs_of_pos hQ0, abs_sub_comm, mul_comm]
    have hkey : (Q : ℝ) * |Int.fract ((j : ℝ) * α k) - Int.fract ((i : ℝ) * α k)| < 1 :=
      heq ▸ habs
    rw [hrem, lt_div_iff₀ hQ0, mul_comm]
    exact hkey
  -- so `delta α q ≤ ‖rem α q M‖ < 1/Q`
  calc delta α (q : ℤ) ≤ ‖rem α (q : ℤ) M‖ := delta_le α (q : ℤ) M
    _ < 1 / Q := by
        rw [pi_norm_lt_iff (by positivity)]
        intro k
        rw [Real.norm_eq_abs]
        exact hcoord k

/-- **Dirichlet's theorem (ε form).** For every `ε > 0` there is `q ≥ 1` with `delta α q < ε`. -/
theorem exists_delta_lt (α : Fin d → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ q : ℕ, 1 ≤ q ∧ delta α q < ε := by
  obtain ⟨Q, hQ⟩ := exists_nat_gt (1 / ε)
  have hQ1 : 1 ≤ Q := by
    by_contra h
    push Not at h
    interval_cases Q
    · simp only [Nat.cast_zero] at hQ; exact absurd hQ (not_lt.mpr (by positivity))
  obtain ⟨q, hq1, -, hq2⟩ := exists_delta_lt_inv α Q hQ1
  refine ⟨q, hq1, lt_of_lt_of_le hq2 ?_⟩
  rw [div_le_iff₀ (by exact_mod_cast hQ1 : (0 : ℝ) < Q)]
  rw [div_lt_iff₀ hε] at hQ
  nlinarith [hQ]

/-! ## Bridge to `UnitAddCircle` -/

/-- Every point of `UnitAddCircle` is the image of a real representative. -/
theorem exists_coe_eq (x : UnitAddCircle) : ∃ a : ℝ, (a : UnitAddCircle) = x := by
  obtain ⟨a, ha⟩ := QuotientAddGroup.mk'_surjective (zmultiples (1 : ℝ)) x
  exact ⟨a, by simpa using ha⟩

/-- Each coordinate of `(q : ℤ) • x` on `UnitAddCircle` has norm bounded by the defect:
`‖q • x i‖ = |q αᵢ − round (q αᵢ)| ≤ |rem α q p i|` for every integer translate `p`,
hence `≤ delta α q = ⨅ p, ‖rem α q p‖`. -/
theorem norm_zsmul_le_delta (x : Fin d → UnitAddCircle) (α : Fin d → ℝ)
    (hα : ∀ i, ((α i : ℝ) : UnitAddCircle) = x i) (q : ℤ) (i : Fin d) :
    ‖q • x i‖ ≤ delta α q := by
  refine le_ciInf fun p => ?_
  calc ‖q • x i‖ = ‖q • ((α i : ℝ) : UnitAddCircle)‖ := by rw [← hα i]
    _ = ‖((q • α i : ℝ) : UnitAddCircle)‖ := by rw [AddCircle.coe_zsmul]
    _ = |q • α i - round (q • α i)| := UnitAddCircle.norm_eq
    _ ≤ |q • α i - (p i : ℝ)| := round_le _ _
    _ = ‖rem α q p i‖ := by
        rw [Real.norm_eq_abs]
        simp only [rem, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, zsmul_eq_mul]
    _ ≤ ‖rem α q p‖ := norm_le_pi_norm _ i

end SimDirichlet

open SimDirichlet in
/-- Simultaneous Dirichlet: a common denominator making all coordinates small. -/
theorem exists_forall_norm_zsmul_lt {d : ℕ} (x : Fin d → UnitAddCircle)
    {ε : ℝ} (hε : 0 < ε) : ∃ q : ℕ, 0 < q ∧ ∀ i, ‖(q : ℤ) • x i‖ < ε := by
  choose α hα using fun i : Fin d => exists_coe_eq (x i)
  obtain ⟨q, hq1, hdel⟩ := exists_delta_lt α hε
  exact ⟨q, hq1, fun i => lt_of_le_of_lt (norm_zsmul_le_delta x α hα (q : ℤ) i) hdel⟩

open SimDirichlet in
/-- Quantitative version with denominator bound. -/
theorem exists_forall_norm_zsmul_lt_inv {d : ℕ} (x : Fin d → UnitAddCircle)
    (Q : ℕ) (hQ : 1 ≤ Q) : ∃ q : ℕ, 1 ≤ q ∧ q ≤ Q ^ d ∧ ∀ i, ‖(q : ℤ) • x i‖ ≤ 1 / Q := by
  choose α hα using fun i : Fin d => exists_coe_eq (x i)
  obtain ⟨q, hq1, hqQ, hdel⟩ := exists_delta_lt_inv α Q hQ
  exact ⟨q, hq1, hqQ, fun i => (norm_zsmul_le_delta x α hα (q : ℤ) i).trans hdel.le⟩
