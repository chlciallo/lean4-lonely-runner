/-
Copyright (c) 2026 Research07 contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Research07 contributors
-/
import Mathlib
import Research07.M3.Dirichlet
import Research07.M3.Relations
import Research07.M3.FlowDenseAux

/-!
# W7c — Flow Kronecker, the analytic core (FROZEN STATEMENT)

A one-parameter orbit `t ↦ (t·c₁, …, t·c_d)` on `T^d` is dense iff the direction
`c` is `ℚ`-linearly independent. Owned by agent W7c.

## Proof sketch

Pick a nonzero coordinate `c j` (it exists whenever `d ≥ 1`, since linear
independence forces each `c i ≠ 0`). To approximate a target `x` in the torus,
first choose `r : ℝ` with `↑r = x j` and set `t₀ = r / c j`, so the flow hits
`x j` exactly at time `t₀`. The shifted target `z i = x i - ↑(t₀ * c i)` then
lies in the subtorus `{z | z j = 0}`.

On that subtorus the return times `t₀ + m / c j` act as the integer rotation
`m ↦ m • (c i / c j)`. The `ℚ`-linear independence of `c` gives the
`{1} ∪ {c i / c j}` no-relation hypothesis of `FlowKronecker.denseRange_zsmul`
(`FlowDenseAux.lean`), so the discrete orbit is dense in the subtorus, and one
`m` gives `t = t₀ + m / c j` with `dist (t·c) x < ε`.
-/

noncomputable section

open Finset

/-- **Flow Kronecker.** If `c : Fin d → ℝ` is `ℚ`-linearly independent, the
one-parameter orbit `t ↦ (t·c₁, …, t·c_d)` is dense in `T^d`. -/
theorem flow_orbit_dense {d : ℕ} {c : Fin d → ℝ} (hc : LinearIndependent ℚ c) :
    Dense (Set.range fun t : ℝ => fun i => ((t * c i : ℝ) : UnitAddCircle)) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · -- `Fin 0 → UnitAddCircle` is a subsingleton, so the range is everything.
    have huniv : (Set.range fun t : ℝ => fun i => ((t * c i : ℝ) : UnitAddCircle)) =
        Set.univ := by
      rw [Set.eq_univ_iff_forall]
      intro x
      exact ⟨(0 : ℝ), Subsingleton.elim _ _⟩
    rw [huniv]
    exact dense_univ
  · classical
    set j : Fin d := ⟨0, hd⟩
    have hcj : c j ≠ 0 := hc.ne_zero j
    rw [dense_iff_inter_open]
    intro U hU hUn
    rcases hUn with ⟨x, hxU⟩
    rcases Metric.isOpen_iff.mp hU x hxU with ⟨ε, hε, hball⟩
    -- lift `x j` to a real `r`; then `t₀ = r / c j` hits `x j` exactly.
    obtain ⟨r, hr⟩ :=
      QuotientAddGroup.mk'_surjective (AddSubgroup.zmultiples (1 : ℝ)) (x j)
    rw [QuotientAddGroup.mk'_apply] at hr
    -- `{1} ∪ {c i / c j}` has no integer relation (for `i ≠ j`).
    have hLI : ∀ k : ({i : Fin d // i ≠ j}) → ℤ, ∀ n : ℤ,
        (∑ i, (k i : ℝ) * (c (i : Fin d) / c j)) = (n : ℝ) → ∀ i, k i = 0 := by
      intro k n hkn
      -- clear the denominator `c j`
      have h1 : (∑ i : {i : Fin d // i ≠ j}, (k i : ℝ) * c (i : Fin d)) =
          (n : ℝ) * c j := by
        have hsum : (∑ i : {i : Fin d // i ≠ j}, (k i : ℝ) * (c (i : Fin d) / c j)) =
            (∑ i : {i : Fin d // i ≠ j}, (k i : ℝ) * c (i : Fin d)) / c j := by
          simp only [← mul_div_assoc]
          rw [← Finset.sum_div]
        rw [hsum] at hkn
        exact (div_eq_iff hcj).mp hkn
      -- package as a `ℚ`-relation on `c`
      set g : Fin d → ℚ :=
        fun i => if h : i = j then (-(n : ℚ)) else (k ⟨i, h⟩ : ℚ) with hgdef
      have h2 : (∑ i : Fin d, (g i : ℝ) * c i) = 0 := by
        rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ j)]
        have hgerase : (∑ i ∈ Finset.univ.erase j, (g i : ℝ) * c i) =
            ∑ i : {i : Fin d // i ≠ j}, (k i : ℝ) * c (i : Fin d) := by
          rw [Finset.sum_subtype (p := fun i => i ≠ j) (Finset.univ.erase j)
            (fun i => by simp) (fun i => (g i : ℝ) * c i)]
          refine Finset.sum_congr rfl fun i _ => ?_
          simp only [hgdef, dite_eq_right i.prop]
          norm_cast
        rw [hgerase, h1]
        have hgj : (g j : ℝ) = -(n : ℝ) := by simp [hgdef]
        rw [hgj]
        ring
      have hQ : (∑ i : Fin d, g i • c i) = 0 := by
        simp only [Rat.smul_def]
        exact h2
      have hg0 : ∀ i : Fin d, g i = 0 := Fintype.linearIndependent_iff.mp hc g hQ
      intro i
      have hgi := hg0 i.val
      simp only [hgdef, dite_eq_right i.prop] at hgi
      exact_mod_cast hgi
    -- the discrete return-time orbit is dense in the subtorus `{z | z j = 0}`
    have hdense := FlowKronecker.denseRange_zsmul
      (ι := {i : Fin d // i ≠ j}) (α := fun i => c (i : Fin d) / c j) hLI
    rcases hdense.exists_dist_lt (fun i : {i : Fin d // i ≠ j} =>
        x (i : Fin d) - ((r / c j * c (i : Fin d) : ℝ) : UnitAddCircle)) hε
      with ⟨m, hm⟩
    -- the approximating flow time
    refine ⟨fun i => (((r / c j) + (m : ℝ) / c j) * c i : UnitAddCircle), ?_, ?_⟩
    · apply hball
      rw [Metric.mem_ball, dist_pi_lt_iff hε]
      intro i
      have hdec : ((r / c j + (m : ℝ) / c j) * c i : ℝ) =
          (r / c j) * c i + (m : ℝ) * (c i / c j) := by ring
      rw [hdec, AddCircle.coe_add]
      by_cases hi : i = j
      · subst hi
        have hTj : ((r / c j * c j : ℝ) : UnitAddCircle) = x j := by
          rw [div_mul_cancel₀ _ hcj]
          exact hr
        have hMj : (((m : ℝ) * (c j / c j) : ℝ) : UnitAddCircle) = 0 := by
          rw [div_self hcj, mul_one, AddCircle.coe_eq_zero_iff]
          exact ⟨m, by simp⟩
        rw [hTj, hMj, add_zero, dist_self]
        exact hε
      · have heq : ((r / c j * c i : ℝ) : UnitAddCircle) +
            (((m : ℝ) * (c i / c j) : ℝ) : UnitAddCircle) - x i =
            (((m : ℝ) * (c i / c j) : ℝ) : UnitAddCircle) -
              (x i - ((r / c j * c i : ℝ) : UnitAddCircle)) := by abel
        rw [dist_eq_norm, heq, ← dist_eq_norm, dist_comm]
        exact (dist_pi_lt_iff hε).mp hm ⟨i, hi⟩
    · exact ⟨(r / c j) + (m : ℝ) / c j, rfl⟩

end
