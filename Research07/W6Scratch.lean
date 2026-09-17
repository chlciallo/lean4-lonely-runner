import Mathlib
import Research07.M3.Relations

/-!
Scratch: countermodel to `kernel_coords_linearIndependent` as stated.
n=3, d=2, u = ![1,1,0], ρ = ![![0,0,1],![1,1,1]], c = ![-1,1].
-/

noncomputable section

open Finset Matrix

private def cmU : Fin 3 → ℝ := ![1, 1, 0]
private def cmRho : Fin 2 → Fin 3 → ℚ := ![![0, 0, 1], ![1, 1, 1]]
private def cmC : Fin 2 → ℝ := ![-1, 1]

example : (∀ x : Fin 3 → ℚ, x ∈ kerSpanRat cmU →
      x ∈ Submodule.span ℚ (Set.range cmRho)) := by
  intro x hx
  have h1 : ![0, 0, 1] ∈ relLattice cmU := by
    rw [relLattice, LinearMap.mem_ker, Fintype.linearCombination_apply]
    simp [Fin.sum_univ_three, cmU]
  have h2 : ![1, -1, 0] ∈ relLattice cmU := by
    rw [relLattice, LinearMap.mem_ker, Fintype.linearCombination_apply]
    simp [Fin.sum_univ_three, cmU]
  have hx1 := hx ![0, 0, 1] h1
  have hx2 := hx ![1, -1, 0] h2
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two] at hx1 hx2
  have hx1' : x 2 = 0 := by simp at hx1 ⊢; exact hx1
  have hx2' : x 0 = x 1 := by simp at hx2; linarith
  have hxeq : x = (x 0) • cmRho 1 - (x 0) • cmRho 0 := by
    ext i
    fin_cases i
    · simp [cmRho]
    · simp [cmRho, hx2']
    · simp [cmRho, hx1']
  rw [hxeq]
  exact sub_mem
    (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self 1)))
    (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self 0)))

example : (∀ i : Fin 3, cmU i = ∑ ℓ : Fin 2, cmC ℓ * (cmRho ℓ i : ℝ)) := by
  intro i
  fin_cases i <;> simp [Fin.sum_univ_two, cmU, cmC, cmRho] <;> norm_num

example : ¬ LinearIndependent ℚ cmC := by
  rw [Fintype.linearIndependent_iff]
  intro h
  have hk : ∑ i : Fin 2, (![(1 : ℚ), 1] i) • cmC i = 0 := by
    simp [Fin.sum_univ_two, cmC]
  have h00 := h ![1, 1] hk 0
  simp at h00

end
