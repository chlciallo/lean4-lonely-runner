/-
Copyright (c) 2026 Research07 contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Research07 contributors
-/
import Mathlib
import Research07.M3.Relations

/-!
# W7a — Subtorus parametrization (FROZEN STATEMENTS)

The annihilator `annihilator u` is the image of a torus under the integer matrix
built from a `ℤ`-basis of `kerSpanInt u`. Owned by agent W7a — fill the `sorry`s.
-/

noncomputable section

/-- The subtorus map of an integer matrix `ρ : Fin d → Fin n → ℤ`:
`x ↦ (i ↦ ∑ ℓ, ρ ℓ i • x ℓ)`, an additive homomorphism `T^d → Tⁿ`. -/
def subtorusMap {n d : ℕ} (ρ : Fin d → Fin n → ℤ) :
    (Fin d → UnitAddCircle) →+ (Fin n → UnitAddCircle) where
  toFun x := fun i => ∑ ℓ, (ρ ℓ i) • x ℓ
  map_zero' := by
    ext i
    simp
  map_add' := by
    intro x y
    ext i
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    congr 1
    ext ℓ
    rw [zsmul_add]

theorem subtorusMap_continuous {n d : ℕ} (ρ : Fin d → Fin n → ℤ) :
    Continuous (subtorusMap ρ) := by
  sorry

/-- If `ρ` is a `ℤ`-basis (as columns) of `kerSpanInt u`, the image of
`subtorusMap ρ` is exactly the annihilator of `u`. -/
theorem subtorusMap_range_eq_annihilator {n d : ℕ} (u : Fin n → ℝ) (ρ : Fin d → Fin n → ℤ)
    (hspan : ∀ x : Fin n → ℤ, x ∈ kerSpanInt u →
      x ∈ Submodule.span ℤ (Set.range ρ))
    (hmem : ∀ ℓ, (ρ ℓ) ∈ kerSpanInt u)
    (hinj : LinearIndependent ℤ ρ) :
    Set.range (subtorusMap ρ) = annihilator u := by
  sorry

end
