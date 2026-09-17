import Mathlib

/-!
# Scratch for W7c — Weyl-criterion route for flow Kronecker
Dev-only file (outside import tree).
-/

noncomputable section

open Set Filter Finset MeasureTheory UnitAddTorus
open scoped Topology Real

variable {d : ℕ}

#check @geom_sum_eq
#check @Complex.exp_nat_mul
#check @Complex.exp_eq_one_iff
#check @integral_eq_zero_of_add_right_eq_neg
#check @MeasureTheory.integral_fintype_prod_volume_eq_prod
#check @span_mFourier_closure_eq_top
#check @mFourier_apply
#check @fourier_coe_apply
#check @fourier_add_half_inv_index
#check @mFourier_zero
#check @mFourier_add
#check @Dense.mono
#check @IsOpen.measure_pos
#check @Submodule.span_induction
#check @Set.Countable
#check (inferInstance : IsAddHaarMeasure (volume : Measure (UnitAddTorus (Fin d))))
#check (inferInstance : IsProbabilityMeasure (volume : Measure (UnitAddTorus (Fin d))))
#check (inferInstance : Measure.IsAddRightInvariant (volume : Measure (UnitAddTorus (Fin d))))
