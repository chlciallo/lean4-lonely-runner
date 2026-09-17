/-
Copyright (c) 2026 Research07 contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Research07 contributors
-/
import Mathlib

/-!
# W7c auxiliary — discrete Kronecker density on the torus via ergodicity

The analytic kernel for `flow_orbit_dense`: if `{1} ∪ α` has no nontrivial
integer relation, the integer multiples `n • α` are dense in `T^ι`.

Proof sketch: the translation `x ↦ a + x` on the compact group `UnitAddTorus ι`
preserves Haar measure. If `s` is a measurable invariant set, its indicator `f`
has Fourier coefficients `f̂ k = f̂ k · mFourier (-k) a`. By hypothesis no
character `mFourier k` with `k ≠ 0` satisfies `mFourier k a = 1` (that would be
an integer relation `∑ kᵢ αᵢ = n`), so `f̂` is supported on `{0}`, `f` is a.e.
constant, and `s` is a.e. empty or full. Hence the translation is ergodic, and
`ergodic_add_left_iff_denseRange_zsmul` turns this into density of multiples.
-/

noncomputable section

open MeasureTheory Filter Set UnitAddTorus
open scoped ComplexConjugate

-- the `mFourier` API (`Mathlib.Analysis.Fourier.AddCircleMulti`) is stated with
-- respect to these local instances: `volume` on `UnitAddCircle` = `haarAddCircle`
-- (total mass 1), not the global `AddCircle.measureSpace` (total mass `T`).
-- We replicate them so `volume` unifies.
/-- In this file we normalise the measure on `ℝ / ℤ` to have total volume 1. -/
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

/-- The measure on `ℝ / ℤ` is a Haar measure. -/
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

/-- The measure on `ℝ / ℤ` is a probability measure. -/
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace FlowKronecker

variable {ι : Type*} [Fintype ι]

/-- `mFourier n` is multiplicative in the torus variable. -/
lemma mFourier_apply_add (n : ι → ℤ) (x y : UnitAddTorus ι) :
    mFourier n (x + y) = mFourier n x * mFourier n y := by
  simp only [mFourier, ContinuousMap.coe_mk, Pi.add_apply, fourier_apply, smul_add,
    AddCircle.toCircle_add, Circle.coe_mul, ← Finset.prod_mul_distrib]

/-- The complex value of `mFourier k a` is `toCircle` of the dot product
`∑ i, k i • a i` (sum taken in `UnitAddCircle`). -/
lemma mFourier_apply_eq_toCircle (k : ι → ℤ) (a : UnitAddTorus ι) :
    mFourier k a = (AddCircle.toCircle (∑ i, (k i) • a i) : ℂ) := by
  classical
  have hprod : ∀ s : Finset ι,
      ((AddCircle.toCircle (∑ i ∈ s, (k i) • a i) : Circle) : ℂ) =
        ∏ i ∈ s, ((AddCircle.toCircle ((k i) • a i) : Circle) : ℂ) := by
    intro s
    induction s using Finset.induction with
    | empty => simp
    | @insert i s hi ih =>
        rw [Finset.sum_insert hi, AddCircle.toCircle_add, Circle.coe_mul, ih,
          Finset.prod_insert hi]
  rw [hprod Finset.univ]
  rfl

/-- If `{1} ∪ α` has no integer relations, no nontrivial character of the torus
fixes `a i = α i mod 1`: `mFourier k a = 1` would give a relation
`∑ i, k i * α i = n`. -/
lemma mFourier_ne_one {α : ι → ℝ}
    (hα : ∀ k : ι → ℤ, ∀ n : ℤ, (∑ i, (k i : ℝ) * α i) = (n : ℝ) → ∀ i, k i = 0)
    {k : ι → ℤ} (hk : k ≠ 0) :
    mFourier k (fun i => ((α i : ℝ) : UnitAddCircle)) ≠ 1 := by
  classical
  rw [mFourier_apply_eq_toCircle]
  intro h
  have h1 : AddCircle.toCircle (∑ i, (k i) • ((α i : ℝ) : UnitAddCircle)) = 1 :=
    Circle.coe_eq_one.mp h
  have hzero : (∑ i, (k i) • ((α i : ℝ) : UnitAddCircle)) = 0 := by
    have hinj := AddCircle.injective_toCircle (one_ne_zero : (1 : ℝ) ≠ 0)
    rw [← AddCircle.toCircle_zero] at h1
    exact hinj h1
  -- rewrite the torus sum as the coercion of a real sum
  have hsum_coe : ∀ s : Finset ι, ∀ β : ι → ℝ,
      ((∑ i ∈ s, β i : ℝ) : UnitAddCircle) =
        ∑ i ∈ s, ((β i : ℝ) : UnitAddCircle) := by
    intro s β
    induction s using Finset.induction with
    | empty => simp
    | @insert i s hi ih =>
        rw [Finset.sum_insert hi, Finset.sum_insert hi, AddCircle.coe_add, ih]
  have hrel : ((∑ i, (k i : ℝ) * α i : ℝ) : UnitAddCircle) = 0 := by
    rw [hsum_coe]
    convert hzero using 3
    rw [← AddCircle.coe_zsmul, zsmul_eq_mul]
  rw [AddCircle.coe_eq_zero_iff] at hrel
  obtain ⟨n, hn⟩ := hrel
  rw [zsmul_eq_mul, mul_one] at hn
  exact hk (funext fun i => hα k n hn.symm i)

/-- A rotation `x ↦ a + x` of the torus is ergodic for Haar measure whenever no
nontrivial character fixes `a`. -/
lemma ergodic_add_left_torus (a : UnitAddTorus ι)
    (ha : ∀ k : ι → ℤ, k ≠ 0 → mFourier k a ≠ 1) :
    Ergodic (a + ·) (volume : Measure (UnitAddTorus ι)) := by
  classical
  refine ⟨measurePreserving_add_left volume a, ⟨fun s => ?_⟩⟩
  intro hs hinv
  -- the L² indicator of `s`
  have hμs : (volume : Measure (UnitAddTorus ι)) s ≠ ⊤ :=
    (measure_lt_top _ _).ne
  set f : UnitAddTorus ι → ℂ := s.indicator fun _ => 1 with hf
  set g : Lp ℂ 2 (volume : Measure (UnitAddTorus ι)) := indicatorConstLp 2 hs hμs 1
  have hgf : (g : UnitAddTorus ι → ℂ) =ᵐ[volume] f := indicatorConstLp_coeFn
  -- invariance of `s` gives invariance of `f`, pointwise
  have hfinv : ∀ x : UnitAddTorus ι, f (a + x) = f x := by
    intro x
    have hmem : (a + x ∈ s) ↔ (x ∈ s) := Set.ext_iff.mp hinv x
    simp only [hf, Set.indicator_apply, hmem]
  -- Fourier coefficients satisfy `f̂ k = mFourier (-k) a * f̂ k`
  have hcoeff : ∀ k : ι → ℤ,
      mFourierCoeff (g : UnitAddTorus ι → ℂ) k =
        mFourier (-k) a * mFourierCoeff (g : UnitAddTorus ι → ℂ) k := by
    intro k
    have hgf' : (fun t => mFourier (-k) t • (g : UnitAddTorus ι → ℂ) t) =ᵐ[volume]
        fun t => mFourier (-k) t • f t :=
      hgf.mono fun x hx => congrArg _ hx
    have hstep : ∀ t : UnitAddTorus ι,
        mFourier (-k) (a + t) • f (a + t) =
          mFourier (-k) a • (mFourier (-k) t • f t) := by
      intro t
      rw [mFourier_apply_add, hfinv t]
      simp only [smul_eq_mul, mul_assoc]
    calc mFourierCoeff (g : UnitAddTorus ι → ℂ) k
        = ∫ t, mFourier (-k) t • (g : UnitAddTorus ι → ℂ) t := rfl
      _ = ∫ t, mFourier (-k) t • f t := integral_congr_ae hgf'
      _ = ∫ t, mFourier (-k) (a + t) • f (a + t) :=
          (integral_add_left_eq_self (fun t => mFourier (-k) t • f t) a).symm
      _ = ∫ t, mFourier (-k) a • (mFourier (-k) t • f t) :=
          integral_congr_ae (Eventually.of_forall hstep)
      _ = mFourier (-k) a • ∫ t, mFourier (-k) t • f t := integral_smul _ _
      _ = mFourier (-k) a • ∫ t, mFourier (-k) t • (g : UnitAddTorus ι → ℂ) t :=
          congrArg _ (integral_congr_ae hgf').symm
      _ = mFourier (-k) a * mFourierCoeff (g : UnitAddTorus ι → ℂ) k := by
          simp only [mFourierCoeff, smul_eq_mul]
  -- hence `f̂` is supported on `k = 0`
  have hzero : ∀ k : ι → ℤ, k ≠ 0 →
      mFourierCoeff (g : UnitAddTorus ι → ℂ) k = 0 := by
    intro k hk
    have hne : mFourier (-k) a ≠ 1 := ha (-k) (neg_ne_zero.mpr hk)
    have h := hcoeff k
    by_contra h0
    apply hne
    have hsub : (mFourier (-k) a - 1) *
        mFourierCoeff (g : UnitAddTorus ι → ℂ) k = 0 := by
      rw [sub_mul, one_mul, ← h, sub_self]
    rcases mul_eq_zero.mp hsub with h1 | h2
    · exact sub_eq_zero.mp h1
    · exact absurd h2 h0
  -- so `g` is a.e. equal to the constant `f̂ 0`
  have hg_const : (g : UnitAddTorus ι → ℂ) =ᵐ[volume] fun _ =>
      mFourierCoeff (g : UnitAddTorus ι → ℂ) 0 := by
    have hseries := hasSum_mFourier_series_L2 g
    have hcollapse : HasSum
        (fun i => mFourierCoeff (g : UnitAddTorus ι → ℂ) i • mFourierLp 2 i)
        (mFourierCoeff (g : UnitAddTorus ι → ℂ) 0 • mFourierLp 2 (0 : ι → ℤ)) := by
      convert hasSum_ite_eq (0 : ι → ℤ)
        (mFourierCoeff (g : UnitAddTorus ι → ℂ) 0 • mFourierLp 2 (0 : ι → ℤ)) using 1
      ext i
      split_ifs with hi
      · rw [hi]
      · rw [hzero i hi, zero_smul]
    have hg_eq : g = mFourierCoeff (g : UnitAddTorus ι → ℂ) 0 •
        mFourierLp 2 (0 : ι → ℤ) := HasSum.unique hseries hcollapse
    have h1 : (g : UnitAddTorus ι → ℂ) =ᵐ[volume]
        mFourierCoeff (g : UnitAddTorus ι → ℂ) 0 • ⇑(mFourierLp 2 (0 : ι → ℤ)) := by
      have h := Lp.coeFn_smul (mFourierCoeff (g : UnitAddTorus ι → ℂ) 0)
        (mFourierLp 2 (0 : ι → ℤ))
      rw [← hg_eq] at h
      exact h
    filter_upwards [h1, coeFn_mFourierLp 2 (0 : ι → ℤ)] with x hx1 hx2
    rw [hx1, Pi.smul_apply, hx2]
    simp [mFourier_zero, smul_eq_mul]
  -- `f` is a.e. constant, so `s` is a.e. empty or full
  have hconst : EventuallyConst f (ae volume) :=
    eventuallyConst_iff_exists_eventuallyEq.mpr
      ⟨mFourierCoeff (g : UnitAddTorus ι → ℂ) 0, hgf.symm.trans hg_const⟩
  exact EventuallyEmptyOrUniv.of_indicator_const hconst one_ne_zero

/-- **Discrete Kronecker.** If `{1} ∪ α` has no integer relations, the integer
multiples of `α` are dense in the torus. -/
theorem denseRange_zsmul {α : ι → ℝ}
    (hα : ∀ k : ι → ℤ, ∀ n : ℤ, (∑ i, (k i : ℝ) * α i) = (n : ℝ) → ∀ i, k i = 0) :
    DenseRange (fun m : ℤ => fun i => ((m * α i : ℝ) : UnitAddCircle)) := by
  have heq : (fun m : ℤ => fun i => ((m * α i : ℝ) : UnitAddCircle)) =
      (fun n : ℤ => n • fun i => ((α i : ℝ) : UnitAddCircle)) := by
    funext m
    funext i
    rw [Pi.smul_apply, ← AddCircle.coe_zsmul, zsmul_eq_mul]
  rw [heq]
  exact (ergodic_add_left_iff_denseRange_zsmul
    (volume : Measure (UnitAddTorus ι))).mp
    (ergodic_add_left_torus _ (fun k hk => mFourier_ne_one hα hk))

end FlowKronecker

end
