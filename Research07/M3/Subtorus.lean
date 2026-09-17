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
  show Continuous fun x : Fin d → UnitAddCircle => fun i => ∑ ℓ, ρ ℓ i • x ℓ
  apply continuous_pi
  intro i
  apply continuous_finsetSum
  intro ℓ _
  exact (continuous_zsmul (ρ ℓ i)).comp (continuous_apply ℓ)

/-- If `ρ` is a `ℤ`-basis (as columns) of `kerSpanInt u`, the image of
`subtorusMap ρ` is exactly the annihilator of `u`. -/
theorem subtorusMap_range_eq_annihilator {n d : ℕ} (u : Fin n → ℝ) (ρ : Fin d → Fin n → ℤ)
    (hspan : ∀ x : Fin n → ℤ, x ∈ kerSpanInt u →
      x ∈ Submodule.span ℤ (Set.range ρ))
    (hmem : ∀ ℓ, (ρ ℓ) ∈ kerSpanInt u)
    (hinj : LinearIndependent ℤ ρ) :
    Set.range (subtorusMap ρ) = annihilator u := by
  ext y
  constructor
  · -- (⊆) the image is contained in the annihilator
    rintro ⟨x, rfl⟩ k hk
    show (∑ i, k i • ∑ ℓ, ρ ℓ i • x ℓ) = 0
    calc (∑ i, k i • ∑ ℓ, ρ ℓ i • x ℓ)
        = ∑ i, ∑ ℓ, (k i * ρ ℓ i) • x ℓ := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl fun ℓ _ => ?_
          rw [← mul_zsmul]
      _ = ∑ ℓ, ∑ i, (k i * ρ ℓ i) • x ℓ := Finset.sum_comm
      _ = ∑ ℓ, (∑ i, k i * ρ ℓ i) • x ℓ := by
          refine Finset.sum_congr rfl fun ℓ _ => ?_
          rw [← Finset.sum_smul]
      _ = ∑ ℓ, (0 : ℤ) • x ℓ := by
          refine Finset.sum_congr rfl fun ℓ _ => ?_
          rw [hmem ℓ k hk]
      _ = 0 := by simp
  · -- (⊇) every annihilator point is hit
    intro hy
    classical
    -- The saturated kernel `K = kerSpanInt u` and its quotient `Q`.
    let K : Submodule ℤ (Fin n → ℤ) := kerSpanInt u
    let Q := (Fin n → ℤ) ⧸ K
    have hmkQ0 : ∀ v : Fin n → ℤ, K.mkQ v = 0 ↔ v ∈ K := fun v => by
      rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
    -- `K` is saturated: `m • v ∈ K` with `m ≠ 0` gives `v ∈ K`. Hence `Q` is
    -- torsion-free, therefore free.
    have hTF : Module.IsTorsionFree ℤ Q := by
      rw [Module.isTorsionFree_iff_smul_eq_zero]
      intro m x hx
      obtain ⟨v, rfl⟩ := K.mkQ_surjective x
      rw [← LinearMap.map_smul] at hx
      have hmv : m • v ∈ K := (hmkQ0 _).mp hx
      rcases eq_or_ne m 0 with rfl | hm
      · exact Or.inl rfl
      · right
        rw [hmkQ0]
        show ∀ k ∈ relLattice u, ∑ i, k i * v i = 0
        intro k hkr
        have h := hmv k hkr
        have h' : ∑ i, k i * (m • v) i = m * ∑ i, k i * v i := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Pi.smul_apply, smul_eq_mul]
          ring
        rw [h'] at h
        exact (mul_eq_zero.mp h).resolve_left hm
    haveI : Module.IsTorsionFree ℤ Q := hTF
    haveI : Module.Free ℤ Q := Module.free_of_finite_type_torsion_free'
    -- A basis `bq` of `Q`, lifts `γ j`, and the coordinate functionals `f j`.
    let bq := Module.Free.chooseBasis ℤ Q
    obtain ⟨γ, hγ⟩ : ∃ γ : Module.Free.ChooseBasisIndex ℤ Q → (Fin n → ℤ),
        ∀ j, K.mkQ (γ j) = bq j :=
      ⟨fun j => (K.mkQ_surjective (bq j)).choose,
       fun j => (K.mkQ_surjective (bq j)).choose_spec⟩
    let f : Module.Free.ChooseBasisIndex ℤ Q → (Fin n → ℤ) →ₗ[ℤ] ℤ := fun j =>
      (Finsupp.lapply j).comp ((bq.repr : Q →ₗ[ℤ] _) ∘ₗ K.mkQ)
    have hf_apply : ∀ j v, f j v = (bq.repr (K.mkQ v)) j := fun j v => rfl
    -- `f j` vanishes exactly on `K`, and `mkQ v = ∑ f j v • bq j`.
    have hmkQ : ∀ v : Fin n → ℤ, K.mkQ v = ∑ j, f j v • bq j := fun v => by
      simpa only [hf_apply] using (bq.sum_repr (K.mkQ v)).symm
    have hfγ : ∀ j j', f j (γ j') = if j' = j then (1 : ℤ) else 0 := by
      intro j j'
      rw [hf_apply, hγ j']
      exact bq.repr_self_apply j' j
    -- Coefficient vectors `c j` representing `f j` as an integer row.
    let c : Module.Free.ChooseBasisIndex ℤ Q → Fin n → ℤ := fun j i => f j (Pi.single i 1)
    have hfv : ∀ j (v : Fin n → ℤ), f j v = ∑ i, c j i * v i := by
      intro j v
      conv_lhs => rw [pi_eq_sum_univ' v]
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, smul_eq_mul, mul_comm]
    -- `f` kills each `ρ ℓ` since `ρ ℓ ∈ K`.
    have h0 : ∀ j ℓ, f j (ρ ℓ) = 0 := by
      intro j ℓ
      rw [hf_apply, (hmkQ0 _).mpr (hmem ℓ), map_zero]
      simp
    -- The real-linear functionals `F j` extending `f j`.
    let F : Module.Free.ChooseBasisIndex ℤ Q → (Fin n → ℝ) →ₗ[ℝ] ℝ := fun j =>
      Fintype.linearCombination ℝ (fun i => ((c j i : ℤ) : ℝ))
    have hF_apply : ∀ j (w : Fin n → ℝ), F j w = ∑ i, w i * ((c j i : ℤ) : ℝ) := by
      intro j w
      show (Fintype.linearCombination ℝ (fun i => ((c j i : ℤ) : ℝ))) w = _
      rw [Fintype.linearCombination_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_eq_mul]
    have hF_int : ∀ j (z : Fin n → ℤ),
        F j (fun i => ((z i : ℤ) : ℝ)) = ((f j z : ℤ) : ℝ) := by
      intro j z
      rw [hfv j z, hF_apply j (fun i => ((z i : ℤ) : ℝ)), Int.cast_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Int.cast_mul, mul_comm (z i) (c j i)]
    -- Common-denominator clearing for finite rational tuples.
    have hdenom : ∀ x : Fin n → ℚ, ∃ N : ℕ, 0 < N ∧ ∃ Nx : Fin n → ℤ,
        ∀ i, ((Nx i : ℤ) : ℚ) = (N : ℚ) * x i := by
      intro x
      refine ⟨∏ i, (x i).den, Finset.prod_pos (fun i _ => (x i).den_pos),
        fun i => (x i).num * (((∏ j, (x j).den) / (x i).den : ℕ) : ℤ), fun i => ?_⟩
      have hdvd : (x i).den ∣ ∏ j, (x j).den := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
      have hden0 : ((x i).den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (x i).den_ne_zero
      dsimp only
      rw [Int.cast_mul, Int.cast_natCast, Nat.cast_div hdvd hden0]
      conv_rhs => rw [← Rat.num_div_den (x i)]
      ring
    -- The real span of `ρ` is exactly `kerSpan u`.
    let ρR : Fin d → Fin n → ℝ := fun ℓ i => ((ρ ℓ i : ℤ) : ℝ)
    have hker_eq : kerSpan u = Submodule.span ℝ (Set.range ρR) := by
      apply le_antisymm
      · rw [kerSpan_eq_span_rat u, Submodule.span_le]
        rintro w ⟨x, hx, rfl⟩
        show (fun i => ((x i : ℚ) : ℝ)) ∈ Submodule.span ℝ (Set.range ρR)
        obtain ⟨N, hN0, Nx, hNx⟩ := hdenom x
        have hNxK : Nx ∈ kerSpanInt u := by
          show ∀ k ∈ relLattice u, ∑ i, k i * Nx i = 0
          intro k hkr
          have hq0 : ((∑ i, k i * Nx i : ℤ) : ℚ) = 0 := by
            push_cast
            calc ∑ i, (k i : ℚ) * ((Nx i : ℤ) : ℚ)
                = ∑ i, (k i : ℚ) * ((N : ℚ) * x i) := by
                  refine Finset.sum_congr rfl fun i _ => ?_
                  rw [hNx i]
              _ = (N : ℚ) * ∑ i, (k i : ℚ) * x i := by
                  rw [Finset.mul_sum]
                  refine Finset.sum_congr rfl fun i _ => ?_
                  ring
              _ = 0 := by rw [hx k hkr, mul_zero]
          exact_mod_cast hq0
        obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp (hspan Nx hNxK)
        have hcast : (fun i => ((Nx i : ℤ) : ℝ)) = ∑ ℓ, ((a ℓ : ℤ) : ℝ) • ρR ℓ := by
          funext i
          show ((Nx i : ℤ) : ℝ) = _
          rw [← ha, Finset.sum_apply, Int.cast_sum, Finset.sum_apply]
          refine Finset.sum_congr rfl fun ℓ _ => ?_
          rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, Int.cast_mul]
        have hmemNx : (fun i => ((Nx i : ℤ) : ℝ)) ∈ Submodule.span ℝ (Set.range ρR) := by
          rw [hcast]
          apply Submodule.sum_mem
          intro ℓ _
          apply Submodule.smul_mem
          exact Submodule.subset_span ⟨ℓ, rfl⟩
        have hN0' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hN0)
        have hw_eq : (fun i => ((x i : ℚ) : ℝ)) =
            ((N : ℝ)⁻¹) • (fun i => ((Nx i : ℤ) : ℝ)) := by
          funext i
          show ((x i : ℚ) : ℝ) = (N : ℝ)⁻¹ * ((Nx i : ℤ) : ℝ)
          rw [inv_mul_eq_div, eq_div_iff hN0', mul_comm]
          have hNxR : ((Nx i : ℤ) : ℝ) = (N : ℝ) * ((x i : ℚ) : ℝ) := by
            have := congrArg (fun q : ℚ => (q : ℝ)) (hNx i)
            push_cast at this
            exact this
          exact hNxR.symm
        rw [hw_eq]
        exact Submodule.smul_mem _ _ hmemNx
      · rw [Submodule.span_le]
        rintro w ⟨ℓ, rfl⟩ k hkr
        have hz : ∑ i, k i * ρ ℓ i = 0 := hmem ℓ k hkr
        have := congrArg (fun z : ℤ => (z : ℝ)) hz
        push_cast at this
        exact this
    have hu_mem : u ∈ Submodule.span ℝ (Set.range ρR) := by
      rw [← hker_eq]
      exact mem_kerSpan_self u
    -- Every `c j` is itself a relation: it kills `kerSpanInt`, hence `kerSpan`,
    -- hence `u`.
    have hFρ : ∀ j, Submodule.span ℝ (Set.range ρR) ≤ LinearMap.ker (F j) := by
      intro j
      rw [Submodule.span_le]
      rintro w ⟨ℓ, rfl⟩
      show F j (fun i => ((ρ ℓ i : ℤ) : ℝ)) = 0
      rw [hF_int j (ρ ℓ), h0 j ℓ]
      simp
    have hcj : ∀ j, c j ∈ relLattice u := by
      intro j
      rw [relLattice, LinearMap.mem_ker, Fintype.linearCombination_apply]
      simp only [zsmul_eq_mul]
      have hFu : F j u = 0 := by
        have := hFρ j hu_mem
        rwa [LinearMap.mem_ker] at this
      rw [hF_apply] at hFu
      rw [← hFu]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_comm]
    -- Cast-sum on the circle.
    have hcoe_sum : ∀ {m : ℕ} (s : Finset (Fin m)) (a : Fin m → ℝ),
        (↑(∑ ℓ ∈ s, a ℓ) : UnitAddCircle) = ∑ ℓ ∈ s, (↑(a ℓ) : UnitAddCircle) := by
      intro m s a
      simpa only [QuotientAddGroup.mk'_apply] using
        map_sum (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))) a s
    -- Lift `y` to a real tuple.
    obtain ⟨yR, hyR⟩ : ∃ yR : Fin n → ℝ, ∀ i, (↑(yR i) : UnitAddCircle) = y i :=
      ⟨fun i => (QuotientAddGroup.mk'_surjective (AddSubgroup.zmultiples (1 : ℝ)) (y i)).choose,
       fun i => (QuotientAddGroup.mk'_surjective (AddSubgroup.zmultiples (1 : ℝ)) (y i)).choose_spec⟩
    -- The `F j`-coordinates of `yR` are integers `w j`.
    have hFy : ∀ j, ∃ z : ℤ, F j yR = (z : ℝ) := by
      intro j
      have hc := hy (c j) (hcj j)
      have e1 : (∑ i, c j i • y i) = ↑(∑ i, (c j i : ℝ) * yR i) := by
        rw [hcoe_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← hyR i, ← AddCircle.coe_zsmul, zsmul_eq_mul]
      rw [e1] at hc
      rw [AddCircle.coe_eq_zero_iff] at hc
      obtain ⟨z, hz⟩ := hc
      refine ⟨z, ?_⟩
      rw [hF_apply]
      calc ∑ i, yR i * ((c j i : ℤ) : ℝ) = ∑ i, (c j i : ℝ) * yR i :=
            Finset.sum_congr rfl fun i _ => mul_comm _ _
        _ = (z • (1 : ℝ)) := hz.symm
        _ = (z : ℝ) := by rw [zsmul_eq_mul, mul_one]
    choose w hw using hFy
    -- Subtract the integral `γ`-part; the remainder `v` has `F j v = 0`.
    let z₀ : Fin n → ℤ := ∑ j, w j • γ j
    have hfz₀ : ∀ j, f j z₀ = w j := by
      intro j
      show f j (∑ j', w j' • γ j') = w j
      rw [map_sum]
      have e : ∀ j', f j (w j' • γ j') = if j' = j then w j' else 0 := fun j' => by
        rw [map_smul, hfγ]
        by_cases h : j' = j <;> simp [h]
      simp only [e]
      rw [Finset.sum_ite_eq']
      simp
    let v : Fin n → ℝ := yR - (fun i => ((z₀ i : ℤ) : ℝ))
    have hFv : ∀ j, F j v = 0 := by
      intro j
      show F j (yR - (fun i => ((z₀ i : ℤ) : ℝ))) = 0
      rw [map_sub, hF_int j z₀, hfz₀ j, hw j, sub_self]
    -- The corrected integer vectors `g i`: `g i = e_i - ∑ c j i • γ j ∈ K`.
    let g : Fin n → Fin n → ℤ := fun i => Pi.single i 1 - ∑ j, c j i • γ j
    have hg : ∀ i, g i ∈ K := by
      intro i
      rw [← hmkQ0]
      show K.mkQ (Pi.single i 1 - ∑ j, c j i • γ j) = 0
      rw [map_sub, map_sum]
      simp only [map_smul, hγ]
      rw [hmkQ]
      exact sub_self _
    have ha : ∀ i, ∃ a : Fin d → ℤ, ∑ ℓ, a ℓ • ρ ℓ = g i := fun i =>
      (Submodule.mem_span_range_iff_exists_fun ℤ).mp (hspan (g i) (hg i))
    -- `v` decomposes over the `g i`, hence lies in `span_ℝ ρ`.
    have hg_cast : ∀ i, (fun i' => ((g i i' : ℤ) : ℝ)) =
        (Pi.single i (1 : ℝ) - ∑ j, ((c j i : ℤ) : ℝ) • (fun i' => ((γ j i' : ℤ) : ℝ))) := by
      intro i
      funext i'
      have hg_i : g i i' = ((Pi.single i (1 : ℤ) : Fin n → ℤ)) i' - ∑ j, c j i * γ j i' := by
        have hgi : g i = Pi.single i (1 : ℤ) - ∑ j, c j i • γ j := rfl
        rw [hgi, Pi.sub_apply, Finset.sum_apply]
        simp only [Pi.smul_apply, smul_eq_mul]
      rw [hg_i, Int.cast_sub, Int.cast_sum]
      show (↑((Pi.single i (1 : ℤ) : Fin n → ℤ) i') - ∑ j, ((c j i * γ j i' : ℤ) : ℝ))
          = ((Pi.single i (1 : ℝ) : Fin n → ℝ)
            - ∑ j, ((c j i : ℤ) : ℝ) • (fun i' => ((γ j i' : ℤ) : ℝ))) i'
      rw [Pi.sub_apply, Finset.sum_apply]
      congr 1
      · by_cases h : i' = i
        · subst h
          simp only [Pi.single_eq_same, Int.cast_one]
        · simp only [Pi.single_eq_of_ne h, Int.cast_zero]
      · refine Finset.sum_congr rfl fun j _ => ?_
        rw [Pi.smul_apply, smul_eq_mul, Int.cast_mul]
    have hg_span : ∀ i, (fun i' => ((g i i' : ℤ) : ℝ)) ∈
        Submodule.span ℝ (Set.range ρR) := by
      intro i
      obtain ⟨a, ha⟩ := ha i
      have hcast : (fun i' => ((g i i' : ℤ) : ℝ)) = ∑ ℓ, ((a ℓ : ℤ) : ℝ) • ρR ℓ := by
        funext i'
        show ((g i i' : ℤ) : ℝ) = _
        rw [← ha, Finset.sum_apply, Int.cast_sum, Finset.sum_apply]
        refine Finset.sum_congr rfl fun ℓ _ => ?_
        rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, Int.cast_mul]
      rw [hcast]
      apply Submodule.sum_mem
      intro ℓ _
      apply Submodule.smul_mem
      exact Submodule.subset_span ⟨ℓ, rfl⟩
    have hv_eq : v = ∑ i, v i • (fun i' => ((g i i' : ℤ) : ℝ)) := by
      have step1 : ∑ i, v i • (fun i' => ((g i i' : ℤ) : ℝ))
          = ∑ i, v i • Pi.single i (1 : ℝ)
            - ∑ j, F j v • (fun i' => ((γ j i' : ℤ) : ℝ)) := by
        calc ∑ i, v i • (fun i' => ((g i i' : ℤ) : ℝ))
            = ∑ i, v i • (Pi.single i (1 : ℝ)
                - ∑ j, ((c j i : ℤ) : ℝ) • (fun i' => ((γ j i' : ℤ) : ℝ))) := by
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [hg_cast i]
          _ = ∑ i, (v i • Pi.single i (1 : ℝ)
                - v i • ∑ j, ((c j i : ℤ) : ℝ) • (fun i' => ((γ j i' : ℤ) : ℝ))) := by
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [smul_sub]
          _ = ∑ i, v i • Pi.single i (1 : ℝ)
                - ∑ i, v i • ∑ j, ((c j i : ℤ) : ℝ) • (fun i' => ((γ j i' : ℤ) : ℝ)) := by
              rw [Finset.sum_sub_distrib]
          _ = ∑ i, v i • Pi.single i (1 : ℝ)
                - ∑ j, F j v • (fun i' => ((γ j i' : ℤ) : ℝ)) := by
              congr 1
              calc ∑ i, v i • ∑ j, ((c j i : ℤ) : ℝ) • (fun i' => ((γ j i' : ℤ) : ℝ))
                  = ∑ i, ∑ j, (v i * ((c j i : ℤ) : ℝ)) • (fun i' => ((γ j i' : ℤ) : ℝ)) := by
                    refine Finset.sum_congr rfl fun i _ => ?_
                    rw [Finset.smul_sum]
                    refine Finset.sum_congr rfl fun j _ => ?_
                    rw [← mul_smul]
                  _ = ∑ j, ∑ i, (v i * ((c j i : ℤ) : ℝ)) •
                        (fun i' => ((γ j i' : ℤ) : ℝ)) := Finset.sum_comm
                  _ = ∑ j, (∑ i, v i * ((c j i : ℤ) : ℝ)) •
                        (fun i' => ((γ j i' : ℤ) : ℝ)) := by
                      refine Finset.sum_congr rfl fun j _ => ?_
                      rw [← Finset.sum_smul]
                  _ = ∑ j, F j v • (fun i' => ((γ j i' : ℤ) : ℝ)) := by
                      refine Finset.sum_congr rfl fun j _ => ?_
                      rw [hF_apply]
      rw [step1]
      simp only [hFv, zero_smul, Finset.sum_const_zero, sub_zero]
      exact pi_eq_sum_univ' v
    have hv_span : v ∈ Submodule.span ℝ (Set.range ρR) := by
      rw [hv_eq]
      apply Submodule.sum_mem
      intro i _
      apply Submodule.smul_mem
      exact hg_span i
    -- Extract real coefficients and build the torus preimage.
    obtain ⟨xR, hxR⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hv_span
    refine ⟨fun ℓ => (↑(xR ℓ) : UnitAddCircle), ?_⟩
    funext i
    show (∑ ℓ, ρ ℓ i • (↑(xR ℓ) : UnitAddCircle)) = y i
    have e1 : ∀ ℓ, ρ ℓ i • (↑(xR ℓ) : UnitAddCircle) = ↑((ρ ℓ i : ℝ) * xR ℓ) := fun ℓ => by
      rw [← AddCircle.coe_zsmul, zsmul_eq_mul]
    rw [Finset.sum_congr rfl (fun ℓ _ => e1 ℓ), ← hcoe_sum]
    have hvi : v i = ∑ ℓ, xR ℓ * ((ρ ℓ i : ℤ) : ℝ) := by
      have h := congrFun hxR i
      rw [← h]
      simp only [Finset.sum_apply, Pi.smul_apply]
      refine Finset.sum_congr rfl fun ℓ _ => ?_
      rw [smul_eq_mul]
    have hsum : (∑ ℓ, ((ρ ℓ i : ℤ) : ℝ) * xR ℓ) = v i := by
      rw [hvi]
      refine Finset.sum_congr rfl fun ℓ _ => ?_
      rw [mul_comm]
    rw [hsum]
    have hv_i' : v i = yR i - ((z₀ i : ℤ) : ℝ) := rfl
    rw [hv_i', AddCircle.coe_sub, hyR i]
    have hz0 : (↑(((z₀ i : ℤ) : ℝ)) : UnitAddCircle) = 0 := by
      rw [AddCircle.coe_eq_zero_iff]
      exact ⟨z₀ i, by rw [zsmul_eq_mul, mul_one]⟩
    rw [hz0, sub_zero]

end
