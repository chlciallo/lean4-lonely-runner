/-
Copyright (c) 2026 Research07 contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Research07 contributors
-/
import Mathlib

/-!
# W8 scratch — develop `orbit_dense_annihilator` offline

Self-contained copy of the frozen signatures (defs verbatim; upstream theorems
sorried) so the proof can be compiled while `Relations.lean` is mid-edit by W6.
-/

noncomputable section

/-- The integer relation lattice of a real tuple. (copied from Relations.lean) -/
def relLattice {n : ℕ} (u : Fin n → ℝ) : Submodule ℤ (Fin n → ℤ) :=
  LinearMap.ker (Fintype.linearCombination ℤ u)

/-- The kernel space `Ker(A)`. (copied) -/
def kerSpan {n : ℕ} (u : Fin n → ℝ) : Submodule ℝ (Fin n → ℝ) where
  carrier := {x | ∀ k ∈ relLattice u, ∑ i, (k i : ℝ) * x i = 0}
  add_mem' := by
    intro x y hx hy k hk
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
    rw [hx k hk, hy k hk, add_zero]
  zero_mem' := by
    intro k _
    simp
  smul_mem' := by
    intro c x hx k hk
    simp only [Pi.smul_apply, smul_eq_mul, mul_left_comm]
    rw [← Finset.mul_sum, hx k hk, mul_zero]

/-- The rational points of `kerSpan u`. (copied) -/
def kerSpanRat {n : ℕ} (u : Fin n → ℝ) : Submodule ℚ (Fin n → ℚ) where
  carrier := {x | ∀ k ∈ relLattice u, ∑ i, k i * x i = 0}
  add_mem' := by
    intro x y hx hy k hk
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
    rw [hx k hk, hy k hk, add_zero]
  zero_mem' := by
    intro k _
    simp
  smul_mem' := by
    intro c x hx k hk
    simp only [Pi.smul_apply, smul_eq_mul, mul_left_comm]
    rw [← Finset.mul_sum, hx k hk, mul_zero]

/-- `u` lies in its own kernel space. (copied, proved upstream) -/
theorem mem_kerSpan_self {n : ℕ} (u : Fin n → ℝ) : u ∈ kerSpan u := by
  intro k hk
  rw [relLattice, LinearMap.mem_ker, Fintype.linearCombination_apply] at hk
  simpa only [zsmul_eq_mul] using hk

/-- The integer points of the kernel space. (copied) -/
def kerSpanInt {n : ℕ} (u : Fin n → ℝ) : Submodule ℤ (Fin n → ℤ) where
  carrier := {x | ∀ k ∈ relLattice u, ∑ i, k i * x i = 0}
  add_mem' := by
    intro x y hx hy k hk
    simp only [Pi.add_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib]
    rw [hx k hk, hy k hk, add_zero]
  zero_mem' := by
    intro k _
    simp
  smul_mem' := by
    intro c x hx k hk
    simp only [Pi.smul_apply, smul_eq_mul, mul_left_comm]
    rw [← Finset.mul_sum, hx k hk, mul_zero]

/-- The annihilator subtorus. (copied) -/
def annihilator {n : ℕ} (u : Fin n → ℝ) : Set (Fin n → UnitAddCircle) :=
  {y | ∀ k ∈ relLattice u, ∑ i, (k i) • y i = 0}

/-- The subtorus map of an integer matrix. (copied) -/
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

/-- `kerSpan u` is the `ℝ`-span of `kerSpanRat u` cast into `ℝ`. (W6, sorried) -/
theorem kerSpan_eq_span_rat {n : ℕ} (u : Fin n → ℝ) :
    kerSpan u = Submodule.span ℝ ((fun x : Fin n → ℚ => fun i => (x i : ℝ)) ''
      (kerSpanRat u : Set (Fin n → ℚ))) := by
  sorry

/-- Minimality lemma — FALSE as frozen (W6 countermodel), kept sorried. -/
theorem kernel_coords_linearIndependent {n d : ℕ} (u : Fin n → ℝ) (ρ : Fin d → Fin n → ℚ)
    (hρspan : ∀ x : Fin n → ℚ, x ∈ kerSpanRat u → x ∈ Submodule.span ℚ (Set.range ρ))
    (c : Fin d → ℝ) (hc : ∀ i, u i = ∑ ℓ, c ℓ * (ρ ℓ i : ℝ)) :
    LinearIndependent ℚ c := by
  sorry

/-- Corrected minimality lemma (W6, proved upstream). -/
theorem kernel_coords_linearIndependent_of_basis {n d : ℕ} (u : Fin n → ℝ)
    (ρ : Fin d → Fin n → ℚ)
    (hρmem : ∀ ℓ, ρ ℓ ∈ kerSpanRat u)
    (hρind : LinearIndependent ℚ ρ)
    (c : Fin d → ℝ) (hc : ∀ i, u i = ∑ ℓ, c ℓ * (ρ ℓ i : ℝ)) :
    LinearIndependent ℚ c := by
  sorry

theorem subtorusMap_continuous {n d : ℕ} (ρ : Fin d → Fin n → ℤ) :
    Continuous (subtorusMap ρ) := by
  sorry

theorem subtorusMap_range_eq_annihilator {n d : ℕ} (u : Fin n → ℝ) (ρ : Fin d → Fin n → ℤ)
    (hspan : ∀ x : Fin n → ℤ, x ∈ kerSpanInt u →
      x ∈ Submodule.span ℤ (Set.range ρ))
    (hmem : ∀ ℓ, (ρ ℓ) ∈ kerSpanInt u)
    (hinj : LinearIndependent ℤ ρ) :
    Set.range (subtorusMap ρ) = annihilator u := by
  sorry

theorem flow_orbit_dense {d : ℕ} {c : Fin d → ℝ} (hc : LinearIndependent ℚ c) :
    Dense (Set.range fun t : ℝ => fun i => ((t * c i : ℝ) : UnitAddCircle)) := by
  sorry

/-! ### W8 work below -/

/-- The coercion `ℝ → UnitAddCircle` commutes with finite sums. -/
private theorem coe_sum_unitAddCircle {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ((∑ i ∈ s, f i : ℝ) : UnitAddCircle) = ∑ i ∈ s, ((f i : ℝ) : UnitAddCircle) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    rfl

/-- `ℤ`-linear independence upgrades to `ℚ`-linear independence under `Int.cast`:
clear denominators in a putative rational relation. -/
private theorem linearIndependent_intCast {n d : ℕ} {ρ : Fin d → Fin n → ℤ}
    (h : LinearIndependent ℤ ρ) : LinearIndependent ℚ (fun ℓ i => (ρ ℓ i : ℚ)) := by
  rw [Fintype.linearIndependent_iff] at h ⊢
  intro g hg ℓ₀
  set D : ℕ := ∏ ℓ, (g ℓ).den with hDdef
  have hD : 0 < D := Finset.prod_pos fun _ _ => Rat.pos _
  have hDQ : (D : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hD.ne'
  set m : Fin d → ℤ := fun ℓ => (g ℓ).num * ((D / (g ℓ).den : ℕ) : ℤ) with hmdef
  have hdvd : ∀ ℓ, (g ℓ).den ∣ D := fun ℓ =>
    Finset.dvd_prod_of_mem _ (Finset.mem_univ ℓ)
  have hm : ∀ ℓ, ((m ℓ : ℤ) : ℚ) = (D : ℚ) * g ℓ := by
    intro ℓ
    have hden : ((g ℓ).den : ℚ) ≠ 0 := by exact_mod_cast (Rat.den_nz (g ℓ))
    have hcast : (((D / (g ℓ).den : ℕ) : ℤ) : ℚ) = (D : ℚ) / ((g ℓ).den : ℚ) := by
      rw [Int.cast_natCast, Nat.cast_div (hdvd ℓ) hden]
    calc ((m ℓ : ℤ) : ℚ)
        = ((g ℓ).num : ℚ) * (((D / (g ℓ).den : ℕ) : ℤ) : ℚ) := by
          rw [Int.cast_mul]
      _ = ((g ℓ).num : ℚ) * ((D : ℚ) / ((g ℓ).den : ℚ)) := by
          rw [hcast]
      _ = (D : ℚ) * (((g ℓ).num : ℚ) / ((g ℓ).den : ℚ)) := by
          rw [← mul_div_assoc, ← mul_div_assoc, mul_comm ((g ℓ).num : ℚ) (D : ℚ)]
      _ = (D : ℚ) * g ℓ := by
          rw [Rat.num_div_den]
  -- the integer relation `∑ m ℓ • ρ ℓ = 0`
  have hsum : ∑ ℓ, m ℓ • ρ ℓ = 0 := by
    funext i
    have hgi : ∑ ℓ, (g ℓ : ℚ) * ((ρ ℓ i : ℤ) : ℚ) = 0 := by
      have := congr_fun hg i
      simpa [Pi.smul_apply, Finset.sum_apply, smul_eq_mul] using this
    have h0 : ((∑ ℓ, m ℓ * ρ ℓ i : ℤ) : ℚ) = 0 := by
      have e : ((∑ ℓ, m ℓ * ρ ℓ i : ℤ) : ℚ) =
          ∑ ℓ, ((m ℓ : ℤ) : ℚ) * ((ρ ℓ i : ℤ) : ℚ) := by
        rw [Int.cast_sum]
        apply Finset.sum_congr rfl
        intro ℓ _
        rw [Int.cast_mul]
      rw [e]
      have e2 : ∀ ℓ, ((m ℓ : ℤ) : ℚ) * ((ρ ℓ i : ℤ) : ℚ) =
          (D : ℚ) * ((g ℓ : ℚ) * ((ρ ℓ i : ℤ) : ℚ)) := by
        intro ℓ
        rw [hm ℓ]
        ring
      rw [Finset.sum_congr rfl (fun ℓ _ => e2 ℓ), ← Finset.mul_sum, hgi, mul_zero]
    have h0' : ∑ ℓ, m ℓ * ρ ℓ i = 0 := by exact_mod_cast h0
    simpa [Pi.smul_apply, Finset.sum_apply, smul_eq_mul] using h0'
  have hm0 : m ℓ₀ = 0 := h m hsum ℓ₀
  have hD0 : (D : ℚ) * g ℓ₀ = 0 := by
    rw [← hm ℓ₀]
    exact_mod_cast hm0
  exact (mul_eq_zero.mp hD0).resolve_left hDQ

/-- Every annihilator point is approximable by the real orbit of `u`. -/
theorem orbit_dense_annihilator {n : ℕ} (u : Fin n → ℝ) :
    annihilator u ⊆
      closure (Set.range fun t : ℝ => fun i => ((t * u i : ℝ) : UnitAddCircle)) := by
  classical
  -- Step 1: a `ℤ`-basis of `kerSpanInt u`, indexed by `Fin d`.
  obtain ⟨d, b⟩ := Submodule.basisOfPid (Pi.basisFun ℤ (Fin n)) (kerSpanInt u)
  set ρ : Fin d → Fin n → ℤ := fun ℓ i => (b ℓ : Fin n → ℤ) i with hρdef
  have hmem : ∀ ℓ, ρ ℓ ∈ kerSpanInt u := fun ℓ => (b ℓ).2
  have hinj : LinearIndependent ℤ ρ := by
    have h := b.linearIndependent.map' (kerSpanInt u).subtype (kerSpanInt u).ker_subtype
    exact h
  have hspan : ∀ x : Fin n → ℤ, x ∈ kerSpanInt u →
      x ∈ Submodule.span ℤ (Set.range ρ) := by
    intro x hx
    have hb : (⟨x, hx⟩ : ↥(kerSpanInt u)) ∈ Submodule.span ℤ (Set.range ⇑b) := by
      rw [b.span_eq]
      exact Submodule.mem_top
    have hrange : Set.range ρ = ⇑(kerSpanInt u).subtype '' Set.range ⇑b := by
      ext y
      simp only [Set.mem_range, Set.mem_image]
      constructor
      · rintro ⟨ℓ, rfl⟩
        exact ⟨b ℓ, ⟨ℓ, rfl⟩, rfl⟩
      · rintro ⟨z, ⟨ℓ, rfl⟩, rfl⟩
        exact ⟨ℓ, rfl⟩
    have hmap : x ∈ (Submodule.span ℤ (Set.range ⇑b)).map (kerSpanInt u).subtype :=
      ⟨⟨x, hx⟩, hb, rfl⟩
    rwa [Submodule.map_span, ← hrange] at hmap
  -- Step 2: the same basis, cast to `ℚ`, spans `kerSpanRat u` (clear denominators).
  set ρQ : Fin d → Fin n → ℚ := fun ℓ i => (ρ ℓ i : ℚ) with hρQdef
  have hρmem : ∀ ℓ, ρQ ℓ ∈ kerSpanRat u := by
    intro ℓ k hk
    have h := hmem ℓ k hk
    have hQ : ((∑ i, k i * ρ ℓ i : ℤ) : ℚ) = 0 := by
      rw [h]
      norm_cast
    rw [Int.cast_sum] at hQ
    simp only [Int.cast_mul] at hQ
    exact hQ
  have hρind : LinearIndependent ℚ ρQ := by
    have h := linearIndependent_intCast hinj
    exact h
  have hρspan : ∀ x : Fin n → ℚ, x ∈ kerSpanRat u →
      x ∈ Submodule.span ℚ (Set.range ρQ) := by
    intro x hx
    -- common denominator
    set m : ℕ := ∏ i, (x i).den with hmdef
    have hm : 0 < m := Finset.prod_pos fun i _ => Rat.pos _
    have hmQ : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
    set y : Fin n → ℤ := fun i => (x i).num * ((m / (x i).den : ℕ) : ℤ) with hydef
    have hdvd : ∀ i, (x i).den ∣ m := fun i =>
      Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
    have hkey : ∀ i, ((y i : ℤ) : ℚ) = (m : ℚ) * x i := by
      intro i
      have hden : ((x i).den : ℚ) ≠ 0 := by
        exact_mod_cast (Rat.den_nz (x i))
      have hcast : (((m / (x i).den : ℕ) : ℤ) : ℚ) = (m : ℚ) / ((x i).den : ℚ) := by
        rw [Int.cast_natCast, Nat.cast_div (hdvd i) hden]
      calc ((y i : ℤ) : ℚ)
          = ((x i).num : ℚ) * (((m / (x i).den : ℕ) : ℤ) : ℚ) := by
            rw [Int.cast_mul]
        _ = ((x i).num : ℚ) * ((m : ℚ) / ((x i).den : ℚ)) := by
            rw [hcast]
        _ = (m : ℚ) * (((x i).num : ℚ) / ((x i).den : ℚ)) := by
            rw [← mul_div_assoc, ← mul_div_assoc, mul_comm ((x i).num : ℚ) (m : ℚ)]
        _ = (m : ℚ) * x i := by
            rw [Rat.num_div_den]
    -- `y` is an integer point of the kernel
    have hy_mem : y ∈ kerSpanInt u := by
      intro k hk
      have h0 : ((∑ i, k i * y i : ℤ) : ℚ) = 0 := by
        have e : ((∑ i, k i * y i : ℤ) : ℚ) = ∑ i, (k i : ℚ) * (y i : ℚ) := by
          rw [Int.cast_sum]
          apply Finset.sum_congr rfl
          intro i _
          rw [Int.cast_mul]
        rw [e]
        have e2 : ∀ i, (k i : ℚ) * (y i : ℚ) = (m : ℚ) * ((k i : ℚ) * x i) := by
          intro i
          rw [hkey i]
          ring
        rw [Finset.sum_congr rfl (fun i _ => e2 i), ← Finset.mul_sum, hx k hk, mul_zero]
      exact_mod_cast h0
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp (hspan y hy_mem)
    refine (Submodule.mem_span_range_iff_exists_fun ℚ).mpr
      ⟨fun ℓ => (a ℓ : ℚ) / (m : ℚ), ?_⟩
    funext i
    have ha_i : ∑ ℓ, (a ℓ : ℚ) * ((ρ ℓ i : ℤ) : ℚ) = (y i : ℚ) := by
      have hcong := congr_fun ha i
      have hcong2 : ∑ ℓ, a ℓ * ρ ℓ i = y i := by
        simpa [Pi.smul_apply, Finset.sum_apply, smul_eq_mul] using hcong
      calc ∑ ℓ, (a ℓ : ℚ) * ((ρ ℓ i : ℤ) : ℚ)
          = ((∑ ℓ, a ℓ * ρ ℓ i : ℤ) : ℚ) := by
            rw [Int.cast_sum]
            apply Finset.sum_congr rfl
            intro ℓ _
            rw [Int.cast_mul]
        _ = (y i : ℚ) := by rw [hcong2]
    have hxi : x i = ((y i : ℤ) : ℚ) / (m : ℚ) := by
      rw [hkey i]
      field_simp
    -- goal: (∑ ℓ, ((a ℓ:ℚ)/m) • ρQ ℓ) i = x i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [hxi, ← ha_i, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro ℓ _
    rw [hρQdef]
    simp only
    ring
  -- Step 3: `u` is in the `ℝ`-span of the basis, giving coordinates `c`.
  have hu_mem : u ∈ kerSpan u := mem_kerSpan_self u
  rw [kerSpan_eq_span_rat u] at hu_mem
  have hsub : (fun x : Fin n → ℚ => fun i => (x i : ℝ)) '' (kerSpanRat u : Set (Fin n → ℚ)) ⊆
      Submodule.span ℝ (Set.range fun ℓ i => (ρQ ℓ i : ℝ)) := by
    rintro w ⟨x, hx, rfl⟩
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).mp (hρspan x hx)
    refine (Submodule.mem_span_range_iff_exists_fun ℝ).mpr ⟨fun ℓ => (c ℓ : ℝ), ?_⟩
    funext i
    have hxi : x i = ∑ ℓ, c ℓ * ρQ ℓ i := by
      have := congr_fun hc i
      simpa [Pi.smul_apply, Finset.sum_apply, smul_eq_mul] using this.symm
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    have h3 : ((∑ ℓ, c ℓ * ρQ ℓ i : ℚ) : ℝ) = ∑ ℓ, (c ℓ : ℝ) * (ρQ ℓ i : ℝ) := by
      rw [Rat.cast_sum]
      apply Finset.sum_congr rfl
      intro ℓ _
      rw [Rat.cast_mul]
    rw [← h3, hxi]
  have hu_span : u ∈ Submodule.span ℝ (Set.range fun ℓ i => (ρQ ℓ i : ℝ)) :=
    Submodule.span_le.mpr hsub hu_mem
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hu_span
  have hc2 : ∀ i, u i = ∑ ℓ, c ℓ * (ρQ ℓ i : ℝ) := by
    intro i
    have := congr_fun hc i
    simpa [Pi.smul_apply, Finset.sum_apply, smul_eq_mul] using this.symm
  have hLI : LinearIndependent ℚ c :=
    kernel_coords_linearIndependent_of_basis u ρQ hρmem hρind c hc2
  -- Step 4: pointwise identity of the orbit with the subtorus map.
  have hdense : Dense (Set.range fun t : ℝ =>
      fun i => ((t * c i : ℝ) : UnitAddCircle)) := flow_orbit_dense hLI
  have hpt : ∀ t : ℝ,
      subtorusMap ρ (fun ℓ => ((t * c ℓ : ℝ) : UnitAddCircle)) =
        fun i => ((t * u i : ℝ) : UnitAddCircle) := by
    intro t
    funext i
    show (∑ ℓ, (ρ ℓ i) • ((t * c ℓ : ℝ) : UnitAddCircle)) = _
    have hρQcast : ∀ ℓ : Fin d, ∀ i : Fin n, (ρQ ℓ i : ℝ) = (ρ ℓ i : ℝ) :=
      fun ℓ i => Rat.cast_intCast _
    have term : ∀ ℓ : Fin d, (ρ ℓ i) • ((t * c ℓ : ℝ) : UnitAddCircle) =
        (((ρ ℓ i : ℝ) * (t * c ℓ) : ℝ) : UnitAddCircle) := by
      intro ℓ
      rw [← AddCircle.coe_zsmul, zsmul_eq_mul]
    rw [Finset.sum_congr rfl (fun ℓ _ => term ℓ)]
    rw [← coe_sum_unitAddCircle]
    congr 1
    rw [hc2 i, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ℓ _
    rw [← hρQcast ℓ i]
    ring
  -- Step 5: pull the dense orbit back through `subtorusMap`.
  intro y hy
  rw [← subtorusMap_range_eq_annihilator u ρ hspan hmem hinj] at hy
  obtain ⟨x, rfl⟩ := hy
  have hsub2 : subtorusMap ρ '' closure (Set.range fun t : ℝ =>
        fun i => ((t * c i : ℝ) : UnitAddCircle)) ⊆
      closure (subtorusMap ρ '' (Set.range fun t : ℝ =>
        fun i => ((t * c i : ℝ) : UnitAddCircle))) :=
    image_closure_subset_closure_image (subtorusMap_continuous ρ)
  have hstep1 : subtorusMap ρ x ∈ closure (subtorusMap ρ '' (Set.range fun t : ℝ =>
        fun i => ((t * c i : ℝ) : UnitAddCircle))) :=
    hsub2 ⟨x, hdense x, rfl⟩
  have himg : subtorusMap ρ '' (Set.range fun t : ℝ =>
        fun i => ((t * c i : ℝ) : UnitAddCircle)) =
      Set.range (fun t : ℝ => fun i => ((t * u i : ℝ) : UnitAddCircle)) := by
    rw [← Set.range_comp]
    congr 1
    funext t
    simp only [Function.comp_apply]
    exact hpt t
  rwa [himg] at hstep1

end
