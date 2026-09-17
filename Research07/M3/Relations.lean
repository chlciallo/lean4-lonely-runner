/-
Copyright (c) 2026 Research07 contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Research07 contributors
-/
import Mathlib
import Research07.LRC3.Circ

/-!
# W6 — Relation lattice API for the BHK reduction (FROZEN STATEMENTS)

For a real tuple `u : Fin n → ℝ` (relative speeds), the **relation lattice** is the set of
integer vectors `k` with `∑ kᵢ·uᵢ = 0`; the **kernel space** `kerSpan u` (= BHK's `Ker(A)`)
is the real subspace annihilated by all relations — equivalently the smallest
rationally-defined subspace containing `u`.

Frozen contract for agent W6. Prove every `sorry`; do not change statements.
-/

noncomputable section

/-- The integer relation lattice of a real tuple: `k : Fin n → ℤ` with `∑ kᵢ·uᵢ = 0`. -/
def relLattice {n : ℕ} (u : Fin n → ℝ) : Submodule ℤ (Fin n → ℤ) :=
  LinearMap.ker (Fintype.linearCombination ℤ u)

/-- The kernel space `Ker(A)`: real vectors annihilated by every integer relation of `u`. -/
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

/-- The rational points of `kerSpan u` (kernel of the rational relation matrix). -/
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

/-- `u` lies in its own kernel space. -/
theorem mem_kerSpan_self {n : ℕ} (u : Fin n → ℝ) : u ∈ kerSpan u := by
  intro k hk
  rw [relLattice, LinearMap.mem_ker, Fintype.linearCombination_apply] at hk
  simpa only [zsmul_eq_mul] using hk

/-- The integer points of the kernel space — a pure (complemented) `ℤ`-submodule. -/
def kerSpanInt {n : ℕ} (u : Fin n → ℝ) : Submodule ℤ (Fin n → ℤ) where
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

/-- The annihilator subtorus: points of `Tⁿ` killed by every integer relation of `u`.
BHK's `M̄(u) = Ker(A) + ℤⁿ` projected to the torus. -/
def annihilator {n : ℕ} (u : Fin n → ℝ) : Set (Fin n → UnitAddCircle) :=
  {y | ∀ k ∈ relLattice u, ∑ i, (k i) • y i = 0}

section W6Helpers

/-- The "dot product" map `Kⁿ → (Kⁿ →ₗ[K] K)`, `t ↦ (x ↦ ∑ tᵢ xᵢ)`. -/
private def dotDual {K : Type*} [Field K] {n : ℕ} :
    (Fin n → K) →ₗ[K] Module.Dual K (Fin n → K) :=
  Fintype.linearCombination K fun i => LinearMap.proj i

private theorem dotDual_apply {K : Type*} [Field K] {n : ℕ} (t x : Fin n → K) :
    dotDual t x = ∑ i, t i * x i := by
  simp only [dotDual, Fintype.linearCombination_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul]

private theorem dotDual_injective {K : Type*} [Field K] {n : ℕ} :
    Function.Injective (dotDual (K := K) (n := n)) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro t ht
  rw [LinearMap.mem_ker] at ht
  rw [Submodule.mem_bot]
  funext j
  have h0 : dotDual t (Pi.single j (1 : K)) = 0 := by rw [ht]; rfl
  rw [dotDual_apply] at h0
  simpa [Pi.single_apply] using h0

/-- The annihilator of a set `T ⊆ Kⁿ` under the dot product, as a `K`-submodule. -/
private def dotAnn {K : Type*} [Field K] {n : ℕ} (T : Set (Fin n → K)) :
    Submodule K (Fin n → K) where
  carrier := {x | ∀ t ∈ T, ∑ i, t i * x i = 0}
  add_mem' := by
    intro x y hx hy t ht
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
    rw [hx t ht, hy t ht, add_zero]
  zero_mem' := by
    intro t _
    simp
  smul_mem' := by
    intro c x hx t ht
    simp only [Pi.smul_apply, smul_eq_mul, mul_left_comm]
    rw [← Finset.mul_sum, hx t ht, mul_zero]

private theorem mem_dotAnn {K : Type*} [Field K] {n : ℕ} {T : Set (Fin n → K)}
    (x : Fin n → K) : x ∈ dotAnn T ↔ ∀ t ∈ T, ∑ i, t i * x i = 0 :=
  Iff.rfl

private theorem dotAnn_eq_dualCoannihilator {K : Type*} [Field K] {n : ℕ}
    (T : Set (Fin n → K)) :
    dotAnn T = (Submodule.span K (dotDual '' T)).dualCoannihilator := by
  ext x
  have hmem : x ∈ (Submodule.span K (dotDual '' T)).dualCoannihilator ↔
      ∀ f ∈ dotDual '' T, f x = 0 := by
    have h := Submodule.coe_dualCoannihilator_span (R := K) (s := dotDual '' T)
    change x ∈ ((Submodule.span K (dotDual '' T)).dualCoannihilator : Set (Fin n → K)) ↔ _
    rw [h]
    rfl
  rw [hmem]
  constructor
  · intro hx f hf
    obtain ⟨t, ht, rfl⟩ := hf
    rw [dotDual_apply]
    exact hx t ht
  · intro hx t ht
    rw [← dotDual_apply t x]
    exact hx _ ⟨t, ht, rfl⟩

private theorem finrank_map_dotDual {K : Type*} [Field K] {n : ℕ}
    (W : Submodule K (Fin n → K)) :
    Module.finrank K (W.map dotDual) = Module.finrank K W := by
  have hr : LinearMap.range (dotDual.domRestrict W) = W.map dotDual := by
    ext y
    simp only [LinearMap.mem_range, LinearMap.domRestrict_apply, Submodule.mem_map]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.1, x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  rw [← hr]
  exact LinearMap.finrank_range_of_inj (fun x y h => Subtype.ext
    (dotDual_injective (by rwa [LinearMap.domRestrict_apply,
      LinearMap.domRestrict_apply] at h)))

private theorem finrank_dotAnn {K : Type*} [Field K] {n : ℕ} (T : Set (Fin n → K)) :
    Module.finrank K (dotAnn T) = n - Module.finrank K (Submodule.span K T) := by
  rw [dotAnn_eq_dualCoannihilator, ← Submodule.map_span]
  have h := Subspace.finrank_add_finrank_dualCoannihilator_eq
    ((Submodule.span K T).map dotDual)
  rw [finrank_map_dotDual, Module.finrank_pi, Fintype.card_fin] at h
  omega

/-- The `ℚ`-linear map `ℚⁿ → ℝⁿ` casting each coordinate. -/
private def ratCastLM {n : ℕ} : (Fin n → ℚ) →ₗ[ℚ] (Fin n → ℝ) where
  toFun x i := (x i : ℝ)
  map_add' x y := funext fun i => Rat.cast_add ..
  map_smul' c x := funext fun i => by
    show (((c • x) i : ℚ) : ℝ) = (c • (fun i => (x i : ℝ))) i
    rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, Rat.cast_mul]
    rfl

private theorem ratCastLM_apply {n : ℕ} (x : Fin n → ℚ) (i : Fin n) :
    ratCastLM x i = (x i : ℝ) := rfl

/-- `q • y` (scalar `q : ℚ` acting on `Fin n → ℝ` through `Algebra ℚ ℝ`) equals
`(q : ℝ) • y`. -/
private theorem rat_smul_eq_real {n : ℕ} (q : ℚ) (y : Fin n → ℝ) :
    q • y = (q : ℝ) • y := by
  funext i
  simp only [Pi.smul_apply, Algebra.smul_def]
  rfl

private theorem span_ratCast_le {n : ℕ} (T : Set (Fin n → ℚ)) :
    ⇑ratCastLM '' ↑(Submodule.span ℚ T) ⊆
      (Submodule.span ℝ (⇑ratCastLM '' T) : Set (Fin n → ℝ)) := by
  rintro x ⟨w, hw, rfl⟩
  induction hw using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [map_smul, rat_smul_eq_real]; exact Submodule.smul_mem _ _ hx

private theorem finrank_span_ratCast {n : ℕ} (T : Set (Fin n → ℚ)) :
    Module.finrank ℝ (Submodule.span ℝ (⇑ratCastLM '' T)) =
      Module.finrank ℚ (Submodule.span ℚ T) := by
  classical
  set K := Submodule.span ℚ T with hK
  let b := Module.Free.chooseBasis ℚ K
  have : Finite (Module.Free.ChooseBasisIndex ℚ K) := Module.Finite.finite_basis b
  let v : Module.Free.ChooseBasisIndex ℚ K → Fin n → ℝ :=
    fun j => ratCastLM ((b j : ↥K) : Fin n → ℚ)
  have hv : LinearIndependent ℝ v := by
    have hv1 : LinearIndependent ℚ
        (fun j : Module.Free.ChooseBasisIndex ℚ K => ((b j : ↥K) : Fin n → ℚ)) :=
      b.linearIndependent.map' K.subtype K.ker_subtype
    have hv2 := (linearIndependent_algebraMap_comp_iff (R := ℚ) (S := ℝ)).mpr hv1
    exact hv2
  have hrange : Submodule.span ℝ (Set.range v) = Submodule.span ℝ (⇑ratCastLM '' T) := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro x ⟨j, rfl⟩
      have hbj : ((b j : ↥K) : Fin n → ℚ) ∈ Submodule.span ℚ T := (b j).2
      exact span_ratCast_le T ⟨_, hbj, rfl⟩
    · apply Submodule.span_le.mpr
      rintro x ⟨t, ht, rfl⟩
      have ht' : t ∈ Submodule.span ℚ T := Submodule.subset_span ht
      have hrepr := congr_arg (fun z : ↥K => (z : Fin n → ℚ)) (b.sum_repr ⟨t, ht'⟩)
      -- t = ∑ (b.repr ⟨t,ht'⟩ i) • (b i : ℚⁿ)
      have ht_eq : t = ∑ i, (b.repr ⟨t, ht'⟩) i • ((b i : ↥K) : Fin n → ℚ) := by
        simp only [Submodule.coe_sum, Submodule.coe_smul] at hrepr
        exact hrepr.symm
      rw [ht_eq, map_sum]
      apply Submodule.sum_mem
      intro i _
      rw [map_smul, rat_smul_eq_real]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  rw [← hrange, finrank_span_set_eq_card (s := Set.range v) hv.linearIndepOn_id]
  rw [Module.finrank_eq_card_basis b, Set.toFinset_card]
  exact Set.card_range_of_injective hv.injective

private theorem kerSpanRat_eq_dotAnn {n : ℕ} (u : Fin n → ℝ) :
    kerSpanRat u = dotAnn ((fun k : Fin n → ℤ => fun i => (k i : ℚ)) ''
      (relLattice u : Set (Fin n → ℤ))) := by
  ext x
  constructor
  · intro hx t ht
    obtain ⟨k, hk, rfl⟩ := ht
    exact hx k hk
  · intro hx k hk
    exact hx _ ⟨k, hk, rfl⟩

private theorem kerSpan_eq_dotAnn {n : ℕ} (u : Fin n → ℝ) :
    kerSpan u = dotAnn (⇑ratCastLM ''
      ((fun k : Fin n → ℤ => fun i => (k i : ℚ)) '' (relLattice u : Set (Fin n → ℤ)))) := by
  ext x
  constructor
  · intro hx t ht
    obtain ⟨w, ⟨k, hk, rfl⟩, rfl⟩ := ht
    simp only [ratCastLM_apply, Rat.cast_intCast]
    exact hx k hk
  · intro hx k hk
    apply hx
    exact ⟨_, ⟨k, hk, rfl⟩, funext fun i => Rat.cast_intCast _⟩

end W6Helpers

/-- `kerSpan u` is defined by rational equations, so its rational points span it:
`kerSpan u` is the `ℝ`-span of `kerSpanRat u` (cast into `ℝ`). -/
theorem kerSpan_eq_span_rat {n : ℕ} (u : Fin n → ℝ) :
    kerSpan u = Submodule.span ℝ ((fun x : Fin n → ℚ => fun i => (x i : ℝ)) ''
      (kerSpanRat u : Set (Fin n → ℚ))) := by
  have hcast : (fun x : Fin n → ℚ => fun i => (x i : ℝ)) = ⇑ratCastLM := rfl
  rw [hcast]
  have hle : Submodule.span ℝ (⇑ratCastLM '' (kerSpanRat u : Set (Fin n → ℚ))) ≤
      kerSpan u := by
    apply Submodule.span_le.mpr
    rintro x ⟨w, hw, rfl⟩ k hk
    have hw0 : ∑ i, (k i : ℚ) * w i = 0 := hw k hk
    have hsum : (∑ i, (k i : ℝ) * ratCastLM w i) =
        ((∑ i, (k i : ℚ) * w i : ℚ) : ℝ) := by
      simp only [ratCastLM_apply]
      symm
      simp only [Rat.cast_sum, Rat.cast_mul, Rat.cast_intCast]
    rw [hsum, hw0]
    simp
  have hfin : Module.finrank ℝ (kerSpan u) =
      Module.finrank ℝ (Submodule.span ℝ (⇑ratCastLM '' (kerSpanRat u : Set (Fin n → ℚ)))) := by
    rw [kerSpan_eq_dotAnn, finrank_dotAnn, finrank_span_ratCast, finrank_span_ratCast,
      ← finrank_dotAnn, ← kerSpanRat_eq_dotAnn, Submodule.span_eq]
  exact (Submodule.eq_of_le_of_finrank_eq hle hfin.symm).symm

/-- A positive real `u ∈ kerSpan u` yields a positive rational point of `kerSpan`:
perturb a rational basis expansion of `u` keeping positivity. -/
theorem exists_pos_rat_kerSpan {n : ℕ} (u : Fin n → ℝ) (hpos : ∀ i, 0 < u i) :
    ∃ r : Fin n → ℚ, (∀ i, 0 < r i) ∧ r ∈ kerSpanRat u := by
  classical
  rcases n with _ | n
  · exact ⟨0, fun i => i.elim0, Submodule.zero_mem _⟩
  -- u lies in the real span of the rational kernel points (cast to ℝ).
  have hu : u ∈ Submodule.span ℝ ((fun x : Fin (n + 1) → ℚ => fun i => (x i : ℝ)) ''
      (kerSpanRat u : Set (Fin (n + 1) → ℚ))) := by
    rw [← kerSpan_eq_span_rat]
    exact mem_kerSpan_self u
  rw [Submodule.mem_span_iff_exists_finset_subset] at hu
  obtain ⟨f, t, htK, _hsupp, huc⟩ := hu
  -- Pull the real generators back to rational kernel vectors.
  have hwa : ∀ a : Fin (n + 1) → ℝ, ∃ w : Fin (n + 1) → ℚ,
      a ∈ t → w ∈ kerSpanRat u ∧ (fun i => (w i : ℝ)) = a := by
    intro a
    by_cases ha : a ∈ t
    · obtain ⟨w', hw'K, hw'eq⟩ := htK ha
      exact ⟨w', fun _ => ⟨hw'K, hw'eq⟩⟩
    · exact ⟨0, fun h => absurd h ha⟩
  choose w hw using hwa
  have hu_eq : ∀ i, u i = ∑ a ∈ t, f a * a i := by
    intro i
    have h := congr_fun huc.symm i
    rw [Finset.sum_apply] at h
    rw [h]
    apply Finset.sum_congr rfl
    intro a _
    rw [Pi.smul_apply, smul_eq_mul]
  -- Positivity budget: `m` is the least coordinate of `u`, `B` bounds the generators.
  set m := (Finset.univ.image u).min' (Finset.image_nonempty.mpr Finset.univ_nonempty)
  have hm_mem : m ∈ Finset.univ.image u := Finset.min'_mem _ _
  obtain ⟨i₀, _, hi₀⟩ := Finset.mem_image.mp hm_mem
  have hm_pos : 0 < m := hi₀ ▸ hpos i₀
  have hm_le : ∀ i, m ≤ u i := fun i =>
    Finset.min'_le _ _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  set B : ℝ := 1 + ∑ a ∈ t, ∑ j, |a j|
  have hB_pos : 0 < B := add_pos_of_pos_of_nonneg zero_lt_one
    (Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun j _ => abs_nonneg _)
  have hSi : ∀ i, ∑ a ∈ t, |a i| ≤ B := fun i => calc
    ∑ a ∈ t, |a i| ≤ ∑ a ∈ t, ∑ j, |a j| :=
      Finset.sum_le_sum fun a _ =>
        Finset.single_le_sum (f := fun j => |a j|) (fun j _ => abs_nonneg _)
          (Finset.mem_univ i)
    _ ≤ B := le_add_of_nonneg_left zero_le_one
  set δ : ℝ := m / (2 * B)
  have hδ : 0 < δ := div_pos hm_pos (mul_pos zero_lt_two hB_pos)
  have hδB : δ * B = m / 2 := by
    rw [div_mul_eq_mul_div]
    exact mul_div_mul_right m 2 hB_pos.ne'
  have hq : ∀ a : Fin (n + 1) → ℝ, ∃ q : ℚ, |f a - (q : ℝ)| < δ :=
    fun a => exists_rat_near (f a) hδ
  choose q hq using hq
  refine ⟨∑ a ∈ t, q a • w a, ?_, ?_⟩
  · intro i
    have hr_cast : ((∑ a ∈ t, q a • w a) i : ℝ) = ∑ a ∈ t, (q a : ℝ) * a i := by
      rw [Finset.sum_apply]
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [Rat.cast_sum]
      apply Finset.sum_congr rfl
      intro a ha
      rw [Rat.cast_mul, ← congr_fun (hw a ha).2 i]
    have hdiff : |u i - ((∑ a ∈ t, q a • w a) i : ℝ)| ≤ m / 2 := by
      rw [hr_cast, hu_eq i, ← Finset.sum_sub_distrib]
      calc |∑ a ∈ t, (f a * a i - (q a : ℝ) * a i)|
          = |∑ a ∈ t, (f a - q a) * a i| := by
            apply congr_arg abs
            apply Finset.sum_congr rfl
            intro a _
            rw [sub_mul]
        _ ≤ ∑ a ∈ t, |(f a - q a) * a i| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ a ∈ t, |f a - q a| * |a i| :=
            Finset.sum_congr rfl fun a _ => abs_mul _ _
        _ ≤ ∑ a ∈ t, δ * |a i| := Finset.sum_le_sum fun a _ =>
            mul_le_mul_of_nonneg_right (le_of_lt (hq a)) (abs_nonneg _)
        _ = δ * ∑ a ∈ t, |a i| := (Finset.mul_sum _ _ _).symm
        _ ≤ δ * B := mul_le_mul_of_nonneg_left (hSi i) (le_of_lt hδ)
        _ = m / 2 := hδB
    have hri : 0 < ((∑ a ∈ t, q a • w a) i : ℝ) := by
      have h2 := abs_le.mp hdiff
      linarith [hm_le i, hm_pos]
    exact Rat.cast_pos.mp hri
  · exact Submodule.sum_mem _ fun a ha => Submodule.smul_mem _ _ (hw a ha).1

/-- If `u` is not proportional to a rational vector, `kerSpanRat` has another vector
linearly independent from any given `r`. (Contrapositive: `kerSpanRat = ℚ·r` would put
`u ∈ ℝ·r`.) -/
theorem exists_kerSpanRat_not_parallel {n : ℕ} (u : Fin n → ℝ) (r : Fin n → ℚ)
    (hr : r ∈ kerSpanRat u)
    (h : ¬ ∃ c : ℝ, ∀ i, u i = c * (r i : ℝ)) :
    ∃ s : Fin n → ℚ, s ∈ kerSpanRat u ∧ ∀ a : ℚ, s ≠ a • r := by
  classical
  rcases n with _ | n
  · exact (h ⟨0, fun i => i.elim0⟩).elim
  by_contra hcon
  push Not at hcon
  -- hcon : every rational kernel vector is a rational multiple of `r`.
  apply h
  have hu : u ∈ Submodule.span ℝ ((fun x : Fin (n + 1) → ℚ => fun i => (x i : ℝ)) ''
      (kerSpanRat u : Set (Fin (n + 1) → ℚ))) := by
    rw [← kerSpan_eq_span_rat]
    exact mem_kerSpan_self u
  rw [Submodule.mem_span_iff_exists_finset_subset] at hu
  obtain ⟨f, t, htK, _hsupp, huc⟩ := hu
  have hwa : ∀ a : Fin (n + 1) → ℝ, ∃ w : Fin (n + 1) → ℚ, ∃ q : ℚ,
      a ∈ t → w ∈ kerSpanRat u ∧ (fun i => (w i : ℝ)) = a ∧ w = q • r := by
    intro a
    by_cases ha : a ∈ t
    · obtain ⟨w', hw'K, hw'eq⟩ := htK ha
      obtain ⟨q', hq'⟩ := hcon w' hw'K
      exact ⟨w', q', fun _ => ⟨hw'K, hw'eq, hq'⟩⟩
    · exact ⟨0, 0, fun h => absurd h ha⟩
  choose w q hw using hwa
  have hui : ∀ i, u i = ∑ a ∈ t, f a * a i := by
    intro i0
    have h1 := congr_fun huc.symm i0
    rw [Finset.sum_apply] at h1
    rw [h1]
    apply Finset.sum_congr rfl
    intro a _
    rw [Pi.smul_apply, smul_eq_mul]
  have hmem : ∀ a ∈ t, ∀ i, a i = (q a : ℝ) * (r i : ℝ) := by
    intro a ha i
    have h1 : a i = ((w a) i : ℝ) := (congr_fun (hw a ha).2.1 i).symm
    rw [h1, (hw a ha).2.2]
    simp [Pi.smul_apply, smul_eq_mul, Rat.cast_mul]
  exact ⟨∑ a ∈ t, f a * (q a : ℝ), fun i => calc
    u i = ∑ a ∈ t, f a * a i := hui i
    _ = ∑ a ∈ t, f a * ((q a : ℝ) * (r i : ℝ)) :=
        Finset.sum_congr rfl fun a ha => by rw [hmem a ha]
    _ = ∑ a ∈ t, (f a * (q a : ℝ)) * (r i : ℝ) :=
        Finset.sum_congr rfl fun a _ => by ring
    _ = (∑ a ∈ t, f a * (q a : ℝ)) * (r i : ℝ) := (Finset.sum_mul _ _ _).symm⟩

/-- **Minimality lemma.** Write `u` in a `ℚ`-basis `ρ` of `kerSpanRat u`:
`u i = ∑ ℓ, c ℓ * ρ ℓ i`. The coefficient tuple `c` is `ℚ`-linearly independent —
a relation among the `c ℓ` would put `u` in the `ℝ`-span of fewer rational vectors,
i.e. a strictly smaller rationally-defined subspace, contradicting the definition of
`kerSpan u` as the annihilator of *all* relations.

**WARNING — this statement is FALSE as frozen** (W6, see `_reports/w6-relations.md`
and the compiling countermodel `Research07/W6Scratch.lean`): `hρspan` only assumes
`kerSpanRat u ⊆ span ρ`, so `ρ` may contain redundant vectors and the coordinates
`c` need not be unique. The corrected version
`kernel_coords_linearIndependent_of_basis` below is proved instead. -/
theorem kernel_coords_linearIndependent {n d : ℕ} (u : Fin n → ℝ) (ρ : Fin d → Fin n → ℚ)
    (hρspan : ∀ x : Fin n → ℚ, x ∈ kerSpanRat u → x ∈ Submodule.span ℚ (Set.range ρ))
    (c : Fin d → ℝ) (hc : ∀ i, u i = ∑ ℓ, c ℓ * (ρ ℓ i : ℝ)) :
    LinearIndependent ℚ c := by
  sorry

/-- **Corrected minimality lemma.** `ρ` must be a `ℚ`-linearly independent family of
kernel vectors (with `hρspan`-style covering, a `ℚ`-basis of `kerSpanRat u`), not
merely a spanning set. Then the real coordinates `c` of `u` are `ℚ`-linearly
independent: a rational relation `∑ g ℓ • c ℓ = 0` with `g ℓ ≠ 0` eliminates `ρ ℓ`,
putting `u` in the real span of a rationally defined subspace missing `ρ ℓ`; a
`ℚ`-linear functional separating `ρ ℓ` from that subspace yields an integer
relation killing `u` but not `ρ ℓ ∈ kerSpanRat u` — contradiction. -/
theorem kernel_coords_linearIndependent_of_basis {n d : ℕ} (u : Fin n → ℝ)
    (ρ : Fin d → Fin n → ℚ)
    (hρmem : ∀ ℓ, ρ ℓ ∈ kerSpanRat u)
    (hρind : LinearIndependent ℚ ρ)
    (c : Fin d → ℝ) (hc : ∀ i, u i = ∑ ℓ, c ℓ * (ρ ℓ i : ℝ)) :
    LinearIndependent ℚ c := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg ℓ
  by_contra hgℓ
  -- Scalar form of the relation `∑ g j • c j = 0`.
  have hg' : ∑ j, (g j : ℝ) * c j = 0 := by
    have h := hg
    simp only [Algebra.smul_def] at h
    simpa using h
  -- `u` is a real combination of the `ρ' j := ρ j - (g j / g ℓ) • ρ ℓ`.
  set ρ' : Fin d → Fin n → ℚ := fun j => ρ j - (g j / g ℓ) • ρ ℓ
  have hu_eq : u = ∑ j, c j • ratCastLM (ρ' j) := by
    funext i
    rw [hc i]
    have hsum0 : ∑ j, c j * ((g j / g ℓ : ℚ) : ℝ) = 0 := by
      have h1 : ∑ j, c j * ((g j / g ℓ : ℚ) : ℝ) =
          (∑ j, c j * (g j : ℝ)) / (g ℓ : ℝ) := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro j _
        rw [Rat.cast_div, ← mul_div_assoc]
      have hgc : ∑ j, c j * (g j : ℝ) = 0 := by
        rw [← hg']
        apply Finset.sum_congr rfl
        intro j _
        ring
      rw [h1, hgc, zero_div]
    calc ∑ j, c j * (ρ j i : ℝ)
        = ∑ j, c j * ((ρ' j) i : ℝ) + (∑ j, c j * ((g j / g ℓ : ℚ) : ℝ)) * (ρ ℓ i : ℝ) := by
          rw [Finset.sum_mul, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro j _
          show c j * (ρ j i : ℝ) =
            c j * (((ρ j - (g j / g ℓ) • ρ ℓ) i : ℚ) : ℝ) +
              c j * ((g j / g ℓ : ℚ) : ℝ) * (ρ ℓ i : ℝ)
          rw [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Rat.cast_sub, Rat.cast_mul]
          ring
      _ = ∑ j, c j * ((ρ' j) i : ℝ) := by rw [hsum0, zero_mul, add_zero]
      _ = (∑ j, c j • ratCastLM (ρ' j)) i := by
          simp [Finset.sum_apply, Pi.smul_apply, ratCastLM_apply, smul_eq_mul]
  -- `ρ ℓ` is not in the rational span of the `ρ' j`.
  have hρ_notmem : ρ ℓ ∉ Submodule.span ℚ (Set.range ρ') := by
    intro hmem
    obtain ⟨q, hq⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).mp hmem
    -- `∑ q j • ρ' j = ρ ℓ` expands to `∑ q j • ρ j = (S + 1) • ρ ℓ`, `S = ∑ q j (g j / g ℓ)`.
    have hexp : ∑ j, q j • ρ j = (∑ j', q j' * (g j' / g ℓ) + 1) • ρ ℓ := by
      have hq' : ∑ j, (q j • ρ j - (q j * (g j / g ℓ)) • ρ ℓ) = ρ ℓ := by
        have hcongr : ∑ j, q j • ρ' j =
            ∑ j, (q j • ρ j - (q j * (g j / g ℓ)) • ρ ℓ) :=
          Finset.sum_congr rfl fun j _ => by
            show q j • (ρ j - (g j / g ℓ) • ρ ℓ) = _
            rw [smul_sub, smul_smul]
        exact hcongr ▸ hq
      rw [Finset.sum_sub_distrib, ← Finset.sum_smul] at hq'
      have h2 : ∑ j, q j • ρ j = ρ ℓ + (∑ j', q j' * (g j' / g ℓ)) • ρ ℓ :=
        sub_eq_iff_eq_add.mp hq'
      rw [h2]
      nth_rewrite 1 [← one_smul ℚ (ρ ℓ)]
      rw [← add_smul, add_comm]
    -- The relation `v j = q j - (if j = ℓ then S + 1 else 0)` kills `ρ` but `v ℓ = -1`.
    have hv_sum : ∑ j, (q j - if j = ℓ then ∑ j', q j' * (g j' / g ℓ) + 1 else 0) • ρ j
        = 0 := by
      have hv_decomp : ∀ j,
          (q j - if j = ℓ then ∑ j', q j' * (g j' / g ℓ) + 1 else 0) • ρ j =
            q j • ρ j - if j = ℓ then (∑ j', q j' * (g j' / g ℓ) + 1) • ρ j else 0 := by
        intro j
        rw [sub_smul]
        by_cases hj : j = ℓ <;> simp [hj]
      calc ∑ j, (q j - if j = ℓ then ∑ j', q j' * (g j' / g ℓ) + 1 else 0) • ρ j
          = ∑ j, (q j • ρ j -
              if j = ℓ then (∑ j', q j' * (g j' / g ℓ) + 1) • ρ j else 0) :=
            Finset.sum_congr rfl fun j _ => hv_decomp j
        _ = (∑ j, q j • ρ j) -
              ∑ j, (if j = ℓ then (∑ j', q j' * (g j' / g ℓ) + 1) • ρ j else 0) :=
            Finset.sum_sub_distrib _ _
        _ = (∑ j, q j • ρ j) - (∑ j', q j' * (g j' / g ℓ) + 1) • ρ ℓ := by
            rw [Finset.sum_ite_eq', ite_eq_left (Finset.mem_univ ℓ)]
        _ = 0 := by rw [hexp, sub_self]
    have hv0 := (Fintype.linearIndependent_iff.mp hρind)
      (fun j => q j - if j = ℓ then ∑ j', q j' * (g j' / g ℓ) + 1 else 0) hv_sum
    have hq_ne : ∀ j, j ≠ ℓ → q j = 0 := fun j hj => by
      have := hv0 j
      simpa [hj] using this
    have hS : ∑ j', q j' * (g j' / g ℓ) = q ℓ := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ ℓ)]
      have h2 : ∑ j' ∈ Finset.univ.erase ℓ, q j' * (g j' / g ℓ) = 0 :=
        Finset.sum_eq_zero fun j hj => by
          rw [hq_ne j (Finset.ne_of_mem_erase hj), zero_mul]
      rw [h2, add_zero]
      have : q ℓ * (g ℓ / g ℓ) = q ℓ := by rw [div_self hgℓ, mul_one]
      exact this
    have := hv0 ℓ
    simp [hS] at this
  -- A rational functional separating `ρ ℓ` from `span ρ'` gives a rational
  -- relation on `u`; clearing denominators gives an integer relation.
  obtain ⟨f, hfv, hpf⟩ := Submodule.exists_le_ker_of_notMem hρ_notmem
  set k : Fin n → ℚ := fun i => f (Pi.single i 1)
  have hpi : ∀ x : Fin n → ℚ, x = ∑ i, x i • Pi.single i (1 : ℚ) := by
    intro x
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  have hfk : ∀ x : Fin n → ℚ, f x = ∑ i, x i * k i := by
    intro x
    conv_lhs => rw [hpi x]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul, smul_eq_mul]
  have hf0 : ∀ j, f (ρ' j) = 0 := fun j =>
    LinearMap.mem_ker.mp (hpf (Submodule.subset_span ⟨j, rfl⟩))
  have hku : ∑ i, (k i : ℝ) * u i = 0 := by
    rw [hu_eq]
    simp only [Finset.sum_apply, Pi.smul_apply, ratCastLM_apply, smul_eq_mul]
    rw [Finset.sum_congr rfl fun i _ => Finset.mul_sum _ _ _, Finset.sum_comm]
    have hinner : ∀ j, ∑ i, (k i : ℝ) * (c j * ((ρ' j) i : ℝ)) =
        c j * ((f (ρ' j) : ℚ) : ℝ) := by
      intro j
      rw [hfk (ρ' j), Rat.cast_sum]
      have hterm : ∀ i, (k i : ℝ) * (c j * ((ρ' j) i : ℝ)) =
          c j * ((((ρ' j) i * k i : ℚ)) : ℝ) := fun i => by
        rw [Rat.cast_mul]; ring
      rw [Finset.sum_congr rfl fun i _ => hterm i, ← Finset.mul_sum]
    rw [Finset.sum_congr rfl fun j _ => hinner j]
    simp [hf0]
  -- Clear denominators: `k' i = N * k i ∈ ℤ` where `N = ∏ (k i).den`.
  set k' : Fin n → ℤ := fun i =>
    (k i).num * ∏ j ∈ Finset.univ.erase i, ((k j).den : ℤ) with hk'
  have hN_pos : 0 < ∏ i, (k i).den := Finset.prod_pos fun i _ => Rat.den_pos _
  have hz : ∀ i, ((∏ j, (k j).den : ℕ) : ℚ) * k i = (k' i : ℚ) := by
    intro i
    have hsplit : (∏ j, (k j).den : ℕ) =
        (k i).den * ∏ j ∈ Finset.univ.erase i, (k j).den :=
      (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm
    calc ((∏ j, (k j).den : ℕ) : ℚ) * k i
        = (((k i).den : ℚ) * ∏ j ∈ Finset.univ.erase i, ((k j).den : ℚ)) * k i := by
          rw [hsplit]
          push_cast
          rfl
      _ = ((k i).num : ℚ) * ∏ j ∈ Finset.univ.erase i, ((k j).den : ℚ) := by
          rw [mul_right_comm, Rat.den_mul_eq_num]
      _ = (k' i : ℚ) := by
          simp only [hk']
          push_cast
          rfl
  have hk'_mem : k' ∈ relLattice u := by
    rw [relLattice, LinearMap.mem_ker, Fintype.linearCombination_apply]
    have h1 : ∀ i, (k' i) • u i = (k' i : ℝ) * u i := fun i => zsmul_eq_mul _ _
    rw [Finset.sum_congr rfl fun i _ => h1 i]
    have h2 : ∀ i, (k' i : ℝ) = ((∏ j, (k j).den : ℕ) : ℝ) * (k i : ℝ) := fun i => by
      have := congr_arg (fun x : ℚ => (x : ℝ)) (hz i)
      simp only [Rat.cast_mul, Rat.cast_natCast, Rat.cast_intCast] at this
      exact this.symm
    rw [Finset.sum_congr rfl fun i _ => congrArg (· * u i) (h2 i)]
    simp only [mul_assoc]
    rw [← Finset.mul_sum, hku, mul_zero]
  -- The relation `k'` kills `ρ ℓ ∈ kerSpanRat u`, i.e. `N * f (ρ ℓ) = 0`.
  have hρrel : ∑ i, (k' i : ℚ) * (ρ ℓ) i = 0 := hρmem ℓ k' hk'_mem
  have hNf : ((∏ i, (k i).den : ℕ) : ℚ) * f (ρ ℓ) = 0 := by
    have h2 : f (ρ ℓ) = ∑ i, k i * (ρ ℓ) i := by
      rw [hfk]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [h2, Finset.mul_sum]
    have h3 : ∑ i, ((∏ j, (k j).den : ℕ) : ℚ) * (k i * (ρ ℓ) i) =
        ∑ i, (k' i : ℚ) * (ρ ℓ) i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← hz i]
      ring
    rw [h3, hρrel]
  have hN_ne : ((∏ i, (k i).den : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hN_pos.ne'
  exact hfv ((mul_eq_zero.mp hNf).resolve_left hN_ne)

end
