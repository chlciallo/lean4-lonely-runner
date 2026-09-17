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
  exact (kerSpanRat u).sub_mem
    ((kerSpanRat u).smul_mem _ hs) ((kerSpanRat u).smul_mem _ hr)

theorem bhk_w_eq_neg {n : ℕ} {r s : Fin n → ℚ} {i j : Fin n} :
    ((r i + r j : ℚ) • s - (s i + s j : ℚ) • r) i =
      -(((r i + r j : ℚ) • s - (s i + s j : ℚ) • r) j) := by
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem bhk_w_ne_zero {n : ℕ} {u : Fin n → ℝ} {r s : Fin n → ℚ}
    {i j : Fin n} (hrpos : ∀ k, 0 < r k)
    (hi : ∀ k, s k / r k ≤ s i / r i) (hj : ∀ k, s j / r j ≤ s k / r k)
    (hij : s i / r i < s j / r j) (k : Fin n) :
    ((r i + r j : ℚ) • s - (s i + s j : ℚ) • r) k ≠ 0 := by
  -- The hypotheses as stated are mutually inconsistent: `hj i` gives
  -- `s j / r j ≤ s i / r i`, contradicting `hij`. (The intended statement has
  -- `i` minimizing and `j` maximizing with adjacent ratio values; the assembly
  -- below proves the needed nonvanishing inline.)
  exact absurd (hj i) (not_le.mpr hij)

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
  -- (i) A positive rational point `r` of `kerSpanRat u`, and a rational `s` in the
  -- kernel not parallel to `r` (else `u` would be rationally proportional).
  obtain ⟨r, hrpos, hr⟩ := exists_pos_rat_kerSpan u hpos
  have hnp : ¬ ∃ c : ℝ, ∀ i, u i = c * (r i : ℝ) := by
    rintro ⟨c, hc⟩
    exact hirr ⟨c, fun i => ⟨r i, hc i⟩⟩
  obtain ⟨s, hs, hsnp⟩ := exists_kerSpanRat_not_parallel u r hr hnp
  -- (ii) Adjacent ratio values: `j` maximizes `sₖ/rₖ`; `i` maximizes it among the
  -- indices strictly below `s j / r j`. Then no `s k / r k` lies in the open
  -- interval `(s i / r i, s j / r j)`.
  obtain ⟨j, -, hjmax⟩ := Finset.univ.exists_max_image (fun k => s k / r k)
    ⟨0, Finset.mem_univ 0⟩
  have hTne : (Finset.univ.filter fun k => s k / r k < s j / r j).Nonempty := by
    by_contra hT'
    rw [Finset.not_nonempty_iff_eq_empty] at hT'
    apply hsnp (s j / r j)
    funext k
    have hlt : ¬ s k / r k < s j / r j := by
      have hk : k ∉ Finset.univ.filter (fun k => s k / r k < s j / r j) := by
        rw [hT']; exact Finset.notMem_empty k
      rw [Finset.mem_filter] at hk
      exact fun h => hk ⟨Finset.mem_univ k, h⟩
    have heq : s k / r k = s j / r j :=
      le_antisymm (hjmax k (Finset.mem_univ k)) (not_lt.mp hlt)
    change s k = (s j / r j) • r k
    rw [smul_eq_mul, ← heq]
    exact (div_mul_cancel₀ (s k) (hrpos k).ne').symm
  obtain ⟨i, hiT, himax⟩ := (Finset.univ.filter fun k => s k / r k < s j / r j).exists_max_image
    (fun k => s k / r k) hTne
  have hij : s i / r i < s j / r j := (Finset.mem_filter.mp hiT).2
  have hinej : i ≠ j := by
    rintro rfl
    exact absurd hij (lt_irrefl _)
  have hadj : ∀ k : Fin 4, s k / r k ≤ s i / r i ∨ s j / r j ≤ s k / r k := by
    intro k
    rcases lt_or_ge (s k / r k) (s j / r j) with hlt | hge
    · exact Or.inl (himax k (Finset.mem_filter.mpr ⟨Finset.mem_univ k, hlt⟩))
    · exact Or.inr hge
  -- (iii) The equal-coordinates vector `w = (rᵢ+rⱼ)·s − (sᵢ+sⱼ)·r`.
  set w : Fin 4 → ℚ := (r i + r j) • s - (s i + s j) • r with hwdef
  have hwmem : w ∈ kerSpanRat u := by
    rw [hwdef]; exact bhk_w_mem_kerSpanRat hr hs
  have hwneg : w i = -w j := by
    rw [hwdef]; exact bhk_w_eq_neg
  have hwne : ∀ k : Fin 4, w k ≠ 0 := by
    intro k hwk
    have hwk' : (r i + r j) * s k = (s i + s j) * r k := by
      rw [hwdef] at hwk
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hwk
      exact sub_eq_zero.mp hwk
    -- `w k = 0` forces `s k / r k` to be the mediant, strictly between the two
    -- extremal ratios — contradicting the adjacency property.
    have hsk : s k / r k = (s i + s j) / (r i + r j) := by
      rw [div_eq_div_iff (hrpos k).ne' (add_pos (hrpos i) (hrpos j)).ne']
      linear_combination hwk'
    have hij' : s i * r j < s j * r i := by
      rwa [div_lt_div_iff₀ (hrpos i) (hrpos j)] at hij
    have hmi : s i / r i < (s i + s j) / (r i + r j) := by
      rw [div_lt_div_iff₀ (hrpos i) (add_pos (hrpos i) (hrpos j))]
      nlinarith
    have hmj : (s i + s j) / (r i + r j) < s j / r j := by
      rw [div_lt_div_iff₀ (add_pos (hrpos i) (hrpos j)) (hrpos j)]
      nlinarith
    rcases hadj k with h | h
    · rw [← hsk] at hmi; exact absurd hmi (not_lt.mpr h)
    · rw [← hsk] at hmj; exact absurd hmj (not_lt.mpr h)
  -- (iv) The set `S = {|wₖ|}` has ≤ 3 elements (`|wᵢ| = |wⱼ|` is one collision).
  have hSpos : ∀ q ∈ Finset.univ.image (fun k => |w k|), 0 < q := by
    intro q hq
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hq
    exact abs_pos.mpr (hwne k)
  have hScard : (Finset.univ.image fun k => |w k|).card ≤ 3 := by
    have hsub : Finset.univ.image (fun k => |w k|) ⊆
        (Finset.univ.erase i).image fun k => |w k| := by
      intro q hq
      obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hq
      by_cases hki : k = i
      · subst hki
        exact Finset.mem_image.mpr
          ⟨j, Finset.mem_erase.mpr ⟨fun h => hinej h.symm, Finset.mem_univ j⟩,
            by rw [hwneg, abs_neg]⟩
      · exact Finset.mem_image.mpr ⟨k, Finset.mem_erase.mpr ⟨hki, Finset.mem_univ k⟩, rfl⟩
    calc (Finset.univ.image fun k => |w k|).card
        ≤ ((Finset.univ.erase i).image fun k => |w k|).card := Finset.card_le_card hsub
      _ ≤ (Finset.univ.erase i).card := Finset.card_image_le
      _ = 3 := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
            Fintype.card_fin]
  obtain ⟨t, htpos, ht⟩ := hlrc4 _ hSpos hScard
  -- `circ (t·wₖ) ≥ 1/4` for every `k` (`t > 0`, `circ` ignores the sign).
  have htk : ∀ k : Fin 4, (1 / 4 : ℝ) ≤ circ (t * (w k : ℝ)) := by
    intro k
    have hq : |w k| ∈ Finset.univ.image (fun k => |w k|) :=
      Finset.mem_image.mpr ⟨k, Finset.mem_univ k, rfl⟩
    have h := ht _ hq
    rw [Rat.cast_abs, ← abs_of_pos htpos, ← abs_mul, circ_abs] at h
    exact h
  -- (v) `δ = 9/40 ∈ (1/5, 1/4)` and `y := i ↦ t·wᵢ ∈ T` lies in the annihilator.
  set δ : ℝ := 9 / 40 with hδdef
  have hδlt : δ < 1 / 4 := by norm_num [hδdef]
  have hδgt : (1 / 5 : ℝ) < δ := by norm_num [hδdef]
  have hδpos : 0 < δ := by norm_num [hδdef]
  have hcirc : ∀ k : Fin 4, δ < circ (t * (w k : ℝ)) := fun k => hδlt.trans_le (htk k)
  have hy_ann : (fun i => ((t * (w i : ℝ) : ℝ) : UnitAddCircle)) ∈ annihilator u := by
    intro k hk
    have hwQ : (∑ i, (k i : ℝ) * (w i : ℝ)) = 0 := by
      have h := hwmem k hk
      have hR := congrArg (fun q : ℚ => (q : ℝ)) h
      push_cast at hR
      simpa using hR
    have hsum0 : (∑ i, (k i : ℝ) * (t * (w i : ℝ))) = 0 := by
      calc (∑ i, (k i : ℝ) * (t * (w i : ℝ)))
          = ∑ i, t * ((k i : ℝ) * (w i : ℝ)) :=
            Finset.sum_congr rfl fun i _ => by ring
        _ = t * ∑ i, (k i : ℝ) * (w i : ℝ) := (Finset.mul_sum _ _ _).symm
        _ = 0 := by rw [hwQ, mul_zero]
    calc (∑ i, (k i) • ((t * (w i : ℝ) : ℝ) : UnitAddCircle))
        = ∑ i, (((k i : ℝ) * (t * (w i : ℝ)) : ℝ) : UnitAddCircle) := by
          apply Finset.sum_congr rfl; intro i _
          rw [← AddCircle.coe_zsmul, zsmul_eq_mul]
      _ = ((∑ i, (k i : ℝ) * (t * (w i : ℝ)) : ℝ) : UnitAddCircle) := by
          have hm := (map_sum (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ)))
            (fun i => (k i : ℝ) * (t * (w i : ℝ))) Finset.univ).symm
          simpa only [QuotientAddGroup.mk'_apply] using hm
      _ = ((0 : ℝ) : UnitAddCircle) := by rw [hsum0]
      _ = 0 := AddCircle.coe_zero (1 : ℝ)
  -- (vi) The cube `U = {∀ i, δ < ‖y i‖}` is open and contains `y`; orbit density
  -- supplies an orbit point in `U`, and `circ` kills its sign.
  have hUopen : IsOpen {y : Fin 4 → UnitAddCircle | ∀ i, δ < ‖y i‖} := by
    have heq : {y : Fin 4 → UnitAddCircle | ∀ i, δ < ‖y i‖} =
        ⋂ i : Fin 4, {y : Fin 4 → UnitAddCircle | δ < ‖y i‖} := by
      ext y
      simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    rw [heq]
    exact isOpen_iInter_of_finite fun i =>
      isOpen_lt continuous_const
        ((continuous_apply i).norm :
          Continuous fun y : Fin 4 → UnitAddCircle => ‖y i‖)
  have hyU : (fun i => ((t * (w i : ℝ) : ℝ) : UnitAddCircle)) ∈
      {y : Fin 4 → UnitAddCircle | ∀ i, δ < ‖y i‖} := fun i => hcirc i
  obtain ⟨z, hzI⟩ := (mem_closure_iff.mp (orbit_dense_annihilator u hy_ann) _
    hUopen hyU)
  obtain ⟨hzU, hzr⟩ := hzI
  obtain ⟨t', ht'⟩ := hzr
  have hδt : ∀ i : Fin 4, δ < circ (t' * u i) := by
    intro i
    have hzi := hzU i
    rw [← ht'] at hzi
    exact hzi
  have ht'ne : t' ≠ 0 := by
    rintro rfl
    have h0 := hδt 0
    rw [zero_mul] at h0
    have hc0 : circ (0 : ℝ) = 0 := by
      change ‖((0 : ℝ) : UnitAddCircle)‖ = 0
      rw [AddCircle.coe_zero, norm_zero]
    rw [hc0] at h0
    exact absurd h0 (not_lt.mpr hδpos.le)
  refine ⟨|t'|, abs_pos.mpr ht'ne, fun i => ?_⟩
  have hc : circ (|t'| * u i) = circ (t' * u i) := by
    have e : |t'| * u i = |t' * u i| := by
      rw [abs_mul, abs_of_pos (hpos i)]
    rw [e, circ_abs]
  rw [hc]
  exact hδgt.trans (hδt i)

end
