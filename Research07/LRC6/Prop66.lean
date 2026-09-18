/-
Copyright (c) 2026 Research07 contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Research07 contributors
-/
import Mathlib
import Research07.LRC6.Setup
import Research07.LRC6.Extremize
import Research07.LRC6.Driver
import Research07.LRC6.Signed

/-!
# Renault Proposition 6.6 (exactly two even speeds)

Setup: `v₁` is the multiple of `6`; `u` has residue `e_u = ±2`; `w x y z`
(the `±1` guards) are odd.  Two cases on which guard anchors the extremal time:

* `prop66_role_two` — the `±2`-runner `u` sits at `5/6`.  Lemma 6.5 applies at
  `tstar` itself (the three odd guards are all in `[1/6,5/6]` there), giving
  `(λ,α) ∈ {(2,0)} ∪ ({1}×{1,5}) ∪ ({3,5}×{0..5})` and `s = λ·tstar + α/6`.
  The `±2`-anchor lands on `⟨5λ/6 + e_u·α/6⟩ ∈ {1/6,1/2,4/6,5/6}`.
* `prop66_role_one` — an odd runner `w` sits at `5/6`.  Reset via
  `t̃ = tstar + e_w/6` (`x_w ↦ 0`), then Lemma 6.2 (`e_w = 1`) or 6.3
  (`e_w = -1`) on `(x_u(t̃), e_u/2)` — the `±2` runner takes the doubled
  shift `2ε·α/6 = e_u·α/6` — and `(x_y, e_y), (x_z, e_z)`.
-/

noncomputable section

/-- The `±2`-anchor's safety under Lemma 6.5's `(λ,α) ∈ {3,5}×{0..5}` moves
(also covers `(2,0)`): `⟨5λ/6 + e·α/6⟩ = (5λ + eα)/6 mod 1` never hits `0`. -/
theorem anchor2_safe {lam al : ℕ} {e : ℤ} (he : e = 2 ∨ e = -2)
    (h : ((lam = 3 ∨ lam = 5) ∧ al ≤ 5) ∨ (lam = 2 ∧ al = 0)) :
    Int.fract ((lam : ℝ) * (5 / 6) + (e : ℝ) * (al : ℝ) / 6) ∈
      Set.Icc (1 / 6) (5 / 6) := by
  have hsum : (lam : ℝ) * (5 / 6) + (e : ℝ) * (al : ℝ) / 6 =
      (((5 * (lam : ℤ) + e * (al : ℤ)) : ℤ) : ℝ) / 6 := by push_cast; ring
  rw [hsum, fract_intCast_div_six]
  rcases h with ⟨hlam, hal⟩ | ⟨hlam, hal⟩
  · rcases hlam with rfl | rfl <;> rcases he with rfl | rfl <;>
      interval_cases al <;>
      refine Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩
  · subst hlam; subst hal
    rcases he with rfl | rfl <;>
      refine Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩

/-- The `±2`-anchor's strict safety under Lemma 6.5's `(1,α)`, `α ∈ {1,5}`:
`⟨5/6 + eα/6⟩ ∈ {1/6, 1/2}`. -/
theorem anchor2_safe_one {al : ℕ} {e : ℤ} (he : e = 2 ∨ e = -2)
    (hal : al = 1 ∨ al = 5) :
    Int.fract (5 / 6 + (e : ℝ) * (al : ℝ) / 6) ∈ Set.Ico (1 / 6) (5 / 6) := by
  have hsum : (5 : ℝ) / 6 + (e : ℝ) * (al : ℝ) / 6 =
      (((5 + e * (al : ℤ)) : ℤ) : ℝ) / 6 := by push_cast; ring
  rw [hsum, fract_intCast_div_six]
  rcases he with rfl | rfl <;> rcases hal with rfl | rfl <;>
    refine Set.mem_Ico.mpr ⟨by norm_num, by norm_num⟩

/-- Case 1 of Proposition 6.6: the `±2`-runner `u` anchors at `5/6`. -/
theorem prop66_role_two {v₁ u x y z : ℕ} (hv1 : 6 ∣ v₁)
    {eu ex ey ez : ℤ}
    (heu : eu = 2 ∨ eu = -2) (hex : ex = 1 ∨ ex = -1)
    (hey : ey = 1 ∨ ey = -1) (hez : ez = 1 ∨ ez = -1)
    (hu : (u : ℤ) ≡ eu [ZMOD 6]) (hxe : (x : ℤ) ≡ ex [ZMOD 6])
    (hye : (y : ℤ) ≡ ey [ZMOD 6]) (hze : (z : ℤ) ≡ ez [ZMOD 6])
    {tstar : ℝ}
    (hu56 : Int.fract ((u : ℝ) * tstar) = 5 / 6)
    (hxI : Int.fract ((x : ℝ) * tstar) ∈ Set.Icc (1 / 6) (5 / 6))
    (hyI : Int.fract ((y : ℝ) * tstar) ∈ Set.Icc (1 / 6) (5 / 6))
    (hzI : Int.fract ((z : ℝ) * tstar) ∈ Set.Icc (1 / 6) (5 / 6))
    (hxa : Int.fract ((v₁ : ℝ) * tstar) ∈ Set.Ioo 0 (1 / 6))
    (hmax : ∀ t : ℝ, (∀ d ∈ ({u, x, y, z} : Finset ℕ),
        Int.fract ((d : ℝ) * t) ∈ Set.Icc (1 / 6) (5 / 6)) →
      circ ((v₁ : ℝ) * t) ≤ circ ((v₁ : ℝ) * tstar))
    (hguards : ({u, x, y, z} : Finset ℕ).Nonempty)
    (hpos : ∀ d ∈ ({u, x, y, z} : Finset ℕ), 0 < d) : False := by
  classical
  have mem4 : ∀ d : ℕ, d ∈ ({u, x, y, z} : Finset ℕ) →
      d = u ∨ d = x ∨ d = y ∨ d = z := by
    intro d hd
    rwa [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert,
      Finset.mem_singleton] at hd
  rcases lemma6_5 hex hey hez hxI hyI hzI with h | h | h
  · -- `(2,0)`: `⟨2xᵢ⟩` strictly inside for all three odd guards.
    obtain ⟨t3, t4, t5⟩ := h
    refine improve_ge_two_contra (lam := 2) (al := 0) hv1 _ hxa rfl hmax ?_ (by norm_num) (by norm_num)
    intro d hd
    rcases mem4 d hd with rfl | rfl | rfl | rfl
    · have hs := fract_lambda_alpha hu tstar 2 0
      rw [hs, hu56]
      exact anchor2_safe heu (Or.inr ⟨rfl, rfl⟩)
    · have hs := fract_lambda_alpha hxe tstar 2 0
      rw [hs]
      simp only [Nat.cast_zero, zero_div, mul_zero, add_zero, Nat.cast_ofNat]
      exact Set.Ioo_subset_Icc_self t3
    · have hs := fract_lambda_alpha hye tstar 2 0
      rw [hs]
      simp only [Nat.cast_zero, zero_div, mul_zero, add_zero, Nat.cast_ofNat]
      exact Set.Ioo_subset_Icc_self t4
    · have hs := fract_lambda_alpha hze tstar 2 0
      rw [hs]
      simp only [Nat.cast_zero, zero_div, mul_zero, add_zero, Nat.cast_ofNat]
      exact Set.Ioo_subset_Icc_self t5
  · -- `(1,α)`, `α ∈ {1,5}`: perturbation case.
    obtain ⟨al, hal, t3, t4, t5⟩ := h
    refine improve_eq_one_contra (al := al) hv1 _ hguards hpos hxa rfl hmax ?_
    intro d hd
    rcases mem4 d hd with rfl | rfl | rfl | rfl
    · have hs := fract_lambda_alpha hu tstar 1 al
      simp only [Nat.cast_one, one_mul] at hs
      rw [hs, hu56]
      exact anchor2_safe_one heu hal
    · have hs := fract_lambda_alpha hxe tstar 1 al
      simp only [Nat.cast_one, one_mul] at hs
      rw [hs]
      exact Set.Ioo_subset_Ico_self t3
    · have hs := fract_lambda_alpha hye tstar 1 al
      simp only [Nat.cast_one, one_mul] at hs
      rw [hs]
      exact Set.Ioo_subset_Ico_self t4
    · have hs := fract_lambda_alpha hze tstar 1 al
      simp only [Nat.cast_one, one_mul] at hs
      rw [hs]
      exact Set.Ioo_subset_Ico_self t5
  · -- `(λ,α) ∈ {3,5}×{0..5}`.
    obtain ⟨lam, al, hlam, hle, t3, t4, t5⟩ := h
    have hl2 : 2 ≤ lam := by rcases hlam with rfl | rfl <;> norm_num
    have hl5 : lam ≤ 5 := by rcases hlam with rfl | rfl <;> norm_num
    refine improve_ge_two_contra (lam := lam) (al := al) hv1 _ hxa rfl hmax ?_ hl2 hl5
    intro d hd
    rcases mem4 d hd with rfl | rfl | rfl | rfl
    · have hs := fract_lambda_alpha hu tstar lam al
      rw [hs, hu56]
      exact anchor2_safe heu (Or.inl ⟨hlam, hle⟩)
    · have hs := fract_lambda_alpha hxe tstar lam al
      rw [hs]
      exact t3
    · have hs := fract_lambda_alpha hye tstar lam al
      rw [hs]
      exact t4
    · have hs := fract_lambda_alpha hze tstar lam al
      rw [hs]
      exact t5

/-- Case 2 of Proposition 6.6: an odd runner `w` anchors at `5/6`; `u` is the
`±2`-runner taking the doubled shift. -/
theorem prop66_role_one {v₁ w u y z : ℕ} (hv1 : 6 ∣ v₁)
    {ew eu ey ez : ℤ}
    (hew : ew = 1 ∨ ew = -1) (heu : eu = 2 ∨ eu = -2)
    (hey : ey = 1 ∨ ey = -1) (hez : ez = 1 ∨ ez = -1)
    (hw : (w : ℤ) ≡ ew [ZMOD 6]) (hu : (u : ℤ) ≡ eu [ZMOD 6])
    (hye : (y : ℤ) ≡ ey [ZMOD 6]) (hze : (z : ℤ) ≡ ez [ZMOD 6])
    {tstar : ℝ}
    (hw56 : Int.fract ((w : ℝ) * tstar) = 5 / 6)
    (hxa : Int.fract ((v₁ : ℝ) * tstar) ∈ Set.Ioo 0 (1 / 6))
    (hmax : ∀ t : ℝ, (∀ d ∈ ({w, u, y, z} : Finset ℕ),
        Int.fract ((d : ℝ) * t) ∈ Set.Icc (1 / 6) (5 / 6)) →
      circ ((v₁ : ℝ) * t) ≤ circ ((v₁ : ℝ) * tstar))
    (hguards : ({w, u, y, z} : Finset ℕ).Nonempty)
    (hpos : ∀ d ∈ ({w, u, y, z} : Finset ℕ), 0 < d) : False := by
  classical
  set ttilde : ℝ := tstar + (ew : ℝ) / 6 with htt
  have haτ : Int.fract ((v₁ : ℝ) * ttilde) = Int.fract ((v₁ : ℝ) * tstar) := by
    rw [htt]
    exact fract_signed_shift_anchor hv1 tstar ew
  have hw0 : Int.fract ((w : ℝ) * ttilde) = 0 := by
    rw [htt, fract_signed_shift hw, hw56]
    have he2 : (ew : ℝ) * ew = 1 := by
      rcases hew with rfl | rfl <;> · push_cast; norm_num
    rw [he2, show (5 / 6 : ℝ) + 1 / 6 = ((1 : ℤ) : ℝ) by norm_num]
    exact Int.fract_intCast 1
  have huI : Int.fract ((u : ℝ) * ttilde) ∈ Set.Ico 0 1 :=
    ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
  have hyI : Int.fract ((y : ℝ) * ttilde) ∈ Set.Ico 0 1 :=
    ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
  have hzI : Int.fract ((z : ℝ) * ttilde) ∈ Set.Ico 0 1 :=
    ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
  have mem4 : ∀ d : ℕ, d ∈ ({w, u, y, z} : Finset ℕ) →
      d = w ∨ d = u ∨ d = y ∨ d = z := by
    intro d hd
    rwa [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert,
      Finset.mem_singleton] at hd
  -- the `±2`-runner's halved residue is the `±1` sign used by Lemma 6.2/6.3.
  have heu2 : (eu / 2 : ℤ) = 1 ∨ (eu / 2 : ℤ) = -1 := by
    rcases heu with rfl | rfl <;> norm_num
  have h2e : (2 : ℝ) * ((eu / 2 : ℤ) : ℝ) = (eu : ℝ) := by
    rcases heu with rfl | rfl <;> norm_num
  rcases hew with rfl | rfl
  · -- `e_w = 1`: Lemma 6.2.
    rcases lemma6_2 heu2 hey hez huI hyI hzI with h | h
    · obtain ⟨lam, al, hl2, hl5, ha1, ha5, t4, t5, t2⟩ := h
      refine improve_ge_two_contra (lam := lam) (al := al) hv1 _ hxa haτ hmax ?_ hl2 hl5
      intro d hd
      rcases mem4 d hd with rfl | rfl | rfl | rfl
      · rw [fract_lambda_alpha hw, hw0]
        simp only [mul_zero, zero_add, Int.cast_one, one_mul]
        exact alpha_Icc ha1 ha5
      · have hs := fract_lambda_alpha hu ttilde lam al
        rw [hs, ← h2e]; exact t2
      · rw [fract_lambda_alpha hye]; exact t4
      · rw [fract_lambda_alpha hze]; exact t5
    · obtain ⟨al, hal, t4, t5, t2⟩ := h
      have ha14 : 1 ≤ al ∧ al ≤ 4 := by
        rcases hal with rfl | rfl | rfl | rfl <;> omega
      refine improve_eq_one_contra (al := al) hv1 _ hguards hpos hxa haτ hmax ?_
      intro d hd
      rcases mem4 d hd with rfl | rfl | rfl | rfl
      · have hs := fract_lambda_alpha hw ttilde 1 al
        simp only [Nat.cast_one, one_mul] at hs
        rw [hs, hw0, zero_add, Int.cast_one, one_mul]
        exact alpha_Ico ha14.1 ha14.2
      · have hs := fract_lambda_alpha hu ttilde 1 al
        simp only [Nat.cast_one, one_mul] at hs
        rw [hs, ← h2e]
        exact Set.Ioo_subset_Ico_self t2
      · have hs := fract_lambda_alpha hye ttilde 1 al
        simp only [Nat.cast_one, one_mul] at hs
        rw [hs]
        exact Set.Ioo_subset_Ico_self t4
      · have hs := fract_lambda_alpha hze ttilde 1 al
        simp only [Nat.cast_one, one_mul] at hs
        rw [hs]
        exact Set.Ioo_subset_Ico_self t5
  · -- `e_w = -1`: Lemma 6.3; the shift is `(6-α)/6` in case (1).
    rcases lemma6_3 heu2 hey hez huI hyI hzI with h | h
    · obtain ⟨lam, al, hl2, hl5, ha1, ha5, t4, t5, t2⟩ := h
      have hcast : ((6 - al : ℕ) : ℝ) = 6 - (al : ℝ) := by
        rw [Nat.cast_sub (by omega : al ≤ 6)]; norm_num
      refine improve_ge_two_contra (lam := lam) (al := 6 - al) hv1 _ hxa haτ hmax ?_ hl2 hl5
      intro d hd
      rcases mem4 d hd with rfl | rfl | rfl | rfl
      · have hs := fract_lambda_alpha hw ttilde lam (6 - al)
        rw [hs, hw0]
        simp only [mul_zero, zero_add, Int.cast_neg, Int.cast_one, neg_one_mul,
          neg_div]
        exact neg_alpha_Icc (by omega : 1 ≤ 6 - al) (by omega : 6 - al ≤ 5)
      · have hs := fract_lambda_alpha hu ttilde lam (6 - al)
        rw [hs, hcast]
        have := t2
        rw [h2e] at this
        exact this
      · have hs := fract_lambda_alpha hye ttilde lam (6 - al)
        rw [hs, hcast]; exact t4
      · have hs := fract_lambda_alpha hze ttilde lam (6 - al)
        rw [hs, hcast]; exact t5
    · obtain ⟨al, hal, t4, t5, t2⟩ := h
      have ha25 : 2 ≤ al ∧ al ≤ 5 := by
        rcases hal with rfl | rfl | rfl | rfl <;> omega
      refine improve_eq_one_contra (al := al) hv1 _ hguards hpos hxa haτ hmax ?_
      intro d hd
      rcases mem4 d hd with rfl | rfl | rfl | rfl
      · have hs := fract_lambda_alpha hw ttilde 1 al
        simp only [Nat.cast_one, one_mul] at hs
        rw [hs, hw0, zero_add, Int.cast_neg, Int.cast_one, neg_one_mul, neg_div]
        exact neg_alpha_Ico ha25.1 ha25.2
      · have hs := fract_lambda_alpha hu ttilde 1 al
        simp only [Nat.cast_one, one_mul] at hs
        rw [hs, ← h2e]
        exact Set.Ioo_subset_Ico_self t2
      · have hs := fract_lambda_alpha hye ttilde 1 al
        simp only [Nat.cast_one, one_mul] at hs
        rw [hs]
        exact Set.Ioo_subset_Ico_self t4
      · have hs := fract_lambda_alpha hze ttilde 1 al
        simp only [Nat.cast_one, one_mul] at hs
        rw [hs]
        exact Set.Ioo_subset_Ico_self t5

/-- Renault Proposition 6.6: exactly two even speeds (the multiple of 6 plus
one `±2`-residue guard) — contradiction from failure. -/
theorem prop6_6 {v₁ : ℕ} (hv1 : 6 ∣ v₁) (hv1pos : 0 < v₁)
    {guards : Finset ℕ} (hg4 : guards.card = 4)
    (hpos : ∀ d ∈ guards, 0 < d)
    {u : ℕ} (hu_mem : u ∈ guards)
    (heu : ∃ e : ℤ, (e = 2 ∨ e = -2) ∧ (u : ℤ) ≡ e [ZMOD 6])
    (hres : ∀ d ∈ guards, d ≠ u →
      ∃ e : ℤ, (e = 1 ∨ e = -1) ∧ (d : ℤ) ≡ e [ZMOD 6])
    (hseed : ∃ τ : ℝ, ∀ d ∈ guards, (1 / 5 : ℝ) ≤ circ (τ * d))
    (hns : ∀ t : ℝ, (∀ d ∈ guards, Int.fract ((d : ℝ) * t) ∈
        Set.Icc (1 / 6) (5 / 6)) → |off v₁ t| < 1 / 6) : False := by
  classical
  have hne : guards.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨tstar, hsafe, hx0, hx6, hfmax, hcmax, d₀, hd₀, h56⟩ :=
    renault6_maximize guards hne hpos hv1pos hns hseed
  obtain ⟨eu, heu', hu⟩ := heu
  by_cases hdu : d₀ = u
  · -- the `±2`-runner anchors: Lemma 6.5 applies at `tstar`.
    rw [hdu] at h56
    have hcard3 : (guards.erase u).card = 3 := by
      rw [Finset.card_erase_of_mem hu_mem, hg4]
    obtain ⟨x, y, z, _, _, _, hrest⟩ := Finset.card_eq_three.mp hcard3
    have hxm : x ∈ guards.erase u := hrest ▸ Finset.mem_insert_self x {y, z}
    have hym : y ∈ guards.erase u :=
      hrest ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self y {z})
    have hzm : z ∈ guards.erase u := hrest ▸ Finset.mem_insert_of_mem
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self z))
    obtain ⟨hxu, hxg⟩ := Finset.mem_erase.mp hxm
    obtain ⟨hyu, hyg⟩ := Finset.mem_erase.mp hym
    obtain ⟨hzu, hzg⟩ := Finset.mem_erase.mp hzm
    have hguards_eq : guards = {u, x, y, z} := by
      rw [← Finset.insert_erase hu_mem, hrest]
    obtain ⟨ex, hex, hxmod⟩ := hres x hxg hxu
    obtain ⟨ey, hey, hymod⟩ := hres y hyg hyu
    obtain ⟨ez, hez, hzmod⟩ := hres z hzg hzu
    rw [hguards_eq] at hcmax hpos
    exact prop66_role_two hv1 heu' hex hey hez hu hxmod hymod hzmod h56
      (hsafe x hxg) (hsafe y hyg) (hsafe z hzg) ⟨hx0, hx6⟩ hcmax
      (Finset.insert_nonempty _ _) hpos
  · -- an odd runner `d₀` anchors: reset to `0` via `t̃`, Lemmas 6.2/6.3.
    have hum : u ∈ guards.erase d₀ :=
      Finset.mem_erase.mpr ⟨Ne.symm hdu, hu_mem⟩
    have hcard2 : ((guards.erase d₀).erase u).card = 2 := by
      rw [Finset.card_erase_of_mem hum, Finset.card_erase_of_mem hd₀, hg4]
    obtain ⟨y, z, _, hrest⟩ := Finset.card_eq_two.mp hcard2
    have hguards_eq : guards = {d₀, u, y, z} := by
      rw [← Finset.insert_erase hd₀, ← Finset.insert_erase hum, hrest]
    have hym : y ∈ (guards.erase d₀).erase u :=
      hrest ▸ Finset.mem_insert_self y {z}
    have hzm : z ∈ (guards.erase d₀).erase u :=
      hrest ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self z)
    obtain ⟨ey, hey, hymod⟩ :=
      hres y (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hym))
        (Finset.mem_erase.mp hym).1
    obtain ⟨ez, hez, hzmod⟩ :=
      hres z (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hzm))
        (Finset.mem_erase.mp hzm).1
    obtain ⟨ew, hew, hw⟩ := hres d₀ hd₀ hdu
    rw [hguards_eq] at hcmax hpos
    exact prop66_role_one hv1 hew heu' hey hez hw hu hymod hzmod h56
      ⟨hx0, hx6⟩ hcmax (Finset.insert_nonempty _ _) hpos

end
