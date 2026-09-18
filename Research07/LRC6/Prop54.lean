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
# Renault Proposition 5.4 (unique even speed)

Setup: `v₁` is the unique multiple of `6`; the four guards `w x y z` all have
residue `e = ±1 (mod 6)`.  The extremal time `tstar` puts some guard (`w`)
exactly at `5/6`.  Renault resets the anchor to `0` via `t̃ = tstar + e_w/6`,
then applies Lemma 5.2 (`e_w = 1`) or Lemma 5.3 (`e_w = -1`) to the other three
guards, obtaining a `(λ,α)` improving move `s = λ·t̃ + α/6`:

* `λ ≥ 2`: `circ (v₁·s) = circ (λ·x₁) > x₁ = circ (v₁·tstar)` — `improve_ge_two_contra`.
* `λ = 1` (`α ∈ {1,2,4}` resp. `{2,4,5}`): all four guards strictly inside the
  band top — `improve_eq_one_contra` perturbs `s + η`.
-/

noncomputable section

/-- The role-parameterized core of Proposition 5.4: `w` is the `5/6`-anchor,
`x y z` the remaining `±1`-guards, `v₁` the multiple-of-6 runner. -/
theorem prop54_role {v₁ w x y z : ℕ} (hv1 : 6 ∣ v₁)
    {ew ex ey ez : ℤ}
    (hew : ew = 1 ∨ ew = -1) (hex : ex = 1 ∨ ex = -1)
    (hey : ey = 1 ∨ ey = -1) (hez : ez = 1 ∨ ez = -1)
    (hw : (w : ℤ) ≡ ew [ZMOD 6]) (hxe : (x : ℤ) ≡ ex [ZMOD 6])
    (hye : (y : ℤ) ≡ ey [ZMOD 6]) (hze : (z : ℤ) ≡ ez [ZMOD 6])
    {tstar : ℝ}
    (hw56 : Int.fract ((w : ℝ) * tstar) = 5 / 6)
    (hxa : Int.fract ((v₁ : ℝ) * tstar) ∈ Set.Ioo 0 (1 / 6))
    (hmax : ∀ t : ℝ, (∀ d ∈ ({w, x, y, z} : Finset ℕ),
        Int.fract ((d : ℝ) * t) ∈ Set.Icc (1 / 6) (5 / 6)) →
      circ ((v₁ : ℝ) * t) ≤ circ ((v₁ : ℝ) * tstar))
    (hguards : ({w, x, y, z} : Finset ℕ).Nonempty)
    (hpos : ∀ d ∈ ({w, x, y, z} : Finset ℕ), 0 < d) : False := by
  classical
  set ttilde : ℝ := tstar + (ew : ℝ) / 6 with htt
  -- `v₁` is a multiple of 6, so the `e_w/6` shift leaves it fixed.
  have haτ : Int.fract ((v₁ : ℝ) * ttilde) = Int.fract ((v₁ : ℝ) * tstar) := by
    rw [htt]
    exact fract_signed_shift_anchor hv1 tstar ew
  -- `x_w(t̃) = ⟨5/6 + e_w²/6⟩ = 0` since `e_w² = 1`.
  have hw0 : Int.fract ((w : ℝ) * ttilde) = 0 := by
    rw [htt, fract_signed_shift hw, hw56]
    have he2 : (ew : ℝ) * ew = 1 := by
      rcases hew with rfl | rfl <;> · push_cast; norm_num
    rw [he2, show (5 / 6 : ℝ) + 1 / 6 = ((1 : ℤ) : ℝ) by norm_num]
    exact Int.fract_intCast 1
  -- the three other guards are arbitrary positions in `[0,1)`.
  have hxI : Int.fract ((x : ℝ) * ttilde) ∈ Set.Ico 0 1 :=
    ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
  have hyI : Int.fract ((y : ℝ) * ttilde) ∈ Set.Ico 0 1 :=
    ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
  have hzI : Int.fract ((z : ℝ) * ttilde) ∈ Set.Ico 0 1 :=
    ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
  have mem4 : ∀ d : ℕ, d ∈ ({w, x, y, z} : Finset ℕ) →
      d = w ∨ d = x ∨ d = y ∨ d = z := by
    intro d hd
    rwa [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert,
      Finset.mem_singleton] at hd
  rcases hew with rfl | rfl
  · -- `e_w = 1`: Lemma 5.2.
    rcases lemma5_2 hex hey hez hxI hyI hzI with h | h
    · obtain ⟨lam, al, hl2, hl5, ha1, ha5, t3, t4, t5⟩ := h
      refine improve_ge_two_contra (lam := lam) (al := al) hv1 _ hxa haτ hmax ?_ hl2 hl5
      intro d hd
      rcases mem4 d hd with rfl | rfl | rfl | rfl
      · rw [fract_lambda_alpha hw, hw0]
        simp only [mul_zero, zero_add, Int.cast_one, one_mul]
        exact alpha_Icc ha1 ha5
      · rw [fract_lambda_alpha hxe]; exact t3
      · rw [fract_lambda_alpha hye]; exact t4
      · rw [fract_lambda_alpha hze]; exact t5
    · obtain ⟨al, hal, t3, t4, t5⟩ := h
      have ha14 : 1 ≤ al ∧ al ≤ 4 := by
        rcases hal with rfl | rfl | rfl <;> omega
      refine improve_eq_one_contra (al := al) hv1 _ hguards hpos hxa haτ hmax ?_
      intro d hd
      rcases mem4 d hd with rfl | rfl | rfl | rfl
      · have hs := fract_lambda_alpha hw ttilde 1 al
        simp only [Nat.cast_one, one_mul] at hs
        rw [hs, hw0, zero_add, Int.cast_one, one_mul]
        exact alpha_Ico ha14.1 ha14.2
      · have hs := fract_lambda_alpha hxe ttilde 1 al
        simp only [Nat.cast_one, one_mul] at hs
        rw [hs]
        exact Set.Ioo_subset_Ico_self t3
      · have hs := fract_lambda_alpha hye ttilde 1 al
        simp only [Nat.cast_one, one_mul] at hs
        rw [hs]
        exact Set.Ioo_subset_Ico_self t4
      · have hs := fract_lambda_alpha hze ttilde 1 al
        simp only [Nat.cast_one, one_mul] at hs
        rw [hs]
        exact Set.Ioo_subset_Ico_self t5
  · -- `e_w = -1`: Lemma 5.3; the anchor lands on `(6-α)/6`.
    rcases lemma5_3 hex hey hez hxI hyI hzI with h | h
    · obtain ⟨lam, al, hl2, hl5, ha1, ha5, t3, t4, t5⟩ := h
      -- the improving time is `s = λ·t̃ + (6-α)/6`
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
      · have hs := fract_lambda_alpha hxe ttilde lam (6 - al)
        rw [hs, hcast]; exact t3
      · have hs := fract_lambda_alpha hye ttilde lam (6 - al)
        rw [hs, hcast]; exact t4
      · have hs := fract_lambda_alpha hze ttilde lam (6 - al)
        rw [hs, hcast]; exact t5
    · obtain ⟨al, hal, t3, t4, t5⟩ := h
      have ha25 : 2 ≤ al ∧ al ≤ 5 := by
        rcases hal with rfl | rfl | rfl <;> omega
      refine improve_eq_one_contra (al := al) hv1 _ hguards hpos hxa haτ hmax ?_
      intro d hd
      rcases mem4 d hd with rfl | rfl | rfl | rfl
      · have hs := fract_lambda_alpha hw ttilde 1 al
        simp only [Nat.cast_one, one_mul] at hs
        rw [hs, hw0, zero_add, Int.cast_neg, Int.cast_one, neg_one_mul, neg_div]
        exact neg_alpha_Ico ha25.1 ha25.2
      · have hs := fract_lambda_alpha hxe ttilde 1 al
        simp only [Nat.cast_one, one_mul] at hs
        rw [hs]
        exact Set.Ioo_subset_Ico_self t3
      · have hs := fract_lambda_alpha hye ttilde 1 al
        simp only [Nat.cast_one, one_mul] at hs
        rw [hs]
        exact Set.Ioo_subset_Ico_self t4
      · have hs := fract_lambda_alpha hze ttilde 1 al
        simp only [Nat.cast_one, one_mul] at hs
        rw [hs]
        exact Set.Ioo_subset_Ico_self t5

/-- Renault Proposition 5.4: if a single speed is even (the multiple of 6),
`D ≠ ∅` — here stated as a contradiction from the failure hypothesis. -/
theorem prop5_4 {v₁ : ℕ} (hv1 : 6 ∣ v₁) (hv1pos : 0 < v₁)
    {guards : Finset ℕ} (hg4 : guards.card = 4)
    (hpos : ∀ d ∈ guards, 0 < d)
    (hres : ∀ d ∈ guards, (d : ℤ) ≡ 1 [ZMOD 6] ∨ (d : ℤ) ≡ -1 [ZMOD 6])
    (hseed : ∃ τ : ℝ, ∀ d ∈ guards, (1 / 5 : ℝ) ≤ circ (τ * d))
    (hns : ∀ t : ℝ, (∀ d ∈ guards, Int.fract ((d : ℝ) * t) ∈
        Set.Icc (1 / 6) (5 / 6)) → |off v₁ t| < 1 / 6) : False := by
  classical
  have hne : guards.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨tstar, hsafe, hx0, hx6, hfmax, hcmax, d₀, hd₀, h56⟩ :=
    renault6_maximize guards hne hpos hv1pos hns hseed
  have e_of : ∀ d ∈ guards, ∃ e : ℤ, (e = 1 ∨ e = -1) ∧ (d : ℤ) ≡ e [ZMOD 6] := by
    intro d hd
    rcases hres d hd with h | h
    · exact ⟨1, Or.inl rfl, h⟩
    · exact ⟨-1, Or.inr rfl, h⟩
  have hcard3 : (guards.erase d₀).card = 3 := by
    rw [Finset.card_erase_of_mem hd₀, hg4]
  obtain ⟨x, y, z, _, _, _, hrest⟩ := Finset.card_eq_three.mp hcard3
  have hguards_eq : guards = {d₀, x, y, z} := by
    rw [← Finset.insert_erase hd₀, hrest]
  obtain ⟨ew, hew, hw⟩ := e_of d₀ hd₀
  obtain ⟨ex, hex, hx⟩ := e_of x (by rw [hguards_eq]; simp)
  obtain ⟨ey, hey, hy⟩ := e_of y (by rw [hguards_eq]; simp)
  obtain ⟨ez, hez, hz⟩ := e_of z (by rw [hguards_eq]; simp)
  rw [hguards_eq] at hcmax hpos
  exact prop54_role hv1 hew hex hey hez hw hx hy hz h56 ⟨hx0, hx6⟩ hcmax
    (Finset.insert_nonempty _ _) hpos

end
