import PhaseWindow.Basic

namespace PhaseWindow

/-- Enclose one slow forbidden interval by points safe for both runners. -/
theorem enclose_slow_block {α β ρ x y K : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hsum : α + β ≤ 1 / 2) (hρ : 1 ≤ ρ)
    (hK₁ : α + β ≤ K) (hK₂ : α * (1 + 2 * β) ≤ (1 - 2 * β) * K)
    (n : ℤ) :
    ∃ l r, l ≤ (n : ℝ) - α - x ∧ (n : ℝ) + α - x ≤ r ∧
      r - l ≤ 2 * K ∧
      (Safe α (l + x) ∧ Safe β (ρ * l + y)) ∧
      (Safe α (r + x) ∧ Safe β (ρ * r + y)) := by
  have hρp : 0 < ρ := by linarith
  have hβh : β ≤ 1 / 2 := by linarith
  obtain ⟨l, hl, hld, hls, hlc⟩ := exit_left hβ.le hβh hρp (x := y)
    (t := (n : ℝ) - α - x)
  obtain ⟨r, hr, hrd, hrs, hrc⟩ := exit_right hβ.le hβh hρp (x := y)
    (t := (n : ℝ) + α - x)
  have hlslow : Safe α (l + x) := by
    apply safe_of_cell (n := n - 1)
    · push_cast
      have : (n : ℝ) - α - x - l ≤ 2 * β := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hρ) (sub_nonneg.mpr hl)]
      linarith
    · push_cast; linarith
  have hrslow : Safe α (r + x) := by
    apply safe_of_cell (n := n)
    · linarith
    · have : r - ((n : ℝ) + α - x) ≤ 2 * β := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hρ) (sub_nonneg.mpr hr)]
      linarith
  refine ⟨l, r, hl, hr, ?_, ⟨hlslow,hls⟩, ⟨hrslow,hrs⟩⟩
  rcases hlc with hle | ⟨j, hje, hj⟩
  · subst l
    have : r - ((n : ℝ) + α - x) ≤ 2 * β := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hρ) (sub_nonneg.mpr hr)]
    linarith
  rcases hrc with hre | ⟨k, hke, hk⟩
  · subst r
    have : (n : ℝ) - α - x - l ≤ 2 * β := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hρ) (sub_nonneg.mpr hl)]
    linarith
  by_cases hkj : k ≤ j
  · have hkj' : (k : ℝ) ≤ j := by exact_mod_cast hkj
    have hw : 0 ≤ r - l := by linarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hρ) hw]
  · have hdiff : (1 : ℝ) ≤ (k : ℝ) - j := by
      exact_mod_cast (by omega : 1 ≤ k - j)
    have hjr := (abs_lt.mp hj).2
    have hkl := (abs_lt.mp hk).1
    have hsep : (k : ℝ) - j - 2 * β < 2 * α * ρ := by nlinarith
    have hratio : (1 - 2 * β) * ((k : ℝ) - j + 2 * β) ≤
        (1 + 2 * β) * ((k : ℝ) - j - 2 * β) := by
      nlinarith [mul_nonneg hβ.le (by linarith : 0 ≤ (k : ℝ) - j - 1)]
    have hprod : (1 - 2 * β) * (ρ * (r - l)) <
        (1 + 2 * β) * (2 * α * ρ) := by
      have hh := mul_lt_mul_of_pos_left hsep (by linarith : 0 < 1 + 2 * β)
      have he : ρ * (r - l) = (k : ℝ) - j + 2 * β := by nlinarith
      rw [he]
      exact lt_of_le_of_lt hratio hh
    have hwidth : (1 - 2 * β) * (r - l) < 2 * α * (1 + 2 * β) := by
      nlinarith
    have hpos : 0 < 1 - 2 * β := by linarith
    nlinarith

/-- A local, arbitrary-phase escape theorem. `K` is a division-free radius certificate. -/
theorem two_speed_escape_normalized {α β ρ x y K t : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hsum : α + β ≤ 1 / 2) (hρ : 1 ≤ ρ)
    (hK₁ : α + β ≤ K) (hK₂ : α * (1 + 2 * β) ≤ (1 - 2 * β) * K) :
    ∃ s, |s - t| ≤ K ∧ Safe α (s + x) ∧ Safe β (ρ * s + y) := by
  have hρp : 0 < ρ := by linarith
  have hβh : β ≤ 1 / 2 := by linarith
  let P := fun s : ℝ => Safe α (s + x) ∧ Safe β (ρ * s + y)
  by_cases hat : Safe α (t + x)
  · by_cases hbt : Safe β (ρ * t + y)
    · exact ⟨t, by simp; linarith, hat, hbt⟩
    obtain ⟨j, hj⟩ := not_safe_iff.mp hbt
    have hjl := (abs_lt.mp hj).1
    have hjr := (abs_lt.mp hj).2
    let u := ((j : ℝ) - β - y) / ρ
    let v := ((j : ℝ) + β - y) / ρ
    have hue : ρ * u + y = (j : ℝ) - β := by dsimp [u]; field_simp; ring
    have hve : ρ * v + y = (j : ℝ) + β := by dsimp [v]; field_simp; ring
    have hut : u < t := by nlinarith
    have htv : t < v := by nlinarith
    have hub : Safe β (ρ * u + y) := by
      apply safe_of_cell (n := j - 1) <;> push_cast <;> linarith
    have hvb : Safe β (ρ * v + y) := by
      apply safe_of_cell (n := j) <;> linarith
    by_cases hua : Safe α (u + x)
    · by_cases hva : Safe α (v + x)
      · apply endpoint_choice hut.le htv.le ?_ P ⟨hua,hub⟩ ⟨hva,hvb⟩
        have hw : 0 ≤ v - u := by linarith
        nlinarith [mul_nonneg (sub_nonneg.mpr hρ) hw]
      obtain ⟨n, hn⟩ := not_safe_iff.mp hva
      obtain ⟨l,r,hl,hr,hw,hls,hrs⟩ := enclose_slow_block (x := x) (y := y) hα hβ hsum hρ hK₁ hK₂ n
      have hnl := (abs_lt.mp hn).1
      have hnr := (abs_lt.mp hn).2
      have hrv : v < r := by linarith
      have hlv : l < v := by linarith
      have hlt : l ≤ t := by
        have hs := hls.2 j
        rw [le_abs] at hs
        rcases hs with hs | hs <;> nlinarith
      exact endpoint_choice hlt (by linarith) hw P hls hrs
    · obtain ⟨n, hn⟩ := not_safe_iff.mp hua
      obtain ⟨l,r,hl,hr,hw,hls,hrs⟩ := enclose_slow_block (x := x) (y := y) hα hβ hsum hρ hK₁ hK₂ n
      have hnl := (abs_lt.mp hn).1
      have hnr := (abs_lt.mp hn).2
      have hlu : l < u := by linarith
      have hru : u < r := by linarith
      have htr : t ≤ r := by
        have hs := hrs.2 j
        rw [le_abs] at hs
        rcases hs with hs | hs <;> nlinarith
      exact endpoint_choice (by linarith) htr hw P hls hrs
  · obtain ⟨n, hn⟩ := not_safe_iff.mp hat
    obtain ⟨l,r,hl,hr,hw,hls,hrs⟩ := enclose_slow_block (x := x) (y := y) hα hβ hsum hρ hK₁ hK₂ n
    have hnl := (abs_lt.mp hn).1
    have hnr := (abs_lt.mp hn).2
    exact endpoint_choice (by linarith) (by linarith) hw P hls hrs

end PhaseWindow
