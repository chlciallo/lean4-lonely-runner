import PhaseWindow.Descent

namespace PhaseWindow

/-- One radius must work for all ordered speed ratios and all phases. -/
def UniformRadius (α β K : ℝ) : Prop :=
  ∀ (ρ : ℝ), 1 ≤ ρ → ∀ (x y t : ℝ),
    ∃ s, |s - t| ≤ K ∧ Safe α (s + x) ∧ Safe β (ρ * s + y)

theorem uniform_radius_sum_lower {α β K : ℝ}
    (_hα : 0 < α) (_hβ : 0 < β) (h : UniformRadius α β K) : α + β ≤ K := by
  by_contra hn
  have hlt : K < α + β := lt_of_not_ge hn
  let R := (K + α + β) / 2
  obtain ⟨s, hs, hsa, hsb⟩ := h 1 le_rfl (R - α) (β - R) 0
  have hsl : -K ≤ s := by simpa using (abs_le.mp hs).1
  have hsr : s ≤ K := by simpa using (abs_le.mp hs).2
  have hRa : K < R := by dsimp [R]; linarith
  have hRb : R < α + β := by dsimp [R]; linarith
  by_cases he : s < 2 * α - R
  · have hb : |s + (R - α) - (0 : ℤ)| < α := by
      apply abs_lt.mpr; constructor <;> norm_num <;> linarith
    exact (not_lt_of_ge (hsa 0)) hb
  · have hb : |1 * s + (β - R) - (0 : ℤ)| < β := by
      apply abs_lt.mpr; constructor <;> norm_num <;> linarith
    exact (not_lt_of_ge (hsb 0)) hb

/-- A slow interval bridging two fast intervals obstructs an entire radius-K window. -/
theorem bridge_obstruction {α β ρ K : ℝ} (hρ : 0 < ρ)
    (hbridge : 1 / 2 - β < ρ * α) (hend : ρ * K < 1 / 2 + β) :
    ¬ ∃ s, |s| ≤ K ∧ Safe α s ∧ Safe β (ρ * s + 1 / 2) := by
  rintro ⟨s, hs, hsa, hsb⟩
  have hsl := (abs_le.mp hs).1
  have hsr := (abs_le.mp hs).2
  have hsa0 := hsa 0
  simp only [Int.cast_zero, sub_zero, le_abs] at hsa0
  rcases hsa0 with hp | hn
  · have hb : |ρ * s + 1 / 2 - (1 : ℤ)| < β := by
      apply abs_lt.mpr; constructor <;> norm_num <;> nlinarith
    exact (not_lt_of_ge (hsb 1)) hb
  · have hb : |ρ * s + 1 / 2 - (0 : ℤ)| < β := by
      apply abs_lt.mpr; constructor <;> norm_num <;> nlinarith
    exact (not_lt_of_ge (hsb 0)) hb

theorem uniform_radius_bridge_lower {α β K : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hsum : α + β ≤ 1 / 2)
    (h : UniformRadius α β K) : α * (1 + 2 * β) ≤ (1 - 2 * β) * K := by
  have hsumK := uniform_radius_sum_lower hα hβ h
  have hK : 0 < K := by linarith
  by_contra hn
  have hbad : (1 - 2 * β) * K < α * (1 + 2 * β) := lt_of_not_ge hn
  have hgap : (1 - 2 * β) / (2 * α) < (1 / 2 + β) / K := by
    apply (div_lt_div_iff₀ (by positivity : 0 < 2 * α) hK).mpr
    nlinarith
  obtain ⟨ρ, hlo, hhi⟩ := exists_between hgap
  have hrbase : 1 ≤ (1 - 2 * β) / (2 * α) := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * α)).mpr
    linarith
  have hr : 1 ≤ ρ := le_trans hrbase hlo.le
  have hb : 1 / 2 - β < ρ * α := by
    have hh := (div_lt_iff₀ (by positivity : 0 < 2 * α)).mp hlo
    nlinarith
  have he : ρ * K < 1 / 2 + β := (lt_div_iff₀ hK).mp hhi
  have hf := bridge_obstruction (by linarith : 0 < ρ) hb he
  obtain ⟨s, hs, hsa, hsb⟩ := h ρ hr 0 (1 / 2) 0
  apply hf
  exact ⟨s, by simpa using hs, by simpa using hsa, hsb⟩

/-- Exact optimum, with all phase and speed-ratio quantifiers retained. -/
theorem uniform_radius_iff {α β K : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hsum : α + β ≤ 1 / 2) :
    UniformRadius α β K ↔
      α + β ≤ K ∧ α * (1 + 2 * β) ≤ (1 - 2 * β) * K := by
  constructor
  · intro h
    exact ⟨uniform_radius_sum_lower hα hβ h, uniform_radius_bridge_lower hα hβ hsum h⟩
  · rintro ⟨h₁,h₂⟩ ρ hρ x y t
    exact two_speed_escape_normalized hα hβ hsum hρ h₁ h₂

theorem uniform_radius_iff_explicit {α β K : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hsum : α + β ≤ 1 / 2) :
    UniformRadius α β K ↔ radiusConstant α β ≤ K := by
  rw [uniform_radius_iff hα hβ hsum, radiusConstant, max_le_iff]
  have hp : 0 < 1 - 2 * β := by linarith
  rw [div_le_iff₀ hp, mul_comm K]

end PhaseWindow
