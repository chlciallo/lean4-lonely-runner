import PhaseWindow.Triple

namespace PhaseWindow

def UniformTripleRadius (δ K : ℝ) : Prop :=
  ∀ (ρ : ℝ), 1 ≤ ρ → ∀ (x y t : ℝ),
    ∃ s, |s - t| ≤ K ∧ Safe δ (s + x) ∧ Safe δ (ρ * s + y) ∧
      Safe δ ((ρ + 1) * s + (x + y))

/-- Three adjacent forbidden intervals force the `5δ/2` term. -/
theorem triple_radius_linear_lower {δ K : ℝ} (h : UniformTripleRadius δ K) :
    5 * δ ≤ 2 * K := by
  by_contra hn
  have hlt : 2 * K < 5 * δ := lt_of_not_ge hn
  let D := K + δ / 2
  obtain ⟨s,hs,hsa,hsb,hsc⟩ := h 1 le_rfl 0 (-D) (D / 2)
  have hsl := (abs_le.mp hs).1
  have hsr := (abs_le.mp hs).2
  have hD : D < 3 * δ := by dsimp [D]; linarith
  have hlo : -δ < s := by dsimp [D] at *; linarith
  have hhi : s < D + δ := by dsimp [D] at *; linarith
  by_cases hl : s < δ
  · have hb : |s + 0 - (0 : ℤ)| < δ := by
      apply abs_lt.mpr; constructor <;> norm_num <;> linarith
    exact (not_lt_of_ge (hsa 0)) hb
  by_cases hr : D - δ < s
  · have hb : |1 * s + -D - (0 : ℤ)| < δ := by
      apply abs_lt.mpr; constructor <;> norm_num <;> linarith
    exact (not_lt_of_ge (hsb 0)) hb
  · have hb : |(1 + 1) * s + (0 + -D) - (0 : ℤ)| < δ := by
      apply abs_lt.mpr; constructor <;> norm_num <;> linarith
    exact (not_lt_of_ge (hsc 0)) hb

/-- The five-interval chain `B,C,A,C,B` gives the second obstruction. -/
theorem triple_bridge_obstruction {δ ρ K : ℝ} (hδ : 0 < δ) (hδ6 : δ ≤ 1 / 6)
    (hρ : 0 < ρ) (hbridge : 1 - 4 * δ < 2 * ρ * δ)
    (hend : ρ * K < 1 / 2 + δ) :
    ¬ ∃ s, |s| ≤ K ∧ Safe δ s ∧ Safe δ (ρ * s + 1 / 2) ∧
      Safe δ ((ρ + 1) * s + 1 / 2) := by
  have hpositive : ∀ u : ℝ, δ ≤ u → u ≤ K →
      Safe δ (ρ * u + 1 / 2) → Safe δ ((ρ + 1) * u + 1 / 2) → False := by
    intro u hu huK hub huc
    have hb := hub 1
    have hc := huc 1
    norm_num only [Int.cast_one] at hb hc
    rw [le_abs] at hb hc
    have hBu : ρ * u ≤ 1 / 2 - δ := by rcases hb with hb | hb <;> nlinarith
    have hCu : 1 / 2 + δ ≤ (ρ + 1) * u := by
      rcases hc with hc | hc
      · linarith
      · nlinarith [mul_nonneg (by linarith : 0 ≤ ρ + 1) (by linarith : 0 ≤ u - δ)]
    have h2 : 2 * δ ≤ u := by linarith
    nlinarith
  rintro ⟨s,hs,hsa,hsb,hsc⟩
  have hsa0 := hsa 0
  simp only [Int.cast_zero, sub_zero, le_abs] at hsa0
  rcases hsa0 with hp | hn
  · exact hpositive s hp (abs_le.mp hs).2 hsb hsc
  · have hb : Safe δ (ρ * (-s) + 1 / 2) := by
      convert safe_add_int (safe_neg hsb) 1 using 1
      norm_num; ring
    have hc : Safe δ ((ρ + 1) * (-s) + 1 / 2) := by
      convert safe_add_int (safe_neg hsc) 1 using 1
      norm_num; ring
    exact hpositive (-s) hn (by have := (abs_le.mp hs).1; linarith) hb hc

theorem triple_radius_bridge_lower {δ K : ℝ} (hδ : 0 < δ) (hδ6 : δ ≤ 1 / 6)
    (h : UniformTripleRadius δ K) : δ * (1 + 2 * δ) ≤ (1 - 4 * δ) * K := by
  have hlin := triple_radius_linear_lower h
  have hK : 0 < K := by linarith
  by_contra hn
  have hbad : (1 - 4 * δ) * K < δ * (1 + 2 * δ) := lt_of_not_ge hn
  have hgap : (1 - 4 * δ) / (2 * δ) < (1 / 2 + δ) / K := by
    apply (div_lt_div_iff₀ (by positivity : 0 < 2 * δ) hK).mpr
    nlinarith
  obtain ⟨ρ,hlo,hhi⟩ := exists_between hgap
  have hbase : 1 ≤ (1 - 4 * δ) / (2 * δ) := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * δ)).mpr
    linarith
  have hρ : 1 ≤ ρ := le_trans hbase hlo.le
  have hb : 1 - 4 * δ < 2 * ρ * δ := by
    have := (div_lt_iff₀ (by positivity : 0 < 2 * δ)).mp hlo
    nlinarith
  have he : ρ * K < 1 / 2 + δ := (lt_div_iff₀ hK).mp hhi
  obtain ⟨s,hs,hsa,hsb,hsc⟩ := h ρ hρ 0 (1 / 2) 0
  apply triple_bridge_obstruction hδ hδ6 (by linarith : 0 < ρ) hb he
  exact ⟨s, by simpa using hs, by simpa using hsa, hsb, by simpa using hsc⟩

/-- Exact optimum with all compatible phases and all ordered real speed ratios. -/
theorem uniform_triple_radius_iff {δ K : ℝ} (hδ : 0 < δ) (hδ6 : δ ≤ 1 / 6) :
    UniformTripleRadius δ K ↔ tripleRadius δ ≤ K := by
  rw [tripleRadius, max_le_iff, div_le_iff₀ (by norm_num : (0 : ℝ) < 2),
    div_le_iff₀ (by linarith : 0 < 1 - 4 * δ)]
  constructor
  · intro h
    exact ⟨by linarith [triple_radius_linear_lower h],
      by nlinarith [triple_radius_bridge_lower hδ hδ6 h]⟩
  · rintro ⟨h₁,h₂⟩ ρ hρ x y t
    exact triple_escape_normalized hδ hδ6 hρ (by linarith) (by nlinarith)

/-- Dropping phase compatibility invalidates the small-threshold constant. -/
theorem incompatible_triple_counterexample :
    ¬ ∃ s : ℝ, |s - 46 / 51| ≤ 5 / 18 ∧ Safe (1 / 9) s ∧
      Safe (1 / 9) ((9 / 8) * s + 1 / 12) ∧
      Safe (1 / 9) ((17 / 8) * s + 7 / 12) := by
  rintro ⟨s,hs,hsa,hsb,hsc⟩
  have hlo := (abs_le.mp hs).1
  have hhi := (abs_le.mp hs).2
  by_cases hleft : s < 110 / 153
  · have hb : |(17 / 8) * s + 7 / 12 - (2 : ℤ)| < (1 / 9 : ℝ) := by
      apply abs_lt.mpr; constructor <;> norm_num <;> linarith
    exact (not_lt_of_ge (hsc 2)) hb
  by_cases hmid : s < 74 / 81
  · have hb : |(9 / 8) * s + 1 / 12 - (1 : ℤ)| < (1 / 9 : ℝ) := by
      apply abs_lt.mpr; constructor <;> norm_num <;> linarith
    exact (not_lt_of_ge (hsb 1)) hb
  by_cases hright : s < 10 / 9
  · have hb : |s - (1 : ℤ)| < (1 / 9 : ℝ) := by
      apply abs_lt.mpr; constructor <;> norm_num <;> linarith
    exact (not_lt_of_ge (hsa 1)) hb
  · have hb : |(17 / 8) * s + 7 / 12 - (3 : ℤ)| < (1 / 9 : ℝ) := by
      apply abs_lt.mpr; constructor <;> norm_num <;> linarith
    exact (not_lt_of_ge (hsc 3)) hb

end PhaseWindow
