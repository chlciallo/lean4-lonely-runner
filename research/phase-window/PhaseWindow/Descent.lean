import PhaseWindow.TwoSpeed

namespace PhaseWindow

noncomputable def radiusConstant (α β : ℝ) : ℝ :=
  max (α + β) (α * (1 + 2 * β) / (1 - 2 * β))

/-- The local theorem for actual speeds, with arbitrary initial phases. -/
theorem two_speed_escape {α β a b x y K t : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hsum : α + β ≤ 1 / 2)
    (ha : 0 < a) (hab : a ≤ b)
    (hK₁ : α + β ≤ K) (hK₂ : α * (1 + 2 * β) ≤ (1 - 2 * β) * K) :
    ∃ s, |s - t| ≤ K / a ∧ Safe α (a * s + x) ∧ Safe β (b * s + y) := by
  have hratio : 1 ≤ b / a := (le_div_iff₀ ha).mpr (by simpa using hab)
  obtain ⟨u, hu, husa, husb⟩ := two_speed_escape_normalized
    (x := x) (y := y) (t := a * t) hα hβ hsum hratio hK₁ hK₂
  refine ⟨u / a, ?_, ?_, ?_⟩
  · have he : u / a - t = (u - a * t) / a := by field_simp
    rw [he, abs_div, abs_of_pos ha]
    exact (div_le_div_iff_of_pos_right ha).mpr hu
  · simpa [mul_div_cancel₀ _ ha.ne'] using husa
  · convert husb using 1; ring

theorem two_speed_escape_explicit {α β a b x y t : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hsum : α + β ≤ 1 / 2)
    (ha : 0 < a) (hab : a ≤ b) :
    ∃ s, |s - t| ≤ radiusConstant α β / a ∧
      Safe α (a * s + x) ∧ Safe β (b * s + y) := by
  apply two_speed_escape hα hβ hsum ha hab
  · exact le_max_left _ _
  · have hp : 0 < 1 - 2 * β := by linarith
    have hm := le_max_right (α + β) (α * (1 + 2 * β) / (1 - 2 * β))
    exact (div_le_iff₀ hp).mp hm |>.trans_eq (mul_comm _ _)

/-- Equal-threshold BHK-type radius, in its parameterized range. -/
theorem two_speed_escape_small {d a b x y t : ℝ}
    (hd : 0 < d) (hd6 : d ≤ 1 / 6) (ha : 0 < a) (hab : a ≤ b) :
    ∃ s, |s - t| ≤ 2 * d / a ∧ Safe d (a * s + x) ∧ Safe d (b * s + y) := by
  apply two_speed_escape hd hd (by linarith) ha hab (by linarith)
  nlinarith

/-- A genuinely lower-dimensional witness lifts, provided its margin pays for the motion. -/
theorem transfer_core {ι : Type*} (v phase : ι → ℝ)
    {d a b x y t R M : ℝ} (_hR : 0 ≤ R)
    (hcore : ∀ i, Safe (d + M * R) (v i * t + phase i))
    (hspeed : ∀ i, |v i| ≤ M)
    (hpair : ∃ s, |s - t| ≤ R ∧ Safe d (a * s + x) ∧ Safe d (b * s + y)) :
    ∃ s, |s - t| ≤ R ∧ (∀ i, Safe d (v i * s + phase i)) ∧
      Safe d (a * s + x) ∧ Safe d (b * s + y) := by
  obtain ⟨s, hst, hsa, hsb⟩ := hpair
  refine ⟨s, hst, ?_, hsa, hsb⟩
  intro i
  apply safe_stable (hcore i)
  have he : v i * s + phase i - (v i * t + phase i) = v i * (s - t) := by ring
  rw [he, abs_mul]
  exact mul_le_mul (hspeed i) hst (abs_nonneg _) (le_trans (abs_nonneg _) (hspeed i))

/-- Delete two speeds: core size is `k-2`, and no same-size conjecture is assumed. -/
theorem delete_two {k : ℕ} (hk : 5 ≤ k) (v phase : Fin (k - 2) → ℝ)
    {a b x y M : ℝ} (ha : 0 < a) (hab : a ≤ b) (_hM : 0 ≤ M)
    (hspeed : ∀ i, |v i| ≤ M)
    (hfast : ((k : ℝ) - 1) * M ≤ a)
    (hcore : ∃ t, ∀ i, Safe (1 / ((k : ℝ) - 1)) (v i * t + phase i)) :
    ∃ s, (∀ i, Safe (1 / ((k : ℝ) + 1)) (v i * s + phase i)) ∧
      Safe (1 / ((k : ℝ) + 1)) (a * s + x) ∧
      Safe (1 / ((k : ℝ) + 1)) (b * s + y) := by
  have hk' : (5 : ℝ) ≤ k := by exact_mod_cast hk
  have hk1 : 0 < (k : ℝ) - 1 := by linarith
  have hkp : 0 < (k : ℝ) + 1 := by linarith
  let d : ℝ := 1 / ((k : ℝ) + 1)
  have hd : 0 < d := by dsimp [d]; positivity
  have hd6 : d ≤ 1 / 6 := by dsimp [d]; apply (div_le_div_iff₀ hkp (by norm_num)).mpr; linarith
  have hbound : d + M * (2 * d / a) ≤ 1 / ((k : ℝ) - 1) := by
    dsimp [d]
    apply (le_div_iff₀ hk1).mpr
    field_simp
    nlinarith
  obtain ⟨t, ht⟩ := hcore
  have hcore' : ∀ i, Safe (d + M * (2 * d / a)) (v i * t + phase i) := by
    intro i n
    exact le_trans hbound (ht i n)
  obtain ⟨s, _, hsc, hsa, hsb⟩ := transfer_core v phase
    (by positivity : 0 ≤ 2 * d / a) hcore' hspeed
    (two_speed_escape_small (x := x) (y := y) (t := t) hd hd6 ha hab)
  exact ⟨s,hsc,hsa,hsb⟩

end PhaseWindow
