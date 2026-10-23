import PhaseWindow.Descent

namespace PhaseWindow

/-- A runner in a forbidden arc reaches its boundary within half the interval length. -/
theorem nearest_boundary {d v x t : ℝ} (hd : 0 < d) (hdh : d ≤ 1 / 2)
    (hv : 0 < v) (hbad : ¬ Safe d (v * t + x)) :
    ∃ s, |s - t| ≤ d / v ∧ Safe d (v * s + x) ∧
      ∃ j : ℤ, |v * s + x - j| ≤ d := by
  obtain ⟨j,hj⟩ := not_safe_iff.mp hbad
  have hjl := (abs_lt.mp hj).1
  have hjr := (abs_lt.mp hj).2
  let l := ((j : ℝ) - d - x) / v
  let r := ((j : ℝ) + d - x) / v
  have hl : v * l + x = (j : ℝ) - d := by dsimp [l]; field_simp; ring
  have hr : v * r + x = (j : ℝ) + d := by dsimp [r]; field_simp; ring
  let P := fun s : ℝ => Safe d (v * s + x) ∧ ∃ j : ℤ, |v * s + x - j| ≤ d
  have hw : r - l ≤ 2 * (d / v) := by
    have he : r - l = 2 * (d / v) := by dsimp [r,l]; ring
    exact he.le
  apply endpoint_choice (by nlinarith : l ≤ t) (by nlinarith : t ≤ r) hw P
  · constructor
    · apply safe_of_cell (n := j - 1) <;> push_cast <;> linarith
    · refine ⟨j, ?_⟩
      rw [hl]
      have he : (j : ℝ) - d - j = -d := by ring
      rw [he, abs_neg, abs_of_pos hd]
  · constructor
    · apply safe_of_cell (n := j) <;> linarith
    · refine ⟨j, ?_⟩
      rw [hr]
      have he : (j : ℝ) + d - j = d := by ring
      rw [he, abs_of_pos hd]

theorem safe_neg {d x : ℝ} (h : Safe d x) : Safe d (-x) := by
  intro n
  have hh := h (-n)
  have he : -x - (n : ℝ) = -(x - ((-n : ℤ) : ℝ)) := by push_cast; ring
  rw [he, abs_neg]
  exact hh

/-- A separated relative phase and one boundary point force the other runner to be safe. -/
theorem safe_from_relative {d X Y : ℝ} (hrel : Safe (2 * d) (Y - X))
    (hbound : ∃ j : ℤ, |X - j| ≤ d) : Safe d Y := by
  obtain ⟨j,hj⟩ := hbound
  intro m
  have hsep := hrel (m - j)
  have htri : |Y - X - (m - j : ℤ)| ≤ |Y - m| + |X - j| := by
    push_cast
    have he : Y - X - ((m : ℝ) - j) = (Y - m) - (X - j) := by ring
    rw [he]
    exact abs_sub _ _
  linarith

/-- Keeping a relative phase separated halves the phase-uniform escape radius. -/
theorem relation_escape {d a b x y t : ℝ}
    (hd : 0 < d) (hdh : d ≤ 1 / 2) (ha : 0 < a) (hab : a ≤ b)
    (hrel : Safe (2 * d + |b - a| * (d / a)) ((b - a) * t + (y - x))) :
    ∃ s, |s - t| ≤ d / a ∧ Safe d (a * s + x) ∧ Safe d (b * s + y) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hmotion : ∀ s, |s - t| ≤ d / a → Safe (2 * d) ((b * s + y) - (a * s + x)) := by
    intro s hs
    apply safe_stable hrel
    have he : (b * s + y - (a * s + x)) - ((b - a) * t + (y - x)) =
        (b - a) * (s - t) := by ring
    rw [he, abs_mul]
    exact mul_le_mul_of_nonneg_left hs (abs_nonneg _)
  by_cases hsa : Safe d (a * t + x)
  · by_cases hsb : Safe d (b * t + y)
    · exact ⟨t, by simp; positivity, hsa, hsb⟩
    obtain ⟨s,hs,hbs,hbd⟩ := nearest_boundary hd hdh hb hsb
    have hle : d / b ≤ d / a := (div_le_div_iff₀ hb ha).mpr (by nlinarith)
    have hs' := le_trans hs hle
    have hrel' : Safe (2 * d) ((a * s + x) - (b * s + y)) := by
      convert safe_neg (hmotion s hs') using 1; ring
    exact ⟨s,hs',safe_from_relative hrel' hbd,hbs⟩
  · obtain ⟨s,hs,has,had⟩ := nearest_boundary hd hdh ha hsa
    exact ⟨s,hs,has,safe_from_relative (hmotion s hs) had⟩

/-- The relative phase is a retained short relation, not an independent free variable. -/
theorem relation_delete {ι : Type*} (v phase : ι → ℝ)
    {d a b x y t M : ℝ} (hd : 0 < d) (hdh : d ≤ 1 / 2)
    (ha : 0 < a) (hab : a ≤ b) (hspeed : ∀ i, |v i| ≤ M)
    (hcore : ∀ i, Safe (d + M * (d / a)) (v i * t + phase i))
    (j : ι) (hvelocity : v j = b - a) (hphase : phase j = y - x)
    (hguard : Safe (2 * d + |v j| * (d / a)) (v j * t + phase j)) :
    ∃ s, |s - t| ≤ d / a ∧ (∀ i, Safe d (v i * s + phase i)) ∧
      Safe d (a * s + x) ∧ Safe d (b * s + y) := by
  have hrel : Safe (2 * d + |b - a| * (d / a)) ((b - a) * t + (y - x)) := by
    simpa [hvelocity,hphase] using hguard
  exact transfer_core v phase (by positivity : 0 ≤ d / a) hcore hspeed
    (relation_escape hd hdh ha hab hrel)

/-- A short-relation descent with an explicit `k-2` core and half the uniform speed bound. -/
theorem relation_delete_two {k : ℕ} (hk : 4 ≤ k) (v phase : Fin (k - 2) → ℝ)
    {a b x y M : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hspeed : ∀ i, |v i| ≤ M) (hfast : ((k : ℝ) - 1) * M ≤ 2 * a)
    (j : Fin (k - 2)) (hvj : v j = b - a) (hpj : phase j = y - x)
    (hcore : ∃ t,
      (∀ i, Safe (1 / ((k : ℝ) - 1)) (v i * t + phase i)) ∧
      Safe (2 / ((k : ℝ) + 1) + |v j| * ((1 / ((k : ℝ) + 1)) / a))
        (v j * t + phase j)) :
    ∃ s, (∀ i, Safe (1 / ((k : ℝ) + 1)) (v i * s + phase i)) ∧
      Safe (1 / ((k : ℝ) + 1)) (a * s + x) ∧
      Safe (1 / ((k : ℝ) + 1)) (b * s + y) := by
  have hk' : (4 : ℝ) ≤ k := by exact_mod_cast hk
  have hk1 : 0 < (k : ℝ) - 1 := by linarith
  have hkp : 0 < (k : ℝ) + 1 := by linarith
  let d : ℝ := 1 / ((k : ℝ) + 1)
  have hd : 0 < d := by dsimp [d]; positivity
  have hdh : d ≤ 1 / 2 := by
    dsimp [d]; apply (div_le_div_iff₀ hkp (by norm_num)).mpr; linarith
  have hbound : d + M * (d / a) ≤ 1 / ((k : ℝ) - 1) := by
    dsimp [d]
    apply (le_div_iff₀ hk1).mpr
    field_simp
    nlinarith
  obtain ⟨t,ht,hguard⟩ := hcore
  have hc : ∀ i, Safe (d + M * (d / a)) (v i * t + phase i) := by
    intro i n; exact le_trans hbound (ht i n)
  have hg : Safe (2 * d + |v j| * (d / a)) (v j * t + phase j) := by
    convert hguard using 1; dsimp [d]; ring
  obtain ⟨s,_,hsc,hsa,hsb⟩ := relation_delete v phase hd hdh ha hab hspeed hc j hvj hpj hg
  exact ⟨s,hsc,hsa,hsb⟩

end PhaseWindow
