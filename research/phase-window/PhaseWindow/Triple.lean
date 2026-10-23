import PhaseWindow.Relation
import Mathlib.Algebra.Order.Archimedean.Real.Basic

namespace PhaseWindow

theorem safe_add_int {δ x : ℝ} (h : Safe δ x) (n : ℤ) : Safe δ (x + n) := by
  intro m
  convert h (m - n) using 1
  push_cast
  congr 1
  ring

/-- The compatible phases let one fast boundary clear both fast runners. -/
theorem triple_right {δ ρ Y : ℝ} (hδ : 0 < δ) (hδ6 : δ ≤ 1 / 6)
    (hρ : 1 ≤ ρ) :
    ∃ r, δ ≤ r ∧ r ≤ 4 * δ ∧ Safe δ r ∧ Safe δ (ρ * r + Y) ∧
      Safe δ ((ρ + 1) * r + Y) ∧
      (r = δ ∨ ∃ j : ℤ, ρ * r + Y = j + δ ∧ (j : ℝ) < Y + (ρ + 2) * δ) := by
  have hρp : 0 < ρ := by linarith
  let j : ℤ := ⌈Y + (ρ + 2) * δ⌉ - 1
  have hjl : (j : ℝ) < Y + (ρ + 2) * δ := by
    have := Int.ceil_lt_add_one (Y + (ρ + 2) * δ)
    dsimp [j]; push_cast; linarith
  have hjr : Y + (ρ + 2) * δ ≤ (j : ℝ) + 1 := by
    have := Int.le_ceil (Y + (ρ + 2) * δ)
    dsimp [j]; push_cast; linarith
  by_cases h : (j : ℝ) + δ ≤ ρ * δ + Y
  · refine ⟨δ, le_rfl, by linarith, ?_, ?_, ?_, Or.inl rfl⟩
    · exact safe_of_cell (n := 0) (by norm_num) (by norm_num; linarith)
    · exact safe_of_cell (n := j) h (by nlinarith)
    · exact safe_of_cell (n := j) (by nlinarith) (by nlinarith)
  · let r := ((j : ℝ) + δ - Y) / ρ
    have he : ρ * r + Y = (j : ℝ) + δ := by dsimp [r]; field_simp; ring
    have hl : δ ≤ r := by nlinarith
    have hb : r ≤ 4 * δ := by
      have hm := mul_nonneg (sub_nonneg.mpr hρ) (sub_nonneg.mpr hl)
      nlinarith
    refine ⟨r, hl, hb, ?_, ?_, ?_, Or.inr ⟨j, he, hjl⟩⟩
    · exact safe_of_cell (n := 0) (by norm_num; exact hl) (by norm_num; linarith)
    · exact safe_of_cell (n := j) (by linarith) (by linarith)
    · exact safe_of_cell (n := j) (by nlinarith) (by nlinarith)

/-- Enclose a slow bad interval for a sum-related triple, retaining the phase relation. -/
theorem enclose_triple {δ ρ Y K : ℝ} (hδ : 0 < δ) (hδ6 : δ ≤ 1 / 6)
    (hρ : 1 ≤ ρ) (hK₁ : 5 * δ ≤ 2 * K)
    (hK₂ : δ * (1 + 2 * δ) ≤ (1 - 4 * δ) * K) :
    ∃ l r, l ≤ -δ ∧ δ ≤ r ∧ r - l ≤ 2 * K ∧
      (Safe δ l ∧ Safe δ (ρ * l + Y) ∧ Safe δ ((ρ + 1) * l + Y)) ∧
      (Safe δ r ∧ Safe δ (ρ * r + Y) ∧ Safe δ ((ρ + 1) * r + Y)) := by
  obtain ⟨r, hr, hr4, hrs, hrb, hrc, hrj⟩ := triple_right (Y := Y) hδ hδ6 hρ
  obtain ⟨q, hq, hq4, hqs, hqb, hqc, hqj⟩ := triple_right (Y := -Y) hδ hδ6 hρ
  have hls : Safe δ (-q) := safe_neg hqs
  have hlb : Safe δ (ρ * (-q) + Y) := by convert safe_neg hqb using 1; ring
  have hlc : Safe δ ((ρ + 1) * (-q) + Y) := by convert safe_neg hqc using 1; ring
  refine ⟨-q, r, by linarith, hr, ?_, ⟨hls, hlb, hlc⟩, ⟨hrs, hrb, hrc⟩⟩
  rcases hrj with he | ⟨j, hje, hj⟩
  · linarith
  rcases hqj with he | ⟨i, hie, hi⟩
  · linarith
  have hρp : 0 < ρ := by linarith
  have he : ρ * (r + q) = (j : ℝ) + i + 2 * δ := by nlinarith
  by_cases hij : j + i ≤ 0
  · have hij' : (j : ℝ) + i ≤ 0 := by exact_mod_cast hij
    nlinarith [mul_nonneg (sub_nonneg.mpr hρ) (by linarith : 0 ≤ r + q)]
  · have hm : (1 : ℝ) ≤ (j : ℝ) + i := by exact_mod_cast (by omega : 1 ≤ j + i)
    have hsep : (j : ℝ) + i - 4 * δ < 2 * ρ * δ := by nlinarith
    have hratio : (1 - 4 * δ) * ((j : ℝ) + i + 2 * δ) ≤
        (1 + 2 * δ) * ((j : ℝ) + i - 4 * δ) := by
      nlinarith [mul_nonneg hδ.le (by linarith : 0 ≤ (j : ℝ) + i - 1)]
    have hprod : (1 - 4 * δ) * (ρ * (r + q)) < (1 + 2 * δ) * (2 * ρ * δ) := by
      rw [he]
      exact lt_of_le_of_lt hratio (mul_lt_mul_of_pos_left hsep (by linarith))
    have hw : (1 - 4 * δ) * (r + q) < 2 * δ * (1 + 2 * δ) := by nlinarith
    have hp : 0 < 1 - 4 * δ := by linarith
    nlinarith

/-- A short enclosing interval has a nearby endpoint even if the reference is outside it. -/
theorem endpoint_choice_near {l r s t K : ℝ} (hls : l ≤ s) (hsr : s ≤ r)
    (hst : |s - t| ≤ K) (hw : r - l ≤ 2 * K)
    (P : ℝ → Prop) (hl : P l) (hr : P r) : ∃ u, |u - t| ≤ K ∧ P u := by
  rcases abs_le.mp hst with ⟨hstl, hstr⟩
  by_cases htl : t < l
  · exact ⟨l, by rw [abs_of_pos (by linarith)]; linarith, hl⟩
  by_cases hrt : r < t
  · exact ⟨r, by rw [abs_of_neg (by linarith)]; linarith, hr⟩
  exact endpoint_choice (by linarith) (by linarith) hw P hl hr

/-- Uniform local escape for speeds `1, ρ, ρ+1` with compatible initial phases. -/
theorem triple_escape_normalized {δ ρ x y K t : ℝ} (hδ : 0 < δ) (hδ6 : δ ≤ 1 / 6)
    (hρ : 1 ≤ ρ) (hK₁ : 5 * δ ≤ 2 * K)
    (hK₂ : δ * (1 + 2 * δ) ≤ (1 - 4 * δ) * K) :
    ∃ s, |s - t| ≤ K ∧ Safe δ (s + x) ∧ Safe δ (ρ * s + y) ∧
      Safe δ ((ρ + 1) * s + (x + y)) := by
  have hρp : 0 < ρ := by linarith
  obtain ⟨s, hst, hsb, hsc⟩ := two_speed_escape_small
    (a := ρ) (b := ρ + 1) (x := y) (y := x + y) (t := t) hδ hδ6 hρp (by linarith)
  have hstK : |s - t| ≤ K := by
    apply le_trans hst
    apply (div_le_iff₀ hρp).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hρ) (by linarith : 0 ≤ K)]
  by_cases hsa : Safe δ (s + x)
  · exact ⟨s, hstK, hsa, hsb, hsc⟩
  obtain ⟨n, hn⟩ := not_safe_iff.mp hsa
  let c : ℝ := n - x
  let Y : ℝ := ρ * c + y
  obtain ⟨l,r,hl,hr,hw,hls,hrs⟩ := enclose_triple (Y := Y) hδ hδ6 hρ hK₁ hK₂
  let P := fun u : ℝ => Safe δ (u + x) ∧ Safe δ (ρ * u + y) ∧
    Safe δ ((ρ + 1) * u + (x + y))
  have htranslate : ∀ u, Safe δ u ∧ Safe δ (ρ * u + Y) ∧ Safe δ ((ρ + 1) * u + Y) → P (c + u) := by
    intro u hu
    refine ⟨?_, ?_, ?_⟩
    · convert safe_add_int hu.1 n using 1
      dsimp [c]; ring
    · convert hu.2.1 using 1
      dsimp [Y]; ring
    · convert safe_add_int hu.2.2 n using 1
      dsimp [c,Y]; ring
  apply endpoint_choice_near (s := s) (l := c + l) (r := c + r) ?_ ?_ hstK
    (by linarith) P (htranslate l hls) (htranslate r hrs)
  · dsimp [c]; have := (abs_lt.mp hn).1; linarith
  · dsimp [c]; have := (abs_lt.mp hn).2; linarith

noncomputable def tripleRadius (δ : ℝ) : ℝ :=
  max (5 * δ / 2) (δ * (1 + 2 * δ) / (1 - 4 * δ))

/-- The optimal normalized bound, rescaled to actual speeds. -/
theorem triple_escape {δ d a x y t : ℝ} (hδ : 0 < δ) (hδ6 : δ ≤ 1 / 6)
    (hd : 0 < d) (hda : d ≤ a) :
    ∃ s, |s - t| ≤ tripleRadius δ / d ∧ Safe δ (d * s + x) ∧
      Safe δ (a * s + y) ∧ Safe δ ((a + d) * s + (x + y)) := by
  have hρ : 1 ≤ a / d := (le_div_iff₀ hd).mpr (by simpa using hda)
  have hK₁ : 5 * δ ≤ 2 * tripleRadius δ := by
    have := le_max_left (5 * δ / 2) (δ * (1 + 2 * δ) / (1 - 4 * δ))
    change 5 * δ ≤ 2 * max _ _
    linarith
  have hK₂ : δ * (1 + 2 * δ) ≤ (1 - 4 * δ) * tripleRadius δ := by
    have hp : 0 < 1 - 4 * δ := by linarith
    have := (div_le_iff₀ hp).mp (le_max_right (5 * δ / 2)
      (δ * (1 + 2 * δ) / (1 - 4 * δ)))
    dsimp [tripleRadius]; nlinarith
  obtain ⟨u,hu,hus,hub,huc⟩ := triple_escape_normalized
    (x := x) (y := y) (t := d * t) hδ hδ6 hρ hK₁ hK₂
  refine ⟨u / d, ?_, ?_, ?_, ?_⟩
  · have he : u / d - t = (u - d * t) / d := by field_simp
    rw [he, abs_div, abs_of_pos hd]
    exact (div_le_div_iff_of_pos_right hd).mpr hu
  · simpa [mul_div_cancel₀ _ hd.ne'] using hus
  · convert hub using 1; ring
  · convert huc using 1
    field_simp

theorem tripleRadius_small {δ : ℝ} (hδ : 0 ≤ δ) (hδ8 : δ ≤ 1 / 8) :
    tripleRadius δ = 5 * δ / 2 := by
  apply max_eq_left
  apply (div_le_iff₀ (by linarith : 0 < 1 - 4 * δ)).mpr
  nlinarith [mul_nonneg hδ (by linarith : 0 ≤ 1 / 8 - δ)]

/-- Three related speeds are removed at once; the core has size `k-3`. -/
theorem delete_sum_triple {k : ℕ} (hk : 7 ≤ k) (v phase : Fin (k - 3) → ℝ)
    {d a x y M : ℝ} (hd : 0 < d) (hda : d ≤ a)
    (hspeed : ∀ i, |v i| ≤ M) (hfast : 5 * ((k : ℝ) - 2) * M ≤ 6 * d)
    (hcore : ∃ t, ∀ i, Safe (1 / ((k : ℝ) - 2)) (v i * t + phase i)) :
    ∃ s, (∀ i, Safe (1 / ((k : ℝ) + 1)) (v i * s + phase i)) ∧
      Safe (1 / ((k : ℝ) + 1)) (d * s + x) ∧
      Safe (1 / ((k : ℝ) + 1)) (a * s + y) ∧
      Safe (1 / ((k : ℝ) + 1)) ((a + d) * s + (x + y)) := by
  have hk' : (7 : ℝ) ≤ k := by exact_mod_cast hk
  have hk2 : 0 < (k : ℝ) - 2 := by linarith
  have hkp : 0 < (k : ℝ) + 1 := by linarith
  let δ : ℝ := 1 / ((k : ℝ) + 1)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ8 : δ ≤ 1 / 8 := by
    dsimp [δ]; apply (div_le_div_iff₀ hkp (by norm_num)).mpr; linarith
  have hbound : δ + M * (tripleRadius δ / d) ≤ 1 / ((k : ℝ) - 2) := by
    rw [tripleRadius_small hδ.le hδ8]
    dsimp [δ]
    apply (le_div_iff₀ hk2).mpr
    field_simp
    nlinarith
  obtain ⟨t,ht⟩ := hcore
  obtain ⟨s,hst,hsd,hsa,hsb⟩ := triple_escape (x := x) (y := y) (t := t)
    hδ (by linarith) hd hda
  refine ⟨s, ?_, hsd, hsa, hsb⟩
  intro i
  have hmargin : Safe (δ + M * (tripleRadius δ / d)) (v i * t + phase i) :=
    fun n => le_trans hbound (ht i n)
  apply safe_stable hmargin
  have he : v i * s + phase i - (v i * t + phase i) = v i * (s - t) := by ring
  rw [he, abs_mul]
  exact mul_le_mul (hspeed i) hst (abs_nonneg _) (le_trans (abs_nonneg _) (hspeed i))

end PhaseWindow
