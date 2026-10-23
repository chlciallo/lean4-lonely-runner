import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

namespace PhaseWindow

/-- Distance at least `d` from every integer, including the boundary. -/
def Safe (d x : ℝ) : Prop := ∀ n : ℤ, d ≤ |x - n|

theorem safe_of_cell {d x : ℝ} {n : ℤ}
    (hl : (n : ℝ) + d ≤ x) (hr : x ≤ (n : ℝ) + 1 - d) : Safe d x := by
  intro m
  by_cases h : m ≤ n
  · have hm : (m : ℝ) ≤ n := by exact_mod_cast h
    exact le_trans (by linarith) (le_abs_self (x - m))
  · have hm : (n : ℝ) + 1 ≤ m := by exact_mod_cast (by omega : n + 1 ≤ m)
    exact le_trans (by linarith) (neg_le_abs (x - m))

theorem not_safe_iff {d x : ℝ} : ¬ Safe d x ↔ ∃ n : ℤ, |x - n| < d := by
  simp only [Safe, not_forall, not_le]

theorem safe_stable {d e x y : ℝ} (h : Safe (d + e) x) (hxy : |y - x| ≤ e) :
    Safe d y := by
  intro n
  have ht : |x - n| ≤ |y - n| + |y - x| := by
    calc
      |x - n| = |(y - n) - (y - x)| := by congr 1; ring
      _ ≤ |y - n| + |y - x| := abs_sub _ _
  have hn := h n
  linarith

/-- Safe endpoints surrounding a forbidden component yield a nearby witness. -/
theorem endpoint_choice {l r t K : ℝ} (hlt : l ≤ t) (htr : t ≤ r)
    (hw : r - l ≤ 2 * K) (P : ℝ → Prop) (hl : P l) (hr : P r) :
    ∃ s, |s - t| ≤ K ∧ P s := by
  by_cases h : t - l ≤ K
  · exact ⟨l, by rw [abs_of_nonpos (by linarith)]; linarith, hl⟩
  · exact ⟨r, by rw [abs_of_nonneg (by linarith)]; linarith, hr⟩

/-- Moving left to the endpoint of the current bad interval, if necessary. -/
theorem exit_left {d v x t : ℝ} (hd : 0 ≤ d) (hdh : d ≤ 1 / 2) (hv : 0 < v) :
    ∃ l, l ≤ t ∧ v * (t - l) ≤ 2 * d ∧ Safe d (v * l + x) ∧
      (l = t ∨ ∃ j : ℤ, v * l + x = j - d ∧ |v * t + x - j| < d) := by
  by_cases hs : Safe d (v * t + x)
  · exact ⟨t, le_rfl, by nlinarith, hs, Or.inl rfl⟩
  · obtain ⟨j, hj⟩ := not_safe_iff.mp hs
    rcases abs_lt.mp hj with ⟨hjl, hjr⟩
    let l := ((j : ℝ) - d - x) / v
    have he : v * l + x = (j : ℝ) - d := by dsimp [l]; field_simp; ring
    refine ⟨l, ?_, ?_, ?_, Or.inr ⟨j, he, hj⟩⟩
    · nlinarith
    · nlinarith
    · apply safe_of_cell (n := j - 1)
      · push_cast; linarith
      · push_cast; linarith

theorem exit_right {d v x t : ℝ} (hd : 0 ≤ d) (hdh : d ≤ 1 / 2) (hv : 0 < v) :
    ∃ r, t ≤ r ∧ v * (r - t) ≤ 2 * d ∧ Safe d (v * r + x) ∧
      (r = t ∨ ∃ j : ℤ, v * r + x = j + d ∧ |v * t + x - j| < d) := by
  by_cases hs : Safe d (v * t + x)
  · exact ⟨t, le_rfl, by nlinarith, hs, Or.inl rfl⟩
  · obtain ⟨j, hj⟩ := not_safe_iff.mp hs
    rcases abs_lt.mp hj with ⟨hjl, hjr⟩
    let r := ((j : ℝ) + d - x) / v
    have he : v * r + x = (j : ℝ) + d := by dsimp [r]; field_simp; ring
    refine ⟨r, ?_, ?_, ?_, Or.inr ⟨j, he, hj⟩⟩
    · nlinarith
    · nlinarith
    · apply safe_of_cell (n := j) <;> linarith

end PhaseWindow
