import Mathlib
import Research07.M3.Relations
import Research07.M3.Subtorus
import Research07.M3.FlowDense

noncomputable section

-- Probe B': kerSpanRat cast membership (beta issue)
example {n : ℕ} (u : Fin n → ℝ) (y : Fin n → ℤ) (hy : y ∈ kerSpanInt u) :
    (fun i => (y i : ℚ)) ∈ kerSpanRat u := by
  intro k hk
  show ∑ i, (k i : ℚ) * (y i : ℚ) = 0
  exact_mod_cast hy k hk

-- Probe C': common denominator
example {n : ℕ} (x : Fin n → ℚ) :
    ∃ m : ℕ, 0 < m ∧ ∀ i, ∃ z : ℤ, (z : ℚ) = m * x i := by
  refine ⟨∏ i, (x i).den, Finset.prod_pos fun i _ => Rat.den_pos _, fun i => ?_⟩
  obtain ⟨s, hs⟩ := Finset.dvd_prod_of_mem (fun i => (x i).den) (Finset.mem_univ i)
  refine ⟨s * (x i).num, ?_⟩
  have hden : ((x i).den : ℚ) * x i = (x i).num := by
    nth_rewrite 2 [← Rat.num_div_den (x i)]
    rw [← mul_div_assoc, mul_div_cancel_left₀]
    exact_mod_cast (Rat.den_pos (x i)).ne'
  calc ((s * (x i).num : ℤ) : ℚ)
      = (s : ℚ) * (((x i).den : ℚ) * x i) := by rw [hden]; push_cast; ring
    _ = ((x i).den * s : ℕ) * x i := by push_cast; ring
    _ = ((∏ j, (x j).den : ℕ) : ℚ) * x i := by rw [hs]

-- Probe D: y in kerSpanInt from denominators (mod_cast down)
example {n : ℕ} (u : Fin n → ℝ) (x : Fin n → ℚ) (hx : x ∈ kerSpanRat u)
    (m : ℕ) (y : Fin n → ℤ) (hy : ∀ i, (y i : ℚ) = m * x i) :
    y ∈ kerSpanInt u := by
  intro k hk
  have hxk : ∑ i, (k i : ℚ) * x i = 0 := hx k hk
  have h0 : (∑ i, (k i : ℚ) * (y i : ℚ)) = 0 := by
    calc ∑ i, (k i : ℚ) * (y i : ℚ)
        = ∑ i, (k i : ℚ) * ((m : ℚ) * x i) := by
          apply Finset.sum_congr rfl; intro i _; rw [hy i]
      _ = (m : ℚ) * ∑ i, (k i : ℚ) * x i := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
      _ = 0 := by rw [hxk, mul_zero]
  exact_mod_cast h0

-- Probe E: cast expansion to span over ℚ
example {n d : ℕ} (a : Fin d → ℤ) (ρ : Fin d → Fin n → ℤ)
    (ρQ : Fin d → Fin n → ℚ) (hρQ : ρQ = fun ℓ i => (ρ ℓ i : ℚ))
    (y : Fin n → ℤ) (ha : ∑ ℓ, a ℓ • ρ ℓ = y) :
    (fun i => (y i : ℚ)) = ∑ ℓ, (a ℓ : ℚ) • ρQ ℓ := by
  funext i
  have hcast : ((y i : ℤ) : ℚ) = (∑ ℓ, (a ℓ : ℚ) * (ρ ℓ i : ℚ)) := by
    rw [← ha]
    simp only [Finset.sum_apply', Pi.smul_apply, smul_eq_mul, Int.cast_sum, Int.cast_mul]
  rw [hcast]
  apply Finset.sum_congr rfl; intro ℓ _
  rw [Pi.smul_apply, smul_eq_mul, hρQ]

-- Probe F: x = m⁻¹ • yQ
example {n : ℕ} (x : Fin n → ℚ) (m : ℕ) (hm0 : 0 < m) (y : Fin n → ℤ)
    (hy : ∀ i, (y i : ℚ) = m * x i) :
    x = ((m : ℚ))⁻¹ • (fun i => (y i : ℚ)) := by
  funext i
  have hmi : (m : ℚ) ≠ 0 := by exact_mod_cast hm0.ne'
  rw [Pi.smul_apply, smul_eq_mul, hy i]
  rw [inv_mul_cancel_left₀ hmi]

end
