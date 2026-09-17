import Mathlib
import Research07.M3.Relations
import Research07.M3.Subtorus
import Research07.M3.FlowDense

noncomputable section

-- Probe A: basis extraction + rho definition
example {n : ℕ} (u : Fin n → ℝ) : True := by
  obtain ⟨d, ⟨b⟩⟩ := Submodule.nonempty_basis_of_pid (Pi.basisFun ℤ (Fin n)) (kerSpanInt u)
  set K := kerSpanInt u with hK
  set ρ : Fin d → Fin n → ℤ := fun ℓ => (b ℓ : Fin n → ℤ) with hρ
  have hmem : ∀ ℓ, ρ ℓ ∈ kerSpanInt u := fun ℓ => (b ℓ).2
  have hinj : LinearIndependent ℤ ρ :=
    b.linearIndependent.map' K.subtype K.ker_subtype
  have hspaneq : Submodule.span ℤ (Set.range ρ) = K := by
    have himg : K.subtype '' (Set.range b) = Set.range ρ := by
      rw [← Set.range_comp]; rfl
    rw [← himg, ← Submodule.map_span, b.span_eq, Submodule.map_subtype_top]
  have hspan : ∀ x : Fin n → ℤ, x ∈ kerSpanInt u → x ∈ Submodule.span ℤ (Set.range ρ) := by
    intro x hx; rw [hspaneq]; exact hx
  trivial

-- Probe B: kerSpanRat cast membership
example {n : ℕ} (u : Fin n → ℝ) (y : Fin n → ℤ) (hy : y ∈ kerSpanInt u) :
    (fun i => (y i : ℚ)) ∈ kerSpanRat u := by
  intro k hk
  have h := hy k hk
  exact_mod_cast h

-- Probe C: common denominator
example {n : ℕ} (x : Fin n → ℚ) :
    ∃ m : ℕ, 0 < m ∧ ∀ i, ∃ z : ℤ, (z : ℚ) = m * x i := by
  refine ⟨∏ i, (x i).den, Finset.prod_pos fun i _ => Rat.den_pos _, fun i => ?_⟩
  obtain ⟨s, hs⟩ := Finset.dvd_prod_of_mem (fun i => (x i).den) (Finset.mem_univ i)
  refine ⟨s * (x i).num, ?_⟩
  have hden : ((x i).den : ℚ) * x i = (x i).num := by
    conv_lhs => rw [← Rat.num_div_den (x i)]
    rw [mul_div_cancel₀]
    exact_mod_cast (Rat.den_pos (x i)).ne'
  calc ((s * (x i).num : ℤ) : ℚ)
      = (s : ℚ) * (((x i).den : ℚ) * x i) := by rw [hden]; push_cast; ring
    _ = (m : ℚ) * x i := by rw [hs]; push_cast; ring

end
