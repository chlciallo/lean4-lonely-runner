import Mathlib
import Research07.M3.Relations

noncomputable section

open Finset Matrix

-- sanity checks: membership unfolds to the carrier definition
example {n : ℕ} (u : Fin n → ℝ) (x : Fin n → ℚ) :
    x ∈ kerSpanRat u ↔ ∀ k ∈ relLattice u, ∑ i, (k i : ℚ) * x i = 0 := by
  rfl

example {n : ℕ} (u : Fin n → ℝ) (x : Fin n → ℝ) :
    x ∈ kerSpan u ↔ ∀ k ∈ relLattice u, ∑ i, (k i : ℝ) * x i = 0 := by
  rfl

/-- **Countermodel to the frozen `kernel_coords_linearIndependent`** (W6).

Take `n = 1`, `d = 2`, `u = (1)`, `ρ = ((1), (1))` — a *spanning* but
`ℚ`-linearly *dependent* family (duplicate vectors) — and `c = (1/2, 1/2)`.
Then `kerSpanRat u ⊆ span ρ` (in fact `span ρ = ⊤`), `u = ∑ c ℓ • ρ ℓ`, yet
`c` is `ℚ`-linearly dependent: `1 • c 0 + (-1) • c 1 = 0`.

Hence `hρspan` alone cannot force `c` to be `ℚ`-independent: the coordinates
of `u` in a dependent spanning family are not unique. The fix (proved as
`kernel_coords_linearIndependent_of_basis`) requires `ρ ℓ ∈ kerSpanRat u`
and `LinearIndependent ℚ ρ`. -/
example : ¬ (∀ {n d : ℕ} (u : Fin n → ℝ) (ρ : Fin d → Fin n → ℚ)
      (_hρspan : ∀ x : Fin n → ℚ, x ∈ kerSpanRat u →
        x ∈ Submodule.span ℚ (Set.range ρ))
      (c : Fin d → ℝ) (_hc : ∀ i, u i = ∑ ℓ, c ℓ * (ρ ℓ i : ℝ)),
      LinearIndependent ℚ c) := by
  intro h
  have hLI : LinearIndependent ℚ (fun _ : Fin 2 => (1 / 2 : ℝ)) :=
    h (fun _ => 1) (fun _ _ => 1)
      (fun x _ => by
        have hx : x = x 0 • (fun _ : Fin 1 => (1 : ℚ)) := by
          funext i
          rw [Fin.eq_zero i]
          simp
        rw [hx]
        exact Submodule.smul_mem _ _
          (Submodule.subset_span (Set.mem_range_self (0 : Fin 2))))
      (fun _ => 1 / 2)
      (fun i => by norm_num [Fin.sum_univ_two])
  rw [Fintype.linearIndependent_iff] at hLI
  have hrel : ∑ i, (![(1 : ℚ), -1] i) • (1 / 2 : ℝ) = 0 := by
    norm_num [Fin.sum_univ_two, smul_eq_mul]
  have h0 := hLI (![(1 : ℚ), -1]) hrel 0
  simp at h0

end
