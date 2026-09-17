import Mathlib
import Research07.M3.Relations

noncomputable section

open Finset Matrix

-- check how `k i * x i` elaborates inside kerSpanRat
example {n : ℕ} (u : Fin n → ℝ) (x : Fin n → ℚ) :
    x ∈ kerSpanRat u ↔ ∀ k ∈ relLattice u, ∑ i, (k i : ℚ) * x i = 0 := by
  rfl

example {n : ℕ} (u : Fin n → ℝ) (x : Fin n → ℝ) :
    x ∈ kerSpan u ↔ ∀ k ∈ relLattice u, ∑ i, (k i : ℝ) * x i = 0 := by
  rfl

end
