/-
Copyright (c) 2026 Research07 contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Research07 contributors
-/
import Mathlib
import Research07.LRC3.Circ

/-!
# W6 — Relation lattice API for the BHK reduction (FROZEN STATEMENTS)

For a real tuple `u : Fin n → ℝ` (relative speeds), the **relation lattice** is the set of
integer vectors `k` with `∑ kᵢ·uᵢ = 0`; the **kernel space** `kerSpan u` (= BHK's `Ker(A)`)
is the real subspace annihilated by all relations — equivalently the smallest
rationally-defined subspace containing `u`.

Frozen contract for agent W6. Prove every `sorry`; do not change statements.
-/

noncomputable section

/-- The integer relation lattice of a real tuple: `k : Fin n → ℤ` with `∑ kᵢ·uᵢ = 0`. -/
def relLattice {n : ℕ} (u : Fin n → ℝ) : Submodule ℤ (Fin n → ℤ) :=
  LinearMap.ker (Fintype.linearCombination ℤ u)

/-- The kernel space `Ker(A)`: real vectors annihilated by every integer relation of `u`. -/
def kerSpan {n : ℕ} (u : Fin n → ℝ) : Submodule ℝ (Fin n → ℝ) where
  carrier := {x | ∀ k ∈ relLattice u, ∑ i, (k i : ℝ) * x i = 0}
  add_mem' := by
    intro x y hx hy k hk
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
    rw [hx k hk, hy k hk, add_zero]
  zero_mem' := by
    intro k _
    simp
  smul_mem' := by
    intro c x hx k hk
    simp only [Pi.smul_apply, smul_eq_mul, mul_left_comm]
    rw [← Finset.mul_sum, hx k hk, mul_zero]

/-- The rational points of `kerSpan u` (kernel of the rational relation matrix). -/
def kerSpanRat {n : ℕ} (u : Fin n → ℝ) : Submodule ℚ (Fin n → ℚ) where
  carrier := {x | ∀ k ∈ relLattice u, ∑ i, k i * x i = 0}
  add_mem' := by
    intro x y hx hy k hk
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
    rw [hx k hk, hy k hk, add_zero]
  zero_mem' := by
    intro k _
    simp
  smul_mem' := by
    intro c x hx k hk
    simp only [Pi.smul_apply, smul_eq_mul, mul_left_comm]
    rw [← Finset.mul_sum, hx k hk, mul_zero]

/-- `u` lies in its own kernel space. -/
theorem mem_kerSpan_self {n : ℕ} (u : Fin n → ℝ) : u ∈ kerSpan u := by
  intro k hk
  rw [relLattice, LinearMap.mem_ker, Fintype.linearCombination_apply] at hk
  simpa only [zsmul_eq_mul] using hk

/-- The integer points of the kernel space — a pure (complemented) `ℤ`-submodule. -/
def kerSpanInt {n : ℕ} (u : Fin n → ℝ) : Submodule ℤ (Fin n → ℤ) where
  carrier := {x | ∀ k ∈ relLattice u, ∑ i, k i * x i = 0}
  add_mem' := by
    intro x y hx hy k hk
    simp only [Pi.add_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib]
    rw [hx k hk, hy k hk, add_zero]
  zero_mem' := by
    intro k _
    simp
  smul_mem' := by
    intro c x hx k hk
    simp only [Pi.smul_apply, smul_eq_mul, mul_left_comm]
    rw [← Finset.mul_sum, hx k hk, mul_zero]

/-- The annihilator subtorus: points of `Tⁿ` killed by every integer relation of `u`.
BHK's `M̄(u) = Ker(A) + ℤⁿ` projected to the torus. -/
def annihilator {n : ℕ} (u : Fin n → ℝ) : Set (Fin n → UnitAddCircle) :=
  {y | ∀ k ∈ relLattice u, ∑ i, (k i) • y i = 0}

/-- `kerSpan u` is defined by rational equations, so its rational points span it:
`kerSpan u` is the `ℝ`-span of `kerSpanRat u` (cast into `ℝ`). -/
theorem kerSpan_eq_span_rat {n : ℕ} (u : Fin n → ℝ) :
    kerSpan u = Submodule.span ℝ ((fun x : Fin n → ℚ => fun i => (x i : ℝ)) ''
      (kerSpanRat u : Set (Fin n → ℚ))) := by
  sorry

/-- A positive real `u ∈ kerSpan u` yields a positive rational point of `kerSpan`:
perturb a rational basis expansion of `u` keeping positivity. -/
theorem exists_pos_rat_kerSpan {n : ℕ} (u : Fin n → ℝ) (hpos : ∀ i, 0 < u i) :
    ∃ r : Fin n → ℚ, (∀ i, 0 < r i) ∧ r ∈ kerSpanRat u := by
  sorry

/-- If `u` is not proportional to a rational vector, `kerSpanRat` has another vector
linearly independent from any given `r`. (Contrapositive: `kerSpanRat = ℚ·r` would put
`u ∈ ℝ·r`.) -/
theorem exists_kerSpanRat_not_parallel {n : ℕ} (u : Fin n → ℝ) (r : Fin n → ℚ)
    (hr : r ∈ kerSpanRat u)
    (h : ¬ ∃ c : ℝ, ∀ i, u i = c * (r i : ℝ)) :
    ∃ s : Fin n → ℚ, s ∈ kerSpanRat u ∧ ∀ a : ℚ, s ≠ a • r := by
  sorry

/-- **Minimality lemma.** Write `u` in a `ℚ`-basis `ρ` of `kerSpanRat u`:
`u i = ∑ ℓ, c ℓ * ρ ℓ i`. The coefficient tuple `c` is `ℚ`-linearly independent —
a relation among the `c ℓ` would put `u` in the `ℝ`-span of fewer rational vectors,
i.e. a strictly smaller rationally-defined subspace, contradicting the definition of
`kerSpan u` as the annihilator of *all* relations. -/
theorem kernel_coords_linearIndependent {n d : ℕ} (u : Fin n → ℝ) (ρ : Fin d → Fin n → ℚ)
    (hρspan : ∀ x : Fin n → ℚ, x ∈ kerSpanRat u → x ∈ Submodule.span ℚ (Set.range ρ))
    (c : Fin d → ℝ) (hc : ∀ i, u i = ∑ ℓ, c ℓ * (ρ ℓ i : ℝ)) :
    LinearIndependent ℚ c := by
  sorry

end
