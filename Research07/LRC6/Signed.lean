/-
Copyright (c) 2026 Research07 contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Research07 contributors
-/
import Mathlib
import Research07.LRC6.Setup
import Research07.LRC6.Lemma51
import Research07.LRC6.Lemma61
import Research07.LRC6.Lemma64

/-!
# signed variants of the combinatorial lemmas

Renault derives Lemmas 5.2/5.3/6.2/6.3/6.5 from the base combinatorial lemmas
(Lemmas 5.1, 6.1, 6.4) by flipping positions `yᵢ = ⟨εᵢ·xᵢ⟩` or `yᵢ = ⟨−εᵢ·xᵢ⟩`
with `εᵢ ∈ {±1}`.

* `signed_move_Icc` / `signed_move_Ioo`: `⟨λ·⟨εx⟩ + s⟩` is (strictly) safe iff
  `⟨λx + ε·s⟩` is — because `ε·(λx + εs) = λ·(εx) + s` and the band is
  symmetric under `u ↦ 1 − u`.
* `signed_move_neg_Icc` / `signed_move_neg_Ioo`: the `yᵢ = ⟨−εx⟩` variant
  Renault uses to shift `α ↦ 6 − α`: `⟨λ·⟨−εx⟩ + s⟩` safe iff
  `⟨λx + ε(1 − s)⟩` is.
-/

noncomputable section

/-- `fract (λ·fract z) = fract (λ·z)` for `λ : ℕ`. -/
theorem fract_mul_fract_nat (lam : ℕ) (z : ℝ) :
    Int.fract ((lam : ℝ) * Int.fract z) = Int.fract ((lam : ℝ) * z) := by
  have hm := fract_nat_mul 1 lam z
  simp only [Nat.cast_one, one_mul] at hm
  exact hm.symm

theorem signed_move_Icc {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (x : ℝ) (lam : ℕ) (s : ℝ) :
    Int.fract ((lam : ℝ) * Int.fract ((ε : ℝ) * x) + s) ∈ Set.Icc (1 / 6) (5 / 6) ↔
      Int.fract ((lam : ℝ) * x + (ε : ℝ) * s) ∈ Set.Icc (1 / 6) (5 / 6) := by
  have h1 : Int.fract ((lam : ℝ) * Int.fract ((ε : ℝ) * x)) =
      Int.fract ((ε : ℝ) * ((lam : ℝ) * x)) := by
    rw [fract_mul_fract_nat]
    congr 1; ring
  rw [fract_self_add ((lam : ℝ) * Int.fract ((ε : ℝ) * x)) s, h1,
      ← fract_self_add ((ε : ℝ) * ((lam : ℝ) * x)) s]
  rcases hε with rfl | rfl
  · simp
  · have h3 : ((-1 : ℤ) : ℝ) * ((lam : ℝ) * x) + s = -(((lam : ℝ) * x) - s) := by push_cast; ring
    rw [h3, fract_neg_mem_Icc]
    have h2 : (lam : ℝ) * x + ((-1 : ℤ) : ℝ) * s = (lam : ℝ) * x - s := by push_cast; ring
    rw [h2]

theorem signed_move_Ioo {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (x : ℝ) (lam : ℕ) (s : ℝ) :
    Int.fract ((lam : ℝ) * Int.fract ((ε : ℝ) * x) + s) ∈ Set.Ioo (1 / 6) (5 / 6) ↔
      Int.fract ((lam : ℝ) * x + (ε : ℝ) * s) ∈ Set.Ioo (1 / 6) (5 / 6) := by
  have h1 : Int.fract ((lam : ℝ) * Int.fract ((ε : ℝ) * x)) =
      Int.fract ((ε : ℝ) * ((lam : ℝ) * x)) := by
    rw [fract_mul_fract_nat]
    congr 1; ring
  rw [fract_self_add ((lam : ℝ) * Int.fract ((ε : ℝ) * x)) s, h1,
      ← fract_self_add ((ε : ℝ) * ((lam : ℝ) * x)) s]
  rcases hε with rfl | rfl
  · simp
  · have h3 : ((-1 : ℤ) : ℝ) * ((lam : ℝ) * x) + s = -(((lam : ℝ) * x) - s) := by push_cast; ring
    rw [h3, fract_neg_mem_Ioo]
    have h2 : (lam : ℝ) * x + ((-1 : ℤ) : ℝ) * s = (lam : ℝ) * x - s := by push_cast; ring
    rw [h2]

theorem signed_move_neg_Icc {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (x : ℝ) (lam : ℕ) (s : ℝ) :
    Int.fract ((lam : ℝ) * Int.fract (-((ε : ℝ) * x)) + s) ∈ Set.Icc (1 / 6) (5 / 6) ↔
      Int.fract ((lam : ℝ) * x + (ε : ℝ) * (1 - s)) ∈ Set.Icc (1 / 6) (5 / 6) := by
  have h1 : Int.fract ((lam : ℝ) * Int.fract (-((ε : ℝ) * x))) =
      Int.fract (-((ε : ℝ) * ((lam : ℝ) * x))) := by
    rw [fract_mul_fract_nat]
    congr 1; ring
  rw [fract_self_add ((lam : ℝ) * Int.fract (-((ε : ℝ) * x))) s, h1,
      ← fract_self_add (-((ε : ℝ) * ((lam : ℝ) * x))) s]
  rcases hε with rfl | rfl
  · have h3 : -(((1 : ℤ) : ℝ) * ((lam : ℝ) * x)) + s = -(((lam : ℝ) * x) - s) := by push_cast; ring
    rw [h3, fract_neg_mem_Icc]
    have h2 : (lam : ℝ) * x + ((1 : ℤ) : ℝ) * (1 - s) =
        ((lam : ℝ) * x - s) + ((1 : ℤ) : ℝ) := by push_cast; ring
    rw [h2, Int.fract_add_intCast]
  · have h3 : -(((-1 : ℤ) : ℝ) * ((lam : ℝ) * x)) + s = (lam : ℝ) * x + s := by push_cast; ring
    rw [h3]
    have h2 : (lam : ℝ) * x + ((-1 : ℤ) : ℝ) * (1 - s) =
        ((lam : ℝ) * x + s) + ((-1 : ℤ) : ℝ) := by push_cast; ring
    rw [h2, Int.fract_add_intCast]

theorem signed_move_neg_Ioo {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (x : ℝ) (lam : ℕ) (s : ℝ) :
    Int.fract ((lam : ℝ) * Int.fract (-((ε : ℝ) * x)) + s) ∈ Set.Ioo (1 / 6) (5 / 6) ↔
      Int.fract ((lam : ℝ) * x + (ε : ℝ) * (1 - s)) ∈ Set.Ioo (1 / 6) (5 / 6) := by
  have h1 : Int.fract ((lam : ℝ) * Int.fract (-((ε : ℝ) * x))) =
      Int.fract (-((ε : ℝ) * ((lam : ℝ) * x))) := by
    rw [fract_mul_fract_nat]
    congr 1; ring
  rw [fract_self_add ((lam : ℝ) * Int.fract (-((ε : ℝ) * x))) s, h1,
      ← fract_self_add (-((ε : ℝ) * ((lam : ℝ) * x))) s]
  rcases hε with rfl | rfl
  · have h3 : -(((1 : ℤ) : ℝ) * ((lam : ℝ) * x)) + s = -(((lam : ℝ) * x) - s) := by push_cast; ring
    rw [h3, fract_neg_mem_Ioo]
    have h2 : (lam : ℝ) * x + ((1 : ℤ) : ℝ) * (1 - s) =
        ((lam : ℝ) * x - s) + ((1 : ℤ) : ℝ) := by push_cast; ring
    rw [h2, Int.fract_add_intCast]
  · have h3 : -(((-1 : ℤ) : ℝ) * ((lam : ℝ) * x)) + s = (lam : ℝ) * x + s := by push_cast; ring
    rw [h3]
    have h2 : (lam : ℝ) * x + ((-1 : ℤ) : ℝ) * (1 - s) =
        ((lam : ℝ) * x + s) + ((-1 : ℤ) : ℝ) := by push_cast; ring
    rw [h2, Int.fract_add_intCast]

/-- Renault Lemma 5.2: the signed variant of Lemma 5.1 (`yᵢ = ⟨εᵢ·xᵢ⟩`). -/
theorem lemma5_2 {x₃ x₄ x₅ : ℝ} {e₃ e₄ e₅ : ℤ}
    (he3 : e₃ = 1 ∨ e₃ = -1) (he4 : e₄ = 1 ∨ e₄ = -1) (he5 : e₅ = 1 ∨ e₅ = -1)
    (_h3 : x₃ ∈ Set.Ico 0 1) (_h4 : x₄ ∈ Set.Ico 0 1) (_h5 : x₅ ∈ Set.Ico 0 1) :
    (∃ lam al : ℕ, 2 ≤ lam ∧ lam ≤ 5 ∧ 1 ≤ al ∧ al ≤ 5 ∧
        Int.fract ((lam : ℝ) * x₃ + (e₃ : ℝ) * (al : ℝ) / 6) ∈ Set.Icc (1 / 6) (5 / 6) ∧
        Int.fract ((lam : ℝ) * x₄ + (e₄ : ℝ) * (al : ℝ) / 6) ∈ Set.Icc (1 / 6) (5 / 6) ∧
        Int.fract ((lam : ℝ) * x₅ + (e₅ : ℝ) * (al : ℝ) / 6) ∈ Set.Icc (1 / 6) (5 / 6))
    ∨
    (∃ al : ℕ, (al = 1 ∨ al = 2 ∨ al = 4) ∧
        Int.fract (x₃ + (e₃ : ℝ) * (al : ℝ) / 6) ∈ Set.Ioo (1 / 6) (5 / 6) ∧
        Int.fract (x₄ + (e₄ : ℝ) * (al : ℝ) / 6) ∈ Set.Ioo (1 / 6) (5 / 6) ∧
        Int.fract (x₅ + (e₅ : ℝ) * (al : ℝ) / 6) ∈ Set.Ioo (1 / 6) (5 / 6)) := by
  have hy3 : Int.fract ((e₃ : ℝ) * x₃) ∈ Set.Ico 0 1 :=
    ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
  have hy4 : Int.fract ((e₄ : ℝ) * x₄) ∈ Set.Ico 0 1 :=
    ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
  have hy5 : Int.fract ((e₅ : ℝ) * x₅) ∈ Set.Ico 0 1 :=
    ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
  rcases lemma5_1 hy3 hy4 hy5 with h | h
  · obtain ⟨lam, al, hl2, hl5, ha1, ha5, t3, t4, t5⟩ := h
    refine Or.inl ⟨lam, al, hl2, hl5, ha1, ha5, ?_, ?_, ?_⟩
    · have := (signed_move_Icc he3 x₃ lam ((al : ℝ) / 6)).mp t3
      rwa [mul_div_assoc]
    · have := (signed_move_Icc he4 x₄ lam ((al : ℝ) / 6)).mp t4
      rwa [mul_div_assoc]
    · have := (signed_move_Icc he5 x₅ lam ((al : ℝ) / 6)).mp t5
      rwa [mul_div_assoc]
  · obtain ⟨al, hal, t3, t4, t5⟩ := h
    refine Or.inr ⟨al, hal, ?_, ?_, ?_⟩
    · have sm := signed_move_Ioo he3 x₃ 1 ((al : ℝ) / 6)
      simp only [Nat.cast_one, one_mul] at sm
      have := sm.mp t3
      rwa [mul_div_assoc]
    · have sm := signed_move_Ioo he4 x₄ 1 ((al : ℝ) / 6)
      simp only [Nat.cast_one, one_mul] at sm
      have := sm.mp t4
      rwa [mul_div_assoc]
    · have sm := signed_move_Ioo he5 x₅ 1 ((al : ℝ) / 6)
      simp only [Nat.cast_one, one_mul] at sm
      have := sm.mp t5
      rwa [mul_div_assoc]

/-- Renault Lemma 5.3: the `yᵢ = ⟨−εᵢ·xᵢ⟩` variant, producing `6 − α` shifts. -/
theorem lemma5_3 {x₃ x₄ x₅ : ℝ} {e₃ e₄ e₅ : ℤ}
    (he3 : e₃ = 1 ∨ e₃ = -1) (he4 : e₄ = 1 ∨ e₄ = -1) (he5 : e₅ = 1 ∨ e₅ = -1)
    (_h3 : x₃ ∈ Set.Ico 0 1) (_h4 : x₄ ∈ Set.Ico 0 1) (_h5 : x₅ ∈ Set.Ico 0 1) :
    (∃ lam al : ℕ, 2 ≤ lam ∧ lam ≤ 5 ∧ 1 ≤ al ∧ al ≤ 5 ∧
        Int.fract ((lam : ℝ) * x₃ + (e₃ : ℝ) * (6 - (al : ℝ)) / 6) ∈ Set.Icc (1 / 6) (5 / 6) ∧
        Int.fract ((lam : ℝ) * x₄ + (e₄ : ℝ) * (6 - (al : ℝ)) / 6) ∈ Set.Icc (1 / 6) (5 / 6) ∧
        Int.fract ((lam : ℝ) * x₅ + (e₅ : ℝ) * (6 - (al : ℝ)) / 6) ∈ Set.Icc (1 / 6) (5 / 6))
    ∨
    (∃ al : ℕ, (al = 2 ∨ al = 4 ∨ al = 5) ∧
        Int.fract (x₃ + (e₃ : ℝ) * (al : ℝ) / 6) ∈ Set.Ioo (1 / 6) (5 / 6) ∧
        Int.fract (x₄ + (e₄ : ℝ) * (al : ℝ) / 6) ∈ Set.Ioo (1 / 6) (5 / 6) ∧
        Int.fract (x₅ + (e₅ : ℝ) * (al : ℝ) / 6) ∈ Set.Ioo (1 / 6) (5 / 6)) := by
  have hy3 : Int.fract (-((e₃ : ℝ) * x₃)) ∈ Set.Ico 0 1 :=
    ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
  have hy4 : Int.fract (-((e₄ : ℝ) * x₄)) ∈ Set.Ico 0 1 :=
    ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
  have hy5 : Int.fract (-((e₅ : ℝ) * x₅)) ∈ Set.Ico 0 1 :=
    ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
  rcases lemma5_1 hy3 hy4 hy5 with h | h
  · obtain ⟨lam, al, hl2, hl5, ha1, ha5, t3, t4, t5⟩ := h
    refine Or.inl ⟨lam, al, hl2, hl5, ha1, ha5, ?_, ?_, ?_⟩
    · have := (signed_move_neg_Icc he3 x₃ lam ((al : ℝ) / 6)).mp t3
      rwa [show (e₃ : ℝ) * (1 - (al : ℝ) / 6) = (e₃ : ℝ) * (6 - (al : ℝ)) / 6 by ring] at this
    · have := (signed_move_neg_Icc he4 x₄ lam ((al : ℝ) / 6)).mp t4
      rwa [show (e₄ : ℝ) * (1 - (al : ℝ) / 6) = (e₄ : ℝ) * (6 - (al : ℝ)) / 6 by ring] at this
    · have := (signed_move_neg_Icc he5 x₅ lam ((al : ℝ) / 6)).mp t5
      rwa [show (e₅ : ℝ) * (1 - (al : ℝ) / 6) = (e₅ : ℝ) * (6 - (al : ℝ)) / 6 by ring] at this
  · obtain ⟨al, hal, t3, t4, t5⟩ := h
    -- `α ↦ 6 − α` sends `{1,2,4}` to `{5,4,2}`.
    have hal' : 6 - al = 5 ∨ 6 - al = 4 ∨ 6 - al = 2 := by omega
    refine Or.inr ⟨6 - al, ?_, ?_, ?_, ?_⟩
    · rcases hal' with r | r | r <;> omega
    · have sm := signed_move_neg_Ioo he3 x₃ 1 ((al : ℝ) / 6)
      simp only [Nat.cast_one, one_mul] at sm
      have := sm.mp t3
      have hcast : ((6 - al : ℕ) : ℝ) = 6 - (al : ℝ) := by
        rw [Nat.cast_sub (by omega : al ≤ 6)]; norm_num
      rwa [hcast, show (e₃ : ℝ) * (6 - (al : ℝ)) / 6 =
        (e₃ : ℝ) * (1 - (al : ℝ) / 6) by ring]
    · have sm := signed_move_neg_Ioo he4 x₄ 1 ((al : ℝ) / 6)
      simp only [Nat.cast_one, one_mul] at sm
      have := sm.mp t4
      have hcast : ((6 - al : ℕ) : ℝ) = 6 - (al : ℝ) := by
        rw [Nat.cast_sub (by omega : al ≤ 6)]; norm_num
      rwa [hcast, show (e₄ : ℝ) * (6 - (al : ℝ)) / 6 =
        (e₄ : ℝ) * (1 - (al : ℝ) / 6) by ring]
    · have sm := signed_move_neg_Ioo he5 x₅ 1 ((al : ℝ) / 6)
      simp only [Nat.cast_one, one_mul] at sm
      have := sm.mp t5
      have hcast : ((6 - al : ℕ) : ℝ) = 6 - (al : ℝ) := by
        rw [Nat.cast_sub (by omega : al ≤ 6)]; norm_num
      rwa [hcast, show (e₅ : ℝ) * (6 - (al : ℝ)) / 6 =
        (e₅ : ℝ) * (1 - (al : ℝ) / 6) by ring]

/-- Renault Lemma 6.2: the signed variant of Lemma 6.1 (`yᵢ = ⟨εᵢ·xᵢ⟩`);
runner 2 keeps the doubled shift `2ε₂α/6`. -/
theorem lemma6_2 {x₂ x₄ x₅ : ℝ} {e₂ e₄ e₅ : ℤ}
    (he2 : e₂ = 1 ∨ e₂ = -1) (he4 : e₄ = 1 ∨ e₄ = -1) (he5 : e₅ = 1 ∨ e₅ = -1)
    (_h2 : x₂ ∈ Set.Ico 0 1) (_h4 : x₄ ∈ Set.Ico 0 1) (_h5 : x₅ ∈ Set.Ico 0 1) :
    (∃ lam al : ℕ, 2 ≤ lam ∧ lam ≤ 5 ∧ 1 ≤ al ∧ al ≤ 5 ∧
        Int.fract ((lam : ℝ) * x₄ + (e₄ : ℝ) * (al : ℝ) / 6) ∈ Set.Icc (1 / 6) (5 / 6) ∧
        Int.fract ((lam : ℝ) * x₅ + (e₅ : ℝ) * (al : ℝ) / 6) ∈ Set.Icc (1 / 6) (5 / 6) ∧
        Int.fract ((lam : ℝ) * x₂ + 2 * (e₂ : ℝ) * (al : ℝ) / 6) ∈ Set.Icc (1 / 6) (5 / 6))
    ∨
    (∃ al : ℕ, (al = 1 ∨ al = 2 ∨ al = 3 ∨ al = 4) ∧
        Int.fract (x₄ + (e₄ : ℝ) * (al : ℝ) / 6) ∈ Set.Ioo (1 / 6) (5 / 6) ∧
        Int.fract (x₅ + (e₅ : ℝ) * (al : ℝ) / 6) ∈ Set.Ioo (1 / 6) (5 / 6) ∧
        Int.fract (x₂ + 2 * (e₂ : ℝ) * (al : ℝ) / 6) ∈ Set.Ioo (1 / 6) (5 / 6)) := by
  have hy2 : Int.fract ((e₂ : ℝ) * x₂) ∈ Set.Ico 0 1 :=
    ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
  have hy4 : Int.fract ((e₄ : ℝ) * x₄) ∈ Set.Ico 0 1 :=
    ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
  have hy5 : Int.fract ((e₅ : ℝ) * x₅) ∈ Set.Ico 0 1 :=
    ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
  rcases lemma6_1 hy2 hy4 hy5 with h | h
  · obtain ⟨lam, al, hl2, hl5, ha1, ha5, t4, t5, t2⟩ := h
    refine Or.inl ⟨lam, al, hl2, hl5, ha1, ha5, ?_, ?_, ?_⟩
    · have := (signed_move_Icc he4 x₄ lam ((al : ℝ) / 6)).mp t4
      rwa [mul_div_assoc]
    · have := (signed_move_Icc he5 x₅ lam ((al : ℝ) / 6)).mp t5
      rwa [mul_div_assoc]
    · have := (signed_move_Icc he2 x₂ lam (2 * (al : ℝ) / 6)).mp t2
      rwa [show (e₂ : ℝ) * (2 * (al : ℝ) / 6) = 2 * (e₂ : ℝ) * (al : ℝ) / 6 by ring] at this
  · obtain ⟨al, hal, t4, t5, t2⟩ := h
    refine Or.inr ⟨al, hal, ?_, ?_, ?_⟩
    · have sm := signed_move_Ioo he4 x₄ 1 ((al : ℝ) / 6)
      simp only [Nat.cast_one, one_mul] at sm
      have := sm.mp t4
      rwa [mul_div_assoc]
    · have sm := signed_move_Ioo he5 x₅ 1 ((al : ℝ) / 6)
      simp only [Nat.cast_one, one_mul] at sm
      have := sm.mp t5
      rwa [mul_div_assoc]
    · have sm := signed_move_Ioo he2 x₂ 1 (2 * (al : ℝ) / 6)
      simp only [Nat.cast_one, one_mul] at sm
      have := sm.mp t2
      rwa [show (e₂ : ℝ) * (2 * (al : ℝ) / 6) = 2 * (e₂ : ℝ) * (al : ℝ) / 6 by ring] at this

/-- Renault Lemma 6.3: the `yᵢ = ⟨−εᵢ·xᵢ⟩` variant of Lemma 6.1, producing
`6 − α` shifts (runner 2 gets `2ε₂(6−α)/6 ≡ −2ε₂α/6`). -/
theorem lemma6_3 {x₂ x₄ x₅ : ℝ} {e₂ e₄ e₅ : ℤ}
    (he2 : e₂ = 1 ∨ e₂ = -1) (he4 : e₄ = 1 ∨ e₄ = -1) (he5 : e₅ = 1 ∨ e₅ = -1)
    (_h2 : x₂ ∈ Set.Ico 0 1) (_h4 : x₄ ∈ Set.Ico 0 1) (_h5 : x₅ ∈ Set.Ico 0 1) :
    (∃ lam al : ℕ, 2 ≤ lam ∧ lam ≤ 5 ∧ 1 ≤ al ∧ al ≤ 5 ∧
        Int.fract ((lam : ℝ) * x₄ + (e₄ : ℝ) * (6 - (al : ℝ)) / 6) ∈ Set.Icc (1 / 6) (5 / 6) ∧
        Int.fract ((lam : ℝ) * x₅ + (e₅ : ℝ) * (6 - (al : ℝ)) / 6) ∈ Set.Icc (1 / 6) (5 / 6) ∧
        Int.fract ((lam : ℝ) * x₂ + 2 * (e₂ : ℝ) * (6 - (al : ℝ)) / 6) ∈ Set.Icc (1 / 6) (5 / 6))
    ∨
    (∃ al : ℕ, (al = 2 ∨ al = 3 ∨ al = 4 ∨ al = 5) ∧
        Int.fract (x₄ + (e₄ : ℝ) * (al : ℝ) / 6) ∈ Set.Ioo (1 / 6) (5 / 6) ∧
        Int.fract (x₅ + (e₅ : ℝ) * (al : ℝ) / 6) ∈ Set.Ioo (1 / 6) (5 / 6) ∧
        Int.fract (x₂ + 2 * (e₂ : ℝ) * (al : ℝ) / 6) ∈ Set.Ioo (1 / 6) (5 / 6)) := by
  have hy2 : Int.fract (-((e₂ : ℝ) * x₂)) ∈ Set.Ico 0 1 :=
    ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
  have hy4 : Int.fract (-((e₄ : ℝ) * x₄)) ∈ Set.Ico 0 1 :=
    ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
  have hy5 : Int.fract (-((e₅ : ℝ) * x₅)) ∈ Set.Ico 0 1 :=
    ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
  rcases lemma6_1 hy2 hy4 hy5 with h | h
  · obtain ⟨lam, al, hl2, hl5, ha1, ha5, t4, t5, t2⟩ := h
    refine Or.inl ⟨lam, al, hl2, hl5, ha1, ha5, ?_, ?_, ?_⟩
    · have := (signed_move_neg_Icc he4 x₄ lam ((al : ℝ) / 6)).mp t4
      rwa [show (e₄ : ℝ) * (1 - (al : ℝ) / 6) = (e₄ : ℝ) * (6 - (al : ℝ)) / 6 by ring] at this
    · have := (signed_move_neg_Icc he5 x₅ lam ((al : ℝ) / 6)).mp t5
      rwa [show (e₅ : ℝ) * (1 - (al : ℝ) / 6) = (e₅ : ℝ) * (6 - (al : ℝ)) / 6 by ring] at this
    · have h2' := (signed_move_neg_Icc he2 x₂ lam (2 * (al : ℝ) / 6)).mp t2
      -- `e₂(1 − 2α/6)` and `2e₂(6−α)/6` differ by the integer `e₂`.
      have heq : (lam : ℝ) * x₂ + 2 * (e₂ : ℝ) * (6 - (al : ℝ)) / 6 =
          (lam : ℝ) * x₂ + (e₂ : ℝ) * (1 - 2 * (al : ℝ) / 6) + ((e₂ : ℤ) : ℝ) := by
        ring
      rw [heq, Int.fract_add_intCast]
      exact h2'
  · obtain ⟨al, hal, t4, t5, t2⟩ := h
    have hal' : 6 - al = 2 ∨ 6 - al = 3 ∨ 6 - al = 4 ∨ 6 - al = 5 := by omega
    have hcast : ((6 - al : ℕ) : ℝ) = 6 - (al : ℝ) := by
      rw [Nat.cast_sub (by omega : al ≤ 6)]; norm_num
    refine Or.inr ⟨6 - al, ?_, ?_, ?_, ?_⟩
    · rcases hal' with r | r | r | r <;> omega
    · have sm := signed_move_neg_Ioo he4 x₄ 1 ((al : ℝ) / 6)
      simp only [Nat.cast_one, one_mul] at sm
      have := sm.mp t4
      rwa [hcast, show (e₄ : ℝ) * (6 - (al : ℝ)) / 6 =
        (e₄ : ℝ) * (1 - (al : ℝ) / 6) by ring]
    · have sm := signed_move_neg_Ioo he5 x₅ 1 ((al : ℝ) / 6)
      simp only [Nat.cast_one, one_mul] at sm
      have := sm.mp t5
      rwa [hcast, show (e₅ : ℝ) * (6 - (al : ℝ)) / 6 =
        (e₅ : ℝ) * (1 - (al : ℝ) / 6) by ring]
    · have sm := signed_move_neg_Ioo he2 x₂ 1 (2 * (al : ℝ) / 6)
      simp only [Nat.cast_one, one_mul] at sm
      have := sm.mp t2
      have heq : x₂ + 2 * (e₂ : ℝ) * (6 - (al : ℝ)) / 6 =
          x₂ + (e₂ : ℝ) * (1 - 2 * (al : ℝ) / 6) + ((e₂ : ℤ) : ℝ) := by
        ring
      rw [hcast, heq, Int.fract_add_intCast]
      exact this

/-- Renault Lemma 6.5: the signed variant of Lemma 6.4. -/
theorem lemma6_5 {x₃ x₄ x₅ : ℝ} {e₃ e₄ e₅ : ℤ}
    (he3 : e₃ = 1 ∨ e₃ = -1) (he4 : e₄ = 1 ∨ e₄ = -1) (he5 : e₅ = 1 ∨ e₅ = -1)
    (h3 : x₃ ∈ Set.Icc (1 / 6) (5 / 6)) (h4 : x₄ ∈ Set.Icc (1 / 6) (5 / 6))
    (h5 : x₅ ∈ Set.Icc (1 / 6) (5 / 6)) :
    (Int.fract (2 * x₃) ∈ Set.Ioo (1 / 6) (5 / 6) ∧
        Int.fract (2 * x₄) ∈ Set.Ioo (1 / 6) (5 / 6) ∧
        Int.fract (2 * x₅) ∈ Set.Ioo (1 / 6) (5 / 6))
    ∨
    (∃ al : ℕ, (al = 1 ∨ al = 5) ∧
        Int.fract (x₃ + (e₃ : ℝ) * (al : ℝ) / 6) ∈ Set.Ioo (1 / 6) (5 / 6) ∧
        Int.fract (x₄ + (e₄ : ℝ) * (al : ℝ) / 6) ∈ Set.Ioo (1 / 6) (5 / 6) ∧
        Int.fract (x₅ + (e₅ : ℝ) * (al : ℝ) / 6) ∈ Set.Ioo (1 / 6) (5 / 6))
    ∨
    (∃ lam al : ℕ, (lam = 3 ∨ lam = 5) ∧ al ≤ 5 ∧
        Int.fract ((lam : ℝ) * x₃ + (e₃ : ℝ) * (al : ℝ) / 6) ∈ Set.Icc (1 / 6) (5 / 6) ∧
        Int.fract ((lam : ℝ) * x₄ + (e₄ : ℝ) * (al : ℝ) / 6) ∈ Set.Icc (1 / 6) (5 / 6) ∧
        Int.fract ((lam : ℝ) * x₅ + (e₅ : ℝ) * (al : ℝ) / 6) ∈ Set.Icc (1 / 6) (5 / 6)) := by
  -- `⟨eᵢ·xᵢ⟩` stays in the band (the band is symmetric under `u ↦ 1 − u`).
  have band : ∀ (e : ℤ) (x : ℝ), e = 1 ∨ e = -1 →
      x ∈ Set.Icc (1 / 6) (5 / 6) → Int.fract ((e : ℝ) * x) ∈ Set.Icc (1 / 6) (5 / 6) := by
    intro e x he hx
    rcases he with rfl | rfl
    · rw [Int.cast_one, one_mul, Int.fract_eq_self.mpr]
      · exact hx
      · rw [Set.mem_Icc] at hx; constructor <;> linarith
    · rw [Int.cast_neg, Int.cast_one, neg_one_mul, fract_neg_mem_Icc]
      have hfx : Int.fract x = x := Int.fract_eq_self.mpr (by
        rw [Set.mem_Icc] at hx; constructor <;> linarith)
      rwa [hfx]
  have hy3 := band e₃ x₃ he3 h3
  have hy4 := band e₄ x₄ he4 h4
  have hy5 := band e₅ x₅ he5 h5
  rcases lemma6_4 hy3 hy4 hy5 with h | h | h
  · obtain ⟨t3, t4, t5⟩ := h
    refine Or.inl ⟨?_, ?_, ?_⟩
    · have sm := signed_move_Ioo he3 x₃ 2 0
      simp only [Nat.cast_ofNat, add_zero, mul_zero] at sm
      exact sm.mp t3
    · have sm := signed_move_Ioo he4 x₄ 2 0
      simp only [Nat.cast_ofNat, add_zero, mul_zero] at sm
      exact sm.mp t4
    · have sm := signed_move_Ioo he5 x₅ 2 0
      simp only [Nat.cast_ofNat, add_zero, mul_zero] at sm
      exact sm.mp t5
  · obtain ⟨al, hal, t3, t4, t5⟩ := h
    refine Or.inr (Or.inl ⟨al, hal, ?_, ?_, ?_⟩)
    · have sm := signed_move_Ioo he3 x₃ 1 ((al : ℝ) / 6)
      simp only [Nat.cast_one, one_mul] at sm
      have := sm.mp t3
      rwa [mul_div_assoc]
    · have sm := signed_move_Ioo he4 x₄ 1 ((al : ℝ) / 6)
      simp only [Nat.cast_one, one_mul] at sm
      have := sm.mp t4
      rwa [mul_div_assoc]
    · have sm := signed_move_Ioo he5 x₅ 1 ((al : ℝ) / 6)
      simp only [Nat.cast_one, one_mul] at sm
      have := sm.mp t5
      rwa [mul_div_assoc]
  · obtain ⟨lam, al, hlam, hle, t3, t4, t5⟩ := h
    refine Or.inr (Or.inr ⟨lam, al, hlam, hle, ?_, ?_, ?_⟩)
    · have := (signed_move_Icc he3 x₃ lam ((al : ℝ) / 6)).mp t3
      rwa [mul_div_assoc]
    · have := (signed_move_Icc he4 x₄ lam ((al : ℝ) / 6)).mp t4
      rwa [mul_div_assoc]
    · have := (signed_move_Icc he5 x₅ lam ((al : ℝ) / 6)).mp t5
      rwa [mul_div_assoc]

end
