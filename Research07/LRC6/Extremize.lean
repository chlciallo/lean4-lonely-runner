/-
Copyright (c) 2026 Research07 contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Research07 contributors
-/
import Mathlib
import Research07.LRC6.Setup

/-!
# extremization machinery for the `n = 6` Renault argument

`forward_endpoint6`/`backward_endpoint6` generalize the `LRC4` endpoint lemmas
from two guard runners to an arbitrary nonempty guard finset: from a time where
every guard is safe, push forward (resp. backward) to the first `5/6`-exit
(resp. `1/6`-exit); all guards stay safe and `off a` does not decrease
(resp. increase).  The maximal `off a` over the finite boundary union is then
attained at an explicit candidate — Renault's `tstar`.
-/

noncomputable section

open Int

/-- Forward endpoint: from a time where all `guards` are safe, push forward to
the first `5/6`-exit; the exit time is in `topBdry6 d` for some `d ∈ guards`,
all guards remain safe, and `off a` does not decrease. -/
theorem forward_endpoint6 (guards : Finset ℕ) (hguards : guards.Nonempty)
    (hpos : ∀ d ∈ guards, 0 < d) {a : ℕ} (ha : 0 < a)
    (hns : ∀ t : ℝ, (∀ d ∈ guards, fract ((d : ℝ) * t) ∈ Set.Icc (1 / 6) (5 / 6)) →
      |off a t| < 1 / 6)
    {t : ℝ} (hsafe : ∀ d ∈ guards, fract ((d : ℝ) * t) ∈ Set.Icc (1 / 6) (5 / 6)) :
    ∃ β : ℝ, (∃ d ∈ guards, β ∈ topBdry6 d)
      ∧ (∀ d ∈ guards, fract ((d : ℝ) * β) ∈ Set.Icc (1 / 6) (5 / 6))
      ∧ off a t ≤ off a β := by
  have ha' : (0 : ℝ) < a := Nat.cast_pos.mpr ha
  classical
  -- headroom of runner `d`: time until its position reaches `5/6`
  set hr : ℕ → ℝ := fun d => (5 / 6 - fract ((d : ℝ) * t)) / (d : ℝ) with hhr
  obtain ⟨d₀, hd₀mem, hd₀min⟩ :=
    guards.exists_min_image hr hguards
  set δ := hr d₀ with hδ_def
  have hd₀pos : (0 : ℝ) < d₀ := Nat.cast_pos.mpr (hpos d₀ hd₀mem)
  -- for every guard, `d·δ ≤ 5/6 − x_d`
  have hle : ∀ d ∈ guards, (d : ℝ) * δ ≤ 5 / 6 - fract ((d : ℝ) * t) := by
    intro d hd
    have hdpos : (0 : ℝ) < d := Nat.cast_pos.mpr (hpos d hd)
    have hδle : δ ≤ hr d := hd₀min d hd
    calc (d : ℝ) * δ ≤ d * hr d := by gcongr
      _ = 5 / 6 - fract ((d : ℝ) * t) := by rw [hhr]; field_simp
  have hδ0 : 0 ≤ δ := by
    rw [hδ_def, hhr]
    apply div_nonneg _ hd₀pos.le
    have := (hsafe d₀ hd₀mem).2
    linarith
  -- positions stay safe along `[t, t+δ]`
  have hseg : ∀ s : ℝ, 0 ≤ s → s ≤ δ →
      ∀ d ∈ guards, fract ((d : ℝ) * (t + s)) ∈ Set.Icc (1 / 6) (5 / 6) := by
    intro s hs0 hsδ d hd
    have hdpos : (0 : ℝ) < d := Nat.cast_pos.mpr (hpos d hd)
    have h2 : (d : ℝ) * s ≤ (d : ℝ) * δ := mul_le_mul_of_nonneg_left hsδ hdpos.le
    have h3 : 0 ≤ (d : ℝ) * s := mul_nonneg hdpos.le hs0
    have h1 : fract ((d : ℝ) * (t + s)) = fract ((d : ℝ) * t) + (d : ℝ) * s := by
      rw [fract_add_shift, fract_eq_self]
      refine ⟨by have h4 := (hsafe d hd).1; linarith,
              by have h5 := hle d hd; linarith⟩
    rw [h1]
    refine ⟨by have h4 := (hsafe d hd).1; linarith,
            by have h5 := hle d hd; linarith⟩
  -- `off a` increases by `a·δ` along the segment
  have hoff : off a (t + δ) = off a t + (a : ℝ) * δ := by
    have hoff0 := hns t hsafe
    rw [abs_lt] at hoff0
    set n₀ := round ((a : ℝ) * t) with hn₀
    have hat : (a : ℝ) * t = (n₀ : ℝ) + off a t := by
      rw [off]; linarith
    have hub : (a : ℝ) * δ < 1 / 6 - off a t := by
      by_contra hcon
      have hcon' : (1 / 6 - off a t) ≤ (a : ℝ) * δ := le_of_not_gt hcon
      set s' := (1 / 6 - off a t) / (a : ℝ) with hs'
      have hs'0 : 0 < s' := div_pos (by linarith [hoff0.2]) ha'
      have hs'δ : s' ≤ δ := by
        rw [hs', div_le_iff₀ ha']
        linarith [hcon']
      have h1 : (a : ℝ) * (t + s') = (n₀ : ℝ) + 1 / 6 := by
        have hs'' : (a : ℝ) * s' = 1 / 6 - off a t := by
          rw [hs']; field_simp
        have hexp : (a : ℝ) * (t + s') = (a : ℝ) * t + (a : ℝ) * s' := by ring
        rw [hexp]; linarith [hat]
      have h2 := hns (t + s') (hseg s' hs'0.le hs'δ)
      have h3 : off a (t + s') = 1 / 6 := by
        rw [off, h1]
        rw [round_of_sixth (by norm_num : (-1 / 2 : ℝ) ≤ 1 / 6)
          (by norm_num : (1 / 6 : ℝ) < 1 / 2)]
        push_cast; ring
      rw [h3] at h2
      norm_num at h2
    have hrnd : round ((a : ℝ) * (t + δ)) = n₀ := by
      have h1 : (a : ℝ) * (t + δ) = (n₀ : ℝ) + (off a t + (a : ℝ) * δ) := by
        have hexp : (a : ℝ) * (t + δ) = (a : ℝ) * t + (a : ℝ) * δ := by ring
        rw [hexp]; linarith [hat]
      rw [h1]
      apply round_of_sixth
      · linarith [hoff0.1, mul_nonneg ha'.le hδ0]
      · linarith [hub]
    rw [off, off, hrnd]
    have hexp : (a : ℝ) * (t + δ) = (a : ℝ) * t + (a : ℝ) * δ := by ring
    rw [hexp]
    show (a : ℝ) * t + (a : ℝ) * δ - ↑n₀ = ((a : ℝ) * t - ↑n₀) + (a : ℝ) * δ
    ring
  -- the exit runner `d₀` sits at `5/6`
  have hxd₀ : fract ((d₀ : ℝ) * (t + δ)) = 5 / 6 := by
    have h1 : fract ((d₀ : ℝ) * (t + δ)) =
        fract ((d₀ : ℝ) * t) + (d₀ : ℝ) * δ := by
      rw [fract_add_shift, fract_eq_self]
      have h3 := (hsafe d₀ hd₀mem).1
      have h4 := mul_nonneg hd₀pos.le hδ0
      have h5 := hle d₀ hd₀mem
      refine ⟨by linarith, by linarith⟩
    have h2 : (d₀ : ℝ) * δ = 5 / 6 - fract ((d₀ : ℝ) * t) := by
      rw [hδ_def, hhr]; field_simp
    rw [h1]; linarith
  refine ⟨fract (t + δ), ?_, ?_, ?_⟩
  · refine ⟨d₀, hd₀mem, ?_⟩
    refine fract_mem_topBdry6 (hpos d₀ hd₀mem) (l := ⌊(d₀ : ℝ) * (t + δ)⌋) ?_
    have h := Int.self_sub_floor ((d₀ : ℝ) * (t + δ))
    linarith [hxd₀]
  · intro d hd
    have hdpos : (0 : ℝ) < d := Nat.cast_pos.mpr (hpos d hd)
    have h : (d : ℝ) * fract (t + δ) =
        (d : ℝ) * (t + δ) + ((- (d : ℤ) * ⌊t + δ⌋ : ℤ) : ℝ) := by
      have hsf := (Int.self_sub_floor (t + δ)).symm
      push_cast
      linear_combination (d : ℝ) * hsf
    have hdδ : fract ((d : ℝ) * (t + δ)) ∈ Set.Icc (1 / 6) (5 / 6) :=
      hseg δ hδ0 (le_refl δ) d hd
    rw [h, fract_add_intCast]
    exact hdδ
  · rw [off_fract, hoff]
    have : 0 ≤ (a : ℝ) * δ := mul_nonneg ha'.le hδ0
    linarith

/-- Backward endpoint: from a time where all `guards` are safe, push backward to
the first `1/6`-exit; the exit time is in `botBdry6 d` for some `d ∈ guards`,
all guards remain safe, and `off a` does not increase. -/
theorem backward_endpoint6 (guards : Finset ℕ) (hguards : guards.Nonempty)
    (hpos : ∀ d ∈ guards, 0 < d) {a : ℕ} (ha : 0 < a)
    (hns : ∀ t : ℝ, (∀ d ∈ guards, fract ((d : ℝ) * t) ∈ Set.Icc (1 / 6) (5 / 6)) →
      |off a t| < 1 / 6)
    {t : ℝ} (hsafe : ∀ d ∈ guards, fract ((d : ℝ) * t) ∈ Set.Icc (1 / 6) (5 / 6)) :
    ∃ β : ℝ, (∃ d ∈ guards, β ∈ botBdry6 d)
      ∧ (∀ d ∈ guards, fract ((d : ℝ) * β) ∈ Set.Icc (1 / 6) (5 / 6))
      ∧ off a β ≤ off a t := by
  have ha' : (0 : ℝ) < a := Nat.cast_pos.mpr ha
  classical
  -- headroom going backward: time until position reaches `1/6`
  set hr : ℕ → ℝ := fun d => (fract ((d : ℝ) * t) - 1 / 6) / (d : ℝ) with hhr
  obtain ⟨d₀, hd₀mem, hd₀min⟩ :=
    guards.exists_min_image hr hguards
  set δ := hr d₀ with hδ_def
  have hd₀pos : (0 : ℝ) < d₀ := Nat.cast_pos.mpr (hpos d₀ hd₀mem)
  -- for every guard, `d·δ ≤ x_d − 1/6` (backward headroom)
  have hle : ∀ d ∈ guards, (d : ℝ) * δ ≤ fract ((d : ℝ) * t) - 1 / 6 := by
    intro d hd
    have hdpos : (0 : ℝ) < d := Nat.cast_pos.mpr (hpos d hd)
    have hδle : δ ≤ hr d := hd₀min d hd
    calc (d : ℝ) * δ ≤ d * hr d := by gcongr
      _ = fract ((d : ℝ) * t) - 1 / 6 := by rw [hhr]; field_simp
  have hδ0 : 0 ≤ δ := by
    rw [hδ_def, hhr]
    apply div_nonneg _ hd₀pos.le
    have := (hsafe d₀ hd₀mem).1
    linarith
  -- positions stay safe along `[t − δ, t]`
  have hseg : ∀ s : ℝ, 0 ≤ s → s ≤ δ →
      ∀ d ∈ guards, fract ((d : ℝ) * (t - s)) ∈ Set.Icc (1 / 6) (5 / 6) := by
    intro s hs0 hsδ d hd
    have hdpos : (0 : ℝ) < d := Nat.cast_pos.mpr (hpos d hd)
    have h2 : (d : ℝ) * s ≤ (d : ℝ) * δ := mul_le_mul_of_nonneg_left hsδ hdpos.le
    have h3 : 0 ≤ (d : ℝ) * s := mul_nonneg hdpos.le hs0
    have h1 : fract ((d : ℝ) * (t - s)) =
        fract ((d : ℝ) * t) - (d : ℝ) * s := by
      have hh : fract ((d : ℝ) * (t - s)) =
          fract (fract ((d : ℝ) * t) - (d : ℝ) * s) := by
        have h := fract_add_shift d t (-s)
        rw [← sub_eq_add_neg, mul_neg, ← sub_eq_add_neg] at h
        exact h
      rw [hh, fract_eq_self]
      have h4 := (hsafe d hd).1
      have h5 := (hsafe d hd).2
      have h6 := mul_nonneg hdpos.le hδ0
      have h7 := hle d hd
      refine ⟨by linarith, by linarith⟩
    rw [h1]
    have h4 := (hsafe d hd).1
    have h5 := (hsafe d hd).2
    have h6 := mul_nonneg hdpos.le hδ0
    have h7 := hle d hd
    refine ⟨by linarith, by linarith⟩
  -- `off a` decreases by `a·δ` backward
  have hoff : off a (t - δ) = off a t - (a : ℝ) * δ := by
    have hoff0 := hns t hsafe
    rw [abs_lt] at hoff0
    set n₀ := round ((a : ℝ) * t) with hn₀
    have hat : (a : ℝ) * t = (n₀ : ℝ) + off a t := by
      rw [off]; linarith
    have hlb : (a : ℝ) * δ < off a t + 1 / 6 := by
      by_contra hcon
      have hcon' : off a t + 1 / 6 ≤ (a : ℝ) * δ := le_of_not_gt hcon
      set s' := (off a t + 1 / 6) / (a : ℝ) with hs'
      have hs'0 : 0 < s' := div_pos (by linarith [hoff0.1]) ha'
      have hs'δ : s' ≤ δ := by
        rw [hs', div_le_iff₀ ha']
        linarith [hcon']
      have h1 : (a : ℝ) * (t - s') = (n₀ : ℝ) - 1 / 6 := by
        have hs'' : (a : ℝ) * s' = off a t + 1 / 6 := by
          rw [hs']; field_simp
        have hexp : (a : ℝ) * (t - s') = (a : ℝ) * t - (a : ℝ) * s' := by ring
        rw [hexp]; linarith [hat]
      have h2 := hns (t - s') (hseg s' hs'0.le hs'δ)
      have h3 : off a (t - s') = -1 / 6 := by
        rw [off, h1]
        have hr : round ((n₀ : ℝ) - 1 / 6) = n₀ := by
          rw [show (n₀ : ℝ) - 1 / 6 = (n₀ : ℝ) + (-1 / 6 : ℝ) by ring]
          exact round_of_sixth (by norm_num) (by norm_num)
        rw [hr]
        push_cast; ring
      rw [h3] at h2
      norm_num at h2
    have hrnd : round ((a : ℝ) * (t - δ)) = n₀ := by
      have h1 : (a : ℝ) * (t - δ) = (n₀ : ℝ) + (off a t - (a : ℝ) * δ) := by
        have hexp : (a : ℝ) * (t - δ) = (a : ℝ) * t - (a : ℝ) * δ := by ring
        rw [hexp]; linarith [hat]
      rw [h1]
      apply round_of_sixth
      · linarith [hlb, hoff0.1]
      · linarith [hoff0.2, mul_nonneg ha'.le hδ0]
    rw [off, off, hrnd]
    have hexp : (a : ℝ) * (t - δ) = (a : ℝ) * t - (a : ℝ) * δ := by ring
    rw [hexp]
    show (a : ℝ) * t - (a : ℝ) * δ - ↑n₀ = ((a : ℝ) * t - ↑n₀) - (a : ℝ) * δ
    ring
  -- the exit runner `d₀` sits at `1/6`
  have hxd₀ : fract ((d₀ : ℝ) * (t - δ)) = 1 / 6 := by
    have h1 : fract ((d₀ : ℝ) * (t - δ)) =
        fract ((d₀ : ℝ) * t) - (d₀ : ℝ) * δ := by
      have hh : fract ((d₀ : ℝ) * (t - δ)) =
          fract (fract ((d₀ : ℝ) * t) - (d₀ : ℝ) * δ) := by
        have h := fract_add_shift d₀ t (-δ)
        rw [← sub_eq_add_neg, mul_neg, ← sub_eq_add_neg] at h
        exact h
      rw [hh, fract_eq_self]
      have h3 := (hsafe d₀ hd₀mem).1
      have h5 := (hsafe d₀ hd₀mem).2
      have h6 := mul_nonneg hd₀pos.le hδ0
      have h7 := hle d₀ hd₀mem
      refine ⟨by linarith, by linarith⟩
    have h2 : (d₀ : ℝ) * δ = fract ((d₀ : ℝ) * t) - 1 / 6 := by
      rw [hδ_def, hhr]; field_simp
    rw [h1]; linarith
  refine ⟨fract (t - δ), ?_, ?_, ?_⟩
  · refine ⟨d₀, hd₀mem, ?_⟩
    refine fract_mem_botBdry6 (hpos d₀ hd₀mem) (l := ⌊(d₀ : ℝ) * (t - δ)⌋) ?_
    have h := Int.self_sub_floor ((d₀ : ℝ) * (t - δ))
    linarith [hxd₀]
  · intro d hd
    have hdpos : (0 : ℝ) < d := Nat.cast_pos.mpr (hpos d hd)
    have h : (d : ℝ) * fract (t - δ) =
        (d : ℝ) * (t - δ) + ((- (d : ℤ) * ⌊t - δ⌋ : ℤ) : ℝ) := by
      have hsf := (Int.self_sub_floor (t - δ)).symm
      push_cast
      linear_combination (d : ℝ) * hsf
    have hdδ : fract ((d : ℝ) * (t - δ)) ∈ Set.Icc (1 / 6) (5 / 6) :=
      hseg δ hδ0 (le_refl δ) d hd
    rw [h, fract_add_intCast]
    exact hdδ
  · rw [off_fract, hoff]
    have : 0 ≤ (a : ℝ) * δ := mul_nonneg ha'.le hδ0
    linarith

/-- There is a positive `ε` with `d·ε < B` for every `d` in a nonempty
positive finset. -/
theorem exists_pos_forall_mul_lt (guards : Finset ℕ) (hg : guards.Nonempty)
    (hpos : ∀ d ∈ guards, 0 < d) {B : ℝ} (hB : 0 < B) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ d ∈ guards, (d : ℝ) * ε < B := by
  obtain ⟨M, hMmem, hMmax⟩ := guards.exists_max_image (fun d => (d : ℝ)) hg
  have hMpos : (0 : ℝ) < M := Nat.cast_pos.mpr (hpos M hMmem)
  refine ⟨B / (2 * (M : ℝ)), by positivity, fun d hd => ?_⟩
  have hdle : (d : ℝ) ≤ (M : ℝ) := hMmax d hd
  calc (d : ℝ) * (B / (2 * (M : ℝ))) ≤ M * (B / (2 * (M : ℝ))) := by gcongr
    _ = B / 2 := by field_simp
    _ < B := by linarith

/-- From a `fract`-maximizer on `fract < 1/6` (plus the no-safe-time hypothesis
`hns`), derive the global `circ`-maximality `N(x₁)` used by Renault. -/
theorem circ_max_of_fract_max (guards : Finset ℕ) {a : ℕ} {tstar : ℝ}
    (hns : ∀ t : ℝ, (∀ d ∈ guards, fract ((d : ℝ) * t) ∈ Set.Icc (1 / 6) (5 / 6)) →
      |off a t| < 1 / 6)
    (hlt : fract ((a : ℝ) * tstar) < 1 / 6)
    (hmax : ∀ t : ℝ, (∀ d ∈ guards, fract ((d : ℝ) * t) ∈ Set.Icc (1 / 6) (5 / 6)) →
      fract ((a : ℝ) * t) < 1 / 6 → fract ((a : ℝ) * t) ≤ fract ((a : ℝ) * tstar)) :
    ∀ s : ℝ, (∀ d ∈ guards, fract ((d : ℝ) * s) ∈ Set.Icc (1 / 6) (5 / 6)) →
      circ ((a : ℝ) * s) ≤ circ ((a : ℝ) * tstar) := by
  intro s hs
  have hcT : circ ((a : ℝ) * tstar) = fract ((a : ℝ) * tstar) := by
    rw [circ_eq, abs_sub_round_eq_min]
    exact min_eq_left (by linarith [Int.fract_lt_one ((a : ℝ) * tstar)])
  rw [hcT, circ_eq, abs_sub_round_eq_min]
  rcases lt_or_ge (fract ((a : ℝ) * s)) (1 / 6) with hlt' | hge'
  · rw [min_eq_left (by linarith [Int.fract_lt_one ((a : ℝ) * s)])]
    exact hmax s hs hlt'
  · -- `fract ≥ 1/6`: `hns` forces `circ < 1/6`, hence `fract > 5/6`; reflect `-s`
    have hbound := hns s hs
    rw [abs_off] at hbound
    rw [circ_eq, abs_sub_round_eq_min] at hbound
    have hgt : 5 / 6 < fract ((a : ℝ) * s) := by
      rcases min_lt_iff.mp hbound with h1 | h1
      · linarith
      · linarith
    have hsn : ∀ d ∈ guards, fract ((d : ℝ) * (-s)) ∈ Set.Icc (1 / 6) (5 / 6) := by
      intro d hd
      obtain ⟨hl, hh⟩ := hs d hd
      have h2 : (d : ℝ) * (-s) = -((d : ℝ) * s) := by ring
      have hz : fract ((d : ℝ) * s) ≠ 0 := by
        intro hz; rw [hz] at hl; norm_num at hl
      rw [h2, Int.fract_neg hz]
      exact ⟨by linarith, by linarith⟩
    have hfn : fract ((a : ℝ) * (-s)) = 1 - fract ((a : ℝ) * s) := by
      have h2 : (a : ℝ) * (-s) = -((a : ℝ) * s) := by ring
      have hz : fract ((a : ℝ) * s) ≠ 0 := by intro hz; rw [hz] at hgt; norm_num at hgt
      rw [h2, Int.fract_neg hz]
    have hle := hmax (-s) hsn (by rw [hfn]; linarith)
    rw [min_eq_right (by linarith)]
    linarith

/-- The Renault `n = 6` maximizer `tstar` (near-zero branch).

Under `hns` (no time makes `a` and all `guards` safe) and a `lrc5_int`-style
seed making all guards `1/5`-safe, produce a time `tstar` where all guards are
`1/6`-safe, `0 < x_a(tstar) < 1/6`, `x_a` is maximal among guard-safe times, and
some guard sits at the top boundary `5/6`. -/
theorem renault6_maximize (guards : Finset ℕ) (hguards : guards.Nonempty)
    (hpos : ∀ d ∈ guards, 0 < d) {a : ℕ} (ha : 0 < a)
    (hns : ∀ t : ℝ, (∀ d ∈ guards, fract ((d : ℝ) * t) ∈ Set.Icc (1 / 6) (5 / 6)) →
      |off a t| < 1 / 6)
    (hseed : ∃ τ : ℝ, ∀ d ∈ guards, (1 / 5 : ℝ) ≤ circ (τ * d)) :
    ∃ tstar : ℝ, (∀ d ∈ guards, fract ((d : ℝ) * tstar) ∈ Set.Icc (1 / 6) (5 / 6))
      ∧ (0 < fract ((a : ℝ) * tstar)) ∧ (fract ((a : ℝ) * tstar) < 1 / 6)
      ∧ (∀ t : ℝ, (∀ d ∈ guards, fract ((d : ℝ) * t) ∈ Set.Icc (1 / 6) (5 / 6)) →
          fract ((a : ℝ) * t) < 1 / 6 → fract ((a : ℝ) * t) ≤ fract ((a : ℝ) * tstar))
      ∧ (∀ s : ℝ, (∀ d ∈ guards, fract ((d : ℝ) * s) ∈ Set.Icc (1 / 6) (5 / 6)) →
          circ ((a : ℝ) * s) ≤ circ ((a : ℝ) * tstar))
      ∧ (∃ d₀ ∈ guards, fract ((d₀ : ℝ) * tstar) = 5 / 6) := by
  classical
  have ha' : (0 : ℝ) < a := Nat.cast_pos.mpr ha
  obtain ⟨τ₀, hτ₀⟩ := hseed
  -- the seed's guards lie strictly inside `(1/6, 5/6)` with margin `1/30`
  have hτsafe : ∀ d ∈ guards, fract ((d : ℝ) * τ₀) ∈ Set.Icc (1 / 6) (5 / 6) := by
    intro d hd
    rw [mul_comm (d : ℝ) τ₀]
    have h := circ_ge_fifth_fract (τ₀ * (d : ℝ)) |>.mp (hτ₀ d hd)
    obtain ⟨h1, h2⟩ := Set.mem_Icc.mp h
    exact Set.mem_Icc.mpr ⟨by linarith, by linarith⟩
  -- the seed's `1/5`-margin: `fract ∈ [1/5, 4/5]` leaves room `1/30` to `5/6`
  have hτstrict : ∀ d ∈ guards,
      (1 / 5 : ℝ) ≤ fract ((d : ℝ) * τ₀) ∧ fract ((d : ℝ) * τ₀) ≤ 4 / 5 := by
    intro d hd
    rw [mul_comm (d : ℝ) τ₀]
    have h := circ_ge_fifth_fract (τ₀ * (d : ℝ)) |>.mp (hτ₀ d hd)
    exact Set.mem_Icc.mp h
  -- a seed with `off a ≠ 0`
  have seed_or :
      (∃ t : ℝ, (∀ d ∈ guards, fract ((d : ℝ) * t) ∈ Set.Icc (1 / 6) (5 / 6))
        ∧ 0 < off a t) ∨
      (∃ t : ℝ, (∀ d ∈ guards, fract ((d : ℝ) * t) ∈ Set.Icc (1 / 6) (5 / 6))
        ∧ off a t < 0) := by
    rcases lt_trichotomy (off a τ₀) 0 with hoff | hoff | hoff
    · exact Or.inr ⟨τ₀, hτsafe, hoff⟩
    · -- `off a τ₀ = 0`: perturb to `τ₀ + ε₁`, which keeps guards safe and has
      -- `off a = a·ε₁ > 0` since `a·τ₀` is an integer.
      left
      obtain ⟨M, hMmem, hMmax⟩ := guards.exists_max_image (fun d => (d : ℝ)) hguards
      have hMpos : (0 : ℝ) < M := Nat.cast_pos.mpr (hpos M hMmem)
      set ε₁ : ℝ := min (1 / (60 * (M : ℝ))) (1 / (4 * (a : ℝ))) with hε₁def
      have hε₁ : 0 < ε₁ := by rw [hε₁def]; refine lt_min ?_ ?_ <;> positivity
      have hεg : ∀ d ∈ guards, (d : ℝ) * ε₁ < 1 / 30 := by
        intro d hd
        have hdle : (d : ℝ) ≤ (M : ℝ) := hMmax d hd
        have hdpos : (0 : ℝ) < d := Nat.cast_pos.mpr (hpos d hd)
        have hεle : ε₁ ≤ 1 / (60 * (M : ℝ)) := by rw [hε₁def]; exact min_le_left _ _
        calc (d : ℝ) * ε₁ ≤ (M : ℝ) * ε₁ := by gcongr
          _ ≤ M * (1 / (60 * M)) := by gcongr
          _ = 1 / 60 := by field_simp
          _ < 1 / 30 := by norm_num
      have hεa : (a : ℝ) * ε₁ < 1 / 2 := by
        have hεle : ε₁ ≤ 1 / (4 * (a : ℝ)) := by rw [hε₁def]; exact min_le_right _ _
        calc (a : ℝ) * ε₁ ≤ a * (1 / (4 * a)) := by gcongr
          _ = 1 / 4 := by field_simp
          _ < 1 / 2 := by norm_num
      have hguard : ∀ d ∈ guards, fract ((d : ℝ) * (τ₀ + ε₁)) ∈ Set.Icc (1 / 6) (5 / 6) := by
        intro d hd
        obtain ⟨hlo, hhi⟩ := hτstrict d hd
        have hdpos : (0 : ℝ) < d := Nat.cast_pos.mpr (hpos d hd)
        have hε := hεg d hd
        have hε0 : 0 ≤ (d : ℝ) * ε₁ := mul_nonneg hdpos.le hε₁.le
        have h1 : fract ((d : ℝ) * (τ₀ + ε₁)) = fract ((d : ℝ) * τ₀) + (d : ℝ) * ε₁ := by
          rw [fract_add_shift]
          exact Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
        rw [h1]
        exact ⟨by linarith, by linarith⟩
      have hoff' : 0 < off a (τ₀ + ε₁) := by
        have h0 : (a : ℝ) * τ₀ = (round ((a : ℝ) * τ₀) : ℝ) := by
          rw [off, sub_eq_zero] at hoff
          exact hoff
        have hmul : (a : ℝ) * (τ₀ + ε₁) =
            (round ((a : ℝ) * τ₀) : ℝ) + (a : ℝ) * ε₁ := by
          rw [← h0]; ring
        have hround : round ((a : ℝ) * (τ₀ + ε₁)) = round ((a : ℝ) * τ₀) := by
          rw [hmul]
          apply round_of_sixth
          · linarith [mul_pos ha' hε₁]
          · linarith [hεa]
        rw [off, hround, hmul]
        linarith [mul_pos ha' hε₁]
      exact ⟨τ₀ + ε₁, hguard, hoff'⟩
    · exact Or.inl ⟨τ₀, hτsafe, hoff⟩
  rcases seed_or with ⟨ts, hts, hoff⟩ | ⟨ts, hts, hoff⟩
  · -- positive seed: maximize `off a` over the top-boundary union
    set Ftop : Finset ℝ := (guards.biUnion topBdry6).filter fun β =>
        (∀ d ∈ guards, fract ((d : ℝ) * β) ∈ Set.Icc (1 / 6) (5 / 6)) ∧
          0 < off a β with hFtopdef
    obtain ⟨β₀, hβ₀bd, hβ₀safe, hβ₀le⟩ :=
      forward_endpoint6 guards hguards hpos ha hns hts
    have hFne : Ftop.Nonempty := by
      refine ⟨β₀, ?_⟩
      rw [hFtopdef, Finset.mem_filter]
      obtain ⟨d₀, hd₀mem, hd₀bd⟩ := hβ₀bd
      exact ⟨Finset.mem_biUnion.mpr ⟨d₀, hd₀mem, hd₀bd⟩, hβ₀safe,
             lt_of_lt_of_le hoff hβ₀le⟩
    obtain ⟨tstar, htstarmem, htstarmax⟩ := Ftop.exists_max_image (off a) hFne
    rw [hFtopdef, Finset.mem_filter] at htstarmem
    obtain ⟨htstarbd, htstarsafe, htstarpos⟩ := htstarmem
    have htstaralt : off a tstar < 1 / 6 := by
      have h := hns tstar htstarsafe
      rwa [abs_of_pos htstarpos] at h
    have hfa : fract ((a : ℝ) * tstar) = off a tstar := fract_eq_off htstarpos.le
    have hmax : ∀ t : ℝ, (∀ d ∈ guards, fract ((d : ℝ) * t) ∈ Set.Icc (1 / 6) (5 / 6)) →
        fract ((a : ℝ) * t) < 1 / 6 → fract ((a : ℝ) * t) ≤ fract ((a : ℝ) * tstar) := by
      intro t hut hat
      rcases lt_trichotomy (off a t) 0 with hneg | hz | hgt
      · rw [fract_eq_one_add_off hneg] at hat
        have hbound := hns t hut
        rw [abs_of_neg hneg] at hbound
        linarith
      · have hz' : fract ((a : ℝ) * t) = 0 := by
          have h2 : (a : ℝ) * t = (round ((a : ℝ) * t) : ℝ) := by
            rw [off, sub_eq_zero] at hz
            exact hz
          rw [h2]
          simp
        rw [hz']
        linarith [htstarpos]
      · obtain ⟨β, hβbd, hβsafe, hβle⟩ := forward_endpoint6 guards hguards hpos ha hns hut
        have hβF : β ∈ Ftop := by
          rw [hFtopdef, Finset.mem_filter]
          obtain ⟨d₀, hd₀mem, hd₀bd⟩ := hβbd
          exact ⟨Finset.mem_biUnion.mpr ⟨d₀, hd₀mem, hd₀bd⟩, hβsafe,
                 lt_of_lt_of_le hgt hβle⟩
        have hβmax := htstarmax β hβF
        rw [hfa, fract_eq_off hgt.le]
        exact hβle.trans hβmax
    obtain ⟨d₀, hd₀mem, hd₀bd⟩ := Finset.mem_biUnion.mp htstarbd
    refine ⟨tstar, htstarsafe, by rw [hfa]; exact htstarpos, by rw [hfa]; exact htstaralt, hmax,
            circ_max_of_fract_max guards hns (by rw [hfa]; exact htstaralt) hmax,
            ⟨d₀, hd₀mem, ?_⟩⟩
    obtain ⟨l, -, rfl⟩ := Finset.mem_image.mp hd₀bd
    exact topBdry6_pos (hpos d₀ hd₀mem)
  · -- negative seed: minimize `off a` over the bottom-boundary union, reflect
    set Fbot : Finset ℝ := (guards.biUnion botBdry6).filter fun β =>
        (∀ d ∈ guards, fract ((d : ℝ) * β) ∈ Set.Icc (1 / 6) (5 / 6)) ∧
          off a β < 0 with hFbotdef
    obtain ⟨γ₀, hγ₀bd, hγ₀safe, hγ₀le⟩ :=
      backward_endpoint6 guards hguards hpos ha hns hts
    have hFne : Fbot.Nonempty := by
      refine ⟨γ₀, ?_⟩
      rw [hFbotdef, Finset.mem_filter]
      obtain ⟨d₀, hd₀mem, hd₀bd⟩ := hγ₀bd
      exact ⟨Finset.mem_biUnion.mpr ⟨d₀, hd₀mem, hd₀bd⟩, hγ₀safe,
             hγ₀le.trans_lt hoff⟩
    obtain ⟨t₁, ht₁mem, ht₁min⟩ := Fbot.exists_max_image (fun β => -off a β) hFne
    rw [hFbotdef, Finset.mem_filter] at ht₁mem
    obtain ⟨ht₁bd, ht₁safe, ht₁neg⟩ := ht₁mem
    have hfa1 : fract ((a : ℝ) * t₁) = 1 + off a t₁ := fract_eq_one_add_off ht₁neg
    have hoff1 : -off a t₁ < 1 / 6 := by
      have h := hns t₁ ht₁safe
      rwa [abs_of_neg ht₁neg] at h
    set s₀ := -t₁ with hs₀def
    have hfa : fract ((a : ℝ) * s₀) = -off a t₁ := by
      have h2 : (a : ℝ) * s₀ = -((a : ℝ) * t₁) := by rw [hs₀def]; ring
      rw [h2, fract_neg (by rw [hfa1]; linarith [hoff1]), hfa1]
      ring
    -- reflected guards are still safe
    have hs₀safe : ∀ d ∈ guards, fract ((d : ℝ) * s₀) ∈ Set.Icc (1 / 6) (5 / 6) := by
      intro d hd
      have hdT := ht₁safe d hd
      obtain ⟨hl, hh⟩ := hdT
      have h2 : (d : ℝ) * s₀ = -((d : ℝ) * t₁) := by rw [hs₀def]; ring
      have hz : fract ((d : ℝ) * t₁) ≠ 0 := by
        intro hz; rw [hz] at hl; norm_num at hl
      rw [h2, fract_neg hz]
      exact ⟨by linarith, by linarith⟩
    have hmax : ∀ t : ℝ, (∀ d ∈ guards, fract ((d : ℝ) * t) ∈ Set.Icc (1 / 6) (5 / 6)) →
        fract ((a : ℝ) * t) < 1 / 6 → fract ((a : ℝ) * t) ≤ fract ((a : ℝ) * s₀) := by
      intro t hut hat
      rcases lt_trichotomy (off a t) 0 with hneg | hz | hgt
      · rw [fract_eq_one_add_off hneg] at hat
        have hbound := hns t hut
        rw [abs_of_neg hneg] at hbound
        linarith
      · have hz' : fract ((a : ℝ) * t) = 0 := by
          have h2 : (a : ℝ) * t = (round ((a : ℝ) * t) : ℝ) := by
            rw [off, sub_eq_zero] at hz
            exact hz
          rw [h2]
          simp
        rw [hz']
        exact Int.fract_nonneg _
      · have hutn : ∀ d ∈ guards, fract ((d : ℝ) * (-t)) ∈ Set.Icc (1 / 6) (5 / 6) := by
          intro d hd
          obtain ⟨hl, hh⟩ := hut d hd
          have h2 : (d : ℝ) * (-t) = -((d : ℝ) * t) := by ring
          have hz : fract ((d : ℝ) * t) ≠ 0 := by
            intro hz; rw [hz] at hl; norm_num at hl
          rw [h2, fract_neg hz]
          exact ⟨by linarith, by linarith⟩
        obtain ⟨γ, hγbd, hγsafe, hγle⟩ := backward_endpoint6 guards hguards hpos ha hns hutn
        rw [off_neg (by linarith [hns t hut])] at hγle
        have hγF : γ ∈ Fbot := by
          rw [hFbotdef, Finset.mem_filter]
          obtain ⟨d₀, hd₀mem, hd₀bd⟩ := hγbd
          exact ⟨Finset.mem_biUnion.mpr ⟨d₀, hd₀mem, hd₀bd⟩, hγsafe, by linarith [hgt]⟩
        have hγmin := ht₁min γ hγF
        rw [hfa, fract_eq_off hgt.le]
        linarith [hγle, hγmin]
    obtain ⟨d₀, hd₀mem, hd₀bd⟩ := Finset.mem_biUnion.mp ht₁bd
    refine ⟨s₀, hs₀safe, by rw [hfa]; linarith [hoff1, ht₁neg],
            by rw [hfa]; linarith [hoff1], hmax,
            circ_max_of_fract_max guards hns (by rw [hfa]; linarith [hoff1]) hmax,
            ⟨d₀, hd₀mem, ?_⟩⟩
    obtain ⟨l, -, rfl⟩ := Finset.mem_image.mp hd₀bd
    -- the bottom-boundary point reflects to the top boundary `5/6`
    have hbd : fract ((d₀ : ℝ) * (((6 * l + 1 : ℕ) : ℝ) / (6 * (d₀ : ℝ)))) = 1 / 6 :=
      botBdry6_pos (hpos d₀ hd₀mem)
    have h2 : (d₀ : ℝ) * s₀ =
        -((d₀ : ℝ) * (((6 * l + 1 : ℕ) : ℝ) / (6 * (d₀ : ℝ)))) := by
      rw [hs₀def]; ring
    have hz : fract ((d₀ : ℝ) * (((6 * l + 1 : ℕ) : ℝ) / (6 * (d₀ : ℝ)))) ≠ 0 := by
      rw [hbd]; norm_num
    rw [h2, fract_neg hz, hbd]
    norm_num

/-- The `λ = 1` improving move: if all guards sit in `[1/6, 5/6)` at `s` (strict
upper bound) and the anchor is at `x₁ ∈ (0, 1/6)`, a small forward perturbation
`s + η` keeps every guard safe while pushing `x₁` higher — the contradiction
Renault uses when `λ = 1`. -/
theorem exists_improve_eq_one (guards : Finset ℕ) (hguards : guards.Nonempty)
    (hpos : ∀ d ∈ guards, 0 < d) {a : ℕ} (ha : 0 < a) {s : ℝ}
    (hgs : ∀ d ∈ guards, fract ((d : ℝ) * s) ∈ Set.Ico (1 / 6) (5 / 6))
    (hx0 : 0 < fract ((a : ℝ) * s)) (hx6 : fract ((a : ℝ) * s) < 1 / 6) :
    ∃ s' : ℝ, (∀ d ∈ guards, fract ((d : ℝ) * s') ∈ Set.Icc (1 / 6) (5 / 6)) ∧
      fract ((a : ℝ) * s) < fract ((a : ℝ) * s') ∧
      fract ((a : ℝ) * s') < 1 / 6 := by
  have ha' : (0 : ℝ) < a := Nat.cast_pos.mpr ha
  classical
  obtain ⟨d₀, hd₀mem, hd₀min⟩ := guards.exists_min_image
    (fun d => (5 / 6 - fract ((d : ℝ) * s)) / (d : ℝ)) hguards
  set δ : ℝ := (5 / 6 - fract ((d₀ : ℝ) * s)) / (d₀ : ℝ) with hδdef
  have hd₀pos : (0 : ℝ) < d₀ := Nat.cast_pos.mpr (hpos d₀ hd₀mem)
  have hδpos : 0 < δ := by
    rw [hδdef]
    exact div_pos (by linarith [(hgs d₀ hd₀mem).2]) hd₀pos
  set η : ℝ := min δ ((1 / 6 - fract ((a : ℝ) * s)) / (a : ℝ)) / 2 with hηdef
  have hmin : 0 < min δ ((1 / 6 - fract ((a : ℝ) * s)) / (a : ℝ)) :=
    lt_min hδpos (div_pos (by linarith) ha')
  have hηpos : 0 < η := by rw [hηdef]; exact half_pos hmin
  have hηδ : η < δ := by
    rw [hηdef]
    exact (half_lt_self hmin).trans_le (min_le_left _ _)
  have hηa : η < (1 / 6 - fract ((a : ℝ) * s)) / (a : ℝ) := by
    rw [hηdef]
    exact (half_lt_self hmin).trans_le (min_le_right _ _)
  refine ⟨s + η, ?_, ?_, ?_⟩
  · intro d hd
    obtain ⟨hlo, hhi⟩ := hgs d hd
    have hdpos : (0 : ℝ) < d := Nat.cast_pos.mpr (hpos d hd)
    have hδd : δ ≤ (5 / 6 - fract ((d : ℝ) * s)) / (d : ℝ) := by
      rw [hδdef]; exact hd₀min d hd
    have hdη : (d : ℝ) * η < 5 / 6 - fract ((d : ℝ) * s) := by
      calc (d : ℝ) * η < (d : ℝ) * δ := by gcongr
        _ ≤ (d : ℝ) * ((5 / 6 - fract ((d : ℝ) * s)) / (d : ℝ)) := by gcongr
        _ = 5 / 6 - fract ((d : ℝ) * s) := by field_simp
    have hdη0 : 0 ≤ (d : ℝ) * η := mul_nonneg hdpos.le hηpos.le
    have hfr : fract ((d : ℝ) * (s + η)) = fract ((d : ℝ) * s) + (d : ℝ) * η := by
      rw [fract_add_shift]
      exact Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
    rw [hfr]
    exact Set.mem_Icc.mpr ⟨by linarith, by linarith⟩
  · have hfr : fract ((a : ℝ) * (s + η)) = fract ((a : ℝ) * s) + (a : ℝ) * η := by
      rw [fract_add_shift]
      have haη : (a : ℝ) * η < 1 / 6 - fract ((a : ℝ) * s) := by
        calc (a : ℝ) * η < (a : ℝ) * ((1 / 6 - fract ((a : ℝ) * s)) / (a : ℝ)) := by gcongr
          _ = 1 / 6 - fract ((a : ℝ) * s) := by field_simp
      exact Int.fract_eq_self.mpr ⟨by linarith [mul_nonneg ha'.le hηpos.le], by linarith⟩
    rw [hfr]
    linarith [mul_pos ha' hηpos]
  · have hfr : fract ((a : ℝ) * (s + η)) = fract ((a : ℝ) * s) + (a : ℝ) * η := by
      rw [fract_add_shift]
      have haη : (a : ℝ) * η < 1 / 6 - fract ((a : ℝ) * s) := by
        calc (a : ℝ) * η < (a : ℝ) * ((1 / 6 - fract ((a : ℝ) * s)) / (a : ℝ)) := by gcongr
          _ = 1 / 6 - fract ((a : ℝ) * s) := by field_simp
      exact Int.fract_eq_self.mpr ⟨by linarith [mul_nonneg ha'.le hηpos.le], by linarith⟩
    rw [hfr]
    have haη : (a : ℝ) * η < 1 / 6 - fract ((a : ℝ) * s) := by
      calc (a : ℝ) * η < (a : ℝ) * ((1 / 6 - fract ((a : ℝ) * s)) / (a : ℝ)) := by gcongr
        _ = 1 / 6 - fract ((a : ℝ) * s) := by field_simp
    linarith

end
