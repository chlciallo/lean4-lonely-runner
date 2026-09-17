/-
Copyright (c) 2026 Research07 contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Research07 contributors
-/

import Mathlib
import Research07.LRC3.Circ
import Research07.LRC3.TwoMoving

/-!# W5 — LRC integer case for ≤3 speeds, threshold 1/4 (FROZEN STATEMENT)

Renault's argument (J. Renault, *View-obstruction: a shorter proof for
6 lonely runners*, Discrete Math. 287 (2004), Appendix A for `s = 3`),
formalized via finite candidate sets of quarter-boundary times rather than
compactness: for each runner `d`, the times where it sits at position `3/4`
mod `1` are `(4l+3)/(4d)`, a finite set modulo `1`.  Every safe time has a
forward exit point in that finite set, so the maximal offset of runner `a` is
attained at an explicit candidate.

Owned by agent W5 — fill the `sorry`.
-/

noncomputable section

/-- `circ x ≥ 1/4` iff `fract x ∈ [1/4, 3/4]`. -/
theorem circ_ge_quarter_fract (x : ℝ) :
    (1 / 4 : ℝ) ≤ circ x ↔ Int.fract x ∈ Set.Icc (1 / 4) (3 / 4) := by
  rw [circ_eq, abs_sub_round_eq_min, Set.mem_Icc]
  constructor
  · intro h
    have h1 := Int.fract_nonneg x
    have h2 := Int.fract_lt_one x
    constructor
    · exact le_trans h (min_le_left _ _)
    · have h3 := le_trans h (min_le_right _ _)
      linarith
  · rintro ⟨h1, h2⟩
    exact le_min h1 (by linarith)

/-- `circ x ≥ 1/4` iff `x` lies in some quarter-gap arc `[k + 1/4, k + 3/4]`. -/
theorem circ_ge_quarter_iff (x : ℝ) :
    (1 / 4 : ℝ) ≤ circ x ↔ ∃ k : ℤ, x ∈ Set.Icc ((k : ℝ) + 1 / 4) ((k : ℝ) + 3 / 4) := by
  rw [circ_ge_quarter_fract, Set.mem_Icc]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨⌊x⌋, ?_, ?_⟩
    · have h3 := Int.self_sub_floor x
      have h4 := Int.fract_nonneg x
      linarith
    · have h3 := Int.self_sub_floor x
      linarith
  · rintro ⟨k, h1, h2⟩
    have hk : Int.fract x = x - (k : ℝ) := by
      have h3 : Int.fract (x - (k : ℝ)) = x - (k : ℝ) := by
        rw [Int.fract_eq_self]
        constructor <;> push_cast <;> linarith
      have h4 : Int.fract (x - (k : ℝ)) = Int.fract x :=
        Int.fract_sub_intCast x k
      linarith [h4]
    constructor
    · rw [hk]; linarith
    · rw [hk]; linarith

/-- `circ` of `|t|·d` equals `circ` of `t·d`. -/
private theorem circ_abs_mul (t : ℝ) (d : ℕ) :
    circ (|t| * (d : ℝ)) = circ (t * (d : ℝ)) := by
  have h : |t * (d : ℝ)| = |t| * (d : ℝ) := by
    rw [abs_mul]; simp
  rw [← circ_abs (t * (d : ℝ)), h]

/-- `fract (x + s) = fract (fract x + s)`. -/
private theorem fract_self_add (x s : ℝ) :
    Int.fract (x + s) = Int.fract (Int.fract x + s) := by
  have h : x + s = Int.fract x + s + (⌊x⌋ : ℝ) := by
    have h2 := Int.self_sub_fract x
    linarith
  rw [h, Int.fract_add_intCast]

/-- Position bookkeeping: `fract (d·(t+s)) = fract (fract (d·t) + d·s)`. -/
private theorem fract_add_shift (d : ℕ) (t s : ℝ) :
    Int.fract ((d : ℝ) * (t + s)) =
      Int.fract (Int.fract ((d : ℝ) * t) + (d : ℝ) * s) := by
  have h2 : (d : ℝ) * t = Int.fract ((d : ℝ) * t) + (⌊(d : ℝ) * t⌋ : ℝ) := by
    have h3 := Int.self_sub_fract ((d : ℝ) * t)
    linarith
  have h1 : (d : ℝ) * (t + s) =
      (Int.fract ((d : ℝ) * t) + (d : ℝ) * s) + (⌊(d : ℝ) * t⌋ : ℝ) := by
    linarith [h2]
  rw [h1, Int.fract_add_intCast]

/-- `fract (d·(k·t)) = fract (k·fract (d·t))` for `k : ℕ`. -/
private theorem fract_nat_mul (d : ℕ) (k : ℕ) (t : ℝ) :
    Int.fract ((d : ℝ) * ((k : ℝ) * t)) =
      Int.fract ((k : ℝ) * Int.fract ((d : ℝ) * t)) := by
  have h2 : (d : ℝ) * t = Int.fract ((d : ℝ) * t) + (⌊(d : ℝ) * t⌋ : ℝ) := by
    have h3 := Int.self_sub_fract ((d : ℝ) * t)
    linarith
  have h1 : (d : ℝ) * ((k : ℝ) * t) =
      (k : ℝ) * Int.fract ((d : ℝ) * t) + (((k : ℤ) * ⌊(d : ℝ) * t⌋ : ℤ) : ℝ) := by
    push_cast
    linear_combination (k : ℝ) * h2
  rw [h1, Int.fract_add_intCast]

/-- Half-shift by an even speed is invisible: `fract (x + v/2) = fract x`. -/
private theorem fract_half_even {v : ℕ} (hv : Even v) (x : ℝ) :
    Int.fract (x + (v : ℝ) / 2) = Int.fract x := by
  obtain ⟨q, rfl⟩ := hv
  push_cast
  rw [show ((q : ℝ) + q) / 2 = (q : ℝ) by ring, Int.fract_add_natCast]

/-- Half-shift by an odd speed is a flip: `fract (x + u/2) = fract (x + 1/2)`. -/
private theorem fract_half_odd {u : ℕ} (hu : Odd u) (x : ℝ) :
    Int.fract (x + (u : ℝ) / 2) = Int.fract (x + 1 / 2) := by
  obtain ⟨p, rfl⟩ := hu
  push_cast
  rw [show ((2 : ℝ) * p + 1) / 2 = (p : ℝ) + 1 / 2 by ring,
    show x + ((p : ℝ) + 1 / 2) = (p : ℝ) + (x + 1 / 2) by ring,
    Int.fract_natCast_add]

/-- `fract (3/2) = 1/2`. -/
private theorem fract_three_halves : Int.fract ((3 / 2 : ℝ)) = 1 / 2 := by
  rw [Int.fract_eq_iff]
  exact ⟨by norm_num, by norm_num, ⟨1, by norm_num⟩⟩

/-- `fract (9/4) = 1/4`. -/
private theorem fract_nine_quarters : Int.fract ((9 / 4 : ℝ)) = 1 / 4 := by
  rw [Int.fract_eq_iff]
  exact ⟨by norm_num, by norm_num, ⟨2, by norm_num⟩⟩

/-- For `y ∈ [0,1)`, either `y` or `fract (y + 1/2)` is safe. -/
private theorem mem_Icc_or_half {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y < 1) :
    y ∈ Set.Icc (1 / 4) (3 / 4) ∨ Int.fract (y + 1 / 2) ∈ Set.Icc (1 / 4) (3 / 4) := by
  rcases le_total y (1 / 4) with h | h
  · right
    rw [Int.fract_eq_self.mpr (by constructor <;> linarith)]
    rw [Set.mem_Icc]
    constructor <;> linarith
  · rcases le_total y (3 / 4) with h2 | h2
    · left
      exact ⟨h, h2⟩
    · right
      have h3 : Int.fract (y + 1 / 2) = y - 1 / 2 := by
        rw [show y + 1 / 2 = (y - 1 / 2) + ((1 : ℤ) : ℝ) by push_cast; ring,
          Int.fract_add_intCast]
        rw [Int.fract_eq_self]
        constructor <;> linarith
      rw [h3, Set.mem_Icc]
      constructor <;> linarith

/-- Signed offset of `a·t` from the nearest integer. -/
private noncomputable def off (a : ℕ) (t : ℝ) : ℝ :=
  (a : ℝ) * t - (round ((a : ℝ) * t) : ℝ)

/-- `|off a t| = circ (a·t)`. -/
private theorem abs_off (a : ℕ) (t : ℝ) :
    |off a t| = circ ((a : ℝ) * t) := by
  rw [off, circ_eq]

/-- `off` is `1`-periodic. -/
private theorem off_add_int (a : ℕ) (t : ℝ) (n : ℤ) :
    off a (t + (n : ℝ)) = off a t := by
  rw [off, off]
  rw [show (a : ℝ) * (t + (n : ℝ)) = (a : ℝ) * t + ((a : ℤ) * n : ℤ) by
    push_cast; ring]
  rw [round_add_intCast]
  push_cast
  ring

/-- `off` at `fract t` equals `off` at `t`. -/
private theorem off_fract (a : ℕ) (t : ℝ) : off a (Int.fract t) = off a t := by
  rw [show Int.fract t = t + ((-⌊t⌋ : ℤ) : ℝ) by
    have h := Int.self_sub_floor t
    push_cast
    linarith]
  exact off_add_int a t _

/-- The finite set of `3/4`-boundary times of runner `d` in `[0,1)`:
times `(4l+3)/(4d)` for `l = 0,…,d−1`. -/
private def topBdry (d : ℕ) : Finset ℝ :=
  (Finset.range d).image fun l => ((4 * l + 3 : ℕ) : ℝ) / (4 * (d : ℝ))

/-- At a `topBdry` point, runner `d` sits at `3/4`. -/
private theorem topBdry_pos {d l : ℕ} (hd : 0 < d) :
    Int.fract ((d : ℝ) * (((4 * l + 3 : ℕ) : ℝ) / (4 * (d : ℝ)))) = 3 / 4 := by
  have hd' : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have h1 : (d : ℝ) * (((4 * l + 3 : ℕ) : ℝ) / (4 * (d : ℝ))) = (l : ℝ) + 3 / 4 := by
    field_simp
    push_cast
    ring
  rw [h1, show (l : ℝ) + 3 / 4 = ((l : ℤ) : ℝ) + 3 / 4 by push_cast; ring,
    Int.fract_intCast_add, Int.fract_eq_self]
  constructor <;> norm_num

/-- Round stays fixed near an integer: `round (n + r) = n` for `r ∈ [−1/2, 1/2)`. -/
private theorem round_of_quarter {n : ℤ} {r : ℝ} (h1 : -1 / 2 ≤ r) (h2 : r < 1 / 2) :
    round ((n : ℝ) + r) = n := by
  rw [round_eq_iff, Set.mem_Ico]
  constructor <;> push_cast <;> linarith

/-- If `d·β' = l + 3/4` for `l : ℤ`, then `Int.fract β'` is a `topBdry d`
element. -/
private theorem fract_mem_topBdry {d : ℕ} (hd : 0 < d) {β' : ℝ} {l : ℤ}
    (h : (d : ℝ) * β' = (l : ℝ) + 3 / 4) :
    Int.fract β' ∈ topBdry d := by
  have hd' : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  set l' : ℤ := l - (d : ℤ) * ⌊β'⌋ with hl'
  have hdβ : (d : ℝ) * Int.fract β' = (l' : ℝ) + 3 / 4 := by
    have hf : Int.fract β' = β' - (⌊β'⌋ : ℝ) := Int.self_sub_floor β'
    rw [hf]
    have h2 : (d : ℝ) * (β' - (⌊β'⌋ : ℝ)) =
        (d : ℝ) * β' - (((d : ℤ) * ⌊β'⌋ : ℤ) : ℝ) := by
      push_cast; ring
    rw [h2, h, hl']
    push_cast
    ring
  have hβ0 : 0 ≤ Int.fract β' := Int.fract_nonneg β'
  have hβ1 : Int.fract β' < 1 := Int.fract_lt_one β'
  have hl'0 : 0 ≤ l' := by
    have h1 : (0 : ℝ) ≤ (l' : ℝ) + 3 / 4 := by rw [← hdβ]; positivity
    by_contra hlt
    have h2 : l' ≤ -1 := by omega
    have h3 : (l' : ℝ) ≤ (-1 : ℝ) := by exact_mod_cast h2
    linarith
  have hl'u : l' < (d : ℤ) := by
    have h1 : (l' : ℝ) + 3 / 4 < (d : ℝ) := by
      rw [← hdβ]
      calc (d : ℝ) * Int.fract β' < (d : ℝ) * 1 := by gcongr
        _ = d := by ring
    have h2 : (l' : ℝ) < (d : ℝ) := by linarith
    exact_mod_cast h2
  have hβeq : Int.fract β' = ((4 * l'.toNat + 3 : ℕ) : ℝ) / (4 * (d : ℝ)) := by
    have hcast : ((l'.toNat : ℕ) : ℝ) = (l' : ℝ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hl'0]
    have hnum : ((4 * l'.toNat + 3 : ℕ) : ℝ) = 4 * (l' : ℝ) + 3 := by
      push_cast
      rw [hcast]
    have h1 : Int.fract β' = ((l' : ℝ) + 3 / 4) / (d : ℝ) := by
      rw [eq_div_iff hd'.ne']
      rw [mul_comm]; exact hdβ
    rw [h1, hnum]
    field_simp
  rw [hβeq, topBdry, Finset.mem_image]
  refine ⟨l'.toNat, Finset.mem_range.mpr ?_, rfl⟩
  omega

/-- Forward endpoint lemma: every safe time `t` has a forward exit point whose
fractional part lies in the finite set `topBdry u ∪ topBdry v`, stays safe for
both runners, and does not decrease `off a`. -/
private theorem forward_endpoint {a u v : ℕ} (ha : 0 < a) (hu : 0 < u) (hv : 0 < v)
    (hns : ∀ t : ℝ, Int.fract ((u : ℝ) * t) ∈ Set.Icc (1 / 4) (3 / 4) →
      Int.fract ((v : ℝ) * t) ∈ Set.Icc (1 / 4) (3 / 4) → |off a t| < 1 / 4)
    {t : ℝ} (huT : Int.fract ((u : ℝ) * t) ∈ Set.Icc (1 / 4) (3 / 4))
    (hvT : Int.fract ((v : ℝ) * t) ∈ Set.Icc (1 / 4) (3 / 4)) :
    ∃ β : ℝ, (β ∈ topBdry u ∨ β ∈ topBdry v)
      ∧ Int.fract ((u : ℝ) * β) ∈ Set.Icc (1 / 4) (3 / 4)
      ∧ Int.fract ((v : ℝ) * β) ∈ Set.Icc (1 / 4) (3 / 4)
      ∧ off a t ≤ off a β := by
  have hu' : (0 : ℝ) < u := Nat.cast_pos.mpr hu
  have hv' : (0 : ℝ) < v := Nat.cast_pos.mpr hv
  have ha' : (0 : ℝ) < a := Nat.cast_pos.mpr ha
  set xu := Int.fract ((u : ℝ) * t) with hxu_def
  set xv := Int.fract ((v : ℝ) * t) with hxv_def
  set δ := min ((3 / 4 - xu) / (u : ℝ)) ((3 / 4 - xv) / (v : ℝ)) with hδ_def
  have hδu : (u : ℝ) * δ ≤ 3 / 4 - xu := by
    have h : δ ≤ (3 / 4 - xu) / (u : ℝ) := min_le_left _ _
    calc (u : ℝ) * δ ≤ u * ((3 / 4 - xu) / u) := by gcongr
      _ = 3 / 4 - xu := by field_simp
  have hδv : (v : ℝ) * δ ≤ 3 / 4 - xv := by
    have h : δ ≤ (3 / 4 - xv) / (v : ℝ) := min_le_right _ _
    calc (v : ℝ) * δ ≤ v * ((3 / 4 - xv) / v) := by gcongr
      _ = 3 / 4 - xv := by field_simp
  have hδ0 : 0 ≤ δ := by
    rw [hδ_def]
    apply le_min
    · apply div_nonneg _ hu'.le
      have := huT.2
      linarith
    · apply div_nonneg _ hv'.le
      have := hvT.2
      linarith
  -- positions along the segment [t, t+δ]
  have hseg : ∀ s : ℝ, 0 ≤ s → s ≤ δ →
      Int.fract ((u : ℝ) * (t + s)) ∈ Set.Icc (1 / 4) (3 / 4)
      ∧ Int.fract ((v : ℝ) * (t + s)) ∈ Set.Icc (1 / 4) (3 / 4) := by
    intro s hs0 hsδ
    refine ⟨?_, ?_⟩
    · have h2 : (u : ℝ) * s ≤ (u : ℝ) * δ :=
        mul_le_mul_of_nonneg_left hsδ hu'.le
      have h3 : 0 ≤ (u : ℝ) * s := mul_nonneg hu'.le hs0
      have h1 : Int.fract ((u : ℝ) * (t + s)) = xu + (u : ℝ) * s := by
        rw [fract_add_shift, Int.fract_eq_self]
        refine ⟨by have h4 := huT.1; linarith, by have h5 := hδu; linarith⟩
      rw [h1]
      refine ⟨by have h4 := huT.1; linarith, by have h5 := hδu; linarith⟩
    · have h2 : (v : ℝ) * s ≤ (v : ℝ) * δ :=
        mul_le_mul_of_nonneg_left hsδ hv'.le
      have h3 : 0 ≤ (v : ℝ) * s := mul_nonneg hv'.le hs0
      have h1 : Int.fract ((v : ℝ) * (t + s)) = xv + (v : ℝ) * s := by
        rw [fract_add_shift, Int.fract_eq_self]
        refine ⟨by have h4 := hvT.1; linarith, by have h5 := hδv; linarith⟩
      rw [h1]
      refine ⟨by have h4 := hvT.1; linarith, by have h5 := hδv; linarith⟩
  -- off is nondecreasing on the segment
  have hoff : off a (t + δ) = off a t + (a : ℝ) * δ := by
    have hoff0 := hns t huT hvT
    rw [abs_lt] at hoff0
    set n₀ := round ((a : ℝ) * t) with hn₀
    have hat : (a : ℝ) * t = (n₀ : ℝ) + off a t := by
      rw [off]; linarith
    -- upper bound: a·δ < 1/4 − off a t
    have hub : (a : ℝ) * δ < 1 / 4 - off a t := by
      by_contra hcon
      have hcon' : (1 / 4 - off a t) ≤ (a : ℝ) * δ := le_of_not_gt hcon
      set s' := (1 / 4 - off a t) / (a : ℝ) with hs'
      have hs'0 : 0 < s' := div_pos (by linarith [hoff0.2]) ha'
      have hs'δ : s' ≤ δ := by
        rw [hs', div_le_iff₀ ha']
        linarith [hcon']
      have h1 : (a : ℝ) * (t + s') = (n₀ : ℝ) + 1 / 4 := by
        have hs'' : (a : ℝ) * s' = 1 / 4 - off a t := by
          rw [hs']; field_simp
        have hexp : (a : ℝ) * (t + s') = (a : ℝ) * t + (a : ℝ) * s' := by ring
        rw [hexp]; linarith [hat]
      have h2 := hns (t + s') (hseg s' hs'0.le hs'δ).1 (hseg s' hs'0.le hs'δ).2
      have h3 : off a (t + s') = 1 / 4 := by
        rw [off, h1]
        rw [round_of_quarter (by norm_num : (-1 / 2 : ℝ) ≤ 1 / 4)
          (by norm_num : (1 / 4 : ℝ) < 1 / 2)]
        push_cast; ring
      rw [h3] at h2
      norm_num at h2
    have hrnd : round ((a : ℝ) * (t + δ)) = n₀ := by
      have h1 : (a : ℝ) * (t + δ) = (n₀ : ℝ) + (off a t + (a : ℝ) * δ) := by
        have hexp : (a : ℝ) * (t + δ) = (a : ℝ) * t + (a : ℝ) * δ := by ring
        rw [hexp]; linarith [hat]
      rw [h1]
      apply round_of_quarter
      · linarith [hoff0.1, mul_nonneg ha'.le hδ0]
      · linarith [hub]
    rw [off, off, hrnd]
    have hexp : (a : ℝ) * (t + δ) = (a : ℝ) * t + (a : ℝ) * δ := by ring
    rw [hexp]
    -- a·t + a·δ − n₀ = (a·t − n₀) + a·δ where n₀ = round (a·t)
    show (a : ℝ) * t + (a : ℝ) * δ - ↑n₀ = ((a : ℝ) * t - ↑n₀) + (a : ℝ) * δ
    ring
  -- the exit runner sits at 3/4
  rcases le_total ((3 / 4 - xu) / (u : ℝ)) ((3 / 4 - xv) / (v : ℝ)) with hcmp | hcmp
  · -- runner u exits at t + δ
    have hmin : δ = (3 / 4 - xu) / (u : ℝ) := min_eq_left hcmp
    have hxuβ' : Int.fract ((u : ℝ) * (t + δ)) = 3 / 4 := by
      have h1 : Int.fract ((u : ℝ) * (t + δ)) = xu + (u : ℝ) * δ := by
        rw [fract_add_shift, Int.fract_eq_self]
        refine ⟨by have h3 := huT.1; have h4 := mul_nonneg hu'.le hδ0; linarith, by linarith [hδu]⟩
      have h2 : (u : ℝ) * δ = 3 / 4 - xu := by
        rw [hmin]; field_simp
      rw [h1]; linarith
    have hxvβ' : Int.fract ((v : ℝ) * (t + δ)) = xv + (v : ℝ) * δ := by
      rw [fract_add_shift, Int.fract_eq_self]
      refine ⟨by have h3 := hvT.1; have h4 := mul_nonneg hv'.le hδ0; linarith, by linarith [hδv]⟩
    refine ⟨Int.fract (t + δ), Or.inl ?_, ?_, ?_, ?_⟩
    · refine fract_mem_topBdry hu (l := ⌊(u : ℝ) * (t + δ)⌋) ?_
      have h := Int.self_sub_floor ((u : ℝ) * (t + δ))
      linarith [hxuβ']
    · have h : (u : ℝ) * Int.fract (t + δ) =
          (u : ℝ) * (t + δ) + ((- (u : ℤ) * ⌊t + δ⌋ : ℤ) : ℝ) := by
        have hsf := (Int.self_sub_floor (t + δ)).symm
        push_cast
        linear_combination (u : ℝ) * hsf
      rw [h, Int.fract_add_intCast, hxuβ']
      refine ⟨by norm_num, le_refl _⟩
    · have h : (v : ℝ) * Int.fract (t + δ) =
          (v : ℝ) * (t + δ) + ((- (v : ℤ) * ⌊t + δ⌋ : ℤ) : ℝ) := by
        have hsf := (Int.self_sub_floor (t + δ)).symm
        push_cast
        linear_combination (v : ℝ) * hsf
      rw [h, Int.fract_add_intCast, hxvβ']
      refine ⟨by have h3 := hvT.1; have h4 := mul_nonneg hv'.le hδ0; linarith, by linarith [hδv]⟩
    · rw [off_fract, hoff]
      have : 0 ≤ (a : ℝ) * δ := mul_nonneg ha'.le hδ0
      linarith
  · -- runner v exits at t + δ
    have hmin : δ = (3 / 4 - xv) / (v : ℝ) := min_eq_right hcmp
    have hxvβ' : Int.fract ((v : ℝ) * (t + δ)) = 3 / 4 := by
      have h1 : Int.fract ((v : ℝ) * (t + δ)) = xv + (v : ℝ) * δ := by
        rw [fract_add_shift, Int.fract_eq_self]
        refine ⟨by have h3 := hvT.1; have h4 := mul_nonneg hv'.le hδ0; linarith, by linarith [hδv]⟩
      have h2 : (v : ℝ) * δ = 3 / 4 - xv := by
        rw [hmin]; field_simp
      rw [h1]; linarith
    have hxuβ' : Int.fract ((u : ℝ) * (t + δ)) = xu + (u : ℝ) * δ := by
      rw [fract_add_shift, Int.fract_eq_self]
      refine ⟨by have h3 := huT.1; have h4 := mul_nonneg hu'.le hδ0; linarith, by linarith [hδu]⟩
    refine ⟨Int.fract (t + δ), Or.inr ?_, ?_, ?_, ?_⟩
    · refine fract_mem_topBdry hv (l := ⌊(v : ℝ) * (t + δ)⌋) ?_
      have h := Int.self_sub_floor ((v : ℝ) * (t + δ))
      linarith [hxvβ']
    · have h : (u : ℝ) * Int.fract (t + δ) =
          (u : ℝ) * (t + δ) + ((- (u : ℤ) * ⌊t + δ⌋ : ℤ) : ℝ) := by
        have hsf := (Int.self_sub_floor (t + δ)).symm
        push_cast
        linear_combination (u : ℝ) * hsf
      rw [h, Int.fract_add_intCast, hxuβ']
      refine ⟨by have h3 := huT.1; have h4 := mul_nonneg hu'.le hδ0; linarith, by linarith [hδu]⟩
    · have h : (v : ℝ) * Int.fract (t + δ) =
          (v : ℝ) * (t + δ) + ((- (v : ℤ) * ⌊t + δ⌋ : ℤ) : ℝ) := by
        have hsf := (Int.self_sub_floor (t + δ)).symm
        push_cast
        linear_combination (v : ℝ) * hsf
      rw [h, Int.fract_add_intCast, hxvβ']
      refine ⟨by norm_num, le_refl _⟩
    · rw [off_fract, hoff]
      have : 0 ≤ (a : ℝ) * δ := mul_nonneg ha'.le hδ0
      linarith

/-- The finite set of `1/4`-boundary times of runner `d` in `[0,1)`:
times `(4l+1)/(4d)` for `l = 0,…,d−1`. -/
private def botBdry (d : ℕ) : Finset ℝ :=
  (Finset.range d).image fun l => ((4 * l + 1 : ℕ) : ℝ) / (4 * (d : ℝ))

/-- If `d·β' = l + 1/4` for `l : ℤ`, then `Int.fract β'` is a `botBdry d`
element. -/
private theorem fract_mem_botBdry {d : ℕ} (hd : 0 < d) {β' : ℝ} {l : ℤ}
    (h : (d : ℝ) * β' = (l : ℝ) + 1 / 4) :
    Int.fract β' ∈ botBdry d := by
  have hd' : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  set l' : ℤ := l - (d : ℤ) * ⌊β'⌋ with hl'
  have hdβ : (d : ℝ) * Int.fract β' = (l' : ℝ) + 1 / 4 := by
    have hf : Int.fract β' = β' - (⌊β'⌋ : ℝ) := Int.self_sub_floor β'
    rw [hf]
    have h2 : (d : ℝ) * (β' - (⌊β'⌋ : ℝ)) =
        (d : ℝ) * β' - (((d : ℤ) * ⌊β'⌋ : ℤ) : ℝ) := by
      push_cast; ring
    rw [h2, h, hl']
    push_cast
    ring
  have hβ0 : 0 ≤ Int.fract β' := Int.fract_nonneg β'
  have hβ1 : Int.fract β' < 1 := Int.fract_lt_one β'
  have hl'0 : 0 ≤ l' := by
    have h1 : (0 : ℝ) ≤ (l' : ℝ) + 1 / 4 := by rw [← hdβ]; positivity
    by_contra hlt
    have h2 : l' ≤ -1 := by omega
    have h3 : (l' : ℝ) ≤ (-1 : ℝ) := by exact_mod_cast h2
    linarith
  have hl'u : l' < (d : ℤ) := by
    have h1 : (l' : ℝ) + 1 / 4 < (d : ℝ) := by
      rw [← hdβ]
      calc (d : ℝ) * Int.fract β' < (d : ℝ) * 1 := by gcongr
        _ = d := by ring
    have h2 : (l' : ℝ) < (d : ℝ) := by linarith
    exact_mod_cast h2
  have hβeq : Int.fract β' = ((4 * l'.toNat + 1 : ℕ) : ℝ) / (4 * (d : ℝ)) := by
    have hcast : ((l'.toNat : ℕ) : ℝ) = (l' : ℝ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hl'0]
    have hnum : ((4 * l'.toNat + 1 : ℕ) : ℝ) = 4 * (l' : ℝ) + 1 := by
      push_cast
      rw [hcast]
    have h1 : Int.fract β' = ((l' : ℝ) + 1 / 4) / (d : ℝ) := by
      rw [eq_div_iff hd'.ne']
      rw [mul_comm]; exact hdβ
    rw [h1, hnum]
    field_simp
  rw [hβeq, botBdry, Finset.mem_image]
  refine ⟨l'.toNat, Finset.mem_range.mpr ?_, rfl⟩
  omega

/-- Backward endpoint lemma: every safe time `t` has a backward exit point whose
fractional part lies in `botBdry u ∪ botBdry v`, stays safe for both runners,
and does not increase `off a`. -/
private theorem backward_endpoint {a u v : ℕ} (ha : 0 < a) (hu : 0 < u) (hv : 0 < v)
    (hns : ∀ t : ℝ, Int.fract ((u : ℝ) * t) ∈ Set.Icc (1 / 4) (3 / 4) →
      Int.fract ((v : ℝ) * t) ∈ Set.Icc (1 / 4) (3 / 4) → |off a t| < 1 / 4)
    {t : ℝ} (huT : Int.fract ((u : ℝ) * t) ∈ Set.Icc (1 / 4) (3 / 4))
    (hvT : Int.fract ((v : ℝ) * t) ∈ Set.Icc (1 / 4) (3 / 4)) :
    ∃ β : ℝ, (β ∈ botBdry u ∨ β ∈ botBdry v)
      ∧ Int.fract ((u : ℝ) * β) ∈ Set.Icc (1 / 4) (3 / 4)
      ∧ Int.fract ((v : ℝ) * β) ∈ Set.Icc (1 / 4) (3 / 4)
      ∧ off a β ≤ off a t := by
  have hu' : (0 : ℝ) < u := Nat.cast_pos.mpr hu
  have hv' : (0 : ℝ) < v := Nat.cast_pos.mpr hv
  have ha' : (0 : ℝ) < a := Nat.cast_pos.mpr ha
  set xu := Int.fract ((u : ℝ) * t) with hxu_def
  set xv := Int.fract ((v : ℝ) * t) with hxv_def
  set δ := min ((xu - 1 / 4) / (u : ℝ)) ((xv - 1 / 4) / (v : ℝ)) with hδ_def
  have hδu : (u : ℝ) * δ ≤ xu - 1 / 4 := by
    have h : δ ≤ (xu - 1 / 4) / (u : ℝ) := min_le_left _ _
    calc (u : ℝ) * δ ≤ u * ((xu - 1 / 4) / u) := by gcongr
      _ = xu - 1 / 4 := by field_simp
  have hδv : (v : ℝ) * δ ≤ xv - 1 / 4 := by
    have h : δ ≤ (xv - 1 / 4) / (v : ℝ) := min_le_right _ _
    calc (v : ℝ) * δ ≤ v * ((xv - 1 / 4) / v) := by gcongr
      _ = xv - 1 / 4 := by field_simp
  have hδ0 : 0 ≤ δ := by
    rw [hδ_def]
    apply le_min
    · apply div_nonneg _ hu'.le
      have := huT.1
      linarith
    · apply div_nonneg _ hv'.le
      have := hvT.1
      linarith
  -- positions along the segment [t − δ, t]
  have hseg : ∀ s : ℝ, 0 ≤ s → s ≤ δ →
      Int.fract ((u : ℝ) * (t - s)) ∈ Set.Icc (1 / 4) (3 / 4)
      ∧ Int.fract ((v : ℝ) * (t - s)) ∈ Set.Icc (1 / 4) (3 / 4) := by
    intro s hs0 hsδ
    refine ⟨?_, ?_⟩
    · have h2 : (u : ℝ) * s ≤ (u : ℝ) * δ :=
        mul_le_mul_of_nonneg_left hsδ hu'.le
      have h3 : 0 ≤ (u : ℝ) * s := mul_nonneg hu'.le hs0
      have h1 : Int.fract ((u : ℝ) * (t - s)) = xu - (u : ℝ) * s := by
        have : Int.fract ((u : ℝ) * (t - s)) =
            Int.fract (xu - (u : ℝ) * s) := by
          have h := fract_add_shift u t (-s)
          rw [← sub_eq_add_neg, mul_neg, ← sub_eq_add_neg] at h
          exact h
        rw [this, Int.fract_eq_self]
        refine ⟨by have h4 := huT.1; linarith, by have h5 := huT.2; have h6 := mul_nonneg hu'.le hδ0; linarith⟩
      rw [h1]
      refine ⟨by have h4 := huT.1; linarith, by have h5 := huT.2; have h6 := mul_nonneg hu'.le hδ0; linarith⟩
    · have h2 : (v : ℝ) * s ≤ (v : ℝ) * δ :=
        mul_le_mul_of_nonneg_left hsδ hv'.le
      have h3 : 0 ≤ (v : ℝ) * s := mul_nonneg hv'.le hs0
      have h1 : Int.fract ((v : ℝ) * (t - s)) = xv - (v : ℝ) * s := by
        have : Int.fract ((v : ℝ) * (t - s)) =
            Int.fract (xv - (v : ℝ) * s) := by
          have h := fract_add_shift v t (-s)
          rw [← sub_eq_add_neg, mul_neg, ← sub_eq_add_neg] at h
          exact h
        rw [this, Int.fract_eq_self]
        refine ⟨by have h4 := hvT.1; linarith, by have h5 := hvT.2; have h6 := mul_nonneg hv'.le hδ0; linarith⟩
      rw [h1]
      refine ⟨by have h4 := hvT.1; linarith, by have h5 := hvT.2; have h6 := mul_nonneg hv'.le hδ0; linarith⟩
  -- off is nonincreasing backward
  have hoff : off a (t - δ) = off a t - (a : ℝ) * δ := by
    have hoff0 := hns t huT hvT
    rw [abs_lt] at hoff0
    set n₀ := round ((a : ℝ) * t) with hn₀
    have hat : (a : ℝ) * t = (n₀ : ℝ) + off a t := by
      rw [off]; linarith
    -- lower bound: a·δ < off a t + 1/4
    have hlb : (a : ℝ) * δ < off a t + 1 / 4 := by
      by_contra hcon
      have hcon' : off a t + 1 / 4 ≤ (a : ℝ) * δ := le_of_not_gt hcon
      set s' := (off a t + 1 / 4) / (a : ℝ) with hs'
      have hs'0 : 0 < s' := div_pos (by linarith [hoff0.1]) ha'
      have hs'δ : s' ≤ δ := by
        rw [hs', div_le_iff₀ ha']
        linarith [hcon']
      have h1 : (a : ℝ) * (t - s') = (n₀ : ℝ) - 1 / 4 := by
        have hs'' : (a : ℝ) * s' = off a t + 1 / 4 := by
          rw [hs']; field_simp
        have hexp : (a : ℝ) * (t - s') = (a : ℝ) * t - (a : ℝ) * s' := by ring
        rw [hexp]; linarith [hat]
      have h2 := hns (t - s') (hseg s' hs'0.le hs'δ).1 (hseg s' hs'0.le hs'δ).2
      have h3 : off a (t - s') = -1 / 4 := by
        rw [off, h1]
        have hr : round ((n₀ : ℝ) - 1 / 4) = n₀ := by
          rw [show (n₀ : ℝ) - 1 / 4 = (n₀ : ℝ) + (-1 / 4 : ℝ) by ring]
          exact round_of_quarter (by norm_num) (by norm_num)
        rw [hr]
        push_cast; ring
      rw [h3] at h2
      norm_num at h2
    have hrnd : round ((a : ℝ) * (t - δ)) = n₀ := by
      have h1 : (a : ℝ) * (t - δ) = (n₀ : ℝ) + (off a t - (a : ℝ) * δ) := by
        have hexp : (a : ℝ) * (t - δ) = (a : ℝ) * t - (a : ℝ) * δ := by ring
        rw [hexp]; linarith [hat]
      rw [h1]
      apply round_of_quarter
      · linarith [hlb, hoff0.1]
      · linarith [hoff0.2, mul_nonneg ha'.le hδ0]
    rw [off, off, hrnd]
    have hexp : (a : ℝ) * (t - δ) = (a : ℝ) * t - (a : ℝ) * δ := by ring
    rw [hexp]
    show (a : ℝ) * t - (a : ℝ) * δ - ↑n₀ = ((a : ℝ) * t - ↑n₀) - (a : ℝ) * δ
    ring
  -- the exit runner sits at 1/4
  rcases le_total ((xu - 1 / 4) / (u : ℝ)) ((xv - 1 / 4) / (v : ℝ)) with hcmp | hcmp
  · -- runner u exits at t − δ
    have hmin : δ = (xu - 1 / 4) / (u : ℝ) := min_eq_left hcmp
    have hxuβ' : Int.fract ((u : ℝ) * (t - δ)) = 1 / 4 := by
      have h1 : Int.fract ((u : ℝ) * (t - δ)) = xu - (u : ℝ) * δ := by
        have hh : Int.fract ((u : ℝ) * (t - δ)) =
            Int.fract (xu - (u : ℝ) * δ) := by
          have h := fract_add_shift u t (-δ)
          rw [← sub_eq_add_neg, mul_neg, ← sub_eq_add_neg] at h
          exact h
        rw [hh, Int.fract_eq_self]
        refine ⟨by have h4 := huT.1; linarith, by have h5 := huT.2; have h6 := mul_nonneg hu'.le hδ0; linarith⟩
      have h2 : (u : ℝ) * δ = xu - 1 / 4 := by
        rw [hmin]; field_simp
      rw [h1]; linarith
    have hxvβ' : Int.fract ((v : ℝ) * (t - δ)) = xv - (v : ℝ) * δ := by
      have hh : Int.fract ((v : ℝ) * (t - δ)) =
          Int.fract (xv - (v : ℝ) * δ) := by
        have h := fract_add_shift v t (-δ)
        rw [← sub_eq_add_neg, mul_neg, ← sub_eq_add_neg] at h
        exact h
      rw [hh, Int.fract_eq_self]
      refine ⟨by have h4 := hvT.1; linarith, by have h5 := hvT.2; have h6 := mul_nonneg hv'.le hδ0; linarith⟩
    refine ⟨Int.fract (t - δ), Or.inl ?_, ?_, ?_, ?_⟩
    · refine fract_mem_botBdry hu (l := ⌊(u : ℝ) * (t - δ)⌋) ?_
      have h := Int.self_sub_floor ((u : ℝ) * (t - δ))
      linarith [hxuβ']
    · have h : (u : ℝ) * Int.fract (t - δ) =
          (u : ℝ) * (t - δ) + ((- (u : ℤ) * ⌊t - δ⌋ : ℤ) : ℝ) := by
        have hsf := (Int.self_sub_floor (t - δ)).symm
        push_cast
        linear_combination (u : ℝ) * hsf
      rw [h, Int.fract_add_intCast, hxuβ']
      refine ⟨by norm_num, by norm_num⟩
    · have h : (v : ℝ) * Int.fract (t - δ) =
          (v : ℝ) * (t - δ) + ((- (v : ℤ) * ⌊t - δ⌋ : ℤ) : ℝ) := by
        have hsf := (Int.self_sub_floor (t - δ)).symm
        push_cast
        linear_combination (v : ℝ) * hsf
      rw [h, Int.fract_add_intCast, hxvβ']
      refine ⟨by have h3 := hvT.1; linarith,
        by have h5 := hvT.2; have h4 := mul_nonneg hv'.le hδ0; linarith⟩
    · rw [off_fract, hoff]
      have : 0 ≤ (a : ℝ) * δ := mul_nonneg ha'.le hδ0
      linarith
  · -- runner v exits at t − δ
    have hmin : δ = (xv - 1 / 4) / (v : ℝ) := min_eq_right hcmp
    have hxvβ' : Int.fract ((v : ℝ) * (t - δ)) = 1 / 4 := by
      have h1 : Int.fract ((v : ℝ) * (t - δ)) = xv - (v : ℝ) * δ := by
        have hh : Int.fract ((v : ℝ) * (t - δ)) =
            Int.fract (xv - (v : ℝ) * δ) := by
          have h := fract_add_shift v t (-δ)
          rw [← sub_eq_add_neg, mul_neg, ← sub_eq_add_neg] at h
          exact h
        rw [hh, Int.fract_eq_self]
        refine ⟨by have h4 := hvT.1; linarith, by have h5 := hvT.2; have h6 := mul_nonneg hv'.le hδ0; linarith⟩
      have h2 : (v : ℝ) * δ = xv - 1 / 4 := by
        rw [hmin]; field_simp
      rw [h1]; linarith
    have hxuβ' : Int.fract ((u : ℝ) * (t - δ)) = xu - (u : ℝ) * δ := by
      have hh : Int.fract ((u : ℝ) * (t - δ)) =
          Int.fract (xu - (u : ℝ) * δ) := by
        have h := fract_add_shift u t (-δ)
        rw [← sub_eq_add_neg, mul_neg, ← sub_eq_add_neg] at h
        exact h
      rw [hh, Int.fract_eq_self]
      refine ⟨by have h4 := huT.1; linarith, by have h5 := huT.2; have h6 := mul_nonneg hu'.le hδ0; linarith⟩
    refine ⟨Int.fract (t - δ), Or.inr ?_, ?_, ?_, ?_⟩
    · refine fract_mem_botBdry hv (l := ⌊(v : ℝ) * (t - δ)⌋) ?_
      have h := Int.self_sub_floor ((v : ℝ) * (t - δ))
      linarith [hxvβ']
    · have h : (u : ℝ) * Int.fract (t - δ) =
          (u : ℝ) * (t - δ) + ((- (u : ℤ) * ⌊t - δ⌋ : ℤ) : ℝ) := by
        have hsf := (Int.self_sub_floor (t - δ)).symm
        push_cast
        linear_combination (u : ℝ) * hsf
      rw [h, Int.fract_add_intCast, hxuβ']
      refine ⟨by have h3 := huT.1; linarith,
        by have h5 := huT.2; have h4 := mul_nonneg hu'.le hδ0; linarith⟩
    · have h : (v : ℝ) * Int.fract (t - δ) =
          (v : ℝ) * (t - δ) + ((- (v : ℤ) * ⌊t - δ⌋ : ℤ) : ℝ) := by
        have hsf := (Int.self_sub_floor (t - δ)).symm
        push_cast
        linear_combination (v : ℝ) * hsf
      rw [h, Int.fract_add_intCast, hxvβ']
      refine ⟨by norm_num, by norm_num⟩
    · rw [off_fract, hoff]
      have : 0 ≤ (a : ℝ) * δ := mul_nonneg ha'.le hδ0
      linarith

/-- There is a positive `ε` making `x·ε < A`, `y·ε < B`, `z·ε < C` when all
bounds are positive. -/
private theorem exists_pos_mul_lt' {x y z A B C : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hC : 0 < C) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    ∃ ε : ℝ, 0 < ε ∧ x * ε < A ∧ y * ε < B ∧ z * ε < C := by
  refine ⟨min (min (A / (2 * x)) (B / (2 * y))) (C / (2 * z)), by positivity,
    ?_, ?_, ?_⟩
  · calc x * min (min (A / (2 * x)) (B / (2 * y))) (C / (2 * z))
        ≤ x * (A / (2 * x)) := by
          gcongr
          exact (min_le_left _ _).trans (min_le_left _ _)
      _ = A / 2 := by field_simp
      _ < A := by linarith
  · calc y * min (min (A / (2 * x)) (B / (2 * y))) (C / (2 * z))
        ≤ y * (B / (2 * y)) := by
          gcongr
          exact (min_le_left _ _).trans (min_le_right _ _)
      _ = B / 2 := by field_simp
      _ < B := by linarith
  · calc z * min (min (A / (2 * x)) (B / (2 * y))) (C / (2 * z))
        ≤ z * (C / (2 * z)) := by
          gcongr
          exact min_le_right _ _
      _ = C / 2 := by field_simp
      _ < C := by linarith

/-- `fract (d·(2t)) = fract (2·fract (d·t))`, cast-friendly form. -/
private theorem fract_two_mul (d : ℕ) (t : ℝ) :
    Int.fract ((d : ℝ) * (2 * t)) = Int.fract (2 * Int.fract ((d : ℝ) * t)) := by
  have h := fract_nat_mul d 2 t
  push_cast at h
  exact h

/-- `fract (d·(3t)) = fract (3·fract (d·t))`, cast-friendly form. -/
private theorem fract_three_mul (d : ℕ) (t : ℝ) :
    Int.fract ((d : ℝ) * (3 * t)) = Int.fract (3 * Int.fract ((d : ℝ) * t)) := by
  have h := fract_nat_mul d 3 t
  push_cast at h
  exact h

/-- `off` is odd on the `|off| < 1/4` region: `off a (-t) = - off a t`. -/
private theorem off_neg {a : ℕ} {t : ℝ} (h : |off a t| < 1 / 4) :
    off a (-t) = -off a t := by
  unfold off
  rw [mul_neg]
  have h' : -(1 / 4) < (a : ℝ) * t - (round ((a : ℝ) * t) : ℝ) ∧
      (a : ℝ) * t - (round ((a : ℝ) * t) : ℝ) < 1 / 4 := by
    have h'' : |(a : ℝ) * t - (round ((a : ℝ) * t) : ℝ)| < 1 / 4 := h
    exact abs_lt.mp h''
  have hround : round (-((a : ℝ) * t)) = -round ((a : ℝ) * t) := by
    rw [round_eq_iff]
    have hr := (round_eq_iff (x := (a : ℝ) * t) (n := round ((a : ℝ) * t))).mp rfl
    rw [Set.mem_Ico] at hr ⊢
    push_cast
    constructor <;> linarith [h'.1, h'.2]
  rw [hround]
  push_cast
  ring

/-- `fract (a·t) = off a t` when the offset is nonnegative. -/
private theorem fract_eq_off {a : ℕ} {t : ℝ} (h : 0 ≤ off a t) :
    Int.fract ((a : ℝ) * t) = off a t := by
  have hlt : off a t < 1 := by
    have h1 : |off a t| ≤ 1 / 2 := by rw [abs_off]; exact circ_le_half _
    linarith [le_trans (le_abs_self _) h1]
  rw [Int.fract_eq_iff]
  refine ⟨h, hlt, round ((a : ℝ) * t), ?_⟩
  rw [off]
  ring

/-- `fract (a·t) = 1 + off a t` when the offset is negative. -/
private theorem fract_eq_one_add_off {a : ℕ} {t : ℝ} (h : off a t < 0) :
    Int.fract ((a : ℝ) * t) = 1 + off a t := by
  have hge : 0 ≤ 1 + off a t := by
    have h1 : |off a t| ≤ 1 / 2 := by rw [abs_off]; exact circ_le_half _
    linarith [le_trans (neg_le_abs _) h1]
  rw [Int.fract_eq_iff]
  refine ⟨hge, by linarith, round ((a : ℝ) * t) - 1, ?_⟩
  rw [off]
  push_cast
  ring

/-- At a `botBdry` time, runner `d` sits at `1/4`. -/
private theorem botBdry_pos {d l : ℕ} (hd : 0 < d) :
    Int.fract ((d : ℝ) * (((4 * l + 1 : ℕ) : ℝ) / (4 * (d : ℝ)))) = 1 / 4 := by
  have hd' : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have h1 : (d : ℝ) * (((4 * l + 1 : ℕ) : ℝ) / (4 * (d : ℝ))) = (l : ℝ) + 1 / 4 := by
    field_simp
    push_cast
    ring
  rw [h1, show (l : ℝ) + 1 / 4 = ((l : ℤ) : ℝ) + 1 / 4 by push_cast; ring,
    Int.fract_intCast_add, Int.fract_eq_self]
  constructor <;> norm_num

/-- `circ x ≥ 1/3` implies `fract x ∈ [1/3, 2/3]`. -/
private theorem fract_mem_third {x : ℝ} (h : (1 / 3 : ℝ) ≤ circ x) :
    Int.fract x ∈ Set.Icc (1 / 3) (2 / 3) := by
  obtain ⟨k, hk⟩ := (circ_ge_third_iff x).mp h
  obtain ⟨hk1, hk2⟩ := Set.mem_Icc.mp hk
  have hf : Int.fract x = x - (k : ℝ) := by
    have h2 : Int.fract (x - (k : ℝ)) = x - (k : ℝ) := by
      rw [Int.fract_eq_self]
      constructor <;> push_cast <;> linarith
    have h3 : Int.fract (x - (k : ℝ)) = Int.fract x := Int.fract_sub_intCast x k
    linarith [h3]
  rw [hf, Set.mem_Icc]
  constructor <;> linarith

/-- Renault's shifted-time argument: if `a` is a multiple of `4`, `u,v` are not
both even, and at `t₀` runner `a` just missed safety while `u` sits at `3/4`,
`v` is safe, and `a`'s position is maximal over the region, then some time
makes all three safe. -/
private theorem renault_core {a u v : ℕ} (ha : 0 < a) (hu : 0 < u) (hv : 0 < v)
    (ha4 : 4 ∣ a) (hpar : ¬ (2 ∣ u ∧ 2 ∣ v))
    {t₀ : ℝ} (hxa0 : 0 < Int.fract ((a : ℝ) * t₀))
    (hxa4 : Int.fract ((a : ℝ) * t₀) < 1 / 4)
    (hxu : Int.fract ((u : ℝ) * t₀) = 3 / 4)
    (hxv : Int.fract ((v : ℝ) * t₀) ∈ Set.Icc (1 / 4) (3 / 4))
    (hmax : ∀ t : ℝ, Int.fract ((u : ℝ) * t) ∈ Set.Icc (1 / 4) (3 / 4) →
      Int.fract ((v : ℝ) * t) ∈ Set.Icc (1 / 4) (3 / 4) →
      Int.fract ((a : ℝ) * t) < 1 / 4 →
      Int.fract ((a : ℝ) * t) ≤ Int.fract ((a : ℝ) * t₀)) :
    ∃ t : ℝ, 0 < t ∧ (1 / 4 : ℝ) ≤ circ (t * a) ∧ (1 / 4 : ℝ) ≤ circ (t * u) ∧
      (1 / 4 : ℝ) ≤ circ (t * v) := by
  have ha' : (0 : ℝ) < a := Nat.cast_pos.mpr ha
  have hu' : (0 : ℝ) < u := Nat.cast_pos.mpr hu
  have hv' : (0 : ℝ) < v := Nat.cast_pos.mpr hv
  -- output packer: |t| works whenever all three positions are safe
  have pack : ∀ t : ℝ, Int.fract ((a : ℝ) * t) ∈ Set.Icc (1 / 4) (3 / 4) →
      Int.fract ((u : ℝ) * t) ∈ Set.Icc (1 / 4) (3 / 4) →
      Int.fract ((v : ℝ) * t) ∈ Set.Icc (1 / 4) (3 / 4) →
      ∃ t' : ℝ, 0 < t' ∧ (1 / 4 : ℝ) ≤ circ (t' * a) ∧ (1 / 4 : ℝ) ≤ circ (t' * u) ∧
        (1 / 4 : ℝ) ≤ circ (t' * v) := by
    intro t hat hut hvt
    have ht0 : t ≠ 0 := by
      rintro rfl
      rw [mul_zero, Int.fract_zero] at hvt
      have hbad := (Set.mem_Icc.mp hvt).1
      norm_num at hbad
    refine ⟨|t|, abs_pos.mpr ht0, ?_, ?_, ?_⟩
    · rw [circ_abs_mul, mul_comm]; exact (circ_ge_quarter_fract _).mpr hat
    · rw [circ_abs_mul, mul_comm]; exact (circ_ge_quarter_fract _).mpr hut
    · rw [circ_abs_mul, mul_comm]; exact (circ_ge_quarter_fract _).mpr hvt
  -- finishing routine: an improving time either contradicts maximality or works
  have finish : ∀ t : ℝ, Int.fract ((u : ℝ) * t) ∈ Set.Icc (1 / 4) (3 / 4) →
      Int.fract ((v : ℝ) * t) ∈ Set.Icc (1 / 4) (3 / 4) →
      Int.fract ((a : ℝ) * t₀) < Int.fract ((a : ℝ) * t) →
      Int.fract ((a : ℝ) * t) < 3 / 4 →
      ∃ t' : ℝ, 0 < t' ∧ (1 / 4 : ℝ) ≤ circ (t' * a) ∧ (1 / 4 : ℝ) ≤ circ (t' * u) ∧
        (1 / 4 : ℝ) ≤ circ (t' * v) := by
    intro t hut hvt hgt hlt
    rcases le_total (Int.fract ((a : ℝ) * t)) (1 / 4) with h' | h'
    · rcases lt_or_eq_of_le h' with hlt' | heq'
      · have hh := hmax t hut hvt hlt'
        exfalso
        linarith
      · exact pack t ⟨heq'.ge, hlt.le⟩ hut hvt
    · exact pack t ⟨h', hlt.le⟩ hut hvt
  obtain ⟨m, hm⟩ := ha4
  -- `a/2` is an even integer
  have ha2 : (a : ℝ) / 2 = ((2 * m : ℤ) : ℝ) := by
    rw [hm]; push_cast; ring
  rcases Nat.even_or_odd v with hvE | hvO
  · -- v even, hence u odd
    have huO : Odd u := by
      rcases Nat.even_or_odd u with huE | huO
      · exact absurd ⟨even_iff_two_dvd.mp huE, even_iff_two_dvd.mp hvE⟩ hpar
      · exact huO
    rcases eq_or_lt_of_le hxv.2 with hxv3 | hxv3
    · -- v sits at 3/4: use t = 2 t₀
      have hxa2 : Int.fract ((a : ℝ) * (2 * t₀)) = 2 * Int.fract ((a : ℝ) * t₀) := by
        rw [fract_two_mul, Int.fract_eq_self]
        refine ⟨by linarith [hxa0], by linarith [hxa4]⟩
      have hxu2 : Int.fract ((u : ℝ) * (2 * t₀)) = 1 / 2 := by
        rw [fract_two_mul, hxu, show (2 : ℝ) * (3 / 4) = 3 / 2 by ring]
        exact fract_three_halves
      have hxv2 : Int.fract ((v : ℝ) * (2 * t₀)) = 1 / 2 := by
        rw [fract_two_mul, hxv3, show (2 : ℝ) * (3 / 4) = 3 / 2 by ring]
        exact fract_three_halves
      exact finish (2 * t₀)
        ⟨by rw [hxu2]; norm_num, by rw [hxu2]; norm_num⟩
        ⟨by rw [hxv2]; norm_num, by rw [hxv2]; norm_num⟩
        (by rw [hxa2]; linarith [hxa0]) (by rw [hxa2]; linarith [hxa4])
    · -- v strictly inside: use t = t₀ + 1/2 + ε
      obtain ⟨ε, hε0, hεu, hεv, hεa⟩ :=
        exists_pos_mul_lt' (show (0:ℝ) < 1 / 2 by norm_num)
          (show (0:ℝ) < 3 / 4 - Int.fract ((v : ℝ) * t₀) by linarith [hxv3])
          (show (0:ℝ) < 1 / 4 - Int.fract ((a : ℝ) * t₀) by linarith [hxa4])
          hu' hv' ha'
      have hu2 : Int.fract ((u : ℝ) * (t₀ + 1 / 2)) = 1 / 4 := by
        rw [fract_add_shift u t₀ (1 / 2), hxu,
          show (u : ℝ) * (1 / 2) = (u : ℝ) / 2 by ring, fract_half_odd huO,
          show (3 / 4 : ℝ) + 1 / 2 = ((1 : ℤ) : ℝ) + 1 / 4 by push_cast; ring,
          Int.fract_intCast_add, Int.fract_eq_self]
        constructor <;> norm_num
      have hxu' : Int.fract ((u : ℝ) * (t₀ + 1 / 2 + ε)) = 1 / 4 + (u : ℝ) * ε := by
        rw [fract_add_shift u (t₀ + 1 / 2) ε, hu2, Int.fract_eq_self]
        refine ⟨by have h4 := mul_nonneg hu'.le hε0.le; linarith, by linarith [hεu]⟩
      have hv2 : Int.fract ((v : ℝ) * (t₀ + 1 / 2)) = Int.fract ((v : ℝ) * t₀) := by
        rw [fract_add_shift v t₀ (1 / 2),
          show (v : ℝ) * (1 / 2) = (v : ℝ) / 2 by ring, fract_half_even hvE,
          Int.fract_fract]
      have hxv' : Int.fract ((v : ℝ) * (t₀ + 1 / 2 + ε)) =
          Int.fract ((v : ℝ) * t₀) + (v : ℝ) * ε := by
        rw [fract_add_shift v (t₀ + 1 / 2) ε, hv2, Int.fract_eq_self]
        refine ⟨by have h4 := mul_nonneg hv'.le hε0.le; linarith [hxv.1],
          by linarith [hxv.2, hεv]⟩
      have ha2' : Int.fract ((a : ℝ) * (t₀ + 1 / 2)) = Int.fract ((a : ℝ) * t₀) := by
        rw [fract_add_shift a t₀ (1 / 2),
          show (a : ℝ) * (1 / 2) = (a : ℝ) / 2 by ring, ha2,
          Int.fract_add_intCast, Int.fract_fract]
      have hxa' : Int.fract ((a : ℝ) * (t₀ + 1 / 2 + ε)) =
          Int.fract ((a : ℝ) * t₀) + (a : ℝ) * ε := by
        rw [fract_add_shift a (t₀ + 1 / 2) ε, ha2', Int.fract_eq_self]
        refine ⟨by have h4 := mul_nonneg ha'.le hε0.le; linarith [hxa0],
          by linarith [hxa4, hεa]⟩
      have huε : (0 : ℝ) ≤ (u : ℝ) * ε := mul_nonneg hu'.le hε0.le
      have hvε : (0 : ℝ) ≤ (v : ℝ) * ε := mul_nonneg hv'.le hε0.le
      have haε : (0 : ℝ) < (a : ℝ) * ε := mul_pos ha' hε0
      exact finish (t₀ + 1 / 2 + ε)
        ⟨by rw [hxu']; linarith [huε], by rw [hxu']; linarith [hεu]⟩
        ⟨by rw [hxv']; linarith [hxv.1, hvε], by rw [hxv']; linarith [hεv]⟩
        (by rw [hxa']; linarith [haε]) (by rw [hxa']; linarith [hxa4, hεa])
  · -- v odd: use t = 3t₀ or 3t₀ + 1/2
    have hxa3 : ∀ s : ℝ, Int.fract ((a : ℝ) * (3 * t₀ + s)) =
        Int.fract (3 * Int.fract ((a : ℝ) * t₀) + (a : ℝ) * s) := by
      intro s
      have h := fract_add_shift a (3 * t₀) s
      rw [fract_three_mul, ← fract_self_add] at h
      exact h
    have hxu3 : Int.fract ((u : ℝ) * (3 * t₀)) = 1 / 4 := by
      rw [fract_three_mul, hxu, show (3 : ℝ) * (3 / 4) = 9 / 4 by norm_num]
      exact fract_nine_quarters
    have hxv3' : Int.fract ((v : ℝ) * (3 * t₀)) =
        Int.fract (3 * Int.fract ((v : ℝ) * t₀)) :=
      fract_three_mul v t₀
    -- a-position at both candidates is fract (3M) = 3M
    have hxa3t : Int.fract ((a : ℝ) * (3 * t₀)) = 3 * Int.fract ((a : ℝ) * t₀) := by
      rw [fract_three_mul, Int.fract_eq_self]
      refine ⟨by linarith [hxa0], by linarith [hxa4]⟩
    rcases mem_Icc_or_half (y := Int.fract (3 * Int.fract ((v : ℝ) * t₀)))
      (Int.fract_nonneg _) (Int.fract_lt_one _) with hy | hy
    · -- t = 3 t₀
      exact finish (3 * t₀)
        ⟨by rw [hxu3], by rw [hxu3]; norm_num⟩
        (by rw [hxv3']; exact hy)
        (by rw [hxa3t]; linarith [hxa0]) (by rw [hxa3t]; linarith [hxa4])
    · -- t = 3 t₀ + 1/2
      have hu3' : Int.fract ((u : ℝ) * (3 * t₀ + 1 / 2)) ∈ Set.Icc (1 / 4) (3 / 4) := by
        have h := fract_add_shift u (3 * t₀) (1 / 2)
        rw [hxu3, show (u : ℝ) * (1 / 2) = (u : ℝ) / 2 by ring] at h
        rw [h]
        rcases Nat.even_or_odd u with huE | huO
        · have he : Int.fract (1 / 4 + (u : ℝ) / 2) = 1 / 4 := by
            rw [fract_half_even huE, Int.fract_eq_self]
            constructor <;> norm_num
          rw [he]
          exact ⟨by norm_num, by norm_num⟩
        · have he : Int.fract (1 / 4 + (u : ℝ) / 2) = 3 / 4 := by
            rw [fract_half_odd huO, show (1 / 4 : ℝ) + 1 / 2 = 3 / 4 by ring,
              Int.fract_eq_self]
            constructor <;> norm_num
          rw [he]
          exact ⟨by norm_num, by norm_num⟩
      have hv3' : Int.fract ((v : ℝ) * (3 * t₀ + 1 / 2)) ∈ Set.Icc (1 / 4) (3 / 4) := by
        have h := fract_add_shift v (3 * t₀) (1 / 2)
        rw [hxv3', show (v : ℝ) * (1 / 2) = (v : ℝ) / 2 by ring] at h
        rw [h, fract_half_odd hvO]
        exact hy
      have ha3' : Int.fract ((a : ℝ) * (3 * t₀ + 1 / 2)) =
          3 * Int.fract ((a : ℝ) * t₀) := by
        have h := hxa3 (1 / 2)
        rw [show (a : ℝ) * (1 / 2) = (a : ℝ) / 2 by ring, ha2,
          Int.fract_add_intCast] at h
        rw [h, Int.fract_eq_self]
        refine ⟨by linarith [hxa0], by linarith [hxa4]⟩
      exact finish (3 * t₀ + 1 / 2) hu3' hv3'
        (by rw [ha3']; linarith [hxa0]) (by rw [ha3']; linarith [hxa4])

/-- The `4 ∣ a` reduction: if `u,v` are not both even, some time makes `a,u,v`
all safe.  Seed from the `two_moving` margin interval (which always contains a
point with `off a ≠ 0`), then extremize `off a` over the finite boundary set. -/
private theorem renault_driver {a u v : ℕ} (ha : 0 < a) (hu : 0 < u) (hv : 0 < v)
    (ha4 : 4 ∣ a) (hpar : ¬ (2 ∣ u ∧ 2 ∣ v)) :
    ∃ t : ℝ, 0 < t ∧ (1 / 4 : ℝ) ≤ circ (t * a) ∧ (1 / 4 : ℝ) ≤ circ (t * u) ∧
      (1 / 4 : ℝ) ≤ circ (t * v) := by
  have ha' : (0 : ℝ) < a := Nat.cast_pos.mpr ha
  have hu' : (0 : ℝ) < u := Nat.cast_pos.mpr hu
  have hv' : (0 : ℝ) < v := Nat.cast_pos.mpr hv
  -- if some time is safe for all three, we are done
  by_cases hdone : ∃ t : ℝ,
      Int.fract ((u : ℝ) * t) ∈ Set.Icc (1 / 4) (3 / 4) ∧
      Int.fract ((v : ℝ) * t) ∈ Set.Icc (1 / 4) (3 / 4) ∧
      Int.fract ((a : ℝ) * t) ∈ Set.Icc (1 / 4) (3 / 4)
  · obtain ⟨t, hut, hvt, hat⟩ := hdone
    have ht0 : t ≠ 0 := by
      rintro rfl
      rw [mul_zero, Int.fract_zero] at hvt
      exact absurd (Set.mem_Icc.mp hvt).1 (by norm_num)
    refine ⟨|t|, abs_pos.mpr ht0, ?_, ?_, ?_⟩
    · rw [circ_abs_mul, mul_comm]; exact (circ_ge_quarter_fract _).mpr hat
    · rw [circ_abs_mul, mul_comm]; exact (circ_ge_quarter_fract _).mpr hut
    · rw [circ_abs_mul, mul_comm]; exact (circ_ge_quarter_fract _).mpr hvt
  push_neg at hdone
  -- otherwise `a` is never safe while `u,v` are: `|off a| < 1/4` on safe times
  have hns : ∀ t : ℝ, Int.fract ((u : ℝ) * t) ∈ Set.Icc (1 / 4) (3 / 4) →
      Int.fract ((v : ℝ) * t) ∈ Set.Icc (1 / 4) (3 / 4) → |off a t| < 1 / 4 := by
    intro t hut hvt
    have hnot : ¬ Int.fract ((a : ℝ) * t) ∈ Set.Icc (1 / 4) (3 / 4) :=
      hdone t hut hvt
    rw [← circ_ge_quarter_fract] at hnot
    rw [abs_off]
    exact not_le.mp hnot
  -- `two_moving` gives `τ₀` with `u,v` at `≥ 1/3` — interior of the safe zone
  obtain ⟨τ₀, -, huτ, hvτ⟩ := two_moving hu' hv'
  have huτ3 : Int.fract ((u : ℝ) * τ₀) ∈ Set.Icc (1 / 3) (2 / 3) := by
    have h := fract_mem_third (x := (u : ℝ) * τ₀)
    rw [mul_comm] at huτ
    exact h huτ
  have hvτ3 : Int.fract ((v : ℝ) * τ₀) ∈ Set.Icc (1 / 3) (2 / 3) := by
    have h := fract_mem_third (x := (v : ℝ) * τ₀)
    rw [mul_comm] at hvτ
    exact h hvτ
  have huτ4 : Int.fract ((u : ℝ) * τ₀) ∈ Set.Icc (1 / 4) (3 / 4) :=
    ⟨by linarith [huτ3.1], by linarith [huτ3.2]⟩
  have hvτ4 : Int.fract ((v : ℝ) * τ₀) ∈ Set.Icc (1 / 4) (3 / 4) :=
    ⟨by linarith [hvτ3.1], by linarith [hvτ3.2]⟩
  -- seed: a safe time with `off a ≠ 0`
  set ε₁ : ℝ := min (min (1 / (24 * (u : ℝ))) (1 / (24 * (v : ℝ))))
    (1 / (8 * (a : ℝ))) with hε₁def
  have hε₁ : 0 < ε₁ := by
    rw [hε₁def]
    refine lt_min (lt_min ?_ ?_) ?_ <;> positivity
  have huε : (u : ℝ) * ε₁ ≤ 1 / 24 := by
    have h : ε₁ ≤ 1 / (24 * (u : ℝ)) := (min_le_left _ _).trans (min_le_left _ _)
    calc (u : ℝ) * ε₁ ≤ u * (1 / (24 * u)) := by gcongr
      _ = 1 / 24 := by field_simp
  have hvε : (v : ℝ) * ε₁ ≤ 1 / 24 := by
    have h : ε₁ ≤ 1 / (24 * (v : ℝ)) := (min_le_left _ _).trans (min_le_right _ _)
    calc (v : ℝ) * ε₁ ≤ v * (1 / (24 * v)) := by gcongr
      _ = 1 / 24 := by field_simp
  have haε : (a : ℝ) * ε₁ ≤ 1 / 8 := by
    have h : ε₁ ≤ 1 / (8 * (a : ℝ)) := min_le_right _ _
    calc (a : ℝ) * ε₁ ≤ a * (1 / (8 * a)) := by gcongr
      _ = 1 / 8 := by field_simp
  have seed_or :
      (∃ t : ℝ, Int.fract ((u : ℝ) * t) ∈ Set.Icc (1 / 4) (3 / 4) ∧
        Int.fract ((v : ℝ) * t) ∈ Set.Icc (1 / 4) (3 / 4) ∧ 0 < off a t) ∨
      (∃ t : ℝ, Int.fract ((u : ℝ) * t) ∈ Set.Icc (1 / 4) (3 / 4) ∧
        Int.fract ((v : ℝ) * t) ∈ Set.Icc (1 / 4) (3 / 4) ∧ off a t < 0) := by
    rcases lt_trichotomy (off a τ₀) 0 with hoff | hoff | hoff
    · exact Or.inr ⟨τ₀, huτ4, hvτ4, hoff⟩
    · -- `off a τ₀ = 0`: perturb to `τ₀ + ε₁`, which keeps `u,v` safe and has
      -- `off a = a·ε₁ > 0` since `a·τ₀` is an integer.
      left
      have huε0 : 0 ≤ (u : ℝ) * ε₁ := mul_nonneg (Nat.cast_nonneg u) hε₁.le
      have hvε0 : 0 ≤ (v : ℝ) * ε₁ := mul_nonneg (Nat.cast_nonneg v) hε₁.le
      refine ⟨τ₀ + ε₁, ?_, ?_, ?_⟩
      · rw [fract_add_shift]
        have hself : Int.fract (Int.fract ((u : ℝ) * τ₀) + (u : ℝ) * ε₁) =
            Int.fract ((u : ℝ) * τ₀) + (u : ℝ) * ε₁ :=
          Int.fract_eq_self.mpr ⟨by linarith [huτ3.1, huε0], by linarith [huτ3.2, huε]⟩
        rw [hself]
        exact ⟨by linarith [huτ3.1, huε0], by linarith [huτ3.2, huε]⟩
      · rw [fract_add_shift]
        have hself : Int.fract (Int.fract ((v : ℝ) * τ₀) + (v : ℝ) * ε₁) =
            Int.fract ((v : ℝ) * τ₀) + (v : ℝ) * ε₁ :=
          Int.fract_eq_self.mpr ⟨by linarith [hvτ3.1, hvε0], by linarith [hvτ3.2, hvε]⟩
        rw [hself]
        exact ⟨by linarith [hvτ3.1, hvε0], by linarith [hvτ3.2, hvε]⟩
      · have h0 : (a : ℝ) * τ₀ = (round ((a : ℝ) * τ₀) : ℝ) := by
          rw [off, sub_eq_zero] at hoff
          exact hoff
        have hmul : (a : ℝ) * (τ₀ + ε₁) =
            (round ((a : ℝ) * τ₀) : ℝ) + (a : ℝ) * ε₁ := by
          rw [← h0]
          ring
        have hround : round ((a : ℝ) * (τ₀ + ε₁)) = round ((a : ℝ) * τ₀) := by
          rw [hmul]
          apply round_of_quarter
          · linarith [mul_pos ha' hε₁]
          · linarith [haε]
        rw [off, hround, hmul]
        linarith [mul_pos ha' hε₁]
    · exact Or.inl ⟨τ₀, huτ4, hvτ4, hoff⟩
  rcases seed_or with ⟨ts, htu, htv, hoff⟩ | ⟨ts, htu, htv, hoff⟩
  · -- positive seed: maximize `off a` over the finite top-boundary set
    set Ftop : Finset ℝ := (topBdry u ∪ topBdry v).filter fun β =>
        Int.fract ((u : ℝ) * β) ∈ Set.Icc (1 / 4) (3 / 4) ∧
        Int.fract ((v : ℝ) * β) ∈ Set.Icc (1 / 4) (3 / 4) ∧ 0 < off a β
      with hFtopdef
    obtain ⟨β₀, hβ₀, hβ₀u, hβ₀v, hβ₀le⟩ := forward_endpoint ha hu hv hns htu htv
    have hFne : Ftop.Nonempty := by
      refine ⟨β₀, ?_⟩
      rw [hFtopdef, Finset.mem_filter]
      exact ⟨Finset.mem_union.mpr hβ₀, hβ₀u, hβ₀v, lt_of_lt_of_le hoff hβ₀le⟩
    obtain ⟨t₀, ht₀mem, ht₀max⟩ := Ftop.exists_max_image (off a) hFne
    rw [hFtopdef, Finset.mem_filter] at ht₀mem
    obtain ⟨ht₀bd, ht₀u, ht₀v, ht₀pos⟩ := ht₀mem
    have ht₀a_lt : off a t₀ < 1 / 4 := by
      have h := hns t₀ ht₀u ht₀v
      rwa [abs_of_pos ht₀pos] at h
    have hfa : Int.fract ((a : ℝ) * t₀) = off a t₀ := fract_eq_off ht₀pos.le
    have hmax : ∀ t : ℝ, Int.fract ((u : ℝ) * t) ∈ Set.Icc (1 / 4) (3 / 4) →
        Int.fract ((v : ℝ) * t) ∈ Set.Icc (1 / 4) (3 / 4) →
        Int.fract ((a : ℝ) * t) < 1 / 4 →
        Int.fract ((a : ℝ) * t) ≤ Int.fract ((a : ℝ) * t₀) := by
      intro t hut hvt hat
      rcases lt_or_ge 0 (off a t) with hpos | hnonpos
      · obtain ⟨β, hβ, hβu, hβv, hβle⟩ := forward_endpoint ha hu hv hns hut hvt
        have hβF : β ∈ Ftop := Finset.mem_filter.mpr
          ⟨Finset.mem_union.mpr hβ, hβu, hβv, lt_of_lt_of_le hpos hβle⟩
        have hβmax := ht₀max β hβF
        rw [hfa, fract_eq_off hpos.le]
        exact hβle.trans hβmax
      · rcases eq_or_lt_of_le hnonpos with hz | hneg
        · have hz' : Int.fract ((a : ℝ) * t) = 0 := by
            have h2 : (a : ℝ) * t = (round ((a : ℝ) * t) : ℝ) := by
              rw [off, sub_eq_zero] at hz
              exact hz
            rw [h2]
            simp
          rw [hz']
          linarith [ht₀pos]
        · rw [fract_eq_one_add_off hneg] at hat
          have hbound := hns t hut hvt
          rw [abs_of_neg hneg] at hbound
          linarith
    rcases Finset.mem_union.mp ht₀bd with htu' | htv'
    · obtain ⟨l, -, rfl⟩ := Finset.mem_image.mp htu'
      exact renault_core ha hu hv ha4 hpar (by rw [hfa]; exact ht₀pos)
        (by rw [hfa]; exact ht₀a_lt) (topBdry_pos hu) ht₀v hmax
    · obtain ⟨l, -, rfl⟩ := Finset.mem_image.mp htv'
      have hpar' : ¬ (2 ∣ v ∧ 2 ∣ u) := fun h => hpar ⟨h.2, h.1⟩
      obtain ⟨t, ht, h1, h2, h3⟩ := renault_core ha hv hu ha4 hpar'
        (by rw [hfa]; exact ht₀pos) (by rw [hfa]; exact ht₀a_lt)
        (topBdry_pos hv) ht₀u (fun t hv' hu' hlt => hmax t hu' hv' hlt)
      exact ⟨t, ht, h1, h3, h2⟩
  · -- negative seed: minimize `off a` over the bottom boundary, then reflect
    set Fbot : Finset ℝ := (botBdry u ∪ botBdry v).filter fun β =>
        Int.fract ((u : ℝ) * β) ∈ Set.Icc (1 / 4) (3 / 4) ∧
        Int.fract ((v : ℝ) * β) ∈ Set.Icc (1 / 4) (3 / 4) ∧ off a β < 0
      with hFbotdef
    obtain ⟨γ₀, hγ₀, hγ₀u, hγ₀v, hγ₀le⟩ := backward_endpoint ha hu hv hns htu htv
    have hFne : Fbot.Nonempty := by
      refine ⟨γ₀, ?_⟩
      rw [hFbotdef, Finset.mem_filter]
      exact ⟨Finset.mem_union.mpr hγ₀, hγ₀u, hγ₀v, hγ₀le.trans_lt hoff⟩
    obtain ⟨t₁, ht₁mem, ht₁min⟩ := Fbot.exists_max_image (fun β => -off a β) hFne
    rw [hFbotdef, Finset.mem_filter] at ht₁mem
    obtain ⟨ht₁bd, ht₁u, ht₁v, ht₁neg⟩ := ht₁mem
    have hfa1 : Int.fract ((a : ℝ) * t₁) = 1 + off a t₁ := fract_eq_one_add_off ht₁neg
    have hoff1 : -off a t₁ < 1 / 4 := by
      have h := hns t₁ ht₁u ht₁v
      rwa [abs_of_neg ht₁neg] at h
    set s₀ := -t₁ with hs₀def
    have hfa : Int.fract ((a : ℝ) * s₀) = -off a t₁ := by
      have h2 : (a : ℝ) * s₀ = -((a : ℝ) * t₁) := by rw [hs₀def]; ring
      rw [h2, Int.fract_neg (by rw [hfa1]; linarith [hoff1]), hfa1]
      ring
    have hmax : ∀ t : ℝ, Int.fract ((u : ℝ) * t) ∈ Set.Icc (1 / 4) (3 / 4) →
        Int.fract ((v : ℝ) * t) ∈ Set.Icc (1 / 4) (3 / 4) →
        Int.fract ((a : ℝ) * t) < 1 / 4 →
        Int.fract ((a : ℝ) * t) ≤ Int.fract ((a : ℝ) * s₀) := by
      intro t hut hvt hat
      rcases lt_or_ge 0 (off a t) with hpos | hnonpos
      · have hutn : Int.fract ((u : ℝ) * (-t)) ∈ Set.Icc (1 / 4) (3 / 4) := by
          have h2 : (u : ℝ) * (-t) = -((u : ℝ) * t) := by ring
          rw [h2, Int.fract_neg]
          · obtain ⟨h1, h3⟩ := Set.mem_Icc.mp hut
            exact ⟨by linarith, by linarith⟩
          · intro hz
            rw [hz] at hut
            exact absurd (Set.mem_Icc.mp hut).1 (by norm_num)
        have hvtn : Int.fract ((v : ℝ) * (-t)) ∈ Set.Icc (1 / 4) (3 / 4) := by
          have h2 : (v : ℝ) * (-t) = -((v : ℝ) * t) := by ring
          rw [h2, Int.fract_neg]
          · obtain ⟨h1, h3⟩ := Set.mem_Icc.mp hvt
            exact ⟨by linarith, by linarith⟩
          · intro hz
            rw [hz] at hvt
            exact absurd (Set.mem_Icc.mp hvt).1 (by norm_num)
        obtain ⟨γ, hγ, hγu, hγv, hγle⟩ := backward_endpoint ha hu hv hns hutn hvtn
        rw [off_neg (hns t hut hvt)] at hγle
        have hγF : γ ∈ Fbot := by
          rw [hFbotdef, Finset.mem_filter]
          exact ⟨Finset.mem_union.mpr hγ, hγu, hγv, by linarith [hpos]⟩
        have hγmin := ht₁min γ hγF
        rw [hfa, fract_eq_off hpos.le]
        linarith [hγle, hγmin]
      · rcases eq_or_lt_of_le hnonpos with hz | hneg
        · have hz' : Int.fract ((a : ℝ) * t) = 0 := by
            have h2 : (a : ℝ) * t = (round ((a : ℝ) * t) : ℝ) := by
              rw [off, sub_eq_zero] at hz
              exact hz
            rw [h2]
            simp
          rw [hz']
          linarith
        · rw [fract_eq_one_add_off hneg] at hat
          have hbound := hns t hut hvt
          rw [abs_of_neg hneg] at hbound
          linarith
    rcases Finset.mem_union.mp ht₁bd with htu' | htv'
    · obtain ⟨l, -, rfl⟩ := Finset.mem_image.mp htu'
      have h1q : Int.fract ((u : ℝ) * (((4 * l + 1 : ℕ) : ℝ) / (4 * (u : ℝ)))) =
          1 / 4 := botBdry_pos hu
      have hus : Int.fract ((u : ℝ) * s₀) = 3 / 4 := by
        have h2 : (u : ℝ) * s₀ =
            -((u : ℝ) * (((4 * l + 1 : ℕ) : ℝ) / (4 * (u : ℝ)))) := by
          rw [hs₀def]; ring
        rw [h2, Int.fract_neg (by rw [h1q]; norm_num), h1q]
        norm_num
      have hvf : Int.fract ((v : ℝ) * (((4 * l + 1 : ℕ) : ℝ) / (4 * (u : ℝ)))) ≠ 0 := by
        intro hz
        rw [hz] at ht₁v
        exact absurd ht₁v.1 (by norm_num)
      have hvs : Int.fract ((v : ℝ) * s₀) ∈ Set.Icc (1 / 4) (3 / 4) := by
        have h2 : (v : ℝ) * s₀ =
            -((v : ℝ) * (((4 * l + 1 : ℕ) : ℝ) / (4 * (u : ℝ)))) := by
          rw [hs₀def]; ring
        rw [h2, Int.fract_neg hvf]
        obtain ⟨hl, hh⟩ := ht₁v
        exact ⟨by linarith, by linarith⟩
      exact renault_core ha hu hv ha4 hpar
        (by rw [hfa]; linarith [ht₁neg]) (by rw [hfa]; linarith) hus hvs hmax
    · obtain ⟨l, -, rfl⟩ := Finset.mem_image.mp htv'
      have h1q : Int.fract ((v : ℝ) * (((4 * l + 1 : ℕ) : ℝ) / (4 * (v : ℝ)))) =
          1 / 4 := botBdry_pos hv
      have hvs : Int.fract ((v : ℝ) * s₀) = 3 / 4 := by
        have h2 : (v : ℝ) * s₀ =
            -((v : ℝ) * (((4 * l + 1 : ℕ) : ℝ) / (4 * (v : ℝ)))) := by
          rw [hs₀def]; ring
        rw [h2, Int.fract_neg (by rw [h1q]; norm_num), h1q]
        norm_num
      have huf : Int.fract ((u : ℝ) * (((4 * l + 1 : ℕ) : ℝ) / (4 * (v : ℝ)))) ≠ 0 := by
        intro hz
        rw [hz] at ht₁u
        exact absurd ht₁u.1 (by norm_num)
      have hus : Int.fract ((u : ℝ) * s₀) ∈ Set.Icc (1 / 4) (3 / 4) := by
        have h2 : (u : ℝ) * s₀ =
            -((u : ℝ) * (((4 * l + 1 : ℕ) : ℝ) / (4 * (v : ℝ)))) := by
          rw [hs₀def]; ring
        rw [h2, Int.fract_neg huf]
        obtain ⟨hl, hh⟩ := ht₁u
        exact ⟨by linarith, by linarith⟩
      have hpar' : ¬ (2 ∣ v ∧ 2 ∣ u) := fun h => hpar ⟨h.2, h.1⟩
      obtain ⟨t, ht, h1, h2, h3⟩ := renault_core ha hv hu ha4 hpar'
        (by rw [hfa]; linarith [ht₁neg]) (by rw [hfa]; linarith) hvs hus
        (fun t hv' hu' hlt => hmax t hu' hv' hlt)
      exact ⟨t, ht, h1, h3, h2⟩

/-- **LRC(4), integer speeds.** Any `≤ 3` positive integer speeds admit a time
at which every runner is at circular distance `≥ 1/4` from the origin. -/
theorem lrc4_int (D : Finset ℕ) (hpos : ∀ d ∈ D, 0 < d) (hcard : D.card ≤ 3) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ D, (1 / 4 : ℝ) ≤ circ (t * d) := by
  have key : ∀ n : ℕ, ∀ D : Finset ℕ, D.sum id = n → (∀ d ∈ D, 0 < d) →
      D.card ≤ 3 → ∃ t : ℝ, 0 < t ∧ ∀ d ∈ D, (1 / 4 : ℝ) ≤ circ (t * d) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n IH =>
      intro D hDn hpos hcard
      have hcases : D.card = 0 ∨ D.card = 1 ∨ D.card = 2 ∨ D.card = 3 := by omega
      rcases hcases with h0 | h1 | h2 | h3
      · rw [Finset.card_eq_zero.mp h0]
        exact ⟨1, one_pos, fun d hd => by simp at hd⟩
      · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h1
        obtain ⟨t, ht, ha1, -⟩ :=
          two_moving (show (0 : ℝ) < a by exact_mod_cast hpos a (by simp))
            (show (0 : ℝ) < a by exact_mod_cast hpos a (by simp))
        exact ⟨t, ht, fun d hd => by
          rw [Finset.mem_singleton] at hd
          subst hd
          linarith⟩
      · obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp h2
        obtain ⟨t, ht, ha1, hb1⟩ :=
          two_moving (show (0 : ℝ) < a by exact_mod_cast hpos a (by simp))
            (show (0 : ℝ) < b by exact_mod_cast hpos b (by simp))
        refine ⟨t, ht, fun d hd => ?_⟩
        rw [Finset.mem_insert, Finset.mem_singleton] at hd
        rcases hd with rfl | rfl <;> linarith
      · obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp h3
        have hpa : 0 < a := hpos a (by simp)
        have hpb : 0 < b := hpos b (by simp)
        have hpc : 0 < c := hpos c (by simp)
        have hsumabc : ({a, b, c} : Finset ℕ).sum id = a + b + c := by
          rw [Finset.sum_insert (by simp [hab, hac]),
            Finset.sum_insert (by simp [hbc]), Finset.sum_singleton]
          show a + (b + c) = a + b + c
          ring
        by_cases hall : 2 ∣ a ∧ 2 ∣ b ∧ 2 ∣ c
        · -- all even: halve all speeds and apply the induction hypothesis
          have h2a : 2 * (a / 2) = a := Nat.mul_div_cancel' hall.1
          have h2b : 2 * (b / 2) = b := Nat.mul_div_cancel' hall.2.1
          have h2c : 2 * (c / 2) = c := Nat.mul_div_cancel' hall.2.2
          -- halves are distinct: halving is injective on even numbers
          have hhalf_ab : a / 2 ≠ b / 2 := fun h => hab (by
            have h2 := congrArg (2 * ·) h
            rwa [h2a, h2b] at h2)
          have hhalf_ac : a / 2 ≠ c / 2 := fun h => hac (by
            have h2 := congrArg (2 * ·) h
            rwa [h2a, h2c] at h2)
          have hhalf_bc : b / 2 ≠ c / 2 := fun h => hbc (by
            have h2 := congrArg (2 * ·) h
            rwa [h2b, h2c] at h2)
          set D' : Finset ℕ := {a / 2, b / 2, c / 2}
          have hD'pos : ∀ d ∈ D', 0 < d := by
            intro d hd
            simp only [D', Finset.mem_insert, Finset.mem_singleton] at hd
            rcases hd with rfl | rfl | rfl
            · exact Nat.div_pos (Nat.le_of_dvd hpa hall.1) (by norm_num)
            · exact Nat.div_pos (Nat.le_of_dvd hpb hall.2.1) (by norm_num)
            · exact Nat.div_pos (Nat.le_of_dvd hpc hall.2.2) (by norm_num)
          have hD'card : D'.card ≤ 3 := by
            rw [Finset.card_insert_of_notMem (by simp [hhalf_ab, hhalf_ac]),
              Finset.card_insert_of_notMem (by simp [hhalf_bc]),
              Finset.card_singleton]
          have hD'sum : D'.sum id = a / 2 + b / 2 + c / 2 := by
            rw [Finset.sum_insert (by simp [hhalf_ab, hhalf_ac]),
              Finset.sum_insert (by simp [hhalf_bc]), Finset.sum_singleton]
            show a / 2 + (b / 2 + c / 2) = a / 2 + b / 2 + c / 2
            ring
          have hsum : D'.sum id < n := by
            rw [hsumabc] at hDn
            rw [hD'sum]
            omega
          obtain ⟨t', ht', h'⟩ := IH _ hsum D' rfl hD'pos hD'card
          refine ⟨t' / 2, half_pos ht', fun d hd => ?_⟩
          simp only [Finset.mem_insert, Finset.mem_singleton] at hd
          have half_eq : ∀ x : ℕ, 2 ∣ x →
              (t' / 2) * (x : ℝ) = t' * ((x / 2 : ℕ) : ℝ) := by
            intro x hx
            have hcast : ((x / 2 : ℕ) : ℝ) = (x : ℝ) / 2 := by
              rw [eq_div_iff (by norm_num : (2 : ℝ) ≠ 0), mul_comm]
              exact_mod_cast Nat.mul_div_cancel' hx
            rw [hcast]
            ring
          rcases hd with hda | hdb | hdc
          · rw [hda, half_eq a hall.1]
            exact h' _ (by simp [D'])
          · rw [hdb, half_eq b hall.2.1]
            exact h' _ (by simp [D'])
          · rw [hdc, half_eq c hall.2.2]
            exact h' _ (by simp [D'])
        · -- not all even: case on residues mod 4
          by_cases h4a : 4 ∣ a
          · have hpar : ¬ (2 ∣ b ∧ 2 ∣ c) := fun ⟨hb2, hc2⟩ =>
              hall ⟨dvd_trans (by norm_num : (2 : ℕ) ∣ 4) h4a, hb2, hc2⟩
            obtain ⟨t, ht, ha1, hu1, hv1⟩ := renault_driver hpa hpb hpc h4a hpar
            refine ⟨t, ht, fun d hd => ?_⟩
            simp only [Finset.mem_insert, Finset.mem_singleton] at hd
            rcases hd with rfl | rfl | rfl
            · exact ha1
            · exact hu1
            · exact hv1
          · by_cases h4b : 4 ∣ b
            · have hpar : ¬ (2 ∣ a ∧ 2 ∣ c) := fun ⟨ha2, hc2⟩ =>
                hall ⟨ha2, dvd_trans (by norm_num : (2 : ℕ) ∣ 4) h4b, hc2⟩
              obtain ⟨t, ht, ha1, hu1, hv1⟩ := renault_driver hpb hpa hpc h4b hpar
              refine ⟨t, ht, fun d hd => ?_⟩
              simp only [Finset.mem_insert, Finset.mem_singleton] at hd
              rcases hd with rfl | rfl | rfl
              · exact hu1
              · exact ha1
              · exact hv1
            · by_cases h4c : 4 ∣ c
              · have hpar : ¬ (2 ∣ a ∧ 2 ∣ b) := fun ⟨ha2, hb2⟩ =>
                  hall ⟨ha2, hb2, dvd_trans (by norm_num : (2 : ℕ) ∣ 4) h4c⟩
                obtain ⟨t, ht, ha1, hu1, hv1⟩ := renault_driver hpc hpa hpb h4c hpar
                refine ⟨t, ht, fun d hd => ?_⟩
                simp only [Finset.mem_insert, Finset.mem_singleton] at hd
                rcases hd with rfl | rfl | rfl
                · exact hu1
                · exact hv1
                · exact ha1
              · -- no element divisible by 4: `t = 1/4` works
                refine ⟨1 / 4, by norm_num, fun d hd => ?_⟩
                have h4 : ¬ 4 ∣ d := by
                  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
                  rcases hd with rfl | rfl | rfl <;> assumption
                have hmod0 : d % 4 ≠ 0 := fun h => h4 (Nat.dvd_of_mod_eq_zero h)
                have hmodlt : d % 4 < 4 := Nat.mod_lt d (by norm_num)
                have heq : Int.fract ((1 / 4 : ℝ) * (d : ℝ)) =
                    ((d % 4 : ℕ) : ℝ) / 4 := by
                  have h1 : (d : ℝ) = 4 * ((d / 4 : ℕ) : ℝ) + ((d % 4 : ℕ) : ℝ) := by
                    have h2 : ((4 * (d / 4) + d % 4 : ℕ) : ℝ) = (d : ℝ) := by
                      exact_mod_cast (Nat.div_add_mod d 4)
                    push_cast at h2
                    linarith [h2]
                  rw [show (1 / 4 : ℝ) * (d : ℝ) =
                      ((d / 4 : ℕ) : ℝ) + ((d % 4 : ℕ) : ℝ) / 4 by
                    rw [h1]; ring]
                  rw [Int.fract_natCast_add, Int.fract_eq_self]
                  constructor
                  · positivity
                  · rw [div_lt_one (by norm_num : (0 : ℝ) < 4)]
                    exact_mod_cast hmodlt
                apply (circ_ge_quarter_fract _).mpr
                rw [heq, Set.mem_Icc]
                interval_cases h : d % 4
                · exact absurd rfl hmod0
                · constructor <;> norm_num
                · constructor <;> norm_num
                · constructor <;> norm_num
  exact key _ D rfl hpos hcard

end
