/-
Copyright (c) 2026 Research07 contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Research07 contributors
-/
import Mathlib
import Research07.LRC6.Setup
import Research07.LRC6.Extremize

/-!
# improving-move drivers

The reusable contradiction engine behind Renault's `(λ,α)` improving moves.
Given the extremal time `tstar` (maximizing the anchor's circular distance over
guard-safe times, from `renault6_maximize`), a `(λ,α)`-shifted time
`s = λ·τ + α/6` that keeps every guard safe produces a contradiction:

* `λ ≥ 2`: `circ (a·s) = circ (λ·x_a)` strictly exceeds `circ (a·tstar) = x_a`,
  contradicting maximality (`improve_ge_two_contra`).
* `λ = 1`: `x_a(s) = x_a(tstar)` but all guards are strictly inside, so a small
  perturbation `s + η` improves the anchor (`improve_eq_one_contra`).
-/

noncomputable section

/-- `circ x = fract x` when `fract x < 1/2`. -/
theorem circ_of_fract_lt_half {x : ℝ} (h : Int.fract x < 1 / 2) :
    circ x = Int.fract x := by
  rw [circ_eq, abs_sub_round_eq_min, min_eq_left (by linarith)]

/-- The `λ ≥ 2` improving move: if `s = λ·τ + α/6` keeps all guards safe and the
anchor's fractional part is unchanged by the `τ`-shift, then `s` strictly beats
the extremal `tstar` — contradicting `circ`-maximality. -/
theorem improve_ge_two_contra {a : ℕ} (ha : 6 ∣ a) (guards : Finset ℕ)
    {tstar τ : ℝ} {lam al : ℕ}
    (hxa : Int.fract ((a : ℝ) * tstar) ∈ Set.Ioo 0 (1 / 6))
    (hτa : Int.fract ((a : ℝ) * τ) = Int.fract ((a : ℝ) * tstar))
    (hmax : ∀ t : ℝ,
      (∀ d ∈ guards, Int.fract ((d : ℝ) * t) ∈ Set.Icc (1 / 6) (5 / 6)) →
        circ ((a : ℝ) * t) ≤ circ ((a : ℝ) * tstar))
    (hsafe : ∀ d ∈ guards,
      Int.fract ((d : ℝ) * ((lam : ℝ) * τ + (al : ℝ) / 6)) ∈ Set.Icc (1 / 6) (5 / 6))
    (hl : 2 ≤ lam) (hl5 : lam ≤ 5) : False := by
  set x := Int.fract ((a : ℝ) * tstar) with hx
  have hs : circ ((a : ℝ) * ((lam : ℝ) * τ + (al : ℝ) / 6)) =
      circ ((lam : ℝ) * Int.fract ((a : ℝ) * τ)) := circ_anchor_lambda ha τ lam al
  rw [hτa] at hs
  have hct : circ ((a : ℝ) * tstar) = x :=
    circ_of_fract_lt_half (by linarith [hxa.2])
  have hgt : circ ((a : ℝ) * ((lam : ℝ) * τ + (al : ℝ) / 6)) > circ ((a : ℝ) * tstar) := by
    rw [hs, hct]
    exact circ_lambda_gt hxa.1 hxa.2 hl hl5
  have hle := hmax ((lam : ℝ) * τ + (al : ℝ) / 6) hsafe
  linarith

/-- The `λ = 1` improving move: if `s = τ + α/6` keeps all guards in
`[1/6, 5/6)` (strict below the top) and preserves the anchor's fractional part,
a perturbation `s + η` strictly improves the anchor — contradicting maximality. -/
theorem improve_eq_one_contra {a : ℕ} (ha : 6 ∣ a) (guards : Finset ℕ)
    (hguards : guards.Nonempty) (hpos : ∀ d ∈ guards, 0 < d)
    {tstar τ : ℝ} {al : ℕ}
    (hxa : Int.fract ((a : ℝ) * tstar) ∈ Set.Ioo 0 (1 / 6))
    (hτa : Int.fract ((a : ℝ) * τ) = Int.fract ((a : ℝ) * tstar))
    (hmax : ∀ t : ℝ,
      (∀ d ∈ guards, Int.fract ((d : ℝ) * t) ∈ Set.Icc (1 / 6) (5 / 6)) →
        circ ((a : ℝ) * t) ≤ circ ((a : ℝ) * tstar))
    (hsafe : ∀ d ∈ guards,
      Int.fract ((d : ℝ) * (τ + (al : ℝ) / 6)) ∈ Set.Ico (1 / 6) (5 / 6)) : False := by
  classical
  set s : ℝ := τ + (al : ℝ) / 6 with hs
  have hapos : 0 < a := Nat.pos_of_ne_zero fun h0 ↦ by
    rw [h0] at hxa
    norm_num at hxa
  -- the anchor is preserved: `fract (a·s) = fract (a·tstar)`
  have hsa : Int.fract ((a : ℝ) * s) = Int.fract ((a : ℝ) * tstar) := by
    obtain ⟨m, hm⟩ := ha
    have h1 : (a : ℝ) * s = (a : ℝ) * τ + ((m * al : ℕ) : ℝ) := by
      rw [hs]
      have : (a : ℝ) * (al : ℝ) / 6 = ((m * al : ℕ) : ℝ) := by
        rw [hm]; push_cast; field_simp
      linear_combination this
    rw [h1, Int.fract_add_natCast, hτa]
  -- perturb: `exists_improve_eq_one` gives `s'` with guards safe and larger anchor
  obtain ⟨s', hgs', hbig, hlt⟩ := exists_improve_eq_one guards hguards hpos hapos
    (fun d hd => hsafe d hd) (by rw [hsa]; exact hxa.1) (by rw [hsa]; exact hxa.2)
  have hct : circ ((a : ℝ) * tstar) = Int.fract ((a : ℝ) * tstar) :=
    circ_of_fract_lt_half (by linarith [hxa.2])
  have hcs' : circ ((a : ℝ) * s') = Int.fract ((a : ℝ) * s') :=
    circ_of_fract_lt_half (by linarith)
  have hgt : circ ((a : ℝ) * s') > circ ((a : ℝ) * tstar) := by
    rw [hcs', hct]
    linarith [hsa ▸ hbig]
  have hle := hmax s' hgs'
  linarith

/-- `fract (c/6) = (c % 6)/6` for `c : ℤ` — the `emod` reduction for `α/6`-shift
computations. -/
theorem fract_intCast_div_six (c : ℤ) :
    Int.fract ((c : ℝ) / 6) = ((c % 6 : ℤ) : ℝ) / 6 := by
  have h1 : (c : ℝ) / 6 = (((c % 6 : ℤ) : ℝ) / 6) + ((c / 6 : ℤ) : ℝ) := by
    have h3 : (c : ℝ) = 6 * ((c / 6 : ℤ) : ℝ) + ((c % 6 : ℤ) : ℝ) := by
      have h4 : (c : ℤ) = 6 * (c / 6) + c % 6 := by omega
      exact_mod_cast h4
    linear_combination h3 / 6
  rw [h1, Int.fract_add_intCast]
  refine Int.fract_eq_self.mpr (Set.mem_Ico.mpr ⟨?_, ?_⟩)
  · have h4 : (0 : ℝ) ≤ (c % 6 : ℤ) := by
      exact_mod_cast (show 0 ≤ c % 6 by omega)
    linarith
  · have h5 : ((c % 6 : ℤ) : ℝ) < 6 := by
      exact_mod_cast (show c % 6 < 6 by omega)
    linarith

/-- `fract (α/6) = α/6 ∈ [1/6, 5/6]` for `1 ≤ α ≤ 5`. -/
theorem alpha_Icc {al : ℕ} (h1 : 1 ≤ al) (h5 : al ≤ 5) :
    Int.fract ((al : ℝ) / 6) ∈ Set.Icc (1 / 6) (5 / 6) := by
  have ha1 : (1 : ℝ) ≤ al := by exact_mod_cast h1
  have ha5 : (al : ℝ) ≤ 5 := by exact_mod_cast h5
  rw [Int.fract_eq_self.mpr (by constructor <;> linarith)]
  exact Set.mem_Icc.mpr ⟨by linarith, by linarith⟩

/-- `fract (α/6) ∈ [1/6, 5/6)` for `1 ≤ α ≤ 4`. -/
theorem alpha_Ico {al : ℕ} (h1 : 1 ≤ al) (h4 : al ≤ 4) :
    Int.fract ((al : ℝ) / 6) ∈ Set.Ico (1 / 6) (5 / 6) := by
  have ha1 : (1 : ℝ) ≤ al := by exact_mod_cast h1
  have ha4 : (al : ℝ) ≤ 4 := by exact_mod_cast h4
  rw [Int.fract_eq_self.mpr (by constructor <;> linarith)]
  exact Set.mem_Ico.mpr ⟨by linarith, by linarith⟩

/-- `fract (−α/6) = (6−α)/6 ∈ [1/6, 5/6]` for `1 ≤ α ≤ 5`. -/
theorem neg_alpha_Icc {al : ℕ} (h1 : 1 ≤ al) (h5 : al ≤ 5) :
    Int.fract (-((al : ℝ) / 6)) ∈ Set.Icc (1 / 6) (5 / 6) := by
  have ha1 : (1 : ℝ) ≤ al := by exact_mod_cast h1
  have ha5 : (al : ℝ) ≤ 5 := by exact_mod_cast h5
  have hself : Int.fract ((al : ℝ) / 6) = (al : ℝ) / 6 :=
    Int.fract_eq_self.mpr (by constructor <;> linarith)
  have h0 : Int.fract ((al : ℝ) / 6) ≠ 0 := by rw [hself]; linarith
  rw [Int.fract_neg h0, hself]
  exact Set.mem_Icc.mpr ⟨by linarith, by linarith⟩

/-- `fract (−α/6) ∈ [1/6, 5/6)` for `2 ≤ α ≤ 5`. -/
theorem neg_alpha_Ico {al : ℕ} (h2 : 2 ≤ al) (h5 : al ≤ 5) :
    Int.fract (-((al : ℝ) / 6)) ∈ Set.Ico (1 / 6) (5 / 6) := by
  have ha2 : (2 : ℝ) ≤ al := by exact_mod_cast h2
  have ha5 : (al : ℝ) ≤ 5 := by exact_mod_cast h5
  have hself : Int.fract ((al : ℝ) / 6) = (al : ℝ) / 6 :=
    Int.fract_eq_self.mpr (by constructor <;> linarith)
  have h0 : Int.fract ((al : ℝ) / 6) ≠ 0 := by rw [hself]; linarith
  rw [Int.fract_neg h0, hself]
  exact Set.mem_Ico.mpr ⟨by linarith, by linarith⟩

/-- `fract (e·α/6) ∈ [1/6, 5/6]` for `e = ±1`, `1 ≤ α ≤ 5`: the `e₂`-anchor's
safety at the improving-move time. -/
theorem signed_alpha_Icc {e : ℤ} (he : e = 1 ∨ e = -1) {al : ℕ}
    (h1 : 1 ≤ al) (h5 : al ≤ 5) :
    Int.fract ((e : ℝ) * (al : ℝ) / 6) ∈ Set.Icc (1 / 6) (5 / 6) := by
  rcases he with rfl | rfl
  · rw [Int.cast_one, one_mul]
    exact alpha_Icc h1 h5
  · rw [Int.cast_neg, Int.cast_one, neg_one_mul, neg_div]
    exact neg_alpha_Icc h1 h5

end
