/-
Copyright (c) 2026 Research07 contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Research07 contributors
-/
import Mathlib
import Research07.LRC3.Circ
import Research07.LRC5.IntCase

/-!
# LRC integer case for ≤5 speeds, threshold 1/6: shared infrastructure

Renault's argument (J. Renault, *View-obstruction: a shorter proof for
6 lonely runners*, Discrete Math. 287 (2004) 93–101), formalized via finite
candidate sets of sixth-boundary times, extending the `LRC4` architecture
(`off`, `fract_add_shift`, forward/backward endpoints, boundary finsets).

Positions are `xᵢ(t) = Int.fract (vᵢ * t)`; runner `i` is *safe* when
`xᵢ(t) ∈ Icc (1/6) (5/6)`, equivalently `1/6 ≤ circ (vᵢ * t)`.
-/

noncomputable section

/-- `circ x ≥ 1/6` iff `fract x ∈ [1/6, 5/6]`. -/
theorem circ_ge_sixth_fract (x : ℝ) :
    (1 / 6 : ℝ) ≤ circ x ↔ Int.fract x ∈ Set.Icc (1 / 6) (5 / 6) := by
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

/-- `circ x ≥ 1/6` iff `x` lies in some sixth-gap arc `[k + 1/6, k + 5/6]`. -/
theorem circ_ge_sixth_iff (x : ℝ) :
    (1 / 6 : ℝ) ≤ circ x ↔
      ∃ k : ℤ, x ∈ Set.Icc ((k : ℝ) + 1 / 6) ((k : ℝ) + 5 / 6) := by
  rw [circ_ge_sixth_fract, Set.mem_Icc]
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
        constructor <;> linarith
      have h4 : Int.fract (x - (k : ℝ)) = Int.fract x :=
        Int.fract_sub_intCast x k
      linarith [h4]
    constructor
    · rw [hk]; linarith
    · rw [hk]; linarith

/-- `circ x ≥ 1/5` iff `fract x ∈ [1/5, 4/5]`.  Used to lift the `lrc5_int`
seed into a `1/6`-safe neighborhood with margin `1/30`. -/
theorem circ_ge_fifth_fract (x : ℝ) :
    (1 / 5 : ℝ) ≤ circ x ↔ Int.fract x ∈ Set.Icc (1 / 5) (4 / 5) := by
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

/-- `circ` of `|t|·d` equals `circ` of `t·d`. -/
theorem circ_abs_mul (t : ℝ) (d : ℕ) :
    circ (|t| * (d : ℝ)) = circ (t * (d : ℝ)) := by
  have h : |t * (d : ℝ)| = |t| * (d : ℝ) := by
    rw [abs_mul]; simp
  rw [← circ_abs (t * (d : ℝ)), h]

/-- `fract (x + s) = fract (fract x + s)`. -/
theorem fract_self_add (x s : ℝ) :
    Int.fract (x + s) = Int.fract (Int.fract x + s) := by
  have h : x + s = Int.fract x + s + (⌊x⌋ : ℝ) := by
    have h2 := Int.self_sub_fract x
    linarith
  rw [h, Int.fract_add_intCast]

/-- Position bookkeeping: `fract (d·(t+s)) = fract (fract (d·t) + d·s)`. -/
theorem fract_add_shift (d : ℕ) (t s : ℝ) :
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
theorem fract_nat_mul (d : ℕ) (k : ℕ) (t : ℝ) :
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

/-- Improving-move position: `xᵢ(λt + α/6) = ⟨λ·xᵢ(t) + vᵢ·α/6⟩`.

This is the core bookkeeping for Renault's `λ t̄ + α/6` shifts. -/
theorem fract_improve (v : ℕ) (lam : ℕ) (al : ℕ) (t : ℝ) :
    Int.fract ((v : ℝ) * ((lam : ℝ) * t + (al : ℝ) / 6)) =
      Int.fract ((lam : ℝ) * Int.fract ((v : ℝ) * t) + (v : ℝ) * (al : ℝ) / 6) := by
  have h2 : (v : ℝ) * t = Int.fract ((v : ℝ) * t) + (⌊(v : ℝ) * t⌋ : ℝ) := by
    have h3 := Int.self_sub_fract ((v : ℝ) * t)
    linarith
  have h1 : (v : ℝ) * ((lam : ℝ) * t + (al : ℝ) / 6) =
      ((lam : ℝ) * Int.fract ((v : ℝ) * t) + (v : ℝ) * (al : ℝ) / 6) +
        (((lam : ℤ) * ⌊(v : ℝ) * t⌋ : ℤ) : ℝ) := by
    push_cast
    linear_combination (lam : ℝ) * h2
  rw [h1, Int.fract_add_intCast]

/-- For a multiple-of-6 anchor `v`, the `α/6` shift is invisible to the anchor:
`x_anchor(λt + α/6) = ⟨λ·x_anchor(t)⟩`. -/
theorem fract_improve_anchor {v : ℕ} (hv : 6 ∣ v) (lam : ℕ) (al : ℕ) (t : ℝ) :
    Int.fract ((v : ℝ) * ((lam : ℝ) * t + (al : ℝ) / 6)) =
      Int.fract ((lam : ℝ) * Int.fract ((v : ℝ) * t)) := by
  obtain ⟨m, hm⟩ := hv
  rw [fract_improve]
  have hdiv : (v : ℝ) * (al : ℝ) / 6 = ((m * al : ℕ) : ℝ) := by
    rw [hm]; push_cast; field_simp
  rw [hdiv, Int.fract_add_natCast]

/-- Guard version of the improving move: for `d ≡ e (mod 6)`,
`x_d(λτ + α/6) = ⟨λ·x_d(τ) + e·α/6⟩`.  The residue `e` replaces `d` because
`d·α/6 = e·α/6 + (d - e)·α/6` and `6 ∣ d - e` makes `(d - e)·α/6` an integer. -/
theorem fract_lambda_alpha {d : ℕ} {e : ℤ} (hde : (d : ℤ) ≡ e [ZMOD 6])
    (τ : ℝ) (lam : ℕ) (al : ℕ) :
    Int.fract ((d : ℝ) * ((lam : ℝ) * τ + (al : ℝ) / 6)) =
      Int.fract ((lam : ℝ) * Int.fract ((d : ℝ) * τ) + (e : ℝ) * (al : ℝ) / 6) := by
  rw [fract_improve]
  obtain ⟨k, hk⟩ := Int.modEq_iff_dvd.mp hde
  have h5 : (d : ℝ) * (al : ℝ) / 6 = (e : ℝ) * (al : ℝ) / 6 - (k : ℝ) * (al : ℝ) := by
    have hd : (d : ℝ) = (e : ℝ) - 6 * (k : ℝ) := by
      have h2 : (d : ℤ) = e - 6 * k := by linarith [hk]
      calc (d : ℝ) = ((d : ℤ) : ℝ) := by simp
        _ = ((e - 6 * k : ℤ) : ℝ) := by rw [h2]
        _ = (e : ℝ) - 6 * (k : ℝ) := by push_cast; ring
    rw [hd]
    field_simp
  rw [h5]
  rw [show (lam : ℝ) * Int.fract ((d : ℝ) * τ) + ((e : ℝ) * (al : ℝ) / 6 - (k : ℝ) * (al : ℝ))
        = ((lam : ℝ) * Int.fract ((d : ℝ) * τ) + (e : ℝ) * (al : ℝ) / 6) +
          (((-k) * (al : ℤ) : ℤ) : ℝ) by push_cast; ring]
  exact Int.fract_add_intCast _ _

/-- For `x ∈ (0, 1/6)` and `λ ∈ {2,…,5}`, `circ(λ·x) > x`: the anchor strictly
improves under the improving move.  This is Renault's `N(x₁(λt̄+α/6)) > N(x₁(t̄))`. -/
theorem circ_lambda_gt {x : ℝ} (hx0 : 0 < x) (hx : x < 1 / 6) {lam : ℕ}
    (h2 : 2 ≤ lam) (h5 : lam ≤ 5) : x < circ ((lam : ℝ) * x) := by
  have hl2 : (2 : ℝ) ≤ (lam : ℝ) := by exact_mod_cast h2
  have hl5 : (lam : ℝ) ≤ 5 := by exact_mod_cast h5
  have hlx0 : 0 < (lam : ℝ) * x := mul_pos (by linarith) hx0
  have hlx1 : (lam : ℝ) * x < 1 := by nlinarith [hl5, hx, hx0]
  rw [circ_eq, abs_sub_round_eq_min,
    Int.fract_eq_self.mpr ⟨hlx0.le, hlx1⟩]
  rcases lt_or_ge ((lam : ℝ) * x) (1 / 2) with h | h
  · rw [min_eq_left (by linarith)]
    nlinarith [hl2, hx0]
  · rw [min_eq_right (by linarith)]
    nlinarith [hl5, hx, hx0]

/-- For a multiple-of-6 anchor `a`, `circ (a·(λτ + α/6)) = circ (λ·x_a(τ))`. -/
theorem circ_anchor_lambda {a : ℕ} (ha : 6 ∣ a) (τ : ℝ) (lam : ℕ) (al : ℕ) :
    circ ((a : ℝ) * ((lam : ℝ) * τ + (al : ℝ) / 6)) =
      circ ((lam : ℝ) * Int.fract ((a : ℝ) * τ)) := by
  obtain ⟨m, hm⟩ := ha
  have h3 : (a : ℝ) * τ = Int.fract ((a : ℝ) * τ) + (⌊(a : ℝ) * τ⌋ : ℝ) := by
    have h4 := Int.self_sub_fract ((a : ℝ) * τ)
    linarith
  have h4 : (a : ℝ) * (al : ℝ) / 6 = (m : ℝ) * (al : ℝ) := by
    rw [hm]; push_cast; field_simp
  have hsplit : (a : ℝ) * ((lam : ℝ) * τ + (al : ℝ) / 6) =
      (lam : ℝ) * Int.fract ((a : ℝ) * τ) +
        (((lam : ℤ) * ⌊(a : ℝ) * τ⌋ + (m : ℤ) * al : ℤ) : ℝ) := by
    push_cast
    linear_combination (lam : ℝ) * h3 + h4
  rw [hsplit, circ_add_int]

/-- Signed offset of `a·t` from the nearest integer. -/
noncomputable def off (a : ℕ) (t : ℝ) : ℝ :=
  (a : ℝ) * t - (round ((a : ℝ) * t) : ℝ)

/-- `|off a t| = circ (a·t)`. -/
theorem abs_off (a : ℕ) (t : ℝ) :
    |off a t| = circ ((a : ℝ) * t) := by
  rw [off, circ_eq]

/-- `off` is `1`-periodic. -/
theorem off_add_int (a : ℕ) (t : ℝ) (n : ℤ) :
    off a (t + (n : ℝ)) = off a t := by
  rw [off, off]
  rw [show (a : ℝ) * (t + (n : ℝ)) = (a : ℝ) * t + ((a : ℤ) * n : ℤ) by
    push_cast; ring]
  rw [round_add_intCast]
  push_cast
  ring

/-- `off` at `fract t` equals `off` at `t`. -/
theorem off_fract (a : ℕ) (t : ℝ) : off a (Int.fract t) = off a t := by
  rw [show Int.fract t = t + ((-⌊t⌋ : ℤ) : ℝ) by
    have h := Int.self_sub_floor t
    push_cast
    linarith]
  exact off_add_int a t _

/-- `off` is odd on the `|off| < 1/2` region: `off a (-t) = - off a t`. -/
theorem off_neg {a : ℕ} {t : ℝ} (h : |off a t| < 1 / 2) :
    off a (-t) = -off a t := by
  unfold off
  rw [mul_neg]
  have h' : -(1 / 2) < (a : ℝ) * t - (round ((a : ℝ) * t) : ℝ) ∧
      (a : ℝ) * t - (round ((a : ℝ) * t) : ℝ) < 1 / 2 := by
    exact abs_lt.mp h
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
theorem fract_eq_off {a : ℕ} {t : ℝ} (h : 0 ≤ off a t) :
    Int.fract ((a : ℝ) * t) = off a t := by
  have hlt : off a t < 1 := by
    have h1 : |off a t| ≤ 1 / 2 := by rw [abs_off]; exact circ_le_half _
    linarith [le_trans (le_abs_self _) h1]
  rw [Int.fract_eq_iff]
  refine ⟨h, hlt, round ((a : ℝ) * t), ?_⟩
  rw [off]
  ring

/-- `fract (a·t) = 1 + off a t` when the offset is negative. -/
theorem fract_eq_one_add_off {a : ℕ} {t : ℝ} (h : off a t < 0) :
    Int.fract ((a : ℝ) * t) = 1 + off a t := by
  have hge : 0 ≤ 1 + off a t := by
    have h1 : |off a t| ≤ 1 / 2 := by rw [abs_off]; exact circ_le_half _
    linarith [le_trans (neg_le_abs _) h1]
  rw [Int.fract_eq_iff]
  refine ⟨hge, by linarith, round ((a : ℝ) * t) - 1, ?_⟩
  rw [off]
  push_cast
  ring

/-- Round stays fixed near an integer: `round (n + r) = n` for `r ∈ [−1/2, 1/2)`. -/
theorem round_of_sixth {n : ℤ} {r : ℝ} (h1 : -1 / 2 ≤ r) (h2 : r < 1 / 2) :
    round ((n : ℝ) + r) = n := by
  rw [round_eq_iff, Set.mem_Ico]
  constructor <;> linarith

/-- The finite set of `5/6`-boundary times of runner `d` in `[0,1)`:
times `(6l+5)/(6d)` for `l = 0,…,d−1`. -/
def topBdry6 (d : ℕ) : Finset ℝ :=
  (Finset.range d).image fun l => ((6 * l + 5 : ℕ) : ℝ) / (6 * (d : ℝ))

/-- At a `topBdry6` point, runner `d` sits at `5/6`. -/
theorem topBdry6_pos {d l : ℕ} (hd : 0 < d) :
    Int.fract ((d : ℝ) * (((6 * l + 5 : ℕ) : ℝ) / (6 * (d : ℝ)))) = 5 / 6 := by
  have hd' : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have h1 : (d : ℝ) * (((6 * l + 5 : ℕ) : ℝ) / (6 * (d : ℝ))) = (l : ℝ) + 5 / 6 := by
    field_simp
    push_cast
    ring
  rw [h1, show (l : ℝ) + 5 / 6 = ((l : ℤ) : ℝ) + 5 / 6 by push_cast; ring,
    Int.fract_intCast_add, Int.fract_eq_self]
  constructor <;> norm_num

/-- The finite set of `1/6`-boundary times of runner `d` in `[0,1)`:
times `(6l+1)/(6d)` for `l = 0,…,d−1`. -/
def botBdry6 (d : ℕ) : Finset ℝ :=
  (Finset.range d).image fun l => ((6 * l + 1 : ℕ) : ℝ) / (6 * (d : ℝ))

/-- At a `botBdry6` point, runner `d` sits at `1/6`. -/
theorem botBdry6_pos {d l : ℕ} (hd : 0 < d) :
    Int.fract ((d : ℝ) * (((6 * l + 1 : ℕ) : ℝ) / (6 * (d : ℝ)))) = 1 / 6 := by
  have hd' : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have h1 : (d : ℝ) * (((6 * l + 1 : ℕ) : ℝ) / (6 * (d : ℝ))) = (l : ℝ) + 1 / 6 := by
    field_simp
    push_cast
    ring
  rw [h1, show (l : ℝ) + 1 / 6 = ((l : ℤ) : ℝ) + 1 / 6 by push_cast; ring,
    Int.fract_intCast_add, Int.fract_eq_self]
  constructor <;> norm_num

/-- If `d·β' = l + 5/6` for `l : ℤ`, then `Int.fract β'` is a `topBdry6 d`
element. -/
theorem fract_mem_topBdry6 {d : ℕ} (hd : 0 < d) {β' : ℝ} {l : ℤ}
    (h : (d : ℝ) * β' = (l : ℝ) + 5 / 6) :
    Int.fract β' ∈ topBdry6 d := by
  have hd' : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  set l' : ℤ := l - (d : ℤ) * ⌊β'⌋ with hl'
  have hdβ : (d : ℝ) * Int.fract β' = (l' : ℝ) + 5 / 6 := by
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
    have h1 : (0 : ℝ) ≤ (l' : ℝ) + 5 / 6 := by rw [← hdβ]; positivity
    by_contra hlt
    have h2 : l' ≤ -1 := by omega
    have h3 : (l' : ℝ) ≤ (-1 : ℝ) := by exact_mod_cast h2
    linarith
  have hl'u : l' < (d : ℤ) := by
    have h1 : (l' : ℝ) + 5 / 6 < (d : ℝ) := by
      rw [← hdβ]
      calc (d : ℝ) * Int.fract β' < (d : ℝ) * 1 := by gcongr
        _ = d := by ring
    have h2 : (l' : ℝ) < (d : ℝ) := by linarith
    exact_mod_cast h2
  have hβeq : Int.fract β' = ((6 * l'.toNat + 5 : ℕ) : ℝ) / (6 * (d : ℝ)) := by
    have hcast : ((l'.toNat : ℕ) : ℝ) = (l' : ℝ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hl'0]
    have hnum : ((6 * l'.toNat + 5 : ℕ) : ℝ) = 6 * (l' : ℝ) + 5 := by
      push_cast
      rw [hcast]
    have h1 : Int.fract β' = ((l' : ℝ) + 5 / 6) / (d : ℝ) := by
      rw [eq_div_iff hd'.ne']
      rw [mul_comm]; exact hdβ
    rw [h1, hnum]
    field_simp
  rw [hβeq, topBdry6, Finset.mem_image]
  refine ⟨l'.toNat, Finset.mem_range.mpr ?_, rfl⟩
  omega

/-- If `d·β' = l + 1/6` for `l : ℤ`, then `Int.fract β'` is a `botBdry6 d`
element. -/
theorem fract_mem_botBdry6 {d : ℕ} (hd : 0 < d) {β' : ℝ} {l : ℤ}
    (h : (d : ℝ) * β' = (l : ℝ) + 1 / 6) :
    Int.fract β' ∈ botBdry6 d := by
  have hd' : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  set l' : ℤ := l - (d : ℤ) * ⌊β'⌋ with hl'
  have hdβ : (d : ℝ) * Int.fract β' = (l' : ℝ) + 1 / 6 := by
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
    have h1 : (0 : ℝ) ≤ (l' : ℝ) + 1 / 6 := by rw [← hdβ]; positivity
    by_contra hlt
    have h2 : l' ≤ -1 := by omega
    have h3 : (l' : ℝ) ≤ (-1 : ℝ) := by exact_mod_cast h2
    linarith
  have hl'u : l' < (d : ℤ) := by
    have h1 : (l' : ℝ) + 1 / 6 < (d : ℝ) := by
      rw [← hdβ]
      calc (d : ℝ) * Int.fract β' < (d : ℝ) * 1 := by gcongr
        _ = d := by ring
    have h2 : (l' : ℝ) < (d : ℝ) := by linarith
    exact_mod_cast h2
  have hβeq : Int.fract β' = ((6 * l'.toNat + 1 : ℕ) : ℝ) / (6 * (d : ℝ)) := by
    have hcast : ((l'.toNat : ℕ) : ℝ) = (l' : ℝ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hl'0]
    have hnum : ((6 * l'.toNat + 1 : ℕ) : ℝ) = 6 * (l' : ℝ) + 1 := by
      push_cast
      rw [hcast]
    have h1 : Int.fract β' = ((l' : ℝ) + 1 / 6) / (d : ℝ) := by
      rw [eq_div_iff hd'.ne']
      rw [mul_comm]; exact hdβ
    rw [h1, hnum]
    field_simp
  rw [hβeq, botBdry6, Finset.mem_image]
  refine ⟨l'.toNat, Finset.mem_range.mpr ?_, rfl⟩
  omega

/-- `fract (-z) = 0` when `fract z = 0`. -/
theorem fract_neg_eq_zero {z : ℝ} (hz : Int.fract z = 0) : Int.fract (-z) = 0 := by
  rw [Int.fract_eq_zero_iff] at hz ⊢
  obtain ⟨k, hk⟩ := hz
  exact ⟨-k, by push_cast at hk ⊢; linarith [hk]⟩

/-- The sixth-band is symmetric under negation:
`⟨-z⟩ ∈ [1/6,5/6] ↔ ⟨z⟩ ∈ [1/6,5/6]`. -/
theorem fract_neg_mem_Icc {z : ℝ} :
    Int.fract (-z) ∈ Set.Icc (1 / 6) (5 / 6) ↔
      Int.fract z ∈ Set.Icc (1 / 6) (5 / 6) := by
  by_cases hz : Int.fract z = 0
  · rw [fract_neg_eq_zero hz, hz]
  · rw [Int.fract_neg hz]
    simp only [Set.mem_Icc]
    constructor
    · rintro ⟨h1, h2⟩
      constructor <;> linarith
    · rintro ⟨h1, h2⟩
      constructor <;> linarith

/-- Open-band version of the negation symmetry. -/
theorem fract_neg_mem_Ioo {z : ℝ} :
    Int.fract (-z) ∈ Set.Ioo (1 / 6) (5 / 6) ↔
      Int.fract z ∈ Set.Ioo (1 / 6) (5 / 6) := by
  by_cases hz : Int.fract z = 0
  · rw [fract_neg_eq_zero hz, hz]
  · rw [Int.fract_neg hz]
    simp only [Set.mem_Ioo]
    constructor
    · rintro ⟨h1, h2⟩
      constructor <;> linarith
    · rintro ⟨h1, h2⟩
      constructor <;> linarith

/-- The signed `t̃ = t + sh/6` shift (`sh : ℤ`, possibly negative): for
`d ≡ e (mod 6)`, `x_d(t + sh/6) = ⟨x_d(t) + e·sh/6⟩`.  This is Renault's
`t̃ = t̄ + e₂/6` anchor-reset move. -/
theorem fract_signed_shift {d : ℕ} {e : ℤ} (hde : (d : ℤ) ≡ e [ZMOD 6])
    (t : ℝ) (sh : ℤ) :
    Int.fract ((d : ℝ) * (t + (sh : ℝ) / 6)) =
      Int.fract (Int.fract ((d : ℝ) * t) + (e : ℝ) * (sh : ℝ) / 6) := by
  obtain ⟨k, hk⟩ := Int.modEq_iff_dvd.mp hde
  have hfloor : (d : ℝ) * t = Int.fract ((d : ℝ) * t) + (⌊(d : ℝ) * t⌋ : ℝ) := by
    have h3 := Int.self_sub_fract ((d : ℝ) * t)
    linarith
  have hd : (d : ℝ) = (e : ℝ) - 6 * (k : ℝ) := by
    have h2 : (d : ℤ) = e - 6 * k := by linarith [hk]
    calc (d : ℝ) = ((d : ℤ) : ℝ) := by simp
      _ = ((e - 6 * k : ℤ) : ℝ) := by rw [h2]
      _ = (e : ℝ) - 6 * (k : ℝ) := by push_cast; ring
  have hd' : (d : ℝ) * (sh : ℝ) / 6 =
      (e : ℝ) * (sh : ℝ) / 6 + (-(k : ℝ)) * (sh : ℝ) := by
    rw [hd]
    ring
  have h1 : (d : ℝ) * (t + (sh : ℝ) / 6) =
      (Int.fract ((d : ℝ) * t) + (e : ℝ) * (sh : ℝ) / 6) +
        ((⌊(d : ℝ) * t⌋ + (-k) * sh : ℤ) : ℝ) := by
    push_cast
    linear_combination hfloor + hd'
  rw [h1, Int.fract_add_intCast]

/-- The multiple-of-6 runner is untouched by a `sh/6` shift:
`x_a(t + sh/6) = x_a(t)` when `6 ∣ a`. -/
theorem fract_signed_shift_anchor {a : ℕ} (ha : 6 ∣ a) (t : ℝ) (sh : ℤ) :
    Int.fract ((a : ℝ) * (t + (sh : ℝ) / 6)) = Int.fract ((a : ℝ) * t) := by
  have hde : (a : ℤ) ≡ 0 [ZMOD 6] := by
    rw [Int.modEq_zero_iff_dvd]
    exact_mod_cast ha
  rw [fract_signed_shift hde]
  simp

end
