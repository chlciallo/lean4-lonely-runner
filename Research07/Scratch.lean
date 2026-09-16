import Research07.LRC5.Filtering
open Finset

/-- `absModN` depends only on the residue. -/
private theorem absModN_congr {a b N : ℕ} (h : a % N = b % N) :
    absModN a N = absModN b N := by
  unfold absModN; rw [h]

/-- `qdig m x` is the mod-5 residue of `x / 5^m`. -/
private theorem qdig_eq (m x : ℕ) : qdig m x = ((x / 5 ^ m : ℕ) : ZMod 5) := by
  unfold qdig
  rw [ZMod.natCast_eq_natCast_iff]
  have hN : (5:ℕ) ^ (m+1) = 5 ^ m * 5 := pow_succ 5 m
  have key : x / 5 ^ m = (x % 5 ^ (m + 1)) / 5 ^ m + 5 * (x / 5 ^ (m + 1)) := by
    conv_lhs => rw [← Nat.div_add_mod x (5 ^ (m + 1)), hN]
    rw [mul_assoc, add_comm,
      Nat.add_mul_div_left _ _ (by positivity : (0:ℕ) < 5 ^ m), ← hN]
  rw [key]
  exact (Nat.add_mul_mod_self_left _ _ _).symm

/-- Adding a multiple of `5^m` shifts the leading digit by the coefficient. -/
private theorem qdig_add_hi (m a c : ℕ) :
    qdig m (a + c * 5 ^ m) = qdig m a + (c : ZMod 5) := by
  rw [qdig_eq, qdig_eq, mul_comm c (5 ^ m),
    Nat.add_mul_div_left _ _ (by positivity : (0:ℕ) < 5 ^ m), Nat.cast_add]

/-- For `λ = j + K·5^m` and a unit `x`, the leading digit of `λx` is
`qdig (j·x) + K·runit x`. -/
private theorem qdig_shift {m j K x : ℕ} (hx : padicValNat 5 x = 0) :
    qdig m ((j + K * 5 ^ m) * x) = qdig m (j * x) + (K : ZMod 5) * runit x := by
  have h1 : (j + K * 5 ^ m) * x = j * x + (K * x) * 5 ^ m := by ring
  rw [h1, qdig_add_hi, Nat.cast_mul]
  congr 1
  show (x : ZMod 5) = runit x
  unfold runit
  rw [hx, pow_zero, Nat.div_one]

/-- The two carries in `qdig(2x)`, `qdig(3x)` relative to `qdig x` are `∈ {0,1}`. -/
private theorem qdig_carries (m x : ℕ) :
    ∃ c d : ZMod 5, c.val ≤ 1 ∧ d.val ≤ 1 ∧
      qdig m (2 * x) = 2 * qdig m x + c ∧
      qdig m (3 * x) = 3 * qdig m x + c + d := by
  have h1 := qdig_add_one m 1 x
  have h2 := qdig_add_one m 2 x
  have e1 : qdig m ((1 + 1) * x) - qdig m (1 * x) - qdig m x =
      qdig m (2 * x) - 2 * qdig m x := by
    rw [show ((1:ℕ) + 1) * x = 2 * x from rfl, one_mul, two_mul]
  have e2 : qdig m ((2 + 1) * x) - qdig m (2 * x) - qdig m x =
      qdig m (3 * x) - qdig m (2 * x) - qdig m x := by
    rw [show ((2:ℕ) + 1) * x = 3 * x from rfl]
  exact ⟨qdig m (2 * x) - 2 * qdig m x,
    qdig m (3 * x) - qdig m (2 * x) - qdig m x,
    e1 ▸ h1, e2 ▸ h2, by ring, by ring⟩

private abbrev bz (b : Bool) : ZMod 5 := if b then 1 else 0
private abbrev gd (x : ZMod 5) : Prop := x = 1 ∨ x = 2 ∨ x = 3

/-- `val ≤ 1` means `c ∈ {0,1}`. -/
private theorem zmod01 {c : ZMod 5} (h : c.val ≤ 1) : c = 0 ∨ c = 1 := by
  have hv : c.val = 0 ∨ c.val = 1 := by omega
  rcases hv with h'|h'
  · left; rw [← ZMod.natCast_zmod_val c, h']; exact Nat.cast_zero
  · right; rw [← ZMod.natCast_zmod_val c, h']; exact Nat.cast_one

private theorem bz_of_val {c : ZMod 5} (hc : c.val ≤ 1) :
    bz (decide (c = 1)) = c := by
  rcases zmod01 hc with h|h <;> rw [h] <;> rfl

/-- Pigeonhole: three elements of `{1,2}` — if `a` differs from both, `b = c`. -/
private theorem zmod5_third {a b c : ZMod 5} (ha : a = 1 ∨ a = 2) (hb : b = 1 ∨ b = 2)
    (hc : c = 1 ∨ c = 2) (hab : a ≠ b) (hac : a ≠ c) : b = c := by
  rcases ha with rfl|rfl <;> rcases hb with rfl|rfl <;> rcases hc with rfl|rfl <;>
    first | rfl | (exact (hab rfl).elim) | (exact (hac rfl).elim)

set_option synthInstance.maxSize 512 in
set_option maxHeartbeats 8000000 in
/-- The finite digit chase (Barajas–Serra §3 residual case): for any base
digits `qᵢ` and carries in `{0,1}`, some multiplier index `j ∈ {1,2,3}` with
some shift puts all three digits in `{1,2,3}`, where the third element's
shift is scaled by `r`. -/
private theorem digit_chase : ∀ (r : ZMod 5) (q₁ q₂ q₃ : ZMod 5)
    (c₁ c₂ c₃ d₁ d₂ d₃ : Bool), (r = 1 ∨ r = 2 ∨ r = 3) →
    (∃ k : ZMod 5, gd (q₁ + k) ∧ gd (q₂ + k) ∧ gd (q₃ + r * k)) ∨
    (∃ k : ZMod 5, gd (2 * q₁ + bz c₁ + k) ∧ gd (2 * q₂ + bz c₂ + k) ∧
      gd (2 * q₃ + bz c₃ + r * k)) ∨
    (∃ k : ZMod 5, gd (3 * q₁ + bz c₁ + bz d₁ + k) ∧ gd (3 * q₂ + bz c₂ + bz d₂ + k) ∧
      gd (3 * q₃ + bz c₃ + bz d₃ + r * k)) := by
  decide
