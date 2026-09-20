/-
Copyright (c) 2026 Research07 contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Research07 contributors
-/
import Research07.LRC5.Discrete

/-!
# Discrete infrastructure for the seven-runner case

Modular-arithmetic layer for the Barajas–Serra proof (EJC 15(1) 2008 #R48,
arXiv:0710.4495) of the lonely runner conjecture for six integer speeds.
Fix `p = 7`, `m = max ν₇(D)`, `N = 7^{m+1}`.

* `level7 D j` — elements of `D` with `padicValNat 7 d = j`.
* `qdig7 m x : ZMod 7` — leading base-7 digit of `x`'s residue mod `7^{m+1}`.
* `runit7 x : ZMod 7` — unit part of `x` mod 7.
* `digit7 j x : ZMod 7` — the `j`-th base-7 digit of `x` (for the general
  `Λ_j` shift identity, paper eq. (7)).
* `multLow7 m j = {1 + k·7^{m−j}}`, `multTop7 = {1,…,6}` — the multiplier
  families `Λ_{j,7}` of the paper.
* `absModN_pow7_scale` — `|7^a·x|_{7^a·M} = 7^a·|x|_M` (used by the
  divide-by-7 recursion and the `j₀ > 0` level reduction).
* `apLen X` — length of the shortest difference-one cyclic arithmetic
  progression in `ZMod 7` containing `X` (paper's `ℓ(X)`); computed as
  `7 − (longest cyclic gap)`.
* `circ_ge_seventh` — `|λd|_M ≥ M/7` gives `circ (λd/M) ≥ 1/7`.

`residN`, `absModN`, `absModN_neg`, `circ_mul_div_eq_absModN` are reused from
`Research07.LRC5.Discrete` (they are `N`-generic).
-/

/-- The `j`-th 7-adic level of `D`: elements with `padicValNat 7 d = j`. -/
def level7 (D : Finset ℕ) (j : ℕ) : Finset ℕ :=
  D.filter fun d => padicValNat 7 d = j

/-- Leading base-7 digit of `x % 7^{m+1}`, valued in `ZMod 7`. -/
def qdig7 (m x : ℕ) : ZMod 7 := (↑((x % 7 ^ (m + 1)) / 7 ^ m) : ZMod 7)

/-- Unit part of `x` modulo 7: the trailing nonzero base-7 digit. -/
def runit7 (x : ℕ) : ZMod 7 := (↑(x / 7 ^ padicValNat 7 x) : ZMod 7)

/-- The `j`-th base-7 digit of `x` (paper eq. (7) shift coefficient). -/
def digit7 (j x : ℕ) : ZMod 7 := (↑((x / 7 ^ j) % 7) : ZMod 7)

/-- Multiplier family `Λ_{j,7}` for `j < m`: `{1 + k·7^{m−j} : k ∈ range 7}`. -/
def multLow7 (m j : ℕ) : Finset ℕ :=
  (Finset.range 7).image fun k => 1 + k * 7 ^ (m - j)

/-- Multiplier family `Λ_{m,7}`: `{1,2,3,4,5,6}`. -/
def multTop7 : Finset ℕ := {1, 2, 3, 4, 5, 6}

/-- The quotient `x / 7^{ν₇ x}` is the `divMaxPow` unit part of `x`. -/
private theorem div_pow_padicValNat7 (x : ℕ) :
    x / 7 ^ padicValNat 7 x = Nat.divMaxPow x 7 := by
  have h := congrArg (· / 7 ^ padicValNat 7 x) (Nat.divMaxPow_mul_pow_padicValNat 7 x)
  rw [Nat.mul_div_cancel _ (Nat.pow_pos (by norm_num))] at h
  exact h.symm

/-- The unit part of a positive integer is a nonzero residue. -/
theorem runit7_ne_zero {x : ℕ} (hx : 0 < x) : runit7 x ≠ 0 := by
  unfold runit7
  rw [div_pow_padicValNat7, Ne, ZMod.natCast_eq_zero_iff]
  exact Nat.not_dvd_divMaxPow (by norm_num) (Nat.ne_of_gt hx)

/-- Multiplication by a `7`-unit preserves the `7`-adic valuation. -/
theorem padicValNat_mul_unit7 {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h7 : ¬ 7 ∣ a) : padicValNat 7 (a * b) = padicValNat 7 b := by
  have hu : ¬ 7 ∣ Nat.divMaxPow b 7 := Nat.not_dvd_divMaxPow (by norm_num) hb
  have hu0 : Nat.divMaxPow b 7 ≠ 0 := fun h => hu (h ▸ dvd_zero 7)
  have hnd : ¬ 7 ∣ a * Nat.divMaxPow b 7 := by
    intro hdvd
    rcases (Nat.Prime.dvd_mul Nat.prime_seven).mp hdvd with h | h
    · exact h7 h
    · exact hu h
  have hv0 : padicValNat 7 (a * Nat.divMaxPow b 7) = 0 := by
    by_contra h
    have h1 : (7 : ℕ) ^ 1 ∣ a * Nat.divMaxPow b 7 :=
      (Nat.pow_dvd_iff_le_padicValNat (by norm_num) (Nat.mul_ne_zero ha hu0)).mpr
        (Nat.pos_of_ne_zero h)
    rw [pow_one] at h1
    exact hnd h1
  have hb_eq : b = Nat.divMaxPow b 7 * 7 ^ padicValNat 7 b :=
    (Nat.divMaxPow_mul_pow_padicValNat 7 b).symm
  have h2 : a * b = 7 ^ padicValNat 7 b * (a * Nat.divMaxPow b 7) := by
    conv_lhs => rw [hb_eq]
    ring
  rw [h2, padicValNat_base_pow_mul (by norm_num) (Nat.mul_ne_zero ha hu0), hv0,
    Nat.zero_add]

/-- Elements at the top level stay at distance `≥ 7^m` under unit multipliers
(their residue is `c·7^m` with `c ∈ {1,…,6}`, and `min c (7−c) ≥ 1`). -/
theorem absModN_top_ge7 {m d lam : ℕ} (hd : padicValNat 7 d = m) (hpos : 0 < d)
    (hlam : ¬ 7 ∣ lam) :
    7 ^ m ≤ absModN (lam * d) (7 ^ (m + 1)) := by
  have hd0 : d ≠ 0 := Nat.ne_of_gt hpos
  have hu7 : ¬ 7 ∣ Nat.divMaxPow d 7 := Nat.not_dvd_divMaxPow (by norm_num) hd0
  have hc7 : ¬ 7 ∣ lam * Nat.divMaxPow d 7 := by
    intro h
    rcases (Nat.Prime.dvd_mul Nat.prime_seven).mp h with h | h
    · exact hlam h
    · exact hu7 h
  have hd_eq : lam * d = lam * Nat.divMaxPow d 7 * 7 ^ m := by
    conv_lhs => rw [← Nat.divMaxPow_mul_pow_padicValNat 7 d, hd]
    ring
  have hr : lam * d % 7 ^ (m + 1) = lam * Nat.divMaxPow d 7 % 7 * 7 ^ m := by
    rw [hd_eq, pow_succ', Nat.mul_mod_mul_right]
  set c := lam * Nat.divMaxPow d 7 % 7 with hc_def
  have hc1 : 1 ≤ c := by
    have h2 : c ≠ 0 := by
      rw [hc_def]
      exact fun h => hc7 (Nat.dvd_iff_mod_eq_zero.mpr h)
    omega
  have hc6 : c ≤ 6 := by
    have h1 : c < 7 := by
      rw [hc_def]
      exact Nat.mod_lt _ (by norm_num)
    omega
  unfold absModN
  rw [hr, pow_succ']
  interval_cases c <;> omega

/-- Digit characterization of `|y|_N ≥ 7^m` for `ν₇(y) < m`: writing
`r = y % 7^{m+1} = e·7^m + f`, the residue `f = y % 7^m` is nonzero (else
`7^m ∣ y`), so the `e = 6, f = 0` boundary is impossible. -/
private theorem absModN_ge_iff_digit7 {m y : ℕ} (hval : padicValNat 7 y < m)
    (hy : y ≠ 0) :
    7 ^ m ≤ absModN y (7 ^ (m + 1)) ↔
      1 ≤ (qdig7 m y).val ∧ (qdig7 m y).val ≤ 5 := by
  unfold absModN
  set E := 7 ^ m with hE
  set r := y % 7 ^ (m + 1) with hr
  set e := r / E with he
  set f := r % E with hf
  have hEpos : 0 < E := by rw [hE]; exact Nat.pow_pos (by norm_num)
  have hN : 7 ^ (m + 1) = 7 * E := by rw [hE]; exact pow_succ' 7 m
  have hrN : r < 7 ^ (m + 1) := Nat.mod_lt _ (Nat.pow_pos (by norm_num))
  have hrN2 : r < 7 * E := by rw [← hN]; exact hrN
  have hr_eq : r = E * e + f := (Nat.div_add_mod r E).symm
  have hf_lt : f < E := Nat.mod_lt _ hEpos
  have he_lt : e < 7 := (Nat.div_lt_iff_lt_mul hEpos).mpr hrN2
  have hfy : f = y % E :=
    Nat.mod_mod_of_dvd y (by rw [hE]; exact Nat.pow_dvd_pow 7 (by omega))
  have hndvd : ¬ 7 ^ m ∣ y := by
    intro h
    have : m ≤ padicValNat 7 y :=
      (Nat.pow_dvd_iff_le_padicValNat (by norm_num) hy).mp h
    omega
  have hf_ne : f ≠ 0 := by
    rw [hfy, hE, Ne, ← Nat.dvd_iff_mod_eq_zero]
    exact hndvd
  have hqval : (qdig7 m y).val = e := by
    unfold qdig7
    rw [ZMod.val_natCast]
    exact Nat.mod_eq_of_lt he_lt
  rw [hqval, hN]
  interval_cases e <;> omega

/-- For non-top elements `ν₇(d) < m` and unit multipliers, the distance
condition `|λd|_N ≥ 7^m` is equivalent to the digit condition
`qdig (λd) ∈ {1,…,5}`. The boundary residue `6·7^m` is excluded since it
would have 7-adic valuation `m`. -/
theorem absModN_ge_iff_qdig7 {m d lam : ℕ} (hd : padicValNat 7 d < m)
    (hpos : 0 < d) (hlam : ¬ 7 ∣ lam) :
    7 ^ m ≤ absModN (lam * d) (7 ^ (m + 1)) ↔
      1 ≤ (qdig7 m (lam * d)).val ∧ (qdig7 m (lam * d)).val ≤ 5 := by
  have hlam0 : lam ≠ 0 := fun h => hlam (h ▸ dvd_zero 7)
  have hd0 : d ≠ 0 := Nat.ne_of_gt hpos
  have hval : padicValNat 7 (lam * d) = padicValNat 7 d :=
    padicValNat_mul_unit7 hlam0 hd0 hlam
  apply absModN_ge_iff_digit7
  · rw [hval]; exact hd
  · exact Nat.mul_ne_zero hlam0 hd0

/-- Preservation identity (paper eq. (2)): a multiplier from `Λ_{j,7}` leaves
the residue of any element at level `> j` unchanged modulo `7^{m+1}`. -/
theorem residN_multLow7 {m j k x : ℕ} (hjm : j < m) (hx : j < padicValNat 7 x) :
    (1 + k * 7 ^ (m - j)) * x % 7 ^ (m + 1) = x % 7 ^ (m + 1) := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx
  have hdvd : 7 ^ (j + 1) ∣ x :=
    (Nat.pow_dvd_iff_le_padicValNat (by norm_num) hx0).mpr hx
  have hdvd2 : 7 ^ (m + 1) ∣ k * 7 ^ (m - j) * x := by
    rw [show m + 1 = (m - j) + (j + 1) by omega, pow_add]
    obtain ⟨y, rfl⟩ := hdvd
    exact ⟨k * y, by ring⟩
  rw [add_mul, one_mul]
  obtain ⟨z, hz⟩ := hdvd2
  rw [hz, Nat.add_mul_mod_self_left]

/-- Pulling `7^j` out of a residue mod `7^{m+1}` for `j ≤ m + 1`. -/
private theorem mod_pow_mul7 {j m : ℕ} (h : j ≤ m + 1) (v : ℕ) :
    (7 ^ j * v) % 7 ^ (m + 1) = 7 ^ j * (v % 7 ^ (m + 1 - j)) := by
  conv_lhs => rw [show 7 ^ (m + 1) = 7 ^ j * 7 ^ (m + 1 - j) by
    rw [← pow_add]; congr 1; omega]
  exact Nat.mul_mod_mul_left _ _ _

/-- Pulling `7^j` out of a division by `7^m` for `j ≤ m`. -/
private theorem div_pow_mul7 {j m : ℕ} (h : j ≤ m) (s : ℕ) :
    (7 ^ j * s) / 7 ^ m = s / 7 ^ (m - j) := by
  conv_lhs => rw [show 7 ^ m = 7 ^ j * 7 ^ (m - j) by
    rw [← pow_add]; congr 1; omega]
  exact Nat.mul_div_mul_left _ _ (Nat.pow_pos (by norm_num))

/-- Shift identity (paper eq. (3)): a `Λ_{j,7}`-multiplier shifts the leading
digit of a level-`j` element by `k · runit x`. -/
theorem qdig7_multLow {m j k x : ℕ} (hjm : j < m) (hx : padicValNat 7 x = j) :
    qdig7 m ((1 + k * 7 ^ (m - j)) * x) = qdig7 m x + (k : ZMod 7) * runit7 x := by
  rcases eq_or_ne x 0 with rfl | hx0
  · simp [qdig7, runit7]
  set u := Nat.divMaxPow x 7 with hu
  have hu7 : ¬ 7 ∣ u := Nat.not_dvd_divMaxPow (by norm_num) hx0
  have hx_eq : x = u * 7 ^ j := by
    have h := Nat.divMaxPow_mul_pow_padicValNat 7 x
    rw [hx, ← hu] at h
    exact h.symm
  have hL : (1 + k * 7 ^ (m - j)) * x = 7 ^ j * ((1 + k * 7 ^ (m - j)) * u) := by
    rw [hx_eq]; ring
  have hqL : qdig7 m ((1 + k * 7 ^ (m - j)) * x) =
      (↑((1 + k * 7 ^ (m - j)) * u / 7 ^ (m - j)) : ZMod 7) := by
    unfold qdig7
    rw [hL, mod_pow_mul7 (by omega : j ≤ m + 1), div_pow_mul7 (by omega : j ≤ m),
      show m + 1 - j = (m - j) + 1 by omega, pow_succ, Nat.mod_mul_right_div_self,
      ZMod.natCast_eq_natCast_iff']
    exact Nat.mod_mod _ _
  have hdiv2 : (1 + k * 7 ^ (m - j)) * u / 7 ^ (m - j) = u / 7 ^ (m - j) + k * u := by
    have h3 : (1 + k * 7 ^ (m - j)) * u = u + 7 ^ (m - j) * (k * u) := by ring
    rw [h3, Nat.add_mul_div_left _ _ (Nat.pow_pos (by norm_num))]
  have hqR : qdig7 m x = (↑(u / 7 ^ (m - j)) : ZMod 7) := by
    unfold qdig7
    have hx2 : x = 7 ^ j * u := by rw [hx_eq]; ring
    rw [hx2, mod_pow_mul7 (by omega : j ≤ m + 1), div_pow_mul7 (by omega : j ≤ m),
      show m + 1 - j = (m - j) + 1 by omega, pow_succ, Nat.mod_mul_right_div_self,
      ZMod.natCast_eq_natCast_iff']
    exact Nat.mod_mod _ _
  have hrunit : runit7 x = (u : ZMod 7) := by
    unfold runit7
    rw [hx, hx_eq, Nat.mul_div_cancel _ (Nat.pow_pos (by norm_num))]
  rw [hqL, hdiv2, hqR, hrunit]
  push_cast
  ring

/-- Top-level identity: multiplying a level-`m` element by `l` scales its
digit by `l`. -/
theorem qdig7_multTop {m l x : ℕ} (hx : padicValNat 7 x = m) :
    qdig7 m (l * x) = (l : ZMod 7) * runit7 x := by
  rcases eq_or_ne x 0 with rfl | hx0
  · simp [qdig7, runit7]
  set u := Nat.divMaxPow x 7 with hu
  have hx_eq : x = u * 7 ^ m := by
    have h := Nat.divMaxPow_mul_pow_padicValNat 7 x
    rw [hx, ← hu] at h
    exact h.symm
  have hL : l * x = 7 ^ m * (l * u) := by rw [hx_eq]; ring
  have hqL : qdig7 m (l * x) = (↑(l * u % 7) : ZMod 7) := by
    unfold qdig7
    rw [hL, pow_succ, Nat.mul_mod_mul_left,
      Nat.mul_div_cancel_left _ (Nat.pow_pos (by norm_num))]
  have hrunit : runit7 x = (u : ZMod 7) := by
    unfold runit7
    rw [hx, hx_eq, Nat.mul_div_cancel _ (Nat.pow_pos (by norm_num))]
  rw [hqL, hrunit, ← Nat.cast_mul, ZMod.natCast_eq_natCast_iff']
  exact Nat.mod_mod _ _

/-- Division of a sum: `(a + b)/c = a/c + b/c + carry` with
`carry = (a%c + b%c)/c`. -/
private theorem add_div_carry7 (a b c : ℕ) (hc : 0 < c) :
    (a + b) / c = a / c + b / c + (a % c + b % c) / c := by
  have h1 : a + b = a % c + b % c + c * (a / c + b / c) := by
    have hda := Nat.div_add_mod a c
    have hdb := Nat.div_add_mod b c
    have hmul : c * (a / c) + c * (b / c) = c * (a / c + b / c) := by ring
    omega
  rw [h1, Nat.add_mul_div_left _ _ hc]
  ring

/-- `qdig7` as a cast of a natural division: `qdig7 m y = ↑(y / 7^m)` since
`y % 7^{m+1} / 7^m = (y / 7^m) % 7`. -/
theorem qdig7_eq_cast_div (m y : ℕ) :
    qdig7 m y = (↑(y / 7 ^ m) : ZMod 7) := by
  unfold qdig7
  rw [pow_succ, Nat.mod_mul_right_div_self, ZMod.natCast_eq_natCast_iff']
  exact Nat.mod_mod _ _

/-- Carry bound (paper eq. (5)): the leading digit of `(j+1)·x` differs from
`qdig (j·x) + qdig x` by a carry of at most `1`. -/
theorem qdig7_add_one (m j x : ℕ) :
    (qdig7 m ((j + 1) * x) - qdig7 m (j * x) - qdig7 m x).val ≤ 1 := by
  rw [qdig7_eq_cast_div, qdig7_eq_cast_div, qdig7_eq_cast_div]
  have hkey : (j + 1) * x / 7 ^ m = j * x / 7 ^ m + x / 7 ^ m +
      (j * x % 7 ^ m + x % 7 ^ m) / 7 ^ m := by
    have h : (j + 1) * x = j * x + x := by ring
    rw [h]
    exact add_div_carry7 _ _ _ (Nat.pow_pos (by norm_num))
  rw [hkey]
  have hsimp : (↑(j * x / 7 ^ m + x / 7 ^ m + (j * x % 7 ^ m + x % 7 ^ m) / 7 ^ m) :
      ZMod 7) - ↑(j * x / 7 ^ m) - ↑(x / 7 ^ m)
      = (↑((j * x % 7 ^ m + x % 7 ^ m) / 7 ^ m) : ZMod 7) := by
    push_cast
    ring
  rw [hsimp, ZMod.val_natCast]
  have hcarry : (j * x % 7 ^ m + x % 7 ^ m) / 7 ^ m ≤ 1 := by
    have h1 : j * x % 7 ^ m < 7 ^ m := Nat.mod_lt _ (Nat.pow_pos (by norm_num))
    have h2 : x % 7 ^ m < 7 ^ m := Nat.mod_lt _ (Nat.pow_pos (by norm_num))
    have h3 : (j * x % 7 ^ m + x % 7 ^ m) / 7 ^ m < 2 :=
      (Nat.div_lt_iff_lt_mul (Nat.pow_pos (by norm_num))).mpr (by omega)
    omega
  exact le_trans (Nat.mod_le _ _) hcarry

/-- **Modulus scaling**: `|7^a·x|_{7^a·M} = 7^a·|x|_M`.
Used by the divide-by-7 preprocessing recursion and by the `j₀ > 0`
level reduction (lift of a multiplier from `N'` to `N`). -/
theorem absModN_pow7_scale (a x M : ℕ) (hM : 0 < M) :
    absModN (7 ^ a * x) (7 ^ a * M) = 7 ^ a * absModN x M := by
  unfold absModN
  set p := 7 ^ a with hp
  have hp0 : 0 < p := Nat.pow_pos (by norm_num)
  have hrx : x % M < M := Nat.mod_lt _ hM
  rw [Nat.mul_mod_mul_left]
  rcases le_or_gt (x % M) (M - x % M) with hle | hgt
  · have h1 : p * (x % M) ≤ p * M - p * (x % M) := by
      have : p * (x % M) + p * (x % M) ≤ p * M :=
        calc p * (x % M) + p * (x % M) = p * ((x % M) + (x % M)) := by ring
          _ ≤ p * M := Nat.mul_le_mul_left _ (by omega)
      omega
    rw [Nat.min_eq_left h1, Nat.min_eq_left hle]
  · have h3 : p * M - p * (x % M) ≤ p * (x % M) := by
      have : p * M ≤ p * (x % M) + p * (x % M) :=
        calc p * M = p * ((M - x % M) + (x % M)) := by
              rw [Nat.sub_add_cancel hrx.le]
          _ = p * (M - x % M) + p * (x % M) := by ring
          _ ≤ p * (x % M) + p * (x % M) :=
              Nat.add_le_add_right (Nat.mul_le_mul_left _ hgt.le) _
      omega
    rw [Nat.min_eq_right h3, Nat.min_eq_right hgt.le]
    have h4 : p * (M - x % M) + p * (x % M) = p * M := by
      rw [← Nat.mul_add, Nat.sub_add_cancel hrx.le]
    omega

/-- Package: `M/7 ≤ |λd|_M` gives `circ (λd/M) ≥ 1/7` for any modulus `M`
divisible by 7. -/
theorem circ_ge_seventh {lam d M : ℕ} (hM7 : 7 ∣ M) (hM : 0 < M)
    (h : M / 7 ≤ absModN (lam * d) M) :
    (1 / 7 : ℝ) ≤ circ ((lam * d : ℝ) / (M : ℝ)) := by
  have hMR : (0:ℝ) < M := Nat.cast_pos.mpr hM
  rw [circ_mul_div_eq_absModN lam d M hM]
  rw [le_div_iff₀ hMR]
  have hR : ((M / 7 : ℕ) : ℝ) ≤ absModN (lam * d) M := Nat.cast_le.mpr h
  have heq : (1 / 7 : ℝ) * (M : ℝ) = (M / 7 : ℕ) := by
    obtain ⟨q, rfl⟩ := hM7
    rw [Nat.mul_div_cancel_left _ (by norm_num : 0 < 7)]
    push_cast
    ring
  rw [heq]
  exact hR

/-- The cyclic interval `{i, i+1, …, i+L−1}` in `ZMod 7`, written as the
residues `x` with `(x − i).val < L`. -/
def cycIv (i : ZMod 7) (L : ℕ) : Finset (ZMod 7) :=
  Finset.univ.filter fun x : ZMod 7 => (x - i).val < L

/-- `cycIv` is monotone in the length parameter. -/
theorem cycIv_mono {i : ZMod 7} {a b : ℕ} (hab : a ≤ b) :
    cycIv i a ⊆ cycIv i b := by
  intro x hx
  simp only [cycIv, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  omega

/-- The score finset used by `apLen`: achievable covering lengths (or `8`). -/
private def apScores (X : Finset (ZMod 7)) : Finset ℕ :=
  (Finset.range 8).image fun L =>
    if ∃ i : ZMod 7, X ⊆ cycIv i L then L else 8

private theorem apScores_nonempty (X : Finset (ZMod 7)) :
    (apScores X).Nonempty :=
  ⟨if ∃ i : ZMod 7, X ⊆ cycIv i 7 then 7 else 8,
    Finset.mem_image.mpr ⟨7, Finset.mem_range.mpr (by norm_num), rfl⟩⟩

/-- **Covering length** `ℓ(X)` (paper notation): the length of the shortest
difference-one cyclic arithmetic progression in `ZMod 7` containing `X`.
`0` for the empty set, `1` for a singleton, `7` for the universe. -/
def apLen (X : Finset (ZMod 7)) : ℕ :=
  (apScores X).min' (apScores_nonempty X)

/-- `apLen X ≤ L` iff some cyclic interval of length `L` covers `X`. -/
theorem apLen_le_iff (X : Finset (ZMod 7)) (L : ℕ) (hL : L ≤ 7) :
    apLen X ≤ L ↔ ∃ i : ZMod 7, X ⊆ cycIv i L := by
  classical
  constructor
  · intro h
    by_contra hcon
    push Not at hcon
    have hv : ∀ v ∈ apScores X, L < v := by
      intro v hv
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hv
      rw [Finset.mem_range] at hj
      rcases le_or_gt j L with h1 | h2
      · have hne : ¬ ∃ i : ZMod 7, X ⊆ cycIv i j := by
          rintro ⟨i, hi⟩
          exact hcon i (hi.trans (cycIv_mono h1))
        rw [ite_eq_right hne]
        omega
      · by_cases hex : ∃ i : ZMod 7, X ⊆ cycIv i j
        · rw [ite_eq_left hex]
          omega
        · rw [ite_eq_right hex]
          omega
    have hmin : L < (apScores X).min' (apScores_nonempty X) := by
      have hmem := Finset.min'_mem _ (apScores_nonempty X)
      exact hv _ hmem
    unfold apLen at h
    omega
  · rintro ⟨i, hi⟩
    have hmem : (if ∃ i' : ZMod 7, X ⊆ cycIv i' L then L else 8) ∈ apScores X :=
      Finset.mem_image.mpr ⟨L, Finset.mem_range.mpr (by omega), rfl⟩
    have hle : (apScores X).min' (apScores_nonempty X)
        ≤ (if ∃ i' : ZMod 7, X ⊆ cycIv i' L then L else 8) :=
      Finset.min'_le _ _ hmem
    have hval : (if ∃ i' : ZMod 7, X ⊆ cycIv i' L then L else 8) = L :=
      ite_eq_left ⟨i, hi⟩
    calc apLen X ≤ (if ∃ i' : ZMod 7, X ⊆ cycIv i' L then L else 8) := hle
      _ = L := hval
