import Research07.LRC5.Discrete

/-!
Scratch development for Discrete.lean proofs.
-/

set_option linter.unusedVariables false

/-- `x / 5 ^ ν₅(x)` is the `divMaxPow` unit part. -/
private theorem div_pow_padicValNat (x : ℕ) :
    x / 5 ^ padicValNat 5 x = Nat.divMaxPow x 5 := by
  have h := congrArg (· / 5 ^ padicValNat 5 x) (Nat.divMaxPow_mul_pow_padicValNat 5 x)
  rw [Nat.mul_div_cancel _ (Nat.pow_pos (by norm_num))] at h
  exact h.symm

-- 1
example {x : ℕ} (hx : 0 < x) : runit x ≠ 0 := by
  unfold runit
  rw [div_pow_padicValNat, Ne, ZMod.natCast_eq_zero_iff]
  exact Nat.not_dvd_divMaxPow (by norm_num) (Nat.ne_of_gt hx)

/-- `5 ∤ a` implies `ν₅(a·b) = ν₅(b)`. -/
private theorem padicValNat_mul_unit {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h5 : ¬ 5 ∣ a) : padicValNat 5 (a * b) = padicValNat 5 b := by
  have hu : ¬ 5 ∣ Nat.divMaxPow b 5 := Nat.not_dvd_divMaxPow (by norm_num) hb
  have hu0 : Nat.divMaxPow b 5 ≠ 0 := fun h => hu (h ▸ dvd_zero 5)
  have hnd : ¬ 5 ∣ a * Nat.divMaxPow b 5 := by
    intro hdvd
    rcases (Nat.Prime.dvd_mul Nat.prime_five).mp hdvd with h | h
    · exact h5 h
    · exact hu h
  have hv0 : padicValNat 5 (a * Nat.divMaxPow b 5) = 0 := by
    by_contra h
    have h1 : (5 : ℕ) ^ 1 ∣ a * Nat.divMaxPow b 5 :=
      (Nat.pow_dvd_iff_le_padicValNat (by norm_num) (Nat.mul_ne_zero ha hu0)).mpr
        (Nat.pos_of_ne_zero h)
    rw [pow_one] at h1
    exact hnd h1
  have hb_eq : b = Nat.divMaxPow b 5 * 5 ^ padicValNat 5 b :=
    (Nat.divMaxPow_mul_pow_padicValNat 5 b).symm
  have h2 : a * b = 5 ^ padicValNat 5 b * (a * Nat.divMaxPow b 5) := by
    conv_lhs => rw [hb_eq]
    ring
  rw [h2, padicValNat_base_pow_mul (by norm_num) (Nat.mul_ne_zero ha hu0), hv0,
    Nat.zero_add]

-- 2
example {m d lam : ℕ} (hd : padicValNat 5 d = m) (hpos : 0 < d)
    (hlam : ¬ 5 ∣ lam) :
    5 ^ m ≤ absModN (lam * d) (5 ^ (m + 1)) := by
  have hd0 : d ≠ 0 := Nat.ne_of_gt hpos
  have hu5 : ¬ 5 ∣ Nat.divMaxPow d 5 := Nat.not_dvd_divMaxPow (by norm_num) hd0
  have hc5 : ¬ 5 ∣ lam * Nat.divMaxPow d 5 := by
    intro h
    rcases (Nat.Prime.dvd_mul Nat.prime_five).mp h with h | h
    · exact hlam h
    · exact hu5 h
  have hd_eq : lam * d = lam * Nat.divMaxPow d 5 * 5 ^ m := by
    conv_lhs => rw [← Nat.divMaxPow_mul_pow_padicValNat 5 d, hd]
    ring
  have hr : lam * d % 5 ^ (m + 1) = lam * Nat.divMaxPow d 5 % 5 * 5 ^ m := by
    rw [hd_eq, pow_succ', Nat.mul_mod_mul_right]
  set c := lam * Nat.divMaxPow d 5 % 5 with hc_def
  have hc1 : 1 ≤ c := by
    have h2 : c ≠ 0 := by
      rw [hc_def]
      exact fun h => hc5 (Nat.dvd_iff_mod_eq_zero.mpr h)
    omega
  have hc4 : c ≤ 4 := by
    have h1 : c < 5 := by
      rw [hc_def]
      exact Nat.mod_lt _ (by norm_num)
    omega
  unfold absModN
  rw [hr, pow_succ']
  interval_cases c <;> omega

-- helper for 3: digit characterization of |y|_N ≥ 5^m for ν₅(y) < m
private theorem absModN_ge_iff_digit {m y : ℕ} (hval : padicValNat 5 y < m)
    (hy : y ≠ 0) :
    5 ^ m ≤ absModN y (5 ^ (m + 1)) ↔
      1 ≤ (qdig m y).val ∧ (qdig m y).val ≤ 3 := by
  unfold absModN
  set E := 5 ^ m with hE
  set r := y % 5 ^ (m + 1) with hr
  set e := r / E with he
  set f := r % E with hf
  have hEpos : 0 < E := by rw [hE]; exact Nat.pow_pos (by norm_num)
  have hN : 5 ^ (m + 1) = 5 * E := by rw [hE]; exact pow_succ' 5 m
  have hrN : r < 5 ^ (m + 1) := Nat.mod_lt _ (Nat.pow_pos (by norm_num))
  have hrN2 : r < 5 * E := by rw [← hN]; exact hrN
  have hr_eq : r = E * e + f := (Nat.div_add_mod r E).symm
  have hf_lt : f < E := Nat.mod_lt _ hEpos
  have he_lt : e < 5 := (Nat.div_lt_iff_lt_mul hEpos).mpr hrN2
  have hfy : f = y % E :=
    Nat.mod_mod_of_dvd y (by rw [hE]; exact Nat.pow_dvd_pow 5 (by omega))
  have hndvd : ¬ 5 ^ m ∣ y := by
    intro h
    have : m ≤ padicValNat 5 y := (Nat.pow_dvd_iff_le_padicValNat (by norm_num) hy).mp h
    omega
  have hf_ne : f ≠ 0 := by
    rw [hfy, hE, Ne, ← Nat.dvd_iff_mod_eq_zero]
    exact hndvd
  have hqval : (qdig m y).val = e := by
    unfold qdig
    rw [ZMod.val_natCast]
    exact Nat.mod_eq_of_lt he_lt
  rw [hqval, hN]
  interval_cases e <;> omega

-- 3
example {m d lam : ℕ} (hd : padicValNat 5 d < m) (hpos : 0 < d)
    (hlam : ¬ 5 ∣ lam) :
    5 ^ m ≤ absModN (lam * d) (5 ^ (m + 1)) ↔
      1 ≤ (qdig m (lam * d)).val ∧ (qdig m (lam * d)).val ≤ 3 := by
  have hlam0 : lam ≠ 0 := fun h => hlam (h ▸ dvd_zero 5)
  have hd0 : d ≠ 0 := Nat.ne_of_gt hpos
  have hval : padicValNat 5 (lam * d) = padicValNat 5 d :=
    padicValNat_mul_unit hlam0 hd0 hlam
  apply absModN_ge_iff_digit
  · rw [hval]; exact hd
  · exact Nat.mul_ne_zero hlam0 hd0

-- 4
example {m j k x : ℕ} (hjm : j < m) (hx : j < padicValNat 5 x) :
    (1 + k * 5 ^ (m - j)) * x % 5 ^ (m + 1) = x % 5 ^ (m + 1) := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx
  have hdvd : 5 ^ (j + 1) ∣ x :=
    (Nat.pow_dvd_iff_le_padicValNat (by norm_num) hx0).mpr hx
  have hdvd2 : 5 ^ (m + 1) ∣ k * 5 ^ (m - j) * x := by
    rw [show m + 1 = (m - j) + (j + 1) by omega, pow_add]
    obtain ⟨y, rfl⟩ := hdvd
    exact ⟨k * y, by ring⟩
  rw [add_mul, one_mul]
  obtain ⟨z, hz⟩ := hdvd2
  rw [hz, Nat.add_mul_mod_self_left]

-- helpers for 5/6
private theorem mod_pow_mul {j m : ℕ} (h : j ≤ m + 1) (v : ℕ) :
    (5 ^ j * v) % 5 ^ (m + 1) = 5 ^ j * (v % 5 ^ (m + 1 - j)) := by
  conv_lhs => rw [show 5 ^ (m + 1) = 5 ^ j * 5 ^ (m + 1 - j) by
    rw [← pow_add]; congr 1; omega]
  exact Nat.mul_mod_mul_left _ _ _

private theorem div_pow_mul {j m : ℕ} (h : j ≤ m) (s : ℕ) :
    (5 ^ j * s) / 5 ^ m = s / 5 ^ (m - j) := by
  conv_lhs => rw [show 5 ^ m = 5 ^ j * 5 ^ (m - j) by
    rw [← pow_add]; congr 1; omega]
  exact Nat.mul_div_mul_left _ _ (Nat.pow_pos (by norm_num))

-- 5
example {m j k x : ℕ} (hjm : j < m) (hx : padicValNat 5 x = j) :
    qdig m ((1 + k * 5 ^ (m - j)) * x) = qdig m x + (k : ZMod 5) * runit x := by
  rcases eq_or_ne x 0 with rfl | hx0
  · simp [qdig, runit]
  set u := Nat.divMaxPow x 5 with hu
  have hu5 : ¬ 5 ∣ u := Nat.not_dvd_divMaxPow (by norm_num) hx0
  have hx_eq : x = u * 5 ^ j := by
    have h := Nat.divMaxPow_mul_pow_padicValNat 5 x
    rw [hx, ← hu] at h
    exact h.symm
  have hL : (1 + k * 5 ^ (m - j)) * x = 5 ^ j * ((1 + k * 5 ^ (m - j)) * u) := by
    rw [hx_eq]; ring
  have hqL : qdig m ((1 + k * 5 ^ (m - j)) * x) =
      (↑((1 + k * 5 ^ (m - j)) * u / 5 ^ (m - j)) : ZMod 5) := by
    unfold qdig
    rw [hL, mod_pow_mul (by omega : j ≤ m + 1), div_pow_mul (by omega : j ≤ m),
      show m + 1 - j = (m - j) + 1 by omega, pow_succ, Nat.mod_mul_right_div_self,
      ZMod.natCast_eq_natCast_iff']
    exact Nat.mod_mod _ _
  have hdiv2 : (1 + k * 5 ^ (m - j)) * u / 5 ^ (m - j) = u / 5 ^ (m - j) + k * u := by
    have h3 : (1 + k * 5 ^ (m - j)) * u = u + 5 ^ (m - j) * (k * u) := by ring
    rw [h3, Nat.add_mul_div_left _ _ (Nat.pow_pos (by norm_num))]
  have hqR : qdig m x = (↑(u / 5 ^ (m - j)) : ZMod 5) := by
    unfold qdig
    have hx2 : x = 5 ^ j * u := by rw [hx_eq]; ring
    rw [hx2, mod_pow_mul (by omega : j ≤ m + 1), div_pow_mul (by omega : j ≤ m),
      show m + 1 - j = (m - j) + 1 by omega, pow_succ, Nat.mod_mul_right_div_self,
      ZMod.natCast_eq_natCast_iff']
    exact Nat.mod_mod _ _
  have hrunit : runit x = (u : ZMod 5) := by
    unfold runit
    rw [hx, hx_eq, Nat.mul_div_cancel _ (Nat.pow_pos (by norm_num))]
  rw [hqL, hdiv2, hqR, hrunit]
  push_cast
  ring

-- 6
example {m l x : ℕ} (hx : padicValNat 5 x = m) :
    qdig m (l * x) = (l : ZMod 5) * runit x := by
  rcases eq_or_ne x 0 with rfl | hx0
  · simp [qdig, runit]
  set u := Nat.divMaxPow x 5 with hu
  have hx_eq : x = u * 5 ^ m := by
    have h := Nat.divMaxPow_mul_pow_padicValNat 5 x
    rw [hx, ← hu] at h
    exact h.symm
  have hL : l * x = 5 ^ m * (l * u) := by rw [hx_eq]; ring
  have hqL : qdig m (l * x) = (↑(l * u % 5) : ZMod 5) := by
    unfold qdig
    rw [hL, pow_succ, Nat.mul_mod_mul_left,
      Nat.mul_div_cancel_left _ (Nat.pow_pos (by norm_num))]
  have hrunit : runit x = (u : ZMod 5) := by
    unfold runit
    rw [hx, hx_eq, Nat.mul_div_cancel _ (Nat.pow_pos (by norm_num))]
  rw [hqL, hrunit, ← Nat.cast_mul, ZMod.natCast_eq_natCast_iff']
  exact Nat.mod_mod _ _

-- helper for 7: division of a sum picks up a carry
private theorem add_div_carry (a b c : ℕ) (hc : 0 < c) :
    (a + b) / c = a / c + b / c + (a % c + b % c) / c := by
  have h1 : a + b = a % c + b % c + c * (a / c + b / c) := by
    have hda := Nat.div_add_mod a c
    have hdb := Nat.div_add_mod b c
    have hmul : c * (a / c) + c * (b / c) = c * (a / c + b / c) := by ring
    omega
  rw [h1, Nat.add_mul_div_left _ _ hc]
  ring

-- qdig via cast of division
private theorem qdig_eq_cast_div (m y : ℕ) :
    qdig m y = ((y / 5 ^ m : ℕ) : ZMod 5) := by
  unfold qdig
  rw [pow_succ, Nat.mod_mul_right_div_self, ZMod.natCast_eq_natCast_iff']
  exact Nat.mod_mod _ _

-- 7
example (m j x : ℕ) :
    (qdig m ((j + 1) * x) - qdig m (j * x) - qdig m x).val ≤ 1 := by
  rw [qdig_eq_cast_div, qdig_eq_cast_div, qdig_eq_cast_div]
  have hkey : (j + 1) * x / 5 ^ m = j * x / 5 ^ m + x / 5 ^ m +
      (j * x % 5 ^ m + x % 5 ^ m) / 5 ^ m := by
    have h : (j + 1) * x = j * x + x := by ring
    rw [h]
    exact add_div_carry _ _ _ (Nat.pow_pos (by norm_num))
  rw [hkey]
  have hsimp : (↑(j * x / 5 ^ m + x / 5 ^ m + (j * x % 5 ^ m + x % 5 ^ m) / 5 ^ m) :
      ZMod 5) - ↑(j * x / 5 ^ m) - ↑(x / 5 ^ m)
      = (↑((j * x % 5 ^ m + x % 5 ^ m) / 5 ^ m) : ZMod 5) := by
    push_cast
    ring
  rw [hsimp, ZMod.val_natCast]
  have hcarry : (j * x % 5 ^ m + x % 5 ^ m) / 5 ^ m ≤ 1 := by
    have h1 : j * x % 5 ^ m < 5 ^ m := Nat.mod_lt _ (Nat.pow_pos (by norm_num))
    have h2 : x % 5 ^ m < 5 ^ m := Nat.mod_lt _ (Nat.pow_pos (by norm_num))
    have h3 : (j * x % 5 ^ m + x % 5 ^ m) / 5 ^ m < 2 :=
      (Nat.div_lt_iff_lt_mul (Nat.pow_pos (by norm_num))).mpr (by omega)
    omega
  exact le_trans (Nat.mod_le _ _) hcarry

-- 8
example {x N : ℕ} (hN : 0 < N) (hx : x % N ≠ 0) :
    absModN (N - x % N) N = absModN x N := by
  have hr : x % N < N := Nat.mod_lt _ hN
  have hr0 : 0 < x % N := Nat.pos_of_ne_zero hx
  have h1 : (N - x % N) % N = N - x % N := Nat.mod_eq_of_lt (by omega)
  have h2 : N - (N - x % N) = x % N := Nat.sub_sub_self (Nat.le_of_lt hr)
  unfold absModN
  rw [h1, h2, min_comm]

-- 9
example (lam d N : ℕ) (hN : 0 < N) :
    circ ((lam * d : ℝ) / N) = (absModN (lam * d) N : ℝ) / N := by
  have hNR : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hdiv : (lam * d : ℝ) / (N : ℝ) =
      ((lam * d % N : ℕ) : ℝ) / N + ((lam * d / N : ℕ) : ℝ) := by
    have h0 := congrArg (Nat.cast (R := ℝ)) (Nat.div_add_mod (lam * d) N)
    push_cast at h0
    rw [mul_comm] at h0
    field_simp
    linarith
  rw [hdiv]
  have hcirc : circ (((lam * d % N : ℕ) : ℝ) / N + ((lam * d / N : ℕ) : ℝ)) =
      circ (((lam * d % N : ℕ) : ℝ) / N) := by
    have h := circ_add_int (((lam * d % N : ℕ) : ℝ) / N) ((lam * d / N : ℕ) : ℤ)
    rwa [Int.cast_natCast] at h
  rw [hcirc]
  set r := lam * d % N with hr
  have hrN : r < N := Nat.mod_lt _ hN
  have hrR0 : (0:ℝ) ≤ (r : ℝ) / N := div_nonneg (Nat.cast_nonneg _) hNR.le
  have hrR1 : (r : ℝ) / N < 1 := by
    rw [div_lt_one hNR]
    exact Nat.cast_lt.mpr hrN
  unfold absModN
  rcases lt_or_ge ((r : ℝ) / N) (1 / 2) with hlt | hge
  · have h2r : 2 * r < N := by
      by_contra hcon
      have hNle : (N:ℝ) ≤ 2 * r := by exact_mod_cast Nat.le_of_not_lt hcon
      have hge2 : (1:ℝ)/2 ≤ (r:ℝ) / N := by
        rw [le_div_iff₀ hNR]
        linarith
      exact absurd hge2 (not_le_of_gt hlt)
    have hmin : min r (N - r) = r := Nat.min_eq_left (by omega)
    rw [circ_eq]
    have hr0 : round ((r : ℝ) / N) = 0 := by
      rw [round_eq_zero_iff]
      exact Set.mem_Ico.mpr ⟨by linarith, hlt⟩
    rw [hr0, Int.cast_zero, sub_zero, abs_of_nonneg hrR0, hmin]
  · have h2r : N ≤ 2 * r := by
      by_contra hcon
      have hrlt : (2 * r : ℝ) < N := by exact_mod_cast lt_of_not_ge hcon
      have hlt2 : (r:ℝ) / N < 1 / 2 := by
        rw [div_lt_iff₀ hNR]
        linarith
      exact absurd hlt2 (not_lt_of_ge hge)
    have hmin : min r (N - r) = N - r := Nat.min_eq_right (by omega)
    rw [circ_eq]
    have hr1 : round ((r : ℝ) / N) = 1 := by
      rw [round_eq_iff]
      refine Set.mem_Ico.mpr ⟨?_, ?_⟩
      · push_cast
        linarith
      · push_cast
        linarith
    rw [hr1, Int.cast_one, hmin]
    have habs : |(r : ℝ) / N - 1| = -((r : ℝ) / N - 1) :=
      abs_of_nonpos (sub_nonpos.mpr hrR1.le)
    rw [habs, neg_sub]
    have hcast : ((N - r : ℕ) : ℝ) = (N : ℝ) - r := Nat.cast_sub (Nat.le_of_lt hrN)
    rw [hcast, sub_div, div_self (ne_of_gt hNR)]

-- 10
example {m lam d : ℕ} (h : 5 ^ m ≤ absModN (lam * d) (5 ^ (m + 1))) :
    (1 / 5 : ℝ) ≤ circ ((lam * d : ℝ) / (5 ^ (m + 1) : ℕ)) := by
  have hN : (0:ℝ) < ((5 ^ (m + 1) : ℕ) : ℝ) :=
    Nat.cast_pos.mpr (Nat.pow_pos (by norm_num))
  rw [circ_mul_div_eq_absModN lam d (5 ^ (m + 1)) (Nat.pow_pos (by norm_num))]
  rw [le_div_iff₀ hN]
  have hR : ((5 ^ m : ℕ) : ℝ) ≤ absModN (lam * d) (5 ^ (m + 1)) := Nat.cast_le.mpr h
  have heq : (1 / 5 : ℝ) * ((5 ^ (m + 1) : ℕ) : ℝ) = (5 ^ m : ℕ) := by
    push_cast
    rw [pow_succ]
    ring
  rw [heq]
  exact hR
