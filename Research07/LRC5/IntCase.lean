/-
Copyright (c) 2026 Research07 contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Research07 contributors
-/
import Research07.LRC5.Filtering

/-!
# The integer case: four speeds, threshold `1/5`

Assembly of the Barajas–Serra argument (arXiv:0710.4495, §3) into the
integer-speeds theorem `lrc5_int`.

Level dichotomy for `|D| = 4`, `gcd D = 1`: `D(0)` and `D(m)` are nonempty,
so a middle level with `≥ 3` elements is impossible, and a low level with
`≥ 3` elements forces the residual shape `|D(0)| = 3`, `|D(m)| = 1` (with
no elements elsewhere). Generic shape → `filtered_multiplier` with `i₀ = m`.
Residual shape → the `ZMod 5` digit chase of `residual_case`.
-/

/-! ### Machinery for the residual digit chase -/

/-- `absModN` depends only on the residue. -/
private theorem absModN_congr {a b N : ℕ} (h : a % N = b % N) :
    absModN a N = absModN b N := by
  unfold absModN; rw [h]

/-- `absModN` as the `ZMod` minimal absolute residue: frees negation symmetry. -/
private theorem absModN_eq_natAbs {x N : ℕ} (hN : 0 < N) :
    absModN x N = ((x : ZMod N).valMinAbs).natAbs := by
  haveI : NeZero N := ⟨hN.ne'⟩
  unfold absModN
  rw [ZMod.valMinAbs_natAbs_eq_min, ZMod.val_natCast]

/-- `absModN` is invariant under negating the residue. -/
private theorem absModN_mul_flip {lam d N : ℕ} (hN : 0 < N) :
    absModN (lam * (N - d % N)) N = absModN (lam * d) N := by
  rw [absModN_eq_natAbs hN, absModN_eq_natAbs hN]
  have hcast : ((lam * (N - d % N) : ℕ) : ZMod N) =
      -((lam * d : ℕ) : ZMod N) := by
    have hle : d % N ≤ N := (Nat.mod_lt d hN).le
    rw [Nat.cast_mul, Nat.cast_sub hle, ZMod.natCast_self, zero_sub,
      ZMod.natCast_mod, mul_neg, ← Nat.cast_mul]
  rw [hcast, ZMod.natAbs_valMinAbs_neg]

/-- `qdig m x` is the mod-5 residue of `x / 5^m`. -/
private theorem qdig_eq (m x : ℕ) : qdig m x = ((x / 5 ^ m : ℕ) : ZMod 5) := by
  unfold qdig
  rw [ZMod.natCast_eq_natCast_iff]
  have hN : (5 : ℕ) ^ (m + 1) = 5 ^ m * 5 := pow_succ 5 m
  have key : x / 5 ^ m = (x % 5 ^ (m + 1)) / 5 ^ m + 5 * (x / 5 ^ (m + 1)) := by
    conv_lhs => rw [← Nat.div_add_mod x (5 ^ (m + 1)), hN]
    rw [mul_assoc, add_comm,
      Nat.add_mul_div_left _ _ (by positivity : (0 : ℕ) < 5 ^ m), ← hN]
  rw [key]
  exact (Nat.add_mul_mod_self_left _ _ _).symm

/-- Adding a multiple of `5^m` shifts the leading digit by the coefficient. -/
private theorem qdig_add_hi (m a c : ℕ) :
    qdig m (a + c * 5 ^ m) = qdig m a + (c : ZMod 5) := by
  rw [qdig_eq, qdig_eq, mul_comm c (5 ^ m),
    Nat.add_mul_div_left _ _ (by positivity : (0 : ℕ) < 5 ^ m), Nat.cast_add]

/-- For `λ = j + K·5^m` and a unit `x`, the leading digit of `λx` is
`qdig (j·x) + K·runit x`. -/
private theorem qdig_shift {m j K x : ℕ} (hx : padicValNat 5 x = 0) :
    qdig m ((j + K * 5 ^ m) * x) = qdig m (j * x) + (K : ZMod 5) * runit x := by
  have h1 : (j + K * 5 ^ m) * x = j * x + (K * x) * 5 ^ m := by ring
  rw [h1, qdig_add_hi, Nat.cast_mul]
  have hxu : (x : ZMod 5) = runit x := by
    unfold runit
    rw [hx, pow_zero, Nat.div_one]
  rw [hxu]

/-- The two carries in `qdig(2x)`, `qdig(3x)` relative to `qdig x` are `∈ {0,1}`. -/
private theorem qdig_carries (m x : ℕ) :
    ∃ c d : ZMod 5, c.val ≤ 1 ∧ d.val ≤ 1 ∧
      qdig m (2 * x) = 2 * qdig m x + c ∧
      qdig m (3 * x) = 3 * qdig m x + c + d := by
  have h1 := qdig_add_one m 1 x
  have h2 := qdig_add_one m 2 x
  have e1 : qdig m ((1 + 1) * x) - qdig m (1 * x) - qdig m x =
      qdig m (2 * x) - 2 * qdig m x := by
    rw [show ((1 : ℕ) + 1) * x = 2 * x from rfl, one_mul, two_mul]
    ring
  have e2 : qdig m ((2 + 1) * x) - qdig m (2 * x) - qdig m x =
      qdig m (3 * x) - qdig m (2 * x) - qdig m x := by
    rw [show ((2 : ℕ) + 1) * x = 3 * x from rfl]
  exact ⟨qdig m (2 * x) - 2 * qdig m x,
    qdig m (3 * x) - qdig m (2 * x) - qdig m x,
    e1 ▸ h1, e2 ▸ h2, by ring, by ring⟩

private abbrev bz (b : Bool) : ZMod 5 := if b then 1 else 0
private abbrev gd (x : ZMod 5) : Prop := x = 1 ∨ x = 2 ∨ x = 3

/-- `val ≤ 1` means `c ∈ {0,1}`. -/
private theorem zmod01 {c : ZMod 5} (h : c.val ≤ 1) : c = 0 ∨ c = 1 := by
  have hv : c.val = 0 ∨ c.val = 1 := by omega
  rcases hv with h' | h'
  · left; rw [← ZMod.natCast_zmod_val c, h']; exact Nat.cast_zero
  · right; rw [← ZMod.natCast_zmod_val c, h']; exact Nat.cast_one

private theorem bz_of_val {c : ZMod 5} (hc : c.val ≤ 1) :
    bz (decide (c = 1)) = c := by
  rcases zmod01 hc with h | h <;> rw [h] <;> rfl

/-- `gd` gives the numerical digit bounds needed by `absModN_ge_iff_qdig`. -/
private theorem gd_val {x : ZMod 5} (h : gd x) : 1 ≤ x.val ∧ x.val ≤ 3 := by
  rcases h with rfl | rfl | rfl <;> decide

/-- Pigeonhole: three elements of `{1,2}` — if `a` differs from both, `b = c`. -/
private theorem zmod5_third {a b c : ZMod 5} (ha : a = 1 ∨ a = 2)
    (hb : b = 1 ∨ b = 2) (hc : c = 1 ∨ c = 2) (hab : a ≠ b) (hac : a ≠ c) :
    b = c := by
  rcases ha with rfl|rfl <;> rcases hb with rfl|rfl <;> rcases hc with rfl|rfl <;>
    first | rfl | (exact (hab rfl).elim) | (exact (hac rfl).elim)

/-- Residues `c ∈ {1,2,3,4}` are nonzero in `ZMod 5`. -/
private theorem zmod5_cast_ne_zero {c : ℕ} (h1 : 0 < c) (h5 : c < 5) :
    ((c : ℕ) : ZMod 5) ≠ 0 := by
  intro h
  have h2 := (ZMod.natCast_eq_zero_iff c 5).mp h
  have h3 := Nat.le_of_dvd h1 h2
  omega

private theorem zmod5_one_ne : (1 : ZMod 5) ≠ 0 := by decide
private theorem zmod5_two_ne : (2 : ZMod 5) ≠ 0 := by decide
private theorem zmod5_2mul3 : (2 : ZMod 5) * 3 = 1 := by decide

private theorem zmod5_2inv : (2 : ZMod 5)⁻¹ = 3 := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  exact inv_eq_of_mul_eq_one_right zmod5_2mul3

/-- Sign-normalized representative of `d` modulo `N`: preserves `absModN`
under any multiplier; for `5 ∤ d` and `5 ∣ N` its residue mod 5 is in
`{1, 2}`. -/
private def normU5 (N d : ℕ) : ℕ := if d % 5 ≤ 2 then d else N - d % N

private theorem normU5_absModN {lam d N : ℕ} (hN : 0 < N) :
    absModN (lam * normU5 N d) N = absModN (lam * d) N := by
  unfold normU5
  split_ifs with _
  · rfl
  · exact absModN_mul_flip hN

/-- For a unit `d`, the normalized representative has mod-5 residue in
`{1,2}` (when `5 ∣ N`). -/
private theorem normU5_mod {d N : ℕ} (hN : 0 < N) (h5 : 5 ∣ N)
    (hd : ¬ 5 ∣ d) :
    normU5 N d % 5 = 1 ∨ normU5 N d % 5 = 2 := by
  have hd5 : d % 5 = 1 ∨ d % 5 = 2 ∨ d % 5 = 3 ∨ d % 5 = 4 := by
    have h1 : d % 5 < 5 := Nat.mod_lt _ (by norm_num)
    have h2 : d % 5 ≠ 0 := fun h => hd (Nat.dvd_iff_mod_eq_zero.mpr h)
    omega
  have hdN : d % N % 5 = d % 5 := Nat.mod_mod_of_dvd d h5
  have hN5 : N % 5 = 0 := Nat.dvd_iff_mod_eq_zero.mp h5
  unfold normU5
  split_ifs with h
  · rcases hd5 with h1 | h1 | h1 | h1 <;> omega
  · have hbd : d % N < N := Nat.mod_lt _ hN
    have h2 : (N - d % N) % 5 = 5 - d % 5 := by omega
    rw [h2]
    omega

/-- For a positive unit `d`, the normalized representative is again a
positive unit, with `runit ∈ {1, 2}`. -/
private theorem normU5_spec {d N : ℕ} (hN : 0 < N) (h5 : 5 ∣ N)
    (hd : ¬ 5 ∣ d) (hdpos : 0 < d) :
    padicValNat 5 (normU5 N d) = 0 ∧ 0 < normU5 N d ∧
      (runit (normU5 N d) = 1 ∨ runit (normU5 N d) = 2) := by
  have hm := normU5_mod hN h5 hd
  have h5nu : ¬ 5 ∣ normU5 N d := by
    intro h'
    have hz : normU5 N d % 5 = 0 := Nat.dvd_iff_mod_eq_zero.mp h'
    rcases hm with h | h <;> omega
  have hν : padicValNat 5 (normU5 N d) = 0 :=
    padicValNat.eq_zero_of_not_dvd h5nu
  have hpos' : 0 < normU5 N d := by
    unfold normU5
    split_ifs with h
    · exact hdpos
    · have : d % N < N := Nat.mod_lt _ hN
      omega
  have hru : runit (normU5 N d) = ((normU5 N d % 5 : ℕ) : ZMod 5) := by
    unfold runit
    rw [hν, pow_zero, Nat.div_one, ZMod.natCast_mod]
  refine ⟨hν, hpos', ?_⟩
  rw [hru]
  rcases hm with h | h <;> rw [h]
  · left; exact Nat.cast_one
  · right; norm_num

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
    (∃ k : ZMod 5, gd (3 * q₁ + bz c₁ + bz d₁ + k) ∧
      gd (3 * q₂ + bz c₂ + bz d₂ + k) ∧
      gd (3 * q₃ + bz c₃ + bz d₃ + r * k)) := by
  decide

/-- `qdig` of `j·(1+k·5^m)·x` unfolds to the digit-shift formula. -/
private theorem qdig_lam {m j k x : ℕ} (hx : padicValNat 5 x = 0) :
    qdig m (j * (1 + k * 5 ^ m) * x) =
      qdig m (j * x) + (j : ZMod 5) * (k : ZMod 5) * runit x := by
  have h1 : j * (1 + k * 5 ^ m) * x = (j + (j * k) * 5 ^ m) * x := by ring
  rw [h1, qdig_shift hx, Nat.cast_mul]

/-- A leading digit in `{1,2,3}` yields `absModN ≥ 5^m` for a unit. -/
private theorem good_of_gd {m lam x : ℕ} (hm : 0 < m) (hlam : ¬ 5 ∣ lam)
    (hx : 0 < x) (hνx : padicValNat 5 x = 0) {e : ZMod 5}
    (hqe : qdig m (lam * x) = e) (hgd : gd e) :
    5 ^ m ≤ absModN (lam * x) (5 ^ (m + 1)) :=
  (absModN_ge_iff_qdig (by rw [hνx]; exact hm) hx hlam).mpr
    (by rw [hqe]; exact gd_val hgd)

/-- For three positive units, two sharing residue class `s ∈ {1,2}` mod 5 and
the third in `s' ∈ {1,2}`, some `λ = j·(1 + k·5^m)` with `j ∈ {1,2,3}`,
`5 ∤ λ` puts every leading digit in `{1,2,3}` — hence every `absModN ≥ 5^m`.
This is the `ZMod 5` digit chase of Barajas–Serra §3. -/
private theorem three_units {m : ℕ} (hm : 0 < m) {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hνa : padicValNat 5 a = 0) (hνb : padicValNat 5 b = 0)
    (hνc : padicValNat 5 c = 0)
    {s s' : ZMod 5} (hs : s = 1 ∨ s = 2) (hs' : s' = 1 ∨ s' = 2)
    (hra : runit a = s) (hrb : runit b = s) (hrc : runit c = s') :
    ∃ lam : ℕ, ¬ 5 ∣ lam ∧
      5 ^ m ≤ absModN (lam * a) (5 ^ (m + 1)) ∧
      5 ^ m ≤ absModN (lam * b) (5 ^ (m + 1)) ∧
      5 ^ m ≤ absModN (lam * c) (5 ^ (m + 1)) := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have h2ne : ((2 : ℕ) : ZMod 5) ≠ 0 :=
    zmod5_cast_ne_zero (by norm_num) (by norm_num)
  have hsnz : s ≠ 0 := by
    rcases hs with rfl | rfl
    · exact zmod5_one_ne
    · exact zmod5_two_ne
  obtain ⟨ca, da, hca, hda, h2a, h3a⟩ := qdig_carries m a
  obtain ⟨cb, db, hcb, hdb, h2b, h3b⟩ := qdig_carries m b
  obtain ⟨cc, dc, hcc, hdc, h2c, h3c⟩ := qdig_carries m c
  have h2inv : (2 : ZMod 5)⁻¹ = 3 := zmod5_2inv
  have hr : s' * s⁻¹ = 1 ∨ s' * s⁻¹ = 2 ∨ s' * s⁻¹ = 3 := by
    rcases hs with rfl | rfl <;> rcases hs' with rfl | rfl
    · exact Or.inl (by rw [inv_one, mul_one])
    · exact Or.inr (Or.inl (by rw [inv_one, mul_one]))
    · exact Or.inr (Or.inr (by rw [h2inv, one_mul]))
    · exact Or.inl (mul_inv_cancel₀ zmod5_two_ne)
  have h5lam : ∀ jN k : ℕ, jN = 1 ∨ jN = 2 ∨ jN = 3 →
      ¬ 5 ∣ jN * (1 + k * 5 ^ m) := by
    intro jN k hj hdiv
    have hM5 : 5 ∣ jN * (k * 5 ^ m) := by
      have h55 : (5 : ℕ) ∣ 5 ^ m := by
        obtain ⟨e, rfl⟩ : ∃ e, m = e + 1 := ⟨m - 1, by omega⟩
        exact ⟨5 ^ e, pow_succ' 5 e⟩
      rw [show jN * (k * 5 ^ m) = (jN * k) * 5 ^ m from by ring]
      exact h55.mul_left (jN * k)
    have hmod5 : (jN * (1 + k * 5 ^ m)) % 5 = jN := by
      rw [mul_add, mul_one, Nat.add_mod,
        Nat.dvd_iff_mod_eq_zero.mp hM5, add_zero]
      rcases hj with rfl | rfl | rfl <;> norm_num
    have h0 := Nat.dvd_iff_mod_eq_zero.mp hdiv
    rw [hmod5] at h0
    rcases hj with rfl | rfl | rfl <;> norm_num at h0
  obtain hch | hch | hch := digit_chase (s' * s⁻¹) (qdig m a) (qdig m b)
    (qdig m c) (decide (ca = 1)) (decide (cb = 1)) (decide (cc = 1))
    (decide (da = 1)) (decide (db = 1)) (decide (dc = 1)) hr
  -- case `j = 1`: `λ = 1 + k·5^m`, `kZ = κ·s⁻¹`
  · obtain ⟨κ, g1, g2, g3⟩ := hch
    set kZ : ZMod 5 := κ * s⁻¹ with hkZ
    have hκs : kZ * s = κ := by
      rw [hkZ]
      calc κ * s⁻¹ * s = κ * (s⁻¹ * s) := by ring
        _ = κ := by rw [inv_mul_cancel₀ hsnz, mul_one]
    have hκr : kZ * s' = (s' * s⁻¹) * κ := by rw [hkZ]; ring
    refine ⟨1 * (1 + kZ.val * 5 ^ m), h5lam 1 kZ.val (Or.inl rfl), ?_, ?_, ?_⟩
    · have qe : qdig m (1 * (1 + kZ.val * 5 ^ m) * a) = qdig m a + κ := by
        rw [qdig_lam hνa, one_mul, Nat.cast_one, one_mul,
          ZMod.natCast_zmod_val, hra, hκs]
      exact good_of_gd hm (h5lam 1 kZ.val (Or.inl rfl)) ha hνa qe g1
    · have qe : qdig m (1 * (1 + kZ.val * 5 ^ m) * b) = qdig m b + κ := by
        rw [qdig_lam hνb, one_mul, Nat.cast_one, one_mul,
          ZMod.natCast_zmod_val, hrb, hκs]
      exact good_of_gd hm (h5lam 1 kZ.val (Or.inl rfl)) hb hνb qe g2
    · have qe : qdig m (1 * (1 + kZ.val * 5 ^ m) * c) =
          qdig m c + (s' * s⁻¹) * κ := by
        rw [qdig_lam hνc, one_mul, Nat.cast_one, one_mul,
          ZMod.natCast_zmod_val, hrc, hκr]
      exact good_of_gd hm (h5lam 1 kZ.val (Or.inl rfl)) hc hνc qe g3
  -- case `j = 2`
  · obtain ⟨κ, g1, g2, g3⟩ := hch
    rw [bz_of_val hca] at g1
    rw [bz_of_val hcb] at g2
    rw [bz_of_val hcc] at g3
    set kZ : ZMod 5 := κ * (((2 : ℕ) : ZMod 5) * s)⁻¹ with hkZ
    have h2nz : (((2 : ℕ) : ZMod 5) * s) ≠ 0 := mul_ne_zero h2ne hsnz
    have hκs : ((2 : ℕ) : ZMod 5) * kZ * s = κ := by
      rw [hkZ]
      calc ((2 : ℕ) : ZMod 5) * (κ * (((2 : ℕ) : ZMod 5) * s)⁻¹) * s
          = κ * ((((2 : ℕ) : ZMod 5) * s)⁻¹ * (((2 : ℕ) : ZMod 5) * s)) := by ring
        _ = κ := by rw [inv_mul_cancel₀ h2nz, mul_one]
    have hκr : ((2 : ℕ) : ZMod 5) * kZ * s' = (s' * s⁻¹) * κ := by
      rw [hkZ]
      have h2 : ((2 : ℕ) : ZMod 5)⁻¹ * (((2 : ℕ) : ZMod 5) * s') = s' := by
        rw [← mul_assoc, inv_mul_cancel₀ h2ne, one_mul]
      calc ((2 : ℕ) : ZMod 5) * (κ * (((2 : ℕ) : ZMod 5) * s)⁻¹) * s'
          = κ * ((((2 : ℕ) : ZMod 5) * s)⁻¹ * (((2 : ℕ) : ZMod 5) * s')) := by
            ring
        _ = κ * (s⁻¹ * s') := by
            congr 1
            rw [mul_inv_rev, mul_assoc, h2]
        _ = (s' * s⁻¹) * κ := by ring
    refine ⟨2 * (1 + kZ.val * 5 ^ m), h5lam 2 kZ.val (Or.inr (Or.inl rfl)),
      ?_, ?_, ?_⟩
    · have qe : qdig m (2 * (1 + kZ.val * 5 ^ m) * a) =
          2 * qdig m a + ca + κ := by
        rw [qdig_lam hνa, h2a, ZMod.natCast_zmod_val, hra, hκs]
      exact good_of_gd hm (h5lam 2 kZ.val (Or.inr (Or.inl rfl))) ha hνa qe g1
    · have qe : qdig m (2 * (1 + kZ.val * 5 ^ m) * b) =
          2 * qdig m b + cb + κ := by
        rw [qdig_lam hνb, h2b, ZMod.natCast_zmod_val, hrb, hκs]
      exact good_of_gd hm (h5lam 2 kZ.val (Or.inr (Or.inl rfl))) hb hνb qe g2
    · have qe : qdig m (2 * (1 + kZ.val * 5 ^ m) * c) =
          2 * qdig m c + cc + (s' * s⁻¹) * κ := by
        rw [qdig_lam hνc, h2c, ZMod.natCast_zmod_val, hrc, hκr]
      exact good_of_gd hm (h5lam 2 kZ.val (Or.inr (Or.inl rfl))) hc hνc qe g3
  -- case `j = 3`
  · obtain ⟨κ, g1, g2, g3⟩ := hch
    rw [bz_of_val hca, bz_of_val hda] at g1
    rw [bz_of_val hcb, bz_of_val hdb] at g2
    rw [bz_of_val hcc, bz_of_val hdc] at g3
    set kZ : ZMod 5 := κ * (((3 : ℕ) : ZMod 5) * s)⁻¹ with hkZ
    have h3ne : ((3 : ℕ) : ZMod 5) ≠ 0 :=
      zmod5_cast_ne_zero (by norm_num) (by norm_num)
    have h3nz : (((3 : ℕ) : ZMod 5) * s) ≠ 0 := mul_ne_zero h3ne hsnz
    have hκs : ((3 : ℕ) : ZMod 5) * kZ * s = κ := by
      rw [hkZ]
      calc ((3 : ℕ) : ZMod 5) * (κ * (((3 : ℕ) : ZMod 5) * s)⁻¹) * s
          = κ * ((((3 : ℕ) : ZMod 5) * s)⁻¹ * (((3 : ℕ) : ZMod 5) * s)) := by ring
        _ = κ := by rw [inv_mul_cancel₀ h3nz, mul_one]
    have hκr : ((3 : ℕ) : ZMod 5) * kZ * s' = (s' * s⁻¹) * κ := by
      rw [hkZ]
      have h3 : ((3 : ℕ) : ZMod 5)⁻¹ * (((3 : ℕ) : ZMod 5) * s') = s' := by
        rw [← mul_assoc, inv_mul_cancel₀ h3ne, one_mul]
      calc ((3 : ℕ) : ZMod 5) * (κ * (((3 : ℕ) : ZMod 5) * s)⁻¹) * s'
          = κ * ((((3 : ℕ) : ZMod 5) * s)⁻¹ * (((3 : ℕ) : ZMod 5) * s')) := by
            ring
        _ = κ * (s⁻¹ * s') := by
            congr 1
            rw [mul_inv_rev, mul_assoc, h3]
        _ = (s' * s⁻¹) * κ := by ring
    refine ⟨3 * (1 + kZ.val * 5 ^ m), h5lam 3 kZ.val (Or.inr (Or.inr rfl)),
      ?_, ?_, ?_⟩
    · have qe : qdig m (3 * (1 + kZ.val * 5 ^ m) * a) =
          3 * qdig m a + ca + da + κ := by
        rw [qdig_lam hνa, h3a, ZMod.natCast_zmod_val, hra, hκs]
      exact good_of_gd hm (h5lam 3 kZ.val (Or.inr (Or.inr rfl))) ha hνa qe g1
    · have qe : qdig m (3 * (1 + kZ.val * 5 ^ m) * b) =
          3 * qdig m b + cb + db + κ := by
        rw [qdig_lam hνb, h3b, ZMod.natCast_zmod_val, hrb, hκs]
      exact good_of_gd hm (h5lam 3 kZ.val (Or.inr (Or.inr rfl))) hb hνb qe g2
    · have qe : qdig m (3 * (1 + kZ.val * 5 ^ m) * c) =
          3 * qdig m c + cc + dc + (s' * s⁻¹) * κ := by
        rw [qdig_lam hνc, h3c, ZMod.natCast_zmod_val, hrc, hκr]
      exact good_of_gd hm (h5lam 3 kZ.val (Or.inr (Or.inr rfl))) hc hνc qe g3

/-- **Residual case**: three units `A` plus one top-level element `d₄`.
Via sign flips `d ↦ N − d` (which preserve `|λd|_N`) we may assume the units
land in residue classes `{1,2}` mod 5; the `ZMod 5` digit chase of
Barajas–Serra §3 then produces `λ = j·(1 + k·5^m)` with all digits in
`{1,2,3}`, while `d₄` stays good automatically. -/
theorem residual_case {D : Finset ℕ} (hpos : ∀ d ∈ D, 0 < d) {m : ℕ}
    (hm : 0 < m) (h0 : (level D 0).card = 3) (hmtop : (level D m).card = 1)
    (hall : ∀ d ∈ D, padicValNat 5 d = 0 ∨ padicValNat 5 d = m) :
    ∃ lam : ℕ, ¬ 5 ∣ lam ∧
      ∀ d ∈ D, 5 ^ m ≤ absModN (lam * d) (5 ^ (m + 1)) := by
  classical
  have hNpos : 0 < 5 ^ (m + 1) := Nat.pow_pos (by norm_num)
  have h5N : 5 ∣ 5 ^ (m + 1) := ⟨5 ^ m, pow_succ' 5 m⟩
  obtain ⟨u₁, u₂, u₃, h12, h13, h23, hU⟩ := Finset.card_eq_three.mp h0
  have hmem : ∀ d ∈ level D 0, d ∈ D ∧ padicValNat 5 d = 0 :=
    fun d hd => Finset.mem_filter.mp hd
  obtain ⟨hd1, hν1⟩ := hmem u₁ (by rw [hU]; exact Finset.mem_insert_self _ _)
  obtain ⟨hd2, hν2⟩ := hmem u₂ (by rw [hU]; simp)
  obtain ⟨hd3, hν3⟩ := hmem u₃ (by rw [hU]; simp)
  have hnd : ∀ d ∈ D, padicValNat 5 d = 0 → ¬ 5 ∣ d := by
    intro d hd hν hdiv
    have h1 : (5 : ℕ) ^ 1 ∣ d := by rwa [pow_one]
    have h2 := (Nat.pow_dvd_iff_le_padicValNat (by norm_num)
      (hpos d hd).ne').mp h1
    omega
  obtain ⟨hνw1, hwp1, hrw1⟩ :=
    normU5_spec hNpos h5N (hnd u₁ hd1 hν1) (hpos u₁ hd1)
  obtain ⟨hνw2, hwp2, hrw2⟩ :=
    normU5_spec hNpos h5N (hnd u₂ hd2 hν2) (hpos u₂ hd2)
  obtain ⟨hνw3, hwp3, hrw3⟩ :=
    normU5_spec hNpos h5N (hnd u₃ hd3 hν3) (hpos u₃ hd3)
  -- shared tail: bounds on the three normalized units settle all of `D`
  have finish : ∀ lam : ℕ, ¬ 5 ∣ lam →
      5 ^ m ≤ absModN (lam * normU5 (5 ^ (m + 1)) u₁) (5 ^ (m + 1)) →
      5 ^ m ≤ absModN (lam * normU5 (5 ^ (m + 1)) u₂) (5 ^ (m + 1)) →
      5 ^ m ≤ absModN (lam * normU5 (5 ^ (m + 1)) u₃) (5 ^ (m + 1)) →
      ∀ d ∈ D, 5 ^ m ≤ absModN (lam * d) (5 ^ (m + 1)) := by
    intro lam hlam g1 g2 g3 d hd
    rcases hall d hd with hν0 | hνm
    · have hdl : d ∈ level D 0 := Finset.mem_filter.mpr ⟨hd, hν0⟩
      rw [hU, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hdl
      rcases hdl with rfl | rfl | rfl
      · rwa [← normU5_absModN hNpos]
      · rwa [← normU5_absModN hNpos]
      · rwa [← normU5_absModN hNpos]
    · exact absModN_top_ge hνm (hpos d hd) hlam
  -- pigeonhole on the three residues in `{1,2}`
  by_cases e12 : runit (normU5 (5 ^ (m + 1)) u₁) =
    runit (normU5 (5 ^ (m + 1)) u₂)
  · obtain ⟨lam, hlam, g1, g2, g3⟩ :=
      three_units hm hwp1 hwp2 hwp3 hνw1 hνw2 hνw3 hrw1 hrw3 rfl e12.symm rfl
    exact ⟨lam, hlam, finish lam hlam g1 g2 g3⟩
  · by_cases e13 : runit (normU5 (5 ^ (m + 1)) u₁) =
      runit (normU5 (5 ^ (m + 1)) u₃)
    · obtain ⟨lam, hlam, g1, g3, g2⟩ :=
        three_units hm hwp1 hwp3 hwp2 hνw1 hνw3 hνw2 hrw1 hrw2 rfl e13.symm rfl
      exact ⟨lam, hlam, finish lam hlam g1 g2 g3⟩
    · have e23 : runit (normU5 (5 ^ (m + 1)) u₂) =
          runit (normU5 (5 ^ (m + 1)) u₃) :=
        zmod5_third hrw1 hrw2 hrw3 e12 e13
      obtain ⟨lam, hlam, g2, g3, g1⟩ :=
        three_units hm hwp2 hwp3 hwp1 hνw2 hνw3 hνw1 hrw2 hrw1 rfl e23.symm rfl
      exact ⟨lam, hlam, finish lam hlam g1 g2 g3⟩

/-- **Multiplier existence** for four coprime positive integers: some `λ`
coprime to `5` puts every element at circular distance `≥ 5^m` in `ℤ/N`,
`N = 5^{m+1}`, `m = max ν₅(D)`. Equivalent to `χ_r(N, D) ≤ 5`. -/
theorem exists_multiplier4 (D : Finset ℕ) (hpos : ∀ d ∈ D, 0 < d)
    (hgcd : D.gcd id = 1) (hcard : D.card = 4) :
    ∃ lam : ℕ, ¬ 5 ∣ lam ∧ ∀ d ∈ D,
      5 ^ (D.sup (padicValNat 5)) ≤
        absModN (lam * d) (5 ^ (D.sup (padicValNat 5) + 1)) := by
  classical
  set m := D.sup (padicValNat 5) with hm
  have hle : ∀ d ∈ D, padicValNat 5 d ≤ m := fun d hd => Finset.le_sup hd
  have hDne : D.Nonempty := Finset.card_ne_zero.mp (by omega)
  -- level `m` is nonempty: the sup is attained
  obtain ⟨dm, hdm⟩ : (level D m).Nonempty := by
    obtain ⟨d, hd, heq⟩ := Finset.exists_mem_eq_sup D hDne (padicValNat 5)
    exact ⟨d, Finset.mem_filter.mpr ⟨hd, heq.symm⟩⟩
  obtain ⟨hdmD, hνm⟩ := Finset.mem_filter.mp hdm
  -- level `0` is nonempty: `gcd D = 1` forces a unit
  have h0ne : (level D 0).Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    have h5 : ∀ d ∈ D, 5 ∣ d := by
      intro d hd
      by_contra hnd
      have hν : padicValNat 5 d = 0 := padicValNat.eq_zero_of_not_dvd hnd
      have : d ∈ level D 0 := Finset.mem_filter.mpr ⟨hd, hν⟩
      rw [hne] at this
      exact Finset.notMem_empty _ this
    have h51 : (5 : ℕ) ∣ D.gcd id := Finset.dvd_gcd h5
    rw [hgcd] at h51
    norm_num at h51
  by_cases hg : ∀ j, j < m → 2 * (level D j).card ≤ 4
  · -- generic case: `filtered_multiplier` with `i₀ = m`
    obtain ⟨lam, hlam, _, hgood⟩ :=
      filtered_multiplier D hpos hle (le_refl m) hg
    refine ⟨lam, hlam, fun d hd => ?_⟩
    rcases lt_or_eq_of_le (hle d hd) with hlt | heq
    · exact (absModN_ge_iff_qdig hlt (hpos d hd) hlam).mpr (hgood d hd hlt)
    · exact absModN_top_ge heq (hpos d hd) hlam
  · -- residual: some level `j < m` has `≥ 3` elements
    push_neg at hg
    obtain ⟨j, hjm, hbig⟩ := hg
    -- `|level j| ≤ |D| = 4`, and `= 4` would force `m = j`, so it is `3`
    have hcardj : (level D j).card = 3 := by
      have hle4 : (level D j).card ≤ 4 := by
        rw [← hcard]
        exact Finset.card_le_card (Finset.filter_subset _ _)
      rcases eq_or_lt_of_le hle4 with h4 | hlt4
      · exfalso
        have hDj : level D j = D :=
          Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
            (by rw [hcard, h4])
        have hallj : ∀ d ∈ D, padicValNat 5 d = j := by
          intro d hd
          have : d ∈ level D j := by rw [hDj]; exact hd
          exact (Finset.mem_filter.mp this).2
        have hmj : m ≤ j :=
          Finset.sup_le_iff.mpr fun d hd => le_of_eq (hallj d hd)
        omega
      · omega
    -- so `D \ level j` is a singleton `{e}`
    have hsub0 : level D j ⊆ D := Finset.filter_subset _ _
    have hcompl : (D \ level D j).card = 1 := by
      rw [Finset.card_sdiff_of_subset hsub0, hcard, hcardj]
    obtain ⟨e, he⟩ := Finset.card_eq_one.mp hcompl
    obtain ⟨d0, hd0⟩ := h0ne
    obtain ⟨hd0D, hν0⟩ := Finset.mem_filter.mp hd0
    -- `j = 0`: otherwise `d0` (level 0) and `dm` (level m) are distinct
    -- elements of the singleton complement, forcing `m = 0`, absurd
    have hj0 : j = 0 := by
      by_contra hjn
      have hd0c : d0 ∈ D \ level D j := Finset.mem_sdiff.mpr
        ⟨hd0D, fun h => hjn ((Finset.mem_filter.mp h).2.symm.trans hν0)⟩
      have hdmc : dm ∈ D \ level D j := Finset.mem_sdiff.mpr
        ⟨hdmD, fun h => (ne_of_lt hjm)
          ((Finset.mem_filter.mp h).2.symm.trans hνm)⟩
      rw [he] at hd0c hdmc
      have h0m : d0 = dm :=
        (Finset.mem_singleton.mp hd0c).trans (Finset.mem_singleton.mp hdmc).symm
      have hm0 : m = 0 :=
        hνm.symm.trans (by rw [h0m]) |>.trans hν0
      omega
    subst hj0
    -- `|level m| = 1`: it is contained in the singleton complement
    have hmtop : (level D m).card = 1 := by
      have hsub : level D m ⊆ {e} := by
        intro x hx
        obtain ⟨hxD, hνx⟩ := Finset.mem_filter.mp hx
        have hxn0 : x ∉ level D 0 := fun h0x =>
          absurd (((Finset.mem_filter.mp h0x).2).symm.trans hνx) (by omega)
        rw [Finset.mem_singleton]
        have : x ∈ D \ level D 0 := Finset.mem_sdiff.mpr ⟨hxD, hxn0⟩
        rw [he] at this
        exact Finset.mem_singleton.mp this
      have hdmc : dm ∈ D \ level D 0 := Finset.mem_sdiff.mpr
        ⟨hdmD, fun h0d =>
          absurd (((Finset.mem_filter.mp h0d).2).symm.trans hνm) (by omega)⟩
      rw [he] at hdmc
      have hdme : dm = e := Finset.mem_singleton.mp hdmc
      rw [Finset.card_eq_one]
      exact ⟨e, Finset.eq_singleton_iff_unique_mem.mpr
        ⟨hdme ▸ hdm, fun x hx => Finset.mem_singleton.mp (hsub hx)⟩⟩
    -- every element is at level `0` or `m`
    have hall : ∀ d ∈ D, padicValNat 5 d = 0 ∨ padicValNat 5 d = m := by
      intro d hd
      by_cases h0d : d ∈ level D 0
      · exact Or.inl (Finset.mem_filter.mp h0d).2
      · have hdc : d ∈ D \ level D 0 := Finset.mem_sdiff.mpr ⟨hd, h0d⟩
        rw [he] at hdc
        have hde : d = e := Finset.mem_singleton.mp hdc
        have hdme : dm = e := by
          have hdm0 : dm ∈ D \ level D 0 := Finset.mem_sdiff.mpr
            ⟨hdmD, fun h0x =>
              absurd (((Finset.mem_filter.mp h0x).2).symm.trans hνm) (by omega)⟩
          rw [he] at hdm0
          exact Finset.mem_singleton.mp hdm0
        rw [hde.trans hdme.symm]
        exact Or.inr hνm
    exact residual_case hpos hjm hcardj hmtop hall

/-- **Lonely runner, integer speeds, `|D| ≤ 4`**: any set of at most four
positive integers has a common lonely time `t > 0` at distance `≥ 1/5`.
(Pad `D` to four elements, divide out the gcd, apply `exists_multiplier4`,
bridge `t = λ/(g·5^{m+1})`.) -/
theorem lrc5_int (D : Finset ℕ) (hpos : ∀ d ∈ D, 0 < d) (hcard : D.card ≤ 4) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ D, (1 / 5 : ℝ) ≤ circ (t * d) := by
  classical
  rcases D.eq_empty_or_nonempty with rfl | hDne
  · exact ⟨1, one_pos, fun d hd => (Finset.notMem_empty d hd).elim⟩
  -- pad `D` to exactly four elements with fresh values above `max D`
  set K := D.sup id with hK
  set B := (Finset.range (4 - D.card)).image (fun i => K + 1 + i) with hB
  set D' := D ∪ B with hD'
  have hBinj : Set.InjOn (fun i => K + 1 + i) (Finset.range (4 - D.card)) := by
    intro a _ b _ h
    change K + 1 + a = K + 1 + b at h
    exact Nat.add_left_cancel h
  have hBcard : B.card = 4 - D.card := by
    rw [hB, Finset.card_image_of_injOn hBinj, Finset.card_range]
  have hdisj : Disjoint D B := by
    rw [Finset.disjoint_left]
    intro a haD haB
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp haB
    have haK : K + 1 + i ≤ K := Finset.le_sup (f := id) haD
    omega
  have hD'card : D'.card = 4 := by
    rw [hD', Finset.card_union_of_disjoint hdisj, hBcard]
    omega
  have hpos' : ∀ d ∈ D', 0 < d := by
    intro d hd
    rcases Finset.mem_union.mp hd with hdD | hdB
    · exact hpos d hdD
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hdB
      omega
  -- divide out `g = gcd D'`: division is injective on `D'` and gives `gcd = 1`
  set g := D'.gcd id with hg
  have hgpos : 0 < g := by
    obtain ⟨d, hd⟩ := hDne
    exact Nat.pos_of_dvd_of_pos
      (Finset.gcd_dvd (Finset.mem_union_left _ hd)) (hpos d hd)
  set D'' := D'.image (· / g) with hD''
  have hD''card : D''.card = 4 := by
    rw [hD'', Finset.card_image_of_injOn ?_]
    · exact hD'card
    · intro a ha b hb hdiv
      change a / g = b / g at hdiv
      have hga : g ∣ a := Finset.gcd_dvd (Finset.mem_coe.mp ha)
      have hgb : g ∣ b := Finset.gcd_dvd (Finset.mem_coe.mp hb)
      calc a = a / g * g := (Nat.div_mul_cancel hga).symm
        _ = b / g * g := by rw [hdiv]
        _ = b := Nat.div_mul_cancel hgb
  have hpos'' : ∀ e ∈ D'', 0 < e := by
    intro e he
    obtain ⟨d, hdD', rfl⟩ := Finset.mem_image.mp he
    have hgd : g ∣ d := Finset.gcd_dvd hdD'
    exact Nat.div_pos (Nat.le_of_dvd (hpos' d hdD') hgd) hgpos
  have hgcd'' : D''.gcd id = 1 := by
    have hgg : g * D''.gcd id ∣ g := by
      have h1 : g * D''.gcd id ∣ D'.gcd id := by
        apply Finset.dvd_gcd
        intro d hd
        change g * D''.gcd id ∣ d
        have hgd : g ∣ d := Finset.gcd_dvd hd
        have hd'' : d / g ∈ D'' := Finset.mem_image.mpr ⟨d, hd, rfl⟩
        have h2 : D''.gcd id ∣ d / g := Finset.gcd_dvd hd''
        obtain ⟨k, hk⟩ := h2
        refine ⟨k, ?_⟩
        have hdec : d = g * (d / g) :=
          (Nat.div_mul_cancel hgd).symm.trans (mul_comm _ _)
        rw [hdec, hk]; ring
      rwa [hg] at h1
    obtain ⟨k, hk⟩ := hgg
    have hk1 : D''.gcd id * k = 1 := by
      have e : g * (D''.gcd id * k) = g * 1 := by
        rw [mul_one]; calc g * (D''.gcd id * k) = g * D''.gcd id * k := by ring
          _ = g := hk.symm
      exact Nat.mul_left_cancel hgpos e
    exact Nat.eq_one_of_dvd_one ⟨k, hk1.symm⟩
  obtain ⟨lam, hlam, hbound⟩ := exists_multiplier4 D'' hpos'' hgcd'' hD''card
  set M := D''.sup (padicValNat 5) with hM
  have hlampos : 0 < lam :=
    Nat.pos_of_ne_zero fun h => hlam (by rw [h]; exact dvd_zero 5)
  have hgR : ((g : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hgpos.ne'
  have hNR : ((5 ^ (M + 1) : ℕ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.pow_pos (by norm_num)).ne'
  refine ⟨(lam : ℝ) / ((g * 5 ^ (M + 1) : ℕ) : ℝ), ?_, fun d hd => ?_⟩
  · exact div_pos (Nat.cast_pos.mpr hlampos)
      (Nat.cast_pos.mpr (mul_pos hgpos (Nat.pow_pos (by norm_num))))
  · have hdD' : d ∈ D' := Finset.mem_union_left _ hd
    have hgd : g ∣ d := Finset.gcd_dvd hdD'
    have hdq : d / g ∈ D'' := Finset.mem_image.mpr ⟨d, hdD', rfl⟩
    have hb := hbound (d / g) hdq
    have hdec : (d : ℝ) = (g : ℝ) * (d / g : ℕ) := by
      calc (d : ℝ) = ((d / g * g : ℕ) : ℝ) := by rw [Nat.div_mul_cancel hgd]
        _ = (g : ℝ) * (d / g : ℕ) := by push_cast; ring
    have ht : (lam : ℝ) / ((g * 5 ^ (M + 1) : ℕ) : ℝ) * (d : ℝ) =
        (lam : ℝ) * ((d / g : ℕ) : ℝ) / ((5 ^ (M + 1) : ℕ) : ℝ) := by
      rw [hdec, Nat.cast_mul, div_mul_eq_mul_div,
        mul_left_comm (lam : ℝ) (g : ℝ) ((d / g : ℕ) : ℝ),
        mul_div_mul_left _ _ hgR]
    rw [ht]
    exact circ_ge_fifth hb
