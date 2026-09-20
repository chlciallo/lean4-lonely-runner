import Research07.LRC7.Discrete

/-!
# Digit and carry machinery for LRC7 (BS7 §3.4/§3.7, spec §3.4/§3.7)

- `qdig7_eq_digit7`: `qdig7 m x` is the `m`-th base-7 digit of `x`.
- `digit7_add`, `digit7_add_mem`, `qdig7_add_mem`: the `m`-th digit of a
  sum is the sum of the digits plus a carry `∈ {0,1}` — the engine behind
  eq.(9)/(5): `q(λ'_{j+1} d) ∈ q(λ'_j d) + q(λ'_1 d) + {0,1}`.
- `digit7_add_mul_pow`: `digit7 j (a + b·7^j) = digit7 j a + b`.
- `qdig7_seven`: `q(7x)` at level `m` is the `(m-1)`-th digit of `x`.
- `qdig7_two_eq_smul`, `qdig7_two_eq_smul_add_one`: the second digit of
  `x` controls the top carry of `2x`.
- `digit7_multLow_one` family: the exact two-digit update of
  `x ↦ (1 + k·7^{m-1})·x` (the `q(λ·7d)` ε-trick engine): position `m-1`
  shifts by `k·x₀`, position `m` by `k·x₁ + ⌊(x_{m-1} + k·x₀)/7⌋`.
- `exists_multLow_one_set_seven`: `q(λ·7d)` hits any target via `Λ₁`.
-/

/-- `(x % (a·b))/a = (x/a) % b` — the mixed-radix strip lemma. -/
theorem mod_mul_div {x a b : ℕ} (_ha : 0 < a) (_hb : 0 < b) :
    x % (a * b) / a = x / a % b :=
  Nat.mod_mul_right_div_self x a b

/-- `qdig7 m x` is the `m`-th base-7 digit of `x`. -/
theorem qdig7_eq_digit7 (m x : ℕ) : qdig7 m x = digit7 m x := by
  unfold qdig7 digit7
  rw [pow_succ, mod_mul_div (Nat.pow_pos (by norm_num)) (by norm_num)]

/-- `q(7x)` at level `m` is the `(m-1)`-th digit of `x`. -/
theorem qdig7_seven (m x : ℕ) (hm : 0 < m) :
    qdig7 m (7 * x) = digit7 (m - 1) x := by
  rw [qdig7_eq_digit7]
  unfold digit7
  congr 1
  have h : 7 * x / 7 ^ m = x / 7 ^ (m - 1) := by
    rw [show 7 ^ m = 7 * 7 ^ (m - 1) from by
      rw [← pow_succ']; congr 1; omega]
    exact Nat.mul_div_mul_left x (7 ^ (m - 1)) (by norm_num)
  rw [h]

/-- `digit7` of `a + b·7^j`: shifts digit `j` by `b`. -/
theorem digit7_add_mul_pow (j a b : ℕ) :
    digit7 j (a + b * 7 ^ j) = digit7 j a + (b : ZMod 7) := by
  unfold digit7
  rw [Nat.add_mul_div_right _ _ (Nat.pow_pos (by norm_num))]
  simp only [ZMod.natCast_mod, Nat.cast_add]

/-- The `m`-th digit of a sum: digits add, with a carry
`c = (a % 7^m + b % 7^m) / 7^m ∈ {0,1}`. -/
theorem digit7_add (m a b : ℕ) :
    digit7 m (a + b) = digit7 m a + digit7 m b +
      (((a % 7 ^ m + b % 7 ^ m) / 7 ^ m : ℕ) : ZMod 7) := by
  unfold digit7
  have hpos : (0:ℕ) < 7 ^ m := Nat.pow_pos (by norm_num)
  have hdiv : (a + b) / 7 ^ m =
      a / 7 ^ m + b / 7 ^ m + (a % 7 ^ m + b % 7 ^ m) / 7 ^ m := by
    conv_lhs => rw [← Nat.div_add_mod a (7 ^ m), ← Nat.div_add_mod b (7 ^ m)]
    rw [show 7 ^ m * (a / 7 ^ m) + a % 7 ^ m + (7 ^ m * (b / 7 ^ m) + b % 7 ^ m)
        = (a % 7 ^ m + b % 7 ^ m) + 7 ^ m * (a / 7 ^ m + b / 7 ^ m) from by ring]
    rw [Nat.add_mul_div_left _ _ hpos]
    ring
  rw [hdiv]
  simp only [ZMod.natCast_mod, Nat.cast_add]

/-- The `m`-th digit of a sum lies in `digit + digit + {0,1}` (ZMod form). -/
theorem digit7_add_mem (m a b : ℕ) :
    digit7 m (a + b) ∈
      ({digit7 m a + digit7 m b, digit7 m a + digit7 m b + 1} :
        Finset (ZMod 7)) := by
  rw [digit7_add]
  have hc : (a % 7 ^ m + b % 7 ^ m) / 7 ^ m = 0 ∨
      (a % 7 ^ m + b % 7 ^ m) / 7 ^ m = 1 := by
    have hlt : (a % 7 ^ m + b % 7 ^ m) / 7 ^ m < 2 := by
      rw [Nat.div_lt_iff_lt_mul (Nat.pow_pos (by norm_num))]
      have h1 : a % 7 ^ m < 7 ^ m := Nat.mod_lt _ (Nat.pow_pos (by norm_num))
      have h2 : b % 7 ^ m < 7 ^ m := Nat.mod_lt _ (Nat.pow_pos (by norm_num))
      omega
    interval_cases ((a % 7 ^ m + b % 7 ^ m) / 7 ^ m) <;> simp
  rcases hc with h0 | h1
  · rw [h0, Nat.cast_zero, add_zero]; exact Finset.mem_insert_self _ _
  · rw [h1, Nat.cast_one]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)

/-- `qdig7` form of `digit7_add_mem`. -/
theorem qdig7_add_mem (m a b : ℕ) :
    qdig7 m (a + b) ∈
      ({qdig7 m a + qdig7 m b, qdig7 m a + qdig7 m b + 1} :
        Finset (ZMod 7)) := by
  rw [qdig7_eq_digit7, qdig7_eq_digit7, qdig7_eq_digit7]
  exact digit7_add_mem m a b

/-- `q(7x) = 0` (the `(m-1)`-digit of `x` vanishes) kills the top carry of
`2x`: `q(2x) = 2·q(x)`. -/
theorem qdig7_two_eq_smul {m x : ℕ} (hm : 0 < m)
    (h : qdig7 m (7 * x) = 0) :
    qdig7 m (2 * x) = 2 * qdig7 m x := by
  rw [qdig7_seven m x hm] at h
  have hpos : (0:ℕ) < 7 ^ (m - 1) := Nat.pow_pos (by norm_num)
  have hval : (x / 7 ^ (m - 1)) % 7 = 0 := by
    have h' := h
    unfold digit7 at h'
    have hdvd : 7 ∣ (x / 7 ^ (m - 1)) % 7 :=
      (ZMod.natCast_eq_zero_iff _ _).mp h'
    exact Nat.eq_zero_of_dvd_of_lt hdvd (Nat.mod_lt _ (by norm_num))
  have hxlt : x % 7 ^ m < 7 ^ (m - 1) := by
    have hstrip : x % 7 ^ m / 7 ^ (m - 1) = x / 7 ^ (m - 1) % 7 := by
      have hs := mod_mul_div (x := x) (a := 7 ^ (m - 1)) (b := 7) hpos
        (by norm_num)
      rwa [show 7 ^ (m - 1) * 7 = 7 ^ m from by
        rw [← pow_succ]; congr 1; omega] at hs
    have hdm := Nat.div_add_mod (x % 7 ^ m) (7 ^ (m - 1))
    rw [hstrip, hval] at hdm
    have := Nat.mod_lt (x % 7 ^ m) hpos
    omega
  rw [qdig7_eq_digit7, qdig7_eq_digit7,
    show (2 : ℕ) * x = x + x from two_mul x, digit7_add]
  have hc : (x % 7 ^ m + x % 7 ^ m) / 7 ^ m = 0 := by
    have h7 : 2 * 7 ^ (m - 1) ≤ 7 ^ m := by
      rw [show 7 ^ m = 7 ^ (m - 1) * 7 from by
        rw [← pow_succ]; congr 1; omega]
      omega
    exact Nat.div_eq_of_lt (by omega)
  rw [hc, Nat.cast_zero, add_zero, two_mul]

/-- `q(7x) = 6` (the `(m-1)`-digit is `6`) forces carry `1` in `2x`:
`q(2x) = 2·q(x) + 1`. -/
theorem qdig7_two_eq_smul_add_one {m x : ℕ} (hm : 0 < m)
    (h : qdig7 m (7 * x) = 6) :
    qdig7 m (2 * x) = 2 * qdig7 m x + 1 := by
  rw [qdig7_seven m x hm] at h
  have hpos : (0:ℕ) < 7 ^ (m - 1) := Nat.pow_pos (by norm_num)
  have hpos' : (0:ℕ) < 7 ^ m := Nat.pow_pos (by norm_num)
  have hval : (x / 7 ^ (m - 1)) % 7 = 6 := by
    have h' := h
    unfold digit7 at h'
    have hv := (ZMod.natCast_eq_natCast_iff' _ _ _).mp h'
    simpa [Nat.mod_mod] using hv
  have hxge : 6 * 7 ^ (m - 1) ≤ x % 7 ^ m := by
    have hstrip : x % 7 ^ m / 7 ^ (m - 1) = x / 7 ^ (m - 1) % 7 := by
      have hs := mod_mul_div (x := x) (a := 7 ^ (m - 1)) (b := 7) hpos
        (by norm_num)
      rwa [show 7 ^ (m - 1) * 7 = 7 ^ m from by
        rw [← pow_succ]; congr 1; omega] at hs
    have hdm := Nat.div_add_mod (x % 7 ^ m) (7 ^ (m - 1))
    rw [hstrip, hval] at hdm
    omega
  rw [qdig7_eq_digit7, qdig7_eq_digit7,
    show (2 : ℕ) * x = x + x from two_mul x, digit7_add]
  have hc : (x % 7 ^ m + x % 7 ^ m) / 7 ^ m = 1 := by
    have hge : 7 ^ m ≤ x % 7 ^ m + x % 7 ^ m := by
      have h7 : 7 ^ m = 7 * 7 ^ (m - 1) := by
        rw [← pow_succ']; congr 1; omega
      omega
    have hlt : x % 7 ^ m + x % 7 ^ m - 7 ^ m < 7 ^ m := by
      have := Nat.mod_lt x hpos'
      omega
    rw [show x % 7 ^ m + x % 7 ^ m =
        (x % 7 ^ m + x % 7 ^ m - 7 ^ m) + 1 * 7 ^ m from by omega,
      Nat.add_mul_div_right _ _ hpos', Nat.div_eq_of_lt hlt]
  rw [hc, Nat.cast_one, two_mul]


/-- For a unit `d`, `runit7 d` is just `d` cast to `ZMod 7`. -/
theorem runit7_of_padic_zero {d : ℕ} (hd : padicValNat 7 d = 0) :
    runit7 d = (d : ZMod 7) := by
  unfold runit7
  rw [hd, pow_zero, Nat.div_one]

/-- The `q`-digit of `λ·7d` for `λ = 1 + k·7^{m-1}`: equals
`digit7 (m-1) d + k·runit7 d` — freely settable via `k`. -/
theorem digit7_multLow_one_res {m d k : ℕ} (hm : 0 < m)
    (hd : padicValNat 7 d = 0) :
    qdig7 m ((1 + k * 7 ^ (m - 1)) * (7 * d)) =
      digit7 (m - 1) d + (k : ZMod 7) * runit7 d := by
  have hfac : (1 + k * 7 ^ (m - 1)) * (7 * d) =
      7 * (d + (k * d) * 7 ^ (m - 1)) := by ring
  rw [hfac, qdig7_seven _ _ hm, digit7_add_mul_pow, Nat.cast_mul,
    ← runit7_of_padic_zero hd]

/-- `q(λ·7d)` is settable to any `ZMod 7` value via `λ = 1 + k·7^{m-1}`
(the `Λ₁` family acting on the level-1 element `7d`).

NOTE (corrected variant): the originally drafted statement
`exists_multLow_one_set_seven` omitted `hd0` and was FALSE at `d = 0`
(`padicValNat 7 0 = 0` makes `hd` vacuous while every `(1+k·7^{m-1})·0 = 0`
has `qdig7 = 0`). Spec `lrc7-sec6-spec.md:320` states it with
`(hd0 : 0 < d)` and `2 ≤ m`; `0 < m` suffices. -/
theorem exists_multLow_one_set_seven' {m d : ℕ} (hm : 0 < m)
    (hd : padicValNat 7 d = 0) (hd0 : 0 < d) (c : ZMod 7) :
    ∃ k : ℕ, k < 7 ∧ qdig7 m ((1 + k * 7 ^ (m - 1)) * (7 * d)) = c := by
  haveI : NeZero 7 := ⟨by norm_num⟩
  have hu : runit7 d ≠ 0 := runit7_ne_zero hd0
  -- every nonzero `u : ZMod 7` has a multiplicative inverse (decidable
  -- enumeration; `u⁻¹` itself does not kernel-reduce so `decide` on
  -- `u⁻¹ * u = 1` fails — the `∃ v` form reduces fine)
  have hex : ∀ u : ZMod 7, u ≠ 0 → ∃ v : ZMod 7, v * u = 1 := by decide
  obtain ⟨v, hv⟩ := hex _ hu
  set k0 := (c - digit7 (m - 1) d) * v with hk0
  refine ⟨k0.val, ZMod.val_lt _, ?_⟩
  rw [digit7_multLow_one_res hm hd, ZMod.natCast_zmod_val]
  have hmul : k0 * runit7 d = c - digit7 (m - 1) d := by
    rw [hk0, mul_assoc, hv, mul_one]
  rw [hmul]
  ring

/-- The exact two-digit update of `x ↦ (1 + k·7^{m-1})·x`, `m ≥ 1`:
position `m-1` shifts by `k·x₀`; position `m` by `k·x₁` plus the combined
carry `⌊(x_{m-1} + k·x₀)/7⌋` (the digit-sum carry together with the
`(k·x₀)/7` term inside `k·x/7`).  Exact — via
`x' = lo + S·7^{m-1} + T·7^m` with `S = x_{m-1} + (k·x)%7`,
`T = x/7^m + k·x/7`. -/
theorem digit7_multLow_one {m k x : ℕ} (hm : 1 ≤ m) :
    digit7 (m - 1) ((1 + k * 7 ^ (m - 1)) * x) =
      digit7 (m - 1) x + (k : ZMod 7) * digit7 0 x ∧
    digit7 m ((1 + k * 7 ^ (m - 1)) * x) =
      digit7 m x + (k : ZMod 7) * digit7 1 x +
        ((((x / 7 ^ (m - 1)) % 7 + k * (x % 7)) / 7 : ℕ) : ZMod 7) := by
  have hm1 : 7 ^ m = 7 ^ (m - 1) * 7 := by
    rw [← pow_succ]; congr 1; omega
  have hpos : (0:ℕ) < 7 ^ (m - 1) := Nat.pow_pos (by norm_num)
  have hpos' : (0:ℕ) < 7 ^ m := Nat.pow_pos (by norm_num)
  set S := x / 7 ^ (m - 1) % 7 + (k * x) % 7 with hS
  set T := x / 7 ^ m + k * x / 7 with hT
  -- Exact 3-term decomposition
  have hdecomp : (1 + k * 7 ^ (m - 1)) * x =
      x % 7 ^ (m - 1) + S * 7 ^ (m - 1) + T * 7 ^ m := by
    have h3 : x / 7 ^ (m - 1) / 7 = x / 7 ^ m := by
      rw [Nat.div_div_eq_div_mul, ← hm1]
    have hx : x = x % 7 ^ (m - 1) + x / 7 ^ (m - 1) % 7 * 7 ^ (m - 1) +
        x / 7 ^ m * 7 ^ m := by
      conv_lhs => rw [← Nat.div_add_mod x (7 ^ (m - 1)),
        ← Nat.div_add_mod (x / 7 ^ (m - 1)) 7]
      rw [h3, hm1]
      ring
    have hkx : k * x = (k * x) % 7 + k * x / 7 * 7 := by
      have := Nat.mod_add_div (k * x) 7
      omega
    have key : (1 + k * 7 ^ (m - 1)) * x = x + (k * x) * 7 ^ (m - 1) := by ring
    rw [key, hS, hT]
    conv_lhs => rw [hkx]
    rw [show x % 7 ^ (m - 1) + (x / 7 ^ (m - 1) % 7 + (k * x) % 7) *
        7 ^ (m - 1) + (x / 7 ^ m + k * x / 7) * 7 ^ m =
        (x % 7 ^ (m - 1) + x / 7 ^ (m - 1) % 7 * 7 ^ (m - 1) +
          x / 7 ^ m * 7 ^ m) +
        ((k * x) % 7 + k * x / 7 * 7) * 7 ^ (m - 1) from by rw [hm1]; ring]
    rw [← hx]
  -- Strip the low block for both divisions
  have hdivlo : (1 + k * 7 ^ (m - 1)) * x / 7 ^ (m - 1) = S + T * 7 := by
    have hlo : x % 7 ^ (m - 1) < 7 ^ (m - 1) := Nat.mod_lt _ hpos
    rw [hdecomp,
      show x % 7 ^ (m - 1) + S * 7 ^ (m - 1) + T * 7 ^ m =
        x % 7 ^ (m - 1) + (S + T * 7) * 7 ^ (m - 1) from by rw [hm1]; ring,
      Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hlo, zero_add]
  have hdivhi : (1 + k * 7 ^ (m - 1)) * x / 7 ^ m = S / 7 + T := by
    have hSsplit : S * 7 ^ (m - 1) = S % 7 * 7 ^ (m - 1) + S / 7 * 7 ^ m := by
      rw [hm1]
      conv_lhs => rw [show S = S % 7 + 7 * (S / 7) from
        (Nat.mod_add_div S 7).symm]
      ring
    have hlo : x % 7 ^ (m - 1) + S % 7 * 7 ^ (m - 1) < 7 ^ m := by
      have h1 : x % 7 ^ (m - 1) < 7 ^ (m - 1) := Nat.mod_lt _ hpos
      have h2 : S % 7 < 7 := Nat.mod_lt _ (by norm_num)
      have h3 : S % 7 * 7 ^ (m - 1) ≤ 6 * 7 ^ (m - 1) :=
        Nat.mul_le_mul_right _ (by omega)
      rw [hm1]
      omega
    rw [hdecomp, hSsplit,
      show x % 7 ^ (m - 1) + (S % 7 * 7 ^ (m - 1) + S / 7 * 7 ^ m) +
          T * 7 ^ m =
        x % 7 ^ (m - 1) + S % 7 * 7 ^ (m - 1) + (S / 7 + T) * 7 ^ m
        from by ring,
      Nat.add_mul_div_right _ _ hpos', Nat.div_eq_of_lt hlo, zero_add]
  constructor
  · -- position `m-1`: quotient is `S + T·7`, so digit `= ↑(S % 7)`
    unfold digit7
    rw [hdivlo]
    have hmod : (S + T * 7) % 7 = S % 7 := by omega
    rw [hmod]
    simp only [ZMod.natCast_mod, hS, Nat.cast_add, Nat.cast_mul, pow_zero,
      Nat.div_one]
  · -- position `m`: quotient is `S/7 + T`
    unfold digit7
    rw [pow_one, hdivhi]
    conv_lhs => rw [ZMod.natCast_mod, Nat.cast_add, hT, Nat.cast_add,
      ← ZMod.natCast_mod (x / 7 ^ m) 7]
    -- LHS: `↑(S/7) + (↑((x/7^m)%7) + ↑(k·x/7))`;
    -- RHS: `↑(x/7^m%7) + ↑k·↑(x/7%7) + ↑((d + k·x₀)/7)`
    have hkdiv : ((k * x / 7 : ℕ) : ZMod 7) =
        (k : ZMod 7) * ((x / 7 % 7 : ℕ) : ZMod 7) +
          (((k * (x % 7)) / 7 : ℕ) : ZMod 7) := by
      -- `k·x/7 = k·x₀/7 + k·x₁ + 7·k·(x/49)`
      have hx : x = x % 7 + (x / 7 % 7) * 7 + x / 49 * 49 := by
        have h1 := Nat.div_add_mod x 7
        have h2 := Nat.div_add_mod (x / 7) 7
        have h3 : x / 7 / 7 = x / 49 := Nat.div_div_eq_div_mul x 7 7
        omega
      have hkx' : k * x = k * (x % 7) +
          (k * (x / 7 % 7) + k * (x / 49) * 7) * 7 := by
        conv_lhs => rw [hx]
        ring
      have hk7 : k * x / 7 =
          k * (x % 7) / 7 + k * (x / 7 % 7) + k * (x / 49) * 7 := by
        rw [hkx', Nat.add_mul_div_right _ _ (by norm_num : (0:ℕ) < 7)]
        ring
      rw [hk7, Nat.cast_add, Nat.cast_add]
      have h49 : ((k * (x / 49) * 7 : ℕ) : ZMod 7) = 0 := by
        rw [Nat.cast_mul, show ((7 : ℕ) : ZMod 7) = 0 from
          ZMod.natCast_self 7, mul_zero]
      rw [h49, add_zero, Nat.cast_mul]
      ring
    rw [hkdiv]
    -- combine the carries: `S/7 + (k·x₀)/7 = (d + k·x₀)/7` as naturals
    have hcarry : ((S / 7 : ℕ) : ZMod 7) +
        (((k * (x % 7)) / 7 : ℕ) : ZMod 7) =
        ((((x / 7 ^ (m - 1)) % 7 + k * (x % 7)) / 7 : ℕ) : ZMod 7) := by
      rw [← Nat.cast_add]
      congr 1
      have hS7 : S = x / 7 ^ (m - 1) % 7 + (k * (x % 7)) % 7 := by
        rw [hS]
        congr 1
        rw [Nat.mul_mod, Nat.mul_mod k (x % 7) 7, Nat.mod_mod]
      rw [hS7]
      have hq : k * (x % 7) =
          (k * (x % 7)) % 7 + (k * (x % 7)) / 7 * 7 := by
        have := Nat.mod_add_div (k * (x % 7)) 7
        omega
      have h : x / 7 ^ (m - 1) % 7 + k * (x % 7) =
          (x / 7 ^ (m - 1) % 7 + (k * (x % 7)) % 7) +
            (k * (x % 7)) / 7 * 7 := by
        conv_lhs => rw [hq]
        ring
      rw [h, Nat.add_mul_div_right _ _ (by norm_num : (0:ℕ) < 7)]
    linear_combination hcarry
