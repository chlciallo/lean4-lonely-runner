/-
Copyright (c) 2026 Research07 contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Research07 contributors
-/
import Research07.LRC7.Case5mL9

/-!
# Paper Lemma 9(i′) — the boundary 3-compression lemma (Barajas–Serra §6)

`lemma9_i` (`Case5mL9.lean`) covers three same-class level-0 elements whose
difference residues `x = e(b1,b3)`, `y = e(b2,b3)` sit at *distinct levels
below `m`*.  When exactly one level equals `m` — the paper's `λx = N/7`
edge — the all-pairs `{0,6}` conclusion is FALSE (see
`_reports/lrc7-sec6-lemma9i.md` for the `m = 2`, `(295,8,1)` countermodel:
`q(λx) + q(λe31) = 7` can never be `{6,6}`).  The repair, per the spec
ERRATUM (`_reports/lrc7-sec6-spec.md` §ERRATUM), is to relax the pair
condition to `{0,1,6}` — which is negation-closed and still suffices for
the §6.1 `×3` dichotomy (0 failures / 41160 configs).

This file proves that variant: `lemma9_i'` drops the `hνm` hypothesis of
`lemma9_i` entirely and concludes

* `¬ 7 ∣ lam`,
* every ordered pair digit `q(e(λbi,λbj)) ∈ {0,1,6}`,
* `ℓ(λB) ≤ 2`.

Proof shape (`by_cases` on `hνm`):

1. Both levels `< m` — `lemma9_i` applies verbatim; `{0,6} ⊆ {0,1,6}`.
2. Otherwise the levels (`≤ m` by `enu7_le_of_ne`, distinct by `hν`) are
   split: exactly one equals `m`.  The core `lemma9_ip_aux` is proved once
   for `ν(x) = m`, `ν(y) < m`; the mirrored case applies it to the swapped
   triple `(b2,b1,b3)` (the set is the same by `Finset.insert_comm`).

Core construction (`x` level `m`, `y` level `j < m`): pick `c ∈ {1,…,6}`
with `(c·x) % N = 7^m` (`exists_top_scalar_set`, `t = 1`) and
`lam₂ = 1 + k·7^{m−j} ∈ Λ_j` with `q(lam₂·(c·y)) = 0`
(`exists_multLow_set_qdig`).  With `lam := lam₂·c`:

* `(lam·x) % N = 7^m` (`residN_multLow7`, level `m > j`), so `q(lam·x) = 1`
  and its low part is `0`;
* `f := (lam·y) % N` satisfies `0 < f < 7^m` (digit `0`, and `f ≠ 0` since
  `ν(lam·y) = j < m`), so `q(lam·y) = 0`.

The nine ordered pairs then read (all relations `same`, `e(u,v) = u−v`):
`e13 ↦ 1`, `e31 ↦ 6`, `e23 ↦ 0`, `e32 ↦ 6`, `e12 ↦ 1−0−borrow = 0`,
`e21 ↦ 6`, diagonals `0` — all inside `{0,1,6}`.

For `apLen ≤ 2` the digits are computed directly (the `{0,6}`-based
`remark8_i_int` bridge does not apply): `q(λb3) =: a`,
`q(λb1) = a+1` (since `λb1 ≡ λb3 + 7^m`), and
`q(λb2) = a + carry` with `carry = ((λb3)%7^m + f)/7^m ≤ 1` — so the image
is covered by `cycIv a 2`.

Contents:

* `resid_lt_of_qdig7_zero` — `q(z) = 0` forces `z % N < 7^m`.
* `mod_pos_of_val_lt` — `ν(z) < m` forces `z % N ≠ 0`.
* `qdig7_add_pow` — `q(w + 7^m) = q(w) + 1`.
* `add_div_carry7` — `(a+b)/c = a/c + b/c + carry` (clone).
* `lemma9_ip_aux` — the boundary core lemma.
* `lemma9_i'` — the main theorem.
-/

private instance : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩

/-! ### Private clones of `Differences.lean`/`Discrete.lean` helpers -/

/-- `(a·7^m + b) / 7^m = a` when `b < 7^m` (local copy). -/
private theorem mul_pow_add_div {a b m : ℕ} (hb : b < 7 ^ m) :
    (a * 7 ^ m + b) / 7 ^ m = a := by
  have hP : 0 < 7 ^ m := Nat.pow_pos (by norm_num)
  rw [add_comm (a * 7 ^ m) b, mul_comm a (7 ^ m),
    Nat.add_mul_div_left _ _ hP, Nat.div_eq_of_lt hb, zero_add]

/-- Decompose `x % 7^{m+1}` as `q·7^m + f` with `q < 7`, `f < 7^m`
(local copy). -/
private theorem residue_decomp {m x : ℕ} :
    ∃ q f : ℕ, x % 7 ^ (m + 1) = q * 7 ^ m + f ∧ q < 7 ∧ f < 7 ^ m := by
  refine ⟨(x % 7 ^ (m + 1)) / 7 ^ m, (x % 7 ^ (m + 1)) % 7 ^ m, ?_, ?_,
    Nat.mod_lt _ (Nat.pow_pos (by norm_num))⟩
  · rw [mul_comm, Nat.div_add_mod]
  · rw [Nat.div_lt_iff_lt_mul (Nat.pow_pos (by norm_num)), ← pow_succ']
    exact Nat.mod_lt _ (Nat.pow_pos (by norm_num))

/-- Cast a truncated-subtraction digit expression into `ZMod 7`
(local copy). -/
private theorem natCast_sub_add {a b c : ℕ} (h : c ≤ a + b) :
    ((a + b - c : ℕ) : ZMod 7) = (a : ZMod 7) + b - c := by
  have hcast : ((a + b - c : ℕ) : ZMod 7)
      = (((a + b - c : ℕ) : ℤ) : ZMod 7) := by simp
  rw [hcast, Int.ofNat_sub h]
  push_cast
  ring

/-- `ZMod`-cast of `eMod7`: the wrapped residue casts to the
branch expression (local copy). -/
private theorem eMod7_zmod_cast (m x y : ℕ) :
    ((eMod7 m x y : ℕ) : ZMod (7 ^ (m + 1))) =
      if runit7 y = 2 * runit7 x then 2 * (x : ZMod _) - (y : ZMod _)
      else if runit7 x = 2 * runit7 y then 2 * (y : ZMod _) - (x : ZMod _)
      else (x : ZMod _) - (y : ZMod _) := by
  have hcast : ∀ a : ℕ,
      ((a % 7 ^ (m + 1) : ℕ) : ZMod (7 ^ (m + 1))) = (a : ZMod _) := by
    intro a
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr (Nat.mod_mod a _)
  have hN : ((7 ^ (m + 1) : ℕ) : ZMod (7 ^ (m + 1))) = 0 := ZMod.natCast_self _
  unfold eMod7
  split_ifs with h1 h2
  · rw [hcast, Nat.cast_sub (by
      have : y % 7 ^ (m + 1) < 7 ^ (m + 1) := Nat.mod_lt _ (Nat.pow_pos (by norm_num))
      omega : y % 7 ^ (m + 1) ≤ 2 * (x % 7 ^ (m + 1)) + 7 ^ (m + 1))]
    rw [Nat.cast_add, Nat.cast_mul, hcast x, hcast y, hN, Nat.cast_ofNat]
    ring
  · rw [hcast, Nat.cast_sub (by
      have : x % 7 ^ (m + 1) < 7 ^ (m + 1) := Nat.mod_lt _ (Nat.pow_pos (by norm_num))
      omega : x % 7 ^ (m + 1) ≤ 2 * (y % 7 ^ (m + 1)) + 7 ^ (m + 1))]
    rw [Nat.cast_add, Nat.cast_mul, hcast y, hcast x, hN, Nat.cast_ofNat]
    ring
  · rw [hcast, Nat.cast_sub (by
      have : y % 7 ^ (m + 1) < 7 ^ (m + 1) := Nat.mod_lt _ (Nat.pow_pos (by norm_num))
      omega : y % 7 ^ (m + 1) ≤ x % 7 ^ (m + 1) + 7 ^ (m + 1))]
    rw [Nat.cast_add, hcast x, hcast y, hN]
    ring

/-- Equal `runit7` forces the `same` branch (for nonzero second element). -/
private theorem rel_same {u v : ℕ} (h : runit7 u = runit7 v) (hv : v ≠ 0) :
    residueRelOf u v = residueRel.same := by
  have hv0 : runit7 v ≠ 0 := runit7_ne_zero (Nat.pos_of_ne_zero hv)
  rw [residueRelOf_eq_same]
  refine ⟨?_, ?_⟩ <;> intro hcon <;> rw [h] at hcon <;>
    · have hz : runit7 v = 0 := by
        have e : runit7 v - 2 * runit7 v = 0 := sub_eq_zero.mpr hcon
        have e2 : runit7 v - 2 * runit7 v = - runit7 v := by ring
        rw [e2] at e
        exact neg_eq_zero.mp e
      exact hv0 hz

/-- `eMod7` casts to a plain difference in the `same` branch. -/
private theorem eMod7_zmod_cast_same {m u v : ℕ}
    (h : residueRelOf u v = residueRel.same) :
    ((eMod7 m u v : ℕ) : ZMod (7 ^ (m + 1))) = (u : ZMod _) - (v : ZMod _) := by
  obtain ⟨h1, h2⟩ := (residueRelOf_eq_same).mp h
  rw [eMod7_zmod_cast, ite_eq_right h1, ite_eq_right h2]

/-- `qdig7 m 0 = 0`. -/
private theorem qdig7_zero (m : ℕ) : qdig7 m 0 = 0 := by
  unfold qdig7
  simp

/-- **Exact borrow formula** for the wrapped residue difference
`(a % N + N − b % N)` (local copy): the top digit is `q_a − q_b` minus the
borrow `1` iff `f_a < f_b`. -/
private theorem qdig7_sub_resid {m a b : ℕ} :
    qdig7 m (a % 7 ^ (m + 1) + 7 ^ (m + 1) - b % 7 ^ (m + 1))
      = qdig7 m a - qdig7 m b
        - if a % 7 ^ m < b % 7 ^ m then (1 : ZMod 7) else 0 := by
  obtain ⟨q1, f1, hX, hq1, hf1⟩ := residue_decomp (m := m) (x := a)
  obtain ⟨q2, f2, hY, hq2, hf2⟩ := residue_decomp (m := m) (x := b)
  have hP : 0 < 7 ^ m := Nat.pow_pos (by norm_num)
  have hNe : (7 : ℕ) ^ (m + 1) = 7 * 7 ^ m := pow_succ' 7 m
  have hqA : qdig7 m a = (q1 : ZMod 7) := by
    unfold qdig7
    rw [hX, mul_pow_add_div hf1]
  have hqB : qdig7 m b = (q2 : ZMod 7) := by
    unfold qdig7
    rw [hY, mul_pow_add_div hf2]
  have hf1e : a % 7 ^ m = f1 := by
    have hmod : a % 7 ^ (m + 1) % 7 ^ m = a % 7 ^ m :=
      Nat.mod_mod_of_dvd a (Nat.pow_dvd_pow 7 (Nat.le_succ m))
    rw [← hmod, hX, add_comm (q1 * 7 ^ m) f1,
      Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hf1]
  have hf2e : b % 7 ^ m = f2 := by
    have hmod : b % 7 ^ (m + 1) % 7 ^ m = b % 7 ^ m :=
      Nat.mod_mod_of_dvd b (Nat.pow_dvd_pow 7 (Nat.le_succ m))
    rw [← hmod, hY, add_comm (q2 * 7 ^ m) f2,
      Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hf2]
  rw [qdig7_eq_cast_div]
  by_cases hb : f1 < f2
  · -- borrow: `a' + N − b' = (q1 + 6 − q2)·7^m + (f1 + 7^m − f2)`
    have hexp : (q1 + 6 - q2) * 7 ^ m = q1 * 7 ^ m + 6 * 7 ^ m - q2 * 7 ^ m := by
      rw [Nat.sub_mul, Nat.add_mul]
    have hB : q2 * 7 ^ m ≤ 6 * 7 ^ m :=
      Nat.mul_le_mul (by omega : q2 ≤ 6) (le_refl _)
    have hcalc : a % 7 ^ (m + 1) + 7 ^ (m + 1) - b % 7 ^ (m + 1)
        = (q1 + 6 - q2) * 7 ^ m + (f1 + 7 ^ m - f2) := by
      rw [hX, hY, hNe, hexp]
      omega
    rw [hcalc, mul_pow_add_div (by omega : f1 + 7 ^ m - f2 < 7 ^ m)]
    have hq : ((q1 + 6 - q2 : ℕ) : ZMod 7) = (q1 : ZMod 7) - q2 - 1 := by
      rw [natCast_sub_add (by omega : q2 ≤ q1 + 6)]
      have h6 : ((6 : ℕ) : ZMod 7) = -1 := by decide
      rw [h6]
      ring
    rw [hq, hqA, hqB]
    rw [ite_eq_left (by rwa [hf1e, hf2e] : a % 7 ^ m < b % 7 ^ m)]
  · -- no borrow: `a' + N − b' = (q1 + 7 − q2)·7^m + (f1 − f2)`
    have hge : f2 ≤ f1 := Nat.le_of_not_gt hb
    have hexp : (q1 + 7 - q2) * 7 ^ m = q1 * 7 ^ m + 7 * 7 ^ m - q2 * 7 ^ m := by
      rw [Nat.sub_mul, Nat.add_mul]
    have hB : q2 * 7 ^ m ≤ 7 * 7 ^ m :=
      Nat.mul_le_mul (by omega : q2 ≤ 7) (le_refl _)
    have hcalc : a % 7 ^ (m + 1) + 7 ^ (m + 1) - b % 7 ^ (m + 1)
        = (q1 + 7 - q2) * 7 ^ m + (f1 - f2) := by
      rw [hX, hY, hNe, hexp]
      omega
    rw [hcalc, mul_pow_add_div (by omega : f1 - f2 < 7 ^ m)]
    have hq : ((q1 + 7 - q2 : ℕ) : ZMod 7) = (q1 : ZMod 7) - q2 := by
      rw [natCast_sub_add (by omega : q2 ≤ q1 + 7)]
      have h7 : ((7 : ℕ) : ZMod 7) = 0 := by decide
      rw [h7]
      ring
    rw [hq, hqA, hqB]
    rw [ite_eq_right (by rwa [hf1e, hf2e] : ¬ a % 7 ^ m < b % 7 ^ m)]
    ring

/-- The `q`-digit of a scalar multiple of a difference residue whose
`ZMod N` value is the combination `A − B` (local copy). -/
private theorem qdig_smul_eMod_eq {m lam e A B : ℕ}
    (hcast : ((lam * e : ℕ) : ZMod (7 ^ (m + 1))) = (A : ZMod _) - (B : ZMod _)) :
    qdig7 m (lam * e)
      = qdig7 m A - qdig7 m B
        - if A % 7 ^ m < B % 7 ^ m then (1 : ZMod 7) else 0 := by
  have hcast' : ((lam * e : ℕ) : ZMod (7 ^ (m + 1)))
      = ((A % 7 ^ (m + 1) + 7 ^ (m + 1) - B % 7 ^ (m + 1) : ℕ) : ZMod _) := by
    rw [hcast]
    have hlt : B % 7 ^ (m + 1) ≤ A % 7 ^ (m + 1) + 7 ^ (m + 1) := by
      have := Nat.mod_lt B (Nat.pow_pos (by norm_num) : 0 < 7 ^ (m + 1))
      omega
    rw [Nat.cast_sub hlt, Nat.cast_add, ZMod.natCast_mod, ZMod.natCast_mod,
      ZMod.natCast_self]
    ring
  have hwrap : (lam * e) % 7 ^ (m + 1)
      = (A % 7 ^ (m + 1) + 7 ^ (m + 1) - B % 7 ^ (m + 1)) % 7 ^ (m + 1) :=
    (ZMod.natCast_eq_natCast_iff' _ _ _).mp hcast'
  rw [qdig7_congr hwrap]
  exact qdig7_sub_resid

/-! ### Boundary-specific helpers -/

/-- Division of a sum: `(a + b)/c = a/c + b/c + carry` with
`carry = (a%c + b%c)/c` (local copy of `Discrete.add_div_carry7`). -/
private theorem add_div_carry7 (a b c : ℕ) (hc : 0 < c) :
    (a + b) / c = a / c + b / c + (a % c + b % c) / c := by
  have h1 : a + b = a % c + b % c + c * (a / c + b / c) := by
    have hda := Nat.div_add_mod a c
    have hdb := Nat.div_add_mod b c
    have hmul : c * (a / c) + c * (b / c) = c * (a / c + b / c) := by ring
    omega
  rw [h1, Nat.add_mul_div_left _ _ hc]
  ring

/-- `q(w + 7^m) = q(w) + 1`: adding `7^m` bumps the leading digit exactly
(`(w + 7^m)/7^m = w/7^m + 1`). -/
private theorem qdig7_add_pow (m w : ℕ) :
    qdig7 m (w + 7 ^ m) = qdig7 m w + 1 := by
  rw [qdig7_eq_cast_div, qdig7_eq_cast_div]
  have hdiv : (w + 7 ^ m) / 7 ^ m = w / 7 ^ m + 1 := by
    conv_lhs => rw [show w + 7 ^ m = w + 7 ^ m * 1 by rw [mul_one]]
    exact Nat.add_mul_div_left _ _ (Nat.pow_pos (by norm_num))
  rw [hdiv]
  push_cast
  ring

/-- `q(z) = 0` means the residue `z % 7^{m+1}` is `< 7^m`. -/
private theorem resid_lt_of_qdig7_zero {m z : ℕ} (h : qdig7 m z = 0) :
    z % 7 ^ (m + 1) < 7 ^ m := by
  have hlt7 : z % 7 ^ (m + 1) / 7 ^ m < 7 := by
    rw [Nat.div_lt_iff_lt_mul (Nat.pow_pos (by norm_num)), ← pow_succ']
    exact Nat.mod_lt _ (Nat.pow_pos (by norm_num))
  have h0 : z % 7 ^ (m + 1) / 7 ^ m = 0 := by
    have hdvd : 7 ∣ z % 7 ^ (m + 1) / 7 ^ m := by
      unfold qdig7 at h
      exact (ZMod.natCast_eq_zero_iff _ _).mp h
    exact Nat.eq_zero_of_dvd_of_lt hdvd hlt7
  have h2 := Nat.div_add_mod (z % 7 ^ (m + 1)) (7 ^ m)
  rw [h0] at h2
  have h3 := Nat.mod_lt (z % 7 ^ (m + 1)) (Nat.pow_pos (by norm_num) : 0 < 7 ^ m)
  omega

/-- `ν(z) < m` forces `z % 7^{m+1} > 0` (else `7^{m+1} ∣ z` would give
`ν(z) ≥ m+1`). -/
private theorem mod_pos_of_val_lt {m z : ℕ} (hz : padicValNat 7 z < m)
    (hz0 : z ≠ 0) : 0 < z % 7 ^ (m + 1) := by
  have hmod : z % 7 ^ (m + 1) ≠ 0 := by
    rw [Ne, ← Nat.dvd_iff_mod_eq_zero]
    intro hd
    have hle := (Nat.pow_dvd_iff_le_padicValNat (by norm_num) hz0).mp hd
    omega
  exact Nat.pos_of_ne_zero hmod

/-! ### The boundary core lemma -/

/-- **Boundary core**: with `x = e(b1,b3)` at level `m` and
`y = e(b2,b3)` at level `< m`, the multiplier `lam = lam₂·c`
(`c·x ≡ 7^m`, `lam₂ ∈ Λ_j` zeroing `q(lam₂·(c·y))`) puts every pair digit
in `{0,1,6}` and `ℓ(λB) ≤ 2`. -/
private theorem lemma9_ip_aux {m : ℕ} {b1 b2 b3 : ℕ}
    (hpos : 0 < b1 ∧ 0 < b2 ∧ 0 < b3)
    (hsame : runit7 b1 = runit7 b2 ∧ runit7 b2 = runit7 b3)
    (hxν : padicValNat 7 (eMod7 m b1 b3) = m)
    (hyν : padicValNat 7 (eMod7 m b2 b3) < m)
    (he : eMod7 m b1 b3 ≠ 0 ∧ eMod7 m b2 b3 ≠ 0) :
    ∃ lam : ℕ, ¬ 7 ∣ lam ∧
      (∀ u ∈ ({b1, b2, b3} : Finset ℕ), ∀ v ∈ ({b1, b2, b3} : Finset ℕ),
        qdig7 m (eMod7 m (lam * u) (lam * v)) ∈ ({0, 1, 6} : Finset (ZMod 7))) ∧
      apLen (({b1, b2, b3} : Finset ℕ).image (fun d => qdig7 m (lam * d)))
        ≤ 2 := by
  classical
  set x := eMod7 m b1 b3 with hx
  set y := eMod7 m b2 b3 with hy
  have hx0 : x ≠ 0 := he.1
  have hy0 : y ≠ 0 := he.2
  have hyν' : padicValNat 7 y < m := hyν
  -- Step 1: `c` normalizes `x`'s residue to `7^m`.
  obtain ⟨c, hc0, hc7, hcx_res, hcx_q⟩ :=
    exists_top_scalar_set hxν hx0 (t := 1) ((by decide) : (1 : ZMod 7) ≠ 0)
  have hc_ne7 : ¬ 7 ∣ c := fun hd =>
    (ne_of_gt hc0) (Nat.eq_zero_of_dvd_of_lt hd hc7)
  have h1val : (1 : ZMod 7).val = 1 := by decide
  have hcx_res' : (c * x) % 7 ^ (m + 1) = 7 ^ m := by
    rw [hcx_res, h1val, one_mul]
  have hcxν : padicValNat 7 (c * x) = m := by
    rw [padicValNat_mul_seven hc_ne7 hx0, hxν]
  have hcyν : padicValNat 7 (c * y) = padicValNat 7 y := by
    rw [padicValNat_mul_seven hc_ne7 hy0]
  have hcy0 : c * y ≠ 0 := mul_ne_zero (ne_of_gt hc0) hy0
  -- Step 2: `lam₂ ∈ Λ_j` zeroes the digit of `c·y`.
  obtain ⟨k, hk7, hlam₂q⟩ := exists_multLow_set_qdig hyν' hcyν hcy0 0
  set lam₂ := 1 + k * 7 ^ (m - padicValNat 7 y) with hlam₂def
  set lam := lam₂ * c with hlamdef
  -- keep `lam` an opaque variable: otherwise `↑lam` unfolds to `↑(lam₂*c)`
  -- and gets rewritten by stray `Nat.cast_mul` applications.
  clear_value lam
  have hlam₂mem : lam₂ ∈ multLow7 m (padicValNat 7 y) := by
    rw [hlam₂def]
    exact mem_multLow7 hk7
  have hlam₂7 : ¬ 7 ∣ lam₂ := not_dvd_of_mem_multLow7 hyν' hlam₂mem
  have hlam7 : ¬ 7 ∣ lam := by
    intro hd
    rw [hlamdef] at hd
    rcases (Nat.Prime.dvd_mul Nat.prime_seven).mp hd with h | h
    · exact hlam₂7 h
    · exact hc_ne7 h
  have hl0 : lam ≠ 0 := fun h => hlam7 (h ▸ dvd_zero 7)
  have hrun : runit7 lam₂ = 1 := by
    rw [hlam₂def]
    exact runit7_multLow hyν'
  have hlamr : runit7 lam ≠ 0 := by
    rw [hlamdef, runit7_mul, hrun, one_mul]
    exact runit7_ne_zero hc0
  -- Residues and digits of `lam·x`, `lam·y`.
  have hlamx_eq : lam * x = lam₂ * (c * x) := by rw [hlamdef]; ring
  have hlamy_eq : lam * y = lam₂ * (c * y) := by rw [hlamdef]; ring
  have hlamx_res : (lam * x) % 7 ^ (m + 1) = 7 ^ m := by
    have hres := residN_multLow7 (j := padicValNat 7 y) (k := k) (x := c * x)
      hyν' (by rw [hcxν]; exact hyν')
    rw [hlamx_eq, hlam₂def, hres, hcx_res']
  have hlamy_q : qdig7 m (lam * y) = 0 := by
    rw [hlamy_eq, hlam₂def]
    exact hlam₂q
  have hlamx_q : qdig7 m (lam * x) = 1 := by
    have h : (lam * x) % 7 ^ (m + 1) = (c * x) % 7 ^ (m + 1) := by
      rw [hlamx_res, hcx_res']
    rw [qdig7_congr h, hcx_q]
  set f := (lam * y) % 7 ^ (m + 1) with hfdef
  have hf_lt : f < 7 ^ m := by
    rw [hfdef]
    exact resid_lt_of_qdig7_zero hlamy_q
  have hlamy_val : padicValNat 7 (lam * y) = padicValNat 7 y := by
    rw [hlamy_eq, padicValNat_mul_seven hlam₂7 hcy0, hcyν]
  have hf_pos : 0 < f := by
    rw [hfdef]
    apply mod_pos_of_val_lt
    · rw [hlamy_val]
      exact hyν'
    · exact mul_ne_zero hl0 hy0
  have hlamx_low : (lam * x) % 7 ^ m = 0 := by
    have h := Nat.mod_mod_of_dvd (lam * x) (Nat.pow_dvd_pow 7 (Nat.le_succ m))
    rw [hlamx_res] at h
    rw [← h, Nat.mod_self]
  have hlamy_low : (lam * y) % 7 ^ m = f := by
    have h := Nat.mod_mod_of_dvd (lam * y) (Nat.pow_dvd_pow 7 (Nat.le_succ m))
    rw [← hfdef] at h
    rw [← h, Nat.mod_eq_of_lt hf_lt]
  -- Step 3: residue relations of the (unscaled) pairs
  have hrel12 : residueRelOf b1 b2 = residueRel.same :=
    rel_same hsame.1 (ne_of_gt hpos.2.1)
  have hrel13 : residueRelOf b1 b3 = residueRel.same :=
    rel_same (hsame.1.trans hsame.2) (ne_of_gt hpos.2.2)
  have hrel23 : residueRelOf b2 b3 = residueRel.same :=
    rel_same hsame.2 (ne_of_gt hpos.2.2)
  have hrel21 : residueRelOf b2 b1 = residueRel.same :=
    rel_same hsame.1.symm (ne_of_gt hpos.1)
  have hrel31 : residueRelOf b3 b1 = residueRel.same :=
    rel_same (hsame.1.trans hsame.2).symm (ne_of_gt hpos.1)
  have hrel32 : residueRelOf b3 b2 = residueRel.same :=
    rel_same hsame.2.symm (ne_of_gt hpos.2.1)
  have hrel11 : residueRelOf b1 b1 = residueRel.same :=
    rel_same rfl (ne_of_gt hpos.1)
  have hrel22 : residueRelOf b2 b2 = residueRel.same :=
    rel_same rfl (ne_of_gt hpos.2.1)
  have hrel33 : residueRelOf b3 b3 = residueRel.same :=
    rel_same rfl (ne_of_gt hpos.2.2)
  have hxcast : ((x : ℕ) : ZMod (7 ^ (m + 1)))
      = (b1 : ZMod _) - (b3 : ZMod _) := by
    rw [hx]
    exact eMod7_zmod_cast_same hrel13
  have hycast : ((y : ℕ) : ZMod (7 ^ (m + 1)))
      = (b2 : ZMod _) - (b3 : ZMod _) := by
    rw [hy]
    exact eMod7_zmod_cast_same hrel23
  -- The evaluation engine: `q(e(λu,λv)) = q(A) − q(B) − borrow` whenever
  -- `λ·e(u,v) ≡ A − B (mod N)`.
  have eval : ∀ (u v A B : ℕ),
      (((lam * eMod7 m u v : ℕ) : ZMod (7 ^ (m + 1))) =
        (A : ZMod _) - (B : ZMod _)) →
      qdig7 m (eMod7 m (lam * u) (lam * v))
        = qdig7 m A - qdig7 m B
          - if A % 7 ^ m < B % 7 ^ m then (1 : ZMod 7) else 0 := by
    intro u v A B hcast
    rw [eMod7_smul hlamr, qdig7_congr (Nat.mod_mod _ _)]
    exact qdig_smul_eMod_eq hcast
  -- Step 4: the nine ordered pairs
  have key : ∀ u ∈ ({b1, b2, b3} : Finset ℕ),
      ∀ v ∈ ({b1, b2, b3} : Finset ℕ),
      qdig7 m (eMod7 m (lam * u) (lam * v)) ∈ ({0, 1, 6} : Finset (ZMod 7)) := by
    intro u hu v hv
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hu
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hu with h | h | h <;> rcases hv with h' | h' | h' <;> rw [h, h']
    · -- (b1,b1): `λe ≡ 0 − 0`
      have hcast : ((lam * eMod7 m b1 b1 : ℕ) : ZMod (7 ^ (m + 1)))
          = ((0 : ℕ) : ZMod _) - ((0 : ℕ) : ZMod _) := by
        rw [Nat.cast_mul, eMod7_zmod_cast_same hrel11]
        ring
      rw [eval _ _ _ _ hcast, qdig7_zero]
      rw [ite_eq_right (by simp)]
      decide
    · -- (b1,b2): `λe ≡ λx − λy`, `q = 1 − 0 − borrow(0<f) = 0`
      have hcast : ((lam * eMod7 m b1 b2 : ℕ) : ZMod (7 ^ (m + 1)))
          = ((lam * x : ℕ) : ZMod _) - ((lam * y : ℕ) : ZMod _) := by
        rw [Nat.cast_mul, eMod7_zmod_cast_same hrel12,
          Nat.cast_mul, Nat.cast_mul, hxcast, hycast]
        ring
      rw [eval _ _ _ _ hcast, hlamx_q, hlamy_q]
      rw [ite_eq_left (by rw [hlamx_low, hlamy_low]; exact hf_pos)]
      decide
    · -- (b1,b3): `λe ≡ λx − 0`, `q = 1`
      have hcast : ((lam * eMod7 m b1 b3 : ℕ) : ZMod (7 ^ (m + 1)))
          = ((lam * x : ℕ) : ZMod _) - ((0 : ℕ) : ZMod _) := by
        rw [Nat.cast_mul, eMod7_zmod_cast_same hrel13]
        ring
      rw [eval _ _ _ _ hcast, hlamx_q, qdig7_zero]
      rw [ite_eq_right (by rw [Nat.zero_mod]; exact Nat.not_lt_zero _)]
      decide
    · -- (b2,b1): `λe ≡ λy − λx`, `q = 0 − 1 − borrow(f<0 F) = 6`
      have hcast : ((lam * eMod7 m b2 b1 : ℕ) : ZMod (7 ^ (m + 1)))
          = ((lam * y : ℕ) : ZMod _) - ((lam * x : ℕ) : ZMod _) := by
        rw [Nat.cast_mul, eMod7_zmod_cast_same hrel21,
          Nat.cast_mul, Nat.cast_mul, hxcast, hycast]
        ring
      rw [eval _ _ _ _ hcast, hlamy_q, hlamx_q]
      rw [ite_eq_right (by rw [hlamy_low, hlamx_low]; exact Nat.not_lt_zero _)]
      decide
    · -- (b2,b2): `λe ≡ 0 − 0`
      have hcast : ((lam * eMod7 m b2 b2 : ℕ) : ZMod (7 ^ (m + 1)))
          = ((0 : ℕ) : ZMod _) - ((0 : ℕ) : ZMod _) := by
        rw [Nat.cast_mul, eMod7_zmod_cast_same hrel22]
        ring
      rw [eval _ _ _ _ hcast, qdig7_zero]
      rw [ite_eq_right (by simp)]
      decide
    · -- (b2,b3): `λe ≡ λy − 0`, `q = 0`
      have hcast : ((lam * eMod7 m b2 b3 : ℕ) : ZMod (7 ^ (m + 1)))
          = ((lam * y : ℕ) : ZMod _) - ((0 : ℕ) : ZMod _) := by
        rw [Nat.cast_mul, eMod7_zmod_cast_same hrel23]
        ring
      rw [eval _ _ _ _ hcast, hlamy_q, qdig7_zero]
      rw [ite_eq_right (by rw [Nat.zero_mod]; exact Nat.not_lt_zero _)]
      decide
    · -- (b3,b1): `λe ≡ 0 − λx`, `q = 0 − 1 − borrow(0<0 F) = 6`
      have hcast : ((lam * eMod7 m b3 b1 : ℕ) : ZMod (7 ^ (m + 1)))
          = ((0 : ℕ) : ZMod _) - ((lam * x : ℕ) : ZMod _) := by
        rw [Nat.cast_mul, eMod7_zmod_cast_same hrel31,
          Nat.cast_mul, hxcast]
        ring
      rw [eval _ _ _ _ hcast, qdig7_zero, hlamx_q]
      rw [ite_eq_right (by rw [Nat.zero_mod, hlamx_low]; exact Nat.not_lt_zero _)]
      decide
    · -- (b3,b2): `λe ≡ 0 − λy`, `q = 0 − 0 − borrow(0<f T) = 6`
      have hcast : ((lam * eMod7 m b3 b2 : ℕ) : ZMod (7 ^ (m + 1)))
          = ((0 : ℕ) : ZMod _) - ((lam * y : ℕ) : ZMod _) := by
        rw [Nat.cast_mul, eMod7_zmod_cast_same hrel32,
          Nat.cast_mul, hycast]
        ring
      rw [eval _ _ _ _ hcast, qdig7_zero, hlamy_q]
      rw [ite_eq_left (by rw [Nat.zero_mod, hlamy_low]; exact hf_pos)]
      decide
    · -- (b3,b3): `λe ≡ 0 − 0`
      have hcast : ((lam * eMod7 m b3 b3 : ℕ) : ZMod (7 ^ (m + 1)))
          = ((0 : ℕ) : ZMod _) - ((0 : ℕ) : ZMod _) := by
        rw [Nat.cast_mul, eMod7_zmod_cast_same hrel33]
        ring
      rw [eval _ _ _ _ hcast, qdig7_zero]
      rw [ite_eq_right (by simp)]
      decide
  -- Step 5: `apLen ≤ 2` — digits are `a`, `a+1`, `a+carry` (`carry ≤ 1`).
  set a := qdig7 m (lam * b3) with ha
  have hqa : qdig7 m (lam * b3) = a := ha.symm
  have hlamx_cast : (lam : ZMod (7 ^ (m + 1))) * (x : ZMod _)
      = ((7 ^ m : ℕ) : ZMod _) := by
    have h := congrArg (Nat.cast : ℕ → ZMod (7 ^ (m + 1))) hlamx_res
    rw [ZMod.natCast_mod] at h
    rw [← Nat.cast_mul]
    exact h
  have hlamy_cast : (lam : ZMod (7 ^ (m + 1))) * (y : ZMod _)
      = (f : ZMod _) := by
    have h := ZMod.natCast_mod (lam * y) (7 ^ (m + 1))
    rw [← hfdef] at h
    rw [← Nat.cast_mul]
    exact h.symm
  have hq_b1 : qdig7 m (lam * b1) = a + 1 := by
    have hb1_cast : ((lam * b1 : ℕ) : ZMod (7 ^ (m + 1)))
        = ((lam * b3 + 7 ^ m : ℕ) : ZMod _) := by
      have hkey : (lam : ZMod (7 ^ (m + 1))) * (b1 : ZMod _)
          = (lam : ZMod _) * (b3 : ZMod _) + ((7 ^ m : ℕ) : ZMod _) := by
        have hb1e : (b1 : ZMod (7 ^ (m + 1))) = (b3 : ZMod _) + (x : ZMod _) := by
          rw [hxcast]
          ring
        rw [hb1e, mul_add, hlamx_cast]
      rw [Nat.cast_mul, hkey, Nat.cast_add, Nat.cast_mul]
    have hb1_mod : (lam * b1) % 7 ^ (m + 1) = (lam * b3 + 7 ^ m) % 7 ^ (m + 1) :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mp hb1_cast
    rw [qdig7_congr hb1_mod, qdig7_add_pow, hqa]
  -- the carry `((λb3)%7^m + f)/7^m` (`f < 7^m`, low part `< 7^m`, so `≤ 1`)
  set carry := ((lam * b3) % 7 ^ m + f) / 7 ^ m with hcarrydef
  have hcarry : (lam * b3 + f) / 7 ^ m = (lam * b3) / 7 ^ m + carry := by
    have h := add_div_carry7 (lam * b3) f (7 ^ m) (Nat.pow_pos (by norm_num))
    rwa [Nat.div_eq_of_lt hf_lt, add_zero, Nat.mod_eq_of_lt hf_lt] at h
  have hcarry_le : carry ≤ 1 := by
    rw [hcarrydef]
    have h1 : (lam * b3) % 7 ^ m < 7 ^ m := Nat.mod_lt _ (Nat.pow_pos (by norm_num))
    have h2 : ((lam * b3) % 7 ^ m + f) / 7 ^ m < 2 := by
      rw [Nat.div_lt_iff_lt_mul (Nat.pow_pos (by norm_num))]
      omega
    omega
  have hq_b2 : qdig7 m (lam * b2) = a + (carry : ZMod 7) := by
    have hb2_cast : ((lam * b2 : ℕ) : ZMod (7 ^ (m + 1)))
        = ((lam * b3 + f : ℕ) : ZMod _) := by
      have hkey : (lam : ZMod (7 ^ (m + 1))) * (b2 : ZMod _)
          = (lam : ZMod _) * (b3 : ZMod _) + (f : ZMod _) := by
        have hb2e : (b2 : ZMod (7 ^ (m + 1))) = (b3 : ZMod _) + (y : ZMod _) := by
          rw [hycast]
          ring
        rw [hb2e, mul_add, hlamy_cast]
      rw [Nat.cast_mul, hkey, Nat.cast_add, Nat.cast_mul]
    have hb2_mod : (lam * b2) % 7 ^ (m + 1) = (lam * b3 + f) % 7 ^ (m + 1) :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mp hb2_cast
    rw [qdig7_congr hb2_mod, qdig7_eq_cast_div, hcarry, Nat.cast_add,
      ← qdig7_eq_cast_div m (lam * b3), hqa]
  have hq_b2_sub : qdig7 m (lam * b2) - a = (carry : ZMod 7) := by
    rw [hq_b2]
    ring
  have hsub : ({b1, b2, b3} : Finset ℕ).image (fun d => qdig7 m (lam * d))
      ⊆ cycIv a 2 := by
    intro q hq
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hq
    rw [mem_cycIv]
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with h | h | h <;> rw [h]
    · -- d = b1: digit `a + 1`
      have he : qdig7 m (lam * b1) - a = (1 : ZMod 7) := by
        rw [hq_b1]
        ring
      rw [he]
      decide
    · -- d = b2: digit `a + carry`, `carry ≤ 1`
      rw [hq_b2_sub, ZMod.val_natCast]
      have hlt : carry < 7 := by omega
      rw [Nat.mod_eq_of_lt hlt]
      omega
    · -- d = b3: digit `a`
      have he : qdig7 m (lam * b3) - a = (0 : ZMod 7) := by
        rw [hqa]
        ring
      rw [he]
      decide
  have hlen : apLen (({b1, b2, b3} : Finset ℕ).image
      (fun d => qdig7 m (lam * d))) ≤ 2 :=
    (apLen_le_iff _ 2 (by norm_num)).mpr ⟨a, hsub⟩
  exact ⟨lam, hlam7, key, hlen⟩

/-! ### The main theorem -/

/-- **Paper Lemma 9(i′)** (boundary 3-compression): three same-class
level-0 elements with difference residues `x = e(b1,b3)`,
`y = e(b2,b3)` at *distinct* levels admit a unit `λ` with every pairwise
difference digit in `{0,1,6}` and `ℓ(λB) ≤ 2`.  This is `lemma9_i` minus
the `hνm` hypothesis (which excludes the `ν = m` edge); the pair
condition is relaxed `{0,6} → {0,1,6}` accordingly. -/
theorem lemma9_i' {m : ℕ} {b1 b2 b3 : ℕ}
    (hpos : 0 < b1 ∧ 0 < b2 ∧ 0 < b3)
    (hunit : padicValNat 7 b1 = 0 ∧ padicValNat 7 b2 = 0 ∧ padicValNat 7 b3 = 0)
    (hsame : runit7 b1 = runit7 b2 ∧ runit7 b2 = runit7 b3)
    (hν : padicValNat 7 (eMod7 m b1 b3) ≠ padicValNat 7 (eMod7 m b2 b3))
    (he : eMod7 m b1 b3 ≠ 0 ∧ eMod7 m b2 b3 ≠ 0) :
    ∃ lam : ℕ, ¬ 7 ∣ lam ∧
      (∀ x ∈ ({b1, b2, b3} : Finset ℕ), ∀ y ∈ ({b1, b2, b3} : Finset ℕ),
        qdig7 m (eMod7 m (lam * x) (lam * y)) ∈ ({0, 1, 6} : Finset (ZMod 7))) ∧
      apLen (({b1, b2, b3} : Finset ℕ).image (fun d => qdig7 m (lam * d)))
        ≤ 2 := by
  by_cases hνm : padicValNat 7 (eMod7 m b1 b3) < m ∧
      padicValNat 7 (eMod7 m b2 b3) < m
  · -- both levels `< m`: the primary `lemma9_i` route.
    obtain ⟨lam, hlam7, hpair, hlen⟩ := lemma9_i hpos hunit hsame hν hνm he
    have hsub : ∀ q : ZMod 7, q ∈ ({0, 6} : Finset (ZMod 7)) →
        q ∈ ({0, 1, 6} : Finset (ZMod 7)) := by decide
    exact ⟨lam, hlam7, fun x hx y hy => hsub _ (hpair x hx y hy), hlen⟩
  · -- boundary: levels `≤ m`, distinct, not both `< m` → exactly one `= m`.
    have hxm : padicValNat 7 (eMod7 m b1 b3) ≤ m := enu7_le_of_ne he.1
    have hym : padicValNat 7 (eMod7 m b2 b3) ≤ m := enu7_le_of_ne he.2
    by_cases hxe : padicValNat 7 (eMod7 m b1 b3) = m
    · have hye : padicValNat 7 (eMod7 m b2 b3) < m := by
        rcases lt_or_eq_of_le hym with h | h
        · exact h
        · exact absurd (hxe.trans h.symm) hν
      exact lemma9_ip_aux hpos hsame hxe hye he
    · have hxl : padicValNat 7 (eMod7 m b1 b3) < m := lt_of_le_of_ne hxm hxe
      have hye : padicValNat 7 (eMod7 m b2 b3) = m := by
        rcases lt_or_eq_of_le hym with h | h
        · exact absurd ⟨hxl, h⟩ hνm
        · exact h
      obtain ⟨lam, hlam7, hpair, hlen⟩ := lemma9_ip_aux
        (b1 := b2) (b2 := b1) (b3 := b3)
        ⟨hpos.2.1, hpos.1, hpos.2.2⟩ ⟨hsame.1.symm, hsame.1.trans hsame.2⟩
        hye hxl ⟨he.2, he.1⟩
      have hset : ({b2, b1, b3} : Finset ℕ) = ({b1, b2, b3} : Finset ℕ) :=
        (Finset.insert_comm b1 b2 _).symm
      rw [hset] at hpair hlen
      exact ⟨lam, hlam7, hpair, hlen⟩

#print axioms lemma9_i'
