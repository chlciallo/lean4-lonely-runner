/-
Copyright (c) 2026 Research07 contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Research07 contributors
-/
import Research07.LRC7.Case5mTop
import Research07.LRC7.Case5mL9b
import Research07.LRC7.Case5mL10

/-!
# Paper §6.4 — `|A₁| = 3`, `|A₂| = 2` (Barajas–Serra)

For `A₁` a three-element `Finset ℕ` of `7`-adic units sharing the residue
class `s ∈ {1,2,4}` and `A₂` a two-element set of units in class `2s`,
some `7`-unit multiplier `λ` is `good7` on `A₁ ∪ A₂`.

`lemma9_ii` (the equal-level `j ∈ {2,3}` 3-compression) is landed in
`Case5mL10.lean`; `lemma9_i'` in `Case5mL9b.lean`.  The `case64` signature
matches the `Case5m.lean` dispatcher exactly (no extra hypotheses).

## Route

* `case64_tail` — the shared bridge: after a first multiplier `λ₁`,
  `apLen (q(λ₁A₁)) ≤ 3` closes via paper Lemma 12(i), while
  `apLen = 4` with `∃ d' ∈ A₂, 2i − q(λ₁d') ∈ {0,1,6}` (`i` the interval
  start, a digit of `A₁`) closes via Lemma 12(ii); the resulting
  `ZMod 7` shift is realized by a `Λ₀`-element via
  `exists_lambda0_of_shift`.
* `lemma7_i_expl` / `etd_avoid_016` / `etd_top_step` — explicit-multiplier
  variants of Lemma 7(i)/(ii): the returned `1 + k·7^{m−j}` (`j < m`)
  preserves the pure-top residues `v·7^m` verbatim, keeping `q(A₁)` in the
  `{Q, Q+u, Q+3u}` shape.  `etd_avoid_016` additionally implements the
  mirrored `q(λ·7d) = 0` branch (`qdig7_two_eq_smul`) that the landed
  `lemma7_ii` does not expose — needed for `r(e') = 6`.
* `case64` — `lemma11` numbering; case (i) goes through `lemma9_i'`
  (with a direct collapse when `e₁₃ = 0`); case (ii) with `h < m` goes
  through `lemma9_ii` applied to the swap `(d₂,d₁,d₃)`; the `h = m`
  ratio-2 case normalizes `e₂₃ ↦ N/7`, `e₁₃ ↦ 2N/7` giving `ℓ(A₁) ≤ 3`;
  the `h = m` ratio-3 case chooses the top scalar via the finite lemma
  `c64_choice` so that `e(anchor, d₄)` has digit `r' ∈ {0,1,6}` — then
  `e' = 0` (direct), `r' = 1` (`lemma7_ii` branch) or `r' = 6` (mirrored
  branch) puts `ẽ` in `{0,1,6}` and Lemma 12(ii) finishes.  When
  `ν(e₃₄) < m` the `Λ_{ν(e₃₄)}` Lemma 7(i) route is used instead (paper:
  "Lemma 7 gives `ẽ₃₄ ∉ {2,3,4,5}`"), so only `ν(e₃₄) = m` needs the
  scalar choice.
-/

private instance : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩

/-! ### Low-level clones (private in sibling files) -/

/-- `eMod7` is bounded by the modulus. -/
private theorem eMod7_lt (m x y : ℕ) : eMod7 m x y < 7 ^ (m + 1) := by
  unfold eMod7
  split_ifs <;> exact Nat.mod_lt _ (Nat.pow_pos (by norm_num))

/-- Equal `runit7` forces the `same` branch (nonzero `runit7`). -/
private theorem rel_same {u v : ℕ} (h : runit7 u = runit7 v) (hv : runit7 v ≠ 0) :
    residueRelOf u v = residueRel.same := by
  rw [residueRelOf_eq_same]
  refine ⟨?_, ?_⟩ <;> intro hcon <;> rw [h] at hcon <;>
    · have hz : runit7 v = 0 := by
        have e : runit7 v - 2 * runit7 v = 0 := sub_eq_zero.mpr hcon
        have e2 : runit7 v - 2 * runit7 v = - runit7 v := by ring
        rw [e2] at e
        exact neg_eq_zero.mp e
      exact hv hz

/-- In the `same` branch, `eMod7` is the wrapped difference. -/
private theorem eMod7_same_eq {m x y : ℕ}
    (h : residueRelOf x y = residueRel.same) :
    eMod7 m x y
      = (x % 7 ^ (m + 1) + 7 ^ (m + 1) - y % 7 ^ (m + 1)) % 7 ^ (m + 1) := by
  obtain ⟨h1, h2⟩ := (residueRelOf_eq_same).mp h
  unfold eMod7
  rw [if_neg h1, if_neg h2]

/-- `eMod7 = 0` in the `same` branch forces equal residues. -/
private theorem eq_resid_of_eMod7_eq_zero {m x y : ℕ}
    (h : eMod7 m x y = 0) (hrel : residueRelOf x y = residueRel.same) :
    x % 7 ^ (m + 1) = y % 7 ^ (m + 1) := by
  rw [eMod7_same_eq hrel] at h
  have hx : x % 7 ^ (m + 1) < 7 ^ (m + 1) := Nat.mod_lt _ (Nat.pow_pos (by norm_num))
  have hy : y % 7 ^ (m + 1) < 7 ^ (m + 1) := Nat.mod_lt _ (Nat.pow_pos (by norm_num))
  have hdvd : 7 ^ (m + 1) ∣
      x % 7 ^ (m + 1) + 7 ^ (m + 1) - y % 7 ^ (m + 1) :=
    Nat.dvd_of_mod_eq_zero h
  obtain ⟨k, hk⟩ := hdvd
  have hk1 : k = 1 := by
    have h1 : 0 < x % 7 ^ (m + 1) + 7 ^ (m + 1) - y % 7 ^ (m + 1) := by omega
    have h2 : x % 7 ^ (m + 1) + 7 ^ (m + 1) - y % 7 ^ (m + 1) <
        2 * 7 ^ (m + 1) := by omega
    rw [hk] at h1 h2
    rcases k with _ | _ | k
    · simp at h1
    · rfl
    · have : 7 ^ (m + 1) * (k + 1 + 1) ≥ 7 ^ (m + 1) * 2 := by
        apply Nat.mul_le_mul_left; omega
      omega
  rw [hk1, mul_one] at hk
  omega

/-- `eMod7 m x x = 0` for positive `x`. -/
private theorem eMod7_self {m x : ℕ} (hx : 0 < x) : eMod7 m x x = 0 := by
  have hr : runit7 x ≠ 0 := runit7_ne_zero hx
  have hne : runit7 x ≠ 2 * runit7 x := by
    intro hcon
    apply hr
    have e : runit7 x - 2 * runit7 x = 0 := sub_eq_zero.mpr hcon
    have e2 : runit7 x - 2 * runit7 x = - runit7 x := by ring
    rw [e2] at e
    exact neg_eq_zero.mp e
  unfold eMod7
  rw [if_neg hne, if_neg hne, Nat.add_sub_cancel_left, Nat.mod_self]

/-- `qdig7 m 0 = 0`. -/
private theorem qdig7_zero (m : ℕ) : qdig7 m 0 = 0 := by
  unfold qdig7
  simp

/-- `runit7 0 = 0` (local copy). -/
private theorem runit7_zero : runit7 0 = 0 := by
  unfold runit7
  simp

/-- `(a·7^m + b) / 7^m = a` when `b < 7^m` (local copy). -/
private theorem mul_pow_add_div {a b m : ℕ} (hb : b < 7 ^ m) :
    (a * 7 ^ m + b) / 7 ^ m = a := by
  have hP : 0 < 7 ^ m := Nat.pow_pos (by norm_num)
  rw [add_comm (a * 7 ^ m) b, mul_comm a (7 ^ m),
    Nat.add_mul_div_left _ _ hP, Nat.div_eq_of_lt hb, zero_add]

/-- `ZMod`-cast of `eMod7`: the wrapped residue casts to the branch
expression in `ZMod (7^{m+1})` (local copy). -/
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

/-- `same`-branch pure-top difference: `e(x,y) = v·7^m` is equivalent to
`x ≡ y + v·7^m (mod N)`, giving the exact digit shift `q(x) = q(y) + v`. -/
private theorem qdig_eq_add_of_e_top {m x y : ℕ} {v : ZMod 7}
    (hrel : residueRelOf x y = residueRel.same)
    (he : eMod7 m x y = v.val * 7 ^ m) :
    qdig7 m x = qdig7 m y + v := by
  have hN : (0 : ℕ) < 7 ^ (m + 1) := Nat.pow_pos (by norm_num)
  have hxlt : x % 7 ^ (m + 1) < 7 ^ (m + 1) := Nat.mod_lt _ hN
  have hylt : y % 7 ^ (m + 1) < 7 ^ (m + 1) := Nat.mod_lt _ hN
  rw [eMod7_same_eq hrel] at he
  -- `(a + N − b) % N = v·7^m` with `a,b < N` ⇒ `a ≡ b + v·7^m (mod N)`.
  have hmodeq : x % 7 ^ (m + 1) ≡
      y % 7 ^ (m + 1) + v.val * 7 ^ m [MOD 7 ^ (m + 1)] := by
    have h1 : (x % 7 ^ (m + 1) + 7 ^ (m + 1) - y % 7 ^ (m + 1))
        ≡ v.val * 7 ^ m [MOD 7 ^ (m + 1)] := by
      rw [Nat.ModEq, he, Nat.mod_eq_of_lt]
      rw [pow_succ' 7 m]
      exact Nat.mul_lt_mul_of_pos_right (ZMod.val_lt v)
        (Nat.pow_pos (by norm_num))
    have h2 := h1.add (Nat.ModEq.refl (y % 7 ^ (m + 1)))
    rw [Nat.sub_add_cancel (by omega : y % 7 ^ (m + 1) ≤
        x % 7 ^ (m + 1) + 7 ^ (m + 1))] at h2
    rw [add_comm (v.val * 7 ^ m) (y % 7 ^ (m + 1))] at h2
    have h3 : x % 7 ^ (m + 1) + 7 ^ (m + 1) ≡ x % 7 ^ (m + 1)
        [MOD 7 ^ (m + 1)] := by
      rw [Nat.ModEq]
      rw [Nat.add_mod_right]
    exact h3.symm.trans h2
  have hres : x % 7 ^ (m + 1)
      = (y % 7 ^ (m + 1) + v.val * 7 ^ m) % 7 ^ (m + 1) := by
    rw [Nat.ModEq] at hmodeq
    rw [Nat.mod_eq_of_lt hxlt] at hmodeq
    exact hmodeq
  rw [qdig7_add_top_resid hres, ZMod.natCast_zmod_val]

/-! ### `ZMod 7`-cast of `eMod7` and the `7 ∣ e` divisibility fact -/

/-- `ZMod 7`-cast of `eMod7` (the `ZMod N` version reduced mod `7`). -/
private theorem eMod7_zmod7 (m x y : ℕ) :
    ((eMod7 m x y : ℕ) : ZMod 7) =
      if runit7 y = 2 * runit7 x then 2 * (x : ZMod 7) - (y : ZMod 7)
      else if runit7 x = 2 * runit7 y then 2 * (y : ZMod 7) - (x : ZMod 7)
      else (x : ZMod 7) - (y : ZMod 7) := by
  have h7N : (7 : ℕ) ∣ 7 ^ (m + 1) := dvd_pow_self 7 (by omega)
  have hmod : ∀ a : ℕ, ((a % 7 ^ (m + 1) : ℕ) : ZMod 7) = (a : ZMod 7) := by
    intro a
    exact (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
      (Nat.mod_mod_of_dvd a h7N)
  have hN : ((7 ^ (m + 1) : ℕ) : ZMod 7) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr h7N
  unfold eMod7
  split_ifs with h1 h2
  · rw [hmod, Nat.cast_sub (by
      have : y % 7 ^ (m + 1) < 7 ^ (m + 1) :=
        Nat.mod_lt _ (Nat.pow_pos (by norm_num))
      omega : y % 7 ^ (m + 1) ≤ 2 * (x % 7 ^ (m + 1)) + 7 ^ (m + 1))]
    rw [Nat.cast_add, Nat.cast_mul, hmod, hmod, hN]
    ring
  · rw [hmod, Nat.cast_sub (by
      have : x % 7 ^ (m + 1) < 7 ^ (m + 1) :=
        Nat.mod_lt _ (Nat.pow_pos (by norm_num))
      omega : x % 7 ^ (m + 1) ≤ 2 * (y % 7 ^ (m + 1)) + 7 ^ (m + 1))]
    rw [Nat.cast_add, Nat.cast_mul, hmod, hmod, hN]
    ring
  · rw [hmod, Nat.cast_sub (by
      have : y % 7 ^ (m + 1) < 7 ^ (m + 1) :=
        Nat.mod_lt _ (Nat.pow_pos (by norm_num))
      omega : y % 7 ^ (m + 1) ≤ x % 7 ^ (m + 1) + 7 ^ (m + 1))]
    rw [Nat.cast_add, hmod, hmod, hN]
    ring

/-- `7 ∣ e(x,y)` for a `twoX` pair (`r(y) = 2r(x)`). -/
private theorem dvd7_eMod7_twoX {m x y : ℕ}
    (hx : padicValNat 7 x = 0) (hy : padicValNat 7 y = 0)
    (hrel : runit7 y = 2 * runit7 x) : 7 ∣ eMod7 m x y := by
  apply (ZMod.natCast_eq_zero_iff _ _).mp
  rw [eMod7_zmod7, if_pos hrel]
  rw [runit7_of_padic_zero hx, runit7_of_padic_zero hy] at hrel
  rw [hrel]
  ring

/-- `7 ∣ e(x,y)` for a `same` pair of units in one class. -/
private theorem dvd7_eMod7_same {m x y : ℕ}
    (hx : padicValNat 7 x = 0) (hy : padicValNat 7 y = 0)
    (h : runit7 x = runit7 y)
    (hrel : residueRelOf x y = residueRel.same) : 7 ∣ eMod7 m x y := by
  obtain ⟨h1, h2⟩ := (residueRelOf_eq_same).mp hrel
  apply (ZMod.natCast_eq_zero_iff _ _).mp
  rw [eMod7_zmod7, if_neg h1, if_neg h2]
  rw [runit7_of_padic_zero hx, runit7_of_padic_zero hy] at h
  rw [h, sub_self]

/-! ### Pure-top residues under scaling -/

/-- `ν(v·7^m) = m` for `0 < v < 7`. -/
private theorem nu_pow7 {m v : ℕ} (hv : 0 < v) (hv7 : v < 7) :
    padicValNat 7 (v * 7 ^ m) = m := by
  have hv0 : padicValNat 7 v = 0 := padicValNat.eq_zero_of_not_dvd (fun h => by
    have := Nat.le_of_dvd hv h
    omega)
  rw [padicValNat.mul (ne_of_gt hv) (pow_ne_zero m (by norm_num)), hv0,
    padicValNat.prime_pow m, zero_add]

/-- `runit7 (v·7^m) = v` for nonzero `v : ZMod 7`. -/
private theorem runit7_pow7 {m : ℕ} {v : ZMod 7} (hv : v ≠ 0) :
    runit7 (v.val * 7 ^ m) = v := by
  have hvpos : 0 < v.val := Nat.pos_of_ne_zero (by rwa [Ne, ZMod.val_eq_zero])
  unfold runit7
  rw [nu_pow7 hvpos (ZMod.val_lt v),
    Nat.mul_div_cancel _ (Nat.pow_pos (by norm_num)), ZMod.natCast_zmod_val]

/-- `Λ_j` (with `j < m`) preserves a pure top residue `v·7^m` mod `N`. -/
private theorem top_resid_multLow {m j k : ℕ} (hjm : j < m) {v : ZMod 7}
    (hv : v ≠ 0) :
    (1 + k * 7 ^ (m - j)) * (v.val * 7 ^ m) % 7 ^ (m + 1) = v.val * 7 ^ m := by
  have hvpos : 0 < v.val := Nat.pos_of_ne_zero (by rwa [Ne, ZMod.val_eq_zero])
  have hlt : v.val * 7 ^ m < 7 ^ (m + 1) := by
    rw [pow_succ']
    exact Nat.mul_lt_mul_of_pos_right (ZMod.val_lt v)
      (Nat.pow_pos (by norm_num))
  rw [residN_multLow7 hjm
    (by rw [nu_pow7 hvpos (ZMod.val_lt v)]; exact hjm)]
  exact Nat.mod_eq_of_lt hlt

/-- Scaling a pure-top difference `e = v·7^m` by a `7`-unit `c` gives the
pure-top difference `(c·v)·7^m` (digit product in `ZMod 7`). -/
private theorem e_smul_top {m c x y : ℕ} (hc : runit7 c ≠ 0) {v : ZMod 7}
    (he : eMod7 m x y = v.val * 7 ^ m) :
    eMod7 m (c * x) (c * y) = ((c : ZMod 7) * v).val * 7 ^ m := by
  have hval : ((c : ZMod 7) * v).val = (c * v.val) % 7 := by
    have hcast : ((c * v.val : ℕ) : ZMod 7) = (c : ZMod 7) * v := by
      rw [Nat.cast_mul, ZMod.natCast_zmod_val]
    rw [← hcast, ZMod.val_natCast]
  rw [eMod7_smul hc, he, hval,
    show c * (v.val * 7 ^ m) = (c * v.val) * 7 ^ m from by ring,
    show (7 : ℕ) ^ (m + 1) = 7 * 7 ^ m from pow_succ' 7 m,
    Nat.mul_mod_mul_right]

/-- The `twoX` difference decomposes: `e(x,w) = (2·e(x,z) + e(z,w)) % N`
when `w` is in `twoX` ratio to both `x` and `z`. -/
private theorem eMod7_twoX_add {m x z w : ℕ}
    (hxz : residueRelOf x z = residueRel.same)
    (hzw : runit7 w = 2 * runit7 z) (hxw : runit7 w = 2 * runit7 x) :
    eMod7 m x w = (2 * eMod7 m x z + eMod7 m z w) % 7 ^ (m + 1) := by
  obtain ⟨hxz1, hxz2⟩ := (residueRelOf_eq_same).mp hxz
  have hcast : ((eMod7 m x w : ℕ) : ZMod (7 ^ (m + 1)))
      = ((2 * eMod7 m x z + eMod7 m z w : ℕ) : ZMod _) := by
    rw [Nat.cast_add, Nat.cast_mul, eMod7_zmod_cast, eMod7_zmod_cast,
      eMod7_zmod_cast, if_pos hxw, if_neg hxz1, if_neg hxz2, if_pos hzw]
    push_cast
    ring
  rw [ZMod.natCast_eq_natCast_iff'] at hcast
  have hlt : eMod7 m x w < 7 ^ (m + 1) := eMod7_lt _ _ _
  rwa [Nat.mod_eq_of_lt hlt] at hcast

/-- For `w` in `twoX` ratio to `x` and `z` (same class), pure-top
differences `e(x,z) = a·7^m`, `e(z,w) = b·7^m` give `e(x,w) = (2a+b)·7^m`. -/
private theorem e_top_twoX {m x z w : ℕ}
    (hxz : residueRelOf x z = residueRel.same)
    (hzw : runit7 w = 2 * runit7 z) (hxw : runit7 w = 2 * runit7 x)
    {a b : ZMod 7}
    (h1 : eMod7 m x z = a.val * 7 ^ m) (h2 : eMod7 m z w = b.val * 7 ^ m) :
    eMod7 m x w = (2 * a + b).val * 7 ^ m := by
  rw [eMod7_twoX_add hxz hzw hxw, h1, h2]
  have hsum : 2 * (a.val * 7 ^ m) + b.val * 7 ^ m
      = (2 * a.val + b.val) * 7 ^ m := by ring
  rw [hsum, show (7 : ℕ) ^ (m + 1) = 7 * 7 ^ m from pow_succ' 7 m,
    Nat.mul_mod_mul_right]
  congr 1
  have hval : (2 * a + b).val = (2 * a.val + b.val) % 7 := by
    have hcast : ((2 * a.val + b.val : ℕ) : ZMod 7) = 2 * a + b := by
      rw [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
        ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    rw [← hcast, ZMod.val_natCast]
  rw [hval]

/-! ### Lemma 7 variants with explicit multipliers -/

/-- Explicit-multiplier form of `lemma7_i`: returns the `Λ_{ν(e)}`
parameter `k`. -/
private theorem lemma7_i_expl {m : ℕ} {d d' : ℕ}
    (hd : padicValNat 7 d = 0) (hd' : padicValNat 7 d' = 0)
    (hpos : 0 < d) (hpos' : 0 < d')
    (hrel : runit7 d' = 2 * runit7 d)
    (hν : 0 < padicValNat 7 (eMod7 m d d'))
    (hνm : padicValNat 7 (eMod7 m d d') < m)
    {X : Finset (ZMod 7)} (hX : apLen X ≤ 4) :
    ∃ k : ℕ, k < 7 ∧
      etd7 m ((1 + k * 7 ^ (m - padicValNat 7 (eMod7 m d d'))) * d)
        ((1 + k * 7 ^ (m - padicValNat 7 (eMod7 m d d'))) * d') ∉ X := by
  set e := eMod7 m d d' with he
  have he0 : e ≠ 0 := by
    intro h0
    rw [h0] at hν
    simp at hν
  obtain ⟨x, hx⟩ := exists_not_mem_three hX
  obtain ⟨k, hk7, hkq⟩ := exists_multLow_set_qdig hνm rfl he0 (x - 1)
  refine ⟨k, hk7, ?_⟩
  have hlamr : runit7 (1 + k * 7 ^ (m - padicValNat 7 e)) = 1 :=
    runit7_multLow hνm
  have he' : eMod7 m ((1 + k * 7 ^ (m - padicValNat 7 e)) * d)
        ((1 + k * 7 ^ (m - padicValNat 7 e)) * d')
      = ((1 + k * 7 ^ (m - padicValNat 7 e)) * e) % 7 ^ (m + 1) :=
    eMod7_mul hlamr
  have hqe : qdig7 m (eMod7 m ((1 + k * 7 ^ (m - padicValNat 7 e)) * d)
        ((1 + k * 7 ^ (m - padicValNat 7 e)) * d')) = x - 1 := by
    rw [he', qdig7_congr (Nat.mod_mod _ _)]
    exact hkq
  have hbound := qdig_eMod_sub_etd7 (m := m)
    (x := (1 + k * 7 ^ (m - padicValNat 7 e)) * d)
    (y := (1 + k * 7 ^ (m - padicValNat 7 e)) * d')
  rw [hqe] at hbound
  simp only [Finset.mem_insert, Finset.mem_singleton] at hbound
  rcases hbound with hb | hb | hb
  · have he7 : etd7 m ((1 + k * 7 ^ (m - padicValNat 7 e)) * d)
        ((1 + k * 7 ^ (m - padicValNat 7 e)) * d') = x - 1 :=
      (sub_eq_zero.mp hb).symm
    rw [he7]
    exact hx 1 (by decide)
  · have he7 : etd7 m ((1 + k * 7 ^ (m - padicValNat 7 e)) * d)
        ((1 + k * 7 ^ (m - padicValNat 7 e)) * d') = x - 2 := by
      have h0 : x - 1 - 1 = etd7 m ((1 + k * 7 ^ (m - padicValNat 7 e)) * d)
          ((1 + k * 7 ^ (m - padicValNat 7 e)) * d') := by
        linear_combination hb
      rw [← h0]
      ring
    rw [he7]
    exact hx 2 (by decide)
  · have he7 : etd7 m ((1 + k * 7 ^ (m - padicValNat 7 e)) * d)
        ((1 + k * 7 ^ (m - padicValNat 7 e)) * d') = x := by
      have h0 : x - 1 - 6 = etd7 m ((1 + k * 7 ^ (m - padicValNat 7 e)) * d)
          ((1 + k * 7 ^ (m - padicValNat 7 e)) * d') := by
        linear_combination hb
      rw [← h0]
      have h77 : x - 1 - 6 = x - 7 := by ring
      rw [h77, show (7 : ZMod 7) = 0 by decide, sub_zero]
    rw [he7]
    have hx0 := hx 0 (by decide)
    rwa [sub_zero] at hx0

/-- Mirrored `lemma7_ii` with an explicit multiplier and target `{0,1,6}`:
for a `twoX` pair at level `m` with `r(e) ∈ {1,6}`, a `Λ₁`-element puts
`ẽ ∈ {0,1,6}`.  `r = 1` uses `q(λ·7d) = 6` (`qdig7_two_eq_smul_add_one`);
`r = 6` uses `q(λ·7d) = 0` (`qdig7_two_eq_smul`). -/
private theorem etd_avoid_016 {m : ℕ} (hm : 2 ≤ m) {d d' : ℕ}
    (hd : padicValNat 7 d = 0) (hd' : padicValNat 7 d' = 0)
    (hpos : 0 < d) (hpos' : 0 < d')
    (hrel : runit7 d' = 2 * runit7 d)
    (hν : padicValNat 7 (eMod7 m d d') = m)
    (hr : runit7 (eMod7 m d d') ∈ ({1, 6} : Finset (ZMod 7))) :
    ∃ k : ℕ, k < 7 ∧
      etd7 m ((1 + k * 7 ^ (m - 1)) * d) ((1 + k * 7 ^ (m - 1)) * d')
        ∈ ({0, 1, 6} : Finset (ZMod 7)) := by
  set e := eMod7 m d d' with he
  have h1m : 1 < m := by omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hr
  -- common scaffolding for both branches
  have hrd : runit7 d ≠ 0 := runit7_ne_zero hpos
  rcases hr with hr | hr
  · -- `r(e) = 1`: choose `q(λ·7d) = 6`
    obtain ⟨k, hk7, hkq⟩ :=
      exists_multLow_one_set_seven' (by omega : (0:ℕ) < m) hd hpos 6
    refine ⟨k, hk7, ?_⟩
    set lam := 1 + k * 7 ^ (m - 1) with hlam
    have hlamr : runit7 lam = 1 := runit7_multLow h1m
    have h7d : qdig7 m (7 * (lam * d)) = 6 := by
      have e' : 7 * (lam * d) = lam * (7 * d) := by ring
      rw [e']; exact hkq
    have h2d : qdig7 m (2 * (lam * d)) = 2 * qdig7 m (lam * d) + 1 :=
      qdig7_two_eq_smul_add_one (by omega) h7d
    have hrld : runit7 (lam * d) = runit7 d := by
      rw [runit7_mul, hlamr, one_mul]
    have hrld' : runit7 (lam * d') = 2 * runit7 d := by
      rw [runit7_mul, hlamr, one_mul, hrel]
    have hr2ld : runit7 (2 * (lam * d)) = 2 * runit7 d := by
      rw [runit7_mul, runit7_two, hrld]
    have hsame : residueRelOf (2 * (lam * d)) (lam * d')
        = residueRel.same := by
      rw [residueRelOf_eq_same]
      refine ⟨?_, ?_⟩ <;> rw [hrld', hr2ld] <;> intro hcon <;>
        · have h0 : (2 : ZMod 7) * runit7 d = 0 := by
            have hsub : 2 * (2 * runit7 d) - 2 * runit7 d
                = (2 : ZMod 7) * runit7 d := by ring
            rw [← hcon, sub_self] at hsub
            exact hsub.symm
          rcases mul_eq_zero.mp h0 with h2 | h
          · exact absurd h2 (by decide)
          · exact hrd h
    obtain ⟨hif1, hif2⟩ := (residueRelOf_eq_same).mp hsame
    have he2 : eMod7 m (2 * (lam * d)) (lam * d') = e := by
      have h2l : 2 * (lam * d) = lam * (2 * d) := by ring
      rw [h2l, eMod7_mul hlamr, eMod7_two_mul_left hrel hpos]
      have hlt : e < 7 ^ (m + 1) := by
        rw [he]; unfold eMod7
        split_ifs <;> exact Nat.mod_lt _ (Nat.pow_pos (by norm_num))
      have hres : (lam * e) % 7 ^ (m + 1) = e % 7 ^ (m + 1) :=
        residN_multLow7 (k := k) h1m (by omega : 1 < padicValNat 7 e)
      rw [hres, Nat.mod_eq_of_lt hlt]
    have het2 : etd7 m (2 * (lam * d)) (lam * d') =
        qdig7 m (2 * (lam * d)) - qdig7 m (lam * d') := by
      unfold etd7
      rw [if_neg hif1, if_neg hif2]
    have hbound := qdig_eMod_sub_etd7_same (m := m)
      (x := 2 * (lam * d)) (y := lam * d') hsame
    rw [he2, qdig7_eq_runit7_of_top hν, het2, h2d, hr] at hbound
    have het : etd7 m (lam * d) (lam * d') =
        2 * qdig7 m (lam * d) - qdig7 m (lam * d') := by
      unfold etd7
      rw [if_pos (by rw [hrld', hrld])]
    rw [het]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hbound ⊢
    rcases hbound with hb | hb
    · left
      have : 2 * qdig7 m (lam * d) - qdig7 m (lam * d') = 0 := by
        linear_combination -hb
      exact this
    · right; left
      -- `1 − (ẽ+1) = 6` ⇒ `ẽ + 1 = 1 − 6 = 2` ⇒ `ẽ = 1`
      have hX : 2 * qdig7 m (lam * d) + 1 - qdig7 m (lam * d')
          = (1 : ZMod 7) - 6 := by linear_combination -hb
      rw [show ((1 : ZMod 7) - 6) = 2 by decide] at hX
      have : 2 * qdig7 m (lam * d) - qdig7 m (lam * d') = 1 := by
        linear_combination hX
      exact this
  · -- `r(e) = 6`: mirrored branch, `q(λ·7d) = 0`
    obtain ⟨k, hk7, hkq⟩ :=
      exists_multLow_one_set_seven' (by omega : (0:ℕ) < m) hd hpos 0
    refine ⟨k, hk7, ?_⟩
    set lam := 1 + k * 7 ^ (m - 1) with hlam
    have hlamr : runit7 lam = 1 := runit7_multLow h1m
    have h7d : qdig7 m (7 * (lam * d)) = 0 := by
      have e' : 7 * (lam * d) = lam * (7 * d) := by ring
      rw [e']; exact hkq
    have h2d : qdig7 m (2 * (lam * d)) = 2 * qdig7 m (lam * d) :=
      qdig7_two_eq_smul (by omega) h7d
    have hrld : runit7 (lam * d) = runit7 d := by
      rw [runit7_mul, hlamr, one_mul]
    have hrld' : runit7 (lam * d') = 2 * runit7 d := by
      rw [runit7_mul, hlamr, one_mul, hrel]
    have hr2ld : runit7 (2 * (lam * d)) = 2 * runit7 d := by
      rw [runit7_mul, runit7_two, hrld]
    have hsame : residueRelOf (2 * (lam * d)) (lam * d')
        = residueRel.same := by
      rw [residueRelOf_eq_same]
      refine ⟨?_, ?_⟩ <;> rw [hrld', hr2ld] <;> intro hcon <;>
        · have h0 : (2 : ZMod 7) * runit7 d = 0 := by
            have hsub : 2 * (2 * runit7 d) - 2 * runit7 d
                = (2 : ZMod 7) * runit7 d := by ring
            rw [← hcon, sub_self] at hsub
            exact hsub.symm
          rcases mul_eq_zero.mp h0 with h2 | h
          · exact absurd h2 (by decide)
          · exact hrd h
    obtain ⟨hif1, hif2⟩ := (residueRelOf_eq_same).mp hsame
    have he2 : eMod7 m (2 * (lam * d)) (lam * d') = e := by
      have h2l : 2 * (lam * d) = lam * (2 * d) := by ring
      rw [h2l, eMod7_mul hlamr, eMod7_two_mul_left hrel hpos]
      have hlt : e < 7 ^ (m + 1) := by
        rw [he]; unfold eMod7
        split_ifs <;> exact Nat.mod_lt _ (Nat.pow_pos (by norm_num))
      have hres : (lam * e) % 7 ^ (m + 1) = e % 7 ^ (m + 1) :=
        residN_multLow7 (k := k) h1m (by omega : 1 < padicValNat 7 e)
      rw [hres, Nat.mod_eq_of_lt hlt]
    have het2 : etd7 m (2 * (lam * d)) (lam * d') =
        qdig7 m (2 * (lam * d)) - qdig7 m (lam * d') := by
      unfold etd7
      rw [if_neg hif1, if_neg hif2]
    have hbound := qdig_eMod_sub_etd7_same (m := m)
      (x := 2 * (lam * d)) (y := lam * d') hsame
    rw [he2, qdig7_eq_runit7_of_top hν, het2, h2d, hr] at hbound
    have het : etd7 m (lam * d) (lam * d') =
        2 * qdig7 m (lam * d) - qdig7 m (lam * d') := by
      unfold etd7
      rw [if_pos (by rw [hrld', hrld])]
    rw [het]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hbound ⊢
    rcases hbound with hb | hb
    · right; right
      have : 2 * qdig7 m (lam * d) - qdig7 m (lam * d') = 6 := by
        linear_combination -hb
      exact this
    · left
      have : 2 * qdig7 m (lam * d) - qdig7 m (lam * d') = 0 := by
        linear_combination -hb
      exact this

/-- One-step `ẽ`-correction at the top level: for a `twoX` pair whose
difference is the pure-top `v·7^m` with `v ∈ {0,1,6}`, some `Λ₁`-element
(`k < 7`) puts `ẽ ∈ {0,1,6}`. -/
private theorem etd_top_step {m : ℕ} (hm : 2 ≤ m) {d d' : ℕ}
    (hd : padicValNat 7 d = 0) (hd' : padicValNat 7 d' = 0)
    (hpos : 0 < d) (hpos' : 0 < d')
    (hrel : runit7 d' = 2 * runit7 d)
    {v : ZMod 7} (he : eMod7 m d d' = v.val * 7 ^ m)
    (hv : v ∈ ({0, 1, 6} : Finset (ZMod 7))) :
    ∃ k : ℕ, k < 7 ∧
      etd7 m ((1 + k * 7 ^ (m - 1)) * d) ((1 + k * 7 ^ (m - 1)) * d')
        ∈ ({0, 1, 6} : Finset (ZMod 7)) := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with hv0 | hv1 | hv6
  · -- `v = 0`: `e = 0`, `q(e) = 0` forces `−ẽ ∈ {0,1,6}`; take `k = 0`.
    refine ⟨0, by norm_num, ?_⟩
    rw [zero_mul, add_zero, one_mul, one_mul]
    have he0 : eMod7 m d d' = 0 := by
      rw [he, hv0]
      simp
    have hb := qdig_eMod_sub_etd7 (m := m) (x := d) (y := d')
    rw [he0, qdig7_zero] at hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb ⊢
    rcases hb with h0 | h0 | h0
    · left
      exact (sub_eq_zero.mp h0).symm
    · right; right
      have : etd7 m d d' = -1 := by linear_combination -h0
      rw [this]; decide
    · right; left
      have : etd7 m d d' = -6 := by linear_combination -h0
      rw [this]; decide
  · -- `v = 1`: `etd_avoid_016` `r = 1` branch
    have hν : padicValNat 7 (eMod7 m d d') = m := by
      rw [he, hv1]
      exact nu_pow7 (by decide : 0 < (1 : ZMod 7).val)
        (ZMod.val_lt _)
    have hr : runit7 (eMod7 m d d') = 1 := by
      rw [he, hv1]
      exact runit7_pow7 (by decide)
    exact etd_avoid_016 hm hd hd' hpos hpos' hrel hν
      (by rw [hr]; decide)
  · -- `v = 6`: `etd_avoid_016` `r = 6` branch
    have hν : padicValNat 7 (eMod7 m d d') = m := by
      rw [he, hv6]
      exact nu_pow7 (by decide : 0 < (6 : ZMod 7).val)
        (ZMod.val_lt _)
    have hr : runit7 (eMod7 m d d') = 6 := by
      rw [he, hv6]
      exact runit7_pow7 (by decide)
    exact etd_avoid_016 hm hd hd' hpos hpos' hrel hν
      (by rw [hr]; decide)

/-! ### Finite `ZMod 7` facts (decide) -/

/-- `apLen ≤ 7` for every set (the universal cover). -/
private theorem apLen_le7' (X : Finset (ZMod 7)) : apLen X ≤ 7 := by
  rw [apLen_le_iff X 7 le_rfl]
  exact ⟨0, fun x _ => by rw [mem_cycIv, sub_zero]; exact ZMod.val_lt x⟩

/-- The `{Q, Q+u, Q+3u}` covers: `u ∈ {1,3}` start `Q`. -/
private theorem c64_cover_a :
    ∀ Q u : ZMod 7, u ∈ ({1, 3} : Finset (ZMod 7)) →
      ({Q + 3 * u, Q + u, Q} : Finset (ZMod 7)) ⊆ cycIv Q 4 := by
  decide

/-- The `{Q, Q+u, Q+3u}` covers: `u ∈ {4,5}` start `Q+u`. -/
private theorem c64_cover_b :
    ∀ Q u : ZMod 7, u ∈ ({4, 5} : Finset (ZMod 7)) →
      ({Q + 3 * u, Q + u, Q} : Finset (ZMod 7)) ⊆ cycIv (Q + u) 4 := by
  decide

/-- The `{Q, Q+u, Q+3u}` covers: `u ∈ {2,6}` start `Q+3u`. -/
private theorem c64_cover_c :
    ∀ Q u : ZMod 7, u ∈ ({2, 6} : Finset (ZMod 7)) →
      ({Q + 3 * u, Q + u, Q} : Finset (ZMod 7)) ⊆ cycIv (Q + 3 * u) 4 := by
  decide

/-- `apLen` of the ratio-3 triple is always `4`. -/
private theorem apLen_03u :
    ∀ Q u : ZMod 7, u ≠ 0 →
      apLen ({Q + 3 * u, Q + u, Q} : Finset (ZMod 7)) = 4 := by
  decide

/-- The scalar choice: for `B ≠ 0` some `u` makes the relevant difference
digit `u·(B + off)` land in the right target set for the matching anchor.
(`u ∈ {1,3}` anchor `d₃` gives `uB ∈ {1,6}`; `u ∈ {4,5}` anchor `d₂`
gives `u(B+2) ∈ {0,1,6}`; `u ∈ {2,6}` anchor `d₁` gives `u(B−1) ∈
{0,1,6}`.) -/
private theorem c64_choice :
    ∀ B : ZMod 7, B ≠ 0 → ∃ u : ZMod 7,
      (u ∈ ({1, 3} : Finset (ZMod 7)) ∧
        u * B ∈ ({1, 6} : Finset (ZMod 7))) ∨
      (u ∈ ({4, 5} : Finset (ZMod 7)) ∧
        u * (B + 2) ∈ ({0, 1, 6} : Finset (ZMod 7))) ∨
      (u ∈ ({2, 6} : Finset (ZMod 7)) ∧
        u * (B - 1) ∈ ({0, 1, 6} : Finset (ZMod 7))) := by
  decide

/-- `{2,3,4,5}` has `apLen ≤ 4` (it is `cycIv 2 4`). -/
private theorem apLen_2345 :
    apLen ({2, 3, 4, 5} : Finset (ZMod 7)) ≤ 4 := by
  rw [apLen_le_iff _ 4 (by norm_num)]
  exact ⟨2, by decide⟩

/-- Outside `{2,3,4,5}` means inside `{0,1,6}`. -/
private theorem mem_016_of_not_2345 {x : ZMod 7}
    (h : x ∉ ({2, 3, 4, 5} : Finset (ZMod 7))) :
    x ∈ ({0, 1, 6} : Finset (ZMod 7)) := by
  revert h x
  decide

/-- A minimum-length cover can be started at a set element: sliding the
window until its left edge hits the set. -/
private theorem min_cover_mem {X : Finset (ZMod 7)} (hne : X.Nonempty)
    {i : ZMod 7} {L : ℕ} (hsub : X ⊆ cycIv i L) :
    ∃ i' ∈ X, X ⊆ cycIv i' L := by
  obtain ⟨x0, hx0, hmin⟩ :=
    Finset.exists_min_image X (fun x => (x - i).val) hne
  refine ⟨x0, hx0, ?_⟩
  intro x hx
  have hxsub := hsub hx
  rw [mem_cycIv] at hxsub ⊢
  have hcast : x - x0 = (x - i) - ((x0 - i).val : ZMod 7) := by
    rw [ZMod.natCast_zmod_val (x0 - i)]
    ring
  have hcond : (((x0 - i).val : ZMod 7)).val ≤ (x - i).val := by
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (ZMod.val_lt _)]
    exact hmin x hx
  rw [hcast, ZMod.val_sub hcond]
  omega

/-! ### The shared `lemma12` + `Λ₀`-shift bridge -/

/-- The shared finish: after a first multiplier `λ₁` (a `7`-unit),
`q(λ₁A₁)` is covered by `cycIv i ℓ` with `i` a digit of `λ₁A₁`, and either
`ℓ ≤ 3` (Lemma 12(i)) or `ℓ = 4` with an `A₂` element satisfying the
`ẽ`-condition `2i − q(λ₁d') ∈ {0,1,6}` (Lemma 12(ii)). -/
private theorem case64_tail {m : ℕ} (hm : 0 < m) {A1 A2 : Finset ℕ}
    (hpos : ∀ d ∈ A1 ∪ A2, 0 < d)
    (hunit : ∀ d ∈ A1 ∪ A2, padicValNat 7 d = 0)
    {s : ZMod 7} (hs : s ≠ 0)
    (hcls1 : ∀ d ∈ A1, runit7 d = s)
    (hcls2 : ∀ d ∈ A2, runit7 d = 2 * s)
    (hA2 : A2.card = 2)
    {lam₁ : ℕ} (hlam₁ : ¬ 7 ∣ lam₁)
    {i : ZMod 7}
    (himem : i ∈ (A1.image (fun d => lam₁ * d)).image (qdig7 m))
    (hsub : (A1.image (fun d => lam₁ * d)).image (qdig7 m)
      ⊆ cycIv i (apLen ((A1.image (fun d => lam₁ * d)).image (qdig7 m))))
    (h : apLen ((A1.image (fun d => lam₁ * d)).image (qdig7 m)) ≤ 3 ∨
      (apLen ((A1.image (fun d => lam₁ * d)).image (qdig7 m)) = 4 ∧
        ∃ d' ∈ A2, (2 * i - qdig7 m (lam₁ * d') : ZMod 7)
          ∈ ({0, 1, 6} : Finset (ZMod 7)))) :
    ∃ lam : ℕ, ¬ 7 ∣ lam ∧ good7 m lam (A1 ∪ A2) := by
  classical
  set X1 := (A1.image (fun d => lam₁ * d)).image (qdig7 m) with hX1
  set X2 := (A2.image (fun d => lam₁ * d)).image (qdig7 m) with hX2
  set t : ZMod 7 := 1 - i with ht
  set Y1 := X1.image (· + t) with hY1
  set Y2 := X2.image (· + 2 * t) with hY2
  have hapY1 : apLen Y1 = apLen X1 := apLen_image_add X1 t
  have h1mem : (1 : ZMod 7) ∈ Y1 := by
    apply Finset.mem_image.mpr
    exact ⟨i, himem, by rw [ht]; ring⟩
  have hcardY2 : Y2.card ≤ 2 := by
    calc Y2.card ≤ X2.card := Finset.card_image_le
      _ ≤ (A2.image (fun d => lam₁ * d)).card := Finset.card_image_le
      _ ≤ A2.card := Finset.card_image_le
      _ = 2 := hA2
  have hcov : Y1 ⊆ cycIv 1 (apLen Y1) := by
    intro x hx
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hx
    rw [mem_cycIv, hapY1]
    have hqsub := hsub hq
    rw [mem_cycIv] at hqsub
    have heq : q + t - 1 = q - i := by rw [ht]; ring
    rw [heq]
    exact hqsub
  have hdisj : apLen Y1 ≤ 3 ∨ (apLen Y1 = 4 ∧
      ∃ d' ∈ Y2, (2 - d' : ZMod 7) ∈ ({0, 1, 6} : Finset (ZMod 7))) := by
    rw [hapY1]
    rcases h with h3 | ⟨h4, d', hd', hcond⟩
    · exact Or.inl h3
    · refine Or.inr ⟨h4, ?_⟩
      refine ⟨qdig7 m (lam₁ * d') + 2 * t, ?_, ?_⟩
      · apply Finset.mem_image.mpr
        exact ⟨qdig7 m (lam₁ * d'), Finset.mem_image.mpr ⟨lam₁ * d',
          Finset.mem_image.mpr ⟨d', hd', rfl⟩, rfl⟩, rfl⟩
      · have heq : (2 : ZMod 7) - (qdig7 m (lam₁ * d') + 2 * t)
            = 2 * i - qdig7 m (lam₁ * d') := by rw [ht]; ring
        rw [heq]; exact hcond
  obtain ⟨k, hk, havoid⟩ := lemma12 1 (by decide) h1mem hcardY2 hcov hdisj
  -- assemble the `exists_lambda0_of_shift` avoid-set on `B = λ₁·(A₁∪A₂)`
  set B := (A1 ∪ A2).image (fun d => lam₁ * d) with hB
  set s' : ZMod 7 := runit7 lam₁ * s with hs'
  have hlam₁0 : lam₁ ≠ 0 := fun hh => hlam₁ (hh ▸ dvd_zero _)
  have hrl1 : runit7 lam₁ ≠ 0 := runit7_ne_zero (Nat.pos_of_ne_zero hlam₁0)
  have hs'0 : s' ≠ 0 := by rw [hs']; exact mul_ne_zero hrl1 hs
  have hunitB : ∀ d ∈ B, padicValNat 7 d = 0 := by
    intro d hd
    obtain ⟨d₀, hd₀, rfl⟩ := Finset.mem_image.mp hd
    rw [padicValNat_mul_seven hlam₁ (ne_of_gt (hpos d₀ hd₀))]
    exact hunit d₀ hd₀
  have hclsB : ∀ d ∈ B, runit7 d ∈ ({s', 2 * s', 4 * s'} : Finset (ZMod 7)) := by
    intro d hd
    obtain ⟨d₀, hd₀, rfl⟩ := Finset.mem_image.mp hd
    rw [runit7_mul]
    rcases Finset.mem_union.mp hd₀ with hd₁ | hd₂
    · rw [hcls1 d₀ hd₁]
      exact Finset.mem_insert_self _ _
    · rw [hcls2 d₀ hd₂]
      have : runit7 lam₁ * (2 * s) = 2 * s' := by rw [hs']; ring
      rw [this]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  -- the class filters on `B`
  have hfilt1 : (B.filter (fun d => runit7 d = s')).image (qdig7 m) = X1 := by
    have hf : B.filter (fun d => runit7 d = s')
        = A1.image (fun d => lam₁ * d) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨hB, hr⟩
        obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hB
        rw [runit7_mul, hs'] at hr
        have hrd : runit7 d = s := mul_left_cancel₀ hrl1 hr
        rcases Finset.mem_union.mp hd with hd₁ | hd₂
        · exact ⟨d, hd₁, rfl⟩
        · rw [hcls2 d hd₂] at hrd
          exact absurd (by linear_combination hrd) hs
      · rintro ⟨d, hd₁, rfl⟩
        exact ⟨Finset.mem_image.mpr ⟨d, Finset.mem_union_left _ hd₁, rfl⟩,
          by rw [runit7_mul, hcls1 d hd₁, hs']⟩
    rw [hf]
  have hfilt2 : (B.filter (fun d => runit7 d = 2 * s')).image (qdig7 m) = X2 := by
    have hf : B.filter (fun d => runit7 d = 2 * s')
        = A2.image (fun d => lam₁ * d) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨hB, hr⟩
        obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hB
        rw [runit7_mul, hs'] at hr
        have hrd : runit7 d = 2 * s := by
          have hr' : runit7 lam₁ * runit7 d = runit7 lam₁ * (2 * s) := by
            rw [hr]; ring
          exact mul_left_cancel₀ hrl1 hr'
        rcases Finset.mem_union.mp hd with hd₁ | hd₂
        · rw [hcls1 d hd₁] at hrd
          exact absurd (by linear_combination -hrd) hs
        · exact ⟨d, hd₂, rfl⟩
      · rintro ⟨d, hd₂, rfl⟩
        exact ⟨Finset.mem_image.mpr ⟨d, Finset.mem_union_right _ hd₂, rfl⟩,
          by rw [runit7_mul, hcls2 d hd₂, hs']; ring⟩
    rw [hf]
  have hfilt4 : (B.filter (fun d => runit7 d = 4 * s')).image (qdig7 m)
      = (∅ : Finset (ZMod 7)) := by
    have hf : B.filter (fun d => runit7 d = 4 * s') = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro x hxB hxr
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hxB
      rw [runit7_mul, hs'] at hxr
      have hrd : runit7 d = 4 * s := by
        have hr' : runit7 lam₁ * runit7 d = runit7 lam₁ * (4 * s) := by
          rw [hxr]; ring
        exact mul_left_cancel₀ hrl1 hr'
      rcases Finset.mem_union.mp hd with hd₁ | hd₂
      · rw [hcls1 d hd₁] at hrd
        have hz : (3 : ZMod 7) * s = 0 := by linear_combination -hrd
        rcases mul_eq_zero.mp hz with h3 | h0
        · exact absurd h3 (by decide)
        · exact hs h0
      · rw [hcls2 d hd₂] at hrd
        have hz : (2 : ZMod 7) * s = 0 := by linear_combination -hrd
        rcases mul_eq_zero.mp hz with h2 | h0
        · exact absurd h2 (by decide)
        · exact hs h0
    rw [hf, Finset.image_empty]
  have e1 : X1.image (· + (t + k)) = Y1.image (· + k) := by
    rw [hY1]
    conv_rhs => rw [Finset.image_image]
    apply Finset.image_congr
    intro x _
    show x + (t + k) = x + t + k
    ring
  have e2 : X2.image (· + 2 * (t + k)) = Y2.image (· + 2 * k) := by
    rw [hY2]
    conv_rhs => rw [Finset.image_image]
    apply Finset.image_congr
    intro x _
    show x + 2 * (t + k) = x + 2 * t + 2 * k
    ring
  have hunion :
      ((B.filter fun d => runit7 d = s').image (qdig7 m)).image (· + (t + k))
        ∪ ((B.filter fun d => runit7 d = 2 * s').image (qdig7 m)).image
          (· + 2 * (t + k))
        ∪ ((B.filter fun d => runit7 d = 4 * s').image (qdig7 m)).image
          (· + 4 * (t + k))
        = Y1.image (· + k) ∪ Y2.image (· + 2 * k) := by
    rw [hfilt1, hfilt2, hfilt4, Finset.image_empty, Finset.union_empty]
    rw [e1, e2]
  obtain ⟨lam0, hlam0mem, hgood0⟩ :=
    exists_lambda0_of_shift hm hs'0 hunitB hclsB (t + k)
      (hunion.symm ▸ havoid)
  refine ⟨lam0 * lam₁,
    Nat.prime_seven.not_dvd_mul (not_dvd_of_mem_multLow7_zero hm hlam0mem)
      hlam₁, ?_⟩
  exact good7_mul hgood0

/-- The `ℓ ≤ 3` entry point: obtain a cover `cycIv i' ℓ` with `i'` an
element of `X₁` via `min_cover_mem`, then apply `case64_tail`. -/
private theorem case64_finish3 {m : ℕ} (hm : 0 < m) {A1 A2 : Finset ℕ}
    (hpos : ∀ d ∈ A1 ∪ A2, 0 < d)
    (hunit : ∀ d ∈ A1 ∪ A2, padicValNat 7 d = 0)
    {s : ZMod 7} (hs : s ≠ 0)
    (hcls1 : ∀ d ∈ A1, runit7 d = s)
    (hcls2 : ∀ d ∈ A2, runit7 d = 2 * s)
    (hA2 : A2.card = 2) (hne : A1.Nonempty)
    {lam₁ : ℕ} (hlam₁ : ¬ 7 ∣ lam₁)
    (h3 : apLen ((A1.image (fun d => lam₁ * d)).image (qdig7 m)) ≤ 3) :
    ∃ lam : ℕ, ¬ 7 ∣ lam ∧ good7 m lam (A1 ∪ A2) := by
  classical
  set X1 := (A1.image (fun d => lam₁ * d)).image (qdig7 m) with hX1
  have hX1ne : X1.Nonempty := by
    rw [hX1]
    exact Finset.Nonempty.image
      (Finset.Nonempty.image hne _) _
  obtain ⟨i, hi⟩ := (apLen_le_iff X1 (apLen X1) (apLen_le7' X1)).mp le_rfl
  obtain ⟨i', hi'mem, hi'sub⟩ := min_cover_mem hX1ne hi
  exact case64_tail hm hpos hunit hs hcls1 hcls2 hA2 hlam₁ hi'mem hi'sub
    (Or.inl h3)

/-- The `ℓ = 4` ratio-3 entry point: `q(λ₁A₁) = {Q, Q+u, Q+3u}` (`u ≠ 0`),
the anchor is `d₃` for `u ∈ {1,3}`, `d₂` for `u ∈ {4,5}`, `d₁` for
`u ∈ {2,6}`, and the `ẽ`-condition holds for `d' ∈ A₂`. -/
private theorem case64_finish4 {m : ℕ} (hm : 0 < m) {A1 A2 : Finset ℕ}
    (hpos : ∀ d ∈ A1 ∪ A2, 0 < d)
    (hunit : ∀ d ∈ A1 ∪ A2, padicValNat 7 d = 0)
    {s : ZMod 7} (hs : s ≠ 0)
    (hcls1 : ∀ d ∈ A1, runit7 d = s)
    (hcls2 : ∀ d ∈ A2, runit7 d = 2 * s)
    (hA2 : A2.card = 2)
    {d1 d2 d3 : ℕ} (hd1 : d1 ∈ A1) (hd2 : d2 ∈ A1) (hd3 : d3 ∈ A1)
    (hA1eq : A1 = {d1, d2, d3})
    {lam₁ : ℕ} (hlam₁ : ¬ 7 ∣ lam₁)
    {u : ZMod 7} (hu : u ≠ 0)
    (hq2 : qdig7 m (lam₁ * d2) = qdig7 m (lam₁ * d3) + u)
    (hq1 : qdig7 m (lam₁ * d1) = qdig7 m (lam₁ * d3) + 3 * u)
    {anchor : ℕ}
    (hmatch : (anchor = d3 ∧ u ∈ ({1, 3} : Finset (ZMod 7))) ∨
      (anchor = d2 ∧ u ∈ ({4, 5} : Finset (ZMod 7))) ∨
      (anchor = d1 ∧ u ∈ ({2, 6} : Finset (ZMod 7))))
    {d' : ℕ} (hd' : d' ∈ A2)
    (hcond : etd7 m (lam₁ * anchor) (lam₁ * d')
        ∈ ({0, 1, 6} : Finset (ZMod 7))) :
    ∃ lam : ℕ, ¬ 7 ∣ lam ∧ good7 m lam (A1 ∪ A2) := by
  classical
  set Q := qdig7 m (lam₁ * d3) with hQ
  have hA : anchor ∈ A1 := by
    rcases hmatch with ⟨ha, _⟩ | ⟨ha, _⟩ | ⟨ha, _⟩ <;> subst ha
    · exact hd3
    · exact hd2
    · exact hd1
  have hX1 : (A1.image (fun d => lam₁ * d)).image (qdig7 m)
      = ({Q + 3 * u, Q + u, Q} : Finset (ZMod 7)) := by
    simp only [hA1eq, Finset.image_insert, Finset.image_singleton, hq1, hq2,
      ← hQ]
  have hap4 : apLen ((A1.image (fun d => lam₁ * d)).image (qdig7 m)) = 4 := by
    rw [hX1]
    exact apLen_03u Q u hu
  -- `ẽ` unfolds to `2q(anchor) − q(d')` for the `twoX` pair
  have hA4 : ∀ d ∈ A2, runit7 (lam₁ * d) = 2 * runit7 (lam₁ * anchor) := by
    intro d hd
    rw [runit7_mul, runit7_mul, hcls2 d hd, hcls1 anchor hA]
    ring
  have hcond' : (2 * qdig7 m (lam₁ * anchor) - qdig7 m (lam₁ * d') : ZMod 7)
      ∈ ({0, 1, 6} : Finset (ZMod 7)) := by
    have h : etd7 m (lam₁ * anchor) (lam₁ * d')
        = 2 * qdig7 m (lam₁ * anchor) - qdig7 m (lam₁ * d') := by
      unfold etd7
      rw [if_pos (hA4 d' hd')]
    rwa [h] at hcond
  rcases hmatch with ⟨ha, hu'⟩ | ⟨ha, hu'⟩ | ⟨ha, hu'⟩ <;> subst ha
  · -- anchor `d₃`, interval start `Q`
    refine case64_tail hm hpos hunit hs hcls1 hcls2 hA2 hlam₁
      (Finset.mem_image.mpr ⟨lam₁ * anchor,
        Finset.mem_image.mpr ⟨anchor, hd3, rfl⟩, rfl⟩) ?_
      (Or.inr ⟨hap4, d', hd', hcond'⟩)
    rw [hap4, hX1]
    exact c64_cover_a Q u hu'
  · -- anchor `d₂`, interval start `Q + u`
    have hi : qdig7 m (lam₁ * anchor) = Q + u := hq2
    refine case64_tail hm hpos hunit hs hcls1 hcls2 hA2 hlam₁
      (Finset.mem_image.mpr ⟨lam₁ * anchor,
        Finset.mem_image.mpr ⟨anchor, hd2, rfl⟩, rfl⟩) ?_
      (Or.inr ⟨hap4, d', hd', hcond'⟩)
    rw [hap4, hX1, hi]
    exact c64_cover_b Q u hu'
  · -- anchor `d₁`, interval start `Q + 3u`
    have hi : qdig7 m (lam₁ * anchor) = Q + 3 * u := hq1
    refine case64_tail hm hpos hunit hs hcls1 hcls2 hA2 hlam₁
      (Finset.mem_image.mpr ⟨lam₁ * anchor,
        Finset.mem_image.mpr ⟨anchor, hd1, rfl⟩, rfl⟩) ?_
      (Or.inr ⟨hap4, d', hd', hcond'⟩)
    rw [hap4, hX1, hi]
    exact c64_cover_c Q u hu'

/-! ### The main theorem -/

/-- **§6.4** (Barajas–Serra): `|A₁| = 3` in class `s ∈ {1,2,4}`,
`|A₂| = 2` in class `2s` — a `7`-unit `λ` is `good7` on `A₁ ∪ A₂`. -/
theorem case64 {m : ℕ} (hm : 2 ≤ m) {A1 A2 : Finset ℕ} (hA1 : A1.card = 3)
    (hA2 : A2.card = 2) (hpos : ∀ d ∈ A1 ∪ A2, 0 < d)
    (hunit : ∀ d ∈ A1 ∪ A2, padicValNat 7 d = 0)
    {s : ZMod 7} (hs : s ∈ ({1, 2, 4} : Finset (ZMod 7)))
    (hcls1 : ∀ d ∈ A1, runit7 d = s)
    (hcls2 : ∀ d ∈ A2, runit7 d = 2 * s) :
    ∃ lam : ℕ, ¬ 7 ∣ lam ∧ good7 m lam (A1 ∪ A2) := by
  classical
  have hm0 : 0 < m := by omega
  have hs0 : s ≠ 0 := by
    intro h0
    rw [h0] at hs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with h | h | h <;> exact absurd h (by decide)
  have hpos1 : ∀ d ∈ A1, 0 < d :=
    fun d hd => hpos d (Finset.mem_union_left _ hd)
  have hunit1 : ∀ d ∈ A1, padicValNat 7 d = 0 :=
    fun d hd => hunit d (Finset.mem_union_left _ hd)
  have hpos2 : ∀ d ∈ A2, 0 < d :=
    fun d hd => hpos d (Finset.mem_union_right _ hd)
  have hunit2 : ∀ d ∈ A2, padicValNat 7 d = 0 :=
    fun d hd => hunit d (Finset.mem_union_right _ hd)
  have hA1ne : A1.Nonempty :=
    Finset.card_pos.mp (by rw [hA1]; norm_num)
  obtain ⟨d1, hd1, d2, hd2, d3, hd3, hA1eq, hdis⟩ :=
    lemma11 (m := m) hA1 s hpos1 hunit1 hcls1
  obtain ⟨d4, d5, hd45, hA2eq⟩ := Finset.card_eq_two.mp hA2
  have hd4 : d4 ∈ A2 := by rw [hA2eq]; exact Finset.mem_insert_self _ _
  have hd5 : d5 ∈ A2 := by
    rw [hA2eq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hp1 := hpos1 d1 hd1; have hp2 := hpos1 d2 hd2; have hp3 := hpos1 d3 hd3
  have hu1 := hunit1 d1 hd1; have hu2 := hunit1 d2 hd2; have hu3 := hunit1 d3 hd3
  have hp4 := hpos2 d4 hd4; have hu4 := hunit2 d4 hd4
  have hr1 := hcls1 d1 hd1; have hr2 := hcls1 d2 hd2; have hr3 := hcls1 d3 hd3
  have hr4 := hcls2 d4 hd4
  have hrel23 : residueRelOf d2 d3 = residueRel.same :=
    rel_same (by rw [hr2, hr3]) (by rw [hr3]; exact hs0)
  have hrel13 : residueRelOf d1 d3 = residueRel.same :=
    rel_same (by rw [hr1, hr3]) (by rw [hr3]; exact hs0)
  -- twoX hypotheses for `d₄` against each `A₁` element
  have ht34 : runit7 d4 = 2 * runit7 d3 := by rw [hr4, hr3]
  have ht24 : runit7 d4 = 2 * runit7 d2 := by rw [hr4, hr2]
  have ht14 : runit7 d4 = 2 * runit7 d1 := by rw [hr4, hr1]
  rcases hdis with ⟨hlgt, hleq⟩ | ⟨hlevel, hratios⟩
  · /- case (i): `ℓ₁₃ > ℓ₂₃ = ℓ₁₂` -/
    have h13le : elevel7 m d1 d3 ≤ m + 1 := elevel7_le
    have hl23 : elevel7 m d2 d3 ≤ m := by omega
    have he23 : eMod7 m d2 d3 ≠ 0 := by
      intro h0
      rw [elevel7_of_eq h0] at hl23
      omega
    by_cases he13 : eMod7 m d1 d3 = 0
    · -- `e₁₃ = 0`: `q(d₁) = q(d₃)`, collapse to two points
      have hq13 : qdig7 m d1 = qdig7 m d3 :=
        qdig7_congr (eq_resid_of_eMod7_eq_zero he13 hrel13)
      have hν23 : padicValNat 7 (eMod7 m d2 d3) = elevel7 m d2 d3 :=
        (elevel7_of_ne he23).symm
      by_cases hlm : padicValNat 7 (eMod7 m d2 d3) < m
      · -- `Λ_{ν₂₃}` with `q(λe₂₃) = 0`: `q₂' − q₃' ∈ {0,1}`
        obtain ⟨k, hk7, hkq⟩ := exists_multLow_set_qdig hlm rfl he23 0
        set lam₁ := 1 + k * 7 ^ (m - padicValNat 7 (eMod7 m d2 d3)) with hlam₁
        have hlam₁r : runit7 lam₁ = 1 := runit7_multLow hlm
        have hlam₁7 : ¬ 7 ∣ lam₁ := multLow_not_dvd hlm
        have hsc : ∀ d : ℕ, runit7 (lam₁ * d) = runit7 d :=
          fun d => by rw [runit7_mul, hlam₁r, one_mul]
        have hrel13' : residueRelOf (lam₁ * d1) (lam₁ * d3)
            = residueRel.same :=
          rel_same (by rw [hsc d1, hsc d3, hr1, hr3])
            (by rw [hsc d3, hr3]; exact hs0)
        have hrel23' : residueRelOf (lam₁ * d2) (lam₁ * d3)
            = residueRel.same :=
          rel_same (by rw [hsc d2, hsc d3, hr2, hr3])
            (by rw [hsc d3, hr3]; exact hs0)
        have he13' : eMod7 m (lam₁ * d1) (lam₁ * d3) = 0 := by
          rw [eMod7_mul hlam₁r, he13, mul_zero, Nat.zero_mod]
        have hq13' : qdig7 m (lam₁ * d1) = qdig7 m (lam₁ * d3) :=
          qdig7_congr (eq_resid_of_eMod7_eq_zero he13' hrel13')
        have hqe : qdig7 m (eMod7 m (lam₁ * d2) (lam₁ * d3)) = 0 := by
          rw [eMod7_mul hlam₁r, qdig7_congr (Nat.mod_mod _ _)]
          exact hkq
        have hb := qdig_eMod_sub (m := m) hrel23'
        rw [hqe] at hb
        simp only [Finset.mem_insert, Finset.mem_singleton] at hb
        have hdiff : qdig7 m (lam₁ * d2) - qdig7 m (lam₁ * d3)
            ∈ ({0, 1} : Finset (ZMod 7)) := by
          simp only [Finset.mem_insert, Finset.mem_singleton]
          rcases hb with hb0 | hb6
          · left
            have : qdig7 m (lam₁ * d2) - qdig7 m (lam₁ * d3) = 0 := by
              linear_combination -hb0
            exact this
          · right
            have : qdig7 m (lam₁ * d2) - qdig7 m (lam₁ * d3) = -6 := by
              linear_combination -hb6
            rw [this]; decide
        have hsub : (A1.image (fun d => lam₁ * d)).image (qdig7 m)
            ⊆ cycIv (qdig7 m (lam₁ * d3)) 2 := by
          intro x hx
          obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
          obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hy
          rw [hA1eq] at hd
          simp only [Finset.mem_insert, Finset.mem_singleton] at hd
          rcases hd with rfl | rfl | rfl
          · rw [mem_cycIv, hq13']; simp
          · rw [mem_cycIv]
            simp only [Finset.mem_insert, Finset.mem_singleton] at hdiff
            rcases hdiff with h0 | h1
            · rw [h0]; simp
            · rw [h1]; decide
          · rw [mem_cycIv]; simp
        have hap : apLen ((A1.image (fun d => lam₁ * d)).image (qdig7 m))
            ≤ 2 := (apLen_le_iff _ 2 (by norm_num)).mpr ⟨_, hsub⟩
        exact case64_finish3 hm0 hpos hunit hs0 hcls1 hcls2 hA2 hA1ne hlam₁7
          (le_trans hap (by norm_num))
      · -- `ν(e₂₃) = m`: normalize `e₂₃ ↦ 7^m`
        have hν23m : padicValNat 7 (eMod7 m d2 d3) = m := by
          have := enu7_le_of_ne he23
          omega
        obtain ⟨c, hc0, hc7, hce, hqc⟩ := exists_top_scalar_set hν23m he23
          (by decide : (1 : ZMod 7) ≠ 0)
        have hcl : ¬ (7 : ℕ) ∣ c :=
          fun h => absurd (Nat.le_of_dvd hc0 h) (by omega)
        have hrcast : runit7 c = (c : ZMod 7) :=
          runit7_of_padic_zero (padicValNat.eq_zero_of_not_dvd hcl)
        have hc0z : (c : ZMod 7) ≠ 0 := by
          intro hcon
          have hdvd : 7 ∣ c := (ZMod.natCast_eq_zero_iff c 7).mp hcon
          exact absurd (Nat.le_of_dvd hc0 hdvd) (by omega)
        have hrc : runit7 c ≠ 0 := by rwa [hrcast]
        have hsc : ∀ d : ℕ, runit7 (c * d) = (c : ZMod 7) * runit7 d :=
          fun d => by rw [runit7_mul, hrcast]
        have hrel13' : residueRelOf (c * d1) (c * d3) = residueRel.same :=
          rel_same (by rw [hsc d1, hsc d3, hr1, hr3])
            (by rw [hsc d3, hr3]; exact mul_ne_zero hc0z hs0)
        have hrel23' : residueRelOf (c * d2) (c * d3) = residueRel.same :=
          rel_same (by rw [hsc d2, hsc d3, hr2, hr3])
            (by rw [hsc d3, hr3]; exact mul_ne_zero hc0z hs0)
        have he13' : eMod7 m (c * d1) (c * d3) = 0 := by
          rw [eMod7_smul hrc, he13, mul_zero, Nat.zero_mod]
        have hq13' : qdig7 m (c * d1) = qdig7 m (c * d3) :=
          qdig7_congr (eq_resid_of_eMod7_eq_zero he13' hrel13')
        have he23' : eMod7 m (c * d2) (c * d3)
            = (1 : ZMod 7).val * 7 ^ m := by
          rw [eMod7_smul hrc]; exact hce
        have hq23' : qdig7 m (c * d2) = qdig7 m (c * d3) + 1 :=
          qdig_eq_add_of_e_top hrel23' he23'
        have hsub : (A1.image (fun d => c * d)).image (qdig7 m)
            ⊆ cycIv (qdig7 m (c * d3)) 2 := by
          intro x hx
          obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
          obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hy
          rw [hA1eq] at hd
          simp only [Finset.mem_insert, Finset.mem_singleton] at hd
          rcases hd with rfl | rfl | rfl
          · rw [mem_cycIv, hq13']; simp
          · rw [mem_cycIv, hq23', add_sub_cancel_left]; decide
          · rw [mem_cycIv]; simp
        have hap : apLen ((A1.image (fun d => c * d)).image (qdig7 m))
            ≤ 2 := (apLen_le_iff _ 2 (by norm_num)).mpr ⟨_, hsub⟩
        exact case64_finish3 hm0 hpos hunit hs0 hcls1 hcls2 hA2 hA1ne hcl
          (le_trans hap (by norm_num))
    · -- `e₁₃ ≠ 0`: distinct levels, `lemma9_i'` gives `ℓ ≤ 2`
      have hν13 : padicValNat 7 (eMod7 m d1 d3) = elevel7 m d1 d3 :=
        (elevel7_of_ne he13).symm
      have hν23 : padicValNat 7 (eMod7 m d2 d3) = elevel7 m d2 d3 :=
        (elevel7_of_ne he23).symm
      have hνne : padicValNat 7 (eMod7 m d1 d3)
          ≠ padicValNat 7 (eMod7 m d2 d3) := by
        rw [hν13, hν23]
        exact ne_of_gt hlgt
      obtain ⟨lam, hlam7, _hpair, hlen⟩ :=
        lemma9_i' ⟨hp1, hp2, hp3⟩ ⟨hu1, hu2, hu3⟩
          ⟨hr1.trans hr2.symm, hr2.trans hr3.symm⟩ hνne ⟨he13, he23⟩
      have himg : (A1.image (fun d => lam * d)).image (qdig7 m)
          = ({d1, d2, d3} : Finset ℕ).image
            (fun d => qdig7 m (lam * d)) := by
        rw [hA1eq]
        ext x
        simp only [Finset.mem_image]
        constructor
        · rintro ⟨y, hy, rfl⟩
          obtain ⟨d, hd, rfl⟩ := hy
          exact ⟨d, hd, rfl⟩
        · rintro ⟨d, hd, rfl⟩
          exact ⟨lam * d, ⟨d, hd, rfl⟩, rfl⟩
      have h3 : apLen ((A1.image (fun d => lam * d)).image (qdig7 m))
          ≤ 3 := by
        rw [himg]
        exact le_trans hlen (by norm_num)
      exact case64_finish3 hm0 hpos hunit hs0 hcls1 hcls2 hA2 hA1ne hlam7 h3
  · /- case (ii): `ℓ₁₃ = ℓ₂₃`, ratio `2` or `3` -/
    by_cases he23z : eMod7 m d2 d3 = 0
    · -- `e₂₃ = 0` ⇒ `e₁₃ = 0` (same level): all three digits collapse
      have he13z : eMod7 m d1 d3 = 0 :=
        elevel7_eq_succ.mp (hlevel.trans (elevel7_of_eq he23z))
      have hq13 : qdig7 m d1 = qdig7 m d3 :=
        qdig7_congr (eq_resid_of_eMod7_eq_zero he13z hrel13)
      have hq23 : qdig7 m d2 = qdig7 m d3 :=
        qdig7_congr (eq_resid_of_eMod7_eq_zero he23z hrel23)
      have hsub : (A1.image (fun d => 1 * d)).image (qdig7 m)
          ⊆ cycIv (qdig7 m (1 * d3)) 1 := by
        intro x hx
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
        obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hy
        rw [hA1eq] at hd
        simp only [Finset.mem_insert, Finset.mem_singleton] at hd
        rcases hd with rfl | rfl | rfl
        · rw [mem_cycIv, one_mul, one_mul, hq13]; simp
        · rw [mem_cycIv, one_mul, one_mul, hq23]; simp
        · rw [mem_cycIv]; simp
      have hap : apLen ((A1.image (fun d => 1 * d)).image (qdig7 m)) ≤ 1 :=
        (apLen_le_iff _ 1 (by norm_num)).mpr ⟨_, hsub⟩
      exact case64_finish3 hm0 hpos hunit hs0 hcls1 hcls2 hA2 hA1ne
        (by decide) (le_trans hap (by norm_num))
    · -- `e₂₃ ≠ 0` ⇒ `e₁₃ ≠ 0` (ratio is a unit multiple)
      have he23 := he23z
      have he13 : eMod7 m d1 d3 ≠ 0 := by
        intro h0
        have hr23 : runit7 (eMod7 m d2 d3) ≠ 0 :=
          runit7_ne_zero (Nat.pos_of_ne_zero he23)
        rcases hratios with h2 | ⟨h3, _⟩
        · rw [h0, runit7_zero] at h2
          rcases mul_eq_zero.mp h2.symm with hz | hz
          · exact absurd hz (by decide)
          · exact hr23 hz
        · rw [h0, runit7_zero] at h3
          rcases mul_eq_zero.mp h3.symm with hz | hz
          · exact absurd hz (by decide)
          · exact hr23 hz
      have hν13 : padicValNat 7 (eMod7 m d1 d3) = elevel7 m d1 d3 :=
        (elevel7_of_ne he13).symm
      have hν23 : padicValNat 7 (eMod7 m d2 d3) = elevel7 m d2 d3 :=
        (elevel7_of_ne he23).symm
      have hνeq : padicValNat 7 (eMod7 m d1 d3)
          = padicValNat 7 (eMod7 m d2 d3) := by
        rw [hν13, hν23]; exact hlevel
      have hνle : padicValNat 7 (eMod7 m d2 d3) ≤ m := enu7_le_of_ne he23
      by_cases hlm : padicValNat 7 (eMod7 m d2 d3) < m
      · -- `h < m`: `lemma9_ii` on the swap `(d₂, d₁, d₃)`
        obtain ⟨j, hj, hrj⟩ :
            ∃ j : ℕ, (j = 2 ∨ j = 3) ∧ runit7 (eMod7 m d1 d3)
              = (j : ZMod 7) * runit7 (eMod7 m d2 d3) := by
          rcases hratios with h2 | ⟨h3, _⟩
          · exact ⟨2, Or.inl rfl, by simpa using h2⟩
          · exact ⟨3, Or.inr rfl, by simpa using h3⟩
        obtain ⟨lam, hlam7, _h1, _h2, _h3, hlen⟩ :=
          lemma9_ii ⟨hp2, hp1, hp3⟩ ⟨hu2, hu1, hu3⟩
            ⟨hr2.trans hr1.symm, hr1.trans hr3.symm⟩ hνeq.symm
            (by rwa [hνeq]) hj hrj
        have hset : ({d2, d1, d3} : Finset ℕ) = ({d1, d2, d3} : Finset ℕ) :=
          (Finset.insert_comm d1 d2 {d3}).symm
        rw [hset] at hlen
        have himg : (A1.image (fun d => lam * d)).image (qdig7 m)
            = ({d1, d2, d3} : Finset ℕ).image
              (fun d => qdig7 m (lam * d)) := by
          rw [hA1eq]
          ext x
          simp only [Finset.mem_image]
          constructor
          · rintro ⟨y, hy, rfl⟩
            obtain ⟨d, hd, rfl⟩ := hy
            exact ⟨d, hd, rfl⟩
          · rintro ⟨d, hd, rfl⟩
            exact ⟨lam * d, ⟨d, hd, rfl⟩, rfl⟩
        have h3 : apLen ((A1.image (fun d => lam * d)).image (qdig7 m))
            ≤ 3 := by
          rw [himg]
          exact le_trans hlen (by rcases hj with rfl | rfl <;> norm_num)
        exact case64_finish3 hm0 hpos hunit hs0 hcls1 hcls2 hA2 hA1ne hlam7 h3
      · -- `h = m`: pure-top normalization `e₂₃ ↦ 7^m`
        have hν23m : padicValNat 7 (eMod7 m d2 d3) = m :=
          le_antisymm hνle (by omega)
        have hν13m : padicValNat 7 (eMod7 m d1 d3) = m := by
          rw [hνeq]; exact hν23m
        obtain ⟨c, hc0, hc7, hce, hqc⟩ := exists_top_scalar_set hν23m he23
          (by decide : (1 : ZMod 7) ≠ 0)
        have hcl : ¬ (7 : ℕ) ∣ c :=
          fun h => absurd (Nat.le_of_dvd hc0 h) (by omega)
        have hrcast : runit7 c = (c : ZMod 7) :=
          runit7_of_padic_zero (padicValNat.eq_zero_of_not_dvd hcl)
        have hc0z : (c : ZMod 7) ≠ 0 := by
          intro hcon
          have hdvd : 7 ∣ c := (ZMod.natCast_eq_zero_iff c 7).mp hcon
          exact absurd (Nat.le_of_dvd hc0 hdvd) (by omega)
        have hrc : runit7 c ≠ 0 := by rwa [hrcast]
        have hsc : ∀ d : ℕ, runit7 (c * d) = (c : ZMod 7) * runit7 d :=
          fun d => by rw [runit7_mul, hrcast]
        have hrel13' : residueRelOf (c * d1) (c * d3) = residueRel.same :=
          rel_same (by rw [hsc d1, hsc d3, hr1, hr3])
            (by rw [hsc d3, hr3]; exact mul_ne_zero hc0z hs0)
        have hrel23' : residueRelOf (c * d2) (c * d3) = residueRel.same :=
          rel_same (by rw [hsc d2, hsc d3, hr2, hr3])
            (by rw [hsc d3, hr3]; exact mul_ne_zero hc0z hs0)
        have he23top : eMod7 m d2 d3
            = (runit7 (eMod7 m d2 d3)).val * 7 ^ m := by
          have h := residN_top hν23m
          rwa [qdig7_eq_runit7_of_top hν23m,
            Nat.mod_eq_of_lt (eMod7_lt _ _ _)] at h
        have hca : (c : ZMod 7) * runit7 (eMod7 m d2 d3) = 1 := by
          have h := qdig7_multTop (l := c) hν23m
          rw [hqc] at h
          exact h.symm
        rcases hratios with hrat2 | ⟨hrat3, _⟩
        · -- ratio 2: `e₁₃ ↦ 2·7^m`, `X₁ ⊆ cycIv Q 3`
          have he13top : eMod7 m d1 d3
              = ((2 : ZMod 7) * runit7 (eMod7 m d2 d3)).val * 7 ^ m := by
            have h := residN_top hν13m
            rwa [qdig7_eq_runit7_of_top hν13m,
              Nat.mod_eq_of_lt (eMod7_lt _ _ _), hrat2] at h
          have he23c : eMod7 m (c * d2) (c * d3)
              = (1 : ZMod 7).val * 7 ^ m := by
            rw [e_smul_top hrc he23top, hca]
          have he13c : eMod7 m (c * d1) (c * d3)
              = (2 : ZMod 7).val * 7 ^ m := by
            have h2a : (c : ZMod 7) *
                ((2 : ZMod 7) * runit7 (eMod7 m d2 d3)) = 2 := by
              linear_combination 2 * hca
            rw [e_smul_top hrc he13top, h2a]
          have hq23c : qdig7 m (c * d2) = qdig7 m (c * d3) + 1 :=
            qdig_eq_add_of_e_top hrel23' he23c
          have hq13c : qdig7 m (c * d1) = qdig7 m (c * d3) + 2 :=
            qdig_eq_add_of_e_top hrel13' he13c
          have hsub : (A1.image (fun d => c * d)).image (qdig7 m)
              ⊆ cycIv (qdig7 m (c * d3)) 3 := by
            intro x hx
            obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
            obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hy
            rw [hA1eq] at hd
            simp only [Finset.mem_insert, Finset.mem_singleton] at hd
            rcases hd with rfl | rfl | rfl
            · rw [mem_cycIv, hq13c, add_sub_cancel_left]; decide
            · rw [mem_cycIv, hq23c, add_sub_cancel_left]; decide
            · rw [mem_cycIv]; simp
          have hap : apLen ((A1.image (fun d => c * d)).image (qdig7 m))
              ≤ 3 := (apLen_le_iff _ 3 (by norm_num)).mpr ⟨_, hsub⟩
          exact case64_finish3 hm0 hpos hunit hs0 hcls1 hcls2 hA2 hA1ne
            hcl hap
        · -- ratio 3: `e₁₃ ↦ 3·7^m`; finish via `case64_finish4`
          have he13top : eMod7 m d1 d3
              = ((3 : ZMod 7) * runit7 (eMod7 m d2 d3)).val * 7 ^ m := by
            have h := residN_top hν13m
            rwa [qdig7_eq_runit7_of_top hν13m,
              Nat.mod_eq_of_lt (eMod7_lt _ _ _), hrat3] at h
          have he23c : eMod7 m (c * d2) (c * d3)
              = (1 : ZMod 7).val * 7 ^ m := by
            rw [e_smul_top hrc he23top, hca]
          have he13c : eMod7 m (c * d1) (c * d3)
              = (3 : ZMod 7).val * 7 ^ m := by
            have h3a : (c : ZMod 7) *
                ((3 : ZMod 7) * runit7 (eMod7 m d2 d3)) = 3 := by
              linear_combination 3 * hca
            rw [e_smul_top hrc he13top, h3a]
          -- `Λⱼ` (`j < m`) preserves the normalized pure-top pair on `A₁`
          have hq23L : ∀ j k : ℕ, j < m →
              eMod7 m ((1 + k * 7 ^ (m - j)) * c * d2)
                ((1 + k * 7 ^ (m - j)) * c * d3)
                = (1 : ZMod 7).val * 7 ^ m := by
            intro j k hjm
            have hlam₂r : runit7 (1 + k * 7 ^ (m - j)) = 1 :=
              runit7_multLow hjm
            rw [mul_assoc, mul_assoc, eMod7_mul hlam₂r, he23c]
            exact top_resid_multLow hjm (by decide : (1 : ZMod 7) ≠ 0)
          have hq13L : ∀ j k : ℕ, j < m →
              eMod7 m ((1 + k * 7 ^ (m - j)) * c * d1)
                ((1 + k * 7 ^ (m - j)) * c * d3)
                = (3 : ZMod 7).val * 7 ^ m := by
            intro j k hjm
            have hlam₂r : runit7 (1 + k * 7 ^ (m - j)) = 1 :=
              runit7_multLow hjm
            rw [mul_assoc, mul_assoc, eMod7_mul hlam₂r, he13c]
            exact top_resid_multLow hjm (by decide : (3 : ZMod 7) ≠ 0)
          have hrel23L : ∀ j k : ℕ, j < m →
              residueRelOf ((1 + k * 7 ^ (m - j)) * c * d2)
                ((1 + k * 7 ^ (m - j)) * c * d3) = residueRel.same := by
            intro j k hjm
            apply rel_same
            · rw [runit7_mul, runit7_mul, runit7_mul, runit7_mul,
                runit7_multLow hjm, hrcast, hr2, hr3]
            · rw [runit7_mul, runit7_mul,
                runit7_multLow hjm, one_mul, hrcast, hr3]
              exact mul_ne_zero hc0z hs0
          have hrel13L : ∀ j k : ℕ, j < m →
              residueRelOf ((1 + k * 7 ^ (m - j)) * c * d1)
                ((1 + k * 7 ^ (m - j)) * c * d3) = residueRel.same := by
            intro j k hjm
            apply rel_same
            · rw [runit7_mul, runit7_mul, runit7_mul, runit7_mul,
                runit7_multLow hjm, hrcast, hr1, hr3]
            · rw [runit7_mul, runit7_mul,
                runit7_multLow hjm, one_mul, hrcast, hr3]
              exact mul_ne_zero hc0z hs0
          by_cases h34m : padicValNat 7 (eMod7 m d3 d4) = m
          · -- `ν(e₃₄) = m`: `c64_choice` scalar `c₂ = (u·r(e₂₃)⁻¹).val`
            have he34ne : eMod7 m d3 d4 ≠ 0 := by
              intro h0
              rw [h0, padicValNat.zero] at h34m
              omega
            have he34top : eMod7 m d3 d4
                = (runit7 (eMod7 m d3 d4)).val * 7 ^ m := by
              have h := residN_top h34m
              rwa [qdig7_eq_runit7_of_top h34m,
                Nat.mod_eq_of_lt (eMod7_lt _ _ _)] at h
            have ha0 : runit7 (eMod7 m d2 d3) ≠ 0 :=
              runit7_ne_zero (Nat.pos_of_ne_zero he23)
            have hb0 : runit7 (eMod7 m d3 d4) ≠ 0 :=
              runit7_ne_zero (Nat.pos_of_ne_zero he34ne)
            set B : ZMod 7 := runit7 (eMod7 m d3 d4) *
              (runit7 (eMod7 m d2 d3))⁻¹ with hB
            have hB0 : B ≠ 0 := by
              rw [hB]; exact mul_ne_zero hb0 (inv_ne_zero ha0)
            obtain ⟨u, hdisj⟩ := c64_choice B hB0
            have hu0 : u ≠ 0 := by
              rcases hdisj with ⟨hu', _⟩ | ⟨hu', _⟩ | ⟨hu', _⟩ <;>
                simp only [Finset.mem_insert, Finset.mem_singleton] at hu' <;>
                rcases hu' with rfl | rfl <;> decide
            have hua0 : u * (runit7 (eMod7 m d2 d3))⁻¹ ≠ 0 :=
              mul_ne_zero hu0 (inv_ne_zero ha0)
            set c₂ : ℕ := (u * (runit7 (eMod7 m d2 d3))⁻¹).val with hc₂
            have hc₂0 : 0 < c₂ := by
              rw [hc₂]
              have h : (u * (runit7 (eMod7 m d2 d3))⁻¹).val ≠ 0 := by
                intro h0
                exact hua0 ((ZMod.val_eq_zero _).mp h0)
              omega
            have hcl₂ : ¬ (7 : ℕ) ∣ c₂ := by
              intro hdvd
              have h0 : c₂ = 0 :=
                Nat.eq_zero_of_dvd_of_lt hdvd (ZMod.val_lt _)
              rw [hc₂] at h0
              exact hua0 ((ZMod.val_eq_zero _).mp h0)
            have hrc₂cast : runit7 c₂ = (c₂ : ZMod 7) :=
              runit7_of_padic_zero (padicValNat.eq_zero_of_not_dvd hcl₂)
            have hccast : (c₂ : ZMod 7)
                = u * (runit7 (eMod7 m d2 d3))⁻¹ := by
              rw [hc₂]; exact ZMod.natCast_zmod_val _
            have hrc₂ : runit7 c₂ ≠ 0 := by
              rw [hrc₂cast, hccast]; exact hua0
            have hca₂ : (c₂ : ZMod 7) * runit7 (eMod7 m d2 d3) = u := by
              rw [hccast, mul_assoc, inv_mul_cancel₀ ha0, mul_one]
            have hcb : (c₂ : ZMod 7) * runit7 (eMod7 m d3 d4) = u * B := by
              rw [hccast, hB]; ring
            have he23c₂ : eMod7 m (c₂ * d2) (c₂ * d3) = u.val * 7 ^ m := by
              rw [e_smul_top hrc₂ he23top, hca₂]
            have he13c₂ : eMod7 m (c₂ * d1) (c₂ * d3)
                = (3 * u).val * 7 ^ m := by
              have h3u : (c₂ : ZMod 7) *
                  ((3 : ZMod 7) * runit7 (eMod7 m d2 d3)) = 3 * u := by
                have hexp : (c₂ : ZMod 7) * ((3 : ZMod 7) *
                    runit7 (eMod7 m d2 d3))
                    = 3 * ((c₂ : ZMod 7) * runit7 (eMod7 m d2 d3)) := by ring
                rw [hexp, hca₂]
              rw [e_smul_top hrc₂ he13top, h3u]
            have he34c₂ : eMod7 m (c₂ * d3) (c₂ * d4)
                = (u * B).val * 7 ^ m := by
              rw [e_smul_top hrc₂ he34top, hcb]
            have he24top : eMod7 m d2 d4
                = (2 * runit7 (eMod7 m d2 d3)
                    + runit7 (eMod7 m d3 d4)).val * 7 ^ m :=
              e_top_twoX hrel23 ht34 ht24 he23top he34top
            have he24c₂ : eMod7 m (c₂ * d2) (c₂ * d4)
                = (u * (B + 2)).val * 7 ^ m := by
              have hkey : (c₂ : ZMod 7) * (2 * runit7 (eMod7 m d2 d3)
                  + runit7 (eMod7 m d3 d4)) = u * (B + 2) := by
                have hexp : (c₂ : ZMod 7) * (2 * runit7 (eMod7 m d2 d3)
                    + runit7 (eMod7 m d3 d4))
                    = 2 * ((c₂ : ZMod 7) * runit7 (eMod7 m d2 d3))
                      + (c₂ : ZMod 7) * runit7 (eMod7 m d3 d4) := by ring
                rw [hexp, hca₂, hcb]; ring
              rw [e_smul_top hrc₂ he24top, hkey]
            have he14top : eMod7 m d1 d4
                = (2 * ((3 : ZMod 7) * runit7 (eMod7 m d2 d3))
                    + runit7 (eMod7 m d3 d4)).val * 7 ^ m :=
              e_top_twoX hrel13 ht34 ht14 he13top he34top
            have he14c₂ : eMod7 m (c₂ * d1) (c₂ * d4)
                = (u * (B - 1)).val * 7 ^ m := by
              have hkey : (c₂ : ZMod 7) * (2 * ((3 : ZMod 7)
                  * runit7 (eMod7 m d2 d3)) + runit7 (eMod7 m d3 d4))
                  = u * (B - 1) := by
                have hexp : (c₂ : ZMod 7) * (2 * ((3 : ZMod 7)
                    * runit7 (eMod7 m d2 d3)) + runit7 (eMod7 m d3 d4))
                    = 6 * ((c₂ : ZMod 7) * runit7 (eMod7 m d2 d3))
                      + (c₂ : ZMod 7) * runit7 (eMod7 m d3 d4) := by ring
                rw [hexp, hca₂, hcb,
                  show (6 : ZMod 7) = -1 by decide, mul_sub, mul_one]
                ring
              rw [e_smul_top hrc₂ he14top, hkey]
            have hrel₂L : ∀ j k : ℕ, j < m → ∀ x y : ℕ,
                runit7 x = s → runit7 y = s →
                residueRelOf ((1 + k * 7 ^ (m - j)) * c₂ * x)
                  ((1 + k * 7 ^ (m - j)) * c₂ * y) = residueRel.same := by
              intro j k hjm x y hx hy
              apply rel_same
              · rw [runit7_mul, runit7_mul, runit7_mul, runit7_mul,
                  runit7_multLow hjm, hrc₂cast, hx, hy]
              · rw [runit7_mul, runit7_mul,
                  runit7_multLow hjm, one_mul, hrc₂cast, hy]
                exact mul_ne_zero
                  (by rw [hccast]; exact hua0) hs0
            rcases hdisj with ⟨hu', hcond0⟩ | ⟨hu', hcond0⟩ | ⟨hu', hcond0⟩
            · -- `u ∈ {1,3}`: anchor `d₃`, `v = u·B`
              have hv : u * B ∈ ({0, 1, 6} : Finset (ZMod 7)) := by
                simp only [Finset.mem_insert, Finset.mem_singleton]
                  at hcond0 ⊢
                rcases hcond0 with h | h <;> simp [h]
              obtain ⟨k, hk7, hkk⟩ := etd_top_step hm
                (by rw [padicValNat_mul_seven hcl₂ (ne_of_gt hp3)]
                    exact hu3)
                (by rw [padicValNat_mul_seven hcl₂ (ne_of_gt hp4)]
                    exact hu4)
                (Nat.mul_pos hc₂0 hp3) (Nat.mul_pos hc₂0 hp4)
                (by rw [runit7_mul, runit7_mul, hrc₂cast, hr4, hr3]; ring)
                he34c₂ hv
              have h1m : 1 < m := by omega
              have he23'' : eMod7 m ((1 + k * 7 ^ (m - 1)) * c₂ * d2)
                  ((1 + k * 7 ^ (m - 1)) * c₂ * d3) = u.val * 7 ^ m := by
                rw [mul_assoc, mul_assoc,
                  eMod7_mul (runit7_multLow h1m), he23c₂]
                exact top_resid_multLow h1m hu0
              have he13'' : eMod7 m ((1 + k * 7 ^ (m - 1)) * c₂ * d1)
                  ((1 + k * 7 ^ (m - 1)) * c₂ * d3)
                  = (3 * u).val * 7 ^ m := by
                rw [mul_assoc, mul_assoc,
                  eMod7_mul (runit7_multLow h1m), he13c₂]
                exact top_resid_multLow h1m
                  (mul_ne_zero (by decide : (3 : ZMod 7) ≠ 0) hu0)
              have hq2 : qdig7 m ((1 + k * 7 ^ (m - 1)) * c₂ * d2)
                  = qdig7 m ((1 + k * 7 ^ (m - 1)) * c₂ * d3) + u :=
                qdig_eq_add_of_e_top (hrel₂L 1 k h1m d2 d3 hr2 hr3) he23''
              have hq1 : qdig7 m ((1 + k * 7 ^ (m - 1)) * c₂ * d1)
                  = qdig7 m ((1 + k * 7 ^ (m - 1)) * c₂ * d3) + 3 * u :=
                qdig_eq_add_of_e_top (hrel₂L 1 k h1m d1 d3 hr1 hr3) he13''
              have hcond : etd7 m ((1 + k * 7 ^ (m - 1)) * c₂ * d3)
                  ((1 + k * 7 ^ (m - 1)) * c₂ * d4)
                  ∈ ({0, 1, 6} : Finset (ZMod 7)) := by
                rw [mul_assoc, mul_assoc]; exact hkk
              exact case64_finish4 hm0 hpos hunit hs0 hcls1 hcls2 hA2
                hd1 hd2 hd3 hA1eq
                (Nat.prime_seven.not_dvd_mul (multLow_not_dvd h1m) hcl₂)
                hu0 hq2 hq1 (Or.inl ⟨rfl, hu'⟩) hd4 hcond
            · -- `u ∈ {4,5}`: anchor `d₂`, `v = u·(B+2)`
              obtain ⟨k, hk7, hkk⟩ := etd_top_step hm
                (by rw [padicValNat_mul_seven hcl₂ (ne_of_gt hp2)]
                    exact hu2)
                (by rw [padicValNat_mul_seven hcl₂ (ne_of_gt hp4)]
                    exact hu4)
                (Nat.mul_pos hc₂0 hp2) (Nat.mul_pos hc₂0 hp4)
                (by rw [runit7_mul, runit7_mul, hrc₂cast, hr4, hr2]; ring)
                he24c₂ hcond0
              have h1m : 1 < m := by omega
              have he23'' : eMod7 m ((1 + k * 7 ^ (m - 1)) * c₂ * d2)
                  ((1 + k * 7 ^ (m - 1)) * c₂ * d3) = u.val * 7 ^ m := by
                rw [mul_assoc, mul_assoc,
                  eMod7_mul (runit7_multLow h1m), he23c₂]
                exact top_resid_multLow h1m hu0
              have he13'' : eMod7 m ((1 + k * 7 ^ (m - 1)) * c₂ * d1)
                  ((1 + k * 7 ^ (m - 1)) * c₂ * d3)
                  = (3 * u).val * 7 ^ m := by
                rw [mul_assoc, mul_assoc,
                  eMod7_mul (runit7_multLow h1m), he13c₂]
                exact top_resid_multLow h1m
                  (mul_ne_zero (by decide : (3 : ZMod 7) ≠ 0) hu0)
              have hq2 : qdig7 m ((1 + k * 7 ^ (m - 1)) * c₂ * d2)
                  = qdig7 m ((1 + k * 7 ^ (m - 1)) * c₂ * d3) + u :=
                qdig_eq_add_of_e_top (hrel₂L 1 k h1m d2 d3 hr2 hr3) he23''
              have hq1 : qdig7 m ((1 + k * 7 ^ (m - 1)) * c₂ * d1)
                  = qdig7 m ((1 + k * 7 ^ (m - 1)) * c₂ * d3) + 3 * u :=
                qdig_eq_add_of_e_top (hrel₂L 1 k h1m d1 d3 hr1 hr3) he13''
              have hcond : etd7 m ((1 + k * 7 ^ (m - 1)) * c₂ * d2)
                  ((1 + k * 7 ^ (m - 1)) * c₂ * d4)
                  ∈ ({0, 1, 6} : Finset (ZMod 7)) := by
                rw [mul_assoc, mul_assoc]; exact hkk
              exact case64_finish4 hm0 hpos hunit hs0 hcls1 hcls2 hA2
                hd1 hd2 hd3 hA1eq
                (Nat.prime_seven.not_dvd_mul (multLow_not_dvd h1m) hcl₂)
                hu0 hq2 hq1 (Or.inr (Or.inl ⟨rfl, hu'⟩)) hd4 hcond
            · -- `u ∈ {2,6}`: anchor `d₁`, `v = u·(B−1)`
              obtain ⟨k, hk7, hkk⟩ := etd_top_step hm
                (by rw [padicValNat_mul_seven hcl₂ (ne_of_gt hp1)]
                    exact hu1)
                (by rw [padicValNat_mul_seven hcl₂ (ne_of_gt hp4)]
                    exact hu4)
                (Nat.mul_pos hc₂0 hp1) (Nat.mul_pos hc₂0 hp4)
                (by rw [runit7_mul, runit7_mul, hrc₂cast, hr4, hr1]; ring)
                he14c₂ hcond0
              have h1m : 1 < m := by omega
              have he23'' : eMod7 m ((1 + k * 7 ^ (m - 1)) * c₂ * d2)
                  ((1 + k * 7 ^ (m - 1)) * c₂ * d3) = u.val * 7 ^ m := by
                rw [mul_assoc, mul_assoc,
                  eMod7_mul (runit7_multLow h1m), he23c₂]
                exact top_resid_multLow h1m hu0
              have he13'' : eMod7 m ((1 + k * 7 ^ (m - 1)) * c₂ * d1)
                  ((1 + k * 7 ^ (m - 1)) * c₂ * d3)
                  = (3 * u).val * 7 ^ m := by
                rw [mul_assoc, mul_assoc,
                  eMod7_mul (runit7_multLow h1m), he13c₂]
                exact top_resid_multLow h1m
                  (mul_ne_zero (by decide : (3 : ZMod 7) ≠ 0) hu0)
              have hq2 : qdig7 m ((1 + k * 7 ^ (m - 1)) * c₂ * d2)
                  = qdig7 m ((1 + k * 7 ^ (m - 1)) * c₂ * d3) + u :=
                qdig_eq_add_of_e_top (hrel₂L 1 k h1m d2 d3 hr2 hr3) he23''
              have hq1 : qdig7 m ((1 + k * 7 ^ (m - 1)) * c₂ * d1)
                  = qdig7 m ((1 + k * 7 ^ (m - 1)) * c₂ * d3) + 3 * u :=
                qdig_eq_add_of_e_top (hrel₂L 1 k h1m d1 d3 hr1 hr3) he13''
              have hcond : etd7 m ((1 + k * 7 ^ (m - 1)) * c₂ * d1)
                  ((1 + k * 7 ^ (m - 1)) * c₂ * d4)
                  ∈ ({0, 1, 6} : Finset (ZMod 7)) := by
                rw [mul_assoc, mul_assoc]; exact hkk
              exact case64_finish4 hm0 hpos hunit hs0 hcls1 hcls2 hA2
                hd1 hd2 hd3 hA1eq
                (Nat.prime_seven.not_dvd_mul (multLow_not_dvd h1m) hcl₂)
                hu0 hq2 hq1 (Or.inr (Or.inr ⟨rfl, hu'⟩)) hd4 hcond
          · -- `ν(e₃₄) < m`: `u = 1`, anchor `d₃`, `lemma7_i_expl`/`etd_top_step`
            have hνd' : padicValNat 7 (eMod7 m d3 d4) < m := by
              rcases eq_or_ne (eMod7 m d3 d4) 0 with h0 | h0
              · rw [h0, padicValNat.zero]; exact hm0
              · exact lt_of_le_of_ne (enu7_le_of_ne h0) h34m
            by_cases he34z : eMod7 m d3 d4 = 0
            · -- `e₃₄ = 0`: `etd_top_step` `v = 0`
              obtain ⟨k, hk7, hkk⟩ := etd_top_step hm
                (by rw [padicValNat_mul_seven hcl (ne_of_gt hp3)]; exact hu3)
                (by rw [padicValNat_mul_seven hcl (ne_of_gt hp4)]; exact hu4)
                (Nat.mul_pos hc0 hp3) (Nat.mul_pos hc0 hp4)
                (by rw [runit7_mul, runit7_mul, hrcast, hr4, hr3]; ring)
                (by rw [eMod7_smul hrc, he34z, mul_zero, Nat.zero_mod,
                    ZMod.val_zero, zero_mul])
                (by decide : (0 : ZMod 7) ∈ ({0, 1, 6} : Finset (ZMod 7)))
              have h1m : 1 < m := by omega
              have hlam₁ : ¬ 7 ∣ (1 + k * 7 ^ (m - 1)) * c :=
                Nat.prime_seven.not_dvd_mul (multLow_not_dvd h1m) hcl
              have hq2 : qdig7 m ((1 + k * 7 ^ (m - 1)) * c * d2)
                  = qdig7 m ((1 + k * 7 ^ (m - 1)) * c * d3) + 1 :=
                qdig_eq_add_of_e_top (hrel23L 1 k h1m) (hq23L 1 k h1m)
              have hq1 : qdig7 m ((1 + k * 7 ^ (m - 1)) * c * d1)
                  = qdig7 m ((1 + k * 7 ^ (m - 1)) * c * d3) + 3 * 1 := by
                have h := qdig_eq_add_of_e_top (hrel13L 1 k h1m)
                  (hq13L 1 k h1m)
                simpa using h
              have hcond : etd7 m ((1 + k * 7 ^ (m - 1)) * c * d3)
                  ((1 + k * 7 ^ (m - 1)) * c * d4)
                  ∈ ({0, 1, 6} : Finset (ZMod 7)) := by
                rw [mul_assoc, mul_assoc]; exact hkk
              exact case64_finish4 hm0 hpos hunit hs0 hcls1 hcls2 hA2
                hd1 hd2 hd3 hA1eq hlam₁ (by decide) hq2 hq1
                (Or.inl ⟨rfl, by decide⟩) hd4 hcond
            · -- `ν(e₃₄) ∈ [1, m)`: `lemma7_i_expl` on `(c·d₃, c·d₄)`
              have he34ne := he34z
              have hνe' : padicValNat 7 (eMod7 m (c * d3) (c * d4))
                  = padicValNat 7 (eMod7 m d3 d4) := by
                rw [eMod7_smul hrc]
                have h1 : padicValNat 7 ((c * eMod7 m d3 d4) % 7 ^ (m + 1))
                    = padicValNat 7 (c * eMod7 m d3 d4) :=
                  (padicValNat_eq_of_mod (m := m) (Nat.mod_mod _ _).symm
                    (by rw [padicValNat_mul_seven hcl he34ne]
                        exact enu7_le_of_ne he34ne)
                    (mul_ne_zero (ne_of_gt hc0) he34ne)).symm
                rw [h1, padicValNat_mul_seven hcl he34ne]
              have hνpos : 0 < padicValNat 7 (eMod7 m (c * d3) (c * d4)) := by
                rw [hνe']
                have hdvd : 7 ∣ eMod7 m d3 d4 := dvd7_eMod7_twoX hu3 hu4 ht34
                have h1 : 1 ≤ padicValNat 7 (eMod7 m d3 d4) :=
                  (Nat.pow_dvd_iff_le_padicValNat
                    (by norm_num : (7 : ℕ) ≠ 1) he34ne).mp
                    (show (7 : ℕ) ^ 1 ∣ eMod7 m d3 d4 from by
                      rwa [pow_one])
                omega
              have hνm' : padicValNat 7 (eMod7 m (c * d3) (c * d4)) < m := by
                rw [hνe']; exact hνd'
              obtain ⟨k, hk7, hkk⟩ := lemma7_i_expl
                (by rw [padicValNat_mul_seven hcl (ne_of_gt hp3)]; exact hu3)
                (by rw [padicValNat_mul_seven hcl (ne_of_gt hp4)]; exact hu4)
                (Nat.mul_pos hc0 hp3) (Nat.mul_pos hc0 hp4)
                (by rw [runit7_mul, runit7_mul, hrcast, hr4, hr3]; ring)
                hνpos hνm' apLen_2345
              have hjm : padicValNat 7 (eMod7 m (c * d3) (c * d4)) < m := hνm'
              have hlam₁ : ¬ 7 ∣ (1 + k * 7 ^ (m - padicValNat 7
                  (eMod7 m (c * d3) (c * d4)))) * c :=
                Nat.prime_seven.not_dvd_mul (multLow_not_dvd hjm) hcl
              have hq2 : qdig7 m ((1 + k * 7 ^ (m - padicValNat 7
                    (eMod7 m (c * d3) (c * d4)))) * c * d2)
                  = qdig7 m ((1 + k * 7 ^ (m - padicValNat 7
                    (eMod7 m (c * d3) (c * d4)))) * c * d3) + 1 :=
                qdig_eq_add_of_e_top
                  (hrel23L _ k hjm) (hq23L _ k hjm)
              have hq1 : qdig7 m ((1 + k * 7 ^ (m - padicValNat 7
                    (eMod7 m (c * d3) (c * d4)))) * c * d1)
                  = qdig7 m ((1 + k * 7 ^ (m - padicValNat 7
                    (eMod7 m (c * d3) (c * d4)))) * c * d3) + 3 * 1 := by
                have h := qdig_eq_add_of_e_top (hrel13L _ k hjm)
                  (hq13L _ k hjm)
                simpa using h
              have hcond : etd7 m ((1 + k * 7 ^ (m - padicValNat 7
                    (eMod7 m (c * d3) (c * d4)))) * c * d3)
                  ((1 + k * 7 ^ (m - padicValNat 7
                    (eMod7 m (c * d3) (c * d4)))) * c * d4)
                  ∈ ({0, 1, 6} : Finset (ZMod 7)) := by
                rw [mul_assoc, mul_assoc]
                exact mem_016_of_not_2345 hkk
              exact case64_finish4 hm0 hpos hunit hs0 hcls1 hcls2 hA2
                hd1 hd2 hd3 hA1eq hlam₁ (by decide) hq2 hq1
                (Or.inl ⟨rfl, by decide⟩) hd4 hcond
