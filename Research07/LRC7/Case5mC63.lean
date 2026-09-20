/-
Copyright (c) 2026 Research07 contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Research07 contributors
-/
import Research07.LRC7.Case5mTop
import Research07.LRC7.Case5mL9b
import Research07.LRC7.Case5mL10

/-!
# Paper §6.3 — `|A₁| = 3`, `|A₂| = 1`, `|A₄| = 1` (Barajas–Serra)

For `A₁` a three-element `Finset ℕ` of `7`-adic units sharing the residue
class `s ∈ {1,2,4}`, `A₂ = {d₄}` in class `2s` and `A₄ = {d₅}` in class
`4s`, some `7`-unit multiplier `λ` is `good7` on `A₁ ∪ A₂ ∪ A₄`.

`lemma9_ii` (equal-level `j ∈ {2,3}` 3-compression) is landed in
`Case5mL10.lean`; `lemma9_i'` in `Case5mL9b.lean`; `lemma5`, `lemma6`,
`lemma12` in `Compress.lean`; the finite `ZMod 7` facts `bad63`,
`case63_bad_pairs`, `case63_eps_avoid`, `case63_table`,
`case63_table_rescue` in `Case5mBase.lean`.  The `case63` signature matches
the `Case5m.lean` dispatcher exactly (no extra hypotheses).

## Route

* `c63_finish` — the `Λ₀` realizer: a `ZMod 7` shift `t` avoiding `{0,6}`
  on the three shifted class-images is produced by `1 + K·7^m ∈ Λ₀`
  (`exists_lambda0_of_shift`), after the class filters are identified.
* `c63_lemma5` — the `lemma5` bridge: `apLen ≤ 3` on the `A₁` digit set
  plus `ẽ(d₄,d₅) ∉ {2,4}` (or `apLen ≤ 2`) yields the goal.
* `c63_l9ii3` — explicit-`Λ_h` variant of `lemma9_ii` at `j = 3`:
  the returned `λ = 1 + k·7^{m−h}` form is needed for the order-of-
  application arguments in `(ii.2)` `h < m`.
* Branch structure (paper): `(i)`/`(ii.1)` `h < m` collapse to
  `apLen ≤ 2`; `(ii.2)` `h < m` splits on `ν(e₄₅)` — off-level cases
  normalize `q(e₄₅) = 6`, the equal-level case runs the `ẽ/ũ` table
  (`case63_table`, with the `×2` rescue `case63_table_rescue` at
  `(ẽ,ũ) = (0,3)`); `h = m` normalizes the pure-top differences and runs
  the eight-bad-pair analysis with the `Λ₁` carry mechanism
  (`q(λ·7d₃) = 4ε₁ + 2ε₂`).

Paper subtlety handled here: `(ii.2.b)` needs `r(e₄₅) = ±r(e₁₃)`.  The
three valid ratio-3 labelings give `r(e₁₃) ∈ {3w, −w, −2w}` (for
`w = r(e₂₃)`), and `±{w,2w,3w}` covers all six units — so a relabeling
always exists.  This is what the paper's "by Lemma 11 we may assume
`r(e₄₅) = ±r(e₁₃)`" means.
-/

private instance : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩

/-! ### §1 Low-level clones (private in sibling files) -/

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

/-- `apLen ≤ 3` when all pairwise differences lie in `{0,±1,±2}`
(`{0,1,2,5,6}`) — the `remark8_ii` variant used by `lemma9_ii` (`j=3`),
whose residue-digit condition only yields `{0,1,5,6}+{0,1}`. -/
private theorem remark8_ii'_dec :
    ∀ B : Finset (ZMod 7),
      (∀ x ∈ B, ∀ y ∈ B, x - y ∈ ({0, 1, 2, 5, 6} : Finset (ZMod 7))) →
      apLen B ≤ 3 := by
  set_option maxRecDepth 16384 in
  decide

private theorem remark8_ii' {B : Finset (ZMod 7)}
    (hB : ∀ x ∈ B, ∀ y ∈ B, x - y ∈ ({0, 1, 2, 5, 6} : Finset (ZMod 7))) :
    apLen B ≤ 3 := remark8_ii'_dec B hB

/-- Bridge for `remark8_ii'` (`lemma9_ii` `j = 3` route): pair-residue
digits in `{0,1,5,6}` yield `q`-differences in `{0,1,2,5,6}` via
`qdig_eMod_sub` (`q(e) − (qx−qy) ∈ {0,6}`). -/
private theorem remark8_ii_int {m : ℕ} {B : Finset ℕ}
    (hsame : ∀ x ∈ B, ∀ y ∈ B, residueRelOf x y = residueRel.same)
    (hB : ∀ x ∈ B, ∀ y ∈ B,
      qdig7 m (eMod7 m x y) ∈ ({0, 1, 5, 6} : Finset (ZMod 7))) :
    ∀ a ∈ B.image (qdig7 m), ∀ b ∈ B.image (qdig7 m),
      a - b ∈ ({0, 1, 2, 5, 6} : Finset (ZMod 7)) := by
  intro a ha b hb
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hb
  have hsame' := hsame x hx y hy
  have hsub := qdig_eMod_sub (m := m) hsame'
  have hq := hB x hx y hy
  simp only [Finset.mem_insert, Finset.mem_singleton] at hq hsub ⊢
  rcases hq with hq | hq | hq | hq <;> rcases hsub with hsub | hsub <;>
    rw [hq] at hsub <;>
    (have e : qdig7 m x - qdig7 m y
        = qdig7 m (eMod7 m x y)
          - (qdig7 m (eMod7 m x y) - (qdig7 m x - qdig7 m y)) := by ring
     rw [e, hq, hsub]
     decide)

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

/-! ### §1b The `qdig7_sub_resid` borrow engine (clones) -/

private theorem residue_decomp {m x : ℕ} :
    ∃ q f : ℕ, x % 7 ^ (m + 1) = q * 7 ^ m + f ∧ q < 7 ∧ f < 7 ^ m := by
  refine ⟨(x % 7 ^ (m + 1)) / 7 ^ m, (x % 7 ^ (m + 1)) % 7 ^ m, ?_, ?_,
    Nat.mod_lt _ (Nat.pow_pos (by norm_num))⟩
  · rw [mul_comm, Nat.div_add_mod]
  · rw [Nat.div_lt_iff_lt_mul (Nat.pow_pos (by norm_num)), ← pow_succ']
    exact Nat.mod_lt _ (Nat.pow_pos (by norm_num))

/-- Cast a truncated-subtraction digit expression into `ZMod 7`. -/
private theorem natCast_sub_add {a b c : ℕ} (h : c ≤ a + b) :
    ((a + b - c : ℕ) : ZMod 7) = (a : ZMod 7) + b - c := by
  have hcast : ((a + b - c : ℕ) : ZMod 7)
      = (((a + b - c : ℕ) : ℤ) : ZMod 7) := by simp
  rw [hcast, Int.ofNat_sub h]
  push_cast
  ring

/-- **Exact borrow formula** for the wrapped residue difference
`(a % N + N − b % N)`: writing `a % N = q_a·7^m + f_a`,
`b % N = q_b·7^m + f_b`, the top digit is `q_a − q_b` minus the borrow
`1` iff `f_a < f_b`. -/
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
    rw [if_pos (by rwa [hf1e, hf2e] : a % 7 ^ m < b % 7 ^ m)]
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
    rw [if_neg (by rwa [hf1e, hf2e] : ¬ a % 7 ^ m < b % 7 ^ m)]
    ring

/-- The `q`-digit of a scalar multiple of a difference residue whose
`ZMod N` value is the combination `A − B`: reduces to the borrow formula
`qdig7_sub_resid` via the residue congruence. -/
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

/-- `ZMod`-cast of `eMod7` in the `same` branch. -/
private theorem eMod7_zmod_cast_same {m u v : ℕ}
    (h : residueRelOf u v = residueRel.same) :
    ((eMod7 m u v : ℕ) : ZMod (7 ^ (m + 1))) = (u : ZMod _) - (v : ZMod _) := by
  obtain ⟨h1, h2⟩ := (residueRelOf_eq_same).mp h
  rw [eMod7_zmod_cast, if_neg h1, if_neg h2]

/-- `eMod7` of an element with itself is `0`. -/
private theorem eMod7_self' (m x : ℕ) : eMod7 m x x = 0 := by
  rcases eq_or_ne x 0 with rfl | hx0
  · simp [eMod7]
  · have hr : runit7 x ≠ 0 := runit7_ne_zero (Nat.pos_of_ne_zero hx0)
    have h2 : ¬ runit7 x = 2 * runit7 x := by
      intro h
      have h' : 2 * runit7 x - runit7 x = 0 := by rw [← h, sub_self]
      rw [show 2 * runit7 x - runit7 x = runit7 x by ring] at h'
      exact hr h'
    unfold eMod7
    rw [if_neg h2, if_neg h2]
    have hlt : x % 7 ^ (m + 1) < 7 ^ (m + 1) :=
      Nat.mod_lt _ (Nat.pow_pos (by norm_num))
    have h : x % 7 ^ (m + 1) + 7 ^ (m + 1) - x % 7 ^ (m + 1) = 7 ^ (m + 1) := by
      omega
    rw [h, Nat.mod_self]

/-- `ZMod`-cast difference decomposition: `e(x,y) = e(x,l) − e(y,l)`. -/
private theorem eMod7_cast_sub {m x y l : ℕ}
    (hxl : residueRelOf x l = residueRel.same)
    (hyl : residueRelOf y l = residueRel.same)
    (hxy : residueRelOf x y = residueRel.same) :
    ((eMod7 m x y : ℕ) : ZMod (7 ^ (m + 1)))
      = (eMod7 m x l : ZMod _) - (eMod7 m y l : ZMod _) := by
  rw [eMod7_zmod_cast_same hxy, eMod7_zmod_cast_same hxl,
    eMod7_zmod_cast_same hyl]
  ring

/-- As naturals: `e(x,y) = (e(x,l) + N − e(y,l)) % N`. -/
private theorem eMod7_sub_eq {m x y l : ℕ}
    (hxl : residueRelOf x l = residueRel.same)
    (hyl : residueRelOf y l = residueRel.same)
    (hxy : residueRelOf x y = residueRel.same) :
    eMod7 m x y
      = (eMod7 m x l + 7 ^ (m + 1) - eMod7 m y l) % 7 ^ (m + 1) := by
  have h := eMod7_cast_sub (m := m) hxl hyl hxy
  have hcast : ((eMod7 m x y : ℕ) : ZMod (7 ^ (m + 1)))
      = ((eMod7 m x l + 7 ^ (m + 1) - eMod7 m y l : ℕ) : ZMod _) := by
    rw [h]
    have hlt : eMod7 m y l ≤ eMod7 m x l + 7 ^ (m + 1) := by
      have := eMod7_lt m y l
      omega
    rw [Nat.cast_sub hlt, Nat.cast_add, ZMod.natCast_self]
    ring
  rw [ZMod.natCast_eq_natCast_iff'] at hcast
  have hlt : eMod7 m x y < 7 ^ (m + 1) := eMod7_lt _ _ _
  rwa [Nat.mod_eq_of_lt hlt] at hcast

/-- A `Λ_j`-multiplier preserves the `mod 7^m` part of a `7^j`-divisible
element (`7^{m−j}·w` is a multiple of `7^m`). -/
private theorem multLow_low {m j k w : ℕ} (hjm : j ≤ m) (hw : 7 ^ j ∣ w) :
    ((1 + k * 7 ^ (m - j)) * w) % 7 ^ m = w % 7 ^ m := by
  obtain ⟨u, rfl⟩ := hw
  rw [add_mul, one_mul]
  have hP : k * 7 ^ (m - j) * (7 ^ j * u) = 7 ^ m * (k * u) := by
    have e : k * 7 ^ (m - j) * (7 ^ j * u) = k * u * (7 ^ (m - j) * 7 ^ j) := by
      ring
    rw [e, ← pow_add, Nat.sub_add_cancel hjm]
    ring
  rw [hP, Nat.add_mul_mod_self_left]

/-- A `ZMod 7` element of `val < 2` is `0` or `1`. -/
private theorem zmod7_of_val_lt_two {s : ZMod 7} (h : s.val < 2) :
    s = 0 ∨ s = 1 := by
  have hv : s.val = 0 ∨ s.val = 1 := by omega
  rcases hv with h0 | h1
  · refine Or.inl ?_
    rw [← ZMod.natCast_zmod_val s, h0]
    exact Nat.cast_zero
  · refine Or.inr ?_
    rw [← ZMod.natCast_zmod_val s, h1]
    exact Nat.cast_one

/-- Negation preserves `{0,1,6} ⊆ ZMod 7`. -/
private theorem neg_mem_016 {s : ZMod 7}
    (h : s ∈ ({0, 1, 6} : Finset (ZMod 7))) :
    -s ∈ ({0, 1, 6} : Finset (ZMod 7)) := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at h ⊢
  rcases h with rfl | rfl | rfl <;> decide

/-- `−s − 1` for `s ∈ {0,1,5,6}` stays in `{0,1,5,6}` (`{6,5,1,0}`). -/
private theorem neg_sub_one_mem_0156 {s : ZMod 7}
    (h : s ∈ ({0, 1, 5, 6} : Finset (ZMod 7))) :
    -s - 1 ∈ ({0, 1, 5, 6} : Finset (ZMod 7)) := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at h ⊢
  rcases h with rfl | rfl | rfl | rfl <;> decide

/-- `−s − 1` for `s ∈ {0,5,6}` stays in `{0,1,5,6}` (`{6,1,0}`). -/
private theorem neg_sub_one_mem_056 {s : ZMod 7}
    (h : s ∈ ({0, 5, 6} : Finset (ZMod 7))) :
    -s - 1 ∈ ({0, 1, 5, 6} : Finset (ZMod 7)) := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at h ⊢
  rcases h with rfl | rfl | rfl <;> decide

/-- `s − δ` for `s ∈ {0,1,6}`, `δ ∈ {0,1}` stays in `{0,1,5,6}`. -/
private theorem sub_borrow_mem_0156 {s d : ZMod 7}
    (hs : s ∈ ({0, 1, 6} : Finset (ZMod 7))) (hd : d = 0 ∨ d = 1) :
    s - d ∈ ({0, 1, 5, 6} : Finset (ZMod 7)) := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hs ⊢
  rcases hs with rfl | rfl | rfl <;> rcases hd with rfl | rfl <;> decide

/-- `etd7` on a `twoX` pair (`r(v) = 2r(u)`). -/
private theorem etd7_eq_twoX {m u v : ℕ} (h : runit7 v = 2 * runit7 u) :
    etd7 m u v = 2 * qdig7 m u - qdig7 m v := by
  unfold etd7
  rw [if_pos h]

/-- The `j = 3` multiplier table: for all `qx qy : ZMod 7` some
`t ∈ {0,5,6}` gives `q(λx) = qx + 2qy + 5t ∈ {0,1,5,6}` and
`q(λx) − q(λy) = qx + 2qy + 4t ∈ {0,1,6}` (the `u = 5(t − qy)` shift of
`qdig7_multLow`). -/
private theorem lemma9_ii_table3 :
    ∀ qx qy : ZMod 7, ∃ t : ZMod 7,
      t ∈ ({0, 5, 6} : Finset (ZMod 7)) ∧
      (qx + 2 * qy + 5 * t) ∈ ({0, 1, 5, 6} : Finset (ZMod 7)) ∧
      (qx + 2 * qy + 4 * t) ∈ ({0, 1, 6} : Finset (ZMod 7)) := by
  decide

/-- `q(7^m) = 1`. -/
private theorem qdig7_pow_self (m : ℕ) : qdig7 m (7 ^ m) = 1 := by
  unfold qdig7
  rw [Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self m))]
  rw [Nat.div_self (Nat.pow_pos (by norm_num) : 0 < 7 ^ m)]
  exact Nat.cast_one

/-- `q`-digit from a `ZMod N` subtraction cast (`w ≡ A − B`). -/
private theorem qdig7_of_sub_cast {m w A B : ℕ}
    (hcast : ((w : ℕ) : ZMod (7 ^ (m + 1))) = (A : ZMod _) - (B : ZMod _)) :
    qdig7 m w = qdig7 m A - qdig7 m B
      - if A % 7 ^ m < B % 7 ^ m then (1 : ZMod 7) else 0 := by
  have h := qdig_smul_eMod_eq (m := m) (lam := 1) (e := w) (A := A) (B := B)
    (by simpa using hcast)
  rwa [one_mul] at h

/-- `apLen ≤ 7` for every set (the universal cover). -/
private theorem apLen_le7' (X : Finset (ZMod 7)) : apLen X ≤ 7 := by
  rw [apLen_le_iff X 7 le_rfl]
  exact ⟨0, fun x _ => by rw [mem_cycIv, sub_zero]; exact ZMod.val_lt x⟩

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

/-- Mirrored `lemma7_ii` with an explicit multiplier and target `{0,1,6}`:
for a `twoX` pair with `ν(e) = m` and `r(e) ∈ {1,6}`, a `Λ₁`-element puts
`ẽ ∈ {0,1,6}`.  `r(e) = 1`: `q(λ·7d) = 6` forces `q(2λd) = 2q(λd)+1`,
so `ẽ ∈ {0,1}`; `r(e) = 6`: `q(λ·7d) = 0` gives `ẽ ∈ {0,6}`. -/
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

/-! ### §1c Small `apLen`/`multLow` utilities (Case66 clones) -/

/-- Under `Λ_h` with `h < m`, the mod-`7^m` part of a level-`h` element
is fixed. -/
private theorem multLow_shift_qdig {m h k x : ℕ} (hhm : h < m)
    (hx : padicValNat 7 x = h) (hx0 : x ≠ 0) :
    ((1 + k * 7 ^ (m - h)) * x) % 7 ^ m = x % 7 ^ m := by
  have hdvd : 7 ^ m ∣ k * 7 ^ (m - h) * x := by
    have hxd : 7 ^ h ∣ x :=
      (Nat.pow_dvd_iff_le_padicValNat (by norm_num) hx0).mpr (le_of_eq hx.symm)
    obtain ⟨y, rfl⟩ := hxd
    have hsplit : 7 ^ m = 7 ^ (m - h) * 7 ^ h := by
      rw [← pow_add]
      congr 1
      omega
    rw [hsplit]
    exact ⟨k * y, by ring⟩
  obtain ⟨z, hz⟩ := hdvd
  rw [add_mul, one_mul, hz, Nat.add_mul_mod_self_left]

/-- A `Λ_j`-element applied below a level-`m` residue leaves it fixed. -/
private theorem lambda_low_top_resid {m j k t : ℕ} (hjm : j < m) (ht : t < 7) :
    (1 + k * 7 ^ (m - j)) * (t * 7 ^ m) % 7 ^ (m + 1) = t * 7 ^ m := by
  have hdvd : 7 ^ (m + 1) ∣ k * 7 ^ (m - j) * (t * 7 ^ m) := by
    have hs : 7 ^ (m + 1) ∣ 7 ^ (m - j) * 7 ^ m := by
      rw [← pow_add]
      exact Nat.pow_dvd_pow 7 (by omega)
    rw [show k * 7 ^ (m - j) * (t * 7 ^ m)
        = (7 ^ (m - j) * 7 ^ m) * (k * t) by ring]
    exact dvd_mul_of_dvd_left hs _
  obtain ⟨z, hz⟩ := hdvd
  rw [add_mul, one_mul, hz, Nat.add_mul_mod_self_left]
  have hlt7 : t * 7 ^ m < 7 ^ (m + 1) := by
    rw [pow_succ']
    exact (Nat.mul_lt_mul_right (Nat.pow_pos (by norm_num))).mpr ht
  exact Nat.mod_eq_of_lt hlt7

/-- For `m ≥ 2`, `Λ₁` preserves a level-`m` residue `t·7^m`. -/
private theorem lambda1_top_resid {m k t : ℕ} (hm : 2 ≤ m) (ht : t < 7) :
    (1 + k * 7 ^ (m - 1)) * (t * 7 ^ m) % 7 ^ (m + 1) = t * 7 ^ m :=
  lambda_low_top_resid (by omega : 1 < m) ht

/-- The `Λ₀`-wrapped top residue is verbatim:
`(1+k·7^m)·(t·7^m) ≡ t·7^m`. -/
private theorem lambda0_top_resid {m k t : ℕ} (hm : 1 ≤ m) (ht : t < 7) :
    (1 + k * 7 ^ m) * (t * 7 ^ m) % 7 ^ (m + 1) = t * 7 ^ m := by
  have hdvd : 7 ^ (m + 1) ∣ k * 7 ^ m * (t * 7 ^ m) := by
    have hs : 7 ^ (m + 1) ∣ 7 ^ m * 7 ^ m := by
      rw [← pow_add]
      exact Nat.pow_dvd_pow 7 (by omega)
    rw [show k * 7 ^ m * (t * 7 ^ m)
        = (7 ^ m * 7 ^ m) * (k * t) by ring]
    exact dvd_mul_of_dvd_left hs _
  obtain ⟨z, hz⟩ := hdvd
  rw [add_mul, one_mul, hz, Nat.add_mul_mod_self_left]
  have hlt7 : t * 7 ^ m < 7 ^ (m + 1) := by
    rw [pow_succ']
    exact (Nat.mul_lt_mul_right (Nat.pow_pos (by norm_num))).mpr ht
  exact Nat.mod_eq_of_lt hlt7

/-- Two `ZMod 7` points at cyclic distance `≤ 1` cover with `apLen ≤ 2`. -/
private theorem apLen_pair_le2 :
    ∀ a b : ZMod 7, a - b ∈ ({0, 1, 6} : Finset (ZMod 7)) →
      apLen ({a, b} : Finset (ZMod 7)) ≤ 2 := by
  decide

/-- For a `same`-branch pair, `q(e) ∈ {0,6}` makes the two `q`-digits
cyclically adjacent. -/
private theorem apLen_pair_of_qe {m x y : ℕ}
    (hrel : residueRelOf x y = residueRel.same)
    (hq : qdig7 m (eMod7 m x y) ∈ ({0, 6} : Finset (ZMod 7))) :
    apLen ({qdig7 m x, qdig7 m y} : Finset (ZMod 7)) ≤ 2 := by
  have hb := qdig_eMod_sub (m := m) (x := x) (y := y) hrel
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb hq
  apply apLen_pair_le2
  have hdiff : qdig7 m x - qdig7 m y
      = qdig7 m (eMod7 m x y)
        - (qdig7 m (eMod7 m x y) - (qdig7 m x - qdig7 m y)) := by ring
  rw [hdiff]
  rcases hq with hq0 | hq6 <;> rcases hb with hb0 | hb6
  · rw [hb0, hq0]; decide
  · rw [hb6, hq0]; decide
  · rw [hb0, hq6]; decide
  · rw [hb6, hq6]; decide

/-- A singleton has `apLen ≤ 1`. -/
private theorem apLen_singleton_le1 (a : ZMod 7) :
    apLen ({a} : Finset (ZMod 7)) ≤ 1 := by
  rw [apLen_le_iff _ 1 (by norm_num)]
  exact ⟨a, by rw [cycIv_one]⟩

/-- A nonempty `ZMod 7` set has `apLen ≥ 1`. -/
private theorem apLen_pos_of_nonempty {X : Finset (ZMod 7)}
    (hne : X.Nonempty) : 0 < apLen X := by
  rcases Nat.eq_zero_or_pos (apLen X) with h0 | h
  · obtain ⟨i, hi⟩ := (apLen_le_iff X 0 (by norm_num)).mp (h0 ▸ le_rfl)
    rw [cycIv_zero] at hi
    rw [Finset.subset_empty] at hi
    rw [hi] at hne
    exact absurd hne Finset.not_nonempty_empty
  · exact h

/-- The `same`-branch relation is preserved by a common unit multiplier. -/
private theorem rel_same_of_mul {x y lam : ℕ} (hlam : ¬ 7 ∣ lam)
    (hxy : runit7 x = runit7 y) (hy : y ≠ 0) :
    residueRelOf (lam * x) (lam * y) = residueRel.same := by
  apply rel_same
  · rw [runit7_mul, runit7_mul, hxy]
  · exact runit7_ne_zero (Nat.mul_pos
      (Nat.pos_of_ne_zero (fun h0 => hlam (h0 ▸ dvd_zero _)))
      (Nat.pos_of_ne_zero hy))

/-! ### §2 §6.3 main-case infrastructure: pure-top relations, `Λ₁` carry
engine, finite tables -/

/-- For a `same` pair with pure-top difference `e(x,y) = v·7^m`, the residue
of `x` is the wrapped sum `(res(y) + v·7^m) % N`. -/
private theorem pure_top_res_eq {m x y : ℕ} {v : ZMod 7}
    (hrel : residueRelOf x y = residueRel.same)
    (he : eMod7 m x y = v.val * 7 ^ m) :
    x % 7 ^ (m + 1) = (y % 7 ^ (m + 1) + v.val * 7 ^ m) % 7 ^ (m + 1) := by
  rw [eMod7_same_eq hrel] at he
  have hylt : y % 7 ^ (m + 1) < 7 ^ (m + 1) :=
    Nat.mod_lt _ (Nat.pow_pos (by norm_num))
  have hxlt : x % 7 ^ (m + 1) < 7 ^ (m + 1) :=
    Nat.mod_lt _ (Nat.pow_pos (by norm_num))
  have hvlt : v.val * 7 ^ m < 7 ^ (m + 1) := by
    rw [pow_succ']
    exact Nat.mul_lt_mul_of_pos_right (ZMod.val_lt v)
      (Nat.pow_pos (by norm_num))
  have hmod : (x % 7 ^ (m + 1) + 7 ^ (m + 1) - y % 7 ^ (m + 1))
      % 7 ^ (m + 1) = v.val * 7 ^ m := he
  have hcongr : x % 7 ^ (m + 1) + 7 ^ (m + 1) - y % 7 ^ (m + 1)
      ≡ v.val * 7 ^ m [MOD 7 ^ (m + 1)] := by
    rw [Nat.ModEq, Nat.mod_eq_of_lt hvlt]; exact hmod
  have hsum : x % 7 ^ (m + 1) + 7 ^ (m + 1)
      ≡ v.val * 7 ^ m + y % 7 ^ (m + 1) [MOD 7 ^ (m + 1)] := by
    have h2 := hcongr.add (Nat.ModEq.refl (y % 7 ^ (m + 1)))
    rwa [Nat.sub_add_cancel (by omega :
        y % 7 ^ (m + 1) ≤ x % 7 ^ (m + 1) + 7 ^ (m + 1))] at h2
  have hmodx : x % 7 ^ (m + 1) + 7 ^ (m + 1) ≡ x % 7 ^ (m + 1)
      [MOD 7 ^ (m + 1)] := by
    rw [Nat.ModEq, Nat.add_mod_right]
  have hfinal : x % 7 ^ (m + 1) ≡ v.val * 7 ^ m + y % 7 ^ (m + 1)
      [MOD 7 ^ (m + 1)] := hmodx.symm.trans hsum
  rw [Nat.ModEq] at hfinal
  rw [Nat.mod_eq_of_lt hxlt] at hfinal
  rw [hfinal, add_comm]

/-- For a `same` pair with pure-top difference `e = v·7^m`, the lower `m`
digits of `x` and `y` coincide (`lo(x) = lo(y)`). -/
private theorem pure_top_low_eq {m x y : ℕ} {v : ZMod 7}
    (hrel : residueRelOf x y = residueRel.same)
    (he : eMod7 m x y = v.val * 7 ^ m) :
    x % 7 ^ m = y % 7 ^ m := by
  have hres := pure_top_res_eq hrel he
  have hmodx : x % 7 ^ (m + 1) % 7 ^ m = x % 7 ^ m :=
    Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 7 (Nat.le_succ m))
  have hmody : y % 7 ^ (m + 1) % 7 ^ m = y % 7 ^ m :=
    Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 7 (Nat.le_succ m))
  have hvd : 7 ^ m ∣ v.val * 7 ^ m := dvd_mul_left _ _
  rw [← hmodx, hres,
    Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 7 (Nat.le_succ m)),
    Nat.add_mod, Nat.mod_eq_zero_of_dvd hvd, add_zero, Nat.mod_mod]
  exact hmody

/-- For a `twoX` pair with pure-top difference `e(x,y) = v·7^m`, the low
parts satisfy `2·lo(x) = lo(y) + δ·7^m` for a carry `δ ∈ {0,1}`, and the
digit expression is `ẽ = v − δ`. -/
private theorem pure_top_twoX {m x y : ℕ} {v : ZMod 7}
    (hrel : runit7 y = 2 * runit7 x)
    (he : eMod7 m x y = v.val * 7 ^ m) :
    ∃ δ : ℕ, δ < 2 ∧ 2 * (x % 7 ^ m) = y % 7 ^ m + δ * 7 ^ m ∧
      etd7 m x y = v - δ := by
  have hN : (0 : ℕ) < 7 ^ (m + 1) := Nat.pow_pos (by norm_num)
  have hNe : (7 : ℕ) ^ (m + 1) = 7 * 7 ^ m := pow_succ' 7 m
  obtain ⟨qx, fx, hX, hqx, hfx⟩ := residue_decomp (m := m) (x := x)
  obtain ⟨qy, fy, hY, hqy, hfy⟩ := residue_decomp (m := m) (x := y)
  have hfxm : x % 7 ^ m = fx := by
    have hmod : x % 7 ^ (m + 1) % 7 ^ m = x % 7 ^ m :=
      Nat.mod_mod_of_dvd x (Nat.pow_dvd_pow 7 (Nat.le_succ m))
    rw [← hmod, hX, add_comm (qx * 7 ^ m) fx,
      Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hfx]
  have hfym : y % 7 ^ m = fy := by
    have hmod : y % 7 ^ (m + 1) % 7 ^ m = y % 7 ^ m :=
      Nat.mod_mod_of_dvd y (Nat.pow_dvd_pow 7 (Nat.le_succ m))
    rw [← hmod, hY, add_comm (qy * 7 ^ m) fy,
      Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hfy]
  -- the wrapped `twoX` residue `W = 2·res_x + N − res_y`
  have hunf : eMod7 m x y
      = (2 * (x % 7 ^ (m + 1)) + 7 ^ (m + 1) - y % 7 ^ (m + 1))
        % 7 ^ (m + 1) := by
    unfold eMod7; rw [if_pos hrel]
  have hWmod : (2 * (x % 7 ^ (m + 1)) + 7 ^ (m + 1) - y % 7 ^ (m + 1))
      % 7 ^ (m + 1) = v.val * 7 ^ m := by
    rw [← hunf]; exact he
  have hsplit : (2 * (x % 7 ^ (m + 1)) + 7 ^ (m + 1)
      - y % 7 ^ (m + 1)) + y % 7 ^ (m + 1)
      = 2 * (x % 7 ^ (m + 1)) + 7 ^ (m + 1) := by
    have hb : y % 7 ^ (m + 1)
        ≤ 2 * (x % 7 ^ (m + 1)) + 7 ^ (m + 1) := by
      have := Nat.mod_lt y hN; omega
    omega
  -- carry part: `2·fx % 7^m = fy`
  have hmod7 : (2 * (x % 7 ^ (m + 1)) + 7 ^ (m + 1)
      - y % 7 ^ (m + 1)) % 7 ^ m = 0 := by
    rw [← Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 7 (Nat.le_succ m)),
      hWmod, Nat.mod_eq_zero_of_dvd (dvd_mul_left _ _)]
  have hcong : 2 * fx % 7 ^ m = fy := by
    have h1 : ((2 * (x % 7 ^ (m + 1)) + 7 ^ (m + 1)
        - y % 7 ^ (m + 1)) + y % 7 ^ (m + 1)) % 7 ^ m
        = (2 * (x % 7 ^ (m + 1)) + 7 ^ (m + 1)) % 7 ^ m := by
      rw [hsplit]
    rw [Nat.add_mod, hmod7, zero_add,
      Nat.mod_mod_of_dvd y (Nat.pow_dvd_pow 7 (Nat.le_succ m)),
      Nat.mod_mod, hfym] at h1
    rw [hX, hNe] at h1
    have h2 : (2 * (qx * 7 ^ m + fx) + 7 * 7 ^ m) % 7 ^ m
        = 2 * fx % 7 ^ m := by
      conv_lhs => rw [show 2 * (qx * 7 ^ m + fx) + 7 * 7 ^ m
          = 2 * fx + (2 * qx + 7) * 7 ^ m by ring]
      rw [Nat.add_mul_mod_self_right]
    rw [h2] at h1
    exact h1.symm
  -- `δ := 2fx / 7^m`, `2fx = fy + δ·7^m`, `δ < 2`
  obtain ⟨δ, hδeq, hδlt⟩ :
      ∃ δ : ℕ, 2 * fx = fy + δ * 7 ^ m ∧ δ < 2 := by
    refine ⟨2 * fx / 7 ^ m, ?_, ?_⟩
    · have h := Nat.div_add_mod (2 * fx) (7 ^ m)
      have hc : (2 * fx / 7 ^ m) * 7 ^ m = 7 ^ m * (2 * fx / 7 ^ m) :=
        mul_comm _ _
      omega
    · rw [Nat.div_lt_iff_lt_mul (Nat.pow_pos (by norm_num))]
      omega
  -- the digit part: `W = (2qx + 7 + δ − qy)·7^m`
  have hexp : (2 * qx + 7 + δ) * 7 ^ m
      = 2 * (qx * 7 ^ m) + 7 * 7 ^ m + δ * 7 ^ m := by ring
  have hWq : (2 * (x % 7 ^ (m + 1)) + 7 ^ (m + 1) - y % 7 ^ (m + 1))
      + qy * 7 ^ m = (2 * qx + 7 + δ) * 7 ^ m := by
    rw [hX, hY, hNe, hexp]
    have hq6 : qy * 7 ^ m ≤ 6 * 7 ^ m :=
      Nat.mul_le_mul (by omega : qy ≤ 6) (le_refl _)
    omega
  have hqyle : qy * 7 ^ m ≤ (2 * qx + 7 + δ) * 7 ^ m :=
    Nat.mul_le_mul (by omega : qy ≤ 2 * qx + 7 + δ) (le_refl _)
  have hWform : 2 * (x % 7 ^ (m + 1)) + 7 ^ (m + 1) - y % 7 ^ (m + 1)
      = (2 * qx + 7 + δ - qy) * 7 ^ m := by
    rw [Nat.sub_mul]
    omega
  have hv : (2 * qx + 7 + δ - qy) % 7 = v.val := by
    have hmod := hWmod
    rw [hWform, hNe, Nat.mul_mod_mul_right] at hmod
    exact Nat.mul_right_cancel (Nat.pow_pos (by norm_num)) hmod
  -- `etd = v − δ`
  have hetd : etd7 m x y = v - δ := by
    unfold etd7
    rw [if_pos hrel]
    have hqx' : qdig7 m x = (qx : ZMod 7) := by
      unfold qdig7; rw [hX, mul_pow_add_div hfx]
    have hqy' : qdig7 m y = (qy : ZMod 7) := by
      unfold qdig7; rw [hY, mul_pow_add_div hfy]
    rw [hqx', hqy']
    have hcast : ((2 * qx + 7 + δ - qy : ℕ) : ZMod 7) = v := by
      rw [← ZMod.natCast_zmod_val v, ← hv, ZMod.natCast_mod]
    have h7 : ((7 : ℕ) : ZMod 7) = 0 := by decide
    rw [natCast_sub_add (by omega : qy ≤ 2 * qx + 7 + δ), Nat.cast_add,
      Nat.cast_mul, Nat.cast_ofNat, h7] at hcast
    linear_combination hcast
  exact ⟨δ, hδlt, by rw [hfxm, hfym]; exact hδeq, hetd⟩

/-! ### §2c The `Λ₁` carry machinery -/

/-- `Λ₁` low-block decomposition: `(1+k·7^{m-1})·x mod 7^m` keeps the lower
`m−1` digits of `x` and puts `(x_{m-1}+k·x₀) mod 7` in position `m−1`. -/
private theorem c63_lo1 {m k x : ℕ} (hm : 1 ≤ m) :
    (1 + k * 7 ^ (m - 1)) * x % 7 ^ m
      = x % 7 ^ (m - 1) +
        ((x / 7 ^ (m - 1)) % 7 + k * (x % 7)) % 7 * 7 ^ (m - 1) := by
  have hm1 : 7 ^ m = 7 ^ (m - 1) * 7 := by
    rw [← pow_succ]; congr 1; omega
  have hP : (0 : ℕ) < 7 ^ (m - 1) := Nat.pow_pos (by norm_num)
  -- `x ≡ lo + x_{m-1}·P (mod 7·P)` via the mixed-radix strip
  have hxmod : x % (7 ^ (m - 1) * 7)
      = (x % 7 ^ (m - 1) + (x / 7 ^ (m - 1)) % 7 * 7 ^ (m - 1))
        % (7 ^ (m - 1) * 7) := by
    have hlt : x % 7 ^ (m - 1) + (x / 7 ^ (m - 1)) % 7 * 7 ^ (m - 1)
        < 7 ^ (m - 1) * 7 := by
      have h1 := Nat.mod_lt x hP
      have h2 : (x / 7 ^ (m - 1)) % 7 * 7 ^ (m - 1) ≤ 6 * 7 ^ (m - 1) :=
        Nat.mul_le_mul
          (Nat.le_of_lt_succ (Nat.mod_lt _ (show (0 : ℕ) < 7 by norm_num)))
          (le_refl _)
      omega
    rw [Nat.mod_eq_of_lt hlt]
    conv_lhs => rw [← Nat.div_add_mod (x % (7 ^ (m - 1) * 7)) (7 ^ (m - 1))]
    rw [Nat.mod_mod_of_dvd _ (dvd_mul_right _ _), mod_mul_div hP (by norm_num)]
    ring
  have he2 : x ≡ x % 7 ^ (m - 1) + (x / 7 ^ (m - 1)) % 7 * 7 ^ (m - 1)
      [MOD 7 ^ (m - 1) * 7] := hxmod
  have he3 : 7 ^ (m - 1) * (k * x) ≡ 7 ^ (m - 1) * (k * (x % 7))
      [MOD 7 ^ (m - 1) * 7] :=
    ((Nat.mod_modEq x 7).symm.mul_left k).mul_left' (7 ^ (m - 1))
  -- assemble: `λx ≡ lo + (x_{m-1} + k·x₀)·P`, then mod the coefficient
  have htot : (1 + k * 7 ^ (m - 1)) * x
      ≡ x % 7 ^ (m - 1)
        + ((x / 7 ^ (m - 1)) % 7 + k * (x % 7)) % 7 * 7 ^ (m - 1)
        [MOD 7 ^ (m - 1) * 7] := by
    have e' : (1 + k * 7 ^ (m - 1)) * x = x + 7 ^ (m - 1) * (k * x) := by ring
    rw [e']
    have step1 := he2.add he3
    rw [show x % 7 ^ (m - 1) + (x / 7 ^ (m - 1)) % 7 * 7 ^ (m - 1)
        + 7 ^ (m - 1) * (k * (x % 7))
        = x % 7 ^ (m - 1)
          + ((x / 7 ^ (m - 1)) % 7 + k * (x % 7)) * 7 ^ (m - 1) by ring]
      at step1
    have e6 : ((x / 7 ^ (m - 1)) % 7 + k * (x % 7)) * 7 ^ (m - 1)
        ≡ ((x / 7 ^ (m - 1)) % 7 + k * (x % 7)) % 7 * 7 ^ (m - 1)
        [MOD 7 ^ (m - 1) * 7] := by
      have h := (Nat.mod_modEq ((x / 7 ^ (m - 1)) % 7 + k * (x % 7)) 7).symm.mul_left'
        (7 ^ (m - 1))
      rwa [mul_comm (7 ^ (m - 1))
          (((x / 7 ^ (m - 1)) % 7 + k * (x % 7)) % 7),
        mul_comm (7 ^ (m - 1)) ((x / 7 ^ (m - 1)) % 7 + k * (x % 7))] at h
    exact step1.trans ((Nat.ModEq.refl _).add e6)
  -- both sides reduced: `(λx) % (7P) = (lo + A·P) % (7P) = lo + A·P`
  rw [hm1]
  have hlt' : x % 7 ^ (m - 1)
      + ((x / 7 ^ (m - 1)) % 7 + k * (x % 7)) % 7 * 7 ^ (m - 1)
      < 7 ^ (m - 1) * 7 := by
    have h1 := Nat.mod_lt x hP
    have h2 : ((x / 7 ^ (m - 1)) % 7 + k * (x % 7)) % 7 * 7 ^ (m - 1)
        ≤ 6 * 7 ^ (m - 1) :=
      Nat.mul_le_mul
        (Nat.le_of_lt_succ (Nat.mod_lt _ (show (0 : ℕ) < 7 by norm_num)))
        (le_refl _)
    omega
  calc (1 + k * 7 ^ (m - 1)) * x % (7 ^ (m - 1) * 7)
      = (x % 7 ^ (m - 1)
        + ((x / 7 ^ (m - 1)) % 7 + k * (x % 7)) % 7 * 7 ^ (m - 1))
        % (7 ^ (m - 1) * 7) := htot
    _ = _ := Nat.mod_eq_of_lt hlt'

/-- One `Λ₁` carry step on a pure-top `twoX` difference `e(x,y) = v·7^m`.
Write `A = (x_{m-1}+k·x₀) % 7` (the new `m−1` digit of `x`) and
`β = ⌊2·x_{<m-1}/7^{m-1}⌋ ∈ {0,1}`.  Then (i) `y_{<m-1} = 2·x_{<m-1} mod
7^{m-1}`; (ii) the new `m−1` digit of `y` is `(β+2A) % 7`; (iii)
`ẽ(λx,λy) = v − ⌊(β+2A)/7⌋`. -/
private theorem c63_eps_pair {m k x y : ℕ} (hm : 2 ≤ m) {v : ZMod 7}
    (hrel : runit7 y = 2 * runit7 x) (he : eMod7 m x y = v.val * 7 ^ m) :
    y % 7 ^ (m - 1) = (2 * (x % 7 ^ (m - 1))) % 7 ^ (m - 1) ∧
      ((y / 7 ^ (m - 1)) % 7 + k * (y % 7)) % 7 =
        (2 * (x % 7 ^ (m - 1)) / 7 ^ (m - 1)
          + 2 * (((x / 7 ^ (m - 1)) % 7 + k * (x % 7)) % 7)) % 7 ∧
      etd7 m ((1 + k * 7 ^ (m - 1)) * x) ((1 + k * 7 ^ (m - 1)) * y)
        = v - ((2 * (x % 7 ^ (m - 1)) / 7 ^ (m - 1)
          + 2 * (((x / 7 ^ (m - 1)) % 7 + k * (x % 7)) % 7)) / 7 : ℕ) := by
  have hP : (0 : ℕ) < 7 ^ (m - 1) := Nat.pow_pos (by norm_num)
  have hPm : (0 : ℕ) < 7 ^ m := Nat.pow_pos (by norm_num)
  have h7P : 7 ^ m = 7 * 7 ^ (m - 1) := by
    conv_lhs => rw [show m = m - 1 + 1 by omega]
    exact pow_succ' 7 (m - 1)
  have h7dP : (7 : ℕ) ∣ 7 ^ (m - 1) := dvd_pow_self 7 (by omega)
  have hPP : 7 ^ (m - 1) ∣ 7 ^ m := Nat.pow_dvd_pow 7 (by omega : m - 1 ≤ m)
  obtain ⟨δ, hδlt, hδeq, -⟩ := pure_top_twoX hrel he
  -- `x % 7^m = lo_x + c3·P` (mixed-radix strip)
  have hxm : x % 7 ^ m = x % 7 ^ (m - 1)
      + (x / 7 ^ (m - 1)) % 7 * 7 ^ (m - 1) := by
    have hP7 : 7 ^ m = 7 ^ (m - 1) * 7 := by rw [h7P]; ring
    rw [hP7]
    conv_lhs => rw [← Nat.div_add_mod (x % (7 ^ (m - 1) * 7)) (7 ^ (m - 1))]
    rw [Nat.mod_mod_of_dvd _ (dvd_mul_right _ _), mod_mul_div hP (by norm_num)]
    ring
  have hym : y % 7 ^ m = y % 7 ^ (m - 1)
      + (y / 7 ^ (m - 1)) % 7 * 7 ^ (m - 1) := by
    have hP7 : 7 ^ m = 7 ^ (m - 1) * 7 := by rw [h7P]; ring
    rw [hP7]
    conv_lhs => rw [← Nat.div_add_mod (y % (7 ^ (m - 1) * 7)) (7 ^ (m - 1))]
    rw [Nat.mod_mod_of_dvd _ (dvd_mul_right _ _), mod_mul_div hP (by norm_num)]
    ring
  -- (i) `lo_y = 2·lo_x mod P`: reduce `2·x%7^m = y%7^m + δ·7^m` mod `P`
  have hpart1 : y % 7 ^ (m - 1) = (2 * (x % 7 ^ (m - 1))) % 7 ^ (m - 1) := by
    have hdvd : 7 ^ (m - 1) ∣ δ * 7 ^ m := dvd_mul_of_dvd_right hPP δ
    have h0 : 2 * (x % 7 ^ m) ≡ y % 7 ^ m [MOD 7 ^ (m - 1)] := by
      have hstep : 2 * (x % 7 ^ m) ≡ y % 7 ^ m + δ * 7 ^ m
          [MOD 7 ^ (m - 1)] := by
        rw [hδeq]
      have hz : δ * 7 ^ m ≡ 0 [MOD 7 ^ (m - 1)] :=
        Nat.modEq_zero_iff_dvd.mpr hdvd
      have h := hstep.trans ((Nat.ModEq.refl _).add hz)
      rwa [add_zero] at h
    have hx : x % 7 ^ m ≡ x % 7 ^ (m - 1) [MOD 7 ^ (m - 1)] := by
      rw [Nat.ModEq, Nat.mod_mod]
      exact Nat.mod_mod_of_dvd _ hPP
    have hy : y % 7 ^ m ≡ y % 7 ^ (m - 1) [MOD 7 ^ (m - 1)] := by
      rw [Nat.ModEq, Nat.mod_mod]
      exact Nat.mod_mod_of_dvd _ hPP
    have hfin := (((hx.mul_left 2).symm.trans h0).trans hy)
    rw [Nat.ModEq, Nat.mod_mod] at hfin
    exact hfin.symm
  -- `2·lo_x = β·P + lo_y` where `β = 2·lo_x / P`
  have h2lx : 2 * (x % 7 ^ (m - 1))
      = 7 ^ (m - 1) * (2 * (x % 7 ^ (m - 1)) / 7 ^ (m - 1))
        + y % 7 ^ (m - 1) := by
    have h := Nat.div_add_mod (2 * (x % 7 ^ (m - 1))) (7 ^ (m - 1))
    rw [← hpart1] at h
    omega
  -- divide the carry identity by `P`: `β + 2·c3 = c4 + 7δ`
  have hδeq' : 2 * (x % 7 ^ (m - 1))
      + 2 * ((x / 7 ^ (m - 1)) % 7) * 7 ^ (m - 1)
      = y % 7 ^ (m - 1) + (y / 7 ^ (m - 1)) % 7 * 7 ^ (m - 1)
        + δ * (7 * 7 ^ (m - 1)) := by
    rw [hxm, hym, h7P] at hδeq
    linear_combination hδeq
  have hmain : 7 ^ (m - 1) * (2 * (x % 7 ^ (m - 1)) / 7 ^ (m - 1)
      + 2 * ((x / 7 ^ (m - 1)) % 7))
      = 7 ^ (m - 1) * ((y / 7 ^ (m - 1)) % 7 + 7 * δ) := by
    linear_combination hδeq' - h2lx
  have hcb : 2 * (x % 7 ^ (m - 1)) / 7 ^ (m - 1) + 2 * ((x / 7 ^ (m - 1)) % 7)
      = (y / 7 ^ (m - 1)) % 7 + 7 * δ := Nat.mul_left_cancel hP hmain
  have hc4 : (y / 7 ^ (m - 1)) % 7
      = (2 * (x % 7 ^ (m - 1)) / 7 ^ (m - 1)
        + 2 * ((x / 7 ^ (m - 1)) % 7)) % 7 := by
    have h := congrArg (· % 7) hcb
    rw [Nat.add_mul_mod_self_left, Nat.mod_mod] at h
    exact h.symm
  have hy0 : y % 7 = (2 * (x % 7)) % 7 := by
    have h := congrArg (· % 7) hpart1
    rw [Nat.mod_mod_of_dvd _ h7dP, Nat.mod_mod_of_dvd _ h7dP] at h
    have h' : x % 7 ^ (m - 1) ≡ x % 7 [MOD 7] := by
      rw [Nat.ModEq, Nat.mod_mod]
      exact Nat.mod_mod_of_dvd _ h7dP
    have h'' := h'.mul_left 2
    rw [Nat.ModEq] at h''
    rw [h]
    exact h''
  -- (ii) `A_y = (β + 2·A3) % 7` via the mod-7 congruence chain
  have hpart2 : ((y / 7 ^ (m - 1)) % 7 + k * (y % 7)) % 7
      = (2 * (x % 7 ^ (m - 1)) / 7 ^ (m - 1)
        + 2 * (((x / 7 ^ (m - 1)) % 7 + k * (x % 7)) % 7)) % 7 := by
    have hc4m : (y / 7 ^ (m - 1)) % 7
        ≡ 2 * (x % 7 ^ (m - 1)) / 7 ^ (m - 1) + 2 * ((x / 7 ^ (m - 1)) % 7)
          [MOD 7] := by
      rw [Nat.ModEq, Nat.mod_mod]; exact hc4
    have hy0m : y % 7 ≡ 2 * (x % 7) [MOD 7] := by
      rw [Nat.ModEq, Nat.mod_mod]; exact hy0
    have hA3m : (x / 7 ^ (m - 1)) % 7 + k * (x % 7)
        ≡ ((x / 7 ^ (m - 1)) % 7 + k * (x % 7)) % 7 [MOD 7] :=
      (Nat.mod_modEq _ _).symm
    have h1 := hc4m.add (hy0m.mul_left k)
    rw [show 2 * (x % 7 ^ (m - 1)) / 7 ^ (m - 1) + 2 * ((x / 7 ^ (m - 1)) % 7)
        + k * (2 * (x % 7))
        = 2 * (x % 7 ^ (m - 1)) / 7 ^ (m - 1)
          + 2 * ((x / 7 ^ (m - 1)) % 7 + k * (x % 7)) by ring] at h1
    have h2 := (hA3m.mul_left 2).add_left
      (2 * (x % 7 ^ (m - 1)) / 7 ^ (m - 1))
    show (y / 7 ^ (m - 1)) % 7 + k * (y % 7)
        ≡ 2 * (x % 7 ^ (m - 1)) / 7 ^ (m - 1)
          + 2 * (((x / 7 ^ (m - 1)) % 7 + k * (x % 7)) % 7) [MOD 7]
    exact h1.trans h2
  -- (iii) `ẽ(λx,λy) = v − δ'` via `pure_top_twoX` on the transformed pair
  have hlamr : runit7 (1 + k * 7 ^ (m - 1)) = 1 := runit7_multLow (by omega)
  have hrel' : runit7 ((1 + k * 7 ^ (m - 1)) * y)
      = 2 * runit7 ((1 + k * 7 ^ (m - 1)) * x) := by
    rw [runit7_mul, runit7_mul, hlamr, one_mul, one_mul]; exact hrel
  have he' : eMod7 m ((1 + k * 7 ^ (m - 1)) * x) ((1 + k * 7 ^ (m - 1)) * y)
      = v.val * 7 ^ m := by
    rw [eMod7_mul hlamr, he]
    exact lambda1_top_resid hm (ZMod.val_lt v)
  obtain ⟨δ2, hδ2lt, hδ2eq, hetd2⟩ := pure_top_twoX hrel' he'
  have hδ'eq : 2 * ((1 + k * 7 ^ (m - 1)) * x % 7 ^ m)
      = (1 + k * 7 ^ (m - 1)) * y % 7 ^ m
        + (2 * (x % 7 ^ (m - 1)) / 7 ^ (m - 1)
          + 2 * (((x / 7 ^ (m - 1)) % 7 + k * (x % 7)) % 7)) / 7 * 7 ^ m := by
    have hlo1 := c63_lo1 (by omega : 1 ≤ m) (k := k) (x := x)
    have hlo2 := c63_lo1 (by omega : 1 ≤ m) (k := k) (x := y)
    rw [hlo1, hlo2, hpart2, h7P]
    have hB : (2 * (x % 7 ^ (m - 1)) / 7 ^ (m - 1)
        + 2 * (((x / 7 ^ (m - 1)) % 7 + k * (x % 7)) % 7))
        = (2 * (x % 7 ^ (m - 1)) / 7 ^ (m - 1)
          + 2 * (((x / 7 ^ (m - 1)) % 7 + k * (x % 7)) % 7)) / 7 * 7
          + (2 * (x % 7 ^ (m - 1)) / 7 ^ (m - 1)
            + 2 * (((x / 7 ^ (m - 1)) % 7 + k * (x % 7)) % 7)) % 7 := by
      have h := Nat.div_add_mod (2 * (x % 7 ^ (m - 1)) / 7 ^ (m - 1)
        + 2 * (((x / 7 ^ (m - 1)) % 7 + k * (x % 7)) % 7)) 7
      omega
    linear_combination h2lx + 7 ^ (m - 1) * hB
  have hδ2 : δ2 = (2 * (x % 7 ^ (m - 1)) / 7 ^ (m - 1)
      + 2 * (((x / 7 ^ (m - 1)) % 7 + k * (x % 7)) % 7)) / 7 := by
    have hqq : δ2 * 7 ^ m = (2 * (x % 7 ^ (m - 1)) / 7 ^ (m - 1)
        + 2 * (((x / 7 ^ (m - 1)) % 7 + k * (x % 7)) % 7)) / 7 * 7 ^ m := by
      omega
    exact Nat.mul_right_cancel hPm hqq
  rw [hδ2] at hetd2
  exact ⟨hpart1, hpart2, hetd2⟩

/-! ### §3 The `lemma5` finish bridge -/

/-- Realize a `ZMod 7` shift-avoidance (on the three class-images of the
`lam₁`-scaled union) by a `Λ₀` element; composition gives `good7`. -/
private theorem c63_of_avoid {m : ℕ} (hm : 0 < m) {A1 A2 A4 : Finset ℕ}
    (hpos : ∀ d ∈ A1 ∪ A2 ∪ A4, 0 < d)
    (hunit : ∀ d ∈ A1 ∪ A2 ∪ A4, padicValNat 7 d = 0)
    {s : ZMod 7} (hs : s ≠ 0)
    (hcls1 : ∀ d ∈ A1, runit7 d = s)
    (hcls2 : ∀ d ∈ A2, runit7 d = 2 * s)
    (hcls4 : ∀ d ∈ A4, runit7 d = 4 * s)
    {lam₁ : ℕ} (hlam₁ : ¬ 7 ∣ lam₁)
    {t : ZMod 7}
    (h : avoids06
      (((A1.image fun d => lam₁ * d).image (qdig7 m)).image (· + t)
        ∪ ((A2.image fun d => lam₁ * d).image (qdig7 m)).image (· + 2 * t)
        ∪ ((A4.image fun d => lam₁ * d).image (qdig7 m)).image (· + 4 * t))) :
    ∃ lam : ℕ, ¬ 7 ∣ lam ∧ good7 m lam (A1 ∪ A2 ∪ A4) := by
  classical
  set B := (A1 ∪ A2 ∪ A4).image (fun d => lam₁ * d) with hB
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
    rcases Finset.mem_union.mp hd₀ with hd₁₂ | hd₄
    · rcases Finset.mem_union.mp hd₁₂ with hd₁ | hd₂
      · rw [hcls1 d₀ hd₁]
        exact Finset.mem_insert_self _ _
      · rw [hcls2 d₀ hd₂]
        have : runit7 lam₁ * (2 * s) = 2 * s' := by rw [hs']; ring
        rw [this]
        exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    · rw [hcls4 d₀ hd₄]
      have : runit7 lam₁ * (4 * s) = 4 * s' := by rw [hs']; ring
      rw [this]
      exact Finset.mem_insert_of_mem
        (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  -- the three class filters on `B`
  have hfilt1 : (B.filter fun d => runit7 d = s').image (qdig7 m)
      = (A1.image fun d => lam₁ * d).image (qdig7 m) := by
    have hf : B.filter (fun d => runit7 d = s')
        = A1.image (fun d => lam₁ * d) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨hB', hr⟩
        obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hB'
        rw [runit7_mul, hs'] at hr
        have hrd : runit7 d = s := mul_left_cancel₀ hrl1 hr
        rcases Finset.mem_union.mp hd with hd₁₂ | hd₄
        · rcases Finset.mem_union.mp hd₁₂ with hd₁ | hd₂
          · exact ⟨d, hd₁, rfl⟩
          · rw [hcls2 d hd₂] at hrd
            exact absurd (by linear_combination hrd) hs
        · rw [hcls4 d hd₄] at hrd
          have hz : (3 : ZMod 7) * s = 0 := by linear_combination hrd
          rcases mul_eq_zero.mp hz with h3 | h0
          · exact absurd h3 (by decide)
          · exact absurd h0 hs
      · rintro ⟨d, hd₁, rfl⟩
        exact ⟨Finset.mem_image.mpr ⟨d,
          Finset.mem_union_left _ (Finset.mem_union_left _ hd₁), rfl⟩,
          by rw [runit7_mul, hcls1 d hd₁, hs']⟩
    rw [hf]
  have hfilt2 : (B.filter fun d => runit7 d = 2 * s').image (qdig7 m)
      = (A2.image fun d => lam₁ * d).image (qdig7 m) := by
    have hf : B.filter (fun d => runit7 d = 2 * s')
        = A2.image (fun d => lam₁ * d) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨hB', hr⟩
        obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hB'
        rw [runit7_mul, hs'] at hr
        have hrd : runit7 d = 2 * s := by
          have hr' : runit7 lam₁ * runit7 d = runit7 lam₁ * (2 * s) := by
            rw [hr]; ring
          exact mul_left_cancel₀ hrl1 hr'
        rcases Finset.mem_union.mp hd with hd₁₂ | hd₄
        · rcases Finset.mem_union.mp hd₁₂ with hd₁ | hd₂
          · rw [hcls1 d hd₁] at hrd
            exact absurd (by linear_combination -hrd) hs
          · exact ⟨d, hd₂, rfl⟩
        · rw [hcls4 d hd₄] at hrd
          have hz : (2 : ZMod 7) * s = 0 := by linear_combination hrd
          rcases mul_eq_zero.mp hz with h2 | h0
          · exact absurd h2 (by decide)
          · exact absurd h0 hs
      · rintro ⟨d, hd₂, rfl⟩
        exact ⟨Finset.mem_image.mpr ⟨d,
          Finset.mem_union_left _ (Finset.mem_union_right _ hd₂), rfl⟩,
          by rw [runit7_mul, hcls2 d hd₂, hs']; ring⟩
    rw [hf]
  have hfilt4 : (B.filter fun d => runit7 d = 4 * s').image (qdig7 m)
      = (A4.image fun d => lam₁ * d).image (qdig7 m) := by
    have hf : B.filter (fun d => runit7 d = 4 * s')
        = A4.image (fun d => lam₁ * d) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨hB', hr⟩
        obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hB'
        rw [runit7_mul, hs'] at hr
        have hrd : runit7 d = 4 * s := by
          have hr' : runit7 lam₁ * runit7 d = runit7 lam₁ * (4 * s) := by
            rw [hr]; ring
          exact mul_left_cancel₀ hrl1 hr'
        rcases Finset.mem_union.mp hd with hd₁₂ | hd₄
        · rcases Finset.mem_union.mp hd₁₂ with hd₁ | hd₂
          · rw [hcls1 d hd₁] at hrd
            have hz : (3 : ZMod 7) * s = 0 := by linear_combination -hrd
            rcases mul_eq_zero.mp hz with h3 | h0
            · exact absurd h3 (by decide)
            · exact absurd h0 hs
          · rw [hcls2 d hd₂] at hrd
            have hz : (2 : ZMod 7) * s = 0 := by linear_combination -hrd
            rcases mul_eq_zero.mp hz with h2 | h0
            · exact absurd h2 (by decide)
            · exact absurd h0 hs
        · exact ⟨d, hd₄, rfl⟩
      · rintro ⟨d, hd₄, rfl⟩
        exact ⟨Finset.mem_image.mpr ⟨d, Finset.mem_union_right _ hd₄, rfl⟩,
          by rw [runit7_mul, hcls4 d hd₄, hs']; ring⟩
    rw [hf]
  have hunion :
      ((B.filter fun d => runit7 d = s').image (qdig7 m)).image (· + t)
        ∪ ((B.filter fun d => runit7 d = 2 * s').image (qdig7 m)).image
          (· + 2 * t)
        ∪ ((B.filter fun d => runit7 d = 4 * s').image (qdig7 m)).image
          (· + 4 * t)
      = ((A1.image fun d => lam₁ * d).image (qdig7 m)).image (· + t)
        ∪ ((A2.image fun d => lam₁ * d).image (qdig7 m)).image (· + 2 * t)
        ∪ ((A4.image fun d => lam₁ * d).image (qdig7 m)).image (· + 4 * t) := by
    rw [hfilt1, hfilt2, hfilt4]
  obtain ⟨lam0, hlam0mem, hgood0⟩ :=
    exists_lambda0_of_shift hm hs'0 hunitB hclsB t (hunion.symm ▸ h)
  refine ⟨lam0 * lam₁,
    Nat.prime_seven.not_dvd_mul (not_dvd_of_mem_multLow7_zero hm hlam0mem)
      hlam₁, ?_⟩
  exact good7_mul hgood0

/-- `lemma5` finish when `apLen X₁ ≤ 2`: the exceptional `(3,1,1)` case
cannot occur, so a shift always exists. -/
private theorem c63_tail2 {m : ℕ} (hm : 0 < m) {A1 A2 A4 : Finset ℕ}
    (hpos : ∀ d ∈ A1 ∪ A2 ∪ A4, 0 < d)
    (hunit : ∀ d ∈ A1 ∪ A2 ∪ A4, padicValNat 7 d = 0)
    {s : ZMod 7} (hs : s ≠ 0)
    (hcls1 : ∀ d ∈ A1, runit7 d = s)
    (hcls2 : ∀ d ∈ A2, runit7 d = 2 * s)
    (hcls4 : ∀ d ∈ A4, runit7 d = 4 * s)
    (hA2 : A2.card = 1) (hA4 : A4.card = 1) (hne1 : A1.Nonempty)
    {lam₁ : ℕ} (hlam₁ : ¬ 7 ∣ lam₁)
    (h2 : apLen ((A1.image fun d => lam₁ * d).image (qdig7 m)) ≤ 2) :
    ∃ lam : ℕ, ¬ 7 ∣ lam ∧ good7 m lam (A1 ∪ A2 ∪ A4) := by
  classical
  set X1 := (A1.image fun d => lam₁ * d).image (qdig7 m) with hX1
  set X2 := (A2.image fun d => lam₁ * d).image (qdig7 m) with hX2
  set X4 := (A4.image fun d => lam₁ * d).image (qdig7 m) with hX4
  have hcardX2 : X2.card ≤ 1 :=
    le_trans Finset.card_image_le (le_trans Finset.card_image_le (le_of_eq hA2))
  have hcardX4 : X4.card ≤ 1 :=
    le_trans Finset.card_image_le (le_trans Finset.card_image_le (le_of_eq hA4))
  have hX1ne : X1.Nonempty :=
    Finset.Nonempty.image (Finset.Nonempty.image hne1 _) _
  have hapX2 : apLen X2 ≤ 1 := by
    rcases X2.eq_empty_or_nonempty with hX | hX
    · rw [hX]
      exact (apLen_le_iff _ 1 (by norm_num)).mpr ⟨0, Finset.empty_subset _⟩
    · obtain ⟨a, ha⟩ :=
        Finset.card_eq_one.mp (le_antisymm hcardX2 (Finset.card_pos.mpr hX))
      rw [ha]
      exact apLen_singleton_le1 a
  have hapX4 : apLen X4 ≤ 1 := by
    rcases X4.eq_empty_or_nonempty with hX | hX
    · rw [hX]
      exact (apLen_le_iff _ 1 (by norm_num)).mpr ⟨0, Finset.empty_subset _⟩
    · obtain ⟨a, ha⟩ :=
        Finset.card_eq_one.mp (le_antisymm hcardX4 (Finset.card_pos.mpr hX))
      rw [ha]
      exact apLen_singleton_le1 a
  have hapX1 : 1 ≤ apLen X1 := apLen_pos_of_nonempty hX1ne
  have hsum : apLen X1 + apLen X2 + apLen X4 ≤ 5 := by omega
  have hord : apLen X2 ≤ apLen X1 ∧ apLen X4 ≤ apLen X1 := ⟨by omega, by omega⟩
  obtain ⟨t, ht⟩ | ⟨hl1, -, -, -⟩ := lemma5 1 (by decide) hord hsum
  · exact c63_of_avoid hm hpos hunit hs hcls1 hcls2 hcls4 hlam₁ ht
  · omega

/-- `lemma5` finish when `apLen X₁ ≤ 3`: the exceptional `(3,1,1)`
configuration is killed by the `ẽ(d₄,d₅) ∉ {2,4}` side-condition. -/
private theorem c63_tail3 {m : ℕ} (hm : 0 < m) {A1 A2 A4 : Finset ℕ}
    (hpos : ∀ d ∈ A1 ∪ A2 ∪ A4, 0 < d)
    (hunit : ∀ d ∈ A1 ∪ A2 ∪ A4, padicValNat 7 d = 0)
    {s : ZMod 7} (hs : s ≠ 0)
    (hcls1 : ∀ d ∈ A1, runit7 d = s)
    (hcls2 : ∀ d ∈ A2, runit7 d = 2 * s)
    (hcls4 : ∀ d ∈ A4, runit7 d = 4 * s)
    (hA2 : A2.card = 1) (hA4 : A4.card = 1) (hne1 : A1.Nonempty)
    {lam₁ : ℕ} (hlam₁ : ¬ 7 ∣ lam₁)
    (h3 : apLen ((A1.image fun d => lam₁ * d).image (qdig7 m)) ≤ 3)
    (hcond : ∀ d₄ ∈ A2, ∀ d₅ ∈ A4,
      (2 * qdig7 m (lam₁ * d₄) - qdig7 m (lam₁ * d₅) : ZMod 7)
        ∉ ({2, 4} : Finset (ZMod 7))) :
    ∃ lam : ℕ, ¬ 7 ∣ lam ∧ good7 m lam (A1 ∪ A2 ∪ A4) := by
  classical
  set X1 := (A1.image fun d => lam₁ * d).image (qdig7 m) with hX1
  set X2 := (A2.image fun d => lam₁ * d).image (qdig7 m) with hX2
  set X4 := (A4.image fun d => lam₁ * d).image (qdig7 m) with hX4
  have hcardX2 : X2.card ≤ 1 :=
    le_trans Finset.card_image_le (le_trans Finset.card_image_le (le_of_eq hA2))
  have hcardX4 : X4.card ≤ 1 :=
    le_trans Finset.card_image_le (le_trans Finset.card_image_le (le_of_eq hA4))
  have hX1ne : X1.Nonempty :=
    Finset.Nonempty.image (Finset.Nonempty.image hne1 _) _
  have hapX2 : apLen X2 ≤ 1 := by
    rcases X2.eq_empty_or_nonempty with hX | hX
    · rw [hX]
      exact (apLen_le_iff _ 1 (by norm_num)).mpr ⟨0, Finset.empty_subset _⟩
    · obtain ⟨a, ha⟩ :=
        Finset.card_eq_one.mp (le_antisymm hcardX2 (Finset.card_pos.mpr hX))
      rw [ha]
      exact apLen_singleton_le1 a
  have hapX4 : apLen X4 ≤ 1 := by
    rcases X4.eq_empty_or_nonempty with hX | hX
    · rw [hX]
      exact (apLen_le_iff _ 1 (by norm_num)).mpr ⟨0, Finset.empty_subset _⟩
    · obtain ⟨a, ha⟩ :=
        Finset.card_eq_one.mp (le_antisymm hcardX4 (Finset.card_pos.mpr hX))
      rw [ha]
      exact apLen_singleton_le1 a
  have hapX1 : 1 ≤ apLen X1 := apLen_pos_of_nonempty hX1ne
  have hsum : apLen X1 + apLen X2 + apLen X4 ≤ 5 := by omega
  have hord : apLen X2 ≤ apLen X1 ∧ apLen X4 ≤ apLen X1 := ⟨by omega, by omega⟩
  obtain ⟨t, ht⟩ | ⟨-, -, -, hexc⟩ := lemma5 1 (by decide) hord hsum
  · exact c63_of_avoid hm hpos hunit hs hcls1 hcls2 hcls4 hlam₁ ht
  · exfalso
    obtain ⟨d₄, hd₄⟩ : A2.Nonempty :=
      Finset.card_pos.mp (by rw [hA2]; norm_num)
    obtain ⟨d₅, hd₅⟩ : A4.Nonempty :=
      Finset.card_pos.mp (by rw [hA4]; norm_num)
    have hmem2 : qdig7 m (lam₁ * d₄) ∈ X2 :=
      Finset.mem_image.mpr ⟨lam₁ * d₄,
        Finset.mem_image.mpr ⟨d₄, hd₄, rfl⟩, rfl⟩
    have hmem4 : qdig7 m (lam₁ * d₅) ∈ X4 :=
      Finset.mem_image.mpr ⟨lam₁ * d₅,
        Finset.mem_image.mpr ⟨d₅, hd₅, rfl⟩, rfl⟩
    exact hcond d₄ hd₄ d₅ hd₅ (hexc _ hmem2 _ hmem4)

/-- The `Λ₁` carry chain on a `twoX` pair of pure-top differences:
`ẽ(λd₃,λd₄) = v34 − δ34'` and `ẽ(λd₄,λd₅) = v45 − δ45'` with the explicit
floor-corrected carries from `c63_eps_pair`. -/
private theorem eps_chain {m k d₃ d₄ d₅ : ℕ} (hm : 2 ≤ m)
    (hrel34 : runit7 d₄ = 2 * runit7 d₃)
    (hrel45 : runit7 d₅ = 2 * runit7 d₄)
    {v34 v45 : ZMod 7}
    (he34 : eMod7 m d₃ d₄ = v34.val * 7 ^ m)
    (he45 : eMod7 m d₄ d₅ = v45.val * 7 ^ m) :
    etd7 m ((1 + k * 7 ^ (m - 1)) * d₃) ((1 + k * 7 ^ (m - 1)) * d₄)
      = v34 - ((2 * (d₃ % 7 ^ (m - 1)) / 7 ^ (m - 1)
        + 2 * (((d₃ / 7 ^ (m - 1)) % 7 + k * (d₃ % 7)) % 7)) / 7 : ℕ) ∧
    etd7 m ((1 + k * 7 ^ (m - 1)) * d₄) ((1 + k * 7 ^ (m - 1)) * d₅)
      = v45 - ((2 * (d₄ % 7 ^ (m - 1)) / 7 ^ (m - 1)
        + 2 * (((d₄ / 7 ^ (m - 1)) % 7 + k * (d₄ % 7)) % 7)) / 7 : ℕ) ∧
    ((d₄ / 7 ^ (m - 1)) % 7 + k * (d₄ % 7)) % 7
      = (2 * (d₃ % 7 ^ (m - 1)) / 7 ^ (m - 1)
        + 2 * (((d₃ / 7 ^ (m - 1)) % 7 + k * (d₃ % 7)) % 7)) % 7 := by
  obtain ⟨-, hAy, hetd34⟩ := c63_eps_pair hm hrel34 he34
  obtain ⟨-, -, hetd45⟩ := c63_eps_pair hm hrel45 he45
  exact ⟨hetd34, hetd45, hAy⟩

/-- `single_carry`: the `Λ₁`-shift digit of a `7`-unit can be prescribed.
Since `x % 7` is a unit, `k ↦ (c + k·u₀) mod 7` is a bijection, so some
`k < 7` realizes any target `w < 7` (the paper's `w = 4ε₁ + 2ε₂`). -/
private theorem single_carry {m x : ℕ} (hxp : 0 < x) (hx : padicValNat 7 x = 0)
    {w : ℕ} (hw : w < 7) :
    ∃ k : ℕ, k < 7 ∧ ((x / 7 ^ (m - 1)) % 7 + k * (x % 7)) % 7 = w := by
  have hu : ((x % 7 : ℕ) : ZMod 7) ≠ 0 := by
    have hr : runit7 x ≠ 0 := runit7_ne_zero hxp
    rw [runit7_of_padic_zero hx] at hr
    rwa [ZMod.natCast_mod]
  set c : ZMod 7 := (((x / 7 ^ (m - 1)) % 7 : ℕ) : ZMod 7) with hc
  set u : ZMod 7 := ((x % 7 : ℕ) : ZMod 7) with hu'
  set k0 : ℕ := (((w : ZMod 7) - c) * u⁻¹).val with hk0
  refine ⟨k0, ZMod.val_lt _, ?_⟩
  have hk : ((k0 : ℕ) : ZMod 7) = (w - c) * u⁻¹ := by
    rw [hk0]
    exact ZMod.natCast_zmod_val _
  have hcongr : (((x / 7 ^ (m - 1)) % 7 + k0 * (x % 7) : ℕ) : ZMod 7)
      = (w : ZMod 7) := by
    rw [Nat.cast_add, Nat.cast_mul, hk, ← hu']
    have hu'' : u⁻¹ * u = 1 := inv_mul_cancel₀ hu
    calc (((x / 7 ^ (m - 1)) % 7 : ℕ) : ZMod 7) + ((w : ZMod 7) - c) * u⁻¹ * u
        = c + ((w : ZMod 7) - c) * (u⁻¹ * u) := by rw [← hc, mul_assoc]
      _ = c + (w - c) := by rw [hu'', mul_one]
      _ = w := by ring
  have hfin : ((x / 7 ^ (m - 1)) % 7 + k0 * (x % 7)) % 7 = w % 7 := by
    have hmod := (ZMod.natCast_eq_natCast_iff' _ _ _).mp hcongr
    exact hmod
  rwa [Nat.mod_eq_of_lt hw] at hfin

/-- `c63_l9ii3` — the `j = 3` case of `lemma9_ii` with the multiplier
*form* exposed: the returned `λ = 1 + k·7^{m−h}` (`k < 7`) is the
`Λ_h` realizer needed for the order-of-application arguments in the
`(ii.2)` `h < m` branch (the abstract `lemma9_ii` hides `λ`'s shape). -/
private theorem c63_l9ii3 {m : ℕ} {b1 b2 b3 : ℕ}
    (hpos : 0 < b1 ∧ 0 < b2 ∧ 0 < b3)
    (_hunit : padicValNat 7 b1 = 0 ∧
      padicValNat 7 b2 = 0 ∧ padicValNat 7 b3 = 0)
    (hsame : runit7 b1 = runit7 b2 ∧ runit7 b2 = runit7 b3)
    (h : padicValNat 7 (eMod7 m b1 b3) =
      padicValNat 7 (eMod7 m b2 b3))
    (hm' : padicValNat 7 (eMod7 m b2 b3) < m)
    (hr : runit7 (eMod7 m b2 b3) =
      (3 : ZMod 7) * runit7 (eMod7 m b1 b3)) :
    ∃ lam : ℕ, (∃ k : ℕ, k < 7 ∧
        lam = 1 + k * 7 ^ (m - padicValNat 7 (eMod7 m b2 b3))) ∧
      ¬ 7 ∣ lam ∧
      qdig7 m (eMod7 m (lam * b2) (lam * b3)) ∈
        ({0, 5, 6} : Finset (ZMod 7)) ∧
      (∀ x ∈ ({b1, b2, b3} : Finset ℕ), ∀ y ∈ ({b1, b2, b3} : Finset ℕ),
        qdig7 m (eMod7 m (lam * x) (lam * y)) ∈
          ({0, 1, 5, 6} : Finset (ZMod 7))) ∧
      apLen (({b1, b2, b3} : Finset ℕ).image
        (fun d => qdig7 m (lam * d))) ≤ 3 := by
  classical
  set x := eMod7 m b1 b3 with hx
  set y := eMod7 m b2 b3 with hy
  have hb1 : b1 ∈ ({b1, b2, b3} : Finset ℕ) := by simp
  have hb2 : b2 ∈ ({b1, b2, b3} : Finset ℕ) := by simp
  have hb3 : b3 ∈ ({b1, b2, b3} : Finset ℕ) := by simp
  have hposB : ∀ d ∈ ({b1, b2, b3} : Finset ℕ), 0 < d := by
    intro d hd
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl | rfl
    · exact hpos.1
    · exact hpos.2.1
    · exact hpos.2.2
  have hr_all : ∀ d ∈ ({b1, b2, b3} : Finset ℕ), runit7 d = runit7 b3 := by
    intro d hd
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl | rfl
    · exact hsame.1.trans hsame.2
    · exact hsame.2
    · rfl
  have hsameB : ∀ u ∈ ({b1, b2, b3} : Finset ℕ),
      ∀ v ∈ ({b1, b2, b3} : Finset ℕ),
      residueRelOf u v = residueRel.same := fun u hu v hv =>
    rel_same ((hr_all u hu).trans (hr_all v hv).symm)
      (runit7_ne_zero (hposB v hv))
  have hc12 : ((eMod7 m b1 b2 : ℕ) : ZMod (7 ^ (m + 1)))
      = (x : ZMod _) - (y : ZMod _) :=
    eMod7_cast_sub (hsameB b1 hb1 b3 hb3) (hsameB b2 hb2 b3 hb3)
      (hsameB b1 hb1 b2 hb2)
  have hc21 : ((eMod7 m b2 b1 : ℕ) : ZMod (7 ^ (m + 1)))
      = (y : ZMod _) - (x : ZMod _) :=
    eMod7_cast_sub (hsameB b2 hb2 b3 hb3) (hsameB b1 hb1 b3 hb3)
      (hsameB b2 hb2 b1 hb1)
  have hc31 : ((eMod7 m b3 b1 : ℕ) : ZMod (7 ^ (m + 1)))
      = -(x : ZMod _) := by
    have hh := eMod7_cast_sub (m := m) (hsameB b3 hb3 b3 hb3)
      (hsameB b1 hb1 b3 hb3) (hsameB b3 hb3 b1 hb1)
    rw [eMod7_self'] at hh
    rwa [Nat.cast_zero, zero_sub] at hh
  have hc32 : ((eMod7 m b3 b2 : ℕ) : ZMod (7 ^ (m + 1)))
      = -(y : ZMod _) := by
    have hh := eMod7_cast_sub (m := m) (hsameB b3 hb3 b3 hb3)
      (hsameB b2 hb2 b3 hb3) (hsameB b3 hb3 b2 hb2)
    rw [eMod7_self'] at hh
    rwa [Nat.cast_zero, zero_sub] at hh
  rcases eq_or_ne x 0 with hx0 | hx0
  · -- `x = 0` ⇒ `y = 0`: all difference residues vanish; `λ = 1` (`k = 0`).
    have hy0 : y = 0 := by
      by_contra hne
      have hry : runit7 y ≠ 0 := runit7_ne_zero (Nat.pos_of_ne_zero hne)
      rw [hx0, runit7_zero] at hr
      simp at hr
      exact hry hr
    have hAll03 : ∀ u ∈ ({b1, b2, b3} : Finset ℕ), eMod7 m u b3 = 0 := by
      intro u hu
      rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with h | h | h
      · rw [h]; exact hx0
      · rw [h]; exact hy0
      · rw [h]; exact eMod7_self' _ _
    have hAll0 : ∀ u ∈ ({b1, b2, b3} : Finset ℕ),
        ∀ v ∈ ({b1, b2, b3} : Finset ℕ), eMod7 m u v = 0 := by
      intro u hu v hv
      rw [eMod7_sub_eq (hsameB u hu b3 hb3) (hsameB v hv b3 hb3)
          (hsameB u hu v hv),
        hAll03 u hu, hAll03 v hv, Nat.zero_add, Nat.sub_zero, Nat.mod_self]
    refine ⟨1, ⟨0, by norm_num, by simp⟩, by decide, ?_, ?_, ?_⟩
    · rw [eMod7_smul (runit7_ne_zero (by norm_num : (0 : ℕ) < 1)),
        hAll0 b2 hb2 b3 hb3, one_mul, Nat.zero_mod, qdig7_zero]
      exact Finset.mem_insert_self _ _
    · intro x' hx' y' hy'
      rw [eMod7_smul (runit7_ne_zero (by norm_num : (0 : ℕ) < 1)),
        hAll0 x' hx' y' hy', one_mul, Nat.zero_mod, qdig7_zero]
      exact Finset.mem_insert_self _ _
    · -- all residues coincide ⇒ digit set is a singleton
      have himg : (({b1, b2, b3} : Finset ℕ).image
            (fun d => qdig7 m (1 * d))) ⊆ {qdig7 m b3} := by
        intro q hq
        obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hq
        rw [Finset.mem_singleton, one_mul]
        have hres : d % 7 ^ (m + 1) = b3 % 7 ^ (m + 1) :=
          eq_resid_of_eMod7_eq_zero (hAll03 d hd) (hsameB d hd b3 hb3)
        exact qdig7_congr hres
      have h1 : apLen (({b1, b2, b3} : Finset ℕ).image
            (fun d => qdig7 m (1 * d))) ≤ 1 := by
        rw [apLen_le_iff _ 1 (by norm_num)]
        exact ⟨qdig7 m b3, by rwa [cycIv_one]⟩
      omega
  · -- `x ≠ 0` ⇒ `y ≠ 0` (`3·r(x) ≠ 0`)
    have hy0 : y ≠ 0 := by
      intro hc
      rw [hc, runit7_zero] at hr
      have h3x : (3 : ZMod 7) * runit7 x = 0 := hr.symm
      have hxr : runit7 x = 0 := by
        have h3 : (3 : ZMod 7) ≠ 0 := by decide
        rcases mul_eq_zero.mp h3x with h0 | h0
        · exact absurd h0 h3
        · exact h0
      have : x = 0 := by
        by_contra hne
        exact runit7_ne_zero (Nat.pos_of_ne_zero hne) hxr
      exact hx0 this
    set hν := padicValNat 7 x with hνdef
    have hxν : padicValNat 7 x = hν := rfl
    have hyν : padicValNat 7 y = hν := h.symm
    have hνm : hν < m := by rwa [hyν] at hm'
    -- single `Λ_h` multiplier `λ = 1 + k·7^{m−h}`
    obtain ⟨t, ht, htx, hdxy⟩ := lemma9_ii_table3 (qdig7 m x) (qdig7 m y)
    obtain ⟨k, hk7, hset⟩ := exists_multLow_set_qdig hνm hyν hy0 t
    set lam : ℕ := 1 + k * 7 ^ (m - hν) with hlamdef
    have hlam1 : runit7 lam = 1 := by
      rw [hlamdef]; exact runit7_multLow hνm
    have hlam0 : runit7 lam ≠ 0 := by rw [hlam1]; decide
    have hlam7 : ¬ 7 ∣ lam := by rw [hlamdef]; exact multLow_not_dvd hνm
    have hlamne : lam ≠ 0 := by
      intro h0
      rw [h0] at hlam7
      exact hlam7 (dvd_zero 7)
    -- `(k)·r(x) = 5·(t − qy)` via `3·u = v ⇒ u = 5v`
    have hkry : (k : ZMod 7) * runit7 y = t - qdig7 m y := by
      have h1 := qdig7_multLow hνm hyν (k := k)
      rw [hset] at h1
      have h2 : (k : ZMod 7) * runit7 y + qdig7 m y = t := by
        rw [add_comm]; exact h1.symm
      exact eq_sub_iff_add_eq.mpr h2
    have hkqx : (k : ZMod 7) * runit7 x = 5 * (t - qdig7 m y) := by
      have h3 : (3 : ZMod 7) * ((k : ZMod 7) * runit7 x)
          = t - qdig7 m y := by
        have e : (3 : ZMod 7) * ((k : ZMod 7) * runit7 x)
            = (k : ZMod 7) * runit7 y := by
          rw [hr]; ring
        rw [e]; exact hkry
      calc (k : ZMod 7) * runit7 x
          = 5 * (3 * ((k : ZMod 7) * runit7 x)) := by
            have h15 : (5 : ZMod 7) * 3 = 1 := by decide
            rw [← mul_assoc, h15, one_mul]
        _ = 5 * (t - qdig7 m y) := by rw [h3]
    have hqx : qdig7 m (lam * x)
        = qdig7 m x + 2 * qdig7 m y + 5 * t := by
      have h1 := qdig7_multLow hνm hxν (k := k)
      rw [← hlamdef] at h1
      rw [h1, hkqx]
      have hsub5 : (5 : ZMod 7) * (t - qdig7 m y) = 5 * t + 2 * qdig7 m y := by
        have h5 : (-5 : ZMod 7) = 2 := by decide
        rw [mul_sub, sub_eq_add_neg, ← neg_mul, h5]
      rw [hsub5]; ring
    have hqy : qdig7 m (lam * y) = t := hset
    have hdvx : 7 ^ hν ∣ x :=
      (Nat.pow_dvd_iff_le_padicValNat (by norm_num) hx0).mpr
        (le_of_eq hxν.symm)
    have hdvy : 7 ^ hν ∣ y :=
      (Nat.pow_dvd_iff_le_padicValNat (by norm_num) hy0).mpr
        (le_of_eq hyν.symm)
    have hlowx : (lam * x) % 7 ^ m = x % 7 ^ m := by
      rw [hlamdef]; exact multLow_low hνm.le hdvx
    have hlowy : (lam * y) % 7 ^ m = y % 7 ^ m := by
      rw [hlamdef]; exact multLow_low hνm.le hdvy
    have hlowx0 : (lam * x) % 7 ^ m ≠ 0 := by
      rw [hlowx]
      intro hc
      have hd : 7 ^ m ∣ x := Nat.dvd_of_mod_eq_zero hc
      have hle : m ≤ padicValNat 7 x :=
        (Nat.pow_dvd_iff_le_padicValNat (by norm_num) hx0).mp hd
      rw [hxν] at hle
      omega
    have hlowy0 : (lam * y) % 7 ^ m ≠ 0 := by
      rw [hlowy]
      intro hc
      have hd : 7 ^ m ∣ y := Nat.dvd_of_mod_eq_zero hc
      have hle : m ≤ padicValNat 7 y :=
        (Nat.pow_dvd_iff_le_padicValNat (by norm_num) hy0).mp hd
      rw [hyν] at hle
      omega
    have eval : ∀ {u v A B : ℕ},
        ((lam * eMod7 m u v : ℕ) : ZMod (7 ^ (m + 1)))
          = (A : ZMod _) - (B : ZMod _) →
        qdig7 m (eMod7 m (lam * u) (lam * v))
          = qdig7 m A - qdig7 m B
            - if A % 7 ^ m < B % 7 ^ m then (1 : ZMod 7) else 0 := by
      intro u v A B hcast
      rw [eMod7_smul hlam0, qdig7_congr (Nat.mod_mod _ _)]
      exact qdig_smul_eMod_eq hcast
    have key : ∀ u ∈ ({b1, b2, b3} : Finset ℕ),
        ∀ v ∈ ({b1, b2, b3} : Finset ℕ),
        qdig7 m (eMod7 m (lam * u) (lam * v))
          ∈ ({0, 1, 5, 6} : Finset (ZMod 7)) := by
      intro u hu v hv
      rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hu hv
      rcases hu with hu' | hu' | hu' <;> rcases hv with hv' | hv' | hv' <;>
        rw [hu', hv']
      · rw [eMod7_self', qdig7_zero]; decide
      · -- (b1,b2): `λx − λy` — `qx+2qy+4t ∈ {0,1,6}` minus borrow
        have hcast : ((lam * eMod7 m b1 b2 : ℕ) : ZMod (7 ^ (m + 1)))
            = ((lam * x : ℕ) : ZMod _) - ((lam * y : ℕ) : ZMod _) := by
          simp only [Nat.cast_mul]
          rw [hc12]; ring
        rw [eval hcast, hqx, hqy]
        have hsimp : qdig7 m x + 2 * qdig7 m y + 5 * t - t
            = qdig7 m x + 2 * qdig7 m y + 4 * t := by ring
        rw [hsimp]
        by_cases hδ : lam * x % 7 ^ m < lam * y % 7 ^ m
        · rw [if_pos hδ]
          exact sub_borrow_mem_0156 hdxy (Or.inr rfl)
        · rw [if_neg hδ]
          exact sub_borrow_mem_0156 hdxy (Or.inl rfl)
      · -- (b1,b3): `q(λx) = qx+2qy+5t ∈ {0,1,5,6}`
        rw [eMod7_smul hlam0, qdig7_congr (Nat.mod_mod _ _), ← hx, hqx]
        exact htx
      · -- (b2,b1): `λy − λx` — `−(qx+2qy+4t)` minus borrow
        have hcast : ((lam * eMod7 m b2 b1 : ℕ) : ZMod (7 ^ (m + 1)))
            = ((lam * y : ℕ) : ZMod _) - ((lam * x : ℕ) : ZMod _) := by
          simp only [Nat.cast_mul]
          rw [hc21]; ring
        rw [eval hcast, hqy, hqx]
        have hsimp : t - (qdig7 m x + 2 * qdig7 m y + 5 * t)
            = -(qdig7 m x + 2 * qdig7 m y + 4 * t) := by ring
        rw [hsimp]
        by_cases hδ : lam * y % 7 ^ m < lam * x % 7 ^ m
        · rw [if_pos hδ]
          exact sub_borrow_mem_0156 (neg_mem_016 hdxy) (Or.inr rfl)
        · rw [if_neg hδ]
          exact sub_borrow_mem_0156 (neg_mem_016 hdxy) (Or.inl rfl)
      · rw [eMod7_self', qdig7_zero]; decide
      · -- (b2,b3): `q(λy) = t ∈ {0,5,6} ⊆ {0,1,5,6}`
        rw [eMod7_smul hlam0, qdig7_congr (Nat.mod_mod _ _), ← hy, hqy]
        simp only [Finset.mem_insert, Finset.mem_singleton] at ht ⊢
        rcases ht with rfl | rfl | rfl <;> decide
      · -- (b3,b1): `−λx`, borrow forced
        have hcast : ((lam * eMod7 m b3 b1 : ℕ) : ZMod (7 ^ (m + 1)))
            = ((0 : ℕ) : ZMod _) - ((lam * x : ℕ) : ZMod _) := by
          simp only [Nat.cast_mul, Nat.cast_zero]
          rw [hc31]; ring
        rw [eval hcast, qdig7_zero, Nat.zero_mod,
          if_pos (Nat.pos_of_ne_zero hlowx0), hqx]
        have hsimp : (0 : ZMod 7) - (qdig7 m x + 2 * qdig7 m y + 5 * t) - 1
            = -(qdig7 m x + 2 * qdig7 m y + 5 * t) - 1 := by ring
        rw [hsimp]
        exact neg_sub_one_mem_0156 htx
      · -- (b3,b2): `−λy`
        have hcast : ((lam * eMod7 m b3 b2 : ℕ) : ZMod (7 ^ (m + 1)))
            = ((0 : ℕ) : ZMod _) - ((lam * y : ℕ) : ZMod _) := by
          simp only [Nat.cast_mul, Nat.cast_zero]
          rw [hc32]; ring
        rw [eval hcast, qdig7_zero, Nat.zero_mod,
          if_pos (Nat.pos_of_ne_zero hlowy0), hqy]
        have hsimp : (0 : ZMod 7) - t - 1 = -t - 1 := by ring
        rw [hsimp]
        exact neg_sub_one_mem_056 ht
      · rw [eMod7_self', qdig7_zero]; decide
    set BL : Finset ℕ := ({b1, b2, b3} : Finset ℕ).image (lam * ·)
      with hBLdef
    have hBLsame : ∀ u ∈ BL, ∀ v ∈ BL,
        residueRelOf u v = residueRel.same := by
      intro u hu v hv
      obtain ⟨u', hu', rfl⟩ := Finset.mem_image.mp hu
      obtain ⟨v', hv', rfl⟩ := Finset.mem_image.mp hv
      apply rel_same _ (runit7_ne_zero
        (Nat.mul_pos (Nat.pos_of_ne_zero hlamne) (hposB v' hv')))
      rw [runit7_mul, runit7_mul, hlam1, one_mul, one_mul,
        hr_all u' hu', hr_all v' hv']
    have hBL : ∀ u ∈ BL, ∀ v ∈ BL,
        qdig7 m (eMod7 m u v) ∈ ({0, 1, 5, 6} : Finset (ZMod 7)) := by
      intro u hu v hv
      obtain ⟨u', hu', rfl⟩ := Finset.mem_image.mp hu
      obtain ⟨v', hv', rfl⟩ := Finset.mem_image.mp hv
      exact key u' hu' v' hv'
    have hdiff := remark8_ii_int hBLsame hBL
    have hlen : apLen (BL.image (qdig7 m)) ≤ 3 := remark8_ii' hdiff
    have himg : BL.image (qdig7 m)
        = ({b1, b2, b3} : Finset ℕ).image (fun d => qdig7 m (lam * d)) := by
      rw [hBLdef, Finset.image_image]
      exact Finset.image_congr fun d _ => rfl
    refine ⟨lam, ⟨k, hk7, ?_⟩, hlam7, ?_, ?_, ?_⟩
    · rw [hyν]
    · rw [eMod7_smul hlam0, qdig7_congr (Nat.mod_mod _ _), ← hy, hqy]
      exact ht
    · intro x' hx' y' hy'
      exact hBL _ (Finset.mem_image.mpr ⟨x', hx', rfl⟩)
        _ (Finset.mem_image.mpr ⟨y', hy', rfl⟩)
    · rw [himg] at hlen
      exact hlen

private theorem c63_finish2 {m : ℕ} (hm : 0 < m)
    {A1 A2 A4 : Finset ℕ}
    (hpos : ∀ d ∈ A1 ∪ A2 ∪ A4, 0 < d)
    (hunit : ∀ d ∈ A1 ∪ A2 ∪ A4, padicValNat 7 d = 0)
    {s : ZMod 7} (hs0 : s ≠ 0)
    (hcls1 : ∀ d ∈ A1, runit7 d = s)
    (hcls2 : ∀ d ∈ A2, runit7 d = 2 * s)
    (hcls4 : ∀ d ∈ A4, runit7 d = 4 * s)
    {d1 d2 d3 : ℕ} (hA1 : A1 = {d1, d2, d3})
    (hA2 : A2.card = 1) (hA4 : A4.card = 1) (hne : A1.Nonempty)
    {lam : ℕ} (hlam : ¬ 7 ∣ lam)
    (hlen : apLen (({d1, d2, d3} : Finset ℕ).image
      (fun d => qdig7 m (lam * d))) ≤ 2) :
    ∃ l : ℕ, ¬ 7 ∣ l ∧ good7 m l (A1 ∪ A2 ∪ A4) := by
  have himg : (A1.image (fun d => lam * d)).image (qdig7 m) =
      ({d1, d2, d3} : Finset ℕ).image (fun d => qdig7 m (lam * d)) := by
    rw [hA1, Finset.image_image]
    exact Finset.image_congr fun d _ => rfl
  exact c63_tail2 hm hpos hunit hs0 hcls1 hcls2 hcls4 hA2 hA4 hne
    hlam (by rwa [himg])

private theorem c63_finish3 {m : ℕ} (hm : 0 < m)
    {A1 A2 A4 : Finset ℕ}
    (hpos : ∀ d ∈ A1 ∪ A2 ∪ A4, 0 < d)
    (hunit : ∀ d ∈ A1 ∪ A2 ∪ A4, padicValNat 7 d = 0)
    {s : ZMod 7} (hs0 : s ≠ 0)
    (hcls1 : ∀ d ∈ A1, runit7 d = s)
    (hcls2 : ∀ d ∈ A2, runit7 d = 2 * s)
    (hcls4 : ∀ d ∈ A4, runit7 d = 4 * s)
    {d1 d2 d3 d4 d5 : ℕ} (hA1 : A1 = {d1, d2, d3})
    (hA2eq : A2 = {d4}) (hA4eq : A4 = {d5})
    (hA2 : A2.card = 1) (hA4 : A4.card = 1) (hne : A1.Nonempty)
    {lam : ℕ} (hlam : ¬ 7 ∣ lam)
    (hlen : apLen (({d1, d2, d3} : Finset ℕ).image
      (fun d => qdig7 m (lam * d))) ≤ 3)
    (hpair : (2 * qdig7 m (lam * d4) - qdig7 m (lam * d5) : ZMod 7)
      ∉ ({2, 4} : Finset (ZMod 7))) :
    ∃ l : ℕ, ¬ 7 ∣ l ∧ good7 m l (A1 ∪ A2 ∪ A4) := by
  have himg : (A1.image (fun d => lam * d)).image (qdig7 m) =
      ({d1, d2, d3} : Finset ℕ).image (fun d => qdig7 m (lam * d)) := by
    rw [hA1, Finset.image_image]
    exact Finset.image_congr fun d _ => rfl
  apply c63_tail3 hm hpos hunit hs0 hcls1 hcls2 hcls4 hA2 hA4 hne
    hlam (by rwa [himg])
  intro x hx y hy
  rw [hA2eq, Finset.mem_singleton] at hx
  rw [hA4eq, Finset.mem_singleton] at hy
  rwa [hx, hy]

private theorem c63_case_i {m : ℕ} (hm : 2 ≤ m)
    {A1 A2 A4 : Finset ℕ}
    (hA2 : A2.card = 1) (hA4 : A4.card = 1)
    (hpos : ∀ d ∈ A1 ∪ A2 ∪ A4, 0 < d)
    (hunit : ∀ d ∈ A1 ∪ A2 ∪ A4, padicValNat 7 d = 0)
    {s : ZMod 7} (hs0 : s ≠ 0)
    (hcls1 : ∀ d ∈ A1, runit7 d = s)
    (hcls2 : ∀ d ∈ A2, runit7 d = 2 * s)
    (hcls4 : ∀ d ∈ A4, runit7 d = 4 * s)
    {d1 d2 d3 : ℕ} (hA1eq : A1 = {d1, d2, d3}) (hne : A1.Nonempty)
    (hp1 : 0 < d1) (hp2 : 0 < d2) (hp3 : 0 < d3)
    (hu1 : padicValNat 7 d1 = 0) (hu2 : padicValNat 7 d2 = 0)
    (hu3 : padicValNat 7 d3 = 0)
    (hr1 : runit7 d1 = s) (hr2 : runit7 d2 = s) (hr3 : runit7 d3 = s)
    (hlgt : elevel7 m d1 d3 > elevel7 m d2 d3) :
    ∃ lam : ℕ, ¬ 7 ∣ lam ∧ good7 m lam (A1 ∪ A2 ∪ A4) := by
  have hrel13 : residueRelOf d1 d3 = residueRel.same :=
    rel_same (by rw [hr1, hr3]) (by rw [hr3]; exact hs0)
  have hrel23 : residueRelOf d2 d3 = residueRel.same :=
    rel_same (by rw [hr2, hr3]) (by rw [hr3]; exact hs0)
  have he23 : eMod7 m d2 d3 ≠ 0 := by
    intro h0
    rw [elevel7_of_eq h0] at hlgt
    have hle : elevel7 m d1 d3 ≤ m + 1 := elevel7_le
    omega
  by_cases he13 : eMod7 m d1 d3 = 0
  · have hq13 : qdig7 m d1 = qdig7 m d3 :=
      qdig7_congr (eq_resid_of_eMod7_eq_zero he13 hrel13)
    have hν23 : padicValNat 7 (eMod7 m d2 d3) = elevel7 m d2 d3 :=
      (elevel7_of_ne he23).symm
    by_cases hlm : padicValNat 7 (eMod7 m d2 d3) < m
    · obtain ⟨k, hk7, hkq⟩ := exists_multLow_set_qdig hlm rfl he23 0
      set lam := 1 + k * 7 ^ (m - padicValNat 7 (eMod7 m d2 d3)) with hlam
      have hlamr : runit7 lam = 1 := runit7_multLow hlm
      have hlam7 : ¬ 7 ∣ lam := multLow_not_dvd hlm
      have hrel13' : residueRelOf (lam * d1) (lam * d3) = residueRel.same :=
        rel_same_of_mul hlam7 (by rw [hr1, hr3]) (ne_of_gt hp3)
      have hrel23' : residueRelOf (lam * d2) (lam * d3) = residueRel.same :=
        rel_same_of_mul hlam7 (by rw [hr2, hr3]) (ne_of_gt hp3)
      have he13' : eMod7 m (lam * d1) (lam * d3) = 0 := by
        rw [eMod7_mul hlamr, he13, mul_zero, Nat.zero_mod]
      have hq13' : qdig7 m (lam * d1) = qdig7 m (lam * d3) :=
        qdig7_congr (eq_resid_of_eMod7_eq_zero he13' hrel13')
      have hqe : qdig7 m (eMod7 m (lam * d2) (lam * d3)) = 0 := by
        rw [eMod7_mul hlamr, qdig7_congr (Nat.mod_mod _ _)]
        exact hkq
      have hb := qdig_eMod_sub (m := m) hrel23'
      rw [hqe] at hb
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb
      have hdiff : qdig7 m (lam * d2) - qdig7 m (lam * d3) ∈
          ({0, 1} : Finset (ZMod 7)) := by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        rcases hb with hb0 | hb6
        · left; linear_combination -hb0
        · right
          have h : qdig7 m (lam * d2) - qdig7 m (lam * d3) = -6 := by
            linear_combination -hb6
          rw [h]
          decide
      have hsub : ({d1, d2, d3} : Finset ℕ).image (fun d => qdig7 m (lam * d))
          ⊆ cycIv (qdig7 m (lam * d3)) 2 := by
        intro x hx
        obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hd
        rcases hd with rfl | rfl | rfl
        · rw [mem_cycIv, hq13']; simp
        · rw [mem_cycIv]
          simp only [Finset.mem_insert, Finset.mem_singleton] at hdiff
          rcases hdiff with h0 | h1
          · rw [h0]; simp
          · rw [h1]; decide
        · rw [mem_cycIv]; simp
      have hlen : apLen (({d1, d2, d3} : Finset ℕ).image
          (fun d => qdig7 m (lam * d))) ≤ 2 :=
        (apLen_le_iff _ 2 (by norm_num)).mpr ⟨_, hsub⟩
      exact c63_finish2 (by omega) hpos hunit hs0 hcls1 hcls2 hcls4
        hA1eq hA2 hA4 hne hlam7 hlen
    · have hν23m : padicValNat 7 (eMod7 m d2 d3) = m := by
        have hle := enu7_le_of_ne he23
        unfold enu7 at hle
        omega
      obtain ⟨c, hcpos, hc7, hce, hqc⟩ := exists_top_scalar_set hν23m he23
        (t := (1 : ZMod 7)) (by decide)
      have hcnd : ¬ 7 ∣ c := fun hd => absurd (Nat.le_of_dvd hcpos hd) (by omega)
      have hrc : runit7 c ≠ 0 := runit7_ne_zero hcpos
      have hrel13' : residueRelOf (c * d1) (c * d3) = residueRel.same :=
        rel_same_of_mul hcnd (by rw [hr1, hr3]) (ne_of_gt hp3)
      have hrel23' : residueRelOf (c * d2) (c * d3) = residueRel.same :=
        rel_same_of_mul hcnd (by rw [hr2, hr3]) (ne_of_gt hp3)
      have he13' : eMod7 m (c * d1) (c * d3) = 0 := by
        rw [eMod7_smul hrc, he13, mul_zero, Nat.zero_mod]
      have hq13' : qdig7 m (c * d1) = qdig7 m (c * d3) :=
        qdig7_congr (eq_resid_of_eMod7_eq_zero he13' hrel13')
      have he23' : eMod7 m (c * d2) (c * d3) = (1 : ZMod 7).val * 7 ^ m := by
        rw [eMod7_smul hrc]
        exact hce
      have hq23' : qdig7 m (c * d2) = qdig7 m (c * d3) + 1 :=
        qdig_eq_add_of_e_top hrel23' he23'
      have hsub : ({d1, d2, d3} : Finset ℕ).image (fun d => qdig7 m (c * d))
          ⊆ cycIv (qdig7 m (c * d3)) 2 := by
        intro x hx
        obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hd
        rcases hd with rfl | rfl | rfl
        · rw [mem_cycIv, hq13']; simp
        · rw [mem_cycIv, hq23', add_sub_cancel_left]; decide
        · rw [mem_cycIv]; simp
      have hlen : apLen (({d1, d2, d3} : Finset ℕ).image
          (fun d => qdig7 m (c * d))) ≤ 2 :=
        (apLen_le_iff _ 2 (by norm_num)).mpr ⟨_, hsub⟩
      exact c63_finish2 (by omega) hpos hunit hs0 hcls1 hcls2 hcls4
        hA1eq hA2 hA4 hne hcnd hlen
  · have hν13 : padicValNat 7 (eMod7 m d1 d3) = elevel7 m d1 d3 :=
      (elevel7_of_ne he13).symm
    have hν23 : padicValNat 7 (eMod7 m d2 d3) = elevel7 m d2 d3 :=
      (elevel7_of_ne he23).symm
    have hνne : padicValNat 7 (eMod7 m d1 d3) ≠
        padicValNat 7 (eMod7 m d2 d3) := by
      rw [hν13, hν23]
      exact ne_of_gt hlgt
    obtain ⟨lam, hlam, hpair, hlen⟩ := lemma9_i'
      ⟨hp1, hp2, hp3⟩ ⟨hu1, hu2, hu3⟩
      ⟨hr1.trans hr2.symm, hr2.trans hr3.symm⟩ hνne ⟨he13, he23⟩
    exact c63_finish2 (by omega) hpos hunit hs0 hcls1 hcls2 hcls4
      hA1eq hA2 hA4 hne hlam hlen

private theorem c63_case_collision {m : ℕ} (hm : 0 < m)
    {A1 A2 A4 : Finset ℕ}
    (hA2 : A2.card = 1) (hA4 : A4.card = 1)
    (hpos : ∀ d ∈ A1 ∪ A2 ∪ A4, 0 < d)
    (hunit : ∀ d ∈ A1 ∪ A2 ∪ A4, padicValNat 7 d = 0)
    {s : ZMod 7} (hs0 : s ≠ 0)
    (hcls1 : ∀ d ∈ A1, runit7 d = s)
    (hcls2 : ∀ d ∈ A2, runit7 d = 2 * s)
    (hcls4 : ∀ d ∈ A4, runit7 d = 4 * s)
    {d1 d2 d3 : ℕ} (hA1eq : A1 = {d1, d2, d3}) (hne : A1.Nonempty)
    (hp3 : 0 < d3) (hr1 : runit7 d1 = s) (hr2 : runit7 d2 = s)
    (hr3 : runit7 d3 = s)
    (he13 : eMod7 m d1 d3 = 0) (he23 : eMod7 m d2 d3 = 0) :
    ∃ lam : ℕ, ¬ 7 ∣ lam ∧ good7 m lam (A1 ∪ A2 ∪ A4) := by
  have hrel13 : residueRelOf d1 d3 = residueRel.same :=
    rel_same (by rw [hr1, hr3]) (by rw [hr3]; exact hs0)
  have hrel23 : residueRelOf d2 d3 = residueRel.same :=
    rel_same (by rw [hr2, hr3]) (by rw [hr3]; exact hs0)
  have hq13 : qdig7 m d1 = qdig7 m d3 :=
    qdig7_congr (eq_resid_of_eMod7_eq_zero he13 hrel13)
  have hq23 : qdig7 m d2 = qdig7 m d3 :=
    qdig7_congr (eq_resid_of_eMod7_eq_zero he23 hrel23)
  have hsub : ({d1, d2, d3} : Finset ℕ).image (fun d => qdig7 m (1 * d))
      ⊆ cycIv (qdig7 m d3) 1 := by
    intro x hx
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl | rfl
    · rw [one_mul, mem_cycIv, hq13]; simp
    · rw [one_mul, mem_cycIv, hq23]; simp
    · rw [one_mul, mem_cycIv]; simp
  have hlen : apLen (({d1, d2, d3} : Finset ℕ).image
      (fun d => qdig7 m (1 * d))) ≤ 2 := by
    have h1 : apLen (({d1, d2, d3} : Finset ℕ).image
        (fun d => qdig7 m (1 * d))) ≤ 1 :=
      (apLen_le_iff _ 1 (by norm_num)).mpr ⟨_, hsub⟩
    omega
  exact c63_finish2 hm hpos hunit hs0 hcls1 hcls2 hcls4
    hA1eq hA2 hA4 hne (by decide) hlen

private theorem c63_case_ii1_low {m : ℕ} (hm : 2 ≤ m)
    {A1 A2 A4 : Finset ℕ}
    (hA2 : A2.card = 1) (hA4 : A4.card = 1)
    (hpos : ∀ d ∈ A1 ∪ A2 ∪ A4, 0 < d)
    (hunit : ∀ d ∈ A1 ∪ A2 ∪ A4, padicValNat 7 d = 0)
    {s : ZMod 7} (hs0 : s ≠ 0)
    (hcls1 : ∀ d ∈ A1, runit7 d = s)
    (hcls2 : ∀ d ∈ A2, runit7 d = 2 * s)
    (hcls4 : ∀ d ∈ A4, runit7 d = 4 * s)
    {d1 d2 d3 : ℕ} (hA1eq : A1 = {d1, d2, d3}) (hne : A1.Nonempty)
    (hp1 : 0 < d1) (hp2 : 0 < d2) (hp3 : 0 < d3)
    (hu1 : padicValNat 7 d1 = 0) (hu2 : padicValNat 7 d2 = 0)
    (hu3 : padicValNat 7 d3 = 0)
    (hr1 : runit7 d1 = s) (hr2 : runit7 d2 = s) (hr3 : runit7 d3 = s)
    (hνeq : padicValNat 7 (eMod7 m d1 d3) =
      padicValNat 7 (eMod7 m d2 d3))
    (hνm : padicValNat 7 (eMod7 m d2 d3) < m)
    (hrat : runit7 (eMod7 m d1 d3) = 2 * runit7 (eMod7 m d2 d3)) :
    ∃ lam : ℕ, ¬ 7 ∣ lam ∧ good7 m lam (A1 ∪ A2 ∪ A4) := by
  obtain ⟨lam, hlam, hqe, hpairs, hj2, hlen⟩ := lemma9_ii
    ⟨hp2, hp1, hp3⟩ ⟨hu2, hu1, hu3⟩
    ⟨hr2.trans hr1.symm, hr1.trans hr3.symm⟩ hνeq.symm
    (by rwa [hνeq]) (Or.inl rfl) hrat
  have hset : ({d2, d1, d3} : Finset ℕ) = ({d1, d2, d3} : Finset ℕ) := by
    rw [Finset.insert_comm d2 d1]
  rw [hset] at hlen
  exact c63_finish2 (by omega) hpos hunit hs0 hcls1 hcls2 hcls4
    hA1eq hA2 hA4 hne hlam hlen

private theorem c63_eps24_dec : ∀ v : ZMod 7,
    ∃ eps : ZMod 7, eps ∈ ({0, 1} : Finset (ZMod 7)) ∧
      v - eps ∉ ({2, 4} : Finset (ZMod 7)) := by
  decide

private theorem c63_sigma_single (cm eps : ℕ) (hcm : cm < 2) (heps : eps < 2) :
    (cm + 2 * (4 * eps)) / 7 = eps := by
  interval_cases cm <;> interval_cases eps <;> decide

private theorem c63_top_avoid24 {m d d' : ℕ} (hm : 2 ≤ m)
    (hd : padicValNat 7 d = 0) (hpos : 0 < d)
    (hrel : runit7 d' = 2 * runit7 d) {v : ZMod 7}
    (he : eMod7 m d d' = v.val * 7 ^ m) :
    ∃ k : ℕ, k < 7 ∧
      etd7 m ((1 + k * 7 ^ (m - 1)) * d)
        ((1 + k * 7 ^ (m - 1)) * d') ∉ ({2, 4} : Finset (ZMod 7)) := by
  obtain ⟨eps, heps, hsafe⟩ := c63_eps24_dec v
  have hepsval : eps.val < 2 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at heps
    rcases heps with rfl | rfl <;> decide
  obtain ⟨k, hk7, hW⟩ := single_carry (m := m) hpos hd
    (by omega : 4 * eps.val < 7)
  refine ⟨k, hk7, ?_⟩
  obtain ⟨hlo, hpart, hetd⟩ := c63_eps_pair hm hrel he
  have hcm : 2 * (d % 7 ^ (m - 1)) / 7 ^ (m - 1) < 2 := by
    apply Nat.div_lt_of_lt_mul
    have hlt := Nat.mod_lt d (Nat.pow_pos (by norm_num) : 0 < 7 ^ (m - 1))
    omega
  have hsigma :
      (2 * (d % 7 ^ (m - 1)) / 7 ^ (m - 1) +
        2 * (((d / 7 ^ (m - 1)) % 7 + k * (d % 7)) % 7)) / 7 = eps.val := by
    rw [hW]
    exact c63_sigma_single _ _ hcm hepsval
  rw [hetd, hsigma, ZMod.natCast_zmod_val]
  exact hsafe

private theorem c63_len3_top {m x1 x2 x3 : ℕ}
    (hp3 : 0 < x3)
    (hr1 : runit7 x1 = runit7 x3) (hr2 : runit7 x2 = runit7 x3)
    (he13 : eMod7 m x1 x3 = (2 : ZMod 7).val * 7 ^ m)
    (he23 : eMod7 m x2 x3 = (1 : ZMod 7).val * 7 ^ m) :
    apLen (({x1, x2, x3} : Finset ℕ).image (qdig7 m)) ≤ 3 := by
  have hrel13 : residueRelOf x1 x3 = residueRel.same :=
    rel_same hr1 (runit7_ne_zero hp3)
  have hrel23 : residueRelOf x2 x3 = residueRel.same :=
    rel_same hr2 (runit7_ne_zero hp3)
  have hq13 : qdig7 m x1 = qdig7 m x3 + 2 :=
    qdig_eq_add_of_e_top hrel13 he13
  have hq23 : qdig7 m x2 = qdig7 m x3 + 1 :=
    qdig_eq_add_of_e_top hrel23 he23
  rw [apLen_le_iff _ 3 (by norm_num)]
  refine ⟨qdig7 m x3, ?_⟩
  intro q hq
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hq
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl
  · rw [mem_cycIv, hq13, add_sub_cancel_left]
    decide
  · rw [mem_cycIv, hq23, add_sub_cancel_left]
    decide
  · rw [mem_cycIv]
    simp

set_option maxHeartbeats 3000000 in
private theorem c63_case_ii1_top {m : ℕ} (hm : 2 ≤ m)
    {A1 A2 A4 : Finset ℕ}
    (hA2 : A2.card = 1) (hA4 : A4.card = 1)
    (hpos : ∀ d ∈ A1 ∪ A2 ∪ A4, 0 < d)
    (hunit : ∀ d ∈ A1 ∪ A2 ∪ A4, padicValNat 7 d = 0)
    {s : ZMod 7} (hs0 : s ≠ 0)
    (hcls1 : ∀ d ∈ A1, runit7 d = s)
    (hcls2 : ∀ d ∈ A2, runit7 d = 2 * s)
    (hcls4 : ∀ d ∈ A4, runit7 d = 4 * s)
    {d1 d2 d3 d4 d5 : ℕ}
    (hA1eq : A1 = {d1, d2, d3}) (hA2eq : A2 = {d4}) (hA4eq : A4 = {d5})
    (hne : A1.Nonempty)
    (hp1 : 0 < d1) (hp2 : 0 < d2) (hp3 : 0 < d3) (hp4 : 0 < d4) (hp5 : 0 < d5)
    (hu1 : padicValNat 7 d1 = 0) (hu2 : padicValNat 7 d2 = 0)
    (hu3 : padicValNat 7 d3 = 0) (hu4 : padicValNat 7 d4 = 0)
    (hu5 : padicValNat 7 d5 = 0)
    (hr1 : runit7 d1 = s) (hr2 : runit7 d2 = s) (hr3 : runit7 d3 = s)
    (hr4 : runit7 d4 = 2 * s) (hr5 : runit7 d5 = 4 * s)
    (he13 : eMod7 m d1 d3 ≠ 0) (he23 : eMod7 m d2 d3 ≠ 0)
    (hν13 : padicValNat 7 (eMod7 m d1 d3) = m)
    (hν23 : padicValNat 7 (eMod7 m d2 d3) = m)
    (hrat : runit7 (eMod7 m d1 d3) = 2 * runit7 (eMod7 m d2 d3)) :
    ∃ lam : ℕ, ¬ 7 ∣ lam ∧ good7 m lam (A1 ∪ A2 ∪ A4) := by
  obtain ⟨c, hcpos, hc7, hce23, hqc23⟩ := exists_top_scalar_set hν23 he23
    (t := (1 : ZMod 7)) (by decide)
  have hcnd : ¬ 7 ∣ c := fun hd => absurd (Nat.le_of_dvd hcpos hd) (by omega)
  have hrcast : runit7 c = (c : ZMod 7) :=
    runit7_of_padic_zero (padicValNat.eq_zero_of_not_dvd hcnd)
  have hrc : runit7 c ≠ 0 := runit7_ne_zero hcpos
  have hca : (c : ZMod 7) * runit7 (eMod7 m d2 d3) = 1 := by
    have h := qdig7_multTop (l := c) hν23
    rw [hqc23] at h
    exact h.symm
  have he23top : eMod7 m d2 d3 = (runit7 (eMod7 m d2 d3)).val * 7 ^ m := by
    have h := residN_top hν23
    rwa [qdig7_eq_runit7_of_top hν23,
      Nat.mod_eq_of_lt (eMod7_lt _ _ _)] at h
  have he13top : eMod7 m d1 d3 =
      ((2 : ZMod 7) * runit7 (eMod7 m d2 d3)).val * 7 ^ m := by
    have h := residN_top hν13
    rwa [qdig7_eq_runit7_of_top hν13,
      Nat.mod_eq_of_lt (eMod7_lt _ _ _), hrat] at h
  have he23c : eMod7 m (c * d2) (c * d3) = (1 : ZMod 7).val * 7 ^ m := by
    rw [e_smul_top hrc he23top, hca]
  have h2a : (c : ZMod 7) *
      ((2 : ZMod 7) * runit7 (eMod7 m d2 d3)) = 2 := by
    calc
      (c : ZMod 7) * (2 * runit7 (eMod7 m d2 d3)) =
          2 * ((c : ZMod 7) * runit7 (eMod7 m d2 d3)) := by ring
      _ = 2 := by rw [hca, mul_one]
  have he13c : eMod7 m (c * d1) (c * d3) = (2 : ZMod 7).val * 7 ^ m := by
    rw [e_smul_top hrc he13top, h2a]
  have huc : ∀ d : ℕ, d ≠ 0 → padicValNat 7 d = 0 →
      padicValNat 7 (c * d) = 0 := fun _ hd0 hd => by
    rw [padicValNat_mul_seven hcnd hd0, hd]
  have hr : ∀ d : ℕ, runit7 (c * d) = (c : ZMod 7) * runit7 d :=
    fun d => by rw [runit7_mul, hrcast]
  have hrel45c : runit7 (c * d5) = 2 * runit7 (c * d4) := by
    rw [hr, hr, hr5, hr4]
    ring
  set e45 := eMod7 m (c * d4) (c * d5) with he45
  by_cases he450 : e45 = 0
  · have hlen0 := c63_len3_top (m := m) (x1 := c * d1) (x2 := c * d2)
      (x3 := c * d3) (Nat.mul_pos hcpos hp3)
      (by rw [hr, hr, hr1, hr3]) (by rw [hr, hr, hr2, hr3]) he13c he23c
    have hlen : apLen (({d1, d2, d3} : Finset ℕ).image
        (fun d => qdig7 m (c * d))) ≤ 3 := by
      simpa only [Finset.image_insert, Finset.image_singleton] using hlen0
    have hb := qdig_eMod_sub_etd7 (m := m) (x := c * d4) (y := c * d5)
    rw [← he45, he450, qdig7_zero] at hb
    have hpair : etd7 m (c * d4) (c * d5) ∉ ({2, 4} : Finset (ZMod 7)) := by
      have hfin : ∀ z : ZMod 7,
          -z ∈ ({0, 1, 6} : Finset (ZMod 7)) → z ∉ ({2, 4} : Finset (ZMod 7)) := by
        decide
      exact hfin _ (by simpa using hb)
    have hpair' : (2 * qdig7 m (c * d4) - qdig7 m (c * d5) : ZMod 7)
        ∉ ({2, 4} : Finset (ZMod 7)) := by
      rw [← etd7_eq_twoX hrel45c]
      exact hpair
    exact c63_finish3 (m := m) (A1 := A1) (A2 := A2) (A4 := A4)
      (d1 := d1) (d2 := d2) (d3 := d3) (d4 := d4) (d5 := d5) (lam := c)
      (by omega) hpos hunit hs0 hcls1 hcls2 hcls4
      hA1eq hA2eq hA4eq hA2 hA4 hne hcnd hlen hpair'
  · have hνle : padicValNat 7 e45 ≤ m := by
      rw [he45]
      exact enu7_le_of_ne (by rwa [← he45])
    rcases eq_or_lt_of_le hνle with hνm | hνlt
    · have he45top : e45 = (runit7 e45).val * 7 ^ m := by
        have h := residN_top hνm
        rwa [qdig7_eq_runit7_of_top hνm,
          Nat.mod_eq_of_lt (by rw [he45]; exact eMod7_lt _ _ _)] at h
      obtain ⟨k, hk7, hpair⟩ := c63_top_avoid24 hm
        (huc d4 (ne_of_gt hp4) hu4) (Nat.mul_pos hcpos hp4) hrel45c
        (by rwa [← he45])
      set lam2 := 1 + k * 7 ^ (m - 1) with hlam2
      have h1m : 1 < m := by omega
      have hlam2r : runit7 lam2 = 1 := by rw [hlam2]; exact runit7_multLow h1m
      have he13L : eMod7 m (lam2 * (c * d1)) (lam2 * (c * d3)) =
          (2 : ZMod 7).val * 7 ^ m := by
        rw [eMod7_mul hlam2r, he13c, hlam2]
        exact lambda1_top_resid hm (ZMod.val_lt (2 : ZMod 7))
      have he23L : eMod7 m (lam2 * (c * d2)) (lam2 * (c * d3)) =
          (1 : ZMod 7).val * 7 ^ m := by
        rw [eMod7_mul hlam2r, he23c, hlam2]
        exact lambda1_top_resid hm (ZMod.val_lt (1 : ZMod 7))
      have hlam2_mul : ∀ x, runit7 (lam2 * x) = runit7 x :=
        fun x => by rw [runit7_mul, hlam2r, one_mul]
      have hsame13 : runit7 (lam2 * (c * d1)) = runit7 (lam2 * (c * d3)) := by
        rw [hlam2_mul, hlam2_mul, hr, hr, hr1, hr3]
      have hsame23 : runit7 (lam2 * (c * d2)) = runit7 (lam2 * (c * d3)) := by
        rw [hlam2_mul, hlam2_mul, hr, hr, hr2, hr3]
      have hrel45L : runit7 (lam2 * (c * d5)) = 2 * runit7 (lam2 * (c * d4)) := by
        rw [hlam2_mul, hlam2_mul, hrel45c]
      have hlen := c63_len3_top
        (Nat.mul_pos (by positivity) (Nat.mul_pos hcpos hp3)) hsame13 hsame23 he13L he23L
      have hlen' : apLen (({d1, d2, d3} : Finset ℕ).image
          (fun d => qdig7 m ((lam2 * c) * d))) ≤ 3 := by
        simpa [mul_assoc] using hlen
      have hpair' : (2 * qdig7 m ((lam2 * c) * d4) -
          qdig7 m ((lam2 * c) * d5) : ZMod 7) ∉ ({2, 4} : Finset (ZMod 7)) := by
        rw [mul_assoc, mul_assoc, ← etd7_eq_twoX hrel45L, hlam2]
        exact hpair
      exact c63_finish3 (m := m) (A1 := A1) (A2 := A2) (A4 := A4)
        (d1 := d1) (d2 := d2) (d3 := d3) (d4 := d4) (d5 := d5)
        (lam := lam2 * c) (by omega) hpos hunit hs0 hcls1 hcls2 hcls4
        hA1eq hA2eq hA4eq hA2 hA4 hne
        (Nat.prime_seven.not_dvd_mul (multLow_not_dvd h1m) hcnd) hlen' hpair'
    · have hνpos : 0 < padicValNat 7 e45 := by
        have hdvd : 7 ∣ e45 := by
          rw [he45]
          exact dvd7_eMod7_twoX (huc d4 (ne_of_gt hp4) hu4)
            (huc d5 (ne_of_gt hp5) hu5) hrel45c
        rcases Nat.eq_zero_or_pos (padicValNat 7 e45) with hzero | hposv
        · rcases padicValNat.eq_zero_iff.mp hzero with hp | hz | hnd
          · exact absurd hp (by norm_num)
          · exact (he450 hz).elim
          · exact absurd hdvd hnd
        · exact hposv
      obtain ⟨k, hk7, hpair⟩ := lemma7_i_expl
        (huc d4 (ne_of_gt hp4) hu4) (huc d5 (ne_of_gt hp5) hu5)
        (Nat.mul_pos hcpos hp4) (Nat.mul_pos hcpos hp5) hrel45c
        (by rwa [← he45]) (by rwa [← he45]) (X := ({2, 4} : Finset (ZMod 7)))
        (by decide)
      set lam2 := 1 + k * 7 ^ (m - padicValNat 7 e45) with hlam2
      have hlam2r : runit7 lam2 = 1 := by rw [hlam2]; exact runit7_multLow hνlt
      have he13L : eMod7 m (lam2 * (c * d1)) (lam2 * (c * d3)) =
          (2 : ZMod 7).val * 7 ^ m := by
        rw [eMod7_mul hlam2r, he13c, hlam2]
        exact top_resid_multLow hνlt (by decide)
      have he23L : eMod7 m (lam2 * (c * d2)) (lam2 * (c * d3)) =
          (1 : ZMod 7).val * 7 ^ m := by
        rw [eMod7_mul hlam2r, he23c, hlam2]
        exact top_resid_multLow hνlt (by decide)
      have hlam2_mul : ∀ x, runit7 (lam2 * x) = runit7 x :=
        fun x => by rw [runit7_mul, hlam2r, one_mul]
      have hsame13 : runit7 (lam2 * (c * d1)) = runit7 (lam2 * (c * d3)) := by
        rw [hlam2_mul, hlam2_mul, hr, hr, hr1, hr3]
      have hsame23 : runit7 (lam2 * (c * d2)) = runit7 (lam2 * (c * d3)) := by
        rw [hlam2_mul, hlam2_mul, hr, hr, hr2, hr3]
      have hrel45L : runit7 (lam2 * (c * d5)) = 2 * runit7 (lam2 * (c * d4)) := by
        rw [hlam2_mul, hlam2_mul, hrel45c]
      have hlen := c63_len3_top
        (Nat.mul_pos (by positivity) (Nat.mul_pos hcpos hp3)) hsame13 hsame23 he13L he23L
      have hlen' : apLen (({d1, d2, d3} : Finset ℕ).image
          (fun d => qdig7 m ((lam2 * c) * d))) ≤ 3 := by
        simpa [mul_assoc] using hlen
      have hpair' : (2 * qdig7 m ((lam2 * c) * d4) -
          qdig7 m ((lam2 * c) * d5) : ZMod 7) ∉ ({2, 4} : Finset (ZMod 7)) := by
        rw [mul_assoc, mul_assoc, ← etd7_eq_twoX hrel45L, hlam2]
        exact hpair
      exact c63_finish3 (m := m) (A1 := A1) (A2 := A2) (A4 := A4)
        (d1 := d1) (d2 := d2) (d3 := d3) (d4 := d4) (d5 := d5)
        (lam := lam2 * c) (by omega) hpos hunit hs0 hcls1 hcls2 hcls4
        hA1eq hA2eq hA4eq hA2 hA4 hne
        (Nat.prime_seven.not_dvd_mul (multLow_not_dvd hνlt) hcnd) hlen' hpair'

private theorem c63_cell :
    ∀ z i j : ZMod 7,
      (∃ t : ZMod 7, avoids06 ({z + t, z + 1 + t, z + 3 + t, i + 2 * t, j + 4 * t} : Finset (ZMod 7))) ∨
      (2 * z - i, 2 * i - j) ∈ bad63 := by
  decide

private theorem c63_sigma_double :
    ∀ c3 c4 eps1 eps2 : ℕ, c3 < 2 → c4 < 2 → eps1 < 2 → eps2 < 2 →
      ∃ w : ℕ, w < 7 ∧
        (c3 + 2 * w) / 7 = eps1 ∧
        (c4 + 2 * ((c3 + 2 * w) % 7)) / 7 = eps2 := by
  intro c3 c4 eps1 eps2 hc3 hc4 he1 he2
  interval_cases c3 <;> interval_cases c4 <;> interval_cases eps1 <;> interval_cases eps2 <;>
    first
    | exact ⟨0, by decide⟩
    | exact ⟨1, by decide⟩
    | exact ⟨2, by decide⟩
    | exact ⟨3, by decide⟩
    | exact ⟨4, by decide⟩
    | exact ⟨5, by decide⟩
    | exact ⟨6, by decide⟩

private theorem bad63_first_coord :
    ∀ p ∈ bad63, (p : ZMod 7 × ZMod 7).1 ∉ ({0, 1, 6} : Finset (ZMod 7)) := by
  decide

private theorem bad63_first_coord_in :
    ∀ p ∈ bad63, (p : ZMod 7 × ZMod 7).1 ∈ ({2, 3, 4, 5} : Finset (ZMod 7)) := by
  decide

private theorem bad63_second_coord_23 :
    ∀ p ∈ bad63, (p : ZMod 7 × ZMod 7).1 ∈ ({2, 3} : Finset (ZMod 7)) →
      (p : ZMod 7 × ZMod 7).2 ∈ ({2, 3, 4, 5} : Finset (ZMod 7)) := by
  decide

private theorem bad63_second_coord_45 :
    ∀ p ∈ bad63, (p : ZMod 7 × ZMod 7).1 ∈ ({4, 5} : Finset (ZMod 7)) →
      (p : ZMod 7 × ZMod 7).2 ∈ ({1, 2, 3, 4} : Finset (ZMod 7)) := by
  decide

private theorem apLen_1234 :
    apLen ({1, 2, 3, 4} : Finset (ZMod 7)) ≤ 4 := by
  rw [apLen_le_iff _ 4 (by norm_num)]
  exact ⟨1, by decide⟩

private theorem bad63_first_coord_cases :
    ∀ p ∈ bad63, (p : ZMod 7 × ZMod 7).1 ∈ ({2, 3} : Finset (ZMod 7)) ∨
      (p : ZMod 7 × ZMod 7).1 ∈ ({4, 5} : Finset (ZMod 7)) := by
  decide

private theorem bad63_avoid_23 :
    ∀ p ∈ bad63, (p : ZMod 7 × ZMod 7).1 ∈ ({2, 3} : Finset (ZMod 7)) →
      ∀ q ∉ ({2, 3, 4, 5} : Finset (ZMod 7)),
        ∀ diff ∈ ({0, 1, 6} : Finset (ZMod 7)),
          ((p : ZMod 7 × ZMod 7).1 + diff, q) ∉ bad63 := by
  decide

private theorem bad63_avoid_45 :
    ∀ p ∈ bad63, (p : ZMod 7 × ZMod 7).1 ∈ ({4, 5} : Finset (ZMod 7)) →
      ∀ q ∉ ({1, 2, 3, 4} : Finset (ZMod 7)),
        ∀ diff ∈ ({0, 1, 6} : Finset (ZMod 7)),
          ((p : ZMod 7 × ZMod 7).1 + diff, q) ∉ bad63 := by
  decide

private theorem diff_of_pure_top_twoX (δ δ' : ℕ) (hδ : δ < 2) (hδ' : δ' < 2) :
    ((δ : ZMod 7) - (δ' : ZMod 7)) ∈ ({0, 1, 6} : Finset (ZMod 7)) := by
  interval_cases δ <;> interval_cases δ' <;> decide

private theorem c63_union_five_eq {A1 A2 A4 : Finset ℕ} {d1 d2 d3 d4 d5 lam : ℕ}
    {z i j t : ZMod 7} {m : ℕ}
    (hA1 : A1 = {d1, d2, d3}) (hA2 : A2 = {d4}) (hA4 : A4 = {d5})
    (hq1 : qdig7 m (lam * d1) = z + 3)
    (hq2 : qdig7 m (lam * d2) = z + 1)
    (hq3 : qdig7 m (lam * d3) = z)
    (hq4 : qdig7 m (lam * d4) = i)
    (hq5 : qdig7 m (lam * d5) = j) :
    (((A1.image fun d => lam * d).image (qdig7 m)).image (· + t)
      ∪ ((A2.image fun d => lam * d).image (qdig7 m)).image (· + 2 * t)
      ∪ ((A4.image fun d => lam * d).image (qdig7 m)).image (· + 4 * t))
    = ({z + t, z + 1 + t, z + 3 + t, i + 2 * t, j + 4 * t} : Finset (ZMod 7)) := by
  rw [hA1, hA2, hA4]
  simp only [Finset.image_insert, Finset.image_singleton, hq1, hq2, hq3, hq4, hq5]
  ext x
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
  tauto

set_option maxHeartbeats 3000000 in
private theorem c63_case_ii2_top {m : ℕ} (hm : 2 ≤ m)
    {A1 A2 A4 : Finset ℕ}
    (hA2 : A2.card = 1) (hA4 : A4.card = 1)
    (hpos : ∀ d ∈ A1 ∪ A2 ∪ A4, 0 < d)
    (hunit : ∀ d ∈ A1 ∪ A2 ∪ A4, padicValNat 7 d = 0)
    {s : ZMod 7} (hs0 : s ≠ 0)
    (hcls1 : ∀ d ∈ A1, runit7 d = s)
    (hcls2 : ∀ d ∈ A2, runit7 d = 2 * s)
    (hcls4 : ∀ d ∈ A4, runit7 d = 4 * s)
    {d1 d2 d3 d4 d5 : ℕ}
    (hA1eq : A1 = {d1, d2, d3}) (hA2eq : A2 = {d4}) (hA4eq : A4 = {d5})
    (hne : A1.Nonempty)
    (hp1 : 0 < d1) (hp2 : 0 < d2) (hp3 : 0 < d3) (hp4 : 0 < d4) (hp5 : 0 < d5)
    (hu1 : padicValNat 7 d1 = 0) (hu2 : padicValNat 7 d2 = 0)
    (hu3 : padicValNat 7 d3 = 0) (hu4 : padicValNat 7 d4 = 0)
    (hu5 : padicValNat 7 d5 = 0)
    (hr1 : runit7 d1 = s) (hr2 : runit7 d2 = s) (hr3 : runit7 d3 = s)
    (hr4 : runit7 d4 = 2 * s) (hr5 : runit7 d5 = 4 * s)
    (he13 : eMod7 m d1 d3 ≠ 0) (he23 : eMod7 m d2 d3 ≠ 0)
    (hν13 : padicValNat 7 (eMod7 m d1 d3) = m)
    (hν23 : padicValNat 7 (eMod7 m d2 d3) = m)
    (hrat : runit7 (eMod7 m d1 d3) = 3 * runit7 (eMod7 m d2 d3)) :
    ∃ lam : ℕ, ¬ 7 ∣ lam ∧ good7 m lam (A1 ∪ A2 ∪ A4) := by
  obtain ⟨c, hcpos, hc7, hce23, hqc23⟩ := exists_top_scalar_set hν23 he23
    (t := (1 : ZMod 7)) (by decide)
  have hcnd : ¬ 7 ∣ c := fun hd => absurd (Nat.le_of_dvd hcpos hd) (by omega)
  have hrcast : runit7 c = (c : ZMod 7) :=
    runit7_of_padic_zero (padicValNat.eq_zero_of_not_dvd hcnd)
  have hrc : runit7 c ≠ 0 := runit7_ne_zero hcpos
  have hca : (c : ZMod 7) * runit7 (eMod7 m d2 d3) = 1 := by
    have h := qdig7_multTop (l := c) hν23
    rw [hqc23] at h
    exact h.symm
  have he23top : eMod7 m d2 d3 = (runit7 (eMod7 m d2 d3)).val * 7 ^ m := by
    have h := residN_top hν23
    rwa [qdig7_eq_runit7_of_top hν23,
      Nat.mod_eq_of_lt (eMod7_lt _ _ _)] at h
  have he13top : eMod7 m d1 d3 =
      ((3 : ZMod 7) * runit7 (eMod7 m d2 d3)).val * 7 ^ m := by
    have h := residN_top hν13
    rwa [qdig7_eq_runit7_of_top hν13,
      Nat.mod_eq_of_lt (eMod7_lt _ _ _), hrat] at h
  have he23c : eMod7 m (c * d2) (c * d3) = (1 : ZMod 7).val * 7 ^ m := by
    rw [e_smul_top hrc he23top, hca]
  have h3a : (c : ZMod 7) *
      ((3 : ZMod 7) * runit7 (eMod7 m d2 d3)) = 3 := by
    calc
      (c : ZMod 7) * (3 * runit7 (eMod7 m d2 d3)) =
          3 * ((c : ZMod 7) * runit7 (eMod7 m d2 d3)) := by ring
      _ = 3 := by rw [hca, mul_one]
  have he13c : eMod7 m (c * d1) (c * d3) = (3 : ZMod 7).val * 7 ^ m := by
    rw [e_smul_top hrc he13top, h3a]
  have huc : ∀ d : ℕ, d ≠ 0 → padicValNat 7 d = 0 →
      padicValNat 7 (c * d) = 0 := fun _ hd0 hd => by
    rw [padicValNat_mul_seven hcnd hd0, hd]
  have hr : ∀ d : ℕ, runit7 (c * d) = (c : ZMod 7) * runit7 d :=
    fun d => by rw [runit7_mul, hrcast]
  have hrel13c : residueRelOf (c * d1) (c * d3) = residueRel.same :=
    rel_same (by rw [hr, hr, hr1, hr3]) (runit7_ne_zero (Nat.mul_pos hcpos hp3))
  have hrel23c : residueRelOf (c * d2) (c * d3) = residueRel.same :=
    rel_same (by rw [hr, hr, hr2, hr3]) (runit7_ne_zero (Nat.mul_pos hcpos hp3))
  have hrel34c : runit7 (c * d4) = 2 * runit7 (c * d3) := by
    rw [hr, hr, hr4, hr3]; ring
  have hrel45c : runit7 (c * d5) = 2 * runit7 (c * d4) := by
    rw [hr, hr, hr5, hr4]; ring
  have hq23c : qdig7 m (c * d2) = qdig7 m (c * d3) + 1 :=
    qdig_eq_add_of_e_top hrel23c he23c
  have hq13c : qdig7 m (c * d1) = qdig7 m (c * d3) + 3 := by
    have h := qdig_eq_add_of_e_top hrel13c he13c
    simpa using h
  set z := qdig7 m (c * d3)
  set i := qdig7 m (c * d4)
  set j := qdig7 m (c * d5)
  rcases c63_cell z i j with ⟨t, ht⟩ | hbad
  · have hunion := c63_union_five_eq (lam := c) hA1eq hA2eq hA4eq hq13c hq23c rfl rfl rfl (t := t)
    rw [← hunion] at ht
    exact c63_of_avoid (by omega) hpos hunit hs0 hcls1 hcls2 hcls4 hcnd ht
  · have hetd34c : etd7 m (c * d3) (c * d4) = 2 * z - i := etd7_eq_twoX hrel34c
    have hetd45c : etd7 m (c * d4) (c * d5) = 2 * i - j := etd7_eq_twoX hrel45c
    have hpair_bad : (etd7 m (c * d3) (c * d4), etd7 m (c * d4) (c * d5)) ∈ bad63 := by
      rw [hetd34c, hetd45c]
      exact hbad
    have he34ne : eMod7 m (c * d3) (c * d4) ≠ 0 := by
      intro h0
      have hb := qdig_eMod_sub_etd7 (m := m) (x := c * d3) (y := c * d4)
      rw [h0, qdig7_zero] at hb
      have hfin : ∀ z0 : ZMod 7,
          -z0 ∈ ({0, 1, 6} : Finset (ZMod 7)) → z0 ∈ ({0, 1, 6} : Finset (ZMod 7)) := by
        decide
      have h016 : etd7 m (c * d3) (c * d4) ∈ ({0, 1, 6} : Finset (ZMod 7)) :=
        hfin _ (by simpa using hb)
      have hnot := bad63_first_coord (etd7 m (c * d3) (c * d4), etd7 m (c * d4) (c * d5)) hpair_bad
      exact hnot h016
    have hν34le : padicValNat 7 (eMod7 m (c * d3) (c * d4)) ≤ m := enu7_le_of_ne he34ne
    rcases eq_or_lt_of_le hν34le with hν34m | hν34lt
    · have he34top : eMod7 m (c * d3) (c * d4) =
          (runit7 (eMod7 m (c * d3) (c * d4))).val * 7 ^ m := by
        have h := residN_top hν34m
        rwa [qdig7_eq_runit7_of_top hν34m,
          Nat.mod_eq_of_lt (eMod7_lt _ _ _)] at h
      set v34 := runit7 (eMod7 m (c * d3) (c * d4)) with hv34
      by_cases he45top : padicValNat 7 (eMod7 m (c * d4) (c * d5)) = m ∨
          eMod7 m (c * d4) (c * d5) = 0
      · obtain ⟨v45, he45top_eq⟩ : ∃ v45 : ZMod 7,
            eMod7 m (c * d4) (c * d5) = v45.val * 7 ^ m := by
          rcases he45top with hν45m | he45z
          · refine ⟨runit7 (eMod7 m (c * d4) (c * d5)), ?_⟩
            have h := residN_top hν45m
            rwa [qdig7_eq_runit7_of_top hν45m,
              Nat.mod_eq_of_lt (eMod7_lt _ _ _)] at h
          · refine ⟨0, ?_⟩
            rw [he45z]
            simp
        obtain ⟨eps1, eps2, he1, he2, hsafe⟩ := case63_eps_avoid v34 v45
        have heps1val : eps1.val < 2 := by
          simp only [Finset.mem_insert, Finset.mem_singleton] at he1
          rcases he1 with rfl | rfl <;> decide
        have heps2val : eps2.val < 2 := by
          simp only [Finset.mem_insert, Finset.mem_singleton] at he2
          rcases he2 with rfl | rfl <;> decide
        have hc3 : 2 * ((c * d3) % 7 ^ (m - 1)) / 7 ^ (m - 1) < 2 := by
          apply Nat.div_lt_of_lt_mul
          have hlt := Nat.mod_lt (c * d3) (Nat.pow_pos (by norm_num) : 0 < 7 ^ (m - 1))
          omega
        have hc4 : 2 * ((c * d4) % 7 ^ (m - 1)) / 7 ^ (m - 1) < 2 := by
          apply Nat.div_lt_of_lt_mul
          have hlt := Nat.mod_lt (c * d4) (Nat.pow_pos (by norm_num) : 0 < 7 ^ (m - 1))
          omega
        obtain ⟨w, hw7, hsig1, hsig2⟩ :=
          c63_sigma_double _ _ _ _ hc3 hc4 heps1val heps2val
        obtain ⟨k, hk7, hW⟩ := single_carry (m := m)
          (Nat.mul_pos hcpos hp3) (huc d3 (ne_of_gt hp3) hu3) hw7
        set lam2 := 1 + k * 7 ^ (m - 1) with hlam2
        have h1m : 1 < m := by omega
        have hlam2r : runit7 lam2 = 1 := by rw [hlam2]; exact runit7_multLow h1m
        have he13L : eMod7 m (lam2 * (c * d1)) (lam2 * (c * d3)) =
            (3 : ZMod 7).val * 7 ^ m := by
          rw [eMod7_mul hlam2r, he13c, hlam2]
          exact lambda1_top_resid hm (by decide)
        have he23L : eMod7 m (lam2 * (c * d2)) (lam2 * (c * d3)) =
            (1 : ZMod 7).val * 7 ^ m := by
          rw [eMod7_mul hlam2r, he23c, hlam2]
          exact lambda1_top_resid hm (by decide)
        have hlam2_mul : ∀ x, runit7 (lam2 * x) = runit7 x :=
          fun x => by rw [runit7_mul, hlam2r, one_mul]
        have hsame13 : residueRelOf (lam2 * (c * d1)) (lam2 * (c * d3)) = residueRel.same :=
          rel_same (by rw [hlam2_mul, hlam2_mul, hr, hr, hr1, hr3])
            (by rw [hlam2_mul]; exact runit7_ne_zero (Nat.mul_pos hcpos hp3))
        have hsame23 : residueRelOf (lam2 * (c * d2)) (lam2 * (c * d3)) = residueRel.same :=
          rel_same (by rw [hlam2_mul, hlam2_mul, hr, hr, hr2, hr3])
            (by rw [hlam2_mul]; exact runit7_ne_zero (Nat.mul_pos hcpos hp3))
        have hq23L : qdig7 m ((lam2 * c) * d2) = qdig7 m ((lam2 * c) * d3) + 1 := by
          have h := qdig_eq_add_of_e_top hsame23 he23L
          rwa [mul_assoc, mul_assoc]
        have hq13L : qdig7 m ((lam2 * c) * d1) = qdig7 m ((lam2 * c) * d3) + 3 := by
          have h := qdig_eq_add_of_e_top hsame13 he13L
          have h' : qdig7 m (lam2 * (c * d1)) = qdig7 m (lam2 * (c * d3)) + 3 := by simpa using h
          rwa [mul_assoc, mul_assoc]
        obtain ⟨hetd34, hetd45, hAy⟩ := eps_chain hm hrel34c hrel45c he34top he45top_eq (k := k)
        have hetd34' : etd7 m ((lam2 * c) * d3) ((lam2 * c) * d4) = v34 - eps1 := by
          rw [mul_assoc, mul_assoc, hetd34, hW, hsig1, ZMod.natCast_zmod_val]
        have hetd45' : etd7 m ((lam2 * c) * d4) ((lam2 * c) * d5) = v45 - eps2 := by
          rw [mul_assoc, mul_assoc, hetd45, hAy, hW, hsig2, ZMod.natCast_zmod_val]
        set z' := qdig7 m ((lam2 * c) * d3)
        set i' := qdig7 m ((lam2 * c) * d4)
        set j' := qdig7 m ((lam2 * c) * d5)
        rcases c63_cell z' i' j' with ⟨t', ht'⟩ | hbad'
        · have hunion' := c63_union_five_eq (lam := lam2 * c) hA1eq hA2eq hA4eq hq13L hq23L rfl rfl rfl (t := t')
          rw [← hunion'] at ht'
          exact c63_of_avoid (by omega) hpos hunit hs0 hcls1 hcls2 hcls4
            (Nat.prime_seven.not_dvd_mul (multLow_not_dvd h1m) hcnd) ht'
        · exfalso
          have hrel34L : runit7 ((lam2 * c) * d4) = 2 * runit7 ((lam2 * c) * d3) := by
            rw [mul_assoc, mul_assoc, hlam2_mul, hlam2_mul, hrel34c]
          have hrel45L : runit7 ((lam2 * c) * d5) = 2 * runit7 ((lam2 * c) * d4) := by
            rw [mul_assoc, mul_assoc, hlam2_mul, hlam2_mul, hrel45c]
          have hetd34_val : 2 * z' - i' = etd7 m ((lam2 * c) * d3) ((lam2 * c) * d4) :=
            (etd7_eq_twoX hrel34L).symm
          have hetd45_val : 2 * i' - j' = etd7 m ((lam2 * c) * d4) ((lam2 * c) * d5) :=
            (etd7_eq_twoX hrel45L).symm
          rw [hetd34_val, hetd45_val, hetd34', hetd45'] at hbad'
          exact hsafe hbad'
      · have hnot : ¬ (padicValNat 7 (eMod7 m (c * d4) (c * d5)) = m ∨ eMod7 m (c * d4) (c * d5) = 0) := he45top
        rw [not_or] at hnot
        have he45ne : eMod7 m (c * d4) (c * d5) ≠ 0 := hnot.2
        have hν45le : padicValNat 7 (eMod7 m (c * d4) (c * d5)) ≤ m := enu7_le_of_ne he45ne
        have hν45lt : padicValNat 7 (eMod7 m (c * d4) (c * d5)) < m :=
          lt_of_le_of_ne hν45le hnot.1
        have hν45pos : 0 < padicValNat 7 (eMod7 m (c * d4) (c * d5)) := by
          have hdvd : 7 ∣ eMod7 m (c * d4) (c * d5) :=
            dvd7_eMod7_twoX (huc d4 (ne_of_gt hp4) hu4) (huc d5 (ne_of_gt hp5) hu5) hrel45c
          rcases Nat.eq_zero_or_pos (padicValNat 7 (eMod7 m (c * d4) (c * d5))) with hz | hp
          · rcases padicValNat.eq_zero_iff.mp hz with hp' | hz' | hnd
            · exact absurd hp' (by norm_num)
            · exact (he45ne hz').elim
            · exact absurd hdvd hnd
          · exact hp
        rcases bad63_first_coord_cases _ hpair_bad with hcase23 | hcase45
        · obtain ⟨k, hk7, hkX⟩ := lemma7_i_expl
            (huc d4 (ne_of_gt hp4) hu4) (huc d5 (ne_of_gt hp5) hu5)
            (Nat.mul_pos hcpos hp4) (Nat.mul_pos hcpos hp5) hrel45c
            hν45pos hν45lt apLen_2345
          set lam2 := 1 + k * 7 ^ (m - padicValNat 7 (eMod7 m (c * d4) (c * d5))) with hlam2
          have hlam2r : runit7 lam2 = 1 := by rw [hlam2]; exact runit7_multLow hν45lt
          have he13L : eMod7 m (lam2 * (c * d1)) (lam2 * (c * d3)) =
              (3 : ZMod 7).val * 7 ^ m := by
            rw [eMod7_mul hlam2r, he13c, hlam2]
            exact top_resid_multLow hν45lt (by decide)
          have he23L : eMod7 m (lam2 * (c * d2)) (lam2 * (c * d3)) =
              (1 : ZMod 7).val * 7 ^ m := by
            rw [eMod7_mul hlam2r, he23c, hlam2]
            exact top_resid_multLow hν45lt (by decide)
          have he34L : eMod7 m (lam2 * (c * d3)) (lam2 * (c * d4)) =
              v34.val * 7 ^ m := by
            rw [eMod7_mul hlam2r, he34top, hlam2]
            exact top_resid_multLow hν45lt (runit7_ne_zero (Nat.pos_of_ne_zero he34ne))
          have hlam2_mul : ∀ x, runit7 (lam2 * x) = runit7 x :=
            fun x => by rw [runit7_mul, hlam2r, one_mul]
          have hsame13 : residueRelOf (lam2 * (c * d1)) (lam2 * (c * d3)) = residueRel.same :=
            rel_same (by rw [hlam2_mul, hlam2_mul, hr, hr, hr1, hr3])
              (by rw [hlam2_mul]; exact runit7_ne_zero (Nat.mul_pos hcpos hp3))
          have hsame23 : residueRelOf (lam2 * (c * d2)) (lam2 * (c * d3)) = residueRel.same :=
            rel_same (by rw [hlam2_mul, hlam2_mul, hr, hr, hr2, hr3])
              (by rw [hlam2_mul]; exact runit7_ne_zero (Nat.mul_pos hcpos hp3))
          have hq23L : qdig7 m ((lam2 * c) * d2) = qdig7 m ((lam2 * c) * d3) + 1 := by
            have h := qdig_eq_add_of_e_top hsame23 he23L
            rwa [mul_assoc, mul_assoc]
          have hq13L : qdig7 m ((lam2 * c) * d1) = qdig7 m ((lam2 * c) * d3) + 3 := by
            have h := qdig_eq_add_of_e_top hsame13 he13L
            have h' : qdig7 m (lam2 * (c * d1)) = qdig7 m (lam2 * (c * d3)) + 3 := by simpa using h
            rwa [mul_assoc, mul_assoc]
          set z' := qdig7 m ((lam2 * c) * d3)
          set i' := qdig7 m ((lam2 * c) * d4)
          set j' := qdig7 m ((lam2 * c) * d5)
          rcases c63_cell z' i' j' with ⟨t', ht'⟩ | hbad'
          · have hunion' := c63_union_five_eq (lam := lam2 * c) hA1eq hA2eq hA4eq hq13L hq23L rfl rfl rfl (t := t')
            rw [← hunion'] at ht'
            exact c63_of_avoid (by omega) hpos hunit hs0 hcls1 hcls2 hcls4
              (Nat.prime_seven.not_dvd_mul (multLow_not_dvd hν45lt) hcnd) ht'
          · exfalso
            have hrel34L : runit7 ((lam2 * c) * d4) = 2 * runit7 ((lam2 * c) * d3) := by
              rw [mul_assoc, mul_assoc, hlam2_mul, hlam2_mul, hrel34c]
            have hrel45L : runit7 ((lam2 * c) * d5) = 2 * runit7 ((lam2 * c) * d4) := by
              rw [mul_assoc, mul_assoc, hlam2_mul, hlam2_mul, hrel45c]
            obtain ⟨δ, hδ2, -, hetd_orig⟩ := pure_top_twoX hrel34c he34top
            obtain ⟨δ', hδ'2, -, hetd_new⟩ := pure_top_twoX hrel34L (by rw [mul_assoc, mul_assoc]; exact he34L)
            have hetd_diff : (2 * z' - i') = etd7 m (c * d3) (c * d4) + ((δ : ZMod 7) - (δ' : ZMod 7)) := by
              have h1 : etd7 m (c * d3) (c * d4) = v34 - (δ : ZMod 7) := hetd_orig
              have h2 : 2 * z' - i' = v34 - (δ' : ZMod 7) := by
                rw [← etd7_eq_twoX hrel34L, hetd_new]
              linear_combination h2 - h1
            have hdiff_mem := diff_of_pure_top_twoX δ δ' hδ2 hδ'2
            have hnot45 : 2 * i' - j' ∉ ({2, 3, 4, 5} : Finset (ZMod 7)) := by
              have h : 2 * i' - j' = etd7 m ((lam2 * c) * d4) ((lam2 * c) * d5) := by
                rw [← etd7_eq_twoX hrel45L]
              rw [h, mul_assoc, mul_assoc]
              exact hkX
            have hnotbad := bad63_avoid_23 (etd7 m (c * d3) (c * d4), etd7 m (c * d4) (c * d5))
              hpair_bad hcase23 (2 * i' - j') hnot45
              ((δ : ZMod 7) - (δ' : ZMod 7)) hdiff_mem
            rw [← hetd_diff] at hnotbad
            exact hnotbad hbad'
        · obtain ⟨k, hk7, hkX⟩ := lemma7_i_expl
            (huc d4 (ne_of_gt hp4) hu4) (huc d5 (ne_of_gt hp5) hu5)
            (Nat.mul_pos hcpos hp4) (Nat.mul_pos hcpos hp5) hrel45c
            hν45pos hν45lt apLen_1234
          set lam2 := 1 + k * 7 ^ (m - padicValNat 7 (eMod7 m (c * d4) (c * d5))) with hlam2
          have hlam2r : runit7 lam2 = 1 := by rw [hlam2]; exact runit7_multLow hν45lt
          have he13L : eMod7 m (lam2 * (c * d1)) (lam2 * (c * d3)) =
              (3 : ZMod 7).val * 7 ^ m := by
            rw [eMod7_mul hlam2r, he13c, hlam2]
            exact top_resid_multLow hν45lt (by decide)
          have he23L : eMod7 m (lam2 * (c * d2)) (lam2 * (c * d3)) =
              (1 : ZMod 7).val * 7 ^ m := by
            rw [eMod7_mul hlam2r, he23c, hlam2]
            exact top_resid_multLow hν45lt (by decide)
          have he34L : eMod7 m (lam2 * (c * d3)) (lam2 * (c * d4)) =
              v34.val * 7 ^ m := by
            rw [eMod7_mul hlam2r, he34top, hlam2]
            exact top_resid_multLow hν45lt (runit7_ne_zero (Nat.pos_of_ne_zero he34ne))
          have hlam2_mul : ∀ x, runit7 (lam2 * x) = runit7 x :=
            fun x => by rw [runit7_mul, hlam2r, one_mul]
          have hsame13 : residueRelOf (lam2 * (c * d1)) (lam2 * (c * d3)) = residueRel.same :=
            rel_same (by rw [hlam2_mul, hlam2_mul, hr, hr, hr1, hr3])
              (by rw [hlam2_mul]; exact runit7_ne_zero (Nat.mul_pos hcpos hp3))
          have hsame23 : residueRelOf (lam2 * (c * d2)) (lam2 * (c * d3)) = residueRel.same :=
            rel_same (by rw [hlam2_mul, hlam2_mul, hr, hr, hr2, hr3])
              (by rw [hlam2_mul]; exact runit7_ne_zero (Nat.mul_pos hcpos hp3))
          have hq23L : qdig7 m ((lam2 * c) * d2) = qdig7 m ((lam2 * c) * d3) + 1 := by
            have h := qdig_eq_add_of_e_top hsame23 he23L
            rwa [mul_assoc, mul_assoc]
          have hq13L : qdig7 m ((lam2 * c) * d1) = qdig7 m ((lam2 * c) * d3) + 3 := by
            have h := qdig_eq_add_of_e_top hsame13 he13L
            have h' : qdig7 m (lam2 * (c * d1)) = qdig7 m (lam2 * (c * d3)) + 3 := by simpa using h
            rwa [mul_assoc, mul_assoc]
          set z' := qdig7 m ((lam2 * c) * d3)
          set i' := qdig7 m ((lam2 * c) * d4)
          set j' := qdig7 m ((lam2 * c) * d5)
          rcases c63_cell z' i' j' with ⟨t', ht'⟩ | hbad'
          · have hunion' := c63_union_five_eq (lam := lam2 * c) hA1eq hA2eq hA4eq hq13L hq23L rfl rfl rfl (t := t')
            rw [← hunion'] at ht'
            exact c63_of_avoid (by omega) hpos hunit hs0 hcls1 hcls2 hcls4
              (Nat.prime_seven.not_dvd_mul (multLow_not_dvd hν45lt) hcnd) ht'
          · exfalso
            have hrel34L : runit7 ((lam2 * c) * d4) = 2 * runit7 ((lam2 * c) * d3) := by
              rw [mul_assoc, mul_assoc, hlam2_mul, hlam2_mul, hrel34c]
            have hrel45L : runit7 ((lam2 * c) * d5) = 2 * runit7 ((lam2 * c) * d4) := by
              rw [mul_assoc, mul_assoc, hlam2_mul, hlam2_mul, hrel45c]
            obtain ⟨δ, hδ2, -, hetd_orig⟩ := pure_top_twoX hrel34c he34top
            obtain ⟨δ', hδ'2, -, hetd_new⟩ := pure_top_twoX hrel34L (by rw [mul_assoc, mul_assoc]; exact he34L)
            have hetd_diff : (2 * z' - i') = etd7 m (c * d3) (c * d4) + ((δ : ZMod 7) - (δ' : ZMod 7)) := by
              have h1 : etd7 m (c * d3) (c * d4) = v34 - (δ : ZMod 7) := hetd_orig
              have h2 : 2 * z' - i' = v34 - (δ' : ZMod 7) := by
                rw [← etd7_eq_twoX hrel34L, hetd_new]
              linear_combination h2 - h1
            have hdiff_mem := diff_of_pure_top_twoX δ δ' hδ2 hδ'2
            have hnot45 : 2 * i' - j' ∉ ({1, 2, 3, 4} : Finset (ZMod 7)) := by
              have h : 2 * i' - j' = etd7 m ((lam2 * c) * d4) ((lam2 * c) * d5) := by
                rw [← etd7_eq_twoX hrel45L]
              rw [h, mul_assoc, mul_assoc]
              exact hkX
            have hnotbad := bad63_avoid_45 (etd7 m (c * d3) (c * d4), etd7 m (c * d4) (c * d5))
              hpair_bad hcase45 (2 * i' - j') hnot45
              ((δ : ZMod 7) - (δ' : ZMod 7)) hdiff_mem
            rw [← hetd_diff] at hnotbad
            exact hnotbad hbad'
    · have hν34pos : 0 < padicValNat 7 (eMod7 m (c * d3) (c * d4)) := by
        have hdvd : 7 ∣ eMod7 m (c * d3) (c * d4) :=
          dvd7_eMod7_twoX (huc d3 (ne_of_gt hp3) hu3) (huc d4 (ne_of_gt hp4) hu4) hrel34c
        rcases Nat.eq_zero_or_pos (padicValNat 7 (eMod7 m (c * d3) (c * d4))) with hz | hp
        · rcases padicValNat.eq_zero_iff.mp hz with hp' | hz' | hnd
          · exact absurd hp' (by norm_num)
          · exact (he34ne hz').elim
          · exact absurd hdvd hnd
        · exact hp
      obtain ⟨k, hk7, hkX⟩ := lemma7_i_expl
        (huc d3 (ne_of_gt hp3) hu3) (huc d4 (ne_of_gt hp4) hu4)
        (Nat.mul_pos hcpos hp3) (Nat.mul_pos hcpos hp4) hrel34c
        hν34pos hν34lt apLen_2345
      set lam2 := 1 + k * 7 ^ (m - padicValNat 7 (eMod7 m (c * d3) (c * d4))) with hlam2
      have hlam2r : runit7 lam2 = 1 := by rw [hlam2]; exact runit7_multLow hν34lt
      have he13L : eMod7 m (lam2 * (c * d1)) (lam2 * (c * d3)) =
          (3 : ZMod 7).val * 7 ^ m := by
        rw [eMod7_mul hlam2r, he13c, hlam2]
        exact top_resid_multLow hν34lt (by decide)
      have he23L : eMod7 m (lam2 * (c * d2)) (lam2 * (c * d3)) =
          (1 : ZMod 7).val * 7 ^ m := by
        rw [eMod7_mul hlam2r, he23c, hlam2]
        exact top_resid_multLow hν34lt (by decide)
      have hlam2_mul : ∀ x, runit7 (lam2 * x) = runit7 x :=
        fun x => by rw [runit7_mul, hlam2r, one_mul]
      have hsame13 : residueRelOf (lam2 * (c * d1)) (lam2 * (c * d3)) = residueRel.same :=
        rel_same (by rw [hlam2_mul, hlam2_mul, hr, hr, hr1, hr3])
          (by rw [hlam2_mul]; exact runit7_ne_zero (Nat.mul_pos hcpos hp3))
      have hsame23 : residueRelOf (lam2 * (c * d2)) (lam2 * (c * d3)) = residueRel.same :=
        rel_same (by rw [hlam2_mul, hlam2_mul, hr, hr, hr2, hr3])
          (by rw [hlam2_mul]; exact runit7_ne_zero (Nat.mul_pos hcpos hp3))
      have hq23L : qdig7 m ((lam2 * c) * d2) = qdig7 m ((lam2 * c) * d3) + 1 := by
        have h := qdig_eq_add_of_e_top hsame23 he23L
        rwa [mul_assoc, mul_assoc]
      have hq13L : qdig7 m ((lam2 * c) * d1) = qdig7 m ((lam2 * c) * d3) + 3 := by
        have h := qdig_eq_add_of_e_top hsame13 he13L
        have h' : qdig7 m (lam2 * (c * d1)) = qdig7 m (lam2 * (c * d3)) + 3 := by simpa using h
        rwa [mul_assoc, mul_assoc]
      set z' := qdig7 m ((lam2 * c) * d3)
      set i' := qdig7 m ((lam2 * c) * d4)
      set j' := qdig7 m ((lam2 * c) * d5)
      rcases c63_cell z' i' j' with ⟨t', ht'⟩ | hbad'
      · have hunion' := c63_union_five_eq (lam := lam2 * c) hA1eq hA2eq hA4eq hq13L hq23L rfl rfl rfl (t := t')
        rw [← hunion'] at ht'
        exact c63_of_avoid (by omega) hpos hunit hs0 hcls1 hcls2 hcls4
          (Nat.prime_seven.not_dvd_mul (multLow_not_dvd hν34lt) hcnd) ht'
      · exfalso
        have h1 := bad63_first_coord_in _ hbad'
        have hrel34L : runit7 ((lam2 * c) * d4) = 2 * runit7 ((lam2 * c) * d3) := by
          rw [mul_assoc, mul_assoc, hlam2_mul, hlam2_mul, hrel34c]
        have hetd' : 2 * z' - i' = etd7 m ((lam2 * c) * d3) ((lam2 * c) * d4) :=
          (etd7_eq_twoX hrel34L).symm
        rw [hetd'] at h1
        have hnot : etd7 m ((lam2 * c) * d3) ((lam2 * c) * d4) ∉ ({2, 3, 4, 5} : Finset (ZMod 7)) := by
          have h : etd7 m ((lam2 * c) * d3) ((lam2 * c) * d4) =
              etd7 m (lam2 * (c * d3)) (lam2 * (c * d4)) := by rw [mul_assoc, mul_assoc]
          rw [h]
          exact hkX
        exact hnot h1

/-! ### §6.3 ii.2-low bad-pair rescue: level bookkeeping helpers

The remaining `hpair`-false branch of `c63_case_ii2_low` follows the
paper's §6.3 (ii.2) "low" argument: split on `ν(e45)` relative to the
common `A1`-level `h = ν(e13) = ν(e23)`.  The three subcases are handled
by `c63_ii2_low_lt` (`ν45 < h`: a `Λ_h` exclusion step then a `Λ_{ν45}`
normalization of `e45`), `c63_ii2_low_gt` (`ν45 > h`: normalize `e45`
first — `Λ_{ν45}` or a scalar — then the `Λ_h` table `c63_l9ii3`), and
`c63_eqlevel` (`ν45 = h`: normalize `f = e13 − E` at level `> h`, then
the finite `case63_table` lookup, with the `(0,3)` cell rescued by the
doubling `case63_table_rescue`).  The `E` parameter is `e45` for
`r(e45) = r(e13)` and `7^{m+1} − e45` for `r(e45) = −r(e13)`, which makes
the equal/opposite-residue cases uniform. -/

/-- **Block form**: `e ≡ r(e)·7^{ν(e)} (mod 7^{ν(e)+1})` for `e ≠ 0`. -/
private theorem c63_nat_mod_pow_succ {e h : ℕ} (he : e ≠ 0)
    (hν : padicValNat 7 e = h) :
    e % 7 ^ (h + 1) = (runit7 e).val * 7 ^ h := by
  set u := Nat.divMaxPow e 7 with hu
  have he_eq : e = u * 7 ^ h := by
    have hh := Nat.divMaxPow_mul_pow_padicValNat 7 e
    rw [hν] at hh
    exact hh.symm
  have hmod : e % 7 ^ (h + 1) = (u % 7) * 7 ^ h := by
    rw [he_eq, pow_succ', Nat.mul_mod_mul_right]
  have hdiv : e / 7 ^ h = u := by
    rw [he_eq]
    exact Nat.mul_div_cancel _ (Nat.pow_pos (by norm_num))
  have hr : (runit7 e).val = u % 7 := by
    unfold runit7
    rw [hν, hdiv, ZMod.val_natCast]
  rw [hmod, hr]

/-- A natural `w` congruent to `s·7^h (mod 7^{h+1})` with `0 < s < 7` has
level exactly `h` and unit digit `s`. -/
private theorem c63_level_of_mod_block {w h s : ℕ}
    (hmod : w % 7 ^ (h + 1) = s * 7 ^ h) (hs : 0 < s) (hs7 : s < 7) :
    w ≠ 0 ∧ padicValNat 7 w = h ∧ runit7 w = (s : ZMod 7) := by
  have hP : 0 < 7 ^ h := Nat.pow_pos (by norm_num)
  have hw_eq : w = 7 ^ h * (s + 7 * (w / 7 ^ (h + 1))) := by
    conv_lhs => rw [← Nat.div_add_mod w (7 ^ (h + 1))]
    rw [hmod, pow_succ']
    ring
  have hw0 : w ≠ 0 := by
    rintro rfl
    rw [Nat.zero_mod] at hmod
    rcases Nat.mul_eq_zero.mp hmod.symm with hs0 | h70
    · omega
    · exact absurd h70 hP.ne'
  have hν : padicValNat 7 w = h := by
    have hdvd : 7 ^ h ∣ w := ⟨_, hw_eq⟩
    have hndvd : ¬ 7 ^ (h + 1) ∣ w := by
      intro hd
      rw [Nat.dvd_iff_mod_eq_zero] at hd
      rw [hmod] at hd
      rcases Nat.mul_eq_zero.mp hd with hs0 | h70
      · omega
      · exact absurd h70 hP.ne'
    have hle := (Nat.pow_dvd_iff_le_padicValNat (by norm_num) hw0).mp hdvd
    have hlt : padicValNat 7 w < h + 1 := by
      by_contra hc
      push_neg at hc
      exact hndvd ((Nat.pow_dvd_iff_le_padicValNat (by norm_num) hw0).mpr hc)
    omega
  refine ⟨hw0, hν, ?_⟩
  unfold runit7
  rw [hν]
  have hdiv : w / 7 ^ h = s + 7 * (w / 7 ^ (h + 1)) := by
    conv_lhs => rw [hw_eq]
    exact Nat.mul_div_cancel_left _ hP
  rw [hdiv, Nat.cast_add, Nat.cast_mul,
    show ((7 : ℕ) : ZMod 7) = 0 from ZMod.natCast_self 7, zero_mul, add_zero]

/-- The negated residue `N − e` (for `0 < e < N`, `ν(e) ≤ m`) has the
same level as `e` and unit `−r(e)`. -/
private theorem c63_neg_resid_level {m e : ℕ} (he : e ≠ 0)
    (helt : e < 7 ^ (m + 1)) (hνm : padicValNat 7 e ≤ m) :
    padicValNat 7 (7 ^ (m + 1) - e) = padicValNat 7 e ∧
    runit7 (7 ^ (m + 1) - e) = - runit7 e := by
  set h := padicValNat 7 e with hh
  have hub := c63_nat_mod_pow_succ he rfl
  have hu7 : (runit7 e).val < 7 := ZMod.val_lt _
  have hu0 : 0 < (runit7 e).val := by
    rcases Nat.eq_zero_or_pos (runit7 e).val with h0 | h0
    · exfalso
      rw [ZMod.val_eq_zero] at h0
      exact runit7_ne_zero (Nat.pos_of_ne_zero he) h0
    · exact h0
  have hmod : (7 ^ (m + 1) - e) % 7 ^ (h + 1)
      = (7 - (runit7 e).val) * 7 ^ h := by
    obtain ⟨K, hK⟩ := Nat.pow_dvd_pow 7 (by omega : h + 1 ≤ m + 1)
    have hK' : 7 ^ (m + 1) = K * 7 ^ (h + 1) := by rw [hK, mul_comm]
    have hdec : 7 ^ (m + 1) - e
        = (K - e / 7 ^ (h + 1) - 1) * 7 ^ (h + 1)
          + (7 ^ (h + 1) - e % 7 ^ (h + 1)) := by
      have he' := Nat.div_add_mod e (7 ^ (h + 1))
      rw [mul_comm] at he'
      have helt' : e / 7 ^ (h + 1) < K := by
        rw [Nat.div_lt_iff_lt_mul (Nat.pow_pos (by norm_num)), ← hK']
        exact helt
      have hr : e % 7 ^ (h + 1) < 7 ^ (h + 1) :=
        Nat.mod_lt _ (Nat.pow_pos (by norm_num))
      have hoP : e / 7 ^ (h + 1) * 7 ^ (h + 1) + 7 ^ (h + 1)
          ≤ K * 7 ^ (h + 1) := by
        have hle : (e / 7 ^ (h + 1) + 1) * 7 ^ (h + 1)
            ≤ K * 7 ^ (h + 1) :=
          Nat.mul_le_mul_right _ (by omega)
        rwa [Nat.add_mul, one_mul] at hle
      have hexp : (K - e / 7 ^ (h + 1) - 1) * 7 ^ (h + 1)
          = K * 7 ^ (h + 1) - e / 7 ^ (h + 1) * 7 ^ (h + 1)
            - 7 ^ (h + 1) := by
        rw [Nat.sub_mul, Nat.sub_mul, one_mul]
      rw [hexp, hK']
      omega
    rw [hdec]
    have hsplit : ((K - e / 7 ^ (h + 1) - 1) * 7 ^ (h + 1)
          + (7 ^ (h + 1) - e % 7 ^ (h + 1))) % 7 ^ (h + 1)
        = (7 ^ (h + 1) - e % 7 ^ (h + 1)) % 7 ^ (h + 1) := by
      rw [add_comm,
        mul_comm (K - e / 7 ^ (h + 1) - 1) (7 ^ (h + 1))]
      exact Nat.add_mul_mod_self_left _ _ _
    rw [hsplit]
    have hlt' : 7 ^ (h + 1) - e % 7 ^ (h + 1) < 7 ^ (h + 1) := by
      have hpos : 0 < e % 7 ^ (h + 1) := by
        rw [hub]
        exact Nat.mul_pos hu0 (Nat.pow_pos (by norm_num))
      omega
    rw [Nat.mod_eq_of_lt hlt', hub, pow_succ', Nat.sub_mul]
  have ⟨hw0, hνw, hrw⟩ :=
    c63_level_of_mod_block hmod (by omega : 0 < 7 - (runit7 e).val)
      (by omega : 7 - (runit7 e).val < 7)
  refine ⟨hνw, ?_⟩
  rw [hrw]
  rw [Nat.cast_sub (by omega : (runit7 e).val ≤ 7)]
  push_cast
  rw [show (7 : ZMod 7) = 0 from by decide, zero_sub,
    ZMod.natCast_zmod_val]

/-- Leading digit of the complemented residue `N − x` (nonzero low
part): `q(N − x) = −q(x) − 1`. -/
private theorem c63_qdig_compl {m x : ℕ}
    (hxl : x % 7 ^ m ≠ 0) :
    qdig7 m ((7 ^ (m + 1) - x % 7 ^ (m + 1)) % 7 ^ (m + 1))
      = - qdig7 m x - 1 := by
  obtain ⟨q, f, hX, hq, hf⟩ := residue_decomp (m := m) (x := x)
  have hN : (0 : ℕ) < 7 ^ (m + 1) := Nat.pow_pos (by norm_num)
  have hNe : (7 : ℕ) ^ (m + 1) = 7 * 7 ^ m := pow_succ' 7 m
  have hf0 : 0 < f := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · exfalso
      apply hxl
      have hmod : x % 7 ^ (m + 1) % 7 ^ m = x % 7 ^ m :=
        Nat.mod_mod_of_dvd x (Nat.pow_dvd_pow 7 (Nat.le_succ m))
      rw [← hmod, hX, h0, add_zero]
      exact Nat.mod_eq_zero_of_dvd (dvd_mul_left _ _)
    · exact h0
  have hq6 : q ≤ 6 := by
    have hxlt : x % 7 ^ (m + 1) < 7 ^ (m + 1) := Nat.mod_lt _ hN
    rw [hX, hNe] at hxlt
    by_contra hc
    push Not at hc
    have hle : 7 * 7 ^ m ≤ q * 7 ^ m + f := by
      calc 7 * 7 ^ m ≤ q * 7 ^ m := Nat.mul_le_mul_right _ hc
        _ ≤ q * 7 ^ m + f := Nat.le_add_right _ _
    omega
  -- `N − x = (6 − q)·7^m + (7^m − f)`
  have hlt : (6 - q) * 7 ^ m + (7 ^ m - f) < 7 ^ (m + 1) := by
    have h1 : (6 - q) * 7 ^ m ≤ 6 * 7 ^ m :=
      Nat.mul_le_mul_right _ (by omega)
    rw [hNe]
    omega
  have hcalc : 7 ^ (m + 1) - (q * 7 ^ m + f)
      = (6 - q) * 7 ^ m + (7 ^ m - f) := by
    have hs1 : 7 * 7 ^ m - (q * 7 ^ m + f) = (7 - q) * 7 ^ m - f := by
      have h1 : (7 - q) * 7 ^ m = 7 * 7 ^ m - q * 7 ^ m :=
        Nat.sub_mul 7 q (7 ^ m)
      rw [h1]
      omega
    have hs2 : 7 - q = (6 - q) + 1 := by omega
    rw [hNe, hs1, hs2, add_mul, one_mul,
      Nat.add_sub_assoc (by omega : f ≤ 7 ^ m)]
  have hbody : (7 ^ (m + 1) - x % 7 ^ (m + 1)) % 7 ^ (m + 1)
      = (6 - q) * 7 ^ m + (7 ^ m - f) := by
    rw [hX, hcalc]
    exact Nat.mod_eq_of_lt hlt
  have hq' : qdig7 m x = (q : ZMod 7) := by
    unfold qdig7
    rw [hX, mul_pow_add_div hf]
  rw [hbody, hq']
  unfold qdig7
  rw [Nat.mod_eq_of_lt hlt,
    mul_pow_add_div (by omega : 7 ^ m - f < 7 ^ m)]
  have hcast : ((6 - q : ℕ) : ZMod 7) = -(q : ZMod 7) - 1 := by
    rw [Nat.cast_sub (by omega : q ≤ 6)]
    push_cast
    rw [show (6 : ZMod 7) = -1 from by decide]
    ring
  exact hcast

/-- `ν(x) < m` forces a nonzero low part (`x % 7^m ≠ 0`). -/
private theorem c63_low_ne_of_level {m x : ℕ} (hx : x ≠ 0)
    (hν : padicValNat 7 x < m) : x % 7 ^ m ≠ 0 := by
  intro h0
  have hdvd : 7 ^ m ∣ x := Nat.dvd_iff_mod_eq_zero.mpr h0
  have : m ≤ padicValNat 7 x :=
    (Nat.pow_dvd_iff_le_padicValNat (by norm_num) hx).mp hdvd
  omega

/-- `ν(x) < m` forces `x % 7^{m+1} ≠ 0` (same argument). -/
private theorem c63_res_ne_of_level {m x : ℕ} (hx : x ≠ 0)
    (hν : padicValNat 7 x < m + 1) : x % 7 ^ (m + 1) ≠ 0 := by
  intro h0
  have hdvd : 7 ^ (m + 1) ∣ x := Nat.dvd_iff_mod_eq_zero.mpr h0
  have : m + 1 ≤ padicValNat 7 x :=
    (Nat.pow_dvd_iff_le_padicValNat (by norm_num) hx).mp hdvd
  omega

/-- Bad-pair rescue table for `ν(e45) < h` (`ii.2` low, first `Λ_h`
step): a `t` with `q13 + 3t, q23 + t ∈ {0,5,6}` avoiding the two
configurations `(0,5)`, `(5,0)` that can force `apLen = 4` after the
second normalization. -/
private theorem c63_low_lt_table :
    ∀ q13 q23 : ZMod 7, ∃ t : ZMod 7,
      q13 + 3 * t ∈ ({0, 5, 6} : Finset (ZMod 7)) ∧
      q23 + t ∈ ({0, 5, 6} : Finset (ZMod 7)) ∧
      ¬ (q13 + 3 * t = 0 ∧ q23 + t = 5) ∧
      ¬ (q13 + 3 * t = 5 ∧ q23 + t = 0) := by
  decide

/-- For `q13,q23 ∈ {0,5,6}` with `(q13,q23) ∉ {(0,5),(5,0)}` and borrows
`b13,b23 ∈ {0,1}`, the digit set `{0, q23+b23, q13+b13}` has all
pairwise differences in `{0,1,2,5,6}` (so `apLen ≤ 3`). -/
private theorem c63_low_lt_diffs :
    ∀ q13 q23 b13 b23 : ZMod 7,
      q13 ∈ ({0, 5, 6} : Finset (ZMod 7)) →
      q23 ∈ ({0, 5, 6} : Finset (ZMod 7)) →
      b13 ∈ ({0, 1} : Finset (ZMod 7)) →
      b23 ∈ ({0, 1} : Finset (ZMod 7)) →
      ¬ (q13 = 0 ∧ q23 = 5) → ¬ (q13 = 5 ∧ q23 = 0) →
      ∀ x ∈ ({0, q23 + b23, q13 + b13} : Finset (ZMod 7)),
        ∀ y ∈ ({0, q23 + b23, q13 + b13} : Finset (ZMod 7)),
          x - y ∈ ({0, 1, 2, 5, 6} : Finset (ZMod 7)) := by
  decide

/-- §6.3 (ii.2) low subcase `ν(e45) < h`: choose `Λ_h` so the
`(e13,e23)`-pair digits avoid `(0,5)`/`(5,0)`, then a `Λ_{ν45}` step
sets `q(e45) = 0` while preserving the `A1` residues
(`residN_multLow7`). -/
private theorem c63_ii2_low_lt {m : ℕ} (hm : 2 ≤ m)
    {A1 A2 A4 : Finset ℕ}
    (hA2 : A2.card = 1) (hA4 : A4.card = 1)
    (hpos : ∀ d ∈ A1 ∪ A2 ∪ A4, 0 < d)
    (hunit : ∀ d ∈ A1 ∪ A2 ∪ A4, padicValNat 7 d = 0)
    {s : ZMod 7} (hs0 : s ≠ 0)
    (hcls1 : ∀ d ∈ A1, runit7 d = s)
    (hcls2 : ∀ d ∈ A2, runit7 d = 2 * s)
    (hcls4 : ∀ d ∈ A4, runit7 d = 4 * s)
    {d1 d2 d3 d4 d5 : ℕ}
    (hA1eq : A1 = {d1, d2, d3}) (hA2eq : A2 = {d4}) (hA4eq : A4 = {d5})
    (hne : A1.Nonempty)
    (hp1 : 0 < d1) (hp2 : 0 < d2) (hp3 : 0 < d3) (hp4 : 0 < d4) (hp5 : 0 < d5)
    (hr1 : runit7 d1 = s) (hr2 : runit7 d2 = s) (hr3 : runit7 d3 = s)
    (hr4 : runit7 d4 = 2 * s) (hr5 : runit7 d5 = 4 * s)
    (hνeq : padicValNat 7 (eMod7 m d1 d3) = padicValNat 7 (eMod7 m d2 d3))
    (hνm : padicValNat 7 (eMod7 m d2 d3) < m)
    (hrat : runit7 (eMod7 m d1 d3) = 3 * runit7 (eMod7 m d2 d3))
    (he45 : eMod7 m d4 d5 ≠ 0)
    (hν45 : padicValNat 7 (eMod7 m d4 d5)
      < padicValNat 7 (eMod7 m d2 d3)) :
    ∃ lam : ℕ, ¬ 7 ∣ lam ∧ good7 m lam (A1 ∪ A2 ∪ A4) := by
  set j := padicValNat 7 (eMod7 m d2 d3) with hj
  set e13 := eMod7 m d1 d3 with he13d
  set e23 := eMod7 m d2 d3 with he23d
  set e45 := eMod7 m d4 d5 with he45d
  have hν23 : padicValNat 7 e23 = j := rfl
  have hν13 : padicValNat 7 e13 = j := hνeq
  have hν45v : padicValNat 7 e45 < j := hν45
  have hjm : j < m := hνm
  have hjpos : 0 < j := lt_of_le_of_lt (Nat.zero_le _) hν45v
  have hν45m : padicValNat 7 e45 < m := lt_trans hν45v hjm
  have he23 : e23 ≠ 0 := fun h0 => by
    rw [h0, padicValNat.zero] at hν23
    omega
  have he13 : e13 ≠ 0 := fun h0 => by
    rw [h0, padicValNat.zero] at hν13
    omega
  have hr23 : runit7 e23 ≠ 0 := runit7_ne_zero (Nat.pos_of_ne_zero he23)
  obtain ⟨t, ht13, ht23, ht05, ht50⟩ :=
    c63_low_lt_table (qdig7 m e13) (qdig7 m e23)
  -- first stage: `lam1 = 1 + K·7^{m−j}` with `K·r(e23) = t`
  set K : ZMod 7 := t * (runit7 e23)⁻¹ with hK
  set lam1 := 1 + K.val * 7 ^ (m - j) with hlam1
  have hlam1r : runit7 lam1 = 1 := by rw [hlam1]; exact runit7_multLow hjm
  have hlam1nd : ¬ 7 ∣ lam1 := by rw [hlam1]; exact multLow_not_dvd hjm
  have hlam1pos : 0 < lam1 := by rw [hlam1]; exact Nat.add_pos_left Nat.one_pos _
  have hKmul : (K.val : ZMod 7) * runit7 e23 = t := by
    rw [hK, ZMod.natCast_zmod_val, mul_assoc, inv_mul_cancel₀ hr23, mul_one]
  have hKmul3 : (K.val : ZMod 7) * runit7 e13 = 3 * t := by
    rw [hrat]
    have h1 : (K.val : ZMod 7) * (3 * runit7 e23)
        = 3 * ((K.val : ZMod 7) * runit7 e23) := by ring
    rw [h1, hKmul]
  have he13' : eMod7 m (lam1 * d1) (lam1 * d3)
      = (lam1 * e13) % 7 ^ (m + 1) := eMod7_mul hlam1r
  have he23' : eMod7 m (lam1 * d2) (lam1 * d3)
      = (lam1 * e23) % 7 ^ (m + 1) := eMod7_mul hlam1r
  have he45' : eMod7 m (lam1 * d4) (lam1 * d5)
      = (lam1 * e45) % 7 ^ (m + 1) := eMod7_mul hlam1r
  have hq13' : qdig7 m (eMod7 m (lam1 * d1) (lam1 * d3))
      = qdig7 m e13 + 3 * t := by
    rw [he13', qdig7_congr (Nat.mod_mod _ _), hlam1,
      qdig7_multLow hjm hν13, hKmul3]
  have hq23' : qdig7 m (eMod7 m (lam1 * d2) (lam1 * d3))
      = qdig7 m e23 + t := by
    rw [he23', qdig7_congr (Nat.mod_mod _ _), hlam1,
      qdig7_multLow hjm hν23, hKmul]
  -- `e45` survives the `Λ_j`-step verbatim (level `ν45 < j`)
  have hν45' : padicValNat 7 (eMod7 m (lam1 * d4) (lam1 * d5))
      = padicValNat 7 e45 := by
    rw [he45']
    have hνl : padicValNat 7 (lam1 * e45) = padicValNat 7 e45 :=
      padicValNat_mul_seven hlam1nd he45
    have hmod : (lam1 * e45) % 7 ^ (m + 1)
        = ((lam1 * e45) % 7 ^ (m + 1)) % 7 ^ (m + 1) :=
      (Nat.mod_mod _ _).symm
    exact (padicValNat_eq_of_mod hmod
      (by rw [hνl]; exact le_of_lt hν45m)
      (mul_ne_zero (ne_of_gt hlam1pos) he45)).symm.trans hνl
  have he45'ne : eMod7 m (lam1 * d4) (lam1 * d5) ≠ 0 := by
    rw [he45']
    intro h0
    have hdvd : 7 ^ (m + 1) ∣ lam1 * e45 := Nat.dvd_iff_mod_eq_zero.mpr h0
    have hνle : m + 1 ≤ padicValNat 7 (lam1 * e45) :=
      (Nat.pow_dvd_iff_le_padicValNat (by norm_num)
        (mul_ne_zero (ne_of_gt hlam1pos) he45)).mp hdvd
    rw [padicValNat_mul_seven hlam1nd he45] at hνle
    omega
  -- second stage: `lam2 = 1 + k2·7^{m−ν45}` sets `q(e45') = 0`
  set e45' := eMod7 m (lam1 * d4) (lam1 * d5) with he45'd
  obtain ⟨k2, hk2lt, hk2q⟩ := exists_multLow_set_qdig
    (j := padicValNat 7 e45') (x := e45')
    (by rw [hν45']; exact hν45m) rfl he45'ne (0 : ZMod 7)
  set lam2 := 1 + k2 * 7 ^ (m - padicValNat 7 e45') with hlam2
  set lam := lam2 * lam1 with hlam
  have hlam2r : runit7 lam2 = 1 := by
    rw [hlam2]; exact runit7_multLow (by rw [hν45']; exact hν45m)
  have hlam2nd : ¬ 7 ∣ lam2 := by
    rw [hlam2]; exact multLow_not_dvd (by rw [hν45']; exact hν45m)
  have hlamnd : ¬ 7 ∣ lam := Nat.prime_seven.not_dvd_mul hlam2nd hlam1nd
  have hmass : ∀ d : ℕ, lam * d = lam2 * (lam1 * d) := fun d => by
    rw [hlam]; exact mul_assoc _ _ _
  -- `e45''` has digit `0`
  have he45'' : eMod7 m (lam * d4) (lam * d5) = (lam2 * e45') % 7 ^ (m + 1) := by
    rw [hmass d4, hmass d5]
    exact eMod7_mul hlam2r
  have hq45'' : qdig7 m (eMod7 m (lam * d4) (lam * d5)) = 0 := by
    rw [he45'', qdig7_congr (Nat.mod_mod _ _), hlam2]
    exact hk2q
  -- `A1` differences are `lam2`-fixed (levels `j > ν45`)
  have hν13' : padicValNat 7 e45' < padicValNat 7 (eMod7 m (lam1 * d1) (lam1 * d3)) := by
    rw [hν45']
    rw [he13']
    have hνl : padicValNat 7 (lam1 * e13) = j := by
      rw [padicValNat_mul_seven hlam1nd he13]; exact hν13
    have hmod : (lam1 * e13) % 7 ^ (m + 1)
        = ((lam1 * e13) % 7 ^ (m + 1)) % 7 ^ (m + 1) :=
      (Nat.mod_mod _ _).symm
    rw [(padicValNat_eq_of_mod hmod (by rw [hνl]; exact le_of_lt hjm)
      (mul_ne_zero (ne_of_gt hlam1pos) he13)).symm, hνl]
    exact hν45v
  have hν23' : padicValNat 7 e45' < padicValNat 7 (eMod7 m (lam1 * d2) (lam1 * d3)) := by
    rw [hν45']
    rw [he23']
    have hνl : padicValNat 7 (lam1 * e23) = j := by
      rw [padicValNat_mul_seven hlam1nd he23]
    have hmod : (lam1 * e23) % 7 ^ (m + 1)
        = ((lam1 * e23) % 7 ^ (m + 1)) % 7 ^ (m + 1) :=
      (Nat.mod_mod _ _).symm
    rw [(padicValNat_eq_of_mod hmod (by rw [hνl]; exact le_of_lt hjm)
      (mul_ne_zero (ne_of_gt hlam1pos) he23)).symm, hνl]
    exact hν45v
  have he13'' : eMod7 m (lam * d1) (lam * d3)
      = eMod7 m (lam1 * d1) (lam1 * d3) := by
    rw [hmass d1, hmass d3, eMod7_mul hlam2r]
    have hfix : (lam2 * eMod7 m (lam1 * d1) (lam1 * d3)) % 7 ^ (m + 1)
        = eMod7 m (lam1 * d1) (lam1 * d3) % 7 ^ (m + 1) := by
      rw [hlam2]
      exact residN_multLow7 (by rw [hν45']; exact hν45m) hν13'
    rw [hfix, Nat.mod_eq_of_lt (eMod7_lt _ _ _)]
  have he23'' : eMod7 m (lam * d2) (lam * d3)
      = eMod7 m (lam1 * d2) (lam1 * d3) := by
    rw [hmass d2, hmass d3, eMod7_mul hlam2r]
    have hfix : (lam2 * eMod7 m (lam1 * d2) (lam1 * d3)) % 7 ^ (m + 1)
        = eMod7 m (lam1 * d2) (lam1 * d3) % 7 ^ (m + 1) := by
      rw [hlam2]
      exact residN_multLow7 (by rw [hν45']; exact hν45m) hν23'
    rw [hfix, Nat.mod_eq_of_lt (eMod7_lt _ _ _)]
  -- pair digits of the doubled-`lam` `A1` triple
  have hsame13 : residueRelOf (lam * d1) (lam * d3) = residueRel.same :=
    rel_same_of_mul hlamnd (hr1.trans hr3.symm) (ne_of_gt hp3)
  have hsame23 : residueRelOf (lam * d2) (lam * d3) = residueRel.same :=
    rel_same_of_mul hlamnd (hr2.trans hr3.symm) (ne_of_gt hp3)
  have hsub13 := qdig_eMod_sub (m := m) hsame13
  have hsub23 := qdig_eMod_sub (m := m) hsame23
  rw [he13'', hq13'] at hsub13
  rw [he23'', hq23'] at hsub23
  -- `hdiffs`: pairwise diffs of the `A1`-digit image stay in `{0,1,2,5,6}`
  set b13 := qdig7 m (lam * d1) - qdig7 m (lam * d3)
    - (qdig7 m e13 + 3 * t) with hb13
  set b23 := qdig7 m (lam * d2) - qdig7 m (lam * d3)
    - (qdig7 m e23 + t) with hb23
  have hb13m : b13 ∈ ({0, 1} : Finset (ZMod 7)) := by
    have h : b13 = -(qdig7 m e13 + 3 * t
        - (qdig7 m (lam * d1) - qdig7 m (lam * d3))) := by
      rw [hb13]; ring
    rw [h]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hsub13
    rcases hsub13 with h0 | h6
    · rw [h0]; decide
    · rw [h6]; decide
  have hb23m : b23 ∈ ({0, 1} : Finset (ZMod 7)) := by
    have h : b23 = -(qdig7 m e23 + t
        - (qdig7 m (lam * d2) - qdig7 m (lam * d3))) := by
      rw [hb23]; ring
    rw [h]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hsub23
    rcases hsub23 with h0 | h6
    · rw [h0]; decide
    · rw [h6]; decide
  have hdiffs := c63_low_lt_diffs (qdig7 m e13 + 3 * t) (qdig7 m e23 + t)
    b13 b23 ht13 ht23 hb13m hb23m ht05 ht50
  have hlen : apLen (({d1, d2, d3} : Finset ℕ).image
      (fun d => qdig7 m (lam * d))) ≤ 3 := by
    apply remark8_ii'
    intro x hx y hy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
    have key : ∀ a ∈ ({d1, d2, d3} : Finset ℕ),
        qdig7 m (lam * a) - qdig7 m (lam * d3) ∈
          ({0, qdig7 m e23 + t + b23, qdig7 m e13 + 3 * t + b13}
            : Finset (ZMod 7)) := by
      intro a ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha ⊢
      rcases ha with rfl | rfl | rfl
      · right; right
        rw [hb13]; ring
      · right; left
        rw [hb23]; ring
      · left
        exact sub_self _
    have : qdig7 m (lam * a) - qdig7 m (lam * b)
        = (qdig7 m (lam * a) - qdig7 m (lam * d3))
          - (qdig7 m (lam * b) - qdig7 m (lam * d3)) := by ring
    rw [this]
    exact hdiffs _ (key a ha) _ (key b hb)
  -- the `(d4,d5)` pair is good since `q(e45'') = 0`
  have hrel45 : runit7 (lam * d5) = 2 * runit7 (lam * d4) := by
    have h1 : runit7 (lam * d5) = runit7 lam * runit7 d5 := runit7_mul _ _
    have h2 : runit7 (lam * d4) = runit7 lam * runit7 d4 := runit7_mul _ _
    rw [h1, h2, hr4, hr5]
    ring
  have hetd : etd7 m (lam * d4) (lam * d5)
      = 2 * qdig7 m (lam * d4) - qdig7 m (lam * d5) := etd7_eq_twoX hrel45
  have hb45 := qdig_eMod_sub_etd7 (m := m) (x := lam * d4) (y := lam * d5)
  rw [hq45''] at hb45
  have hpair : (2 * qdig7 m (lam * d4) - qdig7 m (lam * d5) : ZMod 7)
      ∉ ({2, 4} : Finset (ZMod 7)) := by
    rw [← hetd]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb45
    rcases hb45 with h0 | h1 | h6
    · have : etd7 m (lam * d4) (lam * d5) = 0 := by
        linear_combination -h0
      rw [this]; decide
    · have : etd7 m (lam * d4) (lam * d5) = -1 := by
        linear_combination -h1
      rw [this]; decide
    · have : etd7 m (lam * d4) (lam * d5) = -6 := by
        linear_combination -h6
      rw [this]; decide
  exact c63_finish3 (by omega) hpos hunit hs0 hcls1 hcls2 hcls4
    hA1eq hA2eq hA4eq hA2 hA4 hne hlamnd hlen hpair

/-- §6.3 (ii.2) low subcase `ν(e45) > h`: normalize `e45` first —
`Λ_{ν45}` (`exists_multLow_set_qdig`) when `ν45 < m`, a `Λ_m` scalar
(`exists_top_scalar_set`) when `ν45 = m` — then apply `c63_l9ii3` (the
`Λ_h` block) to the rescaled `A1`; the `Λ_h` multiplier preserves the
higher-level `e45'` (`residN_multLow7`). -/
private theorem c63_ii2_low_gt {m : ℕ} (hm : 2 ≤ m)
    {A1 A2 A4 : Finset ℕ}
    (hA2 : A2.card = 1) (hA4 : A4.card = 1)
    (hpos : ∀ d ∈ A1 ∪ A2 ∪ A4, 0 < d)
    (hunit : ∀ d ∈ A1 ∪ A2 ∪ A4, padicValNat 7 d = 0)
    {s : ZMod 7} (hs0 : s ≠ 0)
    (hcls1 : ∀ d ∈ A1, runit7 d = s)
    (hcls2 : ∀ d ∈ A2, runit7 d = 2 * s)
    (hcls4 : ∀ d ∈ A4, runit7 d = 4 * s)
    {d1 d2 d3 d4 d5 : ℕ}
    (hA1eq : A1 = {d1, d2, d3}) (hA2eq : A2 = {d4}) (hA4eq : A4 = {d5})
    (hne : A1.Nonempty)
    (hp1 : 0 < d1) (hp2 : 0 < d2) (hp3 : 0 < d3) (hp4 : 0 < d4) (hp5 : 0 < d5)
    (hu1 : padicValNat 7 d1 = 0) (hu2 : padicValNat 7 d2 = 0)
    (hu3 : padicValNat 7 d3 = 0)
    (hr1 : runit7 d1 = s) (hr2 : runit7 d2 = s) (hr3 : runit7 d3 = s)
    (hr4 : runit7 d4 = 2 * s) (hr5 : runit7 d5 = 4 * s)
    (hνeq : padicValNat 7 (eMod7 m d1 d3) = padicValNat 7 (eMod7 m d2 d3))
    (hνm : padicValNat 7 (eMod7 m d2 d3) < m)
    (hrat : runit7 (eMod7 m d1 d3) = 3 * runit7 (eMod7 m d2 d3))
    (he13 : eMod7 m d1 d3 ≠ 0) (he23 : eMod7 m d2 d3 ≠ 0)
    (he45 : eMod7 m d4 d5 ≠ 0)
    (hν45 : padicValNat 7 (eMod7 m d2 d3)
      < padicValNat 7 (eMod7 m d4 d5)) :
    ∃ lam : ℕ, ¬ 7 ∣ lam ∧ good7 m lam (A1 ∪ A2 ∪ A4) := by
  set j := padicValNat 7 (eMod7 m d2 d3) with hj
  set e13 := eMod7 m d1 d3 with he13d
  set e23 := eMod7 m d2 d3 with he23d
  set e45 := eMod7 m d4 d5 with he45d
  have hν23 : padicValNat 7 e23 = j := rfl
  have hν13 : padicValNat 7 e13 = j := hνeq
  have hν45v : j < padicValNat 7 e45 := hν45
  have hjm : j < m := hνm
  have hν45le : padicValNat 7 e45 ≤ m := enu7_le_of_ne he45
  -- stage 1: `lam2` sends `q(e45')` into `{0,6}` while preserving levels
  obtain ⟨lam2, hlam2pos, hlam2nd, hlam2r0, he45'eq, hν45', hq45'⟩ :
      ∃ lam2 : ℕ, 0 < lam2 ∧ ¬ 7 ∣ lam2 ∧ runit7 lam2 ≠ 0 ∧
        eMod7 m (lam2 * d4) (lam2 * d5) = (lam2 * e45) % 7 ^ (m + 1) ∧
        padicValNat 7 (eMod7 m (lam2 * d4) (lam2 * d5))
          = padicValNat 7 e45 ∧
        qdig7 m (eMod7 m (lam2 * d4) (lam2 * d5))
          ∈ ({0, 6} : Finset (ZMod 7)) := by
    rcases lt_or_eq_of_le hν45le with hlt | heq
    · obtain ⟨k2, hk2lt, hk2q⟩ := exists_multLow_set_qdig
        (j := padicValNat 7 e45) (x := e45) hlt rfl he45 (0 : ZMod 7)
      set lam2 := 1 + k2 * 7 ^ (m - padicValNat 7 e45) with hlam2
      have hlam2r : runit7 lam2 = 1 := by rw [hlam2]; exact runit7_multLow hlt
      have hlam2pos : 0 < lam2 := by
        rw [hlam2]; exact Nat.add_pos_left Nat.one_pos _
      refine ⟨lam2, hlam2pos,
        by rw [hlam2]; exact multLow_not_dvd hlt,
        by rw [hlam2r]; exact one_ne_zero, eMod7_mul hlam2r, ?_, ?_⟩
      · have hmod : (lam2 * e45) % 7 ^ (m + 1)
            = ((lam2 * e45) % 7 ^ (m + 1)) % 7 ^ (m + 1) :=
          (Nat.mod_mod _ _).symm
        have hνl : padicValNat 7 (lam2 * e45) = padicValNat 7 e45 :=
          padicValNat_mul_seven (by rw [hlam2]; exact multLow_not_dvd hlt) he45
        rw [eMod7_mul hlam2r]
        exact (padicValNat_eq_of_mod hmod (by rw [hνl]; exact hν45le)
          (mul_ne_zero (ne_of_gt hlam2pos) he45)).symm.trans hνl
      · rw [eMod7_mul hlam2r, qdig7_congr (Nat.mod_mod _ _), hk2q]
        decide
    · obtain ⟨c, hcpos, hc7', hcmod, hqc⟩ :=
        exists_top_scalar_set heq he45 (t := 6) (by decide)
      have hcnd : ¬ 7 ∣ c := fun hd =>
        absurd (Nat.le_of_dvd hcpos hd) (by omega)
      have hrc0 : runit7 c ≠ 0 := runit7_ne_zero hcpos
      refine ⟨c, hcpos, hcnd, hrc0, eMod7_smul hrc0, ?_, ?_⟩
      · have hmod : (c * e45) % 7 ^ (m + 1)
            = ((c * e45) % 7 ^ (m + 1)) % 7 ^ (m + 1) :=
          (Nat.mod_mod _ _).symm
        have hνl : padicValNat 7 (c * e45) = padicValNat 7 e45 :=
          padicValNat_mul_seven hcnd he45
        rw [eMod7_smul hrc0]
        exact (padicValNat_eq_of_mod hmod (by rw [hνl]; exact hν45le)
          (mul_ne_zero (ne_of_gt hcpos) he45)).symm.trans hνl
      · rw [eMod7_smul hrc0, qdig7_congr (Nat.mod_mod _ _), hqc]
        decide
  -- level bookkeeping for the rescaled `A1` differences
  have he13'e : eMod7 m (lam2 * d1) (lam2 * d3)
      = (lam2 * e13) % 7 ^ (m + 1) := eMod7_smul hlam2r0
  have he23'e : eMod7 m (lam2 * d2) (lam2 * d3)
      = (lam2 * e23) % 7 ^ (m + 1) := eMod7_smul hlam2r0
  have hνmod : ∀ x : ℕ, x ≠ 0 → padicValNat 7 x ≤ m →
      padicValNat 7 ((lam2 * x) % 7 ^ (m + 1)) = padicValNat 7 x := by
    intro x hx0 hxm
    have hνl : padicValNat 7 (lam2 * x) = padicValNat 7 x :=
      padicValNat_mul_seven hlam2nd hx0
    have hmod : (lam2 * x) % 7 ^ (m + 1)
        = ((lam2 * x) % 7 ^ (m + 1)) % 7 ^ (m + 1) := (Nat.mod_mod _ _).symm
    exact (padicValNat_eq_of_mod hmod (by rw [hνl]; exact hxm)
      (mul_ne_zero (ne_of_gt hlam2pos) hx0)).symm.trans hνl
  have hrmod : ∀ x : ℕ, x ≠ 0 → padicValNat 7 x ≤ m →
      runit7 ((lam2 * x) % 7 ^ (m + 1)) = runit7 lam2 * runit7 x := by
    intro x hx0 hxm
    have hνl : padicValNat 7 (lam2 * x) = padicValNat 7 x :=
      padicValNat_mul_seven hlam2nd hx0
    have hmod : (lam2 * x) % 7 ^ (m + 1)
        = ((lam2 * x) % 7 ^ (m + 1)) % 7 ^ (m + 1) := (Nat.mod_mod _ _).symm
    rw [← runit7_eq_of_mod hmod (by rw [hνl]; exact hxm)
      (mul_ne_zero (ne_of_gt hlam2pos) hx0), runit7_mul]
  have hν13' : padicValNat 7 (eMod7 m (lam2 * d1) (lam2 * d3)) = j := by
    rw [he13'e,
      hνmod e13 he13 (by rw [hν13]; exact le_of_lt hjm), hν13]
  have hν23' : padicValNat 7 (eMod7 m (lam2 * d2) (lam2 * d3)) = j := by
    rw [he23'e,
      hνmod e23 he23 (by rw [hν23]; exact le_of_lt hjm), hν23]
  have hr13' : runit7 (eMod7 m (lam2 * d1) (lam2 * d3))
      = runit7 lam2 * runit7 e13 := by
    rw [he13'e, hrmod e13 he13 (by rw [hν13]; exact le_of_lt hjm)]
  have hr23' : runit7 (eMod7 m (lam2 * d2) (lam2 * d3))
      = runit7 lam2 * runit7 e23 := by
    rw [he23'e, hrmod e23 he23 (by rw [hν23]; exact le_of_lt hjm)]
  -- `c63_l9ii3` on `b1 = lam2·d2, b2 = lam2·d1, b3 = lam2·d3`
  obtain ⟨lam9, ⟨k9, hk9lt, hlam9eq⟩, hlam9nd, _hqe, _hpairs, hlen9⟩ :=
    c63_l9ii3
      ⟨Nat.mul_pos hlam2pos hp2, Nat.mul_pos hlam2pos hp1,
        Nat.mul_pos hlam2pos hp3⟩
      ⟨by rw [padicValNat_mul_seven hlam2nd (ne_of_gt hp2), hu2],
        by rw [padicValNat_mul_seven hlam2nd (ne_of_gt hp1), hu1],
        by rw [padicValNat_mul_seven hlam2nd (ne_of_gt hp3), hu3]⟩
      ⟨by rw [runit7_mul, runit7_mul, hr2, hr1],
        by rw [runit7_mul, runit7_mul, hr1, hr3]⟩
      (by rw [hν23', hν13']) (by rw [hν13']; exact hjm)
      (by rw [hr13', hr23', hrat]; ring)
  -- `lam9 = 1 + k9·7^{m−j}` preserves `e45'`
  have hlam9r : runit7 lam9 = 1 := by
    rw [hlam9eq]
    exact runit7_multLow (by rw [hν13']; exact hjm)
  set lam := lam9 * lam2 with hlam
  have hlamnd : ¬ 7 ∣ lam := Nat.prime_seven.not_dvd_mul hlam9nd hlam2nd
  have hfix : eMod7 m (lam9 * (lam2 * d4)) (lam9 * (lam2 * d5))
      = eMod7 m (lam2 * d4) (lam2 * d5) := by
    rw [eMod7_mul hlam9r]
    have h1 : (lam9 * eMod7 m (lam2 * d4) (lam2 * d5)) % 7 ^ (m + 1)
        = eMod7 m (lam2 * d4) (lam2 * d5) % 7 ^ (m + 1) := by
      rw [hlam9eq]
      exact residN_multLow7 (by rw [hν13']; exact hjm)
        (by rw [hν45', hν13']; exact hν45v)
    rw [h1, Nat.mod_eq_of_lt (eMod7_lt _ _ _)]
  have hfin : qdig7 m (eMod7 m (lam * d4) (lam * d5))
      ∈ ({0, 6} : Finset (ZMod 7)) := by
    have h1 : eMod7 m (lam * d4) (lam * d5)
        = eMod7 m (lam2 * d4) (lam2 * d5) := by
      rw [hlam, show lam9 * lam2 * d4 = lam9 * (lam2 * d4) from mul_assoc _ _ _,
        show lam9 * lam2 * d5 = lam9 * (lam2 * d5) from mul_assoc _ _ _]
      exact hfix
    rw [h1]; exact hq45'
  -- finish: `apLen` bound transported through `lam2`-image
  have hlen : apLen (({d1, d2, d3} : Finset ℕ).image
      (fun d => qdig7 m (lam * d))) ≤ 3 := by
    have hset : ({lam2 * d2, lam2 * d1, lam2 * d3} : Finset ℕ)
        = ({d1, d2, d3} : Finset ℕ).image (fun d => lam2 * d) := by
      rw [Finset.image_insert, Finset.image_insert, Finset.image_singleton,
        Finset.insert_comm (lam2 * d2) (lam2 * d1)]
    rw [hset, Finset.image_image] at hlen9
    have hcongr : ({d1, d2, d3} : Finset ℕ).image
          (fun d => qdig7 m (lam9 * (lam2 * d)))
        = ({d1, d2, d3} : Finset ℕ).image
          (fun d => qdig7 m (lam * d)) :=
      Finset.image_congr fun d _ => by
        rw [hlam]
        exact congrArg _ (mul_assoc _ _ _).symm
    rwa [← hcongr]
  have hrel45 : runit7 (lam * d5) = 2 * runit7 (lam * d4) := by
    have h1 : runit7 (lam * d5) = runit7 lam * runit7 d5 := runit7_mul _ _
    have h2 : runit7 (lam * d4) = runit7 lam * runit7 d4 := runit7_mul _ _
    rw [h1, h2, hr4, hr5]
    ring
  have hetd : etd7 m (lam * d4) (lam * d5)
      = 2 * qdig7 m (lam * d4) - qdig7 m (lam * d5) := etd7_eq_twoX hrel45
  have hb45 := qdig_eMod_sub_etd7 (m := m) (x := lam * d4) (y := lam * d5)
  have hpair : (2 * qdig7 m (lam * d4) - qdig7 m (lam * d5) : ZMod 7)
      ∉ ({2, 4} : Finset (ZMod 7)) := by
    rw [← hetd]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hfin hb45
    rcases hfin with hq | hq <;> rw [hq] at hb45 <;>
      rcases hb45 with h | h | h
    · have hv : etd7 m (lam * d4) (lam * d5) = 0 := by linear_combination -h
      rw [hv]; decide
    · have hv : etd7 m (lam * d4) (lam * d5) = -1 := by linear_combination -h
      rw [hv]; decide
    · have hv : etd7 m (lam * d4) (lam * d5) = -6 := by linear_combination -h
      rw [hv]; decide
    · have hv : etd7 m (lam * d4) (lam * d5) = 6 := by linear_combination -h
      rw [hv]; decide
    · have hv : etd7 m (lam * d4) (lam * d5) = 5 := by linear_combination -h
      rw [hv]; decide
    · have hv : etd7 m (lam * d4) (lam * d5) = 0 := by linear_combination -h
      rw [hv]; decide
  exact c63_finish3 (by omega) hpos hunit hs0 hcls1 hcls2 hcls4
    hA1eq hA2eq hA4eq hA2 hA4 hne hlamnd hlen hpair

/-! ### §6.3 ii.2-low equal-level rescue (paper `ii.2.b`)

When `ν(e₄₅) = ν(e₁₃) = ν(e₂₃) = j < m` the paper relabels `A₁` so that
`r(e₄₅) = ±r(e₁₃)`, sets `f := e₁₃ ∓ e₄₅` (level `> j` or `0`), normalizes
`f` by `Λ_{ν(f)}` (or a top scalar when `ν(f) = m`), then applies a
`Λ_j`-shift chosen by the finite `case63_table`; the exceptional cell
`(ẽ,ũ) = (0,3)` is finished by doubling.  We implement `f` uniformly as
`(e₁₃ + N − g) % N` where `g := e₄₅` (resp. `N − e₄₅`) is the `e₄₅`-residue
with `r(g) = r(e₁₃)`.  The relabeling needed for `r(e₄₅) = ±r(e₁₃)` is
*not* the Lemma-11 `±s` alternative: with `r(e₁₃) = 3u`,
`u := r(e₂₃)`, the three cyclic orders of `A₁` produce `r(e₁₃)`-units
`3u, 5u, 6u`, and `{3u,4u,5u,2u,6u,1u}` covers every `r(e₄₅)`, so one of
the three orders always lands `r(e₄₅) ∈ {±r(e₁₃)}`. -/

/-- `(a + c − b) % P` depends only on `a % P`, `b % P` when `P ∣ c` (and the
subtraction does not truncate).  (Port of `wrap_sub_mod_gen`.) -/
private theorem c63_wrap_sub_mod_gen {a b c P : ℕ} (hP : 0 < P) (hc : P ∣ c)
    (hle : b ≤ a + c) :
    (a + c - b) % P = (a % P + P - b % P) % P := by
  obtain ⟨k, rfl⟩ := hc
  have hlt1 : b ≤ a + P * k := hle
  have hlt2 : b % P ≤ a % P + P := by
    have := Nat.mod_lt b hP
    omega
  have hcast : ((a + P * k - b : ℕ) : ZMod P)
      = ((a % P + P - b % P : ℕ) : ZMod P) := by
    rw [Nat.cast_sub hlt1, Nat.cast_sub hlt2]
    push_cast
    rw [ZMod.natCast_self, ZMod.natCast_mod, ZMod.natCast_mod]
    ring
  exact (ZMod.natCast_eq_natCast_iff' _ _ _).mp hcast

/-- Difference of two level-`h` naturals reads `(r(u)−r(v))·7^h` mod
`7^{h+1}` (wrapped subtraction inside the modulus).  (Port of
`sub_mod_block`.) -/
private theorem c63_sub_mod_block {u v h : ℕ} (hu : u ≠ 0) (hv : v ≠ 0)
    (huν : padicValNat 7 u = h) (hvν : padicValNat 7 v = h) :
    (u % 7 ^ (h + 1) + 7 ^ (h + 1) - v % 7 ^ (h + 1)) % 7 ^ (h + 1)
      = (runit7 u - runit7 v).val * 7 ^ h := by
  have hub := c63_nat_mod_pow_succ hu huν
  have hvb := c63_nat_mod_pow_succ hv hvν
  have hru7 : (runit7 u).val < 7 := ZMod.val_lt _
  have hrv7 : (runit7 v).val < 7 := ZMod.val_lt _
  have hvv : (runit7 u - runit7 v).val
      = ((runit7 u).val + 7 - (runit7 v).val) % 7 := by
    have hcast : (runit7 u - runit7 v : ZMod 7)
        = (((runit7 u).val + 7 - (runit7 v).val : ℕ) : ZMod 7) := by
      rw [Nat.cast_sub (by omega : (runit7 v).val ≤ (runit7 u).val + 7)]
      push_cast
      rw [show (7 : ZMod 7) = 0 from by decide, add_zero,
        ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    rw [hcast, ZMod.val_natCast]
  rw [hub, hvb]
  have hsub : (runit7 u).val * 7 ^ h + 7 ^ (h + 1) - (runit7 v).val * 7 ^ h
      = ((runit7 u).val + 7 - (runit7 v).val) * 7 ^ h := by
    rw [pow_succ', Nat.sub_mul, Nat.add_mul]
  rw [hsub, pow_succ', Nat.mul_mod_mul_right, hvv]

/-- Reversal of a `same`-pair residue: `e(y,x) = (N − e(x,y)) % N`. -/
private theorem c63_eMod7_rev {m x y : ℕ}
    (hxy : residueRelOf x y = residueRel.same)
    (hyx : residueRelOf y x = residueRel.same) :
    eMod7 m y x = (7 ^ (m + 1) - eMod7 m x y) % 7 ^ (m + 1) := by
  have hlt : eMod7 m y x < 7 ^ (m + 1) := eMod7_lt _ _ _
  have hcast : ((eMod7 m y x : ℕ) : ZMod (7 ^ (m + 1)))
      = ((7 ^ (m + 1) - eMod7 m x y : ℕ) : ZMod _) := by
    rw [eMod7_zmod_cast_same hyx]
    have hle : eMod7 m x y ≤ 7 ^ (m + 1) := le_of_lt (eMod7_lt _ _ _)
    rw [Nat.cast_sub hle, ZMod.natCast_self, zero_sub,
      eMod7_zmod_cast_same hxy]
    ring
  rw [ZMod.natCast_eq_natCast_iff'] at hcast
  rwa [Nat.mod_eq_of_lt hlt] at hcast

/-- Level/runit of the reversed `same`-pair residue. -/
private theorem c63_rev_level {m x y : ℕ}
    (hxy : residueRelOf x y = residueRel.same)
    (hyx : residueRelOf y x = residueRel.same)
    (he : eMod7 m x y ≠ 0) (hν : padicValNat 7 (eMod7 m x y) ≤ m) :
    eMod7 m y x ≠ 0 ∧ padicValNat 7 (eMod7 m y x)
      = padicValNat 7 (eMod7 m x y)
      ∧ runit7 (eMod7 m y x) = - runit7 (eMod7 m x y) := by
  have hlt : eMod7 m x y < 7 ^ (m + 1) := eMod7_lt _ _ _
  have hpos : 0 < eMod7 m x y := Nat.pos_of_ne_zero he
  have hN : 0 < 7 ^ (m + 1) := Nat.pow_pos (by norm_num)
  have hlt2 : 7 ^ (m + 1) - eMod7 m x y < 7 ^ (m + 1) := by omega
  have hmod : (7 ^ (m + 1) - eMod7 m x y) % 7 ^ (m + 1)
      = 7 ^ (m + 1) - eMod7 m x y := Nat.mod_eq_of_lt hlt2
  rw [c63_eMod7_rev hxy hyx, hmod]
  obtain ⟨hν', hr'⟩ := c63_neg_resid_level he hlt hν
  exact ⟨by omega, hν', hr'⟩

/-- `e(x,y)`-block from two same-level residues through a common `l`
(the `eMod7_sub_block` port). -/
private theorem c63_eMod7_sub_block {m x y l h : ℕ}
    (hxl : residueRelOf x l = residueRel.same)
    (hyl : residueRelOf y l = residueRel.same)
    (hxy : residueRelOf x y = residueRel.same)
    (hxl0 : eMod7 m x l ≠ 0) (hyl0 : eMod7 m y l ≠ 0)
    (hxlν : padicValNat 7 (eMod7 m x l) = h)
    (hylν : padicValNat 7 (eMod7 m y l) = h) (hm : h ≤ m) :
    eMod7 m x y % 7 ^ (h + 1)
      = (runit7 (eMod7 m x l) - runit7 (eMod7 m y l)).val * 7 ^ h := by
  rw [eMod7_sub_eq hxl hyl hxy]
  rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 7 (by omega : h + 1 ≤ m + 1))]
  rw [c63_wrap_sub_mod_gen (Nat.pow_pos (by norm_num))
    (Nat.pow_dvd_pow 7 (by omega : h + 1 ≤ m + 1))
    (by have := eMod7_lt m y l; omega)]
  exact c63_sub_mod_block hxl0 hyl0 hxlν hylν

/-- Distinct `r`'s through a common point give `e(x,y)` level `h` and
unit `r(e_{xl}) − r(e_{yl})` (the `eMod7_level_of_runit_ne` port). -/
private theorem c63_eMod7_level_of_runit_ne {m x y l h : ℕ}
    (hxl : residueRelOf x l = residueRel.same)
    (hyl : residueRelOf y l = residueRel.same)
    (hxy : residueRelOf x y = residueRel.same)
    (hxl0 : eMod7 m x l ≠ 0) (hyl0 : eMod7 m y l ≠ 0)
    (hxlν : padicValNat 7 (eMod7 m x l) = h)
    (hylν : padicValNat 7 (eMod7 m y l) = h) (hm : h ≤ m)
    (hr : runit7 (eMod7 m x l) ≠ runit7 (eMod7 m y l)) :
    eMod7 m x y ≠ 0 ∧ padicValNat 7 (eMod7 m x y) = h ∧
      runit7 (eMod7 m x y)
        = runit7 (eMod7 m x l) - runit7 (eMod7 m y l) := by
  have hblk := c63_eMod7_sub_block hxl hyl hxy hxl0 hyl0 hxlν hylν hm
  have hs : 0 < (runit7 (eMod7 m x l) - runit7 (eMod7 m y l)).val := by
    have h' : runit7 (eMod7 m x l) - runit7 (eMod7 m y l) ≠ 0 :=
      sub_ne_zero.mpr hr
    have : (runit7 (eMod7 m x l) - runit7 (eMod7 m y l)).val ≠ 0 := by
      intro h0
      exact h' ((ZMod.val_eq_zero _).mp h0)
    omega
  have hs7 : (runit7 (eMod7 m x l) - runit7 (eMod7 m y l)).val < 7 :=
    ZMod.val_lt _
  obtain ⟨hw0, hνw, hrw⟩ := c63_level_of_mod_block hblk hs hs7
  exact ⟨hw0, hνw, by rw [hrw, ZMod.natCast_zmod_val]⟩

/-- For `r(a) = r(b)` at common level `j ≤ m` (`b < N`), the wrapped
difference `f := (a + N − b) % N` is `0` or has level in `(j, m]`. -/
private theorem c63_f_level_gt {m j a b : ℕ} (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (hνa : padicValNat 7 a = j) (hνb : padicValNat 7 b = j) (hjm : j ≤ m)
    (hbN : b < 7 ^ (m + 1)) (hr : runit7 a = runit7 b) :
    (a + 7 ^ (m + 1) - b) % 7 ^ (m + 1) = 0 ∨
      (j < padicValNat 7 ((a + 7 ^ (m + 1) - b) % 7 ^ (m + 1)) ∧
        padicValNat 7 ((a + 7 ^ (m + 1) - b) % 7 ^ (m + 1)) ≤ m) := by
  set f := (a + 7 ^ (m + 1) - b) % 7 ^ (m + 1) with hfd
  have hmod : f % 7 ^ (j + 1) = 0 := by
    have h1 : f % 7 ^ (j + 1)
        = (a + 7 ^ (m + 1) - b) % 7 ^ (j + 1) := by
      rw [hfd, Nat.mod_mod_of_dvd _
        (Nat.pow_dvd_pow 7 (by omega : j + 1 ≤ m + 1))]
    rw [h1, c63_wrap_sub_mod_gen (Nat.pow_pos (by norm_num))
      (Nat.pow_dvd_pow 7 (by omega : j + 1 ≤ m + 1))
      (by have := hbN; omega)]
    rw [c63_sub_mod_block ha0 hb0 hνa hνb, hr, sub_self, ZMod.val_zero,
      zero_mul]
  rcases eq_or_ne f 0 with h0 | h0
  · exact Or.inl h0
  · right
    have hdvd : 7 ^ (j + 1) ∣ f := Nat.dvd_iff_mod_eq_zero.mpr hmod
    have hgt : j < padicValNat 7 f := by
      have := (Nat.pow_dvd_iff_le_padicValNat (by norm_num) h0).mp hdvd
      omega
    refine ⟨hgt, ?_⟩
    have hlt : f < 7 ^ (m + 1) := Nat.mod_lt _ (Nat.pow_pos (by norm_num))
    by_contra hc
    push_neg at hc
    have hdvd2 : 7 ^ (m + 1) ∣ f :=
      (Nat.pow_dvd_iff_le_padicValNat (by norm_num) h0).mpr (by omega)
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero h0) hdvd2
    omega

/-- Small finite checks used by the equal-level doubling rescue: the
doubled residue digits land in `{0,6}` (`2·3 + c`), so each element-digit
difference `q(e''') − b` lies in `{0,6} − {0,6} = {0,1,6}`, the
`{0,1,6}`-valued three-point sets sit in `cycIv 6 3 = {6,0,1}` hence have
`apLen ≤ 3`, and `{0,6} − {0,1,6} = {0,1,5,6}` avoids the bad pair
`{2,4}`. -/
private theorem c63_eq_dec :
    (∀ a ∈ ({0, 6} : Finset (ZMod 7)), ∀ b ∈ ({0, 6} : Finset (ZMod 7)),
      a - b ∈ ({0, 1, 6} : Finset (ZMod 7))) ∧
    (∀ x ∈ ({0, 1, 6} : Finset (ZMod 7)), ∀ y ∈ ({0, 1, 6} : Finset (ZMod 7)),
      apLen ({0, x, y} : Finset (ZMod 7)) ≤ 3) ∧
    (∀ a ∈ ({0, 6} : Finset (ZMod 7)), ∀ b ∈ ({0, 1, 6} : Finset (ZMod 7)),
      a - b ∉ ({2, 4} : Finset (ZMod 7))) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- Doubling rescue for the exceptional `(ẽ,ũ) = (0,3)` cell of
`case63_table` (paper `ii.2.b` endgame): if the leading digits of the
`(1,3)`- and `(2,3)`-difference residues are both `3`, then the doubled
multiplier `2·lam` puts both in `{0,6}`, the borrows add `{0,1}`, so
the doubled `A₁`-digit set is a translate of a subset of `{0,1,6}` —
`apLen ≤ 2` — and `c63_finish2` finishes. -/
private theorem c63_eq_double {m : ℕ} (hm : 2 ≤ m) {A1 A2 A4 : Finset ℕ}
    (hA2 : A2.card = 1) (hA4 : A4.card = 1)
    (hpos : ∀ d ∈ A1 ∪ A2 ∪ A4, 0 < d)
    (hunit : ∀ d ∈ A1 ∪ A2 ∪ A4, padicValNat 7 d = 0)
    {s : ZMod 7} (hs0 : s ≠ 0)
    (hcls1 : ∀ d ∈ A1, runit7 d = s)
    (hcls2 : ∀ d ∈ A2, runit7 d = 2 * s)
    (hcls4 : ∀ d ∈ A4, runit7 d = 4 * s)
    {d1 d2 d3 d4 d5 lam : ℕ} (hA1eq : A1 = {d1, d2, d3})
    (hA2eq : A2 = {d4}) (hA4eq : A4 = {d5})
    (hne : A1.Nonempty) (hp3 : 0 < d3)
    (hr1 : runit7 d1 = s) (hr2 : runit7 d2 = s) (hr3 : runit7 d3 = s)
    (hr4 : runit7 d4 = 2 * s) (hr5 : runit7 d5 = 4 * s)
    (hlam : ¬ 7 ∣ lam)
    (hq13 : qdig7 m (eMod7 m (lam * d1) (lam * d3)) = 3)
    (hq23 : qdig7 m (eMod7 m (lam * d2) (lam * d3)) = 3)
    (hq45 : qdig7 m (eMod7 m (lam * d4) (lam * d5)) = 3) :
    ∃ l : ℕ, ¬ 7 ∣ l ∧ good7 m l (A1 ∪ A2 ∪ A4) := by
  set lam2 := 2 * lam with hlam2d
  have h2nd : ¬ 7 ∣ (2 : ℕ) := by norm_num
  have hlam2nd : ¬ 7 ∣ lam2 := by
    rw [hlam2d]
    rintro h
    rcases (Nat.prime_seven.dvd_mul).mp h with h | h
    · exact h2nd h
    · exact hlam h
  have h2r : runit7 (2 : ℕ) ≠ 0 := by
    unfold runit7
    rw [padicValNat.eq_zero_of_not_dvd h2nd, pow_zero, Nat.div_one]
    decide
  obtain ⟨hsum, hdec, hpairdec⟩ := c63_eq_dec
  -- doubled residues `e(2λx, 2λy) = (2·e) % N` and their digits `∈ {0,6}`
  have hdig : ∀ x y : ℕ,
      qdig7 m (eMod7 m (lam * x) (lam * y)) = 3 →
      qdig7 m (eMod7 m (lam2 * x) (lam2 * y))
        ∈ ({0, 6} : Finset (ZMod 7)) := by
    intro x y hq
    have he : eMod7 m (lam2 * x) (lam2 * y)
        = (2 * eMod7 m (lam * x) (lam * y)) % 7 ^ (m + 1) := by
      rw [hlam2d, show 2 * lam * x = 2 * (lam * x) from by ring,
        show 2 * lam * y = 2 * (lam * y) from by ring]
      exact eMod7_smul h2r
    rw [he, qdig7_congr (Nat.mod_mod _ _)]
    have hc := qdig7_smul_carry_mem (m := m) (c := 2)
      (x := eMod7 m (lam * x) (lam * y)) (by norm_num) (by norm_num)
    have hS : (Finset.range 2).image (fun n : ℕ => (n : ZMod 7))
        = ({0, 1} : Finset (ZMod 7)) := by decide
    rw [hS, hq] at hc
    -- `q(2e) = 2·3 + c` with `c ∈ {0,1}` lands in `{0,6}`
    have h2c : ∀ c ∈ ({0, 1} : Finset (ZMod 7)),
        ((2 : ℕ) : ZMod 7) * 3 + c ∈ ({0, 6} : Finset (ZMod 7)) := by
      decide
    have hv : qdig7 m (2 * eMod7 m (lam * x) (lam * y))
        = ((2 : ℕ) : ZMod 7) * 3
          + (qdig7 m (2 * eMod7 m (lam * x) (lam * y))
            - ((2 : ℕ) : ZMod 7) * 3) := by
      ring
    rw [hv]
    exact h2c _ hc
  have hrel13 : residueRelOf (lam2 * d1) (lam2 * d3) = residueRel.same :=
    rel_same_of_mul hlam2nd (by rw [hr1, hr3]) (ne_of_gt hp3)
  have hrel23 : residueRelOf (lam2 * d2) (lam2 * d3) = residueRel.same :=
    rel_same_of_mul hlam2nd (by rw [hr2, hr3]) (ne_of_gt hp3)
  have hb13 := qdig_eMod_sub (m := m) hrel13
  have hb23 := qdig_eMod_sub (m := m) hrel23
  have hq13d := hdig d1 d3 hq13
  have hq23d := hdig d2 d3 hq23
  have hq45d := hdig d4 d5 hq45
  have hs1 : qdig7 m (lam2 * d1) - qdig7 m (lam2 * d3)
      ∈ ({0, 1, 6} : Finset (ZMod 7)) := by
    have hv : qdig7 m (lam2 * d1) - qdig7 m (lam2 * d3)
        = qdig7 m (eMod7 m (lam2 * d1) (lam2 * d3))
          - (qdig7 m (eMod7 m (lam2 * d1) (lam2 * d3))
            - (qdig7 m (lam2 * d1) - qdig7 m (lam2 * d3))) := by
      ring
    rw [hv]
    exact hsum _ hq13d _ hb13
  have hs2 : qdig7 m (lam2 * d2) - qdig7 m (lam2 * d3)
      ∈ ({0, 1, 6} : Finset (ZMod 7)) := by
    have hv : qdig7 m (lam2 * d2) - qdig7 m (lam2 * d3)
        = qdig7 m (eMod7 m (lam2 * d2) (lam2 * d3))
          - (qdig7 m (eMod7 m (lam2 * d2) (lam2 * d3))
            - (qdig7 m (lam2 * d2) - qdig7 m (lam2 * d3))) := by
      ring
    rw [hv]
    exact hsum _ hq23d _ hb23
  have himg : ({d1, d2, d3} : Finset ℕ).image (fun d => qdig7 m (lam2 * d))
      = {qdig7 m (lam2 * d1), qdig7 m (lam2 * d2), qdig7 m (lam2 * d3)} := by
    rw [Finset.image_insert, Finset.image_insert, Finset.image_singleton]
  have htr : ({qdig7 m (lam2 * d1), qdig7 m (lam2 * d2), qdig7 m (lam2 * d3)}
        : Finset (ZMod 7))
      = ({0, qdig7 m (lam2 * d1) - qdig7 m (lam2 * d3),
          qdig7 m (lam2 * d2) - qdig7 m (lam2 * d3)} : Finset (ZMod 7)).image
        (· + qdig7 m (lam2 * d3)) := by
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_image]
    constructor
    · rintro (rfl | rfl | rfl)
      · exact ⟨_, Or.inr (Or.inl rfl), by ring⟩
      · exact ⟨_, Or.inr (Or.inr rfl), by ring⟩
      · exact ⟨0, Or.inl rfl, by ring⟩
    · rintro ⟨w, hw, rfl⟩
      rcases hw with rfl | rfl | rfl
      · exact Or.inr (Or.inr (by ring))
      · exact Or.inl (by ring)
      · exact Or.inr (Or.inl (by ring))
  have hlen : apLen (({d1, d2, d3} : Finset ℕ).image
      (fun d => qdig7 m (lam2 * d))) ≤ 3 := by
    rw [himg, htr, apLen_image_add]
    exact hdec _ hs1 _ hs2
  -- the pair is safe: `ẽ(2λd₄,2λd₅) = q(e₄₅''') − b ∈ {0,6}−{0,1,6}`
  have hrel45 : runit7 (lam2 * d5) = 2 * runit7 (lam2 * d4) := by
    rw [runit7_mul, runit7_mul, runit7_mul, runit7_mul, hr4, hr5]
    ring
  have hetd : etd7 m (lam2 * d4) (lam2 * d5)
      = 2 * qdig7 m (lam2 * d4) - qdig7 m (lam2 * d5) :=
    etd7_eq_twoX hrel45
  have hb45 := qdig_eMod_sub_etd7 (m := m) (x := lam2 * d4) (y := lam2 * d5)
  have hpair : (2 * qdig7 m (lam2 * d4) - qdig7 m (lam2 * d5) : ZMod 7)
      ∉ ({2, 4} : Finset (ZMod 7)) := by
    rw [← hetd]
    have hv : etd7 m (lam2 * d4) (lam2 * d5)
        = qdig7 m (eMod7 m (lam2 * d4) (lam2 * d5))
          - (qdig7 m (eMod7 m (lam2 * d4) (lam2 * d5))
            - etd7 m (lam2 * d4) (lam2 * d5)) := by
      ring
    rw [hv]
    exact hpairdec _ hq45d _ hb45
  exact c63_finish3 (by omega) hpos hunit hs0 hcls1 hcls2 hcls4
    hA1eq hA2eq hA4eq hA2 hA4 hne hlam2nd hlen hpair

/-- Equal-level rescue, step 2: given `lam1` whose scaled residues sit at
level `j` with `r(e₁₃') = 3r(e₂₃')`, an auxiliary residue `g` at level
`j` with `r(g') = r(e₁₃')` and the normalized invariant
`q(e₁₃') − q(g') ∈ {0,1}` (the paper's `ẽ`), plus the `e₄₅ ↔ g`
conversion `e₄₅'' ≡ σ·g'' (mod N)` (`σ = ±1`), a `Λ_j`-shift `lam2`
moves `q(g')` to the `case63_table` target `T`; `lam2·lam1` then
finishes via `c63_finish2`, `c63_finish3`, or the `(0,3)`-doubling
(`c63_eq_double`). -/
private theorem c63_eq_step2 {m : ℕ} (hm : 2 ≤ m) {A1 A2 A4 : Finset ℕ}
    (hA2 : A2.card = 1) (hA4 : A4.card = 1)
    (hpos : ∀ d ∈ A1 ∪ A2 ∪ A4, 0 < d)
    (hunit : ∀ d ∈ A1 ∪ A2 ∪ A4, padicValNat 7 d = 0)
    {s : ZMod 7} (hs0 : s ≠ 0)
    (hcls1 : ∀ d ∈ A1, runit7 d = s)
    (hcls2 : ∀ d ∈ A2, runit7 d = 2 * s)
    (hcls4 : ∀ d ∈ A4, runit7 d = 4 * s)
    {d1 d2 d3 d4 d5 lam1 g : ℕ} {j : ℕ}
    (hA1eq : A1 = {d1, d2, d3}) (hA2eq : A2 = {d4}) (hA4eq : A4 = {d5})
    (hne : A1.Nonempty)
    (hp2 : 0 < d2) (hp3 : 0 < d3)
    (hr1 : runit7 d1 = s) (hr2 : runit7 d2 = s) (hr3 : runit7 d3 = s)
    (hr4 : runit7 d4 = 2 * s) (hr5 : runit7 d5 = 4 * s)
    (hjm : j < m)
    (hlam1pos : 0 < lam1) (hlam1nd : ¬ 7 ∣ lam1) (hlam1r : runit7 lam1 ≠ 0)
    (hg0 : g ≠ 0) (hgN : g < 7 ^ (m + 1))
    (hν13' : padicValNat 7 (eMod7 m (lam1 * d1) (lam1 * d3)) = j)
    (hν23' : padicValNat 7 (eMod7 m (lam1 * d2) (lam1 * d3)) = j)
    (he13' : eMod7 m (lam1 * d1) (lam1 * d3) ≠ 0)
    (he23' : eMod7 m (lam1 * d2) (lam1 * d3) ≠ 0)
    (hrat' : runit7 (eMod7 m (lam1 * d1) (lam1 * d3))
      = 3 * runit7 (eMod7 m (lam1 * d2) (lam1 * d3)))
    (hg'0 : (lam1 * g) % 7 ^ (m + 1) ≠ 0)
    (hνg' : padicValNat 7 ((lam1 * g) % 7 ^ (m + 1)) = j)
    (hrg' : runit7 ((lam1 * g) % 7 ^ (m + 1))
      = runit7 (eMod7 m (lam1 * d1) (lam1 * d3)))
    (hed : qdig7 m (eMod7 m (lam1 * d1) (lam1 * d3))
        - qdig7 m ((lam1 * g) % 7 ^ (m + 1)) ∈ ({0, 1} : Finset (ZMod 7)))
    {σ : ZMod 7} (hσ : σ = 1 ∨ σ = -1)
    (hgrel : ∀ lam : ℕ, runit7 lam ≠ 0 →
      ((eMod7 m (lam * d4) (lam * d5) : ℕ) : ZMod (7 ^ (m + 1)))
        = (if σ = 1 then (1 : ZMod (7 ^ (m + 1))) else -1)
          * (((lam * g) % 7 ^ (m + 1) : ℕ) : ZMod _)) :
    ∃ lam : ℕ, ¬ 7 ∣ lam ∧ good7 m lam (A1 ∪ A2 ∪ A4) := by
  set e13' := eMod7 m (lam1 * d1) (lam1 * d3) with he13'd
  set e23' := eMod7 m (lam1 * d2) (lam1 * d3) with he23'd
  set g' := (lam1 * g) % 7 ^ (m + 1) with hg'd
  set edig := qdig7 m e13' - qdig7 m g' with hedd
  set udig := 3 * qdig7 m e13' + 5 * qdig7 m e23' with hudd
  set δ := (if e13' % 7 ^ m < e23' % 7 ^ m then (1 : ZMod 7) else 0)
    with hδd
  have hδ : δ ∈ ({0, 1} : Finset (ZMod 7)) := by
    rw [hδd]; split_ifs <;> simp
  have h7z : (7 : ZMod 7) = 0 := by decide
  have hrg'0 : runit7 g' ≠ 0 := runit7_ne_zero (Nat.pos_of_ne_zero hg'0)
  -- choose `T`: the `(0,3)`-cell takes `T = 3`, everything else uses
  -- `case63_table`
  obtain ⟨T, hTexc, hT⟩ : ∃ T : ZMod 7,
      ((edig = 0 ∧ udig = 3) → T = 3) ∧
      (¬ (edig = 0 ∧ udig = 3) →
        ∀ b12 ∈ ({0, 1} : Finset (ZMod 7)),
        ∀ b13 ∈ ({0, 1} : Finset (ZMod 7)),
        ∀ b23 ∈ ({0, 1} : Finset (ZMod 7)),
        b13 = b12 + b23 - δ →
        apLen ({0, T + edig + b13, 3 * (udig - 3 * (T + edig)) + b23}
            : Finset (ZMod 7)) ≤ 2 ∨
        (apLen ({0, T + edig + b13, 3 * (udig - 3 * (T + edig)) + b23}
            : Finset (ZMod 7)) ≤ 3 ∧ T ∈ ({0, 6} : Finset (ZMod 7)))) := by
    by_cases hcell : edig = 0 ∧ udig = 3
    · exact ⟨3, fun _ => rfl, fun hn => absurd hcell hn⟩
    · obtain ⟨T, hT⟩ := case63_table hed hcell hδ
      exact ⟨T, fun h => absurd h hcell, fun _ => hT⟩
  set K : ZMod 7 := (T - qdig7 m g') * (runit7 g')⁻¹ with hKd
  set lam2 := 1 + K.val * 7 ^ (m - j) with hlam2d
  have hlam2r : runit7 lam2 = 1 := by rw [hlam2d]; exact runit7_multLow hjm
  have hlam2nd : ¬ 7 ∣ lam2 := by rw [hlam2d]; exact multLow_not_dvd hjm
  have hKmul : (K.val : ZMod 7) * runit7 g' = T - qdig7 m g' := by
    rw [hKd, ZMod.natCast_zmod_val, mul_assoc, inv_mul_cancel₀ hrg'0,
      mul_one]
  set lam := lam2 * lam1 with hlamd
  have hlampos : 0 < lam := Nat.mul_pos
    (Nat.pos_of_ne_zero (fun h => hlam2nd (h ▸ dvd_zero _))) hlam1pos
  have hlamnd : ¬ 7 ∣ lam := by
    rw [hlamd]
    rintro h
    rcases (Nat.prime_seven.dvd_mul).mp h with h | h
    · exact hlam2nd h
    · exact hlam1nd h
  have hlamr : runit7 lam ≠ 0 := by
    rw [hlamd, runit7_mul, hlam2r, one_mul]
    exact hlam1r
  have h2r0 : runit7 lam2 ≠ 0 := by rw [hlam2r]; exact one_ne_zero
  -- double-primed residues `eᵢⱼ'' = (lam2 * eᵢⱼ') % N`
  have he13'' : eMod7 m (lam * d1) (lam * d3)
      = (lam2 * e13') % 7 ^ (m + 1) := by
    rw [hlamd, show lam2 * lam1 * d1 = lam2 * (lam1 * d1) from by ring,
      show lam2 * lam1 * d3 = lam2 * (lam1 * d3) from by ring]
    exact eMod7_smul h2r0
  have he23'' : eMod7 m (lam * d2) (lam * d3)
      = (lam2 * e23') % 7 ^ (m + 1) := by
    rw [hlamd, show lam2 * lam1 * d2 = lam2 * (lam1 * d2) from by ring,
      show lam2 * lam1 * d3 = lam2 * (lam1 * d3) from by ring]
    exact eMod7_smul h2r0
  have he12'' : eMod7 m (lam * d1) (lam * d2)
      = (lam2 * eMod7 m (lam1 * d1) (lam1 * d2)) % 7 ^ (m + 1) := by
    rw [hlamd, show lam2 * lam1 * d1 = lam2 * (lam1 * d1) from by ring,
      show lam2 * lam1 * d2 = lam2 * (lam1 * d2) from by ring]
    exact eMod7_smul h2r0
  -- `g'' := (lam·g) % N = (lam2·g') % N` and `q(g'') = T`
  have hg''eq : (lam * g) % 7 ^ (m + 1) = (lam2 * g') % 7 ^ (m + 1) := by
    have hme : lam2 * (lam1 * g) ≡ lam2 * g' [MOD 7 ^ (m + 1)] := by
      have h1 : lam1 * g ≡ g' [MOD 7 ^ (m + 1)] := by
        show (lam1 * g) % 7 ^ (m + 1) = g' % 7 ^ (m + 1)
        rw [hg'd, Nat.mod_mod]
      exact h1.mul_left lam2
    rw [hlamd, mul_assoc]
    exact hme
  have hg''0 : (lam * g) % 7 ^ (m + 1) ≠ 0 := by
    rw [hg''eq]
    exact c63_res_ne_of_level
      (mul_ne_zero (fun h => hlam2nd (h ▸ dvd_zero _)) hg'0)
      (by rw [padicValNat_mul_seven hlam2nd hg'0, hνg']; omega)
  have hνg'' : padicValNat 7 ((lam * g) % 7 ^ (m + 1)) = j := by
    have h1 : padicValNat 7 (lam2 * g') = j := by
      rw [padicValNat_mul_seven hlam2nd hg'0, hνg']
    have hmod : (lam2 * g') % 7 ^ (m + 1)
        = ((lam * g) % 7 ^ (m + 1)) % 7 ^ (m + 1) := by
      rw [← hg''eq, Nat.mod_mod]
    have h2 := padicValNat_eq_of_mod hmod (by rw [h1]; exact le_of_lt hjm)
      (mul_ne_zero (fun h => hlam2nd (h ▸ dvd_zero _)) hg'0)
    rw [← h2]; exact h1
  have hqg'' : qdig7 m ((lam * g) % 7 ^ (m + 1)) = T := by
    rw [hg''eq, qdig7_congr (Nat.mod_mod _ _), hlam2d,
      qdig7_multLow hjm hνg']
    linear_combination hKmul
  -- digit shifts: `q(e₁₃'') = edig + T`, `q(e₂₃'') = 3(udig − 3q(e₁₃''))`
  have hq13'' : qdig7 m (eMod7 m (lam * d1) (lam * d3)) = edig + T := by
    rw [he13'', qdig7_congr (Nat.mod_mod _ _), hlam2d,
      qdig7_multLow hjm hν13', ← hrg', hedd]
    linear_combination hKmul
  have hsum : 3 * qdig7 m (eMod7 m (lam * d1) (lam * d3))
      + 5 * qdig7 m (eMod7 m (lam * d2) (lam * d3)) = udig := by
    rw [he13'', he23'', qdig7_congr (Nat.mod_mod _ _),
      qdig7_congr (Nat.mod_mod _ _), hlam2d, qdig7_multLow hjm hν13',
      qdig7_multLow hjm hν23']
    have hzero : 3 * runit7 e13' + 5 * runit7 e23' = 0 := by
      rw [hrat']
      linear_combination (2 * runit7 e23') * h7z
    rw [hudd]
    linear_combination (↑K.val * hzero)
  have hq23'' : qdig7 m (eMod7 m (lam * d2) (lam * d3))
      = 3 * (udig - 3 * qdig7 m (eMod7 m (lam * d1) (lam * d3))) := by
    rw [← hsum]
    linear_combination (-2 * qdig7 m (eMod7 m (lam * d2) (lam * d3))) * h7z
  -- low parts of `e₁₃''`, `e₂₃''` are those of `e₁₃'`, `e₂₃'`
  -- (`Λ_j` preserves `mod 7^m` on level-`j` residues)
  have hlow13 : eMod7 m (lam * d1) (lam * d3) % 7 ^ m = e13' % 7 ^ m := by
    rw [he13'', Nat.mod_mod_of_dvd _
      (Nat.pow_dvd_pow 7 (Nat.le_succ m)), hlam2d]
    exact multLow_low (le_of_lt hjm)
      ((Nat.pow_dvd_iff_le_padicValNat (by norm_num) he13').mpr
        (le_of_eq hν13'.symm))
  have hlow23 : eMod7 m (lam * d2) (lam * d3) % 7 ^ m = e23' % 7 ^ m := by
    rw [he23'', Nat.mod_mod_of_dvd _
      (Nat.pow_dvd_pow 7 (Nat.le_succ m)), hlam2d]
    exact multLow_low (le_of_lt hjm)
      ((Nat.pow_dvd_iff_le_padicValNat (by norm_num) he23').mpr
        (le_of_eq hν23'.symm))
  -- borrows of the scaled elements
  have hrel13 : residueRelOf (lam * d1) (lam * d3) = residueRel.same :=
    rel_same_of_mul hlamnd (by rw [hr1, hr3]) (ne_of_gt hp3)
  have hrel23 : residueRelOf (lam * d2) (lam * d3) = residueRel.same :=
    rel_same_of_mul hlamnd (by rw [hr2, hr3]) (ne_of_gt hp3)
  have hrel12 : residueRelOf (lam * d1) (lam * d2) = residueRel.same :=
    rel_same_of_mul hlamnd (by rw [hr1, hr2]) (ne_of_gt hp2)
  have hb12 : qdig7 m (lam * d1) - qdig7 m (lam * d2)
      - qdig7 m (eMod7 m (lam * d1) (lam * d2))
      ∈ ({0, 1} : Finset (ZMod 7)) := by
    have hc := qdig_eMod_sub (m := m) hrel12
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc ⊢
    rcases hc with h | h
    · left; linear_combination -h
    · right; linear_combination -h - h7z
  have hb23 : qdig7 m (lam * d2) - qdig7 m (lam * d3)
      - qdig7 m (eMod7 m (lam * d2) (lam * d3))
      ∈ ({0, 1} : Finset (ZMod 7)) := by
    have hc := qdig_eMod_sub (m := m) hrel23
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc ⊢
    rcases hc with h | h
    · left; linear_combination -h
    · right; linear_combination -h - h7z
  have hb13 : qdig7 m (lam * d1) - qdig7 m (lam * d3)
      - qdig7 m (eMod7 m (lam * d1) (lam * d3))
      ∈ ({0, 1} : Finset (ZMod 7)) := by
    have hc := qdig_eMod_sub (m := m) hrel13
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc ⊢
    rcases hc with h | h
    · left; linear_combination -h
    · right; linear_combination -h - h7z
  -- `e₁₂''` and the borrow consistency `b₁₃ = b₁₂ + b₂₃ − δ`
  set δ'' := (if eMod7 m (lam * d1) (lam * d3) % 7 ^ m
      < eMod7 m (lam * d2) (lam * d3) % 7 ^ m
    then (1 : ZMod 7) else 0) with hδ''d
  have hqe12 : qdig7 m (eMod7 m (lam * d1) (lam * d2))
      = qdig7 m (eMod7 m (lam * d1) (lam * d3))
        - qdig7 m (eMod7 m (lam * d2) (lam * d3)) - δ'' := by
    have hsub := eMod7_sub_eq (m := m) hrel13 hrel23 hrel12
    rw [hsub, qdig7_congr (Nat.mod_mod _ _)]
    nth_rewrite 1 [show eMod7 m (lam * d1) (lam * d3)
        = eMod7 m (lam * d1) (lam * d3) % 7 ^ (m + 1)
        from (Nat.mod_eq_of_lt (eMod7_lt m (lam * d1) (lam * d3))).symm]
    nth_rewrite 1 [show eMod7 m (lam * d2) (lam * d3)
        = eMod7 m (lam * d2) (lam * d3) % 7 ^ (m + 1)
        from (Nat.mod_eq_of_lt (eMod7_lt m (lam * d2) (lam * d3))).symm]
    rw [qdig7_sub_resid, hδ''d]
  have hqe12' : qdig7 m (eMod7 m (lam * d1) (lam * d2))
      = qdig7 m (eMod7 m (lam * d1) (lam * d3))
        - qdig7 m (eMod7 m (lam * d2) (lam * d3)) - δ := by
    have hδ''δ : δ'' = δ := by rw [hδ''d, hδd, hlow13, hlow23]
    rw [← hδ''δ]; exact hqe12
  have hb_eq : (qdig7 m (lam * d1) - qdig7 m (lam * d2)
        - qdig7 m (eMod7 m (lam * d1) (lam * d2)))
      + (qdig7 m (lam * d2) - qdig7 m (lam * d3)
        - qdig7 m (eMod7 m (lam * d2) (lam * d3))) - δ
      = qdig7 m (lam * d1) - qdig7 m (lam * d3)
        - qdig7 m (eMod7 m (lam * d1) (lam * d3)) := by
    linear_combination -hqe12'
  -- dispatch: exceptional `(0,3)`-cell vs. the `case63_table` output
  by_cases hcell : edig = 0 ∧ udig = 3
  · have hT3 : T = 3 := hTexc hcell
    have hqA : qdig7 m (eMod7 m (lam * d1) (lam * d3)) = 3 := by
      rw [hq13'', hcell.1, hT3, zero_add]
    have hqB : qdig7 m (eMod7 m (lam * d2) (lam * d3)) = 3 := by
      rw [hq23'', hqA, hcell.2]; decide
    -- `q(e₄₅'') = 3`: for `σ = 1` it is `T`; for `σ = −1` it is
    -- `−T − 1 = −4 = 3` (paper's `q(2e₄₅) ∈ {0,6}` uses `q(e₄₅') = 3`
    -- in both sign cases).
    have hqC : qdig7 m (eMod7 m (lam * d4) (lam * d5)) = 3 := by
      have hconv := hgrel lam hlamr
      rcases hσ with rfl | rfl
      · rw [if_pos rfl, one_mul] at hconv
        have h1 := (ZMod.natCast_eq_natCast_iff' _ _ _).mp hconv
        rw [Nat.mod_eq_of_lt (eMod7_lt _ _ _), Nat.mod_mod] at h1
        rw [h1, hqg'', hT3]
      · rw [if_neg (show (-1 : ZMod 7) ≠ 1 by decide),
            neg_one_mul] at hconv
        have hlt : eMod7 m (lam * d4) (lam * d5) < 7 ^ (m + 1) :=
          eMod7_lt _ _ _
        have hcast : ((eMod7 m (lam * d4) (lam * d5) : ℕ)
              : ZMod (7 ^ (m + 1)))
            = (((7 ^ (m + 1) - ((lam * g) % 7 ^ (m + 1)) % 7 ^ (m + 1))
                % 7 ^ (m + 1) : ℕ) : ZMod _) := by
          rw [ZMod.natCast_mod]
          rw [Nat.cast_sub (by
            have := Nat.mod_lt ((lam * g) % 7 ^ (m + 1))
              (Nat.pow_pos (by norm_num) : 0 < 7 ^ (m + 1))
            omega)]
          rw [ZMod.natCast_self, ZMod.natCast_mod, zero_sub]
          rw [hconv]
        rw [ZMod.natCast_eq_natCast_iff'] at hcast
        rw [Nat.mod_eq_of_lt hlt, Nat.mod_mod] at hcast
        rw [hcast]
        have hg''low : ((lam * g) % 7 ^ (m + 1)) % 7 ^ m ≠ 0 :=
          c63_low_ne_of_level hg''0 (by rw [hνg'']; exact hjm)
        rw [c63_qdig_compl hg''low, hqg'', hT3]
        decide
    exact c63_eq_double hm hA2 hA4 hpos hunit hs0 hcls1 hcls2 hcls4
      hA1eq hA2eq hA4eq hne hp3 hr1 hr2 hr3 hr4 hr5 hlamnd hqA hqB hqC
  · obtain htab := hT hcell _ hb12 _ hb13 _ hb23 hb_eq.symm
    rw [show T + edig = qdig7 m (eMod7 m (lam * d1) (lam * d3)) from by
        rw [hq13'', add_comm]] at htab
    rw [← hq23''] at htab
    have hs1 : qdig7 m (eMod7 m (lam * d1) (lam * d3))
        + (qdig7 m (lam * d1) - qdig7 m (lam * d3)
          - qdig7 m (eMod7 m (lam * d1) (lam * d3)))
        = qdig7 m (lam * d1) - qdig7 m (lam * d3) := by ring
    have hs2 : qdig7 m (eMod7 m (lam * d2) (lam * d3))
        + (qdig7 m (lam * d2) - qdig7 m (lam * d3)
          - qdig7 m (eMod7 m (lam * d2) (lam * d3)))
        = qdig7 m (lam * d2) - qdig7 m (lam * d3) := by ring
    rw [hs1, hs2] at htab
    -- the rescaled `A₁` digit set is a translate of `{0, q₁−q₃, q₂−q₃}`
    have himg : ({d1, d2, d3} : Finset ℕ).image (fun d => qdig7 m (lam * d))
        = ({qdig7 m (lam * d1), qdig7 m (lam * d2), qdig7 m (lam * d3)}
            : Finset (ZMod 7)) := by
      rw [Finset.image_insert, Finset.image_insert, Finset.image_singleton]
    have htr : ({qdig7 m (lam * d1), qdig7 m (lam * d2), qdig7 m (lam * d3)}
          : Finset (ZMod 7))
        = ({0, qdig7 m (lam * d1) - qdig7 m (lam * d3),
            qdig7 m (lam * d2) - qdig7 m (lam * d3)} : Finset (ZMod 7)).image
          (· + qdig7 m (lam * d3)) := by
      ext x
      simp only [Finset.mem_image, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro (rfl | rfl | rfl)
        · exact ⟨_, Or.inr (Or.inl rfl), by ring⟩
        · exact ⟨_, Or.inr (Or.inr rfl), by ring⟩
        · exact ⟨0, Or.inl rfl, by ring⟩
      · rintro ⟨w, hw, rfl⟩
        rcases hw with rfl | rfl | rfl
        · exact Or.inr (Or.inr (by ring))
        · exact Or.inl (by ring)
        · exact Or.inr (Or.inl (by ring))
    have hlenconv : ∀ L : ℕ,
        apLen (({d1, d2, d3} : Finset ℕ).image
            (fun d => qdig7 m (lam * d))) ≤ L ↔
        apLen ({0, qdig7 m (lam * d1) - qdig7 m (lam * d3),
            qdig7 m (lam * d2) - qdig7 m (lam * d3)}
            : Finset (ZMod 7)) ≤ L := by
      intro L
      rw [himg, htr, apLen_image_add]
    rcases htab with hL | ⟨hL, hfin⟩
    · exact c63_finish2 (by omega) hpos hunit hs0 hcls1 hcls2 hcls4
        hA1eq hA2 hA4 hne hlamnd ((hlenconv 2).mpr hL)
    · -- `T ∈ {0,6}` forces `q(e₄₅'') ∈ {0,6}`, hence
      -- `ẽ(d₄'',d₅'') ∉ {2,4}`
      have hq45'' : qdig7 m (eMod7 m (lam * d4) (lam * d5))
          ∈ ({0, 6} : Finset (ZMod 7)) := by
        have hconv := hgrel lam hlamr
        rcases hσ with rfl | rfl
        · rw [if_pos rfl, one_mul] at hconv
          have h1 := (ZMod.natCast_eq_natCast_iff' _ _ _).mp hconv
          rw [Nat.mod_eq_of_lt (eMod7_lt _ _ _), Nat.mod_mod] at h1
          rw [h1, hqg'']
          exact hfin
        · rw [if_neg (show (-1 : ZMod 7) ≠ 1 by decide),
              neg_one_mul] at hconv
          have hlt : eMod7 m (lam * d4) (lam * d5) < 7 ^ (m + 1) :=
            eMod7_lt _ _ _
          have hcast : ((eMod7 m (lam * d4) (lam * d5) : ℕ)
                : ZMod (7 ^ (m + 1)))
              = (((7 ^ (m + 1) - ((lam * g) % 7 ^ (m + 1)) % 7 ^ (m + 1))
                  % 7 ^ (m + 1) : ℕ) : ZMod _) := by
            rw [ZMod.natCast_mod]
            rw [Nat.cast_sub (by
              have := Nat.mod_lt ((lam * g) % 7 ^ (m + 1))
                (Nat.pow_pos (by norm_num) : 0 < 7 ^ (m + 1))
              omega)]
            rw [ZMod.natCast_self, ZMod.natCast_mod, zero_sub]
            rw [hconv]
          rw [ZMod.natCast_eq_natCast_iff'] at hcast
          rw [Nat.mod_eq_of_lt hlt, Nat.mod_mod] at hcast
          rw [hcast]
          have hg''low : ((lam * g) % 7 ^ (m + 1)) % 7 ^ m ≠ 0 :=
            c63_low_ne_of_level hg''0 (by rw [hνg'']; exact hjm)
          rw [c63_qdig_compl hg''low, hqg'']
          simp only [Finset.mem_insert, Finset.mem_singleton] at hfin ⊢
          rcases hfin with rfl | rfl <;> decide
      have hrel45 : runit7 (lam * d5) = 2 * runit7 (lam * d4) := by
        have h1 : runit7 (lam * d5) = runit7 lam * runit7 d5 := runit7_mul _ _
        have h2 : runit7 (lam * d4) = runit7 lam * runit7 d4 := runit7_mul _ _
        rw [h1, h2, hr4, hr5]
        ring
      have hetd : etd7 m (lam * d4) (lam * d5)
          = 2 * qdig7 m (lam * d4) - qdig7 m (lam * d5) :=
        etd7_eq_twoX hrel45
      have hb45 := qdig_eMod_sub_etd7 (m := m) (x := lam * d4) (y := lam * d5)
      have hpair : (2 * qdig7 m (lam * d4) - qdig7 m (lam * d5) : ZMod 7)
          ∉ ({2, 4} : Finset (ZMod 7)) := by
        rw [← hetd]
        simp only [Finset.mem_insert, Finset.mem_singleton] at hq45'' hb45
        rcases hq45'' with hq | hq <;> rw [hq] at hb45 <;>
          rcases hb45 with h | h | h
        · have hv : etd7 m (lam * d4) (lam * d5) = 0 := by
            linear_combination -h
          rw [hv]; decide
        · have hv : etd7 m (lam * d4) (lam * d5) = -1 := by
            linear_combination -h
          rw [hv]; decide
        · have hv : etd7 m (lam * d4) (lam * d5) = -6 := by
            linear_combination -h
          rw [hv]; decide
        · have hv : etd7 m (lam * d4) (lam * d5) = 6 := by
            linear_combination -h
          rw [hv]; decide
        · have hv : etd7 m (lam * d4) (lam * d5) = 5 := by
            linear_combination -h
          rw [hv]; decide
        · have hv : etd7 m (lam * d4) (lam * d5) = 0 := by
            linear_combination -h
          rw [hv]; decide
      exact c63_finish3 (by omega) hpos hunit hs0 hcls1 hcls2 hcls4
        hA1eq hA2eq hA4eq hA2 hA4 hne hlamnd ((hlenconv 3).mpr hL) hpair

/-- Equal-level rescue, step 1 (paper `ii.2.b` after relabeling to
`r(e₄₅) = σ·r(e₁₃)`, `σ = ±1`): form the auxiliary residue
`f := (e₁₃ + N − g) % N` where `g := e₄₅` (`σ = 1`) or `g := N − e₄₅`
(`σ = −1`), so `e₁₃ ≡ g + f (mod N)` and `r(g) = r(e₁₃)`.  Then
`f = 0` or `j < ν(f) ≤ m` (`c63_f_level_gt`): normalize `f` with
`Λ_{ν(f)}` when `ν(f) < m` (paper's `ẽ = q(f') + δ̂`), a top scalar when
`ν(f) = m` (`f' = 7^m`, giving `ẽ = 1`), and `lam1 := 1` when `f = 0`.
The primed data then feed `c63_eq_step2`. -/
private theorem c63_eq_core {m : ℕ} (hm : 2 ≤ m) {A1 A2 A4 : Finset ℕ}
    (hA2 : A2.card = 1) (hA4 : A4.card = 1)
    (hpos : ∀ d ∈ A1 ∪ A2 ∪ A4, 0 < d)
    (hunit : ∀ d ∈ A1 ∪ A2 ∪ A4, padicValNat 7 d = 0)
    {s : ZMod 7} (hs0 : s ≠ 0)
    (hcls1 : ∀ d ∈ A1, runit7 d = s)
    (hcls2 : ∀ d ∈ A2, runit7 d = 2 * s)
    (hcls4 : ∀ d ∈ A4, runit7 d = 4 * s)
    {d1 d2 d3 d4 d5 : ℕ} {j : ℕ}
    (hA1eq : A1 = {d1, d2, d3}) (hA2eq : A2 = {d4}) (hA4eq : A4 = {d5})
    (hne : A1.Nonempty)
    (hp1 : 0 < d1) (hp2 : 0 < d2) (hp3 : 0 < d3) (hp4 : 0 < d4) (hp5 : 0 < d5)
    (hr1 : runit7 d1 = s) (hr2 : runit7 d2 = s) (hr3 : runit7 d3 = s)
    (hr4 : runit7 d4 = 2 * s) (hr5 : runit7 d5 = 4 * s)
    (hjm : j < m)
    (hν13 : padicValNat 7 (eMod7 m d1 d3) = j)
    (hν23 : padicValNat 7 (eMod7 m d2 d3) = j)
    (hν45 : padicValNat 7 (eMod7 m d4 d5) = j)
    (he13 : eMod7 m d1 d3 ≠ 0) (he23 : eMod7 m d2 d3 ≠ 0)
    (he45 : eMod7 m d4 d5 ≠ 0)
    (hrat : runit7 (eMod7 m d1 d3) = 3 * runit7 (eMod7 m d2 d3))
    {σ : ZMod 7} (hσ : σ = 1 ∨ σ = -1)
    (hr45 : runit7 (eMod7 m d4 d5) = σ * runit7 (eMod7 m d1 d3)) :
    ∃ lam : ℕ, ¬ 7 ∣ lam ∧ good7 m lam (A1 ∪ A2 ∪ A4) := by
  set N := 7 ^ (m + 1) with hN
  set e13 := eMod7 m d1 d3 with he13d
  set e23 := eMod7 m d2 d3 with he23d
  set e45 := eMod7 m d4 d5 with he45d
  -- the effective `e₄₅`-residue `g` with `r(g) = r(e₁₃)`
  obtain ⟨g, hg0, hgN, hνg, hrg, hgrel⟩ :
      ∃ g : ℕ, g ≠ 0 ∧ g < N ∧ padicValNat 7 g = j ∧
        runit7 g = runit7 e13 ∧
        (∀ lam : ℕ, runit7 lam ≠ 0 →
          ((eMod7 m (lam * d4) (lam * d5) : ℕ) : ZMod N)
            = (if σ = 1 then (1 : ZMod N) else -1)
              * (((lam * g) % N : ℕ) : ZMod N)) := by
    rcases hσ with rfl | rfl
    · refine ⟨e45, he45, eMod7_lt _ _ _, hν45, ?_, ?_⟩
      · simpa using hr45
      · intro lam hlamr
        rw [eMod7_smul hlamr, if_pos rfl, one_mul]
    · refine ⟨N - e45, ?_, ?_, ?_, ?_, ?_⟩
      · have hlt := eMod7_lt m d4 d5
        have hp := Nat.pos_of_ne_zero he45
        omega
      · have hlt := eMod7_lt m d4 d5
        have hp := Nat.pos_of_ne_zero he45
        omega
      · rw [hN, (c63_neg_resid_level he45 (eMod7_lt _ _ _)
          (by rw [hν45]; exact le_of_lt hjm)).1]
        exact hν45
      · have h1 := (c63_neg_resid_level he45 (eMod7_lt _ _ _)
          (by rw [hν45]; exact le_of_lt hjm)).2
        rw [hN, h1, hr45]
        ring
      · intro lam hlamr
        rw [if_neg (show (-1 : ZMod 7) ≠ 1 by decide), neg_one_mul]
        have hcast : ((eMod7 m (lam * d4) (lam * d5) : ℕ) : ZMod N)
            = ((lam * e45 : ℕ) : ZMod N) := by
          rw [eMod7_smul hlamr]
          exact ZMod.natCast_mod _ _
        have hgc : ((lam * (N - e45) : ℕ) : ZMod N)
            = -((lam * e45 : ℕ) : ZMod N) := by
          have hle : e45 ≤ N := le_of_lt (eMod7_lt _ _ _)
          rw [Nat.cast_mul, Nat.cast_sub hle, ZMod.natCast_self, zero_sub,
            Nat.cast_mul]
          ring
        rw [hcast]
        have h2 : (((lam * (N - e45)) % N : ℕ) : ZMod N)
            = ((lam * (N - e45) : ℕ) : ZMod N) := ZMod.natCast_mod _ _
        rw [h2, hgc]
        ring
  -- `f := (e13 + N − g) % N` satisfies `e13 ≡ g + f (mod N)`
  set f := (e13 + N - g) % N with hfd
  have hefg : ((e13 : ℕ) : ZMod N) = (g : ZMod N) + (f : ZMod N) := by
    have hfc : ((f : ℕ) : ZMod N) = ((e13 : ℕ) : ZMod N) - (g : ZMod N) := by
      have h1 : ((f : ℕ) : ZMod N) = ((e13 + N - g : ℕ) : ZMod N) := by
        rw [hfd]; exact ZMod.natCast_mod _ _
      rw [h1, Nat.cast_sub (by have := hgN; omega), Nat.cast_add,
        ZMod.natCast_self]
      ring
    linear_combination -hfc
  obtain hfC : f = 0 ∨ (j < padicValNat 7 f ∧ padicValNat 7 f ≤ m) := by
    rcases c63_f_level_gt he13 hg0 hν13 hνg (le_of_lt hjm) hgN hrg.symm
      with h | h
    · exact Or.inl h
    · exact Or.inr h
  -- step 1: choose `lam1` so that `q(e₁₃') − q(g') ∈ {0,1}` (the `ẽ`)
  obtain ⟨lam1, hlam1pos, hlam1nd, hlam1r, hed⟩ : ∃ lam1 : ℕ,
      0 < lam1 ∧ ¬ 7 ∣ lam1 ∧ runit7 lam1 ≠ 0 ∧
        qdig7 m (eMod7 m (lam1 * d1) (lam1 * d3))
          - qdig7 m ((lam1 * g) % N) ∈ ({0, 1} : Finset (ZMod 7)) := by
    rcases hfC with hf0 | ⟨hfgt, hfm⟩
    · -- `f = 0`: `e13 = g`, take `lam1 = 1`, `ẽ = 0`
      have h1r : runit7 (1 : ℕ) = 1 := by
        unfold runit7
        rw [padicValNat.eq_zero_of_not_dvd (by norm_num : ¬ 7 ∣ 1),
          pow_zero, Nat.div_one]
        decide
      refine ⟨1, one_pos, by norm_num, by rw [h1r]; exact one_ne_zero, ?_⟩
      have heqg : e13 = g := by
        have hcast : ((e13 : ℕ) : ZMod N) = (g : ZMod N) := by
          rw [hefg, hf0, Nat.cast_zero, add_zero]
        have hme := (ZMod.natCast_eq_natCast_iff' _ _ _).mp hcast
        rwa [Nat.mod_eq_of_lt (eMod7_lt _ _ _), Nat.mod_eq_of_lt hgN] at hme
      have he13' : eMod7 m (1 * d1) (1 * d3) = e13 := by
        rw [eMod7_smul (by rw [h1r]; exact one_ne_zero)]
        rw [one_mul, Nat.mod_eq_of_lt (eMod7_lt _ _ _)]
      rw [he13', heqg, one_mul, Nat.mod_eq_of_lt hgN, sub_self]
      simp
    · have hf0' : f ≠ 0 := by
        intro h
        rw [h, padicValNat_zero_right] at hfgt
        exact absurd hfgt (Nat.not_lt_zero _)
      rcases lt_or_ge (padicValNat 7 f) m with hνfm | hνfm
      · -- `νf < m`: `Λ_{νf}` sends `q(f')` to `0`
        obtain ⟨k, hk7, hkq⟩ := exists_multLow_set_qdig hνfm rfl hf0' 0
        set lam1 := 1 + k * 7 ^ (m - padicValNat 7 f) with hlam1d
        refine ⟨lam1, by positivity, multLow_not_dvd hνfm,
          by rw [hlam1d, runit7_multLow hνfm]; exact one_ne_zero, ?_⟩
        have hlam1r1 : runit7 lam1 = 1 := by
          rw [hlam1d]; exact runit7_multLow hνfm
        have he13' : eMod7 m (lam1 * d1) (lam1 * d3)
            = (lam1 * e13) % N := eMod7_mul hlam1r1
        -- `(lam1·g) ≡ e13' − (lam1·f)%N (mod N)` then
        -- `qdig_smul_eMod_eq` gives `q(lam1·g) = q13' − q(f') − δ̂`
        have hcast : ((lam1 * g : ℕ) : ZMod N)
            = ((eMod7 m (lam1 * d1) (lam1 * d3) : ℕ) : ZMod N)
              - (((lam1 * f) % N : ℕ) : ZMod N) := by
          have h1 : ((lam1 * e13 : ℕ) : ZMod N)
              = ((lam1 * g : ℕ) : ZMod N) + ((lam1 * f : ℕ) : ZMod N) := by
            push_cast
            rw [hefg]
            ring
          rw [he13', ZMod.natCast_mod _ _, ZMod.natCast_mod _ _]
          linear_combination -h1
        have hqdig := qdig_smul_eMod_eq hcast
        have hgg : qdig7 m ((lam1 * g) % N) = qdig7 m (lam1 * g) :=
          qdig7_congr (Nat.mod_mod _ _)
        have hqf : qdig7 m ((lam1 * f) % N) = 0 := by
          rw [qdig7_congr (Nat.mod_mod _ _)]
          exact hkq
        rw [hgg, hqdig, hqf]
        have hring : qdig7 m (eMod7 m (lam1 * d1) (lam1 * d3))
            - (qdig7 m (eMod7 m (lam1 * d1) (lam1 * d3)) - 0
              - (if eMod7 m (lam1 * d1) (lam1 * d3) % 7 ^ m
                  < ((lam1 * f) % N) % 7 ^ m then (1 : ZMod 7) else 0))
            = (if eMod7 m (lam1 * d1) (lam1 * d3) % 7 ^ m
                < ((lam1 * f) % N) % 7 ^ m then (1 : ZMod 7) else 0) := by
          ring
        rw [hring]
        split_ifs <;> simp
      · -- `νf = m`: a top scalar sends `f'` to `7^m`
        have hνfm' : padicValNat 7 f = m :=
          le_antisymm hfm hνfm
        obtain ⟨c, hcpos, hc7, hcmod, hqc⟩ :=
          exists_top_scalar_set hνfm' hf0' (t := 1) one_ne_zero
        have hcnd : ¬ 7 ∣ c := by
          intro hd
          have h0 : c = 0 := Nat.eq_zero_of_dvd_of_lt hd hc7
          omega
        have hcr : runit7 c ≠ 0 := by
          have hrc : runit7 c = (c : ZMod 7) := by
            unfold runit7
            rw [padicValNat.eq_zero_of_not_dvd hcnd, pow_zero, Nat.div_one]
          rw [hrc]
          intro h
          exact hcnd ((ZMod.natCast_eq_zero_iff c 7).mp h)
        refine ⟨c, hcpos, hcnd, hcr, ?_⟩
        have he13' : eMod7 m (c * d1) (c * d3) = (c * e13) % N :=
          eMod7_smul hcr
        have hf' : (c * f) % N = 1 * 7 ^ m := by
          have h := hcmod
          rw [show ZMod.val (1 : ZMod 7) = 1 from by decide, ← hN] at h
          exact h
        -- `e13' = (g' + 7^m) % N`, hence `q13' = q(g') + 1`
        have hdecomp : eMod7 m (c * d1) (c * d3)
            = (((c * g) % N) + 1 * 7 ^ m) % N := by
          have hcast : ((eMod7 m (c * d1) (c * d3) : ℕ) : ZMod N)
              = (((((c * g) % N) + 1 * 7 ^ m) % N : ℕ) : ZMod N) := by
            have h1 : ((c * e13 : ℕ) : ZMod N)
                = ((c * g : ℕ) : ZMod N) + ((c * f : ℕ) : ZMod N) := by
              push_cast
              rw [hefg]
              ring
            have h2 : ((c * f : ℕ) : ZMod N)
                = ((1 * 7 ^ m : ℕ) : ZMod N) := by
              rw [← ZMod.natCast_mod (c * f) N, hf']
            rw [he13', ZMod.natCast_mod _ _, ZMod.natCast_mod _ _,
              Nat.cast_add, ZMod.natCast_mod _ _, h1, h2]
          rw [ZMod.natCast_eq_natCast_iff'] at hcast
          rwa [Nat.mod_eq_of_lt (eMod7_lt _ _ _), Nat.mod_mod] at hcast
        have htop : qdig7 m (eMod7 m (c * d1) (c * d3))
            = qdig7 m ((c * g) % N) + 1 := by
          have h := qdig7_add_top_resid (m := m)
            (x := eMod7 m (c * d1) (c * d3)) (y := (c * g) % N) (k := 1)
            (by rw [Nat.mod_eq_of_lt (eMod7_lt _ _ _), Nat.mod_mod _ _]
                exact hdecomp)
          simpa using h
        rw [htop, add_sub_cancel_left]
        decide
  -- uniform primed facts feeding `c63_eq_step2`
  have he13'e : eMod7 m (lam1 * d1) (lam1 * d3) = (lam1 * e13) % N :=
    eMod7_smul hlam1r
  have he23'e : eMod7 m (lam1 * d2) (lam1 * d3) = (lam1 * e23) % N :=
    eMod7_smul hlam1r
  have hνl13 : padicValNat 7 (lam1 * e13) = j := by
    rw [padicValNat_mul_seven hlam1nd he13, hν13]
  have hνl23 : padicValNat 7 (lam1 * e23) = j := by
    rw [padicValNat_mul_seven hlam1nd he23, hν23]
  have hνlg : padicValNat 7 (lam1 * g) = j := by
    rw [padicValNat_mul_seven hlam1nd hg0, hνg]
  have hmod13 : (lam1 * e13) % N = (eMod7 m (lam1 * d1) (lam1 * d3)) % N := by
    rw [he13'e, Nat.mod_mod]
  have hmod23 : (lam1 * e23) % N = (eMod7 m (lam1 * d2) (lam1 * d3)) % N := by
    rw [he23'e, Nat.mod_mod]
  have hmodg : (lam1 * g) % N = ((lam1 * g) % N) % N := (Nat.mod_mod _ _).symm
  have hν13' : padicValNat 7 (eMod7 m (lam1 * d1) (lam1 * d3)) = j := by
    have h2 := padicValNat_eq_of_mod hmod13 (by rw [hνl13]; exact le_of_lt hjm)
      (mul_ne_zero (ne_of_gt hlam1pos) he13)
    rw [← h2]; exact hνl13
  have hν23' : padicValNat 7 (eMod7 m (lam1 * d2) (lam1 * d3)) = j := by
    have h2 := padicValNat_eq_of_mod hmod23 (by rw [hνl23]; exact le_of_lt hjm)
      (mul_ne_zero (ne_of_gt hlam1pos) he23)
    rw [← h2]; exact hνl23
  have hνg' : padicValNat 7 ((lam1 * g) % N) = j := by
    have h2 := padicValNat_eq_of_mod hmodg (by rw [hνlg]; exact le_of_lt hjm)
      (mul_ne_zero (ne_of_gt hlam1pos) hg0)
    rw [← h2]; exact hνlg
  have he13'0 : eMod7 m (lam1 * d1) (lam1 * d3) ≠ 0 := by
    rw [he13'e]
    exact c63_res_ne_of_level (mul_ne_zero (ne_of_gt hlam1pos) he13)
      (by rw [hνl13]; omega)
  have he23'0 : eMod7 m (lam1 * d2) (lam1 * d3) ≠ 0 := by
    rw [he23'e]
    exact c63_res_ne_of_level (mul_ne_zero (ne_of_gt hlam1pos) he23)
      (by rw [hνl23]; omega)
  have hg'0 : (lam1 * g) % N ≠ 0 :=
    c63_res_ne_of_level (mul_ne_zero (ne_of_gt hlam1pos) hg0)
      (by rw [hνlg]; omega)
  have hrat' : runit7 (eMod7 m (lam1 * d1) (lam1 * d3))
      = 3 * runit7 (eMod7 m (lam1 * d2) (lam1 * d3)) := by
    have hr13' : runit7 (eMod7 m (lam1 * d1) (lam1 * d3))
        = runit7 (lam1 * e13) :=
      (runit7_eq_of_mod hmod13 (by rw [hνl13]; exact le_of_lt hjm)
        (mul_ne_zero (ne_of_gt hlam1pos) he13)).symm
    have hr23' : runit7 (eMod7 m (lam1 * d2) (lam1 * d3))
        = runit7 (lam1 * e23) :=
      (runit7_eq_of_mod hmod23 (by rw [hνl23]; exact le_of_lt hjm)
        (mul_ne_zero (ne_of_gt hlam1pos) he23)).symm
    rw [hr13', hr23', runit7_mul, runit7_mul, hrat]
    ring
  have hrg' : runit7 ((lam1 * g) % N)
      = runit7 (eMod7 m (lam1 * d1) (lam1 * d3)) := by
    have hrg'v : runit7 ((lam1 * g) % N) = runit7 (lam1 * g) :=
      (runit7_eq_of_mod hmodg (by rw [hνlg]; exact le_of_lt hjm)
        (mul_ne_zero (ne_of_gt hlam1pos) hg0)).symm
    have hr13' : runit7 (eMod7 m (lam1 * d1) (lam1 * d3))
        = runit7 (lam1 * e13) :=
      (runit7_eq_of_mod hmod13 (by rw [hνl13]; exact le_of_lt hjm)
        (mul_ne_zero (ne_of_gt hlam1pos) he13)).symm
    rw [hrg'v, hr13', runit7_mul, runit7_mul, hrg]
  exact c63_eq_step2 hm hA2 hA4 hpos hunit hs0 hcls1 hcls2 hcls4
    hA1eq hA2eq hA4eq hne hp2 hp3 hr1 hr2 hr3 hr4 hr5 hjm
    hlam1pos hlam1nd hlam1r hg0 hgN hν13' hν23' he13'0 he23'0 hrat'
    hg'0 hνg' hrg' hed hσ hgrel

/-- §6.3 (ii.2) low subcase `ν(e₄₅) = ν(e₁₃) = ν(e₂₃) = j`: the paper's
`ii.2.b` relabeling.  Writing `u := r(e₂₃)`, the residue `w := r(e₄₅)`
is a unit, hence `w ∈ {u,…,6u}`.  The three cyclic orders of `A₁` give
`r(e₁₃') ∈ {3u, 5u, 6u}` (with `r(e₁₃') = 3r(e₂₃')` preserved), and
`{3u,4u,5u, 2u,6u,u} = {w, −w}` covers all six cases: `w ∈ {3u,4u}` uses
order `(d1,d2,d3)` with `σ = 1,−1`; `w ∈ {5u,2u}` uses `(d2,d3,d1)`;
`w ∈ {6u,u}` uses `(d3,d1,d2)`.  Each case hands `c63_eq_core` the
matching `r(e₄₅) = σ·r(e₁₃')`. -/
private theorem c63_ii2_low_eq {m : ℕ} (hm : 2 ≤ m)
    {A1 A2 A4 : Finset ℕ}
    (hA2 : A2.card = 1) (hA4 : A4.card = 1)
    (hpos : ∀ d ∈ A1 ∪ A2 ∪ A4, 0 < d)
    (hunit : ∀ d ∈ A1 ∪ A2 ∪ A4, padicValNat 7 d = 0)
    {s : ZMod 7} (hs0 : s ≠ 0)
    (hcls1 : ∀ d ∈ A1, runit7 d = s)
    (hcls2 : ∀ d ∈ A2, runit7 d = 2 * s)
    (hcls4 : ∀ d ∈ A4, runit7 d = 4 * s)
    {d1 d2 d3 d4 d5 : ℕ}
    (hA1eq : A1 = {d1, d2, d3}) (hA2eq : A2 = {d4}) (hA4eq : A4 = {d5})
    (hne : A1.Nonempty)
    (hp1 : 0 < d1) (hp2 : 0 < d2) (hp3 : 0 < d3) (hp4 : 0 < d4) (hp5 : 0 < d5)
    (hr1 : runit7 d1 = s) (hr2 : runit7 d2 = s) (hr3 : runit7 d3 = s)
    (hr4 : runit7 d4 = 2 * s) (hr5 : runit7 d5 = 4 * s)
    (hνeq : padicValNat 7 (eMod7 m d1 d3) = padicValNat 7 (eMod7 m d2 d3))
    (hνm : padicValNat 7 (eMod7 m d2 d3) < m)
    (hrat : runit7 (eMod7 m d1 d3) = 3 * runit7 (eMod7 m d2 d3))
    (he13 : eMod7 m d1 d3 ≠ 0) (he23 : eMod7 m d2 d3 ≠ 0)
    (he45 : eMod7 m d4 d5 ≠ 0)
    (hν45 : padicValNat 7 (eMod7 m d4 d5)
      = padicValNat 7 (eMod7 m d2 d3)) :
    ∃ lam : ℕ, ¬ 7 ∣ lam ∧ good7 m lam (A1 ∪ A2 ∪ A4) := by
  set j := padicValNat 7 (eMod7 m d2 d3) with hj
  have h7 : (7 : ZMod 7) = 0 := by decide
  have hν23 : padicValNat 7 (eMod7 m d2 d3) = j := rfl
  have hν13 : padicValNat 7 (eMod7 m d1 d3) = j := hνeq
  have hν45v : padicValNat 7 (eMod7 m d4 d5) = j := hν45
  have hjm : j < m := hνm
  -- `same` relations on all `A₁` pairs (both directions)
  have hrel13 : residueRelOf d1 d3 = residueRel.same :=
    rel_same (by rw [hr1, hr3]) (by rw [hr3]; exact hs0)
  have hrel23 : residueRelOf d2 d3 = residueRel.same :=
    rel_same (by rw [hr2, hr3]) (by rw [hr3]; exact hs0)
  have hrel12 : residueRelOf d1 d2 = residueRel.same :=
    rel_same (by rw [hr1, hr2]) (by rw [hr2]; exact hs0)
  have hrel31 : residueRelOf d3 d1 = residueRel.same :=
    rel_same (by rw [hr3, hr1]) (by rw [hr1]; exact hs0)
  have hrel21 : residueRelOf d2 d1 = residueRel.same :=
    rel_same (by rw [hr2, hr1]) (by rw [hr1]; exact hs0)
  have hrel32 : residueRelOf d3 d2 = residueRel.same :=
    rel_same (by rw [hr3, hr2]) (by rw [hr2]; exact hs0)
  -- `e₁₂` also sits at level `j` (`r(e₁₃) ≠ r(e₂₃)` from `3u ≠ u`)
  have hrne : runit7 (eMod7 m d1 d3) ≠ runit7 (eMod7 m d2 d3) := by
    intro h
    rw [hrat] at h
    have h1 : (2 : ZMod 7) * runit7 (eMod7 m d2 d3) = 0 := by
      linear_combination h
    rcases mul_eq_zero.mp h1 with h2 | h2
    · exact absurd h2 (by decide)
    · exact runit7_ne_zero (Nat.pos_of_ne_zero he23) h2
  obtain ⟨he12, hν12, hr12⟩ := c63_eMod7_level_of_runit_ne hrel13 hrel23
    hrel12 he13 he23 hν13 hν23 (le_of_lt hjm) hrne
  -- reversal data for the two rotated orders
  obtain ⟨he21, hν21, hr21⟩ := c63_rev_level hrel12 hrel21 he12
    (by rw [hν12]; exact le_of_lt hjm)
  obtain ⟨he31, hν31, hr31⟩ := c63_rev_level hrel13 hrel31 he13
    (by rw [hν13]; exact le_of_lt hjm)
  obtain ⟨he32, hν32, hr32⟩ := c63_rev_level hrel23 hrel32 he23
    (by rw [hν23]; exact le_of_lt hjm)
  -- `w := r(e₄₅)` is one of `u,…,6u`
  have hr23' : runit7 (eMod7 m d2 d3) ≠ 0 :=
    runit7_ne_zero (Nat.pos_of_ne_zero he23)
  have hr45' : runit7 (eMod7 m d4 d5) ≠ 0 :=
    runit7_ne_zero (Nat.pos_of_ne_zero he45)
  have hcases : runit7 (eMod7 m d4 d5) = runit7 (eMod7 m d2 d3)
      ∨ runit7 (eMod7 m d4 d5) = 2 * runit7 (eMod7 m d2 d3)
      ∨ runit7 (eMod7 m d4 d5) = 3 * runit7 (eMod7 m d2 d3)
      ∨ runit7 (eMod7 m d4 d5) = 4 * runit7 (eMod7 m d2 d3)
      ∨ runit7 (eMod7 m d4 d5) = 5 * runit7 (eMod7 m d2 d3)
      ∨ runit7 (eMod7 m d4 d5) = 6 * runit7 (eMod7 m d2 d3) := by
    have hd : ∀ u w : ZMod 7, u ≠ 0 → w ≠ 0 →
        w = u ∨ w = 2 * u ∨ w = 3 * u ∨ w = 4 * u ∨ w = 5 * u
          ∨ w = 6 * u := by decide
    exact hd _ _ hr23' hr45'
  rcases hcases with h | h | h | h | h | h
  · -- `w = u`: order `(d3,d1,d2)`, `r(e₃₂) = −u`, `σ = −1`
    have hA1' : A1 = {d3, d1, d2} := by
      rw [hA1eq]; ext x
      simp only [Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro (rfl | rfl | rfl)
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr rfl)
        · exact Or.inl rfl
      · rintro (rfl | rfl | rfl)
        · exact Or.inr (Or.inr rfl)
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
    exact c63_eq_core hm hA2 hA4 hpos hunit hs0 hcls1 hcls2 hcls4
      hA1' hA2eq hA4eq hne hp3 hp1 hp2 hp4 hp5
      hr3 hr1 hr2 hr4 hr5 hjm
      (hν32.trans hν23) hν12 hν45v he32 he12 he45
      (by rw [hr32, hr12, hrat]; linear_combination (-runit7 (eMod7 m d2 d3)) * h7)
      (hσ := Or.inr rfl)
      (by rw [hr32]; linear_combination h)
  · -- `w = 2u`: order `(d2,d3,d1)`, `r(e₂₁) = −2u`, `σ = −1`
    have hA1' : A1 = {d2, d3, d1} := by
      rw [hA1eq]; ext x
      simp only [Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro (rfl | rfl | rfl)
        · exact Or.inr (Or.inr rfl)
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
      · rintro (rfl | rfl | rfl)
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr rfl)
        · exact Or.inl rfl
    exact c63_eq_core hm hA2 hA4 hpos hunit hs0 hcls1 hcls2 hcls4
      hA1' hA2eq hA4eq hne hp2 hp3 hp1 hp4 hp5
      hr2 hr3 hr1 hr4 hr5 hjm
      (hν21.trans hν12) (hν31.trans hν13) hν45v he21 he31 he45
      (by rw [hr21, hr31, hr12, hrat]; linear_combination runit7 (eMod7 m d2 d3) * h7)
      (hσ := Or.inr rfl)
      (by rw [hr21, hr12]; linear_combination h - hrat)
  · -- `w = 3u`: order `(d1,d2,d3)`, `r(e₁₃) = 3u`, `σ = 1`
    exact c63_eq_core hm hA2 hA4 hpos hunit hs0 hcls1 hcls2 hcls4
      hA1eq hA2eq hA4eq hne hp1 hp2 hp3 hp4 hp5
      hr1 hr2 hr3 hr4 hr5 hjm
      hν13 hν23 hν45v he13 he23 he45 hrat
      (hσ := Or.inl rfl)
      (by linear_combination h - hrat)
  · -- `w = 4u`: order `(d1,d2,d3)`, `−r(e₁₃) = −3u = 4u`, `σ = −1`
    exact c63_eq_core hm hA2 hA4 hpos hunit hs0 hcls1 hcls2 hcls4
      hA1eq hA2eq hA4eq hne hp1 hp2 hp3 hp4 hp5
      hr1 hr2 hr3 hr4 hr5 hjm
      hν13 hν23 hν45v he13 he23 he45 hrat
      (hσ := Or.inr rfl)
      (by rw [h, hrat]; linear_combination runit7 (eMod7 m d2 d3) * h7)
  · -- `w = 5u`: order `(d2,d3,d1)`, `r(e₂₁) = −2u = 5u`, `σ = 1`
    have hA1' : A1 = {d2, d3, d1} := by
      rw [hA1eq]; ext x
      simp only [Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro (rfl | rfl | rfl)
        · exact Or.inr (Or.inr rfl)
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
      · rintro (rfl | rfl | rfl)
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr rfl)
        · exact Or.inl rfl
    exact c63_eq_core hm hA2 hA4 hpos hunit hs0 hcls1 hcls2 hcls4
      hA1' hA2eq hA4eq hne hp2 hp3 hp1 hp4 hp5
      hr2 hr3 hr1 hr4 hr5 hjm
      (hν21.trans hν12) (hν31.trans hν13) hν45v he21 he31 he45
      (by rw [hr21, hr31, hr12, hrat]; linear_combination runit7 (eMod7 m d2 d3) * h7)
      (hσ := Or.inl rfl)
      (by rw [hr21, hr12, h, hrat]; linear_combination runit7 (eMod7 m d2 d3) * h7)
  · -- `w = 6u`: order `(d3,d1,d2)`, `r(e₃₂) = −u = 6u`, `σ = 1`
    have hA1' : A1 = {d3, d1, d2} := by
      rw [hA1eq]; ext x
      simp only [Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro (rfl | rfl | rfl)
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr rfl)
        · exact Or.inl rfl
      · rintro (rfl | rfl | rfl)
        · exact Or.inr (Or.inr rfl)
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
    exact c63_eq_core hm hA2 hA4 hpos hunit hs0 hcls1 hcls2 hcls4
      hA1' hA2eq hA4eq hne hp3 hp1 hp2 hp4 hp5
      hr3 hr1 hr2 hr4 hr5 hjm
      (hν32.trans hν23) hν12 hν45v he32 he12 he45
      (by rw [hr32, hr12, hrat]; linear_combination (-runit7 (eMod7 m d2 d3)) * h7)
      (hσ := Or.inl rfl)
      (by rw [hr32, h]; linear_combination runit7 (eMod7 m d2 d3) * h7)

set_option maxHeartbeats 3000000 in
private theorem c63_case_ii2_low {m : ℕ} (hm : 2 ≤ m)
    {A1 A2 A4 : Finset ℕ}
    (hA2 : A2.card = 1) (hA4 : A4.card = 1)
    (hpos : ∀ d ∈ A1 ∪ A2 ∪ A4, 0 < d)
    (hunit : ∀ d ∈ A1 ∪ A2 ∪ A4, padicValNat 7 d = 0)
    {s : ZMod 7} (hs0 : s ≠ 0)
    (hcls1 : ∀ d ∈ A1, runit7 d = s)
    (hcls2 : ∀ d ∈ A2, runit7 d = 2 * s)
    (hcls4 : ∀ d ∈ A4, runit7 d = 4 * s)
    {d1 d2 d3 d4 d5 : ℕ}
    (hA1eq : A1 = {d1, d2, d3}) (hA2eq : A2 = {d4}) (hA4eq : A4 = {d5})
    (hne : A1.Nonempty)
    (hp1 : 0 < d1) (hp2 : 0 < d2) (hp3 : 0 < d3) (hp4 : 0 < d4) (hp5 : 0 < d5)
    (hu1 : padicValNat 7 d1 = 0) (hu2 : padicValNat 7 d2 = 0)
    (hu3 : padicValNat 7 d3 = 0) (hu4 : padicValNat 7 d4 = 0)
    (hu5 : padicValNat 7 d5 = 0)
    (hr1 : runit7 d1 = s) (hr2 : runit7 d2 = s) (hr3 : runit7 d3 = s)
    (hr4 : runit7 d4 = 2 * s) (hr5 : runit7 d5 = 4 * s)
    (hνeq : padicValNat 7 (eMod7 m d1 d3) = padicValNat 7 (eMod7 m d2 d3))
    (hνm : padicValNat 7 (eMod7 m d2 d3) < m)
    (hrat : runit7 (eMod7 m d1 d3) = 3 * runit7 (eMod7 m d2 d3))
    (he13 : eMod7 m d1 d3 ≠ 0) (he23 : eMod7 m d2 d3 ≠ 0) :
    ∃ lam : ℕ, ¬ 7 ∣ lam ∧ good7 m lam (A1 ∪ A2 ∪ A4) := by
  obtain ⟨lam, hlam, _hqe, _hpairs, _hj2, hlen⟩ := lemma9_ii
    ⟨hp2, hp1, hp3⟩ ⟨hu2, hu1, hu3⟩
    ⟨hr2.trans hr1.symm, hr1.trans hr3.symm⟩ hνeq.symm
    (by rwa [hνeq]) (Or.inr rfl) hrat
  have hset : ({d2, d1, d3} : Finset ℕ) = ({d1, d2, d3} : Finset ℕ) := by
    rw [Finset.insert_comm d2 d1]
  rw [hset] at hlen
  by_cases hpair : (2 * qdig7 m (lam * d4) - qdig7 m (lam * d5) : ZMod 7) ∉ ({2, 4} : Finset (ZMod 7))
  · exact c63_finish3 (by omega) hpos hunit hs0 hcls1 hcls2 hcls4
      hA1eq hA2eq hA4eq hA2 hA4 hne hlam hlen hpair
  · -- the `(d₄,d₅)` pair is bad for `lam`: rescue by a second multiplier
    push_neg at hpair
    by_cases he45z : eMod7 m d4 d5 = 0
    · -- `e₄₅ = 0` forces `ẽ(d₄',d₅') ∈ {0,1,6}`, contradicting `hpair`
      exfalso
      have hlampos : 0 < lam :=
        Nat.pos_of_ne_zero (fun h0 => hlam (h0 ▸ dvd_zero _))
      have hlamr0 : runit7 lam ≠ 0 := runit7_ne_zero hlampos
      have hrel45 : runit7 (lam * d5) = 2 * runit7 (lam * d4) := by
        have h1 : runit7 (lam * d5) = runit7 lam * runit7 d5 :=
          runit7_mul _ _
        have h2 : runit7 (lam * d4) = runit7 lam * runit7 d4 :=
          runit7_mul _ _
        rw [h1, h2, hr4, hr5]
        ring
      have he45'z : eMod7 m (lam * d4) (lam * d5) = 0 := by
        rw [eMod7_smul hlamr0, he45z, Nat.mul_zero, Nat.zero_mod]
      have hetd : etd7 m (lam * d4) (lam * d5)
          = 2 * qdig7 m (lam * d4) - qdig7 m (lam * d5) :=
        etd7_eq_twoX hrel45
      have hb45 := qdig_eMod_sub_etd7 (m := m) (x := lam * d4)
        (y := lam * d5)
      rw [he45'z, qdig7_zero, hetd] at hb45
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb45 hpair
      rcases hb45 with h | h | h <;> rcases hpair with hp | hp <;>
        rw [hp] at h <;> exact absurd h (by decide)
    · -- `e₄₅ ≠ 0`: dispatch on `ν(e₄₅)` vs the common first-three level
      rcases lt_trichotomy (padicValNat 7 (eMod7 m d4 d5))
          (padicValNat 7 (eMod7 m d2 d3)) with hν45 | hν45 | hν45
      · exact c63_ii2_low_lt hm hA2 hA4 hpos hunit hs0 hcls1 hcls2 hcls4
          hA1eq hA2eq hA4eq hne hp1 hp2 hp3 hp4 hp5
          hr1 hr2 hr3 hr4 hr5 hνeq hνm hrat he45z hν45
      · exact c63_ii2_low_eq hm hA2 hA4 hpos hunit hs0 hcls1 hcls2 hcls4
          hA1eq hA2eq hA4eq hne hp1 hp2 hp3 hp4 hp5
          hr1 hr2 hr3 hr4 hr5 hνeq hνm hrat he13 he23 he45z hν45
      · exact c63_ii2_low_gt hm hA2 hA4 hpos hunit hs0 hcls1 hcls2 hcls4
          hA1eq hA2eq hA4eq hne hp1 hp2 hp3 hp4 hp5 hu1 hu2 hu3
          hr1 hr2 hr3 hr4 hr5 hνeq hνm hrat he13 he23 he45z hν45

/-- **Theorem 6.3** (`case63`): For `A1, A2, A4` with cards 3, 1, 1 and residue classes
`s, 2s, 4s` respectively (`s ∈ {1, 2, 4}`), there exists a multiplier `lam` coprime to 7
such that `good7 m lam (A1 ∪ A2 ∪ A4)` holds. -/
theorem case63 {m : ℕ} (hm : 1 < m) {A1 A2 A4 : Finset ℕ}
    (hA1 : A1.card = 3) (hA2 : A2.card = 1) (hA4 : A4.card = 1)
    (hpos : ∀ d ∈ A1 ∪ A2 ∪ A4, 0 < d)
    (hunit : ∀ d ∈ A1 ∪ A2 ∪ A4, padicValNat 7 d = 0)
    {s : ZMod 7} (hs : s ∈ ({1, 2, 4} : Finset (ZMod 7)))
    (hcls1 : ∀ d ∈ A1, runit7 d = s)
    (hcls2 : ∀ d ∈ A2, runit7 d = 2 * s)
    (hcls4 : ∀ d ∈ A4, runit7 d = 4 * s) :
    ∃ lam : ℕ, ¬ 7 ∣ lam ∧ good7 m lam (A1 ∪ A2 ∪ A4) := by
  have hm2 : 2 ≤ m := by omega
  have hs0 : s ≠ 0 := by
    intro h0
    rw [h0] at hs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with h | h | h <;> exact absurd h (by decide)
  have hpos1 : ∀ d ∈ A1, 0 < d := fun d hd =>
    hpos d (Finset.mem_union_left _ (Finset.mem_union_left _ hd))
  have hunit1 : ∀ d ∈ A1, padicValNat 7 d = 0 := fun d hd =>
    hunit d (Finset.mem_union_left _ (Finset.mem_union_left _ hd))
  obtain ⟨d1, hd1, d2, hd2, d3, hd3, hA1eq, hdisj⟩ :=
    lemma11 hA1 s hpos1 hunit1 hcls1
  obtain ⟨d4, hd4⟩ : ∃ d4, A2 = {d4} := Finset.card_eq_one.mp hA2
  obtain ⟨d5, hd5⟩ : ∃ d5, A4 = {d5} := Finset.card_eq_one.mp hA4
  have hne : A1.Nonempty := Finset.card_pos.mp (by rw [hA1]; norm_num)
  have hp1 : 0 < d1 := hpos1 d1 hd1
  have hp2 : 0 < d2 := hpos1 d2 hd2
  have hp3 : 0 < d3 := hpos1 d3 hd3
  have hd4mem : d4 ∈ A1 ∪ A2 ∪ A4 :=
    Finset.mem_union_left _ (Finset.mem_union_right _ (by rw [hd4]; exact Finset.mem_singleton_self _))
  have hd5mem : d5 ∈ A1 ∪ A2 ∪ A4 :=
    Finset.mem_union_right _ (by rw [hd5]; exact Finset.mem_singleton_self _)
  have hp4 : 0 < d4 := hpos d4 hd4mem
  have hp5 : 0 < d5 := hpos d5 hd5mem
  have hu1 : padicValNat 7 d1 = 0 := hunit1 d1 hd1
  have hu2 : padicValNat 7 d2 = 0 := hunit1 d2 hd2
  have hu3 : padicValNat 7 d3 = 0 := hunit1 d3 hd3
  have hu4 : padicValNat 7 d4 = 0 := hunit d4 hd4mem
  have hu5 : padicValNat 7 d5 = 0 := hunit d5 hd5mem
  have hr1 : runit7 d1 = s := hcls1 d1 hd1
  have hr2 : runit7 d2 = s := hcls1 d2 hd2
  have hr3 : runit7 d3 = s := hcls1 d3 hd3
  have hr4 : runit7 d4 = 2 * s := hcls2 d4 (by rw [hd4]; exact Finset.mem_singleton_self _)
  have hr5 : runit7 d5 = 4 * s := hcls4 d5 (by rw [hd5]; exact Finset.mem_singleton_self _)
  rcases hdisj with ⟨hlgt, _⟩ | ⟨heq, hratios⟩
  · exact c63_case_i hm2 hA2 hA4 hpos hunit hs0 hcls1 hcls2 hcls4
      hA1eq hne hp1 hp2 hp3 hu1 hu2 hu3 hr1 hr2 hr3 hlgt
  · by_cases he23_zero : eMod7 m d2 d3 = 0
    · have he13_zero : eMod7 m d1 d3 = 0 := by
        by_contra he13
        have h1 := elevel7_of_eq he23_zero
        have h2 := elevel7_of_ne he13
        have h3 : padicValNat 7 (eMod7 m d1 d3) ≤ m := enu7_le_of_ne he13
        omega
      exact c63_case_collision (by omega) hA2 hA4 hpos hunit hs0
        hcls1 hcls2 hcls4 hA1eq hne hp3 hr1 hr2 hr3 he13_zero he23_zero
    · have he13_ne : eMod7 m d1 d3 ≠ 0 := by
        intro h0
        have h1 := elevel7_of_eq h0
        have h2 := elevel7_of_ne he23_zero
        have h3 : padicValNat 7 (eMod7 m d2 d3) ≤ m := enu7_le_of_ne he23_zero
        omega
      have hν13 : padicValNat 7 (eMod7 m d1 d3) = elevel7 m d1 d3 :=
        (elevel7_of_ne he13_ne).symm
      have hν23 : padicValNat 7 (eMod7 m d2 d3) = elevel7 m d2 d3 :=
        (elevel7_of_ne he23_zero).symm
      have hνeq : padicValNat 7 (eMod7 m d1 d3) = padicValNat 7 (eMod7 m d2 d3) := by
        rw [hν13, hν23, heq]
      have hνle : padicValNat 7 (eMod7 m d2 d3) ≤ m :=
        enu7_le_of_ne he23_zero
      rcases eq_or_lt_of_le hνle with htop | hlow
      · rcases hratios with hrat2 | ⟨hrat3, _⟩
        · exact c63_case_ii1_top hm2 hA2 hA4 hpos hunit hs0 hcls1 hcls2 hcls4
            hA1eq hd4 hd5 hne hp1 hp2 hp3 hp4 hp5 hu1 hu2 hu3 hu4 hu5
            hr1 hr2 hr3 hr4 hr5 he13_ne he23_zero (hνeq ▸ htop) htop hrat2
        · exact c63_case_ii2_top hm2 hA2 hA4 hpos hunit hs0 hcls1 hcls2 hcls4
            hA1eq hd4 hd5 hne hp1 hp2 hp3 hp4 hp5 hu1 hu2 hu3 hu4 hu5
            hr1 hr2 hr3 hr4 hr5 he13_ne he23_zero (hνeq ▸ htop) htop hrat3
      · rcases hratios with hrat2 | ⟨hrat3, _⟩
        · exact c63_case_ii1_low hm2 hA2 hA4 hpos hunit hs0 hcls1 hcls2 hcls4
            hA1eq hne hp1 hp2 hp3 hu1 hu2 hu3 hr1 hr2 hr3 hνeq hlow hrat2
        · exact c63_case_ii2_low hm2 hA2 hA4 hpos hunit hs0 hcls1 hcls2 hcls4
            hA1eq hd4 hd5 hne hp1 hp2 hp3 hp4 hp5 hu1 hu2 hu3 hu4 hu5
            hr1 hr2 hr3 hr4 hr5 hνeq hlow hrat3 he13_ne he23_zero




