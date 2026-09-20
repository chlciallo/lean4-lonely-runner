/-
Copyright (c) 2026 Research07 contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Research07 contributors
-/
import Research07.LRC7.Case5mTop
import Research07.LRC7.Case5mL9b
import Research07.LRC7.Case5mL10

/-!
# Paper §6.5 — `|A₁| = 3`, `|A₄| = 2` (Barajas–Serra)

For `A₁` a three-element `Finset ℕ` of `7`-adic units sharing the residue
class `s ∈ {1,2,4}` and `A₄` a two-element set of units in class `4s`,
some `7`-unit multiplier `λ` is `good7` on `A₁ ∪ A₄`.

## Route (paper §6.5)

* `lemma11` numbers `A₁ = {d₁,d₂,d₃}`; the four branches are
  (i) `l₁₃ > l₂₃ = l₁₂`, (ii.1) `l₁₃ = l₂₃` ratio `2`,
  (ii.2) `l₁₃ = l₂₃` ratio `3` with `r₁₃ = ±s` — each split by `h ≷ m`.
* Every branch produces a first `7`-unit `λ₁` with
  `(ℓ(q(λ₁A₁)) ≤ 3 ∧ ℓ(q(λ₁A₄)) ≤ 3) ∨ (ℓ(q(λ₁A₁)) ≤ 4 ∧ ℓ(q(λ₁A₄)) ≤ 2)`
  (paper eq. (14)) — this is the content of the branch lemmas.
* `c65_tail` then obtains a `ZMod 7` shift `t` from the cover-level
  finite facts `c65_cover33` / `c65_cover42` (a replacement for the
  lemma5/lemma6 normalisation) and realises it by a `Λ₀`-element via
  `exists_lambda0_of_shift`; `good7_mul` closes the multiplier.

Notable deviations/extensions relative to the paper text:
* (ii.2) `h < m`, `ν(e₄₅) = h`: the paper's `r(e₄₅) = r(e₁₃)` rename only
  covers `r₄₅ ∈ {±r₁₃}`.  We instead use the three anchor differences
  `e₁₃, e₃₂, e₂₁` whose residues are `r₁₃·{1,2,4}` (with the `d₄↔d₅` swap
  covering `{3,5,6}`): each gives a valid `lemma9_ii` (`j = 3`)
  application and `f = e₄₅ − e_anchor` has `ν(f) > h`, so the
  `Λ_{ν(f)}`–then–`lemma9` composition works for every `r₄₅`.
* (ii.2) `h < m`, `ν(e₄₅) < h`: `Λ_{ν(e₄₅)}` applied after `lemma9`
  shifts the `A₁`-digits by a shared constant plus a `{0,1}` carry (the
  `A₁` elements agree `mod 7^h`), giving `ℓ(A₁) ≤ 4`, `ℓ(A₄) ≤ 2`.
* (ii.1) `h = m` exceptional rescue: `e₃₄ = r·7^m` pure-top forces
  `ẽ = r−1` (resp. `r`) *exactly* via `qdig_eq_add_of_e_top`, so only
  `r = 5` is bad; the `×2` rescue yields `{1,3,5} ∪ {1,2}`.
-/

private instance : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩

/-! ### §0 Low-level plumbing (clones of private facts in sibling files) -/

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

/-- Equal `runit7` forces the `same` branch (nonzero second element). -/
private theorem rel_same' {u v : ℕ} (h : runit7 u = runit7 v) (hv : v ≠ 0) :
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
  rw [eMod7_zmod_cast, if_neg h1, if_neg h2]

/-- `(a % 7^{m+1}) / 7^m` and `a / 7^m` agree modulo `7`. -/
private theorem div_mod_pow_cast (a m : ℕ) :
    (((a % 7 ^ (m + 1)) / 7 ^ m : ℕ) : ZMod 7)
      = ((a / 7 ^ m : ℕ) : ZMod 7) := by
  rw [pow_succ', Nat.mod_mul_left_div_self,
    ZMod.natCast_eq_natCast_iff', Nat.mod_mod]

/-- `qdig7` of a wrapped residue equals the unwrapped digit cast. -/
private theorem qdig7_eMod_of (m a : ℕ) :
    qdig7 m (a % 7 ^ (m + 1)) = ((a / 7 ^ m : ℕ) : ZMod 7) := by
  rw [qdig7_eq_cast_div]
  exact div_mod_pow_cast a m

/-- Decompose `x % 7^{m+1}` as `q·7^m + f` with `q < 7`, `f < 7^m`. -/
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

/-- `e(x,y) = v·7^m` (same branch) also forces equal low parts. -/
private theorem eq_low_of_e_top {m x y : ℕ} {v : ZMod 7}
    (hrel : residueRelOf x y = residueRel.same)
    (he : eMod7 m x y = v.val * 7 ^ m) :
    x % 7 ^ m = y % 7 ^ m := by
  have hN : (0 : ℕ) < 7 ^ (m + 1) := Nat.pow_pos (by norm_num)
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
  have hmodm : ∀ z : ℕ, z % 7 ^ (m + 1) % 7 ^ m = z % 7 ^ m :=
    fun z => Nat.mod_mod_of_dvd z (Nat.pow_dvd_pow 7 (Nat.le_succ m))
  have hres := hmodeq
  rw [Nat.ModEq] at hres
  have hEq : x % 7 ^ m = y % 7 ^ m := by
    have h2 := congrArg (· % 7 ^ m) hres
    rw [hmodm, hmodm, hmodm, Nat.add_mul_mod_self_right, hmodm] at h2
    exact h2
  exact hEq

/-! ### §0.2 `ZMod 7`-cast of `eMod7`, divisibility, pure-top scaling -/

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

/- `e(cx, cy) ≡ c·e(x,y) (mod 7^{m+1})` whenever `runit7 c ≠ 0` —
the public `eMod7_smul` (Case5mL9) is used directly. -/

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

/-- `eMod7` respects `mod`-congruence of its arguments (with matching
`runit7`). -/
private theorem eMod7_congr {m x y x' y' : ℕ}
    (hx : x % 7 ^ (m + 1) = x' % 7 ^ (m + 1))
    (hy : y % 7 ^ (m + 1) = y' % 7 ^ (m + 1))
    (hrx : runit7 x = runit7 x') (hry : runit7 y = runit7 y') :
    eMod7 m x y = eMod7 m x' y' := by
  unfold eMod7
  rw [hx, hy, hrx, hry]

/-! ### §0.3 Level structure of residues -/

/-- **Block form**: `e ≡ r(e)·7^{ν(e)} (mod 7^{ν(e)+1})` for `e ≠ 0`. -/
private theorem nat_mod_pow_succ_of_padic {e h : ℕ} (he : e ≠ 0)
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
private theorem level_of_mod_block {w h s : ℕ}
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

/-- Difference of two level-`h` naturals reads `(r(u)−r(v))·7^h` mod
`7^{h+1}` (wrapped subtraction `u − v` inside the modulus). -/
private theorem sub_mod_block {u v h : ℕ} (hu : u ≠ 0) (hv : v ≠ 0)
    (huν : padicValNat 7 u = h) (hvν : padicValNat 7 v = h) :
    (u % 7 ^ (h + 1) + 7 ^ (h + 1) - v % 7 ^ (h + 1)) % 7 ^ (h + 1)
      = (runit7 u - runit7 v).val * 7 ^ h := by
  have hub := nat_mod_pow_succ_of_padic hu huν
  have hvb := nat_mod_pow_succ_of_padic hv hvν
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

/-- `(a + c − b) % P` depends only on `a % P`, `b % P` when `P ∣ c`
(and the subtraction does not truncate). -/
private theorem wrap_sub_mod_gen {a b c P : ℕ} (hP : 0 < P) (hc : P ∣ c)
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

/-! ### §0.4 `eMod7` congruence algebra on same-branch triples -/

/-- `(e(x,z) : ZMod N) = e(x,y) + e(y,z)` when all pairs are `same`. -/
private theorem eMod7_cast_add {m x y z : ℕ}
    (hxy : residueRelOf x y = residueRel.same)
    (hyz : residueRelOf y z = residueRel.same)
    (hxz : residueRelOf x z = residueRel.same) :
    ((eMod7 m x z : ℕ) : ZMod (7 ^ (m + 1)))
      = (eMod7 m x y : ZMod _) + (eMod7 m y z : ZMod _) := by
  rw [eMod7_zmod_cast_same hxz, eMod7_zmod_cast_same hxy,
    eMod7_zmod_cast_same hyz]
  ring

/-- As naturals: `e(x,z) = (e(x,y) + e(y,z)) % N`. -/
private theorem eMod7_add_eq {m x y z : ℕ}
    (hxy : residueRelOf x y = residueRel.same)
    (hyz : residueRelOf y z = residueRel.same)
    (hxz : residueRelOf x z = residueRel.same) :
    eMod7 m x z = (eMod7 m x y + eMod7 m y z) % 7 ^ (m + 1) := by
  have h := eMod7_cast_add (m := m) hxy hyz hxz
  rw [← Nat.cast_add] at h
  rw [ZMod.natCast_eq_natCast_iff'] at h
  have hlt : eMod7 m x z < 7 ^ (m + 1) := eMod7_lt _ _ _
  rwa [Nat.mod_eq_of_lt hlt] at h

/-- `(e(x,y) : ZMod N) = e(x,l) − e(y,l)` for `same` pairs. -/
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

/-- `e(y,x) = (N − e(x,y)) % N` for `same` pairs (both `0` or negated). -/
private theorem eMod7_neg_eq {m x y : ℕ}
    (hxy : residueRelOf x y = residueRel.same)
    (hyx : residueRelOf y x = residueRel.same) :
    eMod7 m y x = (7 ^ (m + 1) - eMod7 m x y) % 7 ^ (m + 1) := by
  have hcast : ((eMod7 m y x : ℕ) : ZMod (7 ^ (m + 1)))
      = ((7 ^ (m + 1) - eMod7 m x y : ℕ) : ZMod _) := by
    rw [eMod7_zmod_cast_same hyx]
    have hlt : eMod7 m x y < 7 ^ (m + 1) := eMod7_lt _ _ _
    rw [Nat.cast_sub (by omega : eMod7 m x y ≤ 7 ^ (m + 1)), ZMod.natCast_self,
      eMod7_zmod_cast_same hxy]
    ring
  rw [ZMod.natCast_eq_natCast_iff'] at hcast
  have hlt : eMod7 m y x < 7 ^ (m + 1) := eMod7_lt _ _ _
  rwa [Nat.mod_eq_of_lt hlt] at hcast

/-- The negated residue `N − e` (for `0 < e < N`, `ν(e) ≤ m`) has the
same level as `e` and unit `−r(e)`. -/
private theorem neg_resid_level {m e : ℕ} (he : e ≠ 0)
    (helt : e < 7 ^ (m + 1)) (hνm : padicValNat 7 e ≤ m) :
    padicValNat 7 (7 ^ (m + 1) - e) = padicValNat 7 e ∧
    runit7 (7 ^ (m + 1) - e) = - runit7 e := by
  set h := padicValNat 7 e with hh
  have hub := nat_mod_pow_succ_of_padic he rfl
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
      have hle : (e / 7 ^ (h + 1) + 1) * 7 ^ (h + 1)
          ≤ K * 7 ^ (h + 1) :=
        Nat.mul_le_mul_right _ (by omega)
      rw [Nat.add_mul, one_mul] at hle
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
    level_of_mod_block hmod (by omega : 0 < 7 - (runit7 e).val)
      (by omega : 7 - (runit7 e).val < 7)
  refine ⟨hνw, ?_⟩
  rw [hrw]
  rw [Nat.cast_sub (by omega : (runit7 e).val ≤ 7)]
  push_cast
  rw [show (7 : ZMod 7) = 0 from by decide, zero_sub,
    ZMod.natCast_zmod_val]

/-- `e(y,x)` has the same level and negated unit as `e(x,y)` (`same`
pairs). -/
private theorem enu7_neg {m x y : ℕ}
    (hxy : residueRelOf x y = residueRel.same)
    (hyx : residueRelOf y x = residueRel.same) :
    padicValNat 7 (eMod7 m y x) = padicValNat 7 (eMod7 m x y) ∧
    runit7 (eMod7 m y x) = - runit7 (eMod7 m x y) := by
  rw [eMod7_neg_eq hxy hyx]
  rcases eq_or_ne (eMod7 m x y) 0 with he | he
  · rw [he, Nat.sub_zero, Nat.mod_self]
    simp [runit7]
  · set e := eMod7 m x y
    have hlt : e < 7 ^ (m + 1) := eMod7_lt _ _ _
    have hνm : padicValNat 7 e ≤ m := by
      have hndvd : ¬ 7 ^ (m + 1) ∣ e := by
        intro hd
        exact he (Nat.eq_zero_of_dvd_of_lt hd hlt)
      by_contra hc
      push_neg at hc
      exact hndvd ((Nat.pow_dvd_iff_le_padicValNat (by norm_num) he).mpr hc)
    have hw : (7 ^ (m + 1) - e) % 7 ^ (m + 1) = 7 ^ (m + 1) - e := by
      rw [Nat.mod_eq_of_lt (by omega : 7 ^ (m + 1) - e < 7 ^ (m + 1))]
    rw [hw]
    exact neg_resid_level he hlt hνm

/-- `e(y,x)` has the same level as `e(x,y)` (`same` pairs). -/
private theorem enu7_sym {m x y : ℕ}
    (hxy : residueRelOf x y = residueRel.same)
    (hyx : residueRelOf y x = residueRel.same) :
    padicValNat 7 (eMod7 m y x) = padicValNat 7 (eMod7 m x y) :=
  (enu7_neg hxy hyx).1

/-- `e(y,x)` has negated unit (`same` pairs). -/
private theorem runit7_eMod7_neg {m x y : ℕ}
    (hxy : residueRelOf x y = residueRel.same)
    (hyx : residueRelOf y x = residueRel.same) :
    runit7 (eMod7 m y x) = - runit7 (eMod7 m x y) :=
  (enu7_neg hxy hyx).2

/-- **Block value of `e(x,y)`** through a common point `l` when both
`(x,l)`, `(y,l)` pairs have level `h ≤ m`: reads
`(r(e_{xl}) − r(e_{yl}))·7^h` mod `7^{h+1}`. -/
private theorem eMod7_sub_block {m x y l h : ℕ}
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
  rw [wrap_sub_mod_gen (Nat.pow_pos (by norm_num))
    (Nat.pow_dvd_pow 7 (by omega : h + 1 ≤ m + 1))
    (by have := eMod7_lt m y l; omega)]
  exact sub_mod_block hxl0 hyl0 hxlν hylν

/-- Distinct `r`'s through a common point give `e(x,y)` level `h` and
unit `r(e_{xl}) − r(e_{yl})`. -/
private theorem eMod7_level_of_runit_ne {m x y l h : ℕ}
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
  have hblk := eMod7_sub_block hxl hyl hxy hxl0 hyl0 hxlν hylν hm
  have hs : 0 < (runit7 (eMod7 m x l) - runit7 (eMod7 m y l)).val := by
    rcases Nat.eq_zero_or_pos
        (runit7 (eMod7 m x l) - runit7 (eMod7 m y l)).val with h0 | h0
    · exfalso
      rw [ZMod.val_eq_zero] at h0
      exact hr (sub_eq_zero.mp h0)
    · exact h0
  have hs7 : (runit7 (eMod7 m x l) - runit7 (eMod7 m y l)).val < 7 :=
    ZMod.val_lt _
  obtain ⟨hw0, hνw, hrw⟩ := level_of_mod_block hblk hs hs7
  rw [ZMod.natCast_zmod_val] at hrw
  exact ⟨hw0, hνw, hrw⟩

/-- Equal `r`'s through a common point force `e(x,y) = 0` or level
`> h` (the "collision" alternative). -/
private theorem eMod7_level_gt_of_runit_eq {m x y l h : ℕ}
    (hxl : residueRelOf x l = residueRel.same)
    (hyl : residueRelOf y l = residueRel.same)
    (hxy : residueRelOf x y = residueRel.same)
    (hxl0 : eMod7 m x l ≠ 0) (hyl0 : eMod7 m y l ≠ 0)
    (hxlν : padicValNat 7 (eMod7 m x l) = h)
    (hylν : padicValNat 7 (eMod7 m y l) = h) (hm : h ≤ m)
    (hr : runit7 (eMod7 m x l) = runit7 (eMod7 m y l)) :
    eMod7 m x y = 0 ∨ h < padicValNat 7 (eMod7 m x y) := by
  have hblk := eMod7_sub_block hxl hyl hxy hxl0 hyl0 hxlν hylν hm
  rw [hr, sub_self, ZMod.val_zero, zero_mul] at hblk
  rcases eq_or_ne (eMod7 m x y) 0 with h0 | h0
  · exact Or.inl h0
  · right
    have hdvd : 7 ^ (h + 1) ∣ eMod7 m x y := Nat.dvd_iff_mod_eq_zero.mpr hblk
    exact (Nat.pow_dvd_iff_le_padicValNat (by norm_num) h0).mp hdvd

/-- Level of a wrapped difference of two level-`h` naturals: when the
unit parts cancel, `(u − v) % N` is `0` or has level `> h`. -/
private theorem level_of_sub_gt {m u v h : ℕ} (hu : u ≠ 0) (hv : v ≠ 0)
    (huν : padicValNat 7 u = h) (hvν : padicValNat 7 v = h)
    (hlt : v < 7 ^ (m + 1)) (hhm : h < m)
    (hr : runit7 u = runit7 v) :
    (u + 7 ^ (m + 1) - v) % 7 ^ (m + 1) = 0 ∨
      h < padicValNat 7 ((u + 7 ^ (m + 1) - v) % 7 ^ (m + 1)) := by
  have hblk := sub_mod_block hu hv huν hvν
  rw [hr, sub_self, ZMod.val_zero, zero_mul] at hblk
  have hmod : (u + 7 ^ (m + 1) - v) % 7 ^ (h + 1)
      = (u % 7 ^ (h + 1) + 7 ^ (h + 1) - v % 7 ^ (h + 1)) % 7 ^ (h + 1) := by
    rw [wrap_sub_mod_gen (Nat.pow_pos (by norm_num))
      (Nat.pow_dvd_pow 7 (by omega : h + 1 ≤ m + 1)) (by omega)]
  rw [← hmod] at hblk
  rcases eq_or_ne ((u + 7 ^ (m + 1) - v) % 7 ^ (m + 1)) 0 with h0 | h0
  · exact Or.inl h0
  · right
    have hmod2 : (u + 7 ^ (m + 1) - v) % 7 ^ (m + 1) % 7 ^ (h + 1)
        = (u + 7 ^ (m + 1) - v) % 7 ^ (h + 1) :=
      Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 7 (by omega : h + 1 ≤ m + 1))
    have hdvd : 7 ^ (h + 1) ∣ (u + 7 ^ (m + 1) - v) % 7 ^ (m + 1) :=
      Nat.dvd_iff_mod_eq_zero.mpr (by rw [hmod2]; exact hblk)
    exact (Nat.pow_dvd_iff_le_padicValNat (by norm_num) h0).mp hdvd

/-! ### §1 Digit arithmetic of scalar multiples and residue sums -/

/-- **Wrapped-subtraction digit formula** (clone of `qdig7_sub_resid`):
`q(a′ + N − b′) = q(a) − q(b) − borrow`, where `a′ = a % N`, `b′ = b % N`. -/
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
  have hle : b % 7 ^ (m + 1) ≤ a % 7 ^ (m + 1) + 7 ^ (m + 1) := by
    have hbl := Nat.mod_lt b (Nat.pow_pos (by norm_num) : 0 < 7 ^ (m + 1))
    omega
  by_cases hb : f1 < f2
  · have hq2le : q2 * 7 ^ m ≤ q1 * 7 ^ m + 6 * 7 ^ m := by
      have h := Nat.mul_le_mul_right (7 ^ m) (by omega : q2 ≤ q1 + 6)
      rwa [Nat.add_mul] at h
    have hcalc : a % 7 ^ (m + 1) + 7 ^ (m + 1) - b % 7 ^ (m + 1)
        = (q1 + 6 - q2) * 7 ^ m + (f1 + 7 ^ m - f2) := by
      rw [Nat.sub_eq_iff_eq_add hle, hX, hY, hNe, Nat.sub_mul, Nat.add_mul]
      omega
    rw [hcalc, mul_pow_add_div (by omega : f1 + 7 ^ m - f2 < 7 ^ m)]
    have hq : ((q1 + 6 - q2 : ℕ) : ZMod 7) = (q1 : ZMod 7) - q2 - 1 := by
      rw [natCast_sub_add (by omega : q2 ≤ q1 + 6)]
      have h6 : ((6 : ℕ) : ZMod 7) = -1 := by decide
      rw [h6]
      ring
    rw [hq, hqA, hqB]
    rw [if_pos (by rwa [hf1e, hf2e] : a % 7 ^ m < b % 7 ^ m)]
  · have hge : f2 ≤ f1 := Nat.le_of_not_gt hb
    have hq2le : q2 * 7 ^ m ≤ q1 * 7 ^ m + 7 * 7 ^ m := by
      have h := Nat.mul_le_mul_right (7 ^ m) (by omega : q2 ≤ q1 + 7)
      rwa [Nat.add_mul] at h
    have hcalc : a % 7 ^ (m + 1) + 7 ^ (m + 1) - b % 7 ^ (m + 1)
        = (q1 + 7 - q2) * 7 ^ m + (f1 - f2) := by
      rw [Nat.sub_eq_iff_eq_add hle, hX, hY, hNe, Nat.sub_mul, Nat.add_mul]
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

/-- **Same-branch `eMod7` digit formula**: `q(e(x,y)) = q(x) − q(y) − borrow`
with `borrow = 1` iff `x % 7^m < y % 7^m`. -/
private theorem qdig7_eMod7_same_eq {m x y : ℕ}
    (hrel : residueRelOf x y = residueRel.same) :
    qdig7 m (eMod7 m x y)
      = qdig7 m x - qdig7 m y
        - if x % 7 ^ m < y % 7 ^ m then (1 : ZMod 7) else 0 := by
  rw [eMod7_same_eq hrel, qdig7_congr (Nat.mod_mod _ _)]
  exact qdig7_sub_resid

/-- The leading digit of `A·7^m + r` taken `mod 7^{m+1}` when `r < 7^m`. -/
private theorem qdig7_block {m A r : ℕ} (hr : r < 7 ^ m) :
    qdig7 m (A * 7 ^ m + r) = ((A % 7 : ℕ) : ZMod 7) := by
  have hP : 0 < 7 ^ m := Nat.pow_pos (by norm_num)
  have hNe : (7 : ℕ) ^ (m + 1) = 7 * 7 ^ m := pow_succ' 7 m
  have hA7 : A % 7 < 7 := Nat.mod_lt A (by norm_num)
  have hle : (A % 7) * 7 ^ m ≤ 6 * 7 ^ m :=
    Nat.mul_le_mul_right _ (Nat.le_of_lt_succ hA7)
  have hlt : (A % 7) * 7 ^ m + r < 7 ^ (m + 1) := by
    rw [hNe]
    omega
  have hmod : (A * 7 ^ m + r) % 7 ^ (m + 1) = (A % 7) * 7 ^ m + r := by
    have hsplit : A * 7 ^ m + r
        = ((A % 7) * 7 ^ m + r) + (7 * 7 ^ m) * (A / 7) := by
      have h := Nat.div_add_mod A 7
      calc A * 7 ^ m + r
          = (7 * (A / 7) + A % 7) * 7 ^ m + r := by rw [h]
        _ = ((A % 7) * 7 ^ m + r) + (7 * 7 ^ m) * (A / 7) := by ring
    rw [hNe, hsplit, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt (by rw [hNe] at hlt; exact hlt)
  rw [qdig7_congr (hmod.trans (Nat.mod_eq_of_lt hlt).symm),
    qdig7_eq_cast_div, mul_pow_add_div hr]

/-- **Exact carry formula**: `q(k·x) = k·q(x) + c` with
`c = (k·(x % 7^m)) / 7^m` (and `c < k` when `k > 0`). -/
private theorem qdig7_smul_eq {m k x : ℕ} (hk : 0 < k) :
    qdig7 m (k * x) = (k : ZMod 7) * qdig7 m x
      + (((k * (x % 7 ^ m)) / 7 ^ m : ℕ) : ZMod 7) := by
  obtain ⟨q, f, hX, hq, hf⟩ := residue_decomp (m := m) (x := x)
  have hP : 0 < 7 ^ m := Nat.pow_pos (by norm_num)
  have hfx : x % 7 ^ m = f := by
    have hmod : x % 7 ^ (m + 1) % 7 ^ m = x % 7 ^ m :=
      Nat.mod_mod_of_dvd x (Nat.pow_dvd_pow 7 (Nat.le_succ m))
    rw [← hmod, hX, add_comm (q * 7 ^ m) f,
      Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hf]
  have hqx : qdig7 m x = (q : ZMod 7) := by
    unfold qdig7
    rw [hX, mul_pow_add_div hf]
  have hmod1 : (k * x) % 7 ^ (m + 1)
      = (k * (x % 7 ^ (m + 1))) % 7 ^ (m + 1) := by
    rw [Nat.mul_mod, Nat.mul_mod k (x % 7 ^ (m + 1)) _, Nat.mod_mod]
  have hsplit : k * (x % 7 ^ (m + 1))
      = (k * q + k * f / 7 ^ m) * 7 ^ m + k * f % 7 ^ m := by
    rw [hX]
    have h := Nat.div_add_mod (k * f) (7 ^ m)
    calc k * (q * 7 ^ m + f)
        = k * q * 7 ^ m + k * f := by ring
      _ = k * q * 7 ^ m
            + (7 ^ m * ((k * f) / 7 ^ m) + (k * f) % 7 ^ m) := by
          rw [h]
      _ = (k * q + k * f / 7 ^ m) * 7 ^ m + k * f % 7 ^ m := by ring
  have hqx' : qdig7 m (k * x)
      = (((k * q + k * f / 7 ^ m) % 7 : ℕ) : ZMod 7) := by
    rw [qdig7_congr hmod1, hsplit]
    exact qdig7_block (Nat.mod_lt _ hP)
  rw [hqx', hqx, hfx]
  have hcast : (((k * q + k * f / 7 ^ m) % 7 : ℕ) : ZMod 7)
      = ((k * q + k * f / 7 ^ m : ℕ) : ZMod 7) := by
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_mod]
  rw [hcast, Nat.cast_add, Nat.cast_mul]

/-- The digit of a sum of residues: `q((u+v) % N) − q(u) − q(v) ∈ {0,1}`
(the low-part carry `⌊(fu+fv)/7^m⌋`). -/
private theorem qdig7_add_016 {m u v : ℕ} :
    qdig7 m ((u + v) % 7 ^ (m + 1)) - qdig7 m u - qdig7 m v
      ∈ ({0, 1} : Finset (ZMod 7)) := by
  obtain ⟨q1, f1, hX, hq1, hf1⟩ := residue_decomp (m := m) (x := u)
  obtain ⟨q2, f2, hY, hq2, hf2⟩ := residue_decomp (m := m) (x := v)
  have hP : 0 < 7 ^ m := Nat.pow_pos (by norm_num)
  have hqu : qdig7 m u = (q1 : ZMod 7) := by
    unfold qdig7
    rw [hX, mul_pow_add_div hf1]
  have hqv : qdig7 m v = (q2 : ZMod 7) := by
    unfold qdig7
    rw [hY, mul_pow_add_div hf2]
  have hsum : (u + v) % 7 ^ (m + 1)
      = ((q1 + q2 + (f1 + f2) / 7 ^ m) * 7 ^ m + (f1 + f2) % 7 ^ m)
          % 7 ^ (m + 1) := by
    have hmod : (u + v) % 7 ^ (m + 1)
        = ((u % 7 ^ (m + 1)) + (v % 7 ^ (m + 1))) % 7 ^ (m + 1) :=
      Nat.add_mod u v _
    rw [hmod, hX, hY]
    congr 1
    have h := Nat.div_add_mod (f1 + f2) (7 ^ m)
    calc q1 * 7 ^ m + f1 + (q2 * 7 ^ m + f2)
        = (q1 + q2) * 7 ^ m + (f1 + f2) := by ring
      _ = (q1 + q2) * 7 ^ m
            + (7 ^ m * ((f1 + f2) / 7 ^ m) + (f1 + f2) % 7 ^ m) := by
          rw [h]
      _ = (q1 + q2 + (f1 + f2) / 7 ^ m) * 7 ^ m + (f1 + f2) % 7 ^ m := by
          ring
  have hc : (f1 + f2) / 7 ^ m < 2 := by
    rw [Nat.div_lt_iff_lt_mul hP]
    omega
  have hq : qdig7 m ((u + v) % 7 ^ (m + 1))
      = (((q1 + q2 + (f1 + f2) / 7 ^ m) % 7 : ℕ) : ZMod 7) := by
    rw [qdig7_congr (Nat.mod_mod _ _), qdig7_congr hsum]
    exact qdig7_block (Nat.mod_lt _ hP)
  rw [hq, hqu, hqv]
  have hcast2 : (((q1 + q2 + (f1 + f2) / 7 ^ m) % 7 : ℕ) : ZMod 7)
      = ((q1 + q2 + (f1 + f2) / 7 ^ m : ℕ) : ZMod 7) := by
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_mod]
  rw [hcast2, Nat.cast_add, Nat.cast_add]
  have hcast : (((f1 + f2) / 7 ^ m : ℕ) : ZMod 7)
      ∈ ({0, 1} : Finset (ZMod 7)) := by
    interval_cases ((f1 + f2) / 7 ^ m) <;> decide
  simp only [Finset.mem_insert, Finset.mem_singleton] at hcast ⊢
  rcases hcast with h0 | h1
  · left
    rw [h0]
    ring
  · right
    rw [h1]
    ring

/-- A `Λ_j`-multiplier preserves a `7^{j+1}`-divisible number `mod 7^{m+1}`
(the added term is a multiple of `7^{m+1}`). -/
private theorem multLow_low' {m j k w : ℕ} (hjm : j ≤ m)
    (hw : 7 ^ (j + 1) ∣ w) :
    ((1 + k * 7 ^ (m - j)) * w) % 7 ^ (m + 1) = w % 7 ^ (m + 1) := by
  obtain ⟨u, rfl⟩ := hw
  rw [add_mul, one_mul]
  have hP : k * 7 ^ (m - j) * (7 ^ (j + 1) * u)
      = 7 ^ (m + 1) * (k * u) := by
    have e : k * 7 ^ (m - j) * (7 ^ (j + 1) * u)
        = k * u * (7 ^ (m - j) * 7 ^ (j + 1)) := by ring
    rw [e, ← pow_add, show m - j + (j + 1) = m + 1 by omega]
    ring
  rw [hP, Nat.add_mul_mod_self_left]

/-- `q`-digit preserved by `Λ_j` on `7^{j+1}`-divisible elements. -/
private theorem qdig7_multLow_low' {m j k w : ℕ} (hjm : j ≤ m)
    (hw : 7 ^ (j + 1) ∣ w) :
    qdig7 m ((1 + k * 7 ^ (m - j)) * w) = qdig7 m w :=
  qdig7_congr (multLow_low' hjm hw)

/-- Two-point `apLen` upper bound: `{a,b}` is covered by the forward
`a−b` arc or the `b−a` arc. -/
private theorem apLen_two_le (a b : ZMod 7) :
    apLen ({a, b} : Finset (ZMod 7))
      ≤ min ((a - b).val + 1) ((b - a).val + 1) := by
  have h1 : ({a, b} : Finset (ZMod 7)) ⊆ cycIv b ((a - b).val + 1) := by
    intro x hx
    rw [mem_cycIv]
    rcases Finset.mem_insert.mp hx with hxa | hxb
    · rw [hxa]
      omega
    · rw [Finset.mem_singleton] at hxb
      rw [hxb, sub_self, ZMod.val_zero]
      omega
  have h2 : ({a, b} : Finset (ZMod 7)) ⊆ cycIv a ((b - a).val + 1) := by
    intro x hx
    rw [mem_cycIv]
    rcases Finset.mem_insert.mp hx with hxa | hxb
    · rw [hxa, sub_self, ZMod.val_zero]
      omega
    · rw [Finset.mem_singleton] at hxb
      rw [hxb]
      omega
  have hL1 : (a - b).val + 1 ≤ 7 := by
    have := ZMod.val_lt (a - b)
    omega
  have hL2 : (b - a).val + 1 ≤ 7 := by
    have := ZMod.val_lt (b - a)
    omega
  exact le_min ((apLen_le_iff _ _ hL1).mpr ⟨b, h1⟩)
    ((apLen_le_iff _ _ hL2).mpr ⟨a, h2⟩)

/-- Pointwise lower bound: a cyclic interval covering `{a,b}` has length
at least `min ((a−b)+1, (b−a)+1)`. -/
private theorem apLen_two_lb {a b i : ZMod 7} {L : ℕ}
    (ha : a ∈ cycIv i L) (hb : b ∈ cycIv i L) :
    min ((a - b).val + 1) ((b - a).val + 1) ≤ L := by
  unfold cycIv at ha hb
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  by_contra hcon
  push_neg at hcon
  -- `L < min` ⇒ `L + 1 ≤ min` ⇒ both differences are `< min − 1`,
  -- which the finite check below rules out.
  have hL : L + 1 ≤ min ((a - b).val + 1) ((b - a).val + 1) := hcon
  have key : ∀ a b i : ZMod 7,
      (a - i).val + 1 < min ((a - b).val + 1) ((b - a).val + 1) →
      (b - i).val + 1 < min ((a - b).val + 1) ((b - a).val + 1) →
      False := by decide
  exact key a b i (by omega) (by omega)

/-- Two-point `apLen` lower bound. -/
private theorem apLen_two_ge (a b : ZMod 7) :
    min ((a - b).val + 1) ((b - a).val + 1)
      ≤ apLen ({a, b} : Finset (ZMod 7)) := by
  have h7 : apLen ({a, b} : Finset (ZMod 7)) ≤ 7 := apLen_le_seven _
  obtain ⟨i, hi⟩ := (apLen_le_iff _ _ h7).mp (le_refl _)
  exact apLen_two_lb (hi (Finset.mem_insert_self _ _))
    (hi (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self _))))

/-- `apLen {a,b} ≤ 3` when the difference lies in `{0,±1,±2}`. -/
private theorem apLen_two_le3 {a b : ZMod 7}
    (h : (a - b) ∈ ({0, 1, 2, 5, 6} : Finset (ZMod 7))) :
    apLen ({a, b} : Finset (ZMod 7)) ≤ 3 := by
  have hle := apLen_two_le a b
  have hkey : ∀ d : ZMod 7, d ∈ ({0, 1, 2, 5, 6} : Finset (ZMod 7)) →
      min (d.val + 1) ((-d).val + 1) ≤ 3 := by decide
  have hba : (b - a : ZMod 7) = -(a - b) := by ring
  rw [hba] at hle
  exact le_trans hle (hkey _ h)

/-- `apLen {a,b} ≤ 2` when the difference lies in `{0,±1}`. -/
private theorem apLen_two_le2 {a b : ZMod 7}
    (h : (a - b) ∈ ({0, 1, 6} : Finset (ZMod 7))) :
    apLen ({a, b} : Finset (ZMod 7)) ≤ 2 := by
  have hle := apLen_two_le a b
  have hkey : ∀ d : ZMod 7, d ∈ ({0, 1, 6} : Finset (ZMod 7)) →
      min (d.val + 1) ((-d).val + 1) ≤ 2 := by decide
  have hba : (b - a : ZMod 7) = -(a - b) := by ring
  rw [hba] at hle
  exact le_trans hle (hkey _ h)

/-- `apLen {a,b} ≥ 4` when the difference lies in `{±3} = {3,4}`. -/
private theorem apLen_two_ge4 {a b : ZMod 7}
    (h : (a - b) ∈ ({3, 4} : Finset (ZMod 7))) :
    4 ≤ apLen ({a, b} : Finset (ZMod 7)) := by
  have hge := apLen_two_ge a b
  have hkey : ∀ d : ZMod 7, d ∈ ({3, 4} : Finset (ZMod 7)) →
      4 ≤ min (d.val + 1) ((-d).val + 1) := by decide
  have hba : (b - a : ZMod 7) = -(a - b) := by ring
  rw [hba] at hge
  exact le_trans (hkey _ h) hge

/-! ### §2 The `(3,3)`/`(4,2)` finite covers and the shared tail -/

/-- The `(3,3)` cover fact (verified by Python enumeration over all `49`
start pairs and independently all `7` values of `c` with `k ∈ {0,1,2}`
sufficing): after the normalizing shift putting `A₁`'s window at `1`, some
final `Λ₀`-shift `k` moves both windows off `{0,6}`. -/
private theorem c65_cover33 :
    ∀ c : ZMod 7, ∃ k : ZMod 7,
      avoids06 (cycIv (1 + k) 3 ∪ cycIv (c + 4 * k) 3) := by decide

/-- The `(4,2)` cover fact. -/
private theorem c65_cover42 :
    ∀ c : ZMod 7, ∃ k : ZMod 7,
      avoids06 (cycIv (1 + k) 4 ∪ cycIv (c + 4 * k) 2) := by decide

/-- **The shared tail**: after a first `7`-unit multiplier `λ₁`, if
`q(λ₁A₁) ⊆ cycIv i₁ l₁` and `q(λ₁A₄) ⊆ cycIv i₄ l₄`, and the cover fact for
`(l₁, l₄)` holds, a final `Λ₀` multiplier finishes `good7`. -/
private theorem case65_tail {m : ℕ} (hm : 0 < m) {A1 A4 : Finset ℕ}
    (hpos : ∀ d ∈ A1 ∪ A4, 0 < d)
    (hunit : ∀ d ∈ A1 ∪ A4, padicValNat 7 d = 0)
    {s : ZMod 7} (hs : s ≠ 0)
    (hcls1 : ∀ d ∈ A1, runit7 d = s)
    (hcls4 : ∀ d ∈ A4, runit7 d = 4 * s)
    {lam₁ : ℕ} (hlam₁ : ¬ 7 ∣ lam₁)
    {l1 l4 : ℕ} {i1 i4 : ZMod 7}
    (hsub1 : ((A1.image fun d => lam₁ * d).image (qdig7 m))
      ⊆ cycIv i1 l1)
    (hsub4 : ((A4.image fun d => lam₁ * d).image (qdig7 m))
      ⊆ cycIv i4 l4)
    (hcov : ∀ c : ZMod 7, ∃ k : ZMod 7,
      avoids06 (cycIv (1 + k) l1 ∪ cycIv (c + 4 * k) l4)) :
    ∃ lam : ℕ, ¬ 7 ∣ lam ∧ good7 m lam (A1 ∪ A4) := by
  classical
  set X1 := (A1.image fun d => lam₁ * d).image (qdig7 m) with hX1
  set X4 := (A4.image fun d => lam₁ * d).image (qdig7 m) with hX4
  set t : ZMod 7 := 1 - i1 with ht
  set Y1 := X1.image (· + t) with hY1
  set Y4 := X4.image (· + 4 * t) with hY4
  set c : ZMod 7 := i4 + 4 * t with hc
  have hcov1 : Y1 ⊆ cycIv 1 l1 := by
    intro x hx
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hx
    rw [mem_cycIv]
    have hqsub := hsub1 hq
    rw [mem_cycIv] at hqsub
    have heq : q + t - 1 = q - i1 := by rw [ht]; ring
    rw [heq]; exact hqsub
  have hcov4 : Y4 ⊆ cycIv c l4 := by
    intro x hx
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hx
    rw [mem_cycIv]
    have hqsub := hsub4 hq
    rw [mem_cycIv] at hqsub
    have heq : q + 4 * t - c = q - i4 := by rw [hc]; ring
    rw [heq]; exact hqsub
  obtain ⟨k, havoid⟩ := hcov c
  rw [avoids06_union] at havoid
  obtain ⟨hav1, hav4⟩ := havoid
  have havY1 : avoids06 (Y1.image (· + k)) :=
    avoids06_of_subset_shift hcov1 hav1
  have havY4 : avoids06 (Y4.image (· + 4 * k)) :=
    avoids06_of_subset_shift hcov4 hav4
  -- assemble the `exists_lambda0_of_shift` avoid-set on `B = λ₁·(A₁∪A₄)`
  set B := (A1 ∪ A4).image (fun d => lam₁ * d) with hB
  set s' : ZMod 7 := runit7 lam₁ * s with hs'
  have hlam₁0 : lam₁ ≠ 0 := fun hh => hlam₁ (hh ▸ dvd_zero _)
  have hrl1 : runit7 lam₁ ≠ 0 := runit7_ne_zero (Nat.pos_of_ne_zero hlam₁0)
  have hs'0 : s' ≠ 0 := mul_ne_zero hrl1 hs
  have hunitB : ∀ d ∈ B, padicValNat 7 d = 0 := by
    intro d hd
    obtain ⟨d₀, hd₀, rfl⟩ := Finset.mem_image.mp hd
    rw [padicValNat_mul_seven hlam₁ (ne_of_gt (hpos d₀ hd₀))]
    exact hunit d₀ hd₀
  have hclsB : ∀ d ∈ B, runit7 d ∈ ({s', 2 * s', 4 * s'} : Finset (ZMod 7)) := by
    intro d hd
    obtain ⟨d₀, hd₀, rfl⟩ := Finset.mem_image.mp hd
    rw [runit7_mul]
    rcases Finset.mem_union.mp hd₀ with hd₁ | hd₄
    · rw [hcls1 d₀ hd₁]
      exact Finset.mem_insert_self _ _
    · rw [hcls4 d₀ hd₄]
      have h4 : runit7 lam₁ * (4 * s) = 4 * s' := by rw [hs']; ring
      rw [h4]
      simp
  have hfilt1 : (B.filter fun d => runit7 d = s').image (qdig7 m) = X1 := by
    have hf : B.filter (fun d => runit7 d = s')
        = A1.image (fun d => lam₁ * d) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨hBx, hr⟩
        obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hBx
        rw [runit7_mul, hs'] at hr
        have hrd : runit7 d = s := mul_left_cancel₀ hrl1 hr
        rcases Finset.mem_union.mp hd with hd₁ | hd₄
        · exact ⟨d, hd₁, rfl⟩
        · rw [hcls4 d hd₄] at hrd
          have hz : (3 : ZMod 7) * s = 0 := by linear_combination hrd
          rcases mul_eq_zero.mp hz with h3 | h0
          · exact absurd h3 (by decide)
          · exact absurd h0 hs
      · rintro ⟨d, hd₁, rfl⟩
        exact ⟨Finset.mem_image.mpr
            ⟨d, Finset.mem_union_left _ hd₁, rfl⟩,
          by rw [runit7_mul, hcls1 d hd₁, hs']⟩
    rw [hf]
  have hfilt2 : (B.filter fun d => runit7 d = 2 * s').image (qdig7 m)
      = (∅ : Finset (ZMod 7)) := by
    have hf : B.filter (fun d => runit7 d = 2 * s') = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro x hxB hxr
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hxB
      rw [runit7_mul, hs'] at hxr
      have hrd : runit7 d = 2 * s := by
        have hr' : runit7 lam₁ * runit7 d = runit7 lam₁ * (2 * s) := by
          rw [hxr]; ring
        exact mul_left_cancel₀ hrl1 hr'
      rcases Finset.mem_union.mp hd with hd₁ | hd₄
      · rw [hcls1 d hd₁] at hrd
        have hz : (1 : ZMod 7) * s = 0 := by linear_combination -hrd
        rcases mul_eq_zero.mp hz with h1 | h0
        · exact absurd h1 (by decide)
        · exact hs h0
      · rw [hcls4 d hd₄] at hrd
        have hz : (2 : ZMod 7) * s = 0 := by linear_combination hrd
        rcases mul_eq_zero.mp hz with h2 | h0
        · exact absurd h2 (by decide)
        · exact hs h0
    rw [hf, Finset.image_empty]
  have hfilt4 : (B.filter fun d => runit7 d = 4 * s').image (qdig7 m)
      = X4 := by
    have hf : B.filter (fun d => runit7 d = 4 * s')
        = A4.image (fun d => lam₁ * d) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨hBx, hr⟩
        obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hBx
        rw [runit7_mul, hs'] at hr
        have hrd : runit7 d = 4 * s := by
          have hr' : runit7 lam₁ * runit7 d = runit7 lam₁ * (4 * s) := by
            rw [hr]; ring
          exact mul_left_cancel₀ hrl1 hr'
        rcases Finset.mem_union.mp hd with hd₁ | hd₄
        · rw [hcls1 d hd₁] at hrd
          have hz : (3 : ZMod 7) * s = 0 := by linear_combination -hrd
          rcases mul_eq_zero.mp hz with h3 | h0
          · exact absurd h3 (by decide)
          · exact absurd h0 hs
        · exact ⟨d, hd₄, rfl⟩
      · rintro ⟨d, hd₄, rfl⟩
        exact ⟨Finset.mem_image.mpr
            ⟨d, Finset.mem_union_right _ hd₄, rfl⟩,
          by rw [runit7_mul, hcls4 d hd₄, hs']; ring⟩
    rw [hf]
  have e1 : X1.image (· + (t + k)) = Y1.image (· + k) := by
    rw [hY1]
    conv_rhs => rw [Finset.image_image]
    apply Finset.image_congr
    intro x _
    show x + (t + k) = x + t + k
    ring
  have e4 : X4.image (· + 4 * (t + k)) = Y4.image (· + 4 * k) := by
    rw [hY4]
    conv_rhs => rw [Finset.image_image]
    apply Finset.image_congr
    intro x _
    show x + 4 * (t + k) = x + 4 * t + 4 * k
    ring
  have hunion :
      ((B.filter fun d => runit7 d = s').image (qdig7 m)).image (· + (t + k))
        ∪ ((B.filter fun d => runit7 d = 2 * s').image (qdig7 m)).image
          (· + 2 * (t + k))
        ∪ ((B.filter fun d => runit7 d = 4 * s').image (qdig7 m)).image
          (· + 4 * (t + k))
        = Y1.image (· + k) ∪ Y4.image (· + 4 * k) := by
    rw [hfilt1, hfilt2, hfilt4, Finset.image_empty, Finset.union_empty]
    rw [e1, e4]
  have havB : avoids06 (Y1.image (· + k) ∪ Y4.image (· + 4 * k)) :=
    avoids06_union.mpr ⟨havY1, havY4⟩
  obtain ⟨lam0, hlam0mem, hgood0⟩ :=
    exists_lambda0_of_shift hm hs'0 hunitB hclsB (t + k)
      (hunion.symm ▸ havB)
  refine ⟨lam0 * lam₁,
    Nat.prime_seven.not_dvd_mul (not_dvd_of_mem_multLow7_zero hm hlam0mem)
      hlam₁, ?_⟩
  exact good7_mul hgood0

/-! ### §3 The `×2`/`×3` rescue for `{0,6}`-difference pairs -/

/-- Two-point sets always have `apLen ≤ 4`. -/
private theorem apLen_two_le4 (a b : ZMod 7) :
    apLen ({a, b} : Finset (ZMod 7)) ≤ 4 := by
  have hle := apLen_two_le a b
  have hkey : ∀ d : ZMod 7,
      min (d.val + 1) ((-d).val + 1) ≤ 4 := by decide
  have hba : (b - a : ZMod 7) = -(a - b) := by ring
  rw [hba] at hle
  exact le_trans hle (hkey _)

/-- **×2 rescue, difference form** (paper §6.5 rescue): for a same-class
pair `b₁,b₂` whose difference digit satisfies `q(e(b₁,b₂)) ∈ {0,6}`, the
doubled digit difference lies in `{0,±1,±2}`.  The `{0,6}` condition forces
`q₁ − q₂ ∈ {0,±1}` together with the borrow/low-part anticorrelation
(`q₁−q₂ = 1 ⇒ f₁ < f₂`, `q₁−q₂ = −1 ⇒ f₁ ≥ f₂`); the doubled carry
`cᵢ = ⌊2fᵢ/7^m⌋ ∈ {0,1}` then moves the same way. -/
private theorem qdig7_smul2_diff06 {m : ℕ} {b1 b2 : ℕ}
    (hsame : residueRelOf b1 b2 = residueRel.same)
    (he : qdig7 m (eMod7 m b1 b2) ∈ ({0, 6} : Finset (ZMod 7))) :
    qdig7 m (2 * b1) - qdig7 m (2 * b2)
      ∈ ({0, 1, 2, 5, 6} : Finset (ZMod 7)) := by
  have hP : 0 < 7 ^ m := Nat.pow_pos (by norm_num)
  have hqd := qdig7_eMod7_same_eq (m := m) hsame
  set q1 := qdig7 m b1 with hq1def
  set q2 := qdig7 m b2 with hq2def
  generalize hc1 : (2 * (b1 % 7 ^ m)) / 7 ^ m = c1
  generalize hc2 : (2 * (b2 % 7 ^ m)) / 7 ^ m = c2
  have hq2b1 : qdig7 m (2 * b1) = (2 : ZMod 7) * q1 + (c1 : ZMod 7) := by
    have h := qdig7_smul_eq (m := m) (k := 2) (x := b1) (by norm_num : 0 < 2)
    rw [hc1] at h
    exact h
  have hq2b2 : qdig7 m (2 * b2) = (2 : ZMod 7) * q2 + (c2 : ZMod 7) := by
    have h := qdig7_smul_eq (m := m) (k := 2) (x := b2) (by norm_num : 0 < 2)
    rw [hc2] at h
    exact h
  rw [hq2b1, hq2b2]
  -- `q1 − q2 = q(e) + borrow`, so `q1 − q2 ∈ {0,1,6}`
  have hdiff : q1 - q2 = qdig7 m (eMod7 m b1 b2)
      + (if b1 % 7 ^ m < b2 % 7 ^ m then (1 : ZMod 7) else 0) := by
    rw [hqd]; ring
  have hbor : q1 - q2 ∈ ({0, 1, 6} : Finset (ZMod 7)) := by
    rw [hdiff]
    have hb : (if b1 % 7 ^ m < b2 % 7 ^ m then (1 : ZMod 7) else 0)
        ∈ ({0, 1} : Finset (ZMod 7)) := by
      by_cases h' : b1 % 7 ^ m < b2 % 7 ^ m <;> simp [h']
    have hsub : ∀ x y : ZMod 7, x ∈ ({0, 6} : Finset (ZMod 7)) →
        y ∈ ({0, 1} : Finset (ZMod 7)) →
        x + y ∈ ({0, 1, 6} : Finset (ZMod 7)) := by decide
    exact hsub _ _ he hb
  -- carry bounds
  have hc1b : c1 < 2 := by
    rw [← hc1, Nat.div_lt_iff_lt_mul hP]
    have := Nat.mod_lt b1 hP
    omega
  have hc2b : c2 < 2 := by
    rw [← hc2, Nat.div_lt_iff_lt_mul hP]
    have := Nat.mod_lt b2 hP
    omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hbor
  -- split on `q1 − q2`
  have hd : (2 : ZMod 7) * q1 + (c1 : ZMod 7)
        - ((2 : ZMod 7) * q2 + (c2 : ZMod 7))
      = 2 * (q1 - q2) + ((c1 : ZMod 7) - c2) := by ring
  rw [hd]
  rcases hbor with h0 | h1 | h6
  · -- `q1 − q2 = 0`: `c1 − c2 ∈ {0,±1}` is enough.
    have hcc : ((c1 : ZMod 7) - c2) ∈ ({0, 1, 6} : Finset (ZMod 7)) := by
      interval_cases c1 <;> interval_cases c2 <;> decide
    rw [h0]
    have hsub : ∀ x : ZMod 7, x ∈ ({0, 1, 6} : Finset (ZMod 7)) →
        x ∈ ({0, 1, 2, 5, 6} : Finset (ZMod 7)) := by decide
    have heq : (2 : ZMod 7) * 0 + ((c1 : ZMod 7) - c2)
        = (c1 : ZMod 7) - c2 := by ring
    rw [heq]
    exact hsub _ hcc
  · -- `q1 − q2 = 1`: borrow `= 1` so `f1 < f2` and `c1 ≤ c2`.
    have hqe : (1 : ZMod 7)
        - (if b1 % 7 ^ m < b2 % 7 ^ m then (1 : ZMod 7) else 0)
        ∈ ({0, 6} : Finset (ZMod 7)) := by
      have := he
      rw [hqd, h1] at this
      exact this
    have hflt : b1 % 7 ^ m < b2 % 7 ^ m := by
      by_cases hb : b1 % 7 ^ m < b2 % 7 ^ m
      · exact hb
      · rw [if_neg hb] at hqe
        simp only [sub_zero] at hqe
        exact absurd hqe (by decide)
    have hcc : c1 ≤ c2 := by
      rw [← hc1, ← hc2]
      exact Nat.div_le_div_right
        (Nat.mul_le_mul_left 2 (Nat.le_of_lt hflt))
    have hccz : ((c1 : ZMod 7) - c2) ∈ ({0, 6} : Finset (ZMod 7)) := by
      interval_cases c1 <;> interval_cases c2 <;>
        first | exact absurd hcc (by decide) | decide
    rw [h1]
    have hsub : ∀ x : ZMod 7, x ∈ ({2, 1} : Finset (ZMod 7)) →
        x ∈ ({0, 1, 2, 5, 6} : Finset (ZMod 7)) := by decide
    have hmem : (2 : ZMod 7) * 1 + ((c1 : ZMod 7) - c2)
        ∈ ({2, 1} : Finset (ZMod 7)) := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hccz ⊢
      rcases hccz with h' | h' <;> rw [h'] <;> decide
    exact hsub _ hmem
  · -- `q1 − q2 = 6`: borrow `= 0` so `f1 ≥ f2` and `c1 ≥ c2`.
    have hqe : (6 : ZMod 7)
        - (if b1 % 7 ^ m < b2 % 7 ^ m then (1 : ZMod 7) else 0)
        ∈ ({0, 6} : Finset (ZMod 7)) := by
      have := he
      rw [hqd, h6] at this
      exact this
    have hfle : ¬ (b1 % 7 ^ m < b2 % 7 ^ m) := by
      intro hb
      rw [if_pos hb] at hqe
      have h5 : ((5 : ZMod 7) ∈ ({0, 6} : Finset (ZMod 7))) := hqe
      exact absurd h5 (by decide)
    have hcc : c2 ≤ c1 := by
      rw [← hc2, ← hc1]
      exact Nat.div_le_div_right
        (Nat.mul_le_mul_left 2 (Nat.le_of_not_gt hfle))
    have hccz : ((c1 : ZMod 7) - c2) ∈ ({0, 1} : Finset (ZMod 7)) := by
      interval_cases c1 <;> interval_cases c2 <;>
        first | exact absurd hcc (by decide) | decide
    rw [h6]
    have hsub : ∀ x : ZMod 7, x ∈ ({5, 6} : Finset (ZMod 7)) →
        x ∈ ({0, 1, 2, 5, 6} : Finset (ZMod 7)) := by decide
    have hmem : (2 : ZMod 7) * 6 + ((c1 : ZMod 7) - c2)
        ∈ ({5, 6} : Finset (ZMod 7)) := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hccz ⊢
      rcases hccz with h' | h' <;> rw [h'] <;> decide
    exact hsub _ hmem

/-! ### §4. Scalar rescale bounds and the `|e|`-to-digit bound

After Lemma 9's first multiplier `λ₁`, all difference digits of `A₁` lie in
`{0,6}`.  The rescales `×2` and `×3` then give explicit digit bounds.
`apLen_smul2_06`: whole-set `×2` bound `≤ 3` (per-pair `{0,±1,±2}`).
`apLen_smul3_06`: whole-set `×3` bound `≤ 4` (triple `decide` with the
borrow-monotonicity constraints).  `qdig_pair_diff_absModN` turns an
`absModN` bound on a same-class pair difference into a digit bound. -/

/-- `×2` pair-rescue (wrapper): same-class pair with `q(e) ∈ {0,6}` has
doubled-digit difference in `{0,±1,±2}`, hence `apLen ≤ 3`. -/
private theorem apLen_smul_pair06 {m : ℕ} {b1 b2 : ℕ}
    (hsame : residueRelOf b1 b2 = residueRel.same)
    (he : qdig7 m (eMod7 m b1 b2) ∈ ({0, 6} : Finset (ZMod 7))) :
    apLen (({b1, b2} : Finset ℕ).image (fun b => qdig7 m (2 * b))) ≤ 3 := by
  rw [Finset.image_insert, Finset.image_singleton]
  exact apLen_two_le3 (qdig7_smul2_diff06 hsame he)

/-- Triple finite check: pairwise differences in `{0,±1,±2}` give
`apLen ≤ 3`. -/
private theorem c65_triple2_dec :
    ∀ a b c : ZMod 7,
      a - b ∈ ({0, 1, 2, 5, 6} : Finset (ZMod 7)) →
      b - c ∈ ({0, 1, 2, 5, 6} : Finset (ZMod 7)) →
      a - c ∈ ({0, 1, 2, 5, 6} : Finset (ZMod 7)) →
      apLen ({a, b, c} : Finset (ZMod 7)) ≤ 3 := by
  decide

/-- Triple `×2` bound: a same-class triple all of whose difference digits
lie in `{0,6}` has `×2`-digit length `≤ 3`. -/
private theorem apLen_smul2_06 {m : ℕ} {b1 b2 b3 : ℕ}
    (hsame : ∀ x ∈ ({b1, b2, b3} : Finset ℕ),
      ∀ y ∈ ({b1, b2, b3} : Finset ℕ),
        residueRelOf x y = residueRel.same)
    (hB : ∀ x ∈ ({b1, b2, b3} : Finset ℕ),
      ∀ y ∈ ({b1, b2, b3} : Finset ℕ),
        qdig7 m (eMod7 m x y) ∈ ({0, 6} : Finset (ZMod 7))) :
    apLen (({b1, b2, b3} : Finset ℕ).image (fun b => qdig7 m (2 * b))) ≤ 3 := by
  rw [Finset.image_insert, Finset.image_insert, Finset.image_singleton]
  exact c65_triple2_dec _ _ _
    (qdig7_smul2_diff06 (hsame b1 (by simp) b2 (by simp))
      (hB b1 (by simp) b2 (by simp)))
    (qdig7_smul2_diff06 (hsame b2 (by simp) b3 (by simp))
      (hB b2 (by simp) b3 (by simp)))
    (qdig7_smul2_diff06 (hsame b1 (by simp) b3 (by simp))
      (hB b1 (by simp) b3 (by simp)))

/-- The `×3` triple finite check.  Carries `cᵢ ∈ {0,1,2}`; digit differences
`δ ∈ {0,±1}` (from `{0,6}`-pairs); the borrow forces `δ = 1 → cᵢ ≤ cⱼ` and
`δ = 6 → cⱼ ≤ cᵢ` (`fᵢ < fⱼ` is monotone in `3f/7^m`).  The stated set is the
digit set translated by `-3q₃` (translation invariance of `apLen`). -/
private theorem c65_smul3_dec :
    ∀ δ12 δ23 : ZMod 7, ∀ c1 c2 c3 : Fin 3,
      δ12 ∈ ({0, 1, 6} : Finset (ZMod 7)) →
      δ23 ∈ ({0, 1, 6} : Finset (ZMod 7)) →
      (δ12 + δ23) ∈ ({0, 1, 6} : Finset (ZMod 7)) →
      (δ12 = 1 → c1.val ≤ c2.val) →
      (δ12 = 6 → c2.val ≤ c1.val) →
      (δ23 = 1 → c2.val ≤ c3.val) →
      (δ23 = 6 → c3.val ≤ c2.val) →
      (δ12 + δ23 = 1 → c1.val ≤ c3.val) →
      (δ12 + δ23 = 6 → c3.val ≤ c1.val) →
      apLen ({3 * (δ12 + δ23) + ((c1 : ℕ) : ZMod 7),
        3 * δ23 + ((c2 : ℕ) : ZMod 7), ((c3 : ℕ) : ZMod 7)}
        : Finset (ZMod 7)) ≤ 4 := by
  decide

/-- `⌊3f/7^m⌋ < 3` when `f < 7^m`. -/
private theorem smul3_carry_lt {m f : ℕ} (hf : f < 7 ^ m) :
    (3 * f) / 7 ^ m < 3 := by
  have hP : 0 < 7 ^ m := Nat.pow_pos (by norm_num)
  rw [Nat.div_lt_iff_lt_mul hP]
  exact Nat.mul_lt_mul_of_pos_left hf (by norm_num)

private theorem smul3_carry_mem {m f : ℕ} (hf : f < 7 ^ m) :
    (((3 * f) / 7 ^ m : ℕ) : ZMod 7) ∈ ({0, 1, 2} : Finset (ZMod 7)) := by
  have hc : (3 * f) / 7 ^ m < 3 := smul3_carry_lt hf
  interval_cases h : (3 * f) / 7 ^ m <;> decide

/-- Whole-triple `×3` bound: same-class triple with `{0,6}`-pairs has
`×3`-digit length `≤ 4`. -/
private theorem apLen_smul3_06 {m : ℕ} {b1 b2 b3 : ℕ}
    (hsame : ∀ x ∈ ({b1, b2, b3} : Finset ℕ),
      ∀ y ∈ ({b1, b2, b3} : Finset ℕ),
        residueRelOf x y = residueRel.same)
    (hB : ∀ x ∈ ({b1, b2, b3} : Finset ℕ),
      ∀ y ∈ ({b1, b2, b3} : Finset ℕ),
        qdig7 m (eMod7 m x y) ∈ ({0, 6} : Finset (ZMod 7))) :
    apLen (({b1, b2, b3} : Finset ℕ).image (fun b => qdig7 m (3 * b))) ≤ 4 := by
  set q1 := qdig7 m b1 with hq1
  set q2 := qdig7 m b2 with hq2
  set q3 := qdig7 m b3 with hq3
  set c1 : ZMod 7 := (((3 * (b1 % 7 ^ m)) / 7 ^ m : ℕ) : ZMod 7)
  set c2 : ZMod 7 := (((3 * (b2 % 7 ^ m)) / 7 ^ m : ℕ) : ZMod 7)
  set c3 : ZMod 7 := (((3 * (b3 % 7 ^ m)) / 7 ^ m : ℕ) : ZMod 7)
  have hP : 0 < 7 ^ m := Nat.pow_pos (by norm_num)
  have hf1 : b1 % 7 ^ m < 7 ^ m := Nat.mod_lt _ hP
  have hf2 : b2 % 7 ^ m < 7 ^ m := Nat.mod_lt _ hP
  have hf3 : b3 % 7 ^ m < 7 ^ m := Nat.mod_lt _ hP
  -- doubled → tripled digit formula
  have hq1' : qdig7 m (3 * b1) = 3 * q1 + c1 := qdig7_smul_eq (by norm_num)
  have hq2' : qdig7 m (3 * b2) = 3 * q2 + c2 := qdig7_smul_eq (by norm_num)
  have hq3' : qdig7 m (3 * b3) = 3 * q3 + c3 := qdig7_smul_eq (by norm_num)
  -- digit differences δ = qᵢ − qⱼ ∈ {0,±1}
  have hqd12 := qdig7_eMod7_same_eq (m := m)
    (hsame b1 (by simp) b2 (by simp))
  have hqd23 := qdig7_eMod7_same_eq (m := m)
    (hsame b2 (by simp) b3 (by simp))
  have hqd13 := qdig7_eMod7_same_eq (m := m)
    (hsame b1 (by simp) b3 (by simp))
  have hδmem : ∀ a b : ZMod 7, a ∈ ({0, 6} : Finset (ZMod 7)) →
      a - b ∈ ({0, 6} : Finset (ZMod 7)) →
      b ∈ ({0, 1, 6} : Finset (ZMod 7)) := by
    decide
  have hδ12 : q1 - q2 ∈ ({0, 1, 6} : Finset (ZMod 7)) :=
    hδmem _ _ (hB b1 (by simp) b2 (by simp))
      (qdig_eMod_sub (hsame b1 (by simp) b2 (by simp)))
  have hδ23 : q2 - q3 ∈ ({0, 1, 6} : Finset (ZMod 7)) :=
    hδmem _ _ (hB b2 (by simp) b3 (by simp))
      (qdig_eMod_sub (hsame b2 (by simp) b3 (by simp)))
  have hδ13 : q1 - q3 ∈ ({0, 1, 6} : Finset (ZMod 7)) :=
    hδmem _ _ (hB b1 (by simp) b3 (by simp))
      (qdig_eMod_sub (hsame b1 (by simp) b3 (by simp)))
  -- borrow-monotonicity: δ = 1 forces fᵢ < fⱼ; δ = 6 forces fᵢ ≥ fⱼ
  have mono_of_one {x y : ℕ} (hx : x ∈ ({b1, b2, b3} : Finset ℕ))
      (hy : y ∈ ({b1, b2, b3} : Finset ℕ))
      (hqd : qdig7 m (eMod7 m x y) = qdig7 m x - qdig7 m y
        - if x % 7 ^ m < y % 7 ^ m then (1 : ZMod 7) else 0)
      (hδ : qdig7 m x - qdig7 m y = 1) :
      x % 7 ^ m < y % 7 ^ m := by
    by_contra hcon
    rw [if_neg hcon, sub_zero] at hqd
    have hqe := hB x hx y hy
    rw [hqd, hδ] at hqe
    exact absurd hqe (by decide)
  have mono_of_six {x y : ℕ} (hx : x ∈ ({b1, b2, b3} : Finset ℕ))
      (hy : y ∈ ({b1, b2, b3} : Finset ℕ))
      (hqd : qdig7 m (eMod7 m x y) = qdig7 m x - qdig7 m y
        - if x % 7 ^ m < y % 7 ^ m then (1 : ZMod 7) else 0)
      (hδ : qdig7 m x - qdig7 m y = 6) :
      y % 7 ^ m ≤ x % 7 ^ m := by
    by_contra hcon
    rw [if_pos (not_le.mp hcon)] at hqd
    have hqe := hB x hx y hy
    have hqe' : qdig7 m x - qdig7 m y - 1 ∈ ({0, 6} : Finset (ZMod 7)) := by
      rw [← hqd]; exact hqe
    rw [hδ] at hqe'
    exact absurd hqe' (by decide)
  -- rewrite the image as the translated decide-set
  have hset : ({b1, b2, b3} : Finset ℕ).image (fun b => qdig7 m (3 * b))
      = {3 * q1 + c1, 3 * q2 + c2, 3 * q3 + c3} := by
    ext a
    simp only [Finset.mem_image, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rcases hx with rfl | rfl | rfl
      · left; exact hq1'
      · right; left; exact hq2'
      · right; right; exact hq3'
    · rintro (h | h | h)
      · exact ⟨b1, by simp, hq1'.trans h.symm⟩
      · exact ⟨b2, by simp, hq2'.trans h.symm⟩
      · exact ⟨b3, by simp, hq3'.trans h.symm⟩
  rw [hset]
  -- translate by -3q3: {3q1+c1, 3q2+c2, 3q3+c3} = {3δ13+c1, 3δ23+c2, c3} + 3q3
  have hshift : ({3 * q1 + c1, 3 * q2 + c2, 3 * q3 + c3} : Finset (ZMod 7))
      = ({3 * (q1 - q3) + c1, 3 * (q2 - q3) + c2, c3}
        : Finset (ZMod 7)).image (· + 3 * q3) := by
    ext a
    simp only [Finset.mem_image, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (h | h | h)
      · refine ⟨3 * (q1 - q3) + c1, Or.inl rfl, ?_⟩
        rw [h]; ring
      · refine ⟨3 * (q2 - q3) + c2, Or.inr (Or.inl rfl), ?_⟩
        rw [h]; ring
      · refine ⟨c3, Or.inr (Or.inr rfl), ?_⟩
        rw [h]; ring
    · rintro ⟨x, hx, rfl⟩
      rcases hx with h | h | h <;> rw [h]
      · left; ring
      · right; left; ring
      · right; right; ring
  rw [hshift, apLen_image_add]
  -- apply the decide: δ12 = q1-q2, δ23 = q2-q3, Nat carries
  have hsum : (q1 - q2) + (q2 - q3) = q1 - q3 := by ring
  rw [← hsum]
  have hδ13' : (q1 - q2) + (q2 - q3) ∈ ({0, 1, 6} : Finset (ZMod 7)) := by
    rw [hsum]; exact hδ13
  refine c65_smul3_dec (q1 - q2) (q2 - q3)
    ⟨(3 * (b1 % 7 ^ m)) / 7 ^ m, smul3_carry_lt hf1⟩
    ⟨(3 * (b2 % 7 ^ m)) / 7 ^ m, smul3_carry_lt hf2⟩
    ⟨(3 * (b3 % 7 ^ m)) / 7 ^ m, smul3_carry_lt hf3⟩
    hδ12 hδ23 hδ13' ?_ ?_ ?_ ?_ ?_ ?_
  · intro h
    have hlt := mono_of_one (by simp : b1 ∈ ({b1, b2, b3} : Finset ℕ))
      (by simp : b2 ∈ ({b1, b2, b3} : Finset ℕ)) hqd12 h
    exact Nat.div_le_div_right (Nat.mul_le_mul_left _ (le_of_lt hlt))
  · intro h
    have hle := mono_of_six (by simp : b1 ∈ ({b1, b2, b3} : Finset ℕ))
      (by simp : b2 ∈ ({b1, b2, b3} : Finset ℕ)) hqd12 h
    exact Nat.div_le_div_right (Nat.mul_le_mul_left _ hle)
  · intro h
    have hlt := mono_of_one (by simp : b2 ∈ ({b1, b2, b3} : Finset ℕ))
      (by simp : b3 ∈ ({b1, b2, b3} : Finset ℕ)) hqd23 h
    exact Nat.div_le_div_right (Nat.mul_le_mul_left _ (le_of_lt hlt))
  · intro h
    have hle := mono_of_six (by simp : b2 ∈ ({b1, b2, b3} : Finset ℕ))
      (by simp : b3 ∈ ({b1, b2, b3} : Finset ℕ)) hqd23 h
    exact Nat.div_le_div_right (Nat.mul_le_mul_left _ hle)
  · intro h
    have hlt : b1 % 7 ^ m < b3 % 7 ^ m := by
      have hδ : q1 - q3 = 1 := by rw [← hsum]; exact h
      exact mono_of_one (by simp : b1 ∈ ({b1, b2, b3} : Finset ℕ))
        (by simp : b3 ∈ ({b1, b2, b3} : Finset ℕ)) hqd13 hδ
    exact Nat.div_le_div_right (Nat.mul_le_mul_left _ (le_of_lt hlt))
  · intro h
    have hle : b3 % 7 ^ m ≤ b1 % 7 ^ m := by
      have hδ : q1 - q3 = 6 := by rw [← hsum]; exact h
      exact mono_of_six (by simp : b1 ∈ ({b1, b2, b3} : Finset ℕ))
        (by simp : b3 ∈ ({b1, b2, b3} : Finset ℕ)) hqd13 hδ
    exact Nat.div_le_div_right (Nat.mul_le_mul_left _ hle)

/-- From `|e(x,y)|_N ≤ k·7^m` (same-class pair): the digit difference lies
in `{0,±1,…,±k}`.  `k = 2` version. -/
private theorem qdig_pair_diff_absModN2 {m x y : ℕ}
    (hrel : residueRelOf x y = residueRel.same)
    (he : absModN (eMod7 m x y) (7 ^ (m + 1)) ≤ 2 * 7 ^ m) :
    qdig7 m x - qdig7 m y ∈ ({0, 1, 2, 5, 6} : Finset (ZMod 7)) := by
  have hP : 0 < 7 ^ m := Nat.pow_pos (by norm_num)
  have hN : 0 < 7 ^ (m + 1) := Nat.pow_pos (by norm_num)
  have hNe : 7 ^ (m + 1) = 7 * 7 ^ m := pow_succ' 7 m
  have hE : eMod7 m x y
      = (x % 7 ^ (m + 1) + 7 ^ (m + 1) - y % 7 ^ (m + 1)) % 7 ^ (m + 1) :=
    eMod7_same_eq hrel
  have hXlt : x % 7 ^ (m + 1) < 7 ^ (m + 1) := Nat.mod_lt _ hN
  have hYlt : y % 7 ^ (m + 1) < 7 ^ (m + 1) := Nat.mod_lt _ hN
  have hX6 : x % 7 ^ (m + 1) / 7 ^ m ≤ 6 := by
    have hlt : x % 7 ^ (m + 1) / 7 ^ m < 7 := by
      rw [Nat.div_lt_iff_lt_mul hP, ← hNe]
      exact hXlt
    omega
  have hY6 : y % 7 ^ (m + 1) / 7 ^ m ≤ 6 := by
    have hlt : y % 7 ^ (m + 1) / 7 ^ m < 7 := by
      rw [Nat.div_lt_iff_lt_mul hP, ← hNe]
      exact hYlt
    omega
  have he' : eMod7 m x y
      = if y % 7 ^ (m + 1) ≤ x % 7 ^ (m + 1)
        then x % 7 ^ (m + 1) - y % 7 ^ (m + 1)
        else x % 7 ^ (m + 1) + 7 ^ (m + 1) - y % 7 ^ (m + 1) := by
    rw [hE]
    by_cases h : y % 7 ^ (m + 1) ≤ x % 7 ^ (m + 1)
    · rw [if_pos h]
      have e1 : x % 7 ^ (m + 1) + 7 ^ (m + 1) - y % 7 ^ (m + 1)
          = (x % 7 ^ (m + 1) - y % 7 ^ (m + 1)) + 7 ^ (m + 1) := by omega
      rw [e1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    · rw [if_neg h]
      push_neg at h
      exact Nat.mod_eq_of_lt (by omega)
  have hEm : eMod7 m x y % 7 ^ (m + 1) = eMod7 m x y :=
    Nat.mod_eq_of_lt (eMod7_lt m x y)
  simp only [absModN] at he
  rw [hEm] at he
  rcases Nat.le_total (eMod7 m x y) (7 ^ (m + 1) - eMod7 m x y)
    with hmin | hmin
  · rw [Nat.min_eq_left hmin] at he
    by_cases hXY : y % 7 ^ (m + 1) ≤ x % 7 ^ (m + 1)
    · rw [he', if_pos hXY] at he
      have hab : x % 7 ^ (m + 1) / 7 ^ m ≤ y % 7 ^ (m + 1) / 7 ^ m + 2 := by
        calc x % 7 ^ (m + 1) / 7 ^ m
            ≤ (y % 7 ^ (m + 1) + 2 * 7 ^ m) / 7 ^ m :=
              Nat.div_le_div_right (by omega)
          _ = y % 7 ^ (m + 1) / 7 ^ m + 2 :=
              Nat.add_mul_div_right _ _ hP
      have hge : y % 7 ^ (m + 1) / 7 ^ m ≤ x % 7 ^ (m + 1) / 7 ^ m :=
        Nat.div_le_div_right hXY
      have hd : qdig7 m x - qdig7 m y
          = ((x % 7 ^ (m + 1) / 7 ^ m - y % 7 ^ (m + 1) / 7 ^ m : ℕ)
            : ZMod 7) := by
        unfold qdig7
        rw [Nat.cast_sub hge]
      rw [hd]
      have hle : x % 7 ^ (m + 1) / 7 ^ m - y % 7 ^ (m + 1) / 7 ^ m ≤ 2 := by
        omega
      interval_cases h :
        x % 7 ^ (m + 1) / 7 ^ m - y % 7 ^ (m + 1) / 7 ^ m <;> decide
    · rw [he', if_neg hXY] at he
      push_neg at hXY
      have hba : x % 7 ^ (m + 1) / 7 ^ m + 5
          ≤ y % 7 ^ (m + 1) / 7 ^ m := by
        have h1 : x % 7 ^ (m + 1) + 5 * 7 ^ m ≤ y % 7 ^ (m + 1) := by omega
        calc x % 7 ^ (m + 1) / 7 ^ m + 5
            = (x % 7 ^ (m + 1) + 5 * 7 ^ m) / 7 ^ m :=
              (Nat.add_mul_div_right _ _ hP).symm
          _ ≤ y % 7 ^ (m + 1) / 7 ^ m := Nat.div_le_div_right h1
      have hd : qdig7 m x - qdig7 m y
          = -(((y % 7 ^ (m + 1) / 7 ^ m - x % 7 ^ (m + 1) / 7 ^ m : ℕ)
            : ZMod 7)) := by
        unfold qdig7
        rw [Nat.cast_sub (by omega : x % 7 ^ (m + 1) / 7 ^ m
          ≤ y % 7 ^ (m + 1) / 7 ^ m)]
        ring
      rw [hd]
      interval_cases hxv : x % 7 ^ (m + 1) / 7 ^ m <;>
        interval_cases hyv : y % 7 ^ (m + 1) / 7 ^ m <;>
        first | omega | decide
  · rw [Nat.min_eq_right hmin] at he
    have hege : 5 * 7 ^ m ≤ eMod7 m x y := by omega
    by_cases hXY : y % 7 ^ (m + 1) ≤ x % 7 ^ (m + 1)
    · rw [he', if_pos hXY] at hege
      have hab : y % 7 ^ (m + 1) / 7 ^ m + 5
          ≤ x % 7 ^ (m + 1) / 7 ^ m := by
        have h1 : y % 7 ^ (m + 1) + 5 * 7 ^ m ≤ x % 7 ^ (m + 1) := by omega
        calc y % 7 ^ (m + 1) / 7 ^ m + 5
            = (y % 7 ^ (m + 1) + 5 * 7 ^ m) / 7 ^ m :=
              (Nat.add_mul_div_right _ _ hP).symm
          _ ≤ x % 7 ^ (m + 1) / 7 ^ m := Nat.div_le_div_right h1
      have hd : qdig7 m x - qdig7 m y
          = ((x % 7 ^ (m + 1) / 7 ^ m - y % 7 ^ (m + 1) / 7 ^ m : ℕ)
            : ZMod 7) := by
        unfold qdig7
        rw [Nat.cast_sub (by omega : y % 7 ^ (m + 1) / 7 ^ m
          ≤ x % 7 ^ (m + 1) / 7 ^ m)]
      rw [hd]
      interval_cases hyv : y % 7 ^ (m + 1) / 7 ^ m <;>
        interval_cases hxv : x % 7 ^ (m + 1) / 7 ^ m <;>
        first | omega | decide
    · rw [he', if_neg hXY] at hege
      push_neg at hXY
      have hba : y % 7 ^ (m + 1) / 7 ^ m
          ≤ x % 7 ^ (m + 1) / 7 ^ m + 2 := by
        calc y % 7 ^ (m + 1) / 7 ^ m
            ≤ (x % 7 ^ (m + 1) + 2 * 7 ^ m) / 7 ^ m :=
              Nat.div_le_div_right (by omega)
          _ = x % 7 ^ (m + 1) / 7 ^ m + 2 :=
              Nat.add_mul_div_right _ _ hP
      have hge : x % 7 ^ (m + 1) / 7 ^ m ≤ y % 7 ^ (m + 1) / 7 ^ m :=
        Nat.div_le_div_right (le_of_lt hXY)
      have hd : qdig7 m x - qdig7 m y
          = -(((y % 7 ^ (m + 1) / 7 ^ m - x % 7 ^ (m + 1) / 7 ^ m : ℕ)
            : ZMod 7)) := by
        unfold qdig7
        rw [Nat.cast_sub hge]
        ring
      rw [hd]
      have hle : y % 7 ^ (m + 1) / 7 ^ m - x % 7 ^ (m + 1) / 7 ^ m ≤ 2 := by
        omega
      interval_cases h :
        y % 7 ^ (m + 1) / 7 ^ m - x % 7 ^ (m + 1) / 7 ^ m <;> decide

/-- `k = 1` version: `|e| ≤ 7^m` gives digit difference in `{0,±1}`. -/
private theorem qdig_pair_diff_absModN1 {m x y : ℕ}
    (hrel : residueRelOf x y = residueRel.same)
    (he : absModN (eMod7 m x y) (7 ^ (m + 1)) ≤ 7 ^ m) :
    qdig7 m x - qdig7 m y ∈ ({0, 1, 6} : Finset (ZMod 7)) := by
  have hP : 0 < 7 ^ m := Nat.pow_pos (by norm_num)
  have hN : 0 < 7 ^ (m + 1) := Nat.pow_pos (by norm_num)
  have hNe : 7 ^ (m + 1) = 7 * 7 ^ m := pow_succ' 7 m
  have hE : eMod7 m x y
      = (x % 7 ^ (m + 1) + 7 ^ (m + 1) - y % 7 ^ (m + 1)) % 7 ^ (m + 1) :=
    eMod7_same_eq hrel
  have hXlt : x % 7 ^ (m + 1) < 7 ^ (m + 1) := Nat.mod_lt _ hN
  have hYlt : y % 7 ^ (m + 1) < 7 ^ (m + 1) := Nat.mod_lt _ hN
  have hX6 : x % 7 ^ (m + 1) / 7 ^ m ≤ 6 := by
    have hlt : x % 7 ^ (m + 1) / 7 ^ m < 7 := by
      rw [Nat.div_lt_iff_lt_mul hP, ← hNe]
      exact hXlt
    omega
  have hY6 : y % 7 ^ (m + 1) / 7 ^ m ≤ 6 := by
    have hlt : y % 7 ^ (m + 1) / 7 ^ m < 7 := by
      rw [Nat.div_lt_iff_lt_mul hP, ← hNe]
      exact hYlt
    omega
  have he' : eMod7 m x y
      = if y % 7 ^ (m + 1) ≤ x % 7 ^ (m + 1)
        then x % 7 ^ (m + 1) - y % 7 ^ (m + 1)
        else x % 7 ^ (m + 1) + 7 ^ (m + 1) - y % 7 ^ (m + 1) := by
    rw [hE]
    by_cases h : y % 7 ^ (m + 1) ≤ x % 7 ^ (m + 1)
    · rw [if_pos h]
      have e1 : x % 7 ^ (m + 1) + 7 ^ (m + 1) - y % 7 ^ (m + 1)
          = (x % 7 ^ (m + 1) - y % 7 ^ (m + 1)) + 7 ^ (m + 1) := by omega
      rw [e1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    · rw [if_neg h]
      push_neg at h
      exact Nat.mod_eq_of_lt (by omega)
  have hEm : eMod7 m x y % 7 ^ (m + 1) = eMod7 m x y :=
    Nat.mod_eq_of_lt (eMod7_lt m x y)
  simp only [absModN] at he
  rw [hEm] at he
  rcases Nat.le_total (eMod7 m x y) (7 ^ (m + 1) - eMod7 m x y)
    with hmin | hmin
  · rw [Nat.min_eq_left hmin] at he
    by_cases hXY : y % 7 ^ (m + 1) ≤ x % 7 ^ (m + 1)
    · rw [he', if_pos hXY] at he
      have hab : x % 7 ^ (m + 1) / 7 ^ m ≤ y % 7 ^ (m + 1) / 7 ^ m + 1 := by
        calc x % 7 ^ (m + 1) / 7 ^ m
            ≤ (y % 7 ^ (m + 1) + 1 * 7 ^ m) / 7 ^ m :=
              Nat.div_le_div_right (by omega)
          _ = y % 7 ^ (m + 1) / 7 ^ m + 1 :=
              Nat.add_mul_div_right _ _ hP
      have hge : y % 7 ^ (m + 1) / 7 ^ m ≤ x % 7 ^ (m + 1) / 7 ^ m :=
        Nat.div_le_div_right hXY
      have hd : qdig7 m x - qdig7 m y
          = ((x % 7 ^ (m + 1) / 7 ^ m - y % 7 ^ (m + 1) / 7 ^ m : ℕ)
            : ZMod 7) := by
        unfold qdig7
        rw [Nat.cast_sub hge]
      rw [hd]
      have hle : x % 7 ^ (m + 1) / 7 ^ m - y % 7 ^ (m + 1) / 7 ^ m ≤ 1 := by
        omega
      interval_cases h :
        x % 7 ^ (m + 1) / 7 ^ m - y % 7 ^ (m + 1) / 7 ^ m <;> decide
    · rw [he', if_neg hXY] at he
      push_neg at hXY
      have hba : x % 7 ^ (m + 1) / 7 ^ m + 6
          ≤ y % 7 ^ (m + 1) / 7 ^ m := by
        have h1 : x % 7 ^ (m + 1) + 6 * 7 ^ m ≤ y % 7 ^ (m + 1) := by omega
        calc x % 7 ^ (m + 1) / 7 ^ m + 6
            = (x % 7 ^ (m + 1) + 6 * 7 ^ m) / 7 ^ m :=
              (Nat.add_mul_div_right _ _ hP).symm
          _ ≤ y % 7 ^ (m + 1) / 7 ^ m := Nat.div_le_div_right h1
      have hd : qdig7 m x - qdig7 m y
          = -(((y % 7 ^ (m + 1) / 7 ^ m - x % 7 ^ (m + 1) / 7 ^ m : ℕ)
            : ZMod 7)) := by
        unfold qdig7
        rw [Nat.cast_sub (by omega : x % 7 ^ (m + 1) / 7 ^ m
          ≤ y % 7 ^ (m + 1) / 7 ^ m)]
        ring
      rw [hd]
      interval_cases hxv : x % 7 ^ (m + 1) / 7 ^ m <;>
        interval_cases hyv : y % 7 ^ (m + 1) / 7 ^ m <;>
        first | omega | decide
  · rw [Nat.min_eq_right hmin] at he
    have hege : 6 * 7 ^ m ≤ eMod7 m x y := by omega
    by_cases hXY : y % 7 ^ (m + 1) ≤ x % 7 ^ (m + 1)
    · rw [he', if_pos hXY] at hege
      have hab : y % 7 ^ (m + 1) / 7 ^ m + 6
          ≤ x % 7 ^ (m + 1) / 7 ^ m := by
        have h1 : y % 7 ^ (m + 1) + 6 * 7 ^ m ≤ x % 7 ^ (m + 1) := by omega
        calc y % 7 ^ (m + 1) / 7 ^ m + 6
            = (y % 7 ^ (m + 1) + 6 * 7 ^ m) / 7 ^ m :=
              (Nat.add_mul_div_right _ _ hP).symm
          _ ≤ x % 7 ^ (m + 1) / 7 ^ m := Nat.div_le_div_right h1
      have hd : qdig7 m x - qdig7 m y
          = ((x % 7 ^ (m + 1) / 7 ^ m - y % 7 ^ (m + 1) / 7 ^ m : ℕ)
            : ZMod 7) := by
        unfold qdig7
        rw [Nat.cast_sub (by omega : y % 7 ^ (m + 1) / 7 ^ m
          ≤ x % 7 ^ (m + 1) / 7 ^ m)]
      rw [hd]
      interval_cases hyv : y % 7 ^ (m + 1) / 7 ^ m <;>
        interval_cases hxv : x % 7 ^ (m + 1) / 7 ^ m <;>
        first | omega | decide
    · rw [he', if_neg hXY] at hege
      push_neg at hXY
      have hba : y % 7 ^ (m + 1) / 7 ^ m
          ≤ x % 7 ^ (m + 1) / 7 ^ m + 1 := by
        calc y % 7 ^ (m + 1) / 7 ^ m
            ≤ (x % 7 ^ (m + 1) + 1 * 7 ^ m) / 7 ^ m :=
              Nat.div_le_div_right (by omega)
          _ = x % 7 ^ (m + 1) / 7 ^ m + 1 :=
              Nat.add_mul_div_right _ _ hP
      have hge : x % 7 ^ (m + 1) / 7 ^ m ≤ y % 7 ^ (m + 1) / 7 ^ m :=
        Nat.div_le_div_right (le_of_lt hXY)
      have hd : qdig7 m x - qdig7 m y
          = -(((y % 7 ^ (m + 1) / 7 ^ m - x % 7 ^ (m + 1) / 7 ^ m : ℕ)
            : ZMod 7)) := by
        unfold qdig7
        rw [Nat.cast_sub hge]
        ring
      rw [hd]
      have hle : y % 7 ^ (m + 1) / 7 ^ m - x % 7 ^ (m + 1) / 7 ^ m ≤ 1 := by
        omega
      interval_cases h :
        y % 7 ^ (m + 1) / 7 ^ m - x % 7 ^ (m + 1) / 7 ^ m <;> decide

/-! ### §3 The `l₂ = 0` Lemma 5 core and the branch finisher -/

/-- Lemma-5-style finite core for `l₂ = 0` (two classes only, no ordering):
for `l₁ + l₄ ≤ 5` and every relative offset `j₄` some `Λ₀`-shift `u` puts
both windows off `{0,6}`.  (Python-verified; the `(1,4)` row is the only
one not subsumed by the `(3,3)`/`(4,2)` covers.) -/
private theorem lemma5_20_core :
    ∀ l₁ ∈ Finset.range 6, ∀ l₄ ∈ Finset.range 6,
      l₁ + l₄ ≤ 5 → ∀ j₄ : ZMod 7,
      ∃ u : ZMod 7, avoids06 (cycIv u l₁) ∧
        avoids06 (cycIv (j₄ + 4 * u) l₄) := by
  set_option maxRecDepth 32768 in
  decide

/-- Cover dispatch: the three branch shapes all admit the
`case65_tail`-form cover hypothesis. -/
private theorem c65_hcov {l1 l4 : ℕ}
    (h : (l1 ≤ 3 ∧ l4 ≤ 3) ∨ (l1 ≤ 4 ∧ l4 ≤ 2) ∨ (l1 + l4 ≤ 5)) :
    ∀ c : ZMod 7, ∃ k : ZMod 7,
      avoids06 (cycIv (1 + k) l1 ∪ cycIv (c + 4 * k) l4) := by
  intro c
  rcases h with ⟨h1, h4⟩ | ⟨h1, h4⟩ | h
  · obtain ⟨k, hk⟩ := c65_cover33 c
    exact ⟨k, avoids06_mono
      (Finset.union_subset_union (cycIv_mono h1) (cycIv_mono h4)) hk⟩
  · obtain ⟨k, hk⟩ := c65_cover42 c
    exact ⟨k, avoids06_mono
      (Finset.union_subset_union (cycIv_mono h1) (cycIv_mono h4)) hk⟩
  · obtain ⟨u, hu1, hu4⟩ := lemma5_20_core l1
      (Finset.mem_range.mpr (by omega)) l4
      (Finset.mem_range.mpr (by omega)) h (c - 4)
    refine ⟨u - 1, ?_⟩
    have e1 : (1 : ZMod 7) + (u - 1) = u := by ring
    have e4 : c + 4 * (u - 1) = c - 4 + 4 * u := by ring
    rw [e1, e4, avoids06_union]
    exact ⟨hu1, hu4⟩

/-- **Branch finisher**: after a first `7`-unit multiplier `λ₁`, if the
digit images have one of the three admissible length shapes, some `Λ₀`
completes `good7`. -/
private theorem c65_finish {m : ℕ} (hm : 0 < m) {A1 A4 : Finset ℕ}
    (hpos : ∀ d ∈ A1 ∪ A4, 0 < d)
    (hunit : ∀ d ∈ A1 ∪ A4, padicValNat 7 d = 0)
    {s : ZMod 7} (hs : s ≠ 0)
    (hcls1 : ∀ d ∈ A1, runit7 d = s)
    (hcls4 : ∀ d ∈ A4, runit7 d = 4 * s)
    {lam₁ : ℕ} (hlam₁ : ¬ 7 ∣ lam₁)
    (hshape :
      (apLen ((A1.image fun d => lam₁ * d).image (qdig7 m)) ≤ 3 ∧
        apLen ((A4.image fun d => lam₁ * d).image (qdig7 m)) ≤ 3) ∨
      (apLen ((A1.image fun d => lam₁ * d).image (qdig7 m)) ≤ 4 ∧
        apLen ((A4.image fun d => lam₁ * d).image (qdig7 m)) ≤ 2) ∨
      (apLen ((A1.image fun d => lam₁ * d).image (qdig7 m)) +
        apLen ((A4.image fun d => lam₁ * d).image (qdig7 m)) ≤ 5)) :
    ∃ lam : ℕ, ¬ 7 ∣ lam ∧ good7 m lam (A1 ∪ A4) := by
  set X1 := (A1.image fun d => lam₁ * d).image (qdig7 m)
  set X4 := (A4.image fun d => lam₁ * d).image (qdig7 m)
  rcases hshape with ⟨h1, h4⟩ | ⟨h1, h4⟩ | h
  · obtain ⟨i1, hi1⟩ := (apLen_le_iff X1 3 (by norm_num)).mp h1
    obtain ⟨i4, hi4⟩ := (apLen_le_iff X4 3 (by norm_num)).mp h4
    exact case65_tail hm hpos hunit hs hcls1 hcls4 hlam₁ hi1 hi4
      (fun c => c65_hcov (Or.inl ⟨le_refl _, le_refl _⟩) c)
  · obtain ⟨i1, hi1⟩ := (apLen_le_iff X1 4 (by norm_num)).mp h1
    obtain ⟨i4, hi4⟩ := (apLen_le_iff X4 2 (by norm_num)).mp h4
    exact case65_tail hm hpos hunit hs hcls1 hcls4 hlam₁ hi1 hi4
      (fun c => c65_hcov (Or.inr (Or.inl ⟨le_refl _, le_refl _⟩)) c)
  · obtain ⟨i1, hi1⟩ := (apLen_le_iff X1 (apLen X1)
      (apLen_le_seven _)).mp le_rfl
    obtain ⟨i4, hi4⟩ := (apLen_le_iff X4 (apLen X4)
      (apLen_le_seven _)).mp le_rfl
    exact case65_tail hm hpos hunit hs hcls1 hcls4 hlam₁ hi1 hi4
      (c65_hcov (Or.inr (Or.inr h)))

/-! ### §4 Element-digit gadgets -/

/-- `q(z) = 0` forces `z % N < 7^m` (clone of `Case5mL9b`). -/
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

/-- `ν(z) < m` forces `z % N ≠ 0` (clone of `Case5mL9b`). -/
private theorem mod_pos_of_val_lt {m z : ℕ} (hz : padicValNat 7 z < m)
    (hz0 : z ≠ 0) : 0 < z % 7 ^ (m + 1) := by
  have hmod : z % 7 ^ (m + 1) ≠ 0 := by
    rw [Ne, ← Nat.dvd_iff_mod_eq_zero]
    intro hd
    have hle := (Nat.pow_dvd_iff_le_padicValNat (by norm_num) hz0).mp hd
    omega
  exact Nat.pos_of_ne_zero hmod

/-- Same-class pair digit bound `≤ 2` from `q(e) ∈ {0,6}`: the difference
`q(x) − q(y)` lies in `{0,±1}` (the borrow can only add `1` to `6`). -/
private theorem c65_pair_len2 {m : ℕ} {x y : ℕ}
    (hrel : residueRelOf x y = residueRel.same)
    (he : qdig7 m (eMod7 m x y) ∈ ({0, 6} : Finset (ZMod 7))) :
    apLen (({x, y} : Finset ℕ).image (qdig7 m)) ≤ 2 := by
  rw [Finset.image_insert, Finset.image_singleton]
  apply apLen_two_le2
  have h := qdig7_eMod7_same_eq (m := m) hrel
  by_cases hδ : x % 7 ^ m < y % 7 ^ m
  · rw [if_pos hδ] at h
    have e : qdig7 m x - qdig7 m y = qdig7 m (eMod7 m x y) + 1 := by
      linear_combination -h
    rw [e]
    simp only [Finset.mem_insert, Finset.mem_singleton] at he ⊢
    rcases he with h | h <;> rw [h] <;> decide
  · rw [if_neg hδ, sub_zero] at h
    rw [← h]
    simp only [Finset.mem_insert, Finset.mem_singleton] at he ⊢
    rcases he with h | h <;> rw [h] <;> decide

/-- Same-class pair digit bound `≤ 3` from `q(e) ∈ {0,±1,±2}` =
`{0,1,2,5,6}`: the difference `q(x) − q(y)` lies in `{0,±1,±2}`. -/
private theorem c65_pair_len3 {m : ℕ} {x y : ℕ}
    (hrel : residueRelOf x y = residueRel.same)
    (he : qdig7 m (eMod7 m x y) ∈ ({0, 1, 5, 6} : Finset (ZMod 7))) :
    apLen (({x, y} : Finset ℕ).image (qdig7 m)) ≤ 3 := by
  rw [Finset.image_insert, Finset.image_singleton]
  apply apLen_two_le3
  have h := qdig7_eMod7_same_eq (m := m) hrel
  by_cases hδ : x % 7 ^ m < y % 7 ^ m
  · rw [if_pos hδ] at h
    have e : qdig7 m x - qdig7 m y = qdig7 m (eMod7 m x y) + 1 := by
      linear_combination -h
    rw [e]
    simp only [Finset.mem_insert, Finset.mem_singleton] at he ⊢
    rcases he with h | h | h | h <;> rw [h] <;> decide
  · rw [if_neg hδ, sub_zero] at h
    rw [← h]
    simp only [Finset.mem_insert, Finset.mem_singleton] at he ⊢
    rcases he with h | h | h | h <;> rw [h] <;> decide

/-- Same-class pair bound `≤ 2` from `q(e) = 0` (`e < 7^m`): the
difference `q(x) − q(y)` lies in `{0,1}`. -/
private theorem c65_pair_len2' {m : ℕ} {x y : ℕ}
    (hrel : residueRelOf x y = residueRel.same)
    (he : qdig7 m (eMod7 m x y) = 0) :
    apLen (({x, y} : Finset ℕ).image (qdig7 m)) ≤ 2 := by
  rw [Finset.image_insert, Finset.image_singleton]
  apply apLen_two_le2
  have h := qdig7_eMod7_same_eq (m := m) hrel
  rw [he] at h
  by_cases hδ : x % 7 ^ m < y % 7 ^ m
  · rw [if_pos hδ] at h
    have e : qdig7 m x - qdig7 m y = 1 := by linear_combination -h
    rw [e]; decide
  · rw [if_neg hδ, sub_zero, eq_comm] at h
    rw [h]; decide

/-! ### §5 Rescue machinery and lemma-9 clones -/

/-- `q(e) ∈ {2,3,4}` forces `|e|_N ≥ 2·7^m` (unconditional version —
`absModN_ge_two_iff_qdig7` also needs `ν < m`). -/
private theorem c65_absMod_ge2 {m e : ℕ} (he : e < 7 ^ (m + 1))
    (hq : qdig7 m e ∈ ({2, 3, 4} : Finset (ZMod 7))) :
    2 * 7 ^ m ≤ absModN e (7 ^ (m + 1)) := by
  have hP : 0 < 7 ^ m := Nat.pow_pos (by norm_num)
  have hN : 7 ^ (m + 1) = 7 * 7 ^ m := pow_succ' 7 m
  have hlt : e / 7 ^ m < 7 := by
    rw [Nat.div_lt_iff_lt_mul hP, ← hN]; exact he
  have hqN : e / 7 ^ m ∈ ({2, 3, 4} : Finset ℕ) := by
    rw [qdig7_eq_cast_div] at hq
    interval_cases h : e / 7 ^ m <;>
      simp only [Nat.cast_ofNat, Finset.mem_insert, Finset.mem_singleton]
        at hq ⊢ <;>
      first | decide | (exfalso; revert hq; decide)
  have hde := Nat.div_add_mod e (7 ^ m)
  have hmlt := Nat.mod_lt e hP
  simp only [Finset.mem_insert, Finset.mem_singleton] at hqN
  simp only [absModN]
  rw [Nat.mod_eq_of_lt he, hN]
  rcases hqN with h2 | h2 | h2 <;> rw [h2] at hde <;>
    rcases Nat.le_total e (7 * 7 ^ m - e) with hmin | hmin <;>
    first | (rw [Nat.min_eq_left hmin]; omega)
          | (rw [Nat.min_eq_right hmin]; omega)


/-- **A4-side rescue**: a bad pair digit `q(e) ∈ {2,3,4}` either admits
`×2` (when `|e| ≥ 5N/14`, giving pair-length `≤ 3`) or `×3`
(when `|e| ∈ [2N/7, 5N/14]`, giving pair-length `≤ 2`). -/
private theorem c65_a4_rescue {m : ℕ} {x y : ℕ}
    (hrel : residueRelOf x y = residueRel.same)
    (hr : runit7 x = runit7 y) (hry : runit7 y ≠ 0)
    (hbad : qdig7 m (eMod7 m x y) ∈ ({2, 3, 4} : Finset (ZMod 7))) :
    (apLen (({x, y} : Finset ℕ).image (fun b => qdig7 m (2 * b))) ≤ 3) ∨
      (apLen (({x, y} : Finset ℕ).image (fun b => qdig7 m (3 * b))) ≤ 2) := by
  set e := eMod7 m x y with he
  have hge : 2 * 7 ^ m ≤ absModN e (7 ^ (m + 1)) :=
    c65_absMod_ge2 (eMod7_lt m x y) hbad
  have hr2 : runit7 (2 * x) = runit7 (2 * y) := by
    rw [runit7_mul, runit7_mul, hr]
  have hr2y : runit7 (2 * y) ≠ 0 := by
    rw [runit7_mul]
    exact mul_ne_zero (runit7_ne_zero (by norm_num : (0:ℕ) < 2)) hry
  have hr3 : runit7 (3 * x) = runit7 (3 * y) := by
    rw [runit7_mul, runit7_mul, hr]
  have hr3y : runit7 (3 * y) ≠ 0 := by
    rw [runit7_mul]
    exact mul_ne_zero (runit7_ne_zero (by norm_num : (0:ℕ) < 3)) hry
  have hrel2 : residueRelOf (2 * x) (2 * y) = residueRel.same :=
    rel_same hr2 hr2y
  have hrel3 : residueRelOf (3 * x) (3 * y) = residueRel.same :=
    rel_same hr3 hr3y
  have he2 : eMod7 m (2 * x) (2 * y) = (2 * e) % 7 ^ (m + 1) := by
    exact eMod7_smul (runit7_ne_zero (by norm_num : (0:ℕ) < 2))
  have he3 : eMod7 m (3 * x) (3 * y) = (3 * e) % 7 ^ (m + 1) := by
    exact eMod7_smul (runit7_ne_zero (by norm_num : (0:ℕ) < 3))
  by_cases hbig : 5 * 7 ^ (m + 1) ≤ 14 * absModN e (7 ^ (m + 1))
  · left
    have hle := absModN_two_mul_le (m := m) (x := e) hbig
    have habs : absModN (eMod7 m (2 * x) (2 * y)) (7 ^ (m + 1))
        ≤ 2 * 7 ^ m := by
      rw [he2]
      simpa [absModN, Nat.mod_mod] using hle
    rw [Finset.image_insert, Finset.image_singleton]
    exact apLen_two_le3 (qdig_pair_diff_absModN2 hrel2 habs)
  · right
    push_neg at hbig
    have hle := absModN_three_mul_le (m := m) (x := e) hge (by omega)
    have habs : absModN (eMod7 m (3 * x) (3 * y)) (7 ^ (m + 1))
        ≤ 7 ^ m := by
      rw [he3]
      simpa [absModN, Nat.mod_mod] using hle
    rw [Finset.image_insert, Finset.image_singleton]
    exact apLen_two_le2 (qdig_pair_diff_absModN1 hrel3 habs)


/-- Element not in `{2,3,4}` lies in `{0,1,5,6}`. -/
private theorem mem_0156_of_not_234 {x : ZMod 7}
    (h : x ∉ ({2, 3, 4} : Finset (ZMod 7))) :
    x ∈ ({0, 1, 5, 6} : Finset (ZMod 7)) := by
  revert x
  decide

/-- Rescue-dispatch: if `lam₁` achieves `apLen ≤ 2` on `A₁` and all pairwise difference
digits of `A₁` lie in `{0, 6}`, then either `lam₁` or `2 * lam₁` or `3 * lam₁` produces an
admissible shape for `c65_finish`. -/
private theorem c65_finish_of_pair06 {m : ℕ} (hm : 0 < m) {A1 A4 : Finset ℕ}
    (hpos : ∀ d ∈ A1 ∪ A4, 0 < d)
    (hunit : ∀ d ∈ A1 ∪ A4, padicValNat 7 d = 0)
    {s : ZMod 7} (hs : s ≠ 0)
    (hcls1 : ∀ d ∈ A1, runit7 d = s)
    (hcls4 : ∀ d ∈ A4, runit7 d = 4 * s)
    {d1 d2 d3 : ℕ} (hA1eq : A1 = {d1, d2, d3})
    {d4 d5 : ℕ} (hA4eq : A4 = {d4, d5})
    {lam₁ : ℕ} (hlam₁ : ¬ 7 ∣ lam₁)
    (hlen : apLen ((A1.image (fun d => lam₁ * d)).image (qdig7 m)) ≤ 2)
    (hB : ∀ x ∈ ({d1, d2, d3} : Finset ℕ), ∀ y ∈ ({d1, d2, d3} : Finset ℕ),
      qdig7 m (eMod7 m (lam₁ * x) (lam₁ * y)) ∈ ({0, 6} : Finset (ZMod 7))) :
    ∃ lam : ℕ, ¬ 7 ∣ lam ∧ good7 m lam (A1 ∪ A4) := by
  set x' := lam₁ * d4
  set y' := lam₁ * d5
  have hd4 : d4 ∈ A4 := by rw [hA4eq]; exact Finset.mem_insert_self _ _
  have hd5 : d5 ∈ A4 := by
    rw [hA4eq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hr4 : runit7 d4 = 4 * s := hcls4 d4 hd4
  have hr5 : runit7 d5 = 4 * s := hcls4 d5 hd5
  have hlam₁0 : lam₁ ≠ 0 := fun h => hlam₁ (h ▸ dvd_zero _)
  have hrl1 : runit7 lam₁ ≠ 0 := runit7_ne_zero (Nat.pos_of_ne_zero hlam₁0)
  have hrx' : runit7 x' = runit7 lam₁ * (4 * s) := by
    dsimp [x']; rw [runit7_mul, hr4]
  have hry' : runit7 y' = runit7 lam₁ * (4 * s) := by
    dsimp [y']; rw [runit7_mul, hr5]
  have hry'0 : runit7 y' ≠ 0 := by
    rw [hry']
    exact mul_ne_zero hrl1 (mul_ne_zero (by decide) hs)
  have hrel' : residueRelOf x' y' = residueRel.same :=
    rel_same (by rw [hrx', hry']) hry'0
  have hA4img : (A4.image (fun d => lam₁ * d)).image (qdig7 m)
      = ({x', y'} : Finset ℕ).image (qdig7 m) := by
    rw [hA4eq]
    simp only [Finset.image_insert, Finset.image_singleton]
    rfl
  by_cases hbad : qdig7 m (eMod7 m x' y') ∈ ({2, 3, 4} : Finset (ZMod 7))
  · rcases c65_a4_rescue hrel' (by rw [hrx', hry']) hry'0 hbad with h2 | h3
    · -- ×2 branch
      set lam₂ := 2 * lam₁ with hlam₂def
      have hlam₂ : ¬ 7 ∣ lam₂ := Nat.prime_seven.not_dvd_mul (by decide) hlam₁
      have h2x' : lam₂ * d4 = 2 * x' := by dsimp [x', lam₂]; ring
      have h2y' : lam₂ * d5 = 2 * y' := by dsimp [y', lam₂]; ring
      have hA4img2 : (A4.image (fun d => lam₂ * d)).image (qdig7 m)
          = ({x', y'} : Finset ℕ).image (fun b => qdig7 m (2 * b)) := by
        rw [hA4eq]
        simp only [Finset.image_insert, Finset.image_singleton, h2x', h2y']
      have hap4 : apLen ((A4.image (fun d => lam₂ * d)).image (qdig7 m)) ≤ 3 := by
        rw [hA4img2]; exact h2
      set b1 := lam₁ * d1 with hb1
      set b2 := lam₁ * d2 with hb2
      set b3 := lam₁ * d3 with hb3
      have h2b1 : lam₂ * d1 = 2 * b1 := by dsimp [b1, lam₂]; ring
      have h2b2 : lam₂ * d2 = 2 * b2 := by dsimp [b2, lam₂]; ring
      have h2b3 : lam₂ * d3 = 2 * b3 := by dsimp [b3, lam₂]; ring
      have hA1img2 : (A1.image (fun d => lam₂ * d)).image (qdig7 m)
          = ({b1, b2, b3} : Finset ℕ).image (fun b => qdig7 m (2 * b)) := by
        rw [hA1eq]
        simp only [Finset.image_insert, Finset.image_singleton, h2b1, h2b2, h2b3]
      have hd1mem : d1 ∈ A1 := by rw [hA1eq]; exact Finset.mem_insert_self _ _
      have hd2mem : d2 ∈ A1 := by
        rw [hA1eq]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
      have hd3mem : d3 ∈ A1 := by
        rw [hA1eq]; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
      have hr1 : runit7 d1 = s := hcls1 d1 hd1mem
      have hr2 : runit7 d2 = s := hcls1 d2 hd2mem
      have hr3 : runit7 d3 = s := hcls1 d3 hd3mem
      have hsame_all : ∀ u ∈ ({b1, b2, b3} : Finset ℕ), runit7 u = runit7 lam₁ * s := by
        intro u hu
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu
        rcases hu with rfl | rfl | rfl
        · rw [runit7_mul, hr1]
        · rw [runit7_mul, hr2]
        · rw [runit7_mul, hr3]
      have hsame : ∀ x ∈ ({b1, b2, b3} : Finset ℕ),
          ∀ y ∈ ({b1, b2, b3} : Finset ℕ),
            residueRelOf x y = residueRel.same := by
        intro x hx y hy
        apply rel_same
        · rw [hsame_all x hx, hsame_all y hy]
        · rw [hsame_all y hy]
          exact mul_ne_zero hrl1 hs
      have hB' : ∀ x ∈ ({b1, b2, b3} : Finset ℕ),
          ∀ y ∈ ({b1, b2, b3} : Finset ℕ),
            qdig7 m (eMod7 m x y) ∈ ({0, 6} : Finset (ZMod 7)) := by
        intro x hx y hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
        rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
        · exact hB d1 (by simp) d1 (by simp)
        · exact hB d1 (by simp) d2 (by simp)
        · exact hB d1 (by simp) d3 (by simp)
        · exact hB d2 (by simp) d1 (by simp)
        · exact hB d2 (by simp) d2 (by simp)
        · exact hB d2 (by simp) d3 (by simp)
        · exact hB d3 (by simp) d1 (by simp)
        · exact hB d3 (by simp) d2 (by simp)
        · exact hB d3 (by simp) d3 (by simp)
      have hap1 : apLen ((A1.image (fun d => lam₂ * d)).image (qdig7 m)) ≤ 3 := by
        rw [hA1img2]
        exact apLen_smul2_06 hsame hB'
      exact c65_finish hm hpos hunit hs hcls1 hcls4 hlam₂ (Or.inl ⟨hap1, hap4⟩)
    · -- ×3 branch
      set lam₃ := 3 * lam₁ with hlam₃def
      have hlam₃ : ¬ 7 ∣ lam₃ := Nat.prime_seven.not_dvd_mul (by decide) hlam₁
      have h3x' : lam₃ * d4 = 3 * x' := by dsimp [x', lam₃]; ring
      have h3y' : lam₃ * d5 = 3 * y' := by dsimp [y', lam₃]; ring
      have hA4img3 : (A4.image (fun d => lam₃ * d)).image (qdig7 m)
          = ({x', y'} : Finset ℕ).image (fun b => qdig7 m (3 * b)) := by
        rw [hA4eq]
        simp only [Finset.image_insert, Finset.image_singleton, h3x', h3y']
      have hap4 : apLen ((A4.image (fun d => lam₃ * d)).image (qdig7 m)) ≤ 2 := by
        rw [hA4img3]; exact h3
      set b1 := lam₁ * d1 with hb1
      set b2 := lam₁ * d2 with hb2
      set b3 := lam₁ * d3 with hb3
      have h3b1 : lam₃ * d1 = 3 * b1 := by dsimp [b1, lam₃]; ring
      have h3b2 : lam₃ * d2 = 3 * b2 := by dsimp [b2, lam₃]; ring
      have h3b3 : lam₃ * d3 = 3 * b3 := by dsimp [b3, lam₃]; ring
      have hA1img3 : (A1.image (fun d => lam₃ * d)).image (qdig7 m)
          = ({b1, b2, b3} : Finset ℕ).image (fun b => qdig7 m (3 * b)) := by
        rw [hA1eq]
        simp only [Finset.image_insert, Finset.image_singleton, h3b1, h3b2, h3b3]
      have hd1mem : d1 ∈ A1 := by rw [hA1eq]; exact Finset.mem_insert_self _ _
      have hd2mem : d2 ∈ A1 := by
        rw [hA1eq]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
      have hd3mem : d3 ∈ A1 := by
        rw [hA1eq]; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
      have hr1 : runit7 d1 = s := hcls1 d1 hd1mem
      have hr2 : runit7 d2 = s := hcls1 d2 hd2mem
      have hr3 : runit7 d3 = s := hcls1 d3 hd3mem
      have hsame_all : ∀ u ∈ ({b1, b2, b3} : Finset ℕ), runit7 u = runit7 lam₁ * s := by
        intro u hu
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu
        rcases hu with rfl | rfl | rfl
        · rw [runit7_mul, hr1]
        · rw [runit7_mul, hr2]
        · rw [runit7_mul, hr3]
      have hsame : ∀ x ∈ ({b1, b2, b3} : Finset ℕ),
          ∀ y ∈ ({b1, b2, b3} : Finset ℕ),
            residueRelOf x y = residueRel.same := by
        intro x hx y hy
        apply rel_same
        · rw [hsame_all x hx, hsame_all y hy]
        · rw [hsame_all y hy]
          exact mul_ne_zero hrl1 hs
      have hB' : ∀ x ∈ ({b1, b2, b3} : Finset ℕ),
          ∀ y ∈ ({b1, b2, b3} : Finset ℕ),
            qdig7 m (eMod7 m x y) ∈ ({0, 6} : Finset (ZMod 7)) := by
        intro x hx y hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
        rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
        · exact hB d1 (by simp) d1 (by simp)
        · exact hB d1 (by simp) d2 (by simp)
        · exact hB d1 (by simp) d3 (by simp)
        · exact hB d2 (by simp) d1 (by simp)
        · exact hB d2 (by simp) d2 (by simp)
        · exact hB d2 (by simp) d3 (by simp)
        · exact hB d3 (by simp) d1 (by simp)
        · exact hB d3 (by simp) d2 (by simp)
        · exact hB d3 (by simp) d3 (by simp)
      have hap1 : apLen ((A1.image (fun d => lam₃ * d)).image (qdig7 m)) ≤ 4 := by
        rw [hA1img3]
        exact apLen_smul3_06 hsame hB'
      exact c65_finish hm hpos hunit hs hcls1 hcls4 hlam₃ (Or.inr (Or.inl ⟨hap1, hap4⟩))
  · have hgood : qdig7 m (eMod7 m x' y') ∈ ({0, 1, 5, 6} : Finset (ZMod 7)) :=
      mem_0156_of_not_234 hbad
    have hap4 : apLen (({x', y'} : Finset ℕ).image (qdig7 m)) ≤ 3 :=
      c65_pair_len3 hrel' hgood
    rw [← hA4img] at hap4
    have hshape : apLen ((A1.image (fun d => lam₁ * d)).image (qdig7 m)) ≤ 3 ∧
        apLen ((A4.image (fun d => lam₁ * d)).image (qdig7 m)) ≤ 3 :=
      ⟨le_trans hlen (by norm_num), hap4⟩
    exact c65_finish hm hpos hunit hs hcls1 hcls4 hlam₁ (Or.inl hshape)


private theorem apLen_singleton_le1 (a : ZMod 7) :
    apLen ({a} : Finset (ZMod 7)) ≤ 1 := by
  have : ({a} : Finset (ZMod 7)) ⊆ cycIv a 1 := by
    intro z hz
    rw [Finset.mem_singleton.mp hz, mem_cycIv, sub_self, ZMod.val_zero]
    decide
  exact (apLen_le_iff _ 1 (by norm_num)).mpr ⟨a, this⟩

/-- Collision case: `e₁₃ = 0` and `e₂₃ = 0` collapses `A₁` to a single digit,
giving `apLen A₁ ≤ 1` and `apLen A₄ ≤ 4`, so `1 + 4 = 5 ≤ 5`. -/
private theorem c65_case_collision {m : ℕ} (hm : 0 < m) {A1 A4 : Finset ℕ}
    (hpos : ∀ d ∈ A1 ∪ A4, 0 < d)
    (hunit : ∀ d ∈ A1 ∪ A4, padicValNat 7 d = 0)
    {s : ZMod 7} (hs : s ≠ 0)
    (hcls1 : ∀ d ∈ A1, runit7 d = s)
    (hcls4 : ∀ d ∈ A4, runit7 d = 4 * s)
    {d1 d2 d3 : ℕ} (hA1eq : A1 = {d1, d2, d3})
    {d4 d5 : ℕ} (hA4eq : A4 = {d4, d5})
    (he13 : eMod7 m d1 d3 = 0) (he23 : eMod7 m d2 d3 = 0) :
    ∃ lam : ℕ, ¬ 7 ∣ lam ∧ good7 m lam (A1 ∪ A4) := by
  have hd1mem : d1 ∈ A1 := by rw [hA1eq]; exact Finset.mem_insert_self _ _
  have hd2mem : d2 ∈ A1 := by
    rw [hA1eq]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hd3mem : d3 ∈ A1 := by
    rw [hA1eq]; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have hr1 : runit7 d1 = s := hcls1 d1 hd1mem
  have hr2 : runit7 d2 = s := hcls1 d2 hd2mem
  have hr3 : runit7 d3 = s := hcls1 d3 hd3mem
  have hrel13 : residueRelOf d1 d3 = residueRel.same :=
    rel_same (by rw [hr1, hr3]) (by rw [hr3]; exact hs)
  have hrel23 : residueRelOf d2 d3 = residueRel.same :=
    rel_same (by rw [hr2, hr3]) (by rw [hr3]; exact hs)
  have hq13 : qdig7 m d1 = qdig7 m d3 :=
    qdig7_congr (eq_resid_of_eMod7_eq_zero he13 hrel13)
  have hq23 : qdig7 m d2 = qdig7 m d3 :=
    qdig7_congr (eq_resid_of_eMod7_eq_zero he23 hrel23)
  have hsub1 : (A1.image (fun d => 1 * d)).image (qdig7 m)
      ⊆ cycIv (qdig7 m d3) 1 := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hy
    rw [hA1eq] at hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rw [one_mul]
    rcases hd with rfl | rfl | rfl
    · rw [mem_cycIv, hq13, sub_self, ZMod.val_zero]; omega
    · rw [mem_cycIv, hq23, sub_self, ZMod.val_zero]; omega
    · rw [mem_cycIv, sub_self, ZMod.val_zero]; omega
  have hap1 : apLen ((A1.image (fun d => 1 * d)).image (qdig7 m)) ≤ 1 :=
    (apLen_le_iff _ 1 (by norm_num)).mpr ⟨_, hsub1⟩
  have hap4 : apLen ((A4.image (fun d => 1 * d)).image (qdig7 m)) ≤ 4 := by
    have heq : (A4.image (fun d => 1 * d)).image (qdig7 m)
        = ({qdig7 m d4, qdig7 m d5} : Finset (ZMod 7)) := by
      rw [hA4eq]
      simp only [Finset.image_insert, Finset.image_singleton, one_mul]
    rw [heq]
    exact apLen_two_le4 _ _
  have hsum : apLen ((A1.image (fun d => 1 * d)).image (qdig7 m)) +
      apLen ((A4.image (fun d => 1 * d)).image (qdig7 m)) ≤ 5 := by omega
  exact c65_finish hm hpos hunit hs hcls1 hcls4 (by decide) (Or.inr (Or.inr hsum))

/-- `e₁₃ = 0` subcase: `d₁ ≡ d₃ mod N` collapses `A₁` to at most two points,
hence `apLen A₁ ≤ 4` for all multipliers.  We select `lam₁` to set `apLen A₄ ≤ 2`. -/
private theorem c65_case_e13_zero {m : ℕ} (hm : 0 < m) {A1 A4 : Finset ℕ}
    (hpos : ∀ d ∈ A1 ∪ A4, 0 < d)
    (hunit : ∀ d ∈ A1 ∪ A4, padicValNat 7 d = 0)
    {s : ZMod 7} (hs : s ≠ 0)
    (hcls1 : ∀ d ∈ A1, runit7 d = s)
    (hcls4 : ∀ d ∈ A4, runit7 d = 4 * s)
    {d1 d2 d3 : ℕ} (hA1eq : A1 = {d1, d2, d3})
    {d4 d5 : ℕ} (hA4eq : A4 = {d4, d5})
    (he13 : eMod7 m d1 d3 = 0) :
    ∃ lam : ℕ, ¬ 7 ∣ lam ∧ good7 m lam (A1 ∪ A4) := by
  have hd1mem : d1 ∈ A1 := by rw [hA1eq]; exact Finset.mem_insert_self _ _
  have hd3mem : d3 ∈ A1 := by
    rw [hA1eq]; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have hr1 : runit7 d1 = s := hcls1 d1 hd1mem
  have hr3 : runit7 d3 = s := hcls1 d3 hd3mem
  have hrel13 : residueRelOf d1 d3 = residueRel.same :=
    rel_same (by rw [hr1, hr3]) (by rw [hr3]; exact hs)
  have hd13res : d1 % 7 ^ (m + 1) = d3 % 7 ^ (m + 1) :=
    eq_resid_of_eMod7_eq_zero he13 hrel13
  have hq13L : ∀ lam₁ : ℕ, qdig7 m (lam₁ * d1) = qdig7 m (lam₁ * d3) := by
    intro lam₁
    apply qdig7_congr
    rw [Nat.mul_mod, hd13res, ← Nat.mul_mod]
  have hap1L : ∀ lam₁ : ℕ,
      apLen ((A1.image (fun d => lam₁ * d)).image (qdig7 m)) ≤ 4 := by
    intro lam₁
    have heq : (A1.image (fun d => lam₁ * d)).image (qdig7 m)
        = ({qdig7 m (lam₁ * d2), qdig7 m (lam₁ * d3)} : Finset (ZMod 7)) := by
      rw [hA1eq]
      simp only [Finset.image_insert, Finset.image_singleton]
      rw [hq13L lam₁]
      ext z
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
    rw [heq]
    exact apLen_two_le4 _ _
  have hd4mem : d4 ∈ A4 := by rw [hA4eq]; exact Finset.mem_insert_self _ _
  have hd5mem : d5 ∈ A4 := by
    rw [hA4eq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hr4 : runit7 d4 = 4 * s := hcls4 d4 hd4mem
  have hr5 : runit7 d5 = 4 * s := hcls4 d5 hd5mem
  have hrel45 : residueRelOf d4 d5 = residueRel.same :=
    rel_same (by rw [hr4, hr5]) (by rw [hr5]; exact mul_ne_zero (by decide) hs)
  by_cases he45 : eMod7 m d4 d5 = 0
  · -- `e₄₅ = 0`: use `lam₁ = 1`
    have hq45 : qdig7 m d4 = qdig7 m d5 :=
      qdig7_congr (eq_resid_of_eMod7_eq_zero he45 hrel45)
    have hap4 : apLen ((A4.image (fun d => 1 * d)).image (qdig7 m)) ≤ 2 := by
      have heq : (A4.image (fun d => 1 * d)).image (qdig7 m)
          = ({qdig7 m d5} : Finset (ZMod 7)) := by
        rw [hA4eq]
        simp only [Finset.image_insert, Finset.image_singleton, one_mul, hq45]
        ext z; simp
      rw [heq]
      have : apLen ({qdig7 m d5} : Finset (ZMod 7)) ≤ 1 := apLen_singleton_le1 _
      omega
    exact c65_finish hm hpos hunit hs hcls1 hcls4 (by decide)
      (Or.inr (Or.inl ⟨hap1L 1, hap4⟩))
  · -- `e₄₅ ≠ 0`
    by_cases hν45m : padicValNat 7 (eMod7 m d4 d5) < m
    · obtain ⟨k, hk7, hkq⟩ :=
        exists_multLow_set_qdig hν45m rfl he45 0
      set lam₁ := 1 + k * 7 ^ (m - padicValNat 7 (eMod7 m d4 d5))
      have hlam₁r : runit7 lam₁ = 1 := runit7_multLow hν45m
      have hlam₁7 : ¬ 7 ∣ lam₁ := multLow_not_dvd hν45m
      have hrel45' : residueRelOf (lam₁ * d4) (lam₁ * d5) = residueRel.same := by
        apply rel_same
        · rw [runit7_mul, runit7_mul, hr4, hr5]
        · rw [runit7_mul, hr5, hlam₁r, one_mul]
          exact mul_ne_zero (by decide) hs
      have hqe : qdig7 m (eMod7 m (lam₁ * d4) (lam₁ * d5)) = 0 := by
        rw [eMod7_mul hlam₁r, qdig7_congr (Nat.mod_mod _ _)]
        exact hkq
      have hap4 : apLen ((A4.image (fun d => lam₁ * d)).image (qdig7 m)) ≤ 2 := by
        have heq : (A4.image (fun d => lam₁ * d)).image (qdig7 m)
            = ({lam₁ * d4, lam₁ * d5} : Finset ℕ).image (qdig7 m) := by
          rw [hA4eq]
          simp only [Finset.image_insert, Finset.image_singleton]
        rw [heq]
        exact c65_pair_len2' hrel45' hqe
      exact c65_finish hm hpos hunit hs hcls1 hcls4 hlam₁7
        (Or.inr (Or.inl ⟨hap1L lam₁, hap4⟩))
    · -- `ν(e₄₅) = m`
      have hν45eq : padicValNat 7 (eMod7 m d4 d5) = m := by
        have hle : padicValNat 7 (eMod7 m d4 d5) ≤ m := enu7_le_of_ne he45
        omega
      obtain ⟨c, hc0, hc7, hce, hqc⟩ :=
        exists_top_scalar_set hν45eq he45 (by decide : (1 : ZMod 7) ≠ 0)
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
      have hrel45' : residueRelOf (c * d4) (c * d5) = residueRel.same :=
        rel_same (by rw [hsc d4, hsc d5, hr4, hr5])
          (by rw [hsc d5, hr5]; exact mul_ne_zero hc0z (mul_ne_zero (by decide) hs))
      have he45' : eMod7 m (c * d4) (c * d5) = (1 : ZMod 7).val * 7 ^ m := by
        rw [eMod7_smul hrc]; exact hce
      have hq45' : qdig7 m (c * d4) = qdig7 m (c * d5) + 1 :=
        qdig_eq_add_of_e_top hrel45' he45'
      have hap4 : apLen ((A4.image (fun d => c * d)).image (qdig7 m)) ≤ 2 := by
        have heq : (A4.image (fun d => c * d)).image (qdig7 m)
            = ({qdig7 m (c * d5) + 1, qdig7 m (c * d5)} : Finset (ZMod 7)) := by
          rw [hA4eq]
          simp only [Finset.image_insert, Finset.image_singleton, hq45']
        rw [heq]
        have hsub : ({qdig7 m (c * d5) + 1, qdig7 m (c * d5)} : Finset (ZMod 7))
            ⊆ cycIv (qdig7 m (c * d5)) 2 := by
          intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl
          · rw [mem_cycIv, add_sub_cancel_left]; decide
          · rw [mem_cycIv, sub_self, ZMod.val_zero]; omega
        exact (apLen_le_iff _ 2 (by norm_num)).mpr ⟨_, hsub⟩
      exact c65_finish hm hpos hunit hs hcls1 hcls4 hcl
        (Or.inr (Or.inl ⟨hap1L c, hap4⟩))

/-- Finite check: in the boundary case, `×2` on `{q₃+1, q₂, q₃}` with borrow-monotonic carries
yields `apLen ≤ 3`. -/
private theorem c65_boundary_dec2 :
    ∀ q3 : ZMod 7, ∀ q2 : ZMod 7, ∀ c3 c2 : Fin 2,
      (q2 = q3 ∨ q2 = q3 + 1) →
      (q2 = q3 → c3.val ≤ c2.val) →
      (q2 = q3 + 1 → c2.val ≤ c3.val) →
      apLen ({2 * (q3 + 1) + ((c3 : ℕ) : ZMod 7),
              2 * q2 + ((c2 : ℕ) : ZMod 7),
              2 * q3 + ((c3 : ℕ) : ZMod 7)} : Finset (ZMod 7)) ≤ 3 := by
  decide

/-- Finite check: in the boundary case, `×3` on `{q₃+1, q₂, q₃}` with borrow-monotonic carries
yields `apLen ≤ 4`. -/
private theorem c65_boundary_dec3 :
    ∀ q3 : ZMod 7, ∀ q2 : ZMod 7, ∀ c3 c2 : Fin 3,
      (q2 = q3 ∨ q2 = q3 + 1) →
      (q2 = q3 → c3.val ≤ c2.val) →
      (q2 = q3 + 1 → c2.val ≤ c3.val) →
      apLen ({3 * (q3 + 1) + ((c3 : ℕ) : ZMod 7),
              3 * q2 + ((c2 : ℕ) : ZMod 7),
              3 * q3 + ((c3 : ℕ) : ZMod 7)} : Finset (ZMod 7)) ≤ 4 := by
  decide

/-- Finite check: in Case (ii.1) with `h = m` and `e₄₅ = 4·7^m`, either some `Λ₀` shift `k`
avoids `{0,6}` on `cycIv 3 ∪ {c, c+4}`, or multiplier 5 avoids `{0,6}` directly. -/
private theorem c65_bad_i_dec :
    ∀ c : ZMod 7,
      (∃ k : ZMod 7, avoids06 (cycIv (1 + k) 3 ∪ ({4 * k + c, 4 * k + c + 4} : Finset (ZMod 7)))) ∨
      avoids06 ((cycIv 1 3).image (5 * ·) ∪ ({5 * c, 5 * (c + 4)} : Finset (ZMod 7))) := by
  decide

/-- Finite check: for any non-zero residue `r`, there exists a scalar `s ∈ {1, 2, 3}`
such that `s * r ∈ {1, 6}` and for every base digit `q`, `apLen {q, q + s, q + 3s} ≤ 4`. -/
private theorem c65_scalar_for_top (r : ZMod 7) (hr : r ≠ 0) :
    ∃ s : Fin 3,
      let sv : ℕ := s.val + 1
      ((sv : ZMod 7) * r = 1 ∨ (sv : ZMod 7) * r = 6) ∧
      ∀ q : ZMod 7, apLen ({q, q + (sv : ZMod 7), q + (sv : ZMod 7) * 3} : Finset (ZMod 7)) ≤ 4 := by
  revert r
  decide

/-- Case (ii.1) with `h < m`: `lemma9_ii` (`j = 2`) on the swap `(d₂, d₁, d₃)` produces
`apLen ≤ 2` and `{0,6}` difference digits on `A₁`, discharging via `c65_finish_of_pair06`. -/
private theorem c65_case_ii1_low {m : ℕ} (hm : 0 < m) {A1 A4 : Finset ℕ}
    (hpos : ∀ d ∈ A1 ∪ A4, 0 < d)
    (hunit : ∀ d ∈ A1 ∪ A4, padicValNat 7 d = 0)
    {s : ZMod 7} (hs : s ≠ 0)
    (hcls1 : ∀ d ∈ A1, runit7 d = s)
    (hcls4 : ∀ d ∈ A4, runit7 d = 4 * s)
    {d1 d2 d3 : ℕ} (hA1eq : A1 = {d1, d2, d3})
    {d4 d5 : ℕ} (hA4eq : A4 = {d4, d5})
    (he13 : eMod7 m d1 d3 ≠ 0) (he23 : eMod7 m d2 d3 ≠ 0)
    (hlevel : elevel7 m d1 d3 = elevel7 m d2 d3)
    (hrat : runit7 (eMod7 m d1 d3) = 2 * runit7 (eMod7 m d2 d3))
    (hlm : padicValNat 7 (eMod7 m d2 d3) < m) :
    ∃ lam : ℕ, ¬ 7 ∣ lam ∧ good7 m lam (A1 ∪ A4) := by
  have hd1mem : d1 ∈ A1 := by rw [hA1eq]; exact Finset.mem_insert_self _ _
  have hd2mem : d2 ∈ A1 := by
    rw [hA1eq]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hd3mem : d3 ∈ A1 := by
    rw [hA1eq]; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have hp1 : 0 < d1 := hpos d1 (Finset.mem_union_left _ hd1mem)
  have hp2 : 0 < d2 := hpos d2 (Finset.mem_union_left _ hd2mem)
  have hp3 : 0 < d3 := hpos d3 (Finset.mem_union_left _ hd3mem)
  have hu1 : padicValNat 7 d1 = 0 := hunit d1 (Finset.mem_union_left _ hd1mem)
  have hu2 : padicValNat 7 d2 = 0 := hunit d2 (Finset.mem_union_left _ hd2mem)
  have hu3 : padicValNat 7 d3 = 0 := hunit d3 (Finset.mem_union_left _ hd3mem)
  have hr1 : runit7 d1 = s := hcls1 d1 hd1mem
  have hr2 : runit7 d2 = s := hcls1 d2 hd2mem
  have hr3 : runit7 d3 = s := hcls1 d3 hd3mem
  have hν13 : padicValNat 7 (eMod7 m d1 d3) = elevel7 m d1 d3 := (elevel7_of_ne he13).symm
  have hν23 : padicValNat 7 (eMod7 m d2 d3) = elevel7 m d2 d3 := (elevel7_of_ne he23).symm
  have hνeq : padicValNat 7 (eMod7 m d2 d3) = padicValNat 7 (eMod7 m d1 d3) := by
    rw [hν23, hν13, hlevel]
  have hset_eq : ({d2, d1, d3} : Finset ℕ) = ({d1, d2, d3} : Finset ℕ) := by
    ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  obtain ⟨lam, hlam7, _, _, hpair06, hlen⟩ := lemma9_ii
    ⟨hp2, hp1, hp3⟩ ⟨hu2, hu1, hu3⟩ ⟨hr2.trans hr1.symm, hr1.trans hr3.symm⟩
    hνeq (hνeq ▸ hlm) (Or.inl rfl) (by simpa using hrat)
  have himg : (A1.image (fun d => lam * d)).image (qdig7 m)
      = ({d2, d1, d3} : Finset ℕ).image (fun d => qdig7 m (lam * d)) := by
    rw [hA1eq, hset_eq, Finset.image_image]; rfl
  have hlen2 : apLen ((A1.image (fun d => lam * d)).image (qdig7 m)) ≤ 2 := by
    rw [himg]; exact hlen
  have hB : ∀ x ∈ ({d1, d2, d3} : Finset ℕ), ∀ y ∈ ({d1, d2, d3} : Finset ℕ),
      qdig7 m (eMod7 m (lam * x) (lam * y)) ∈ ({0, 6} : Finset (ZMod 7)) := by
    intro x hx y hy
    rw [← hset_eq] at hx hy
    exact hpair06 rfl x hx y hy
  exact c65_finish_of_pair06 hm hpos hunit hs hcls1 hcls4 hA1eq hA4eq hlam7 hlen2 hB

/-- Boundary rescue-dispatch: if `lam₁` achieves the boundary digit configuration on `A₁`
(i.e. `q(d₁) = q(d₃) + 1`, equal low parts, and `q(d₂) ∈ {q(d₃), q(d₃)+1}` with borrow monotonicity),
then either `lam₁` or `2 * lam₁` or `3 * lam₁` produces an admissible shape for `c65_finish`. -/
private theorem c65_finish_of_boundary {m : ℕ} (hm : 0 < m) {A1 A4 : Finset ℕ}
    (hpos : ∀ d ∈ A1 ∪ A4, 0 < d)
    (hunit : ∀ d ∈ A1 ∪ A4, padicValNat 7 d = 0)
    {s : ZMod 7} (hs : s ≠ 0)
    (hcls1 : ∀ d ∈ A1, runit7 d = s)
    (hcls4 : ∀ d ∈ A4, runit7 d = 4 * s)
    {d1 d2 d3 : ℕ} (hA1eq : A1 = {d1, d2, d3})
    {d4 d5 : ℕ} (hA4eq : A4 = {d4, d5})
    {lam₁ : ℕ} (hlam₁ : ¬ 7 ∣ lam₁)
    (hq1 : qdig7 m (lam₁ * d1) = qdig7 m (lam₁ * d3) + 1)
    (hlow1 : (lam₁ * d1) % 7 ^ m = (lam₁ * d3) % 7 ^ m)
    (hq2 : qdig7 m (lam₁ * d2) = qdig7 m (lam₁ * d3) ∨
           qdig7 m (lam₁ * d2) = qdig7 m (lam₁ * d3) + 1)
    (hmono : (qdig7 m (lam₁ * d2) = qdig7 m (lam₁ * d3) →
              (lam₁ * d3) % 7 ^ m ≤ (lam₁ * d2) % 7 ^ m) ∧
             (qdig7 m (lam₁ * d2) = qdig7 m (lam₁ * d3) + 1 →
              (lam₁ * d2) % 7 ^ m ≤ (lam₁ * d3) % 7 ^ m)) :
    ∃ lam : ℕ, ¬ 7 ∣ lam ∧ good7 m lam (A1 ∪ A4) := by
  set x' := lam₁ * d4
  set y' := lam₁ * d5
  have hd4 : d4 ∈ A4 := by rw [hA4eq]; exact Finset.mem_insert_self _ _
  have hd5 : d5 ∈ A4 := by
    rw [hA4eq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hr4 : runit7 d4 = 4 * s := hcls4 d4 hd4
  have hr5 : runit7 d5 = 4 * s := hcls4 d5 hd5
  have hlam₁0 : lam₁ ≠ 0 := fun h => hlam₁ (h ▸ dvd_zero _)
  have hrl1 : runit7 lam₁ ≠ 0 := runit7_ne_zero (Nat.pos_of_ne_zero hlam₁0)
  have hrx' : runit7 x' = runit7 lam₁ * (4 * s) := by
    dsimp [x']; rw [runit7_mul, hr4]
  have hry' : runit7 y' = runit7 lam₁ * (4 * s) := by
    dsimp [y']; rw [runit7_mul, hr5]
  have hry'0 : runit7 y' ≠ 0 := by
    rw [hry']
    exact mul_ne_zero hrl1 (mul_ne_zero (by decide) hs)
  have hrel' : residueRelOf x' y' = residueRel.same :=
    rel_same (by rw [hrx', hry']) hry'0
  have hA4img : (A4.image (fun d => lam₁ * d)).image (qdig7 m)
      = ({x', y'} : Finset ℕ).image (qdig7 m) := by
    rw [hA4eq]
    simp only [Finset.image_insert, Finset.image_singleton]
    rfl
  have hap1_base : apLen ((A1.image (fun d => lam₁ * d)).image (qdig7 m)) ≤ 2 := by
    have heq : (A1.image (fun d => lam₁ * d)).image (qdig7 m)
        ⊆ cycIv (qdig7 m (lam₁ * d3)) 2 := by
      intro z hz
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hw
      rw [hA1eq] at hd
      simp only [Finset.mem_insert, Finset.mem_singleton] at hd
      rcases hd with rfl | rfl | rfl
      · rw [mem_cycIv, hq1, add_sub_cancel_left]; decide
      · rw [mem_cycIv]
        rcases hq2 with hq2a | hq2b
        · rw [hq2a, sub_self, ZMod.val_zero]; omega
        · rw [hq2b, add_sub_cancel_left]; decide
      · rw [mem_cycIv, sub_self, ZMod.val_zero]; omega
    exact (apLen_le_iff _ 2 (by norm_num)).mpr ⟨_, heq⟩
  by_cases hbad : qdig7 m (eMod7 m x' y') ∈ ({2, 3, 4} : Finset (ZMod 7))
  · rcases c65_a4_rescue hrel' (by rw [hrx', hry']) hry'0 hbad with h2 | h3
    · -- ×2 branch
      set lam₂ := 2 * lam₁
      have hlam₂ : ¬ 7 ∣ lam₂ := Nat.prime_seven.not_dvd_mul (by decide) hlam₁
      have h2x' : lam₂ * d4 = 2 * x' := by dsimp [x', lam₂]; ring
      have h2y' : lam₂ * d5 = 2 * y' := by dsimp [y', lam₂]; ring
      have hA4img2 : (A4.image (fun d => lam₂ * d)).image (qdig7 m)
          = ({x', y'} : Finset ℕ).image (fun b => qdig7 m (2 * b)) := by
        rw [hA4eq]
        simp only [Finset.image_insert, Finset.image_singleton, h2x', h2y']
      have hap4 : apLen ((A4.image (fun d => lam₂ * d)).image (qdig7 m)) ≤ 3 := by
        rw [hA4img2]; exact h2
      set q3 := qdig7 m (lam₁ * d3)
      set q2 := qdig7 m (lam₁ * d2)
      have hP : 0 < 7 ^ m := Nat.pow_pos (by norm_num)
      have hc3lt : (2 * ((lam₁ * d3) % 7 ^ m)) / 7 ^ m < 2 :=
        Nat.div_lt_of_lt_mul (by rw [mul_comm (7 ^ m) 2]; exact Nat.mul_lt_mul_of_pos_left (Nat.mod_lt _ hP) (by decide : 0 < 2))
      have hc2lt : (2 * ((lam₁ * d2) % 7 ^ m)) / 7 ^ m < 2 :=
        Nat.div_lt_of_lt_mul (by rw [mul_comm (7 ^ m) 2]; exact Nat.mul_lt_mul_of_pos_left (Nat.mod_lt _ hP) (by decide : 0 < 2))
      set C3 : Fin 2 := ⟨(2 * ((lam₁ * d3) % 7 ^ m)) / 7 ^ m, hc3lt⟩
      set C2 : Fin 2 := ⟨(2 * ((lam₁ * d2) % 7 ^ m)) / 7 ^ m, hc2lt⟩
      have hdec := c65_boundary_dec2 q3 q2 C3 C2 hq2
        (fun h => by
          dsimp [C3, C2]
          have hle := hmono.1 h
          exact Nat.div_le_div_right (Nat.mul_le_mul_left 2 hle))
        (fun h => by
          dsimp [C3, C2]
          have hle := hmono.2 h
          exact Nat.div_le_div_right (Nat.mul_le_mul_left 2 hle))
      have hq2d1 : qdig7 m (lam₂ * d1) = 2 * (q3 + 1) + ((C3 : ℕ) : ZMod 7) := by
        have heq : lam₂ * d1 = 2 * (lam₁ * d1) := by dsimp [lam₂]; ring
        rw [heq, qdig7_smul_eq (by decide : 0 < 2), hq1, hlow1]
        rfl
      have hq2d2 : qdig7 m (lam₂ * d2) = 2 * q2 + ((C2 : ℕ) : ZMod 7) := by
        have heq : lam₂ * d2 = 2 * (lam₁ * d2) := by dsimp [lam₂]; ring
        rw [heq, qdig7_smul_eq (by decide : 0 < 2)]
        rfl
      have hq2d3 : qdig7 m (lam₂ * d3) = 2 * q3 + ((C3 : ℕ) : ZMod 7) := by
        have heq : lam₂ * d3 = 2 * (lam₁ * d3) := by dsimp [lam₂]; ring
        rw [heq, qdig7_smul_eq (by decide : 0 < 2)]
        rfl
      have hA1img2 : (A1.image (fun d => lam₂ * d)).image (qdig7 m)
          = ({2 * (q3 + 1) + ((C3 : ℕ) : ZMod 7),
              2 * q2 + ((C2 : ℕ) : ZMod 7),
              2 * q3 + ((C3 : ℕ) : ZMod 7)} : Finset (ZMod 7)) := by
        rw [hA1eq]
        simp only [Finset.image_insert, Finset.image_singleton, hq2d1, hq2d2, hq2d3]
      have hap1 : apLen ((A1.image (fun d => lam₂ * d)).image (qdig7 m)) ≤ 3 := by
        rw [hA1img2]; exact hdec
      exact c65_finish hm hpos hunit hs hcls1 hcls4 hlam₂ (Or.inl ⟨hap1, hap4⟩)
    · -- ×3 branch
      set lam₃ := 3 * lam₁
      have hlam₃ : ¬ 7 ∣ lam₃ := Nat.prime_seven.not_dvd_mul (by decide) hlam₁
      have h3x' : lam₃ * d4 = 3 * x' := by dsimp [x', lam₃]; ring
      have h3y' : lam₃ * d5 = 3 * y' := by dsimp [y', lam₃]; ring
      have hA4img3 : (A4.image (fun d => lam₃ * d)).image (qdig7 m)
          = ({x', y'} : Finset ℕ).image (fun b => qdig7 m (3 * b)) := by
        rw [hA4eq]
        simp only [Finset.image_insert, Finset.image_singleton, h3x', h3y']
      have hap4 : apLen ((A4.image (fun d => lam₃ * d)).image (qdig7 m)) ≤ 2 := by
        rw [hA4img3]; exact h3
      set q3 := qdig7 m (lam₁ * d3)
      set q2 := qdig7 m (lam₁ * d2)
      have hP : 0 < 7 ^ m := Nat.pow_pos (by norm_num)
      have hc3lt : (3 * ((lam₁ * d3) % 7 ^ m)) / 7 ^ m < 3 :=
        Nat.div_lt_of_lt_mul (by rw [mul_comm (7 ^ m) 3]; exact Nat.mul_lt_mul_of_pos_left (Nat.mod_lt _ hP) (by decide : 0 < 3))
      have hc2lt : (3 * ((lam₁ * d2) % 7 ^ m)) / 7 ^ m < 3 :=
        Nat.div_lt_of_lt_mul (by rw [mul_comm (7 ^ m) 3]; exact Nat.mul_lt_mul_of_pos_left (Nat.mod_lt _ hP) (by decide : 0 < 3))
      set C3 : Fin 3 := ⟨(3 * ((lam₁ * d3) % 7 ^ m)) / 7 ^ m, hc3lt⟩
      set C2 : Fin 3 := ⟨(3 * ((lam₁ * d2) % 7 ^ m)) / 7 ^ m, hc2lt⟩
      have hdec := c65_boundary_dec3 q3 q2 C3 C2 hq2
        (fun h => by
          dsimp [C3, C2]
          have hle := hmono.1 h
          exact Nat.div_le_div_right (Nat.mul_le_mul_left 3 hle))
        (fun h => by
          dsimp [C3, C2]
          have hle := hmono.2 h
          exact Nat.div_le_div_right (Nat.mul_le_mul_left 3 hle))
      have hq3d1 : qdig7 m (lam₃ * d1) = 3 * (q3 + 1) + ((C3 : ℕ) : ZMod 7) := by
        have heq : lam₃ * d1 = 3 * (lam₁ * d1) := by dsimp [lam₃]; ring
        rw [heq, qdig7_smul_eq (by decide : 0 < 3), hq1, hlow1]
        rfl
      have hq3d2 : qdig7 m (lam₃ * d2) = 3 * q2 + ((C2 : ℕ) : ZMod 7) := by
        have heq : lam₃ * d2 = 3 * (lam₁ * d2) := by dsimp [lam₃]; ring
        rw [heq, qdig7_smul_eq (by decide : 0 < 3)]
        rfl
      have hq3d3 : qdig7 m (lam₃ * d3) = 3 * q3 + ((C3 : ℕ) : ZMod 7) := by
        have heq : lam₃ * d3 = 3 * (lam₁ * d3) := by dsimp [lam₃]; ring
        rw [heq, qdig7_smul_eq (by decide : 0 < 3)]
        rfl
      have hA1img3 : (A1.image (fun d => lam₃ * d)).image (qdig7 m)
          = ({3 * (q3 + 1) + ((C3 : ℕ) : ZMod 7),
              3 * q2 + ((C2 : ℕ) : ZMod 7),
              3 * q3 + ((C3 : ℕ) : ZMod 7)} : Finset (ZMod 7)) := by
        rw [hA1eq]
        simp only [Finset.image_insert, Finset.image_singleton, hq3d1, hq3d2, hq3d3]
      have hap1 : apLen ((A1.image (fun d => lam₃ * d)).image (qdig7 m)) ≤ 4 := by
        rw [hA1img3]; exact hdec
      exact c65_finish hm hpos hunit hs hcls1 hcls4 hlam₃ (Or.inr (Or.inl ⟨hap1, hap4⟩))
  · have hgood : qdig7 m (eMod7 m x' y') ∈ ({0, 1, 5, 6} : Finset (ZMod 7)) :=
      mem_0156_of_not_234 hbad
    have hap4 : apLen (({x', y'} : Finset ℕ).image (qdig7 m)) ≤ 3 :=
      c65_pair_len3 hrel' hgood
    rw [← hA4img] at hap4
    have hshape : apLen ((A1.image (fun d => lam₁ * d)).image (qdig7 m)) ≤ 3 ∧
        apLen ((A4.image (fun d => lam₁ * d)).image (qdig7 m)) ≤ 3 :=
      ⟨le_trans hap1_base (by norm_num), hap4⟩
    exact c65_finish hm hpos hunit hs hcls1 hcls4 hlam₁ (Or.inl hshape)

/-- `q(w + 7^m) = q(w) + 1`: adding `7^m` bumps the leading digit exactly. -/
private theorem qdig7_add_pow (m w : ℕ) :
    qdig7 m (w + 7 ^ m) = qdig7 m w + 1 := by
  rw [qdig7_eq_cast_div, qdig7_eq_cast_div]
  have hdiv : (w + 7 ^ m) / 7 ^ m = w / 7 ^ m + 1 := by
    conv_lhs => rw [show w + 7 ^ m = w + 7 ^ m * 1 by rw [mul_one]]
    exact Nat.add_mul_div_left _ _ (Nat.pow_pos (by norm_num))
  rw [hdiv]
  push_cast
  ring

/-- Division of a sum: `(a + b)/c = a/c + b/c + carry` with `carry = (a%c + b%c)/c`. -/
private theorem add_div_carry7 (a b c : ℕ) (hc : 0 < c) :
    (a + b) / c = a / c + b / c + (a % c + b % c) / c := by
  have h1 : a + b = a % c + b % c + c * (a / c + b / c) := by
    have hda := Nat.div_add_mod a c
    have hdb := Nat.div_add_mod b c
    have hmul : c * (a / c) + c * (b / c) = c * (a / c + b / c) := by ring
    omega
  rw [h1, Nat.add_mul_div_left _ _ hc]
  ring

/-- Boundary multiplier construction: when `ν₁₃ = m` and `ν₂₃ < m`, there exists a multiplier
`lam₁` satisfying the hypotheses of `c65_finish_of_boundary`. -/
private theorem c65_boundary_lam {m : ℕ} (hm : 0 < m) {d1 d2 d3 : ℕ}
    (hp1 : 0 < d1) (hp2 : 0 < d2) (hp3 : 0 < d3)
    (hu1 : padicValNat 7 d1 = 0) (hu2 : padicValNat 7 d2 = 0) (hu3 : padicValNat 7 d3 = 0)
    {s : ZMod 7} (hs : s ≠ 0)
    (hr1 : runit7 d1 = s) (hr2 : runit7 d2 = s) (hr3 : runit7 d3 = s)
    (he13 : eMod7 m d1 d3 ≠ 0) (he23 : eMod7 m d2 d3 ≠ 0)
    (hν13 : padicValNat 7 (eMod7 m d1 d3) = m)
    (hν23 : padicValNat 7 (eMod7 m d2 d3) < m) :
    ∃ lam₁ : ℕ, ¬ 7 ∣ lam₁ ∧
      qdig7 m (lam₁ * d1) = qdig7 m (lam₁ * d3) + 1 ∧
      (qdig7 m (lam₁ * d2) = qdig7 m (lam₁ * d3) ∨
       qdig7 m (lam₁ * d2) = qdig7 m (lam₁ * d3) + 1) ∧
      (lam₁ * d1) % 7 ^ m = (lam₁ * d3) % 7 ^ m ∧
      ((qdig7 m (lam₁ * d2) = qdig7 m (lam₁ * d3) →
        (lam₁ * d3) % 7 ^ m ≤ (lam₁ * d2) % 7 ^ m) ∧
       (qdig7 m (lam₁ * d2) = qdig7 m (lam₁ * d3) + 1 →
        (lam₁ * d2) % 7 ^ m ≤ (lam₁ * d3) % 7 ^ m)) := by
  classical
  set x := eMod7 m d1 d3 with hx
  set y := eMod7 m d2 d3 with hy
  obtain ⟨c, hc0, hc7, hcx_res, hcx_q⟩ :=
    exists_top_scalar_set hν13 he13 ((by decide) : (1 : ZMod 7) ≠ 0)
  have hc_ne7 : ¬ 7 ∣ c := fun hd =>
    (ne_of_gt hc0) (Nat.eq_zero_of_dvd_of_lt hd hc7)
  have hcx_res' : (c * x) % 7 ^ (m + 1) = 7 ^ m := by
    rw [hcx_res]
    have : (1 : ZMod 7).val = 1 := by decide
    rw [this, one_mul]
  have hcxν : padicValNat 7 (c * x) = m := by
    rw [padicValNat_mul_seven hc_ne7 he13, hν13]
  have hcyν : padicValNat 7 (c * y) = padicValNat 7 y := by
    rw [padicValNat_mul_seven hc_ne7 he23]
  have hcy0 : c * y ≠ 0 := mul_ne_zero (ne_of_gt hc0) he23
  obtain ⟨k, hk7, hlam₂q⟩ := exists_multLow_set_qdig hν23 hcyν hcy0 0
  set lam₂ := 1 + k * 7 ^ (m - padicValNat 7 y) with hlam₂def
  set lam := lam₂ * c with hlamdef
  clear_value lam
  have hlam₂mem : lam₂ ∈ multLow7 m (padicValNat 7 y) := by
    rw [hlam₂def]; exact mem_multLow7 hk7
  have hlam₂7 : ¬ 7 ∣ lam₂ := not_dvd_of_mem_multLow7 hν23 hlam₂mem
  have hlam7 : ¬ 7 ∣ lam := by
    intro hd
    rw [hlamdef] at hd
    rcases (Nat.Prime.dvd_mul Nat.prime_seven).mp hd with h | h
    · exact hlam₂7 h
    · exact hc_ne7 h
  have hlamx_res : (lam * x) % 7 ^ (m + 1) = 7 ^ m := by
    have hres := residN_multLow7 (j := padicValNat 7 y) (k := k) (x := c * x)
      hν23 (by rw [hcxν]; exact hν23)
    have heq : lam * x = lam₂ * (c * x) := by rw [hlamdef]; ring
    rw [heq, hlam₂def, hres, hcx_res']
  have hlamy_q : qdig7 m (lam * y) = 0 := by
    have heq : lam * y = lam₂ * (c * y) := by rw [hlamdef]; ring
    rw [heq, hlam₂def, hlam₂q]
  set f := (lam * y) % 7 ^ (m + 1) with hfdef
  have hf_lt : f < 7 ^ m := by
    rw [hfdef]; exact resid_lt_of_qdig7_zero hlamy_q
  have hrel13 : residueRelOf d1 d3 = residueRel.same :=
    rel_same (by rw [hr1, hr3]) (by rw [hr3]; exact hs)
  have hrel23 : residueRelOf d2 d3 = residueRel.same :=
    rel_same (by rw [hr2, hr3]) (by rw [hr3]; exact hs)
  have hxcast : ((x : ℕ) : ZMod (7 ^ (m + 1))) = (d1 : ZMod _) - (d3 : ZMod _) := by
    rw [hx]; exact eMod7_zmod_cast_same hrel13
  have hycast : ((y : ℕ) : ZMod (7 ^ (m + 1))) = (d2 : ZMod _) - (d3 : ZMod _) := by
    rw [hy]; exact eMod7_zmod_cast_same hrel23
  have hlamx_cast : (lam : ZMod (7 ^ (m + 1))) * (x : ZMod _) = ((7 ^ m : ℕ) : ZMod _) := by
    have h := congrArg (Nat.cast : ℕ → ZMod (7 ^ (m + 1))) hlamx_res
    rw [ZMod.natCast_mod] at h
    rw [← Nat.cast_mul]
    exact h
  have hlamy_cast : (lam : ZMod (7 ^ (m + 1))) * (y : ZMod _) = (f : ZMod _) := by
    have h := ZMod.natCast_mod (lam * y) (7 ^ (m + 1))
    rw [← hfdef] at h
    rw [← Nat.cast_mul]
    exact h.symm
  have hb1_cast : ((lam * d1 : ℕ) : ZMod (7 ^ (m + 1))) = ((lam * d3 + 7 ^ m : ℕ) : ZMod _) := by
    have hkey : (lam : ZMod (7 ^ (m + 1))) * (d1 : ZMod _) =
        (lam : ZMod _) * (d3 : ZMod _) + ((7 ^ m : ℕ) : ZMod _) := by
      have hb1e : (d1 : ZMod (7 ^ (m + 1))) = (d3 : ZMod _) + (x : ZMod _) := by
        rw [hxcast]; ring
      rw [hb1e, mul_add, hlamx_cast]
    rw [Nat.cast_mul, hkey, Nat.cast_add, Nat.cast_mul]
  have hb1_mod : (lam * d1) % 7 ^ (m + 1) = (lam * d3 + 7 ^ m) % 7 ^ (m + 1) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mp hb1_cast
  have hq1 : qdig7 m (lam * d1) = qdig7 m (lam * d3) + 1 := by
    rw [qdig7_congr hb1_mod, qdig7_add_pow]
  have hP : 0 < 7 ^ m := Nat.pow_pos (by norm_num)
  have hlow1 : (lam * d1) % 7 ^ m = (lam * d3) % 7 ^ m := by
    have h1 := Nat.mod_mod_of_dvd (lam * d1) (Nat.pow_dvd_pow 7 (Nat.le_succ m))
    have h2 := Nat.mod_mod_of_dvd (lam * d3 + 7 ^ m) (Nat.pow_dvd_pow 7 (Nat.le_succ m))
    rw [hb1_mod] at h1
    rw [← h1, h2, Nat.add_mod, Nat.mod_self, add_zero, Nat.mod_mod]
  have hb2_cast : ((lam * d2 : ℕ) : ZMod (7 ^ (m + 1))) = ((lam * d3 + f : ℕ) : ZMod _) := by
    have hkey : (lam : ZMod (7 ^ (m + 1))) * (d2 : ZMod _) =
        (lam : ZMod _) * (d3 : ZMod _) + (f : ZMod _) := by
      have hb2e : (d2 : ZMod (7 ^ (m + 1))) = (d3 : ZMod _) + (y : ZMod _) := by
        rw [hycast]; ring
      rw [hb2e, mul_add, hlamy_cast]
    rw [Nat.cast_mul, hkey, Nat.cast_add, Nat.cast_mul]
  have hb2_mod : (lam * d2) % 7 ^ (m + 1) = (lam * d3 + f) % 7 ^ (m + 1) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mp hb2_cast
  have hlow2 : (lam * d2) % 7 ^ m = (lam * d3 + f) % 7 ^ m := by
    have h1 := Nat.mod_mod_of_dvd (lam * d2) (Nat.pow_dvd_pow 7 (Nat.le_succ m))
    have h2 := Nat.mod_mod_of_dvd (lam * d3 + f) (Nat.pow_dvd_pow 7 (Nat.le_succ m))
    rw [hb2_mod] at h1
    rw [← h1, ← h2]
  set carry := ((lam * d3) % 7 ^ m + f) / 7 ^ m with hcarrydef
  have hcarry_div : (lam * d3 + f) / 7 ^ m = (lam * d3) / 7 ^ m + carry := by
    have h := add_div_carry7 (lam * d3) f (7 ^ m) hP
    rwa [Nat.div_eq_of_lt hf_lt, add_zero, Nat.mod_eq_of_lt hf_lt] at h
  have hcarry_lt2 : carry < 2 := by
    rw [hcarrydef, Nat.div_lt_iff_lt_mul hP]
    have hlt := Nat.mod_lt (lam * d3) hP
    omega
  have hcarry_le1 : carry ≤ 1 := by omega
  have hq2_eq : qdig7 m (lam * d2) = qdig7 m (lam * d3) + (carry : ZMod 7) := by
    rw [qdig7_congr hb2_mod, qdig7_eq_cast_div, hcarry_div, Nat.cast_add,
      ← qdig7_eq_cast_div m (lam * d3)]
  have hq2 : qdig7 m (lam * d2) = qdig7 m (lam * d3) ∨
      qdig7 m (lam * d2) = qdig7 m (lam * d3) + 1 := by
    rw [hq2_eq]
    interval_cases carry
    · left; simp
    · right; simp
  have hmono : (qdig7 m (lam * d2) = qdig7 m (lam * d3) →
        (lam * d3) % 7 ^ m ≤ (lam * d2) % 7 ^ m) ∧
       (qdig7 m (lam * d2) = qdig7 m (lam * d3) + 1 →
        (lam * d2) % 7 ^ m ≤ (lam * d3) % 7 ^ m) := by
    constructor
    · intro hqeq
      have hc0 : carry = 0 := by
        rw [hq2_eq] at hqeq
        have hz : (carry : ZMod 7) = 0 := by linear_combination hqeq
        interval_cases carry
        · rfl
        · exfalso; revert hz; decide
      have hlt : (lam * d3) % 7 ^ m + f < 7 ^ m := by
        have hc_eq : ((lam * d3) % 7 ^ m + f) / 7 ^ m = 0 := hc0
        exact (Nat.div_eq_zero_iff.mp hc_eq).resolve_left (ne_of_gt hP)
      rw [hlow2]
      have heq : (lam * d3 + f) % 7 ^ m = (lam * d3) % 7 ^ m + f := by
        rw [Nat.add_mod, Nat.mod_eq_of_lt hf_lt, Nat.mod_eq_of_lt hlt]
      rw [heq]
      omega
    · intro hqeq
      have hc1 : carry = 1 := by
        rw [hq2_eq] at hqeq
        have hz : (carry : ZMod 7) = 1 := by linear_combination hqeq
        interval_cases carry
        · exfalso; revert hz; decide
        · rfl
      have hge : 7 ^ m ≤ (lam * d3) % 7 ^ m + f := by
        have hc_eq : ((lam * d3) % 7 ^ m + f) / 7 ^ m = 1 := hc1
        have h1le : 1 ≤ ((lam * d3) % 7 ^ m + f) / 7 ^ m := by omega
        have hmul := (Nat.le_div_iff_mul_le hP).mp h1le
        omega
      rw [hlow2]
      have heq : (lam * d3 + f) % 7 ^ m = (lam * d3) % 7 ^ m + f - 7 ^ m := by
        have hA : (lam * d3) % 7 ^ m + f - 7 ^ m < 7 ^ m := by
          have hlt := Nat.mod_lt (lam * d3) hP
          omega
        rw [Nat.add_mod, Nat.mod_eq_of_lt hf_lt]
        conv_lhs => rw [show (lam * d3) % 7 ^ m + f =
          ((lam * d3) % 7 ^ m + f - 7 ^ m) + 7 ^ m by omega]
        rw [Nat.add_mod, Nat.mod_self, add_zero, Nat.mod_mod, Nat.mod_eq_of_lt hA]
      rw [heq]
      omega
  exact ⟨lam, hlam7, hq1, hq2, hlow1, hmono⟩

/-- Case (i): `ℓ₁₃ > ℓ₂₃ = ℓ₁₂`. Discharges via `c65_case_e13_zero` (if `e₁₃ = 0`),
or `lemma9_i` + `c65_finish_of_pair06` (if `ν₁₃ < m`),
or `c65_boundary_lam` + `c65_finish_of_boundary` (if `ν₁₃ = m`). -/
private theorem c65_case_i {m : ℕ} (hm : 0 < m) {A1 A4 : Finset ℕ}
    (hpos : ∀ d ∈ A1 ∪ A4, 0 < d)
    (hunit : ∀ d ∈ A1 ∪ A4, padicValNat 7 d = 0)
    {s : ZMod 7} (hs : s ≠ 0)
    (hcls1 : ∀ d ∈ A1, runit7 d = s)
    (hcls4 : ∀ d ∈ A4, runit7 d = 4 * s)
    {d1 d2 d3 : ℕ} (hA1eq : A1 = {d1, d2, d3})
    {d4 d5 : ℕ} (hA4eq : A4 = {d4, d5})
    (hlgt : elevel7 m d1 d3 > elevel7 m d2 d3) :
    ∃ lam : ℕ, ¬ 7 ∣ lam ∧ good7 m lam (A1 ∪ A4) := by
  by_cases he13 : eMod7 m d1 d3 = 0
  · exact c65_case_e13_zero hm hpos hunit hs hcls1 hcls4 hA1eq hA4eq he13
  · have hl23 : elevel7 m d2 d3 ≤ m := by
      have := elevel7_le (m := m) (x := d1) (y := d3)
      omega
    have he23 : eMod7 m d2 d3 ≠ 0 := by
      intro h0
      rw [elevel7_of_eq h0] at hl23
      omega
    have hν13 : padicValNat 7 (eMod7 m d1 d3) = elevel7 m d1 d3 := (elevel7_of_ne he13).symm
    have hν23 : padicValNat 7 (eMod7 m d2 d3) = elevel7 m d2 d3 := (elevel7_of_ne he23).symm
    have hνne : padicValNat 7 (eMod7 m d1 d3) ≠ padicValNat 7 (eMod7 m d2 d3) := by
      rw [hν13, hν23]; exact ne_of_gt hlgt
    have h13le : padicValNat 7 (eMod7 m d1 d3) ≤ m := enu7_le_of_ne he13
    have hν23lt : padicValNat 7 (eMod7 m d2 d3) < m := by
      rw [hν23, hν13] at *
      omega
    have hd1mem : d1 ∈ A1 := by rw [hA1eq]; exact Finset.mem_insert_self _ _
    have hd2mem : d2 ∈ A1 := by rw [hA1eq]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    have hd3mem : d3 ∈ A1 := by rw [hA1eq]; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    have hp1 : 0 < d1 := hpos d1 (Finset.mem_union_left _ hd1mem)
    have hp2 : 0 < d2 := hpos d2 (Finset.mem_union_left _ hd2mem)
    have hp3 : 0 < d3 := hpos d3 (Finset.mem_union_left _ hd3mem)
    have hu1 : padicValNat 7 d1 = 0 := hunit d1 (Finset.mem_union_left _ hd1mem)
    have hu2 : padicValNat 7 d2 = 0 := hunit d2 (Finset.mem_union_left _ hd2mem)
    have hu3 : padicValNat 7 d3 = 0 := hunit d3 (Finset.mem_union_left _ hd3mem)
    have hr1 : runit7 d1 = s := hcls1 d1 hd1mem
    have hr2 : runit7 d2 = s := hcls1 d2 hd2mem
    have hr3 : runit7 d3 = s := hcls1 d3 hd3mem
    by_cases hν13lt : padicValNat 7 (eMod7 m d1 d3) < m
    · obtain ⟨lam, hlam7, hpair06, hlen⟩ := lemma9_i
        ⟨hp1, hp2, hp3⟩ ⟨hu1, hu2, hu3⟩ ⟨hr1.trans hr2.symm, hr2.trans hr3.symm⟩
        hνne ⟨hν13lt, hν23lt⟩ ⟨he13, he23⟩
      have himg : (A1.image (fun d => lam * d)).image (qdig7 m)
          = ({d1, d2, d3} : Finset ℕ).image (fun d => qdig7 m (lam * d)) := by
        rw [hA1eq, Finset.image_image]; rfl
      have hlen2 : apLen ((A1.image (fun d => lam * d)).image (qdig7 m)) ≤ 2 := by
        rw [himg]; exact hlen
      have hB : ∀ x ∈ ({d1, d2, d3} : Finset ℕ), ∀ y ∈ ({d1, d2, d3} : Finset ℕ),
          qdig7 m (eMod7 m (lam * x) (lam * y)) ∈ ({0, 6} : Finset (ZMod 7)) := by
        intro x hx y hy
        exact hpair06 x hx y hy
      exact c65_finish_of_pair06 hm hpos hunit hs hcls1 hcls4 hA1eq hA4eq hlam7 hlen2 hB
    · have hν13eq : padicValNat 7 (eMod7 m d1 d3) = m := by
        omega
      obtain ⟨lam₁, hlam₁, hq1, hq2, hlow1, hmono⟩ :=
        c65_boundary_lam hm hp1 hp2 hp3 hu1 hu2 hu3 hs hr1 hr2 hr3 he13 he23 hν13eq hν23lt
      exact c65_finish_of_boundary hm hpos hunit hs hcls1 hcls4 hA1eq hA4eq hlam₁ hq1 hlow1 hq2 hmono

/-- Non-zero eMod7 remains non-zero under coprime scalar multiplication. -/
private theorem eMod7_smul_ne_zero {m c x y : ℕ} (hcl : ¬ 7 ∣ c) (he : eMod7 m x y ≠ 0) :
    eMod7 m (c * x) (c * y) ≠ 0 := by
  have hc0 : c ≠ 0 := fun h => hcl (h ▸ dvd_zero _)
  have hrc : runit7 c ≠ 0 := runit7_ne_zero (Nat.pos_of_ne_zero hc0)
  rw [eMod7_smul hrc]
  intro h0
  have hdvd : 7 ^ (m + 1) ∣ c * eMod7 m x y := Nat.dvd_of_mod_eq_zero h0
  have hne : c * eMod7 m x y ≠ 0 := mul_ne_zero hc0 he
  have hle := (Nat.pow_dvd_iff_le_padicValNat (by norm_num) hne).mp hdvd
  rw [padicValNat_mul_seven hcl he] at hle
  have hlem : padicValNat 7 (eMod7 m x y) ≤ m := enu7_le_of_ne he
  omega

/-- `padicValNat` of `eMod7` is invariant under coprime scalar multiplication. -/
private theorem padicValNat_eMod7_smul {m c x y : ℕ} (hcl : ¬ 7 ∣ c) (he : eMod7 m x y ≠ 0) :
    padicValNat 7 (eMod7 m (c * x) (c * y)) = padicValNat 7 (eMod7 m x y) := by
  have hc0 : c ≠ 0 := fun h => hcl (h ▸ dvd_zero _)
  have hrc : runit7 c ≠ 0 := runit7_ne_zero (Nat.pos_of_ne_zero hc0)
  rw [eMod7_smul hrc]
  have h1 : padicValNat 7 (c * eMod7 m x y) = padicValNat 7 ((c * eMod7 m x y) % 7 ^ (m + 1)) := by
    apply padicValNat_eq_of_mod (m := m) (Nat.mod_mod _ _).symm
    · rw [padicValNat_mul_seven hcl he]
      exact enu7_le_of_ne he
    · exact mul_ne_zero hc0 he
  rw [← h1, padicValNat_mul_seven hcl he]

/-- Finite check: for any non-zero residue `r` and base `Q`, `apLen {Q + 3r, Q + r, Q} ≤ 4`. -/
private theorem c65_ratio3_top_len4 (r : ZMod 7) (hr : r ≠ 0) (Q : ZMod 7) :
    apLen ({Q + 3 * r, Q + r, Q} : Finset (ZMod 7)) ≤ 4 := by
  revert r hr Q
  decide

/-- Case (ii.2) with `h = m`: ratio 3 pure-top case. -/
private theorem c65_case_ii2_top {m : ℕ} (hm : 0 < m) {A1 A4 : Finset ℕ}
    (hpos : ∀ d ∈ A1 ∪ A4, 0 < d)
    (hunit : ∀ d ∈ A1 ∪ A4, padicValNat 7 d = 0)
    {s : ZMod 7} (hs : s ≠ 0)
    (hcls1 : ∀ d ∈ A1, runit7 d = s)
    (hcls4 : ∀ d ∈ A4, runit7 d = 4 * s)
    {d1 d2 d3 : ℕ} (hA1eq : A1 = {d1, d2, d3})
    {d4 d5 : ℕ} (hA4eq : A4 = {d4, d5})
    (he13 : eMod7 m d1 d3 ≠ 0) (he23 : eMod7 m d2 d3 ≠ 0)
    (hν23m : padicValNat 7 (eMod7 m d2 d3) = m)
    (hν13m : padicValNat 7 (eMod7 m d1 d3) = m)
    (hrat : runit7 (eMod7 m d1 d3) = 3 * runit7 (eMod7 m d2 d3)) :
    ∃ lam : ℕ, ¬ 7 ∣ lam ∧ good7 m lam (A1 ∪ A4) := by
  have hd1mem : d1 ∈ A1 := by rw [hA1eq]; exact Finset.mem_insert_self _ _
  have hd2mem : d2 ∈ A1 := by rw [hA1eq]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hd3mem : d3 ∈ A1 := by rw [hA1eq]; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have hd4mem : d4 ∈ A4 := by rw [hA4eq]; exact Finset.mem_insert_self _ _
  have hd5mem : d5 ∈ A4 := by rw [hA4eq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hr1 : runit7 d1 = s := hcls1 d1 hd1mem
  have hr2 : runit7 d2 = s := hcls1 d2 hd2mem
  have hr3 : runit7 d3 = s := hcls1 d3 hd3mem
  have hr4 : runit7 d4 = 4 * s := hcls4 d4 hd4mem
  have hr5 : runit7 d5 = 4 * s := hcls4 d5 hd5mem
  have hs4_0 : 4 * s ≠ 0 := mul_ne_zero (by decide) hs
  have hrel23 : residueRelOf d2 d3 = residueRel.same :=
    rel_same (by rw [hr2, hr3]) (by rw [hr3]; exact hs)
  have hrel13 : residueRelOf d1 d3 = residueRel.same :=
    rel_same (by rw [hr1, hr3]) (by rw [hr3]; exact hs)
  have hrel45 : residueRelOf d4 d5 = residueRel.same :=
    rel_same (by rw [hr4, hr5]) (by rw [hr5]; exact hs4_0)
  have he23top : eMod7 m d2 d3 = (runit7 (eMod7 m d2 d3)).val * 7 ^ m := by
    have h := residN_top hν23m
    rwa [qdig7_eq_runit7_of_top hν23m, Nat.mod_eq_of_lt (eMod7_lt _ _ _)] at h
  have he13top : eMod7 m d1 d3 = ((3 : ZMod 7) * runit7 (eMod7 m d2 d3)).val * 7 ^ m := by
    have h := residN_top hν13m
    rwa [qdig7_eq_runit7_of_top hν13m, Nat.mod_eq_of_lt (eMod7_lt _ _ _), hrat] at h
  by_cases he45 : eMod7 m d4 d5 = 0
  · -- `e₄₅ = 0`: scalar on `e₂₃`
    obtain ⟨c, hc0, hc7, hce, hqc⟩ :=
      exists_top_scalar_set hν23m he23 (by decide : (1 : ZMod 7) ≠ 0)
    have hcl : ¬ (7 : ℕ) ∣ c := fun h => absurd (Nat.le_of_dvd hc0 h) (by omega)
    have hrcast : runit7 c = (c : ZMod 7) :=
      runit7_of_padic_zero (padicValNat.eq_zero_of_not_dvd hcl)
    have hc0z : (c : ZMod 7) ≠ 0 := by
      intro hcon; have hdvd : 7 ∣ c := (ZMod.natCast_eq_zero_iff c 7).mp hcon
      exact absurd (Nat.le_of_dvd hc0 hdvd) (by omega)
    have hrc : runit7 c ≠ 0 := by rwa [hrcast]
    have hsc : ∀ d : ℕ, runit7 (c * d) = (c : ZMod 7) * runit7 d :=
      fun d => by rw [runit7_mul, hrcast]
    have hrel13' : residueRelOf (c * d1) (c * d3) = residueRel.same :=
      rel_same (by rw [hsc d1, hsc d3, hr1, hr3]) (by rw [hsc d3, hr3]; exact mul_ne_zero hc0z hs)
    have hrel23' : residueRelOf (c * d2) (c * d3) = residueRel.same :=
      rel_same (by rw [hsc d2, hsc d3, hr2, hr3]) (by rw [hsc d3, hr3]; exact mul_ne_zero hc0z hs)
    have hca : (c : ZMod 7) * runit7 (eMod7 m d2 d3) = 1 := by
      have h := qdig7_multTop (l := c) hν23m
      rw [hqc] at h; exact h.symm
    have he23c : eMod7 m (c * d2) (c * d3) = (1 : ZMod 7).val * 7 ^ m := by
      rw [e_smul_top hrc he23top, hca]
    have he13c : eMod7 m (c * d1) (c * d3) = (3 : ZMod 7).val * 7 ^ m := by
      have h3a : (c : ZMod 7) * ((3 : ZMod 7) * runit7 (eMod7 m d2 d3)) = 3 := by
        linear_combination 3 * hca
      rw [e_smul_top hrc he13top, h3a]
    have hq23c : qdig7 m (c * d2) = qdig7 m (c * d3) + 1 :=
      qdig_eq_add_of_e_top hrel23' he23c
    have hq13c : qdig7 m (c * d1) = qdig7 m (c * d3) + 3 :=
      qdig_eq_add_of_e_top hrel13' he13c
    have hap1 : apLen ((A1.image (fun d => c * d)).image (qdig7 m)) ≤ 4 := by
      have heq : (A1.image (fun d => c * d)).image (qdig7 m)
          = ({qdig7 m (c * d3) + 3, qdig7 m (c * d3) + 1, qdig7 m (c * d3)} : Finset (ZMod 7)) := by
        rw [hA1eq]
        simp only [Finset.image_insert, Finset.image_singleton, hq13c, hq23c]
      rw [heq]
      exact c65_ratio3_top_len4 1 (by decide) (qdig7 m (c * d3))
    have hd45res : d4 % 7 ^ (m + 1) = d5 % 7 ^ (m + 1) :=
      eq_resid_of_eMod7_eq_zero he45 hrel45
    have hq45c : qdig7 m (c * d4) = qdig7 m (c * d5) := by
      apply qdig7_congr
      rw [Nat.mul_mod, hd45res, ← Nat.mul_mod]
    have hap4 : apLen ((A4.image (fun d => c * d)).image (qdig7 m)) ≤ 2 := by
      have heq : (A4.image (fun d => c * d)).image (qdig7 m)
          = ({qdig7 m (c * d5)} : Finset (ZMod 7)) := by
        rw [hA4eq]
        simp only [Finset.image_insert, Finset.image_singleton, hq45c]
        ext z; simp
      rw [heq]
      have : apLen ({qdig7 m (c * d5)} : Finset (ZMod 7)) ≤ 1 := apLen_singleton_le1 _
      omega
    exact c65_finish hm hpos hunit hs hcls1 hcls4 hcl (Or.inr (Or.inl ⟨hap1, hap4⟩))
  · -- `e₄₅ ≠ 0`
    by_cases hν45m : padicValNat 7 (eMod7 m d4 d5) < m
    · -- `ν(e₄₅) < m`: scalar on `e₂₃`, then multLow on `e₄₅`
      obtain ⟨c, hc0, hc7, hce, hqc⟩ :=
        exists_top_scalar_set hν23m he23 (by decide : (1 : ZMod 7) ≠ 0)
      have hcl : ¬ (7 : ℕ) ∣ c := fun h => absurd (Nat.le_of_dvd hc0 h) (by omega)
      have hrcast : runit7 c = (c : ZMod 7) :=
        runit7_of_padic_zero (padicValNat.eq_zero_of_not_dvd hcl)
      have hc0z : (c : ZMod 7) ≠ 0 := by
        intro hcon; have hdvd : 7 ∣ c := (ZMod.natCast_eq_zero_iff c 7).mp hcon
        exact absurd (Nat.le_of_dvd hc0 hdvd) (by omega)
      have hrc : runit7 c ≠ 0 := by rwa [hrcast]
      have hsc : ∀ d : ℕ, runit7 (c * d) = (c : ZMod 7) * runit7 d :=
        fun d => by rw [runit7_mul, hrcast]
      have hca : (c : ZMod 7) * runit7 (eMod7 m d2 d3) = 1 := by
        have h := qdig7_multTop (l := c) hν23m
        rw [hqc] at h; exact h.symm
      have he23c : eMod7 m (c * d2) (c * d3) = (1 : ZMod 7).val * 7 ^ m := by
        rw [e_smul_top hrc he23top, hca]
      have he13c : eMod7 m (c * d1) (c * d3) = (3 : ZMod 7).val * 7 ^ m := by
        have h3a : (c : ZMod 7) * ((3 : ZMod 7) * runit7 (eMod7 m d2 d3)) = 3 := by
          linear_combination 3 * hca
        rw [e_smul_top hrc he13top, h3a]
      have he45c_ne : eMod7 m (c * d4) (c * d5) ≠ 0 := eMod7_smul_ne_zero hcl he45
      have hν45c : padicValNat 7 (eMod7 m (c * d4) (c * d5)) < m := by
        rw [padicValNat_eMod7_smul hcl he45]; exact hν45m
      set j := padicValNat 7 (eMod7 m (c * d4) (c * d5))
      obtain ⟨k, hk7, hkq⟩ := exists_multLow_set_qdig hν45c rfl he45c_ne 0
      set lam₂ := 1 + k * 7 ^ (m - j)
      have hlam₂r : runit7 lam₂ = 1 := runit7_multLow hν45c
      have hlam₂7 : ¬ 7 ∣ lam₂ := multLow_not_dvd hν45c
      set lam := lam₂ * c
      have hlam7 : ¬ 7 ∣ lam := Nat.prime_seven.not_dvd_mul hlam₂7 hcl
      have he23L : eMod7 m (lam * d2) (lam * d3) = (1 : ZMod 7).val * 7 ^ m := by
        dsimp [lam]
        rw [mul_assoc, mul_assoc, eMod7_mul hlam₂r, he23c]
        exact top_resid_multLow hν45c (by decide)
      have he13L : eMod7 m (lam * d1) (lam * d3) = (3 : ZMod 7).val * 7 ^ m := by
        dsimp [lam]
        rw [mul_assoc, mul_assoc, eMod7_mul hlam₂r, he13c]
        exact top_resid_multLow hν45c (by decide)
      have hscL : ∀ d : ℕ, runit7 (lam * d) = (c : ZMod 7) * runit7 d := by
        intro d; dsimp [lam]; rw [mul_assoc, runit7_mul, hlam₂r, one_mul, hsc]
      have hrel23L : residueRelOf (lam * d2) (lam * d3) = residueRel.same :=
        rel_same (by rw [hscL d2, hscL d3, hr2, hr3]) (by rw [hscL d3, hr3]; exact mul_ne_zero hc0z hs)
      have hrel13L : residueRelOf (lam * d1) (lam * d3) = residueRel.same :=
        rel_same (by rw [hscL d1, hscL d3, hr1, hr3]) (by rw [hscL d3, hr3]; exact mul_ne_zero hc0z hs)
      have hq23L : qdig7 m (lam * d2) = qdig7 m (lam * d3) + 1 :=
        qdig_eq_add_of_e_top hrel23L he23L
      have hq13L : qdig7 m (lam * d1) = qdig7 m (lam * d3) + 3 :=
        qdig_eq_add_of_e_top hrel13L he13L
      have hap1 : apLen ((A1.image (fun d => lam * d)).image (qdig7 m)) ≤ 4 := by
        have heq : (A1.image (fun d => lam * d)).image (qdig7 m)
            = ({qdig7 m (lam * d3) + 3, qdig7 m (lam * d3) + 1, qdig7 m (lam * d3)} : Finset (ZMod 7)) := by
          rw [hA1eq]
          simp only [Finset.image_insert, Finset.image_singleton, hq13L, hq23L]
        rw [heq]
        exact c65_ratio3_top_len4 1 (by decide) (qdig7 m (lam * d3))
      have hrel45L : residueRelOf (lam * d4) (lam * d5) = residueRel.same :=
        rel_same (by rw [hscL d4, hscL d5, hr4, hr5]) (by rw [hscL d5, hr5]; exact mul_ne_zero hc0z hs4_0)
      have hqe : qdig7 m (eMod7 m (lam * d4) (lam * d5)) = 0 := by
        dsimp [lam]
        rw [mul_assoc, mul_assoc, eMod7_mul hlam₂r, qdig7_congr (Nat.mod_mod _ _)]
        exact hkq
      have hap4 : apLen ((A4.image (fun d => lam * d)).image (qdig7 m)) ≤ 2 := by
        have heq : (A4.image (fun d => lam * d)).image (qdig7 m)
            = ({lam * d4, lam * d5} : Finset ℕ).image (qdig7 m) := by
          rw [hA4eq]; simp only [Finset.image_insert, Finset.image_singleton]
        rw [heq]
        exact c65_pair_len2' hrel45L hqe
      exact c65_finish hm hpos hunit hs hcls1 hcls4 hlam7 (Or.inr (Or.inl ⟨hap1, hap4⟩))
    · -- `ν(e₄₅) = m`: scalar on `e₄₅` with target 1!
      have hν45eq : padicValNat 7 (eMod7 m d4 d5) = m := by
        have hle : padicValNat 7 (eMod7 m d4 d5) ≤ m := enu7_le_of_ne he45
        omega
      obtain ⟨c, hc0, hc7, hce, hqc⟩ :=
        exists_top_scalar_set hν45eq he45 (by decide : (1 : ZMod 7) ≠ 0)
      have hcl : ¬ (7 : ℕ) ∣ c := fun h => absurd (Nat.le_of_dvd hc0 h) (by omega)
      have hrcast : runit7 c = (c : ZMod 7) :=
        runit7_of_padic_zero (padicValNat.eq_zero_of_not_dvd hcl)
      have hc0z : (c : ZMod 7) ≠ 0 := by
        intro hcon; have hdvd : 7 ∣ c := (ZMod.natCast_eq_zero_iff c 7).mp hcon
        exact absurd (Nat.le_of_dvd hc0 hdvd) (by omega)
      have hrc : runit7 c ≠ 0 := by rwa [hrcast]
      have hsc : ∀ d : ℕ, runit7 (c * d) = (c : ZMod 7) * runit7 d :=
        fun d => by rw [runit7_mul, hrcast]
      have hrel45' : residueRelOf (c * d4) (c * d5) = residueRel.same :=
        rel_same (by rw [hsc d4, hsc d5, hr4, hr5]) (by rw [hsc d5, hr5]; exact mul_ne_zero hc0z hs4_0)
      have he45' : eMod7 m (c * d4) (c * d5) = (1 : ZMod 7).val * 7 ^ m := by
        rw [eMod7_smul hrc]; exact hce
      have hq45' : qdig7 m (c * d4) = qdig7 m (c * d5) + 1 :=
        qdig_eq_add_of_e_top hrel45' he45'
      have hap4 : apLen ((A4.image (fun d => c * d)).image (qdig7 m)) ≤ 2 := by
        have heq : (A4.image (fun d => c * d)).image (qdig7 m)
            = ({qdig7 m (c * d5) + 1, qdig7 m (c * d5)} : Finset (ZMod 7)) := by
          rw [hA4eq]
          simp only [Finset.image_insert, Finset.image_singleton, hq45']
        rw [heq]
        have hsub : ({qdig7 m (c * d5) + 1, qdig7 m (c * d5)} : Finset (ZMod 7))
            ⊆ cycIv (qdig7 m (c * d5)) 2 := by
          intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl
          · rw [mem_cycIv, add_sub_cancel_left]; decide
          · rw [mem_cycIv, sub_self, ZMod.val_zero]; omega
        exact (apLen_le_iff _ 2 (by norm_num)).mpr ⟨_, hsub⟩
      set r' : ZMod 7 := (c : ZMod 7) * runit7 (eMod7 m d2 d3)
      have hr'0 : r' ≠ 0 := mul_ne_zero hc0z (runit7_ne_zero (Nat.pos_of_ne_zero he23))
      have he23c : eMod7 m (c * d2) (c * d3) = r'.val * 7 ^ m := by
        rw [e_smul_top hrc he23top]
      have he13c : eMod7 m (c * d1) (c * d3) = (3 * r').val * 7 ^ m := by
        have h3r : (c : ZMod 7) * ((3 : ZMod 7) * runit7 (eMod7 m d2 d3)) = 3 * r' := by
          dsimp [r']; ring
        rw [e_smul_top hrc he13top, h3r]
      have hrel13' : residueRelOf (c * d1) (c * d3) = residueRel.same :=
        rel_same (by rw [hsc d1, hsc d3, hr1, hr3]) (by rw [hsc d3, hr3]; exact mul_ne_zero hc0z hs)
      have hrel23' : residueRelOf (c * d2) (c * d3) = residueRel.same :=
        rel_same (by rw [hsc d2, hsc d3, hr2, hr3]) (by rw [hsc d3, hr3]; exact mul_ne_zero hc0z hs)
      have hq23c : qdig7 m (c * d2) = qdig7 m (c * d3) + r' :=
        qdig_eq_add_of_e_top hrel23' he23c
      have hq13c : qdig7 m (c * d1) = qdig7 m (c * d3) + 3 * r' :=
        qdig_eq_add_of_e_top hrel13' he13c
      have hap1 : apLen ((A1.image (fun d => c * d)).image (qdig7 m)) ≤ 4 := by
        have heq : (A1.image (fun d => c * d)).image (qdig7 m)
            = ({qdig7 m (c * d3) + 3 * r', qdig7 m (c * d3) + r', qdig7 m (c * d3)} : Finset (ZMod 7)) := by
          rw [hA1eq]
          simp only [Finset.image_insert, Finset.image_singleton, hq13c, hq23c]
        rw [heq]
        exact c65_ratio3_top_len4 r' hr'0 (qdig7 m (c * d3))
      exact c65_finish hm hpos hunit hs hcls1 hcls4 hcl (Or.inr (Or.inl ⟨hap1, hap4⟩))

/-! ### §7 The `Λ₀`-shift finisher and Lemma-7 clones for §6.5 -/

/-- Direct `Λ₀` finisher: given a shift `t` making the digit images of
`lam₁·A₁` (shifted by `t`) and `lam₁·A₄` (shifted by `4t`) avoid `{0,6}`,
produce the final multiplier `lam₀ * lam₁`.  This is the `case65_tail`
bookkeeping with the cover step bypassed (the shift is supplied directly). -/
private theorem c65_lambda0_finish {m : ℕ} (hm : 0 < m) {A1 A4 : Finset ℕ}
    (hpos : ∀ d ∈ A1 ∪ A4, 0 < d)
    (hunit : ∀ d ∈ A1 ∪ A4, padicValNat 7 d = 0)
    {s : ZMod 7} (hs : s ≠ 0)
    (hcls1 : ∀ d ∈ A1, runit7 d = s)
    (hcls4 : ∀ d ∈ A4, runit7 d = 4 * s)
    {lam₁ : ℕ} (hlam₁ : ¬ 7 ∣ lam₁)
    (t : ZMod 7)
    (hav : avoids06
      (((A1.image fun d => lam₁ * d).image (qdig7 m)).image (· + t)
        ∪ ((A4.image fun d => lam₁ * d).image (qdig7 m)).image (· + 4 * t))) :
    ∃ lam : ℕ, ¬ 7 ∣ lam ∧ good7 m lam (A1 ∪ A4) := by
  classical
  set X1 := (A1.image fun d => lam₁ * d).image (qdig7 m) with hX1
  set X4 := (A4.image fun d => lam₁ * d).image (qdig7 m) with hX4
  set B := (A1 ∪ A4).image (fun d => lam₁ * d) with hB
  set s' : ZMod 7 := runit7 lam₁ * s with hs'
  have hlam₁0 : lam₁ ≠ 0 := fun hh => hlam₁ (hh ▸ dvd_zero _)
  have hrl1 : runit7 lam₁ ≠ 0 := runit7_ne_zero (Nat.pos_of_ne_zero hlam₁0)
  have hs'0 : s' ≠ 0 := mul_ne_zero hrl1 hs
  have hunitB : ∀ d ∈ B, padicValNat 7 d = 0 := by
    intro d hd
    obtain ⟨d₀, hd₀, rfl⟩ := Finset.mem_image.mp hd
    rw [padicValNat_mul_seven hlam₁ (ne_of_gt (hpos d₀ hd₀))]
    exact hunit d₀ hd₀
  have hclsB : ∀ d ∈ B, runit7 d ∈ ({s', 2 * s', 4 * s'} : Finset (ZMod 7)) := by
    intro d hd
    obtain ⟨d₀, hd₀, rfl⟩ := Finset.mem_image.mp hd
    rw [runit7_mul]
    rcases Finset.mem_union.mp hd₀ with hd₁ | hd₄
    · rw [hcls1 d₀ hd₁]
      exact Finset.mem_insert_self _ _
    · rw [hcls4 d₀ hd₄]
      have h4 : runit7 lam₁ * (4 * s) = 4 * s' := by rw [hs']; ring
      rw [h4]
      simp
  have hfilt1 : (B.filter fun d => runit7 d = s').image (qdig7 m) = X1 := by
    have hf : B.filter (fun d => runit7 d = s')
        = A1.image (fun d => lam₁ * d) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨hBx, hr⟩
        obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hBx
        rw [runit7_mul, hs'] at hr
        have hrd : runit7 d = s := mul_left_cancel₀ hrl1 hr
        rcases Finset.mem_union.mp hd with hd₁ | hd₄
        · exact ⟨d, hd₁, rfl⟩
        · rw [hcls4 d hd₄] at hrd
          have hz : (3 : ZMod 7) * s = 0 := by linear_combination hrd
          rcases mul_eq_zero.mp hz with h3 | h0
          · exact absurd h3 (by decide)
          · exact absurd h0 hs
      · rintro ⟨d, hd₁, rfl⟩
        exact ⟨Finset.mem_image.mpr
            ⟨d, Finset.mem_union_left _ hd₁, rfl⟩,
          by rw [runit7_mul, hcls1 d hd₁, hs']⟩
    rw [hf]
  have hfilt2 : (B.filter fun d => runit7 d = 2 * s').image (qdig7 m)
      = (∅ : Finset (ZMod 7)) := by
    have hf : B.filter (fun d => runit7 d = 2 * s') = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro x hxB hxr
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hxB
      rw [runit7_mul, hs'] at hxr
      have hrd : runit7 d = 2 * s := by
        have hr' : runit7 lam₁ * runit7 d = runit7 lam₁ * (2 * s) := by
          rw [hxr]; ring
        exact mul_left_cancel₀ hrl1 hr'
      rcases Finset.mem_union.mp hd with hd₁ | hd₄
      · rw [hcls1 d hd₁] at hrd
        have hz : (1 : ZMod 7) * s = 0 := by linear_combination -hrd
        rcases mul_eq_zero.mp hz with h1 | h0
        · exact absurd h1 (by decide)
        · exact hs h0
      · rw [hcls4 d hd₄] at hrd
        have hz : (2 : ZMod 7) * s = 0 := by linear_combination hrd
        rcases mul_eq_zero.mp hz with h2 | h0
        · exact absurd h2 (by decide)
        · exact hs h0
    rw [hf, Finset.image_empty]
  have hfilt4 : (B.filter fun d => runit7 d = 4 * s').image (qdig7 m)
      = X4 := by
    have hf : B.filter (fun d => runit7 d = 4 * s')
        = A4.image (fun d => lam₁ * d) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨hBx, hr⟩
        obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hBx
        rw [runit7_mul, hs'] at hr
        have hrd : runit7 d = 4 * s := by
          have hr' : runit7 lam₁ * runit7 d = runit7 lam₁ * (4 * s) := by
            rw [hr]; ring
          exact mul_left_cancel₀ hrl1 hr'
        rcases Finset.mem_union.mp hd with hd₁ | hd₄
        · rw [hcls1 d hd₁] at hrd
          have hz : (3 : ZMod 7) * s = 0 := by linear_combination -hrd
          rcases mul_eq_zero.mp hz with h3 | h0
          · exact absurd h3 (by decide)
          · exact absurd h0 hs
        · exact ⟨d, hd₄, rfl⟩
      · rintro ⟨d, hd₄, rfl⟩
        exact ⟨Finset.mem_image.mpr
            ⟨d, Finset.mem_union_right _ hd₄, rfl⟩,
          by rw [runit7_mul, hcls4 d hd₄, hs']; ring⟩
    rw [hf]
  have hunion :
      ((B.filter fun d => runit7 d = s').image (qdig7 m)).image (· + t)
        ∪ ((B.filter fun d => runit7 d = 2 * s').image (qdig7 m)).image
          (· + 2 * t)
        ∪ ((B.filter fun d => runit7 d = 4 * s').image (qdig7 m)).image
          (· + 4 * t)
        = X1.image (· + t) ∪ X4.image (· + 4 * t) := by
    rw [hfilt1, hfilt2, hfilt4, Finset.image_empty, Finset.union_empty]
  obtain ⟨lam0, hlam0mem, hgood0⟩ :=
    exists_lambda0_of_shift hm hs'0 hunitB hclsB t (hunion.symm ▸ hav)
  refine ⟨lam0 * lam₁,
    Nat.prime_seven.not_dvd_mul (not_dvd_of_mem_multLow7_zero hm hlam0mem)
      hlam₁, ?_⟩
  exact good7_mul hgood0

/-- **Lemma 7(i)** with the multiplier exposed and `ν(e) = 0` allowed
(`Λ₀` shift): verbatim clone of `lemma7_i` — the `0 < ν` hypothesis was
only used to get `e ≠ 0`, which is assumed directly here. -/
private theorem c65_lemma7_i' {m : ℕ} (hm : 0 < m) {d d' : ℕ}
    (hd : padicValNat 7 d = 0) (hd' : padicValNat 7 d' = 0)
    (hpos : 0 < d) (hpos' : 0 < d')
    (hrel : runit7 d' = 2 * runit7 d)
    (he0 : eMod7 m d d' ≠ 0)
    (hνm : padicValNat 7 (eMod7 m d d') < m)
    {X : Finset (ZMod 7)} (hX : apLen X ≤ 4) :
    ∃ k : ℕ, k < 7 ∧
      etd7 m ((1 + k * 7 ^ (m - padicValNat 7 (eMod7 m d d'))) * d)
        ((1 + k * 7 ^ (m - padicValNat 7 (eMod7 m d d'))) * d') ∉ X := by
  set e := eMod7 m d d' with he
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

/-- **Lemma 7(ii)** (`q(λ·7d) = 6` branch) with the `Λ₁`-multiplier
exposed: verbatim clone of `lemma7_ii`. -/
private theorem c65_lemma7_ii' {m : ℕ} (hm : 2 ≤ m) {d d' : ℕ}
    (hd : padicValNat 7 d = 0) (hd' : padicValNat 7 d' = 0)
    (hpos : 0 < d) (hpos' : 0 < d')
    (hrel : runit7 d' = 2 * runit7 d)
    (hν : padicValNat 7 (eMod7 m d d') = m)
    {X : Finset (ZMod 7)}
    (hr : runit7 (eMod7 m d d') ∉ X ∪ X.image (· + 1)) :
    ∃ k : ℕ, k < 7 ∧
      etd7 m ((1 + k * 7 ^ (m - 1)) * d) ((1 + k * 7 ^ (m - 1)) * d')
        ∉ X := by
  set e := eMod7 m d d' with he
  have h1m : 1 < m := by omega
  obtain ⟨k, hk7, hkq⟩ :=
    exists_multLow_one_set_seven' (by omega : 0 < m) hd hpos 6
  refine ⟨k, hk7, ?_⟩
  set lam := 1 + k * 7 ^ (m - 1) with hlam
  have hlamr : runit7 lam = 1 := runit7_multLow h1m
  have h7d : qdig7 m (7 * (lam * d)) = 6 := by
    have e' : 7 * (lam * d) = lam * (7 * d) := by ring
    rw [e']
    exact hkq
  have h2d : qdig7 m (2 * (lam * d)) = 2 * qdig7 m (lam * d) + 1 :=
    qdig7_two_eq_smul_add_one (by omega : 0 < m) h7d
  have hrd : runit7 d ≠ 0 := runit7_ne_zero hpos
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
      rw [he]
      unfold eMod7
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
  rw [he2, qdig7_eq_runit7_of_top hν, het2, h2d] at hbound
  have het : etd7 m (lam * d) (lam * d') =
      2 * qdig7 m (lam * d) - qdig7 m (lam * d') := by
    unfold etd7
    rw [if_pos (by rw [hrld', hrld])]
  rw [het]
  rw [Finset.mem_union] at hr
  push Not at hr
  obtain ⟨hr1, hr2⟩ := hr
  have hr2' : runit7 e - 1 ∉ X := by
    intro hcon
    apply hr2
    rw [Finset.mem_image]
    exact ⟨runit7 e - 1, hcon, by ring⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hbound
  rcases hbound with hb | hb
  · have he7 : 2 * qdig7 m (lam * d) - qdig7 m (lam * d') = runit7 e - 1 := by
      have h0 : runit7 e = 2 * qdig7 m (lam * d) + 1 - qdig7 m (lam * d') :=
        sub_eq_zero.mp hb
      rw [h0]
      ring
    rw [he7]
    exact hr2'
  · have he7 : 2 * qdig7 m (lam * d) - qdig7 m (lam * d') = runit7 e := by
      have h0 : runit7 e - (2 * qdig7 m (lam * d) + 1 - qdig7 m (lam * d')) - 6
          = 0 := by
        rw [hb, sub_self]
      have h6 : (6 : ZMod 7) = -1 := by decide
      rw [h6] at h0
      have h4 : runit7 e - (2 * qdig7 m (lam * d) + 1 - qdig7 m (lam * d')) - -1
          = runit7 e - (2 * qdig7 m (lam * d) - qdig7 m (lam * d')) := by ring
      rw [h4] at h0
      exact (sub_eq_zero.mp h0).symm
    rw [he7]
    exact hr1

/-- **Mirrored Lemma 7(ii)** (`q(λ·7d) = 0` branch): for a `twoX` pair
with `ν(e) = m`, a `Λ₁`-element with `q(λ·7d) = 0` forces
`q(2λd) = 2q(λd)`, so `ẽ ∈ {r(e), r(e)+1}` — avoiding `X` when
`r(e) ∉ X ∪ (X−1)`. -/
private theorem c65_lemma7_ii'' {m : ℕ} (hm : 2 ≤ m) {d d' : ℕ}
    (hd : padicValNat 7 d = 0) (hd' : padicValNat 7 d' = 0)
    (hpos : 0 < d) (hpos' : 0 < d')
    (hrel : runit7 d' = 2 * runit7 d)
    (hν : padicValNat 7 (eMod7 m d d') = m)
    {X : Finset (ZMod 7)}
    (hr : runit7 (eMod7 m d d') ∉ X ∪ X.image (· - 1)) :
    ∃ k : ℕ, k < 7 ∧
      etd7 m ((1 + k * 7 ^ (m - 1)) * d) ((1 + k * 7 ^ (m - 1)) * d')
        ∉ X := by
  set e := eMod7 m d d' with he
  have h1m : 1 < m := by omega
  obtain ⟨k, hk7, hkq⟩ :=
    exists_multLow_one_set_seven' (by omega : 0 < m) hd hpos 0
  refine ⟨k, hk7, ?_⟩
  set lam := 1 + k * 7 ^ (m - 1) with hlam
  have hlamr : runit7 lam = 1 := runit7_multLow h1m
  have h7d : qdig7 m (7 * (lam * d)) = 0 := by
    have e' : 7 * (lam * d) = lam * (7 * d) := by ring
    rw [e']
    exact hkq
  have h2d : qdig7 m (2 * (lam * d)) = 2 * qdig7 m (lam * d) :=
    qdig7_two_eq_smul (by omega : 0 < m) h7d
  have hrd : runit7 d ≠ 0 := runit7_ne_zero hpos
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
      rw [he]
      unfold eMod7
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
  rw [he2, qdig7_eq_runit7_of_top hν, het2, h2d] at hbound
  have het : etd7 m (lam * d) (lam * d') =
      2 * qdig7 m (lam * d) - qdig7 m (lam * d') := by
    unfold etd7
    rw [if_pos (by rw [hrld', hrld])]
  rw [het]
  rw [Finset.mem_union] at hr
  push Not at hr
  obtain ⟨hr1, hr2⟩ := hr
  have hr2' : runit7 e + 1 ∉ X := by
    intro hcon
    apply hr2
    rw [Finset.mem_image]
    exact ⟨runit7 e + 1, hcon, by ring⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hbound
  rcases hbound with hb | hb
  · -- `r(e) − ẽ = 0` gives `ẽ = r(e)`
    have he7 : 2 * qdig7 m (lam * d) - qdig7 m (lam * d') = runit7 e :=
      (sub_eq_zero.mp hb).symm
    rw [he7]
    exact hr1
  · -- `r(e) − ẽ = 6` gives `ẽ = r(e) + 1`
    have he7 : 2 * qdig7 m (lam * d) - qdig7 m (lam * d') = runit7 e + 1 := by
      have h0 : runit7 e - (2 * qdig7 m (lam * d) - qdig7 m (lam * d')) - 6
          = 0 := by
        rw [hb, sub_self]
      have h6 : (6 : ZMod 7) = -1 := by decide
      rw [h6] at h0
      have h5 : runit7 e - (2 * qdig7 m (lam * d) - qdig7 m (lam * d')) + 1
          = 0 := by linear_combination h0
      have h6' : runit7 e + 1 = 2 * qdig7 m (lam * d) - qdig7 m (lam * d') :=
        by linear_combination h5
      exact h6'.symm
    rw [he7]
    exact hr2'

/-- **`Λ₀`-rescue bridge for (ii.1), `h = m`**: if the digit picture of
`lam₂·A₁` is the window `{a, a+x₁, a+x₂}` and `lam₂·A₄` is the pair
`{p, p+ρ}`, and the `Λ₀`-shift `t` avoids `{0,6}` on the shifted picture,
build the final `lam`. -/
private theorem c65_ii1b_fin {m : ℕ} (hm : 0 < m) {A1 A4 : Finset ℕ}
    (hpos : ∀ d ∈ A1 ∪ A4, 0 < d)
    (hunit : ∀ d ∈ A1 ∪ A4, padicValNat 7 d = 0)
    {s : ZMod 7} (hs : s ≠ 0)
    (hcls1 : ∀ d ∈ A1, runit7 d = s)
    (hcls4 : ∀ d ∈ A4, runit7 d = 4 * s)
    {lam₂ : ℕ} (hlam₂ : ¬ 7 ∣ lam₂)
    {d1 d2 d3 u v : ℕ} (hA1eq : A1 = {d1, d2, d3}) (hA4eq : A4 = {u, v})
    (t : ZMod 7) {a p x1 x2 ρ : ZMod 7}
    (hq1 : qdig7 m (lam₂ * d1) = a + x1)
    (hq2 : qdig7 m (lam₂ * d2) = a + x2)
    (hq3 : qdig7 m (lam₂ * d3) = a)
    (hqu : qdig7 m (lam₂ * u) = p + ρ)
    (hqv : qdig7 m (lam₂ * v) = p)
    (hav : avoids06 (({a + x1 + t, a + x2 + t, a + t} : Finset (ZMod 7))
        ∪ ({p + ρ + 4 * t, p + 4 * t} : Finset (ZMod 7)))) :
    ∃ lam : ℕ, ¬ 7 ∣ lam ∧ good7 m lam (A1 ∪ A4) := by
  refine c65_lambda0_finish hm hpos hunit hs hcls1 hcls4 hlam₂ t ?_
  rw [hA1eq, hA4eq]
  simp only [Finset.image_insert, Finset.image_singleton]
  rw [hq1, hq2, hq3, hqu, hqv]
  exact hav


/-- `(2·4)·x = x` in `ZMod 7`. -/
private theorem c65_mul24 (x : ZMod 7) : 2 * (4 * x) = x := by
  rw [← mul_assoc, show (2 : ZMod 7) * 4 = 1 by decide, one_mul]

/-- Finite table `μ = 1`: the direct `Λ₀`-rescue works whenever the
`ẽ`-value `2(p+4)−a` escapes `{4,5}`. -/
private theorem c65_ii1_dec1 : ∀ a p : ZMod 7,
    2 * (p + 4) - a ∉ ({4, 5} : Finset (ZMod 7)) →
    ∃ t : ZMod 7, avoids06
      (({a + 2 + t, a + 1 + t, a + t}
        ∪ {p + 4 + 4 * t, p + 4 * t}) : Finset (ZMod 7)) := by
  decide

/-- Finite table `μ = 3`: after the `×3` pre-scale the window is
`{a, a+3, a+6}` and the pair `{p, p+5}`; the `Λ₀`-rescue works whenever
`2(p+5)−a ∉ {3,5}`. -/
private theorem c65_ii1_dec3 : ∀ a p : ZMod 7,
    2 * (p + 5) - a ∉ ({3, 5} : Finset (ZMod 7)) →
    ∃ t : ZMod 7, avoids06
      (({a + 6 + t, a + 3 + t, a + t}
        ∪ {p + 5 + 4 * t, p + 4 * t}) : Finset (ZMod 7)) := by
  decide

/-- Finite table `μ = 6`: after the `×6` pre-scale the window is
`{a, a+5, a+6}` and the pair `{p, p+3}`; the `Λ₀`-rescue works whenever
`2(p+3)−a ∉ {1,2}`. -/
private theorem c65_ii1_dec6 : ∀ a p : ZMod 7,
    2 * (p + 3) - a ∉ ({1, 2} : Finset (ZMod 7)) →
    ∃ t : ZMod 7, avoids06
      (({a + 5 + t, a + 6 + t, a + t}
        ∪ {p + 3 + 4 * t, p + 4 * t}) : Finset (ZMod 7)) := by
  decide

/-- **Post-Lemma-7 assembly for (ii.1), `h = m`**: given the pure-top
normalised picture under `lam₁` (window offsets `2,1`, pair offset `4`),
a unit `μ` (`×μ` pre-scale) and a `Λⱼ`-element `lam'` (given only through
`runit7 = 1`, `7 ∤`, and its `Λⱼ`-form), with
`etd7 (lam'·μ·lam₁·u, lam'·μ·lam₁·d₃) ∉ X`, the `Λ₀`-rescue table `hdec`
yields the final `lam`. -/
private theorem c65_ii1b_post {m : ℕ} (hm : 0 < m) {A1 A4 : Finset ℕ}
    (hpos : ∀ d ∈ A1 ∪ A4, 0 < d)
    (hunit : ∀ d ∈ A1 ∪ A4, padicValNat 7 d = 0)
    {s : ZMod 7} (hs : s ≠ 0)
    (hcls1 : ∀ d ∈ A1, runit7 d = s)
    (hcls4 : ∀ d ∈ A4, runit7 d = 4 * s)
    {lam₁ : ℕ} (hlam₁ : ¬ 7 ∣ lam₁)
    {d1 d2 d3 u v : ℕ} (hA1eq : A1 = {d1, d2, d3}) (hA4eq : A4 = {u, v})
    (he13 : eMod7 m (lam₁ * d1) (lam₁ * d3) = 2 * 7 ^ m)
    (he23 : eMod7 m (lam₁ * d2) (lam₁ * d3) = 7 ^ m)
    (heuv : eMod7 m (lam₁ * u) (lam₁ * v) = 4 * 7 ^ m)
    {lam' μ : ℕ} (hlam'r : runit7 lam' = 1) (hlam'7 : ¬ 7 ∣ lam')
    (hμ7 : ¬ 7 ∣ μ) (hμpos : 0 < μ)
    (hform : ∃ j k : ℕ, j < m ∧ lam' = 1 + k * 7 ^ (m - j))
    {X : Finset (ZMod 7)}
    (hk : etd7 m (lam' * (μ * (lam₁ * u))) (lam' * (μ * (lam₁ * d3))) ∉ X)
    {x1 x2 ρ : ZMod 7}
    (hx1 : (μ : ZMod 7) * 2 = x1) (hx2 : (μ : ZMod 7) * 1 = x2)
    (hρ : (μ : ZMod 7) * 4 = ρ)
    (hdec : ∀ a p : ZMod 7, 2 * (p + ρ) - a ∉ X → ∃ t : ZMod 7,
      avoids06 (({a + x1 + t, a + x2 + t, a + t}
        ∪ {p + ρ + 4 * t, p + 4 * t}) : Finset (ZMod 7))) :
    ∃ lam : ℕ, ¬ 7 ∣ lam ∧ good7 m lam (A1 ∪ A4) := by
  have hd1mem : d1 ∈ A1 := by rw [hA1eq]; exact Finset.mem_insert_self _ _
  have hd2mem : d2 ∈ A1 := by
    rw [hA1eq]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hd3mem : d3 ∈ A1 := by
    rw [hA1eq]; exact Finset.mem_insert_of_mem
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have humem : u ∈ A4 := by rw [hA4eq]; exact Finset.mem_insert_self _ _
  have hvmem : v ∈ A4 := by
    rw [hA4eq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hlam₁0 : lam₁ ≠ 0 := fun hh => hlam₁ (hh ▸ dvd_zero _)
  have hrl1 : runit7 lam₁ ≠ 0 := runit7_ne_zero (Nat.pos_of_ne_zero hlam₁0)
  set s' : ZMod 7 := runit7 lam₁ * s with hs'
  have hs'0 : s' ≠ 0 := mul_ne_zero hrl1 hs
  have hs4'0 : 4 * s' ≠ 0 := mul_ne_zero (by decide) hs'0
  have hμcast : runit7 μ = (μ : ZMod 7) :=
    runit7_of_padic_zero (padicValNat.eq_zero_of_not_dvd hμ7)
  have hμr : runit7 μ ≠ 0 := runit7_ne_zero hμpos
  have hμz : (μ : ZMod 7) ≠ 0 := by rwa [← hμcast]
  obtain ⟨j, k, hjm, hform⟩ := hform
  set lam₂ := lam' * (μ * lam₁) with hlam₂
  have hlam₂7 : ¬ 7 ∣ lam₂ :=
    Nat.prime_seven.not_dvd_mul hlam'7 (Nat.prime_seven.not_dvd_mul hμ7 hlam₁)
  -- `e`-transport: `e(lam₂·x, lam₂·y) = ((μ)·w)·7^m` when
  -- `e(lam₁·x, lam₁·y) = w·7^m` (pure top).
  have hescale : ∀ {x y : ℕ} {w : ZMod 7} (hw : w ≠ 0),
      eMod7 m (lam₁ * x) (lam₁ * y) = w.val * 7 ^ m →
      eMod7 m (lam₂ * x) (lam₂ * y) = (((μ : ZMod 7) * w).val) * 7 ^ m := by
    intro x y w hw he
    have hstep1 : eMod7 m (μ * (lam₁ * x)) (μ * (lam₁ * y))
        = (((μ : ZMod 7) * w).val) * 7 ^ m := e_smul_top hμr he
    have hμw0 : (μ : ZMod 7) * w ≠ 0 := mul_ne_zero hμz hw
    have hν1 : padicValNat 7 (eMod7 m (μ * (lam₁ * x)) (μ * (lam₁ * y)))
        = m := by
      rw [hstep1]
      exact nu_pow7 (Nat.pos_of_ne_zero (by rwa [Ne, ZMod.val_eq_zero]))
        (ZMod.val_lt _)
    have e1 : lam₂ * x = lam' * (μ * (lam₁ * x)) := by
      dsimp [lam₂]; ring
    have e2 : lam₂ * y = lam' * (μ * (lam₁ * y)) := by
      dsimp [lam₂]; ring
    rw [e1, e2, eMod7_mul hlam'r, hform,
      residN_multLow7 (k := k) hjm (by rw [hν1]; exact hjm),
      Nat.mod_eq_of_lt (eMod7_lt _ _ _), hstep1]
  -- residues and digit relations for `lam₂`-elements
  have hrz : ∀ d : ℕ, runit7 (lam₂ * d) = (μ : ZMod 7) * runit7 (lam₁ * d) := by
    intro d
    rw [show lam₂ * d = lam' * (μ * (lam₁ * d)) by dsimp [lam₂]; ring]
    rw [runit7_mul, hlam'r, one_mul, runit7_mul, hμcast]
  have hrz1 : runit7 (lam₂ * d1) = μ * s' := by
    rw [hrz, runit7_mul, hcls1 d1 hd1mem]
  have hrz2 : runit7 (lam₂ * d2) = μ * s' := by
    rw [hrz, runit7_mul, hcls1 d2 hd2mem]
  have hrz3 : runit7 (lam₂ * d3) = μ * s' := by
    rw [hrz, runit7_mul, hcls1 d3 hd3mem]
  have hru : runit7 (lam₂ * u) = μ * (4 * s') := by
    rw [hrz, runit7_mul, hcls4 u humem, hs']; ring
  have hrv : runit7 (lam₂ * v) = μ * (4 * s') := by
    rw [hrz, runit7_mul, hcls4 v hvmem, hs']; ring
  have hμs'0 : (μ : ZMod 7) * s' ≠ 0 := mul_ne_zero hμz hs'0
  have hμ4s'0 : (μ : ZMod 7) * (4 * s') ≠ 0 := mul_ne_zero hμz hs4'0
  have hrel13' : residueRelOf (lam₂ * d1) (lam₂ * d3) = residueRel.same :=
    rel_same (by rw [hrz1, hrz3]) (by rw [hrz3]; exact hμs'0)
  have hrel23' : residueRelOf (lam₂ * d2) (lam₂ * d3) = residueRel.same :=
    rel_same (by rw [hrz2, hrz3]) (by rw [hrz3]; exact hμs'0)
  have hreluv' : residueRelOf (lam₂ * u) (lam₂ * v) = residueRel.same :=
    rel_same (by rw [hru, hrv]) (by rw [hrv]; exact hμ4s'0)
  have hq13' : qdig7 m (lam₂ * d1) = qdig7 m (lam₂ * d3) + x1 := by
    have he : eMod7 m (lam₂ * d1) (lam₂ * d3) = x1.val * 7 ^ m := by
      have h2v : eMod7 m (lam₁ * d1) (lam₁ * d3) = (2 : ZMod 7).val * 7 ^ m :=
        he13.trans rfl
      rw [hescale (by decide : (2 : ZMod 7) ≠ 0) h2v, hx1]
    exact qdig_eq_add_of_e_top hrel13' he
  have hq23' : qdig7 m (lam₂ * d2) = qdig7 m (lam₂ * d3) + x2 := by
    have he : eMod7 m (lam₂ * d2) (lam₂ * d3) = x2.val * 7 ^ m := by
      have h1v : eMod7 m (lam₁ * d2) (lam₁ * d3) = (1 : ZMod 7).val * 7 ^ m :=
        he23.trans (by rw [show (1 : ZMod 7).val = 1 by decide, one_mul])
      rw [hescale (by decide : (1 : ZMod 7) ≠ 0) h1v, hx2]
    exact qdig_eq_add_of_e_top hrel23' he
  have hquv' : qdig7 m (lam₂ * u) = qdig7 m (lam₂ * v) + ρ := by
    have he : eMod7 m (lam₂ * u) (lam₂ * v) = ρ.val * 7 ^ m := by
      have h4v : eMod7 m (lam₁ * u) (lam₁ * v) = (4 : ZMod 7).val * 7 ^ m :=
        heuv.trans rfl
      rw [hescale (by decide : (4 : ZMod 7) ≠ 0) h4v, hρ]
    exact qdig_eq_add_of_e_top hreluv' he
  -- transport `hk` to the digit bound and apply the finite table
  have h2x' : runit7 (lam₂ * d3) = 2 * runit7 (lam₂ * u) := by
    rw [hrz, hrz, runit7_mul, runit7_mul, hcls1 d3 hd3mem, hcls4 u humem,
      show 2 * (↑μ * (runit7 lam₁ * (4 * s))) =
          ↑μ * (runit7 lam₁ * ((2 : ZMod 7) * 4 * s)) by ring,
      show (2 : ZMod 7) * 4 * s = s by
        rw [show (2 : ZMod 7) * 4 = 1 by decide, one_mul]]
  have hk' : etd7 m (lam₂ * u) (lam₂ * d3) ∉ X := by
    rw [show lam₂ * u = lam' * (μ * (lam₁ * u)) by dsimp [lam₂]; ring,
      show lam₂ * d3 = lam' * (μ * (lam₁ * d3)) by dsimp [lam₂]; ring]
    exact hk
  have hbound : 2 * (qdig7 m (lam₂ * v) + ρ) - qdig7 m (lam₂ * d3) ∉ X := by
    have hE' : etd7 m (lam₂ * u) (lam₂ * d3)
        = 2 * qdig7 m (lam₂ * u) - qdig7 m (lam₂ * d3) := by
      unfold etd7; rw [if_pos h2x']
    rw [hE', hquv'] at hk'
    exact hk'
  obtain ⟨t, ht⟩ := hdec _ _ hbound
  exact c65_ii1b_fin hm hpos hunit hs hcls1 hcls4 hlam₂7 hA1eq hA4eq
    t hq13' hq23' rfl hquv' rfl ht

/-- **(ii.1) bad-`ẽ` core**: the normalised picture `e₁₃' = 2·7^m`,
`e₂₃' = 7^m`, `e_{uv}' = 4·7^m` with `ẽ = etd(u, d₃) ∈ {4,5}`.
The `Λ₀`-rescue table fails exactly on `ẽ ∈ {4,5}`, so Lemma 7 applied
to the pair `(u, d₃)` — via `Λ_{ν(e_{u3})}` when `ν < m`, and via `Λ₁`
(with a `×6`/`×3` pre-scale for `r(e_{u3}) ∈ {4,6}`/`{5}`) when
`ν = m` — pushes `ẽ` into a set on which a finite `Λ₀`-rescue table
succeeds. -/
private theorem c65_ii1b {m : ℕ} (hm : 2 ≤ m) {A1 A4 : Finset ℕ}
    (hpos : ∀ d ∈ A1 ∪ A4, 0 < d)
    (hunit : ∀ d ∈ A1 ∪ A4, padicValNat 7 d = 0)
    {s : ZMod 7} (hs : s ≠ 0)
    (hcls1 : ∀ d ∈ A1, runit7 d = s)
    (hcls4 : ∀ d ∈ A4, runit7 d = 4 * s)
    {lam₁ : ℕ} (hlam₁ : ¬ 7 ∣ lam₁)
    {d1 d2 d3 u v : ℕ} (hA1eq : A1 = {d1, d2, d3}) (hA4eq : A4 = {u, v})
    (he13 : eMod7 m (lam₁ * d1) (lam₁ * d3) = 2 * 7 ^ m)
    (he23 : eMod7 m (lam₁ * d2) (lam₁ * d3) = 7 ^ m)
    (heuv : eMod7 m (lam₁ * u) (lam₁ * v) = 4 * 7 ^ m)
    (hbad : etd7 m (lam₁ * u) (lam₁ * d3) ∈ ({4, 5} : Finset (ZMod 7))) :
    ∃ lam : ℕ, ¬ 7 ∣ lam ∧ good7 m lam (A1 ∪ A4) := by
  have hd1mem : d1 ∈ A1 := by rw [hA1eq]; exact Finset.mem_insert_self _ _
  have hd3mem : d3 ∈ A1 := by
    rw [hA1eq]; exact Finset.mem_insert_of_mem
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have humem : u ∈ A4 := by rw [hA4eq]; exact Finset.mem_insert_self _ _
  have hvmem : v ∈ A4 := by
    rw [hA4eq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hlam₁0 : lam₁ ≠ 0 := fun hh => hlam₁ (hh ▸ dvd_zero _)
  have hlam₁pos : 0 < lam₁ := Nat.pos_of_ne_zero hlam₁0
  have hrl1 : runit7 lam₁ ≠ 0 := runit7_ne_zero hlam₁pos
  set s' : ZMod 7 := runit7 lam₁ * s with hs'
  have hs'0 : s' ≠ 0 := mul_ne_zero hrl1 hs
  have hs4'0 : 4 * s' ≠ 0 := mul_ne_zero (by decide) hs'0
  have hpz3 : 0 < lam₁ * d3 := Nat.mul_pos hlam₁pos
    (hpos d3 (Finset.mem_union_left _ hd3mem))
  have hpu : 0 < lam₁ * u := Nat.mul_pos hlam₁pos
    (hpos u (Finset.mem_union_right _ humem))
  have huz3 : padicValNat 7 (lam₁ * d3) = 0 :=
    (padicValNat_mul_seven hlam₁
      (ne_of_gt (hpos d3 (Finset.mem_union_left _ hd3mem)))).trans
      (hunit d3 (Finset.mem_union_left _ hd3mem))
  have huzu : padicValNat 7 (lam₁ * u) = 0 :=
    (padicValNat_mul_seven hlam₁
      (ne_of_gt (hpos u (Finset.mem_union_right _ humem)))).trans
      (hunit u (Finset.mem_union_right _ humem))
  have hrz3 : runit7 (lam₁ * d3) = s' := by
    rw [runit7_mul, hcls1 d3 hd3mem]
  have hru : runit7 (lam₁ * u) = 4 * s' := by
    rw [runit7_mul, hcls4 u humem, hs']; ring
  have hrv : runit7 (lam₁ * v) = 4 * s' := by
    rw [runit7_mul, hcls4 v hvmem, hs']; ring
  have hreluv : residueRelOf (lam₁ * u) (lam₁ * v) = residueRel.same :=
    rel_same (by rw [hru, hrv]) (by rw [hrv]; exact hs4'0)
  have hquv : qdig7 m (lam₁ * u) = qdig7 m (lam₁ * v) + 4 := by
    have he : eMod7 m (lam₁ * u) (lam₁ * v) = (4 : ZMod 7).val * 7 ^ m :=
      heuv.trans rfl
    exact qdig_eq_add_of_e_top hreluv he
  have h2x : runit7 (lam₁ * d3) = 2 * runit7 (lam₁ * u) := by
    rw [runit7_mul, runit7_mul, hcls1 d3 hd3mem, hcls4 u humem,
      show 2 * (runit7 lam₁ * (4 * s)) = runit7 lam₁ * ((2 : ZMod 7) * 4 * s) by ring,
      show (2 : ZMod 7) * 4 * s = s by
        rw [show (2 : ZMod 7) * 4 = 1 by decide, one_mul]]
  have hE : etd7 m (lam₁ * u) (lam₁ * d3)
      = 2 * qdig7 m (lam₁ * u) - qdig7 m (lam₁ * d3) := by
    unfold etd7
    rw [if_pos h2x]
  set e34 := eMod7 m (lam₁ * u) (lam₁ * d3) with he34
  have he34ne : e34 ≠ 0 := by
    intro h0
    have hb := qdig_eMod_sub_etd7 (m := m) (x := lam₁ * u) (y := lam₁ * d3)
    rw [← he34, h0, qdig7_zero, hE] at hb
    have hcon : 2 * qdig7 m (lam₁ * u) - qdig7 m (lam₁ * d3)
        ∈ ({4, 5} : Finset (ZMod 7)) := by
      rw [← hE]; exact hbad
    have hneg : ∀ x : ZMod 7, (0 - x) ∈ ({0, 1, 6} : Finset (ZMod 7)) →
        x ∈ ({0, 1, 6} : Finset (ZMod 7)) := by decide
    have hmem := hneg _ hb
    have hdisj : ({0, 1, 6} : Finset (ZMod 7)) ∩ {4, 5} = ∅ := by decide
    have hmem2 := Finset.mem_inter.mpr ⟨hmem, hcon⟩
    rw [hdisj] at hmem2
    simp at hmem2
  have hν34le : padicValNat 7 e34 ≤ m := enu7_le_of_ne he34ne
  rcases lt_or_eq_of_le hν34le with hν34 | hν34
  · -- `ν(e_{u3}) < m`: Lemma 7(i) pushes `ẽ` out of `{4,5}`; `μ = 1`.
    obtain ⟨k, hk7, hk⟩ := c65_lemma7_i' (by omega : 0 < m) huzu huz3 hpu hpz3
      h2x he34ne hν34 (by decide : apLen ({4, 5} : Finset (ZMod 7)) ≤ 4)
    exact c65_ii1b_post (by omega) hpos hunit hs hcls1 hcls4 hlam₁ hA1eq hA4eq
      he13 he23 heuv
      (lam' := 1 + k * 7 ^ (m - padicValNat 7 e34)) (μ := 1)
      (hlam'r := runit7_multLow hν34)
      (hlam'7 := multLow_not_dvd hν34)
      (hμ7 := by decide) (hμpos := by norm_num)
      (hform := ⟨padicValNat 7 e34, k, hν34, rfl⟩)
      (hk := by simpa using hk)
      (hx1 := by decide) (hx2 := by decide) (hρ := by decide)
      (hdec := c65_ii1_dec1)
  · -- `ν(e_{u3}) = m`: split on `r(e34)`
    have hν34m : padicValNat 7 e34 = m := hν34
    have hr34ne : runit7 e34 ≠ 0 := runit7_ne_zero (Nat.pos_of_ne_zero he34ne)
    have he34top : e34 = (runit7 e34).val * 7 ^ m := by
      have h := residN_top hν34m
      rwa [qdig7_eq_runit7_of_top hν34m, Nat.mod_eq_of_lt (eMod7_lt _ _ _)] at h
    have hr34cases : runit7 e34 = 1 ∨ runit7 e34 = 2 ∨ runit7 e34 = 3 ∨
        runit7 e34 = 4 ∨ runit7 e34 = 5 ∨ runit7 e34 = 6 := by
      revert hr34ne
      generalize runit7 e34 = r
      revert r
      decide
    rcases hr34cases with hr34 | hr34 | hr34 | hr34 | hr34 | hr34
    · -- `r = 1`: `Λ₁`, `X = {4,5}` (ẽ' ∈ {0,1})
      obtain ⟨k, hk7, hk⟩ := c65_lemma7_ii' hm huzu huz3 hpu hpz3 h2x hν34m
        (X := ({4, 5} : Finset (ZMod 7))) (by rw [hr34]; decide)
      exact c65_ii1b_post (by omega) hpos hunit hs hcls1 hcls4 hlam₁ hA1eq hA4eq
        he13 he23 heuv
        (lam' := 1 + k * 7 ^ (m - 1)) (μ := 1)
        (hlam'r := runit7_multLow (by omega : 1 < m))
        (hlam'7 := multLow_not_dvd (by omega : 1 < m))
        (hμ7 := by decide) (hμpos := by norm_num)
        (hform := ⟨1, k, by omega, rfl⟩)
        (hk := by simpa using hk)
        (hx1 := by decide) (hx2 := by decide) (hρ := by decide)
        (hdec := c65_ii1_dec1)
    · -- `r = 2`: same as `r = 1`
      obtain ⟨k, hk7, hk⟩ := c65_lemma7_ii' hm huzu huz3 hpu hpz3 h2x hν34m
        (X := ({4, 5} : Finset (ZMod 7))) (by rw [hr34]; decide)
      exact c65_ii1b_post (by omega) hpos hunit hs hcls1 hcls4 hlam₁ hA1eq hA4eq
        he13 he23 heuv
        (lam' := 1 + k * 7 ^ (m - 1)) (μ := 1)
        (hlam'r := runit7_multLow (by omega : 1 < m))
        (hlam'7 := multLow_not_dvd (by omega : 1 < m))
        (hμ7 := by decide) (hμpos := by norm_num)
        (hform := ⟨1, k, by omega, rfl⟩)
        (hk := by simpa using hk)
        (hx1 := by decide) (hx2 := by decide) (hρ := by decide)
        (hdec := c65_ii1_dec1)
    · -- `r = 3`: same
      obtain ⟨k, hk7, hk⟩ := c65_lemma7_ii' hm huzu huz3 hpu hpz3 h2x hν34m
        (X := ({4, 5} : Finset (ZMod 7))) (by rw [hr34]; decide)
      exact c65_ii1b_post (by omega) hpos hunit hs hcls1 hcls4 hlam₁ hA1eq hA4eq
        he13 he23 heuv
        (lam' := 1 + k * 7 ^ (m - 1)) (μ := 1)
        (hlam'r := runit7_multLow (by omega : 1 < m))
        (hlam'7 := multLow_not_dvd (by omega : 1 < m))
        (hμ7 := by decide) (hμpos := by norm_num)
        (hform := ⟨1, k, by omega, rfl⟩)
        (hk := by simpa using hk)
        (hx1 := by decide) (hx2 := by decide) (hρ := by decide)
        (hdec := c65_ii1_dec1)
    · -- `r = 4`: `×6` pre-scale sends `r` to `3`; mirrored Lemma 7(ii)
      -- (`X = {1,2}`) then the `μ = 6` table
      have h6r : runit7 (6 : ℕ) ≠ 0 := runit7_ne_zero (by norm_num)
      have h6cast : runit7 (6 : ℕ) = (6 : ZMod 7) :=
        runit7_of_padic_zero (padicValNat.eq_zero_of_not_dvd (by decide))
      have hzu6 : padicValNat 7 (6 * (lam₁ * u)) = 0 :=
        (padicValNat_mul_seven (by decide) (ne_of_gt hpu)).trans huzu
      have hz36 : padicValNat 7 (6 * (lam₁ * d3)) = 0 :=
        (padicValNat_mul_seven (by decide) (ne_of_gt hpz3)).trans huz3
      have hpu6 : 0 < 6 * (lam₁ * u) := Nat.mul_pos (by norm_num) hpu
      have hpz36 : 0 < 6 * (lam₁ * d3) := Nat.mul_pos (by norm_num) hpz3
      have h2x6 : runit7 (6 * (lam₁ * d3)) = 2 * runit7 (6 * (lam₁ * u)) := by
        rw [runit7_mul, runit7_mul, runit7_mul, runit7_mul, h6cast,
          hcls1 d3 hd3mem, hcls4 u humem,
          show 2 * ((6 : ZMod 7) * (runit7 lam₁ * (4 * s))) =
              6 * (runit7 lam₁ * ((2 : ZMod 7) * 4 * s)) by ring,
          show (2 : ZMod 7) * 4 * s = s by
            rw [show (2 : ZMod 7) * 4 = 1 by decide, one_mul]]
      have hν346 : padicValNat 7 (eMod7 m (6 * (lam₁ * u)) (6 * (lam₁ * d3)))
          = m := by
        rw [e_smul_top h6r he34top, hr34]
        exact nu_pow7 (by decide) (by decide)
      have hr346 : runit7 (eMod7 m (6 * (lam₁ * u)) (6 * (lam₁ * d3)))
          ∉ ({1, 2} : Finset (ZMod 7)) ∪ ({1, 2} : Finset (ZMod 7)).image (· - 1) := by
        have hre : runit7 (eMod7 m (6 * (lam₁ * u)) (6 * (lam₁ * d3)))
            = (6 : ZMod 7) * runit7 e34 := by
          rw [e_smul_top h6r he34top]
          exact runit7_pow7 (mul_ne_zero (by decide) hr34ne)
        rw [hre, hr34]; decide
      obtain ⟨k, hk7, hk⟩ := c65_lemma7_ii'' hm hzu6 hz36 hpu6 hpz36 h2x6 hν346
        (X := ({1, 2} : Finset (ZMod 7))) hr346
      exact c65_ii1b_post (by omega) hpos hunit hs hcls1 hcls4 hlam₁ hA1eq hA4eq
        he13 he23 heuv
        (lam' := 1 + k * 7 ^ (m - 1)) (μ := 6)
        (hlam'r := runit7_multLow (by omega : 1 < m))
        (hlam'7 := multLow_not_dvd (by omega : 1 < m))
        (hμ7 := by decide) (hμpos := by norm_num)
        (hform := ⟨1, k, by omega, rfl⟩)
        (hk := hk)
        (hx1 := by decide) (hx2 := by decide) (hρ := by decide)
        (hdec := c65_ii1_dec6)
    · -- `r = 5`: `×3` pre-scale sends `r` to `1`; Lemma 7(ii)
      -- (`X = {3,5}`) then the `μ = 3` table
      have h3r : runit7 (3 : ℕ) ≠ 0 := runit7_ne_zero (by norm_num)
      have h3cast : runit7 (3 : ℕ) = (3 : ZMod 7) :=
        runit7_of_padic_zero (padicValNat.eq_zero_of_not_dvd (by decide))
      have hzu3 : padicValNat 7 (3 * (lam₁ * u)) = 0 :=
        (padicValNat_mul_seven (by decide) (ne_of_gt hpu)).trans huzu
      have hz33 : padicValNat 7 (3 * (lam₁ * d3)) = 0 :=
        (padicValNat_mul_seven (by decide) (ne_of_gt hpz3)).trans huz3
      have hpu3 : 0 < 3 * (lam₁ * u) := Nat.mul_pos (by norm_num) hpu
      have hpz33 : 0 < 3 * (lam₁ * d3) := Nat.mul_pos (by norm_num) hpz3
      have h2x3 : runit7 (3 * (lam₁ * d3)) = 2 * runit7 (3 * (lam₁ * u)) := by
        rw [runit7_mul, runit7_mul, runit7_mul, runit7_mul, h3cast,
          hcls1 d3 hd3mem, hcls4 u humem,
          show 2 * ((3 : ZMod 7) * (runit7 lam₁ * (4 * s))) =
              3 * (runit7 lam₁ * ((2 : ZMod 7) * 4 * s)) by ring,
          show (2 : ZMod 7) * 4 * s = s by
            rw [show (2 : ZMod 7) * 4 = 1 by decide, one_mul]]
      have hν343 : padicValNat 7 (eMod7 m (3 * (lam₁ * u)) (3 * (lam₁ * d3)))
          = m := by
        rw [e_smul_top h3r he34top, hr34]
        exact nu_pow7 (by decide) (by decide)
      have hr345 : runit7 (eMod7 m (3 * (lam₁ * u)) (3 * (lam₁ * d3)))
          ∉ ({3, 5} : Finset (ZMod 7)) ∪ ({3, 5} : Finset (ZMod 7)).image (· + 1) := by
        have hre : runit7 (eMod7 m (3 * (lam₁ * u)) (3 * (lam₁ * d3)))
            = (3 : ZMod 7) * runit7 e34 := by
          rw [e_smul_top h3r he34top]
          exact runit7_pow7 (mul_ne_zero (by decide) hr34ne)
        rw [hre, hr34]; decide
      obtain ⟨k, hk7, hk⟩ := c65_lemma7_ii' hm hzu3 hz33 hpu3 hpz33 h2x3 hν343
        (X := ({3, 5} : Finset (ZMod 7))) hr345
      exact c65_ii1b_post (by omega) hpos hunit hs hcls1 hcls4 hlam₁ hA1eq hA4eq
        he13 he23 heuv
        (lam' := 1 + k * 7 ^ (m - 1)) (μ := 3)
        (hlam'r := runit7_multLow (by omega : 1 < m))
        (hlam'7 := multLow_not_dvd (by omega : 1 < m))
        (hμ7 := by decide) (hμpos := by norm_num)
        (hform := ⟨1, k, by omega, rfl⟩)
        (hk := hk)
        (hx1 := by decide) (hx2 := by decide) (hρ := by decide)
        (hdec := c65_ii1_dec3)
    · -- `r = 6`: mirrored Lemma 7(ii) (`X = {4,5}`, image `· - 1`:
      -- exclusion `{3,4,5}`) then the `μ = 1` table
      obtain ⟨k, hk7, hk⟩ := c65_lemma7_ii'' hm huzu huz3 hpu hpz3 h2x hν34m
        (X := ({4, 5} : Finset (ZMod 7))) (by rw [hr34]; decide)
      exact c65_ii1b_post (by omega) hpos hunit hs hcls1 hcls4 hlam₁ hA1eq hA4eq
        he13 he23 heuv
        (lam' := 1 + k * 7 ^ (m - 1)) (μ := 1)
        (hlam'r := runit7_multLow (by omega : 1 < m))
        (hlam'7 := multLow_not_dvd (by omega : 1 < m))
        (hμ7 := by decide) (hμpos := by norm_num)
        (hform := ⟨1, k, by omega, rfl⟩)
        (hk := by simpa using hk)
        (hx1 := by decide) (hx2 := by decide) (hρ := by decide)
        (hdec := c65_ii1_dec1)

/-! ### §8 Case (ii.1) with `h = m` (the ratio-2 top branch) -/

/-- **Case (ii.1), `h = m`**: ratio-2 pure-top case.  A `Λ_m`-scalar
normalises `e₂₃' = 7^m`, `e₁₃' = 2·7^m` (so `ℓ(A₁) ≤ 3`); then for
`e₄₅' := e(c·d₄, c·d₅)`:
* `e₄₅' = 0`: `A₄` collapses to a single digit (`ℓ ≤ 1`);
* `ν(e₄₅') < m`: a `Λ_{ν₄₅}`-multiplier sets `q(e₄₅') = 0` (`ℓ(A₄) ≤ 2`),
  while `Λ_{ν₄₅}` preserves the pure-top `A₁`-differences;
* `ν(e₄₅') = m`: orient `d₄ ↔ d₅` so `r(e) ∈ {1,2,4}`; for `r ∈ {1,2}`
  the pair digit-difference is `r ≤ 2` (`ℓ(A₄) ≤ 3`); for `r = 4` the
  `Λ₀`-rescue works unless `ẽ ∈ {4,5}` (`c65_ii1b_post`), and otherwise
  `c65_ii1b` supplies the Lemma-7 multiplier. -/
private theorem c65_case_ii1_top {m : ℕ} (hm : 2 ≤ m) {A1 A4 : Finset ℕ}
    (hpos : ∀ d ∈ A1 ∪ A4, 0 < d)
    (hunit : ∀ d ∈ A1 ∪ A4, padicValNat 7 d = 0)
    {s : ZMod 7} (hs : s ≠ 0)
    (hcls1 : ∀ d ∈ A1, runit7 d = s)
    (hcls4 : ∀ d ∈ A4, runit7 d = 4 * s)
    {d1 d2 d3 : ℕ} (hA1eq : A1 = {d1, d2, d3})
    {d4 d5 : ℕ} (hA4eq : A4 = {d4, d5})
    (he13 : eMod7 m d1 d3 ≠ 0) (he23 : eMod7 m d2 d3 ≠ 0)
    (hν23m : padicValNat 7 (eMod7 m d2 d3) = m)
    (hν13m : padicValNat 7 (eMod7 m d1 d3) = m)
    (hrat : runit7 (eMod7 m d1 d3) = 2 * runit7 (eMod7 m d2 d3)) :
    ∃ lam : ℕ, ¬ 7 ∣ lam ∧ good7 m lam (A1 ∪ A4) := by
  have hd1mem : d1 ∈ A1 := by
    rw [hA1eq]; exact Finset.mem_insert_self _ _
  have hd2mem : d2 ∈ A1 := by
    rw [hA1eq]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hd3mem : d3 ∈ A1 := by
    rw [hA1eq]
    exact Finset.mem_insert_of_mem
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have hd4mem : d4 ∈ A4 := by
    rw [hA4eq]; exact Finset.mem_insert_self _ _
  have hd5mem : d5 ∈ A4 := by
    rw [hA4eq]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hr1 : runit7 d1 = s := hcls1 d1 hd1mem
  have hr2 : runit7 d2 = s := hcls1 d2 hd2mem
  have hr3 : runit7 d3 = s := hcls1 d3 hd3mem
  have hr4 : runit7 d4 = 4 * s := hcls4 d4 hd4mem
  have hr5 : runit7 d5 = 4 * s := hcls4 d5 hd5mem
  have hs4_0 : (4 : ZMod 7) * s ≠ 0 := mul_ne_zero (by decide) hs
  have he13top : eMod7 m d1 d3 = ((2 : ZMod 7)
      * runit7 (eMod7 m d2 d3)).val * 7 ^ m := by
    have h := residN_top hν13m
    rw [qdig7_eq_runit7_of_top hν13m, Nat.mod_eq_of_lt (eMod7_lt _ _ _),
      hrat] at h
    exact h
  have he23top : eMod7 m d2 d3 = (runit7 (eMod7 m d2 d3)).val * 7 ^ m := by
    have h := residN_top hν23m
    rwa [qdig7_eq_runit7_of_top hν23m,
      Nat.mod_eq_of_lt (eMod7_lt _ _ _)] at h
  -- `Λ_m`-scalar sending `e₂₃ ↦ 7^m` (hence `e₁₃ ↦ 2·7^m`).
  obtain ⟨c, hc0, hc7, hce, hqc⟩ := exists_top_scalar_set hν23m he23
    (by decide : (1 : ZMod 7) ≠ 0)
  have hcl : ¬ 7 ∣ c := fun h => by
    have := Nat.le_of_dvd hc0 h; omega
  have hrcast : runit7 c = (c : ZMod 7) :=
    runit7_of_padic_zero (padicValNat.eq_zero_of_not_dvd hcl)
  have hc0z : (c : ZMod 7) ≠ 0 := by
    have := runit7_ne_zero hc0; rwa [hrcast] at this
  have hrc : runit7 c ≠ 0 := by rwa [hrcast]
  have hsc : ∀ d : ℕ, runit7 (c * d) = (c : ZMod 7) * runit7 d :=
    fun d => by rw [runit7_mul, hrcast]
  have hca : (c : ZMod 7) * runit7 (eMod7 m d2 d3) = 1 := by
    have h := qdig7_multTop (l := c) hν23m
    rw [hqc] at h
    exact h.symm
  have he23c : eMod7 m (c * d2) (c * d3) = (1 : ZMod 7).val * 7 ^ m := by
    rw [e_smul_top hrc he23top, hca]
  have he13c : eMod7 m (c * d1) (c * d3) = (2 : ZMod 7).val * 7 ^ m := by
    have h2a : (c : ZMod 7) * ((2 : ZMod 7) * runit7 (eMod7 m d2 d3))
        = 2 := by linear_combination 2 * hca
    rw [e_smul_top hrc he13top, h2a]
  have hrel23' : residueRelOf (c * d2) (c * d3) = residueRel.same :=
    rel_same (by rw [hsc d2, hsc d3, hr2, hr3])
      (by rw [hsc d3, hr3]; exact mul_ne_zero hc0z hs)
  have hrel13' : residueRelOf (c * d1) (c * d3) = residueRel.same :=
    rel_same (by rw [hsc d1, hsc d3, hr1, hr3])
      (by rw [hsc d3, hr3]; exact mul_ne_zero hc0z hs)
  have hrel45' : residueRelOf (c * d4) (c * d5) = residueRel.same :=
    rel_same (by rw [hsc d4, hsc d5, hr4, hr5])
      (by rw [hsc d5, hr5]; exact mul_ne_zero hc0z hs4_0)
  have hq23c : qdig7 m (c * d2) = qdig7 m (c * d3) + 1 :=
    qdig_eq_add_of_e_top hrel23' he23c
  have hq13c : qdig7 m (c * d1) = qdig7 m (c * d3) + 2 :=
    qdig_eq_add_of_e_top hrel13' he13c
  have hap1c : apLen ((A1.image fun d => c * d).image (qdig7 m)) ≤ 3 := by
    have heq : (A1.image fun d => c * d).image (qdig7 m)
        = {qdig7 m (c * d3) + 2, qdig7 m (c * d3) + 1,
            qdig7 m (c * d3)} := by
      simp only [hA1eq, Finset.image_insert, Finset.image_singleton,
        hq13c, hq23c]
    rw [heq]
    apply (apLen_le_iff _ 3 (by norm_num)).mpr
    refine ⟨qdig7 m (c * d3), ?_⟩
    intro z hz
    rw [mem_cycIv]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl
    · rw [add_sub_cancel_left]; decide
    · rw [add_sub_cancel_left]; decide
    · rw [sub_self]; decide
  -- Oriented `A₄`-finisher: for `e(cu,cv) = w·7^m` with `w ∈ {1,2,4}`.
  have horiented : ∀ u v : ℕ, A4 = {u, v} → ∀ w : ZMod 7,
      eMod7 m (c * u) (c * v) = w.val * 7 ^ m →
      w ∈ ({1, 2, 4} : Finset (ZMod 7)) →
      ∃ lam : ℕ, ¬ 7 ∣ lam ∧ good7 m lam (A1 ∪ A4) := by
    intro u v hA4eq' w heuv hw
    have humem : u ∈ A4 := by
      rw [hA4eq']; exact Finset.mem_insert_self _ _
    have hvmem : v ∈ A4 := by
      rw [hA4eq']
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    have hru : runit7 (c * u) = (c : ZMod 7) * (4 * s) := by
      rw [hsc u, hcls4 u humem]
    have hrv : runit7 (c * v) = (c : ZMod 7) * (4 * s) := by
      rw [hsc v, hcls4 v hvmem]
    have hreluv : residueRelOf (c * u) (c * v) = residueRel.same :=
      rel_same (by rw [hru, hrv])
        (by rw [hrv]; exact mul_ne_zero hc0z hs4_0)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl
    · -- `w = 1`: pair digit-difference `1`.
      have hquv : qdig7 m (c * u) = qdig7 m (c * v) + 1 :=
        qdig_eq_add_of_e_top hreluv heuv
      have hap4 : apLen ((A4.image fun d => c * d).image (qdig7 m)) ≤ 3 := by
        rw [hA4eq', Finset.image_insert, Finset.image_singleton,
          Finset.image_insert, Finset.image_singleton, hquv]
        apply apLen_two_le3
        rw [add_sub_cancel_left]; decide
      exact c65_finish (by omega) hpos hunit hs hcls1 hcls4 hcl
        (Or.inl ⟨hap1c, hap4⟩)
    · -- `w = 2`: pair digit-difference `2`.
      have hquv : qdig7 m (c * u) = qdig7 m (c * v) + 2 :=
        qdig_eq_add_of_e_top hreluv heuv
      have hap4 : apLen ((A4.image fun d => c * d).image (qdig7 m)) ≤ 3 := by
        rw [hA4eq', Finset.image_insert, Finset.image_singleton,
          Finset.image_insert, Finset.image_singleton, hquv]
        apply apLen_two_le3
        rw [add_sub_cancel_left]; decide
      exact c65_finish (by omega) hpos hunit hs hcls1 hcls4 hcl
        (Or.inl ⟨hap1c, hap4⟩)
    · -- `w = 4`: `Λ₀`-rescue (`c65_ii1b_post`) unless `ẽ ∈ {4,5}`.
      have heuv4 : eMod7 m (c * u) (c * v) = 4 * 7 ^ m := by
        have hv : (4 : ZMod 7).val = 4 := by decide
        rwa [hv] at heuv
      have he13cN : eMod7 m (c * d1) (c * d3) = 2 * 7 ^ m := by
        have hv : (2 : ZMod 7).val = 2 := by decide
        rwa [hv] at he13c
      have he23cN : eMod7 m (c * d2) (c * d3) = 7 ^ m := by
        have hv : (1 : ZMod 7).val = 1 := by decide
        rwa [hv, one_mul] at he23c
      by_cases hbad : etd7 m (c * u) (c * d3) ∈ ({4, 5} : Finset (ZMod 7))
      · exact c65_ii1b hm hpos hunit hs hcls1 hcls4 hcl hA1eq hA4eq'
          he13cN he23cN heuv4 hbad
      · exact c65_ii1b_post (by omega) hpos hunit hs hcls1 hcls4 hcl
          hA1eq hA4eq' he13cN he23cN heuv4
          (lam' := 1) (μ := 1)
          (hlam'r := runit7_eq_one_of_mod7 (by norm_num))
          (hlam'7 := by decide) (hμ7 := by decide) (hμpos := by norm_num)
          (hform := ⟨0, 0, by omega, by simp⟩)
          (hk := by simpa using hbad)
          (hx1 := by decide) (hx2 := by decide) (hρ := by decide)
          (hdec := c65_ii1_dec1)
  -- Dispatch on `e₄₅' := e(c·d₄, c·d₅)`.
  by_cases he45 : eMod7 m (c * d4) (c * d5) = 0
  · -- `e₄₅' = 0`: the two `A₄`-residues agree, giving one digit.
    have hd45res : (c * d4) % 7 ^ (m + 1) = (c * d5) % 7 ^ (m + 1) :=
      eq_resid_of_eMod7_eq_zero he45 hrel45'
    have hq45 : qdig7 m (c * d4) = qdig7 m (c * d5) := qdig7_congr hd45res
    have hap4 : apLen ((A4.image fun d => c * d).image (qdig7 m)) ≤ 3 := by
      have heq : (A4.image fun d => c * d).image (qdig7 m)
          = {qdig7 m (c * d5)} := by
        simp only [hA4eq, Finset.image_insert, Finset.image_singleton,
          hq45]
        rw [Finset.insert_eq_of_mem (Finset.mem_singleton_self _)]
      rw [heq]
      apply le_trans ?_ (by norm_num : (1 : ℕ) ≤ 3)
      apply (apLen_le_iff _ 1 (by norm_num)).mpr
      exact ⟨qdig7 m (c * d5), by
        intro z hz
        rw [Finset.mem_singleton] at hz
        rw [hz, mem_cycIv, sub_self]; decide⟩
    exact c65_finish (by omega) hpos hunit hs hcls1 hcls4 hcl
      (Or.inl ⟨hap1c, hap4⟩)
  · rcases lt_or_eq_of_le (enu7_le_of_ne he45) with hν45 | hν45
    · -- `ν(e₄₅') < m`: `Λ_{ν₄₅}` sets `q(e₄₅') = 0` and preserves the
      -- pure-top `A₁`-differences.
      set j := padicValNat 7 (eMod7 m (c * d4) (c * d5)) with hj
      obtain ⟨k, hk7, hkq⟩ := exists_multLow_set_qdig hν45 rfl he45 0
      set lam₂ := 1 + k * 7 ^ (m - j) with hlam₂def
      have hlam₂r : runit7 lam₂ = 1 := by
        rw [hlam₂def]; exact runit7_multLow hν45
      have hlam₂7 : ¬ 7 ∣ lam₂ := by
        rw [hlam₂def]; exact multLow_not_dvd hν45
      have hlam7 : ¬ 7 ∣ lam₂ * c :=
        Nat.prime_seven.not_dvd_mul hlam₂7 hcl
      have he23L : eMod7 m (lam₂ * c * d2) (lam₂ * c * d3)
          = (1 : ZMod 7).val * 7 ^ m := by
        rw [mul_assoc, mul_assoc, eMod7_mul hlam₂r, he23c, hlam₂def]
        exact top_resid_multLow hν45 (by decide)
      have he13L : eMod7 m (lam₂ * c * d1) (lam₂ * c * d3)
          = (2 : ZMod 7).val * 7 ^ m := by
        rw [mul_assoc, mul_assoc, eMod7_mul hlam₂r, he13c, hlam₂def]
        exact top_resid_multLow hν45 (by decide)
      have hscL : ∀ d : ℕ,
          runit7 (lam₂ * c * d) = (c : ZMod 7) * runit7 d :=
        fun d => by rw [mul_assoc, runit7_mul, hlam₂r, one_mul, hsc]
      have hrel23L : residueRelOf (lam₂ * c * d2) (lam₂ * c * d3)
          = residueRel.same :=
        rel_same (by rw [hscL, hscL, hr2, hr3])
          (by rw [hscL, hr3]; exact mul_ne_zero hc0z hs)
      have hrel13L : residueRelOf (lam₂ * c * d1) (lam₂ * c * d3)
          = residueRel.same :=
        rel_same (by rw [hscL, hscL, hr1, hr3])
          (by rw [hscL, hr3]; exact mul_ne_zero hc0z hs)
      have hrel45L : residueRelOf (lam₂ * c * d4) (lam₂ * c * d5)
          = residueRel.same :=
        rel_same (by rw [hscL, hscL, hr4, hr5])
          (by rw [hscL, hr5]; exact mul_ne_zero hc0z hs4_0)
      have hq23L : qdig7 m (lam₂ * c * d2)
          = qdig7 m (lam₂ * c * d3) + 1 :=
        qdig_eq_add_of_e_top hrel23L he23L
      have hq13L : qdig7 m (lam₂ * c * d1)
          = qdig7 m (lam₂ * c * d3) + 2 :=
        qdig_eq_add_of_e_top hrel13L he13L
      have hap1 : apLen
          ((A1.image fun d => lam₂ * c * d).image (qdig7 m)) ≤ 3 := by
        have heq : (A1.image fun d => lam₂ * c * d).image (qdig7 m)
            = {qdig7 m (lam₂ * c * d3) + 2, qdig7 m (lam₂ * c * d3) + 1,
                qdig7 m (lam₂ * c * d3)} := by
          simp only [hA1eq, Finset.image_insert, Finset.image_singleton,
            hq13L, hq23L]
        rw [heq]
        apply (apLen_le_iff _ 3 (by norm_num)).mpr
        refine ⟨qdig7 m (lam₂ * c * d3), ?_⟩
        intro z hz
        rw [mem_cycIv]
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl | rfl
        · rw [add_sub_cancel_left]; decide
        · rw [add_sub_cancel_left]; decide
        · rw [sub_self]; decide
      have hqe : qdig7 m (eMod7 m (lam₂ * c * d4) (lam₂ * c * d5)) = 0 := by
        rw [mul_assoc, mul_assoc, eMod7_mul hlam₂r,
          qdig7_congr (Nat.mod_mod _ _)]
        exact hkq
      have hap4 : apLen
          ((A4.image fun d => lam₂ * c * d).image (qdig7 m)) ≤ 2 := by
        have heq : (A4.image fun d => lam₂ * c * d).image (qdig7 m)
            = ({lam₂ * c * d4, lam₂ * c * d5} : Finset ℕ).image
              (qdig7 m) := by
          rw [hA4eq]
          simp only [Finset.image_insert, Finset.image_singleton]
        rw [heq]
        exact c65_pair_len2' hrel45L hqe
      exact c65_finish (by omega) hpos hunit hs hcls1 hcls4 hlam7
        (Or.inr (Or.inl ⟨by omega, hap4⟩))
    · -- `ν(e₄₅') = m`: orient `d₄ ↔ d₅` so `r ∈ {1,2,4}`.
      have he45top : eMod7 m (c * d4) (c * d5)
          = (runit7 (eMod7 m (c * d4) (c * d5))).val * 7 ^ m := by
        have h := residN_top hν45
        rwa [qdig7_eq_runit7_of_top hν45,
          Nat.mod_eq_of_lt (eMod7_lt _ _ _)] at h
      have hr45 : runit7 (eMod7 m (c * d4) (c * d5)) ≠ 0 :=
        runit7_ne_zero (Nat.pos_of_ne_zero he45)
      have hrel54 : residueRelOf (c * d5) (c * d4) = residueRel.same :=
        rel_same (by rw [hsc d5, hsc d4, hr5, hr4])
          (by rw [hsc d4, hr4]; exact mul_ne_zero hc0z hs4_0)
      by_cases hsmall : runit7 (eMod7 m (c * d4) (c * d5))
          ∈ ({1, 2, 4} : Finset (ZMod 7))
      · exact horiented d4 d5 hA4eq
          (runit7 (eMod7 m (c * d4) (c * d5))) he45top hsmall
      · have h54 : padicValNat 7 (eMod7 m (c * d5) (c * d4))
            = padicValNat 7 (eMod7 m (c * d4) (c * d5)) ∧
            runit7 (eMod7 m (c * d5) (c * d4))
              = - runit7 (eMod7 m (c * d4) (c * d5)) :=
          enu7_neg hrel45' hrel54
        have h54ν : padicValNat 7 (eMod7 m (c * d5) (c * d4)) = m := by
          rw [h54.1]; exact hν45
        have h54top : eMod7 m (c * d5) (c * d4)
            = (- runit7 (eMod7 m (c * d4) (c * d5))).val * 7 ^ m := by
          have h := residN_top h54ν
          rwa [qdig7_eq_runit7_of_top h54ν,
            Nat.mod_eq_of_lt (eMod7_lt _ _ _), h54.2] at h
        have h54small : - runit7 (eMod7 m (c * d4) (c * d5))
            ∈ ({1, 2, 4} : Finset (ZMod 7)) := by
          revert hsmall hr45
          generalize runit7 (eMod7 m (c * d4) (c * d5)) = r
          revert r
          decide
        have hA4eq' : A4 = ({d5, d4} : Finset ℕ) :=
          hA4eq.trans (Finset.pair_comm d4 d5)
        exact horiented d5 d4 hA4eq'
          (- runit7 (eMod7 m (c * d4) (c * d5))) h54top h54small

/-! ### §7 `lemma9_ii` (`j = 3`) with explicit `Λ_h` multiplier

Clones of the `j = 3` branch internals of `lemma9_ii` (Case5mL10) and of
the `remark8_ii'` difference bound (Case5mC63), needed so that the
returned multiplier is *seen* to be a `Λ_h` element `1 + k·7^{m−h}` —
required by the order-of-application arguments in `c65_case_ii2_low`. -/

/-- `q`-digit of `lam * e` from a `ZMod N` subtraction cast
(`lam * e ≡ A − B`).  Clone of `Case5mL10.qdig_smul_eMod_eq`. -/
private theorem c65_qdig_smul_eMod_eq {m lam e A B : ℕ}
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

/-- `eMod7` of an element with itself is `0` (no positivity needed;
clone of `Case5mC63.eMod7_self'`). -/
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
    have h : x % 7 ^ (m + 1) + 7 ^ (m + 1) - x % 7 ^ (m + 1)
        = 7 ^ (m + 1) := by
      omega
    rw [h, Nat.mod_self]

/-- A `Λ_j`-multiplier preserves the `mod 7^m` part of a `7^j`-divisible
element (clone of `Case5mL10.multLow_low`; distinct from `multLow_low'`
which keeps `mod 7^{m+1}` of `7^{j+1}`-divisible elements). -/
private theorem c65_multLow_low {m j k w : ℕ} (hjm : j ≤ m)
    (hw : 7 ^ j ∣ w) :
    ((1 + k * 7 ^ (m - j)) * w) % 7 ^ m = w % 7 ^ m := by
  obtain ⟨u, rfl⟩ := hw
  rw [add_mul, one_mul]
  have hP : k * 7 ^ (m - j) * (7 ^ j * u) = 7 ^ m * (k * u) := by
    have e : k * 7 ^ (m - j) * (7 ^ j * u)
        = k * u * (7 ^ (m - j) * 7 ^ j) := by
      ring
    rw [e, ← pow_add, Nat.sub_add_cancel hjm]
    ring
  rw [hP, Nat.add_mul_mod_self_left]

/-- Negation preserves `{0,1,6} ⊆ ZMod 7` (clone of C63/L10). -/
private theorem c65_neg_mem_016 {s : ZMod 7}
    (h : s ∈ ({0, 1, 6} : Finset (ZMod 7))) :
    -s ∈ ({0, 1, 6} : Finset (ZMod 7)) := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at h ⊢
  rcases h with rfl | rfl | rfl <;> decide

/-- `−s − 1` for `s ∈ {0,1,5,6}` stays in `{0,1,5,6}` (clone). -/
private theorem c65_neg_sub_one_mem_0156 {s : ZMod 7}
    (h : s ∈ ({0, 1, 5, 6} : Finset (ZMod 7))) :
    -s - 1 ∈ ({0, 1, 5, 6} : Finset (ZMod 7)) := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at h ⊢
  rcases h with rfl | rfl | rfl | rfl <;> decide

/-- `−s − 1` for `s ∈ {0,5,6}` stays in `{0,1,5,6}` (clone). -/
private theorem c65_neg_sub_one_mem_056 {s : ZMod 7}
    (h : s ∈ ({0, 5, 6} : Finset (ZMod 7))) :
    -s - 1 ∈ ({0, 1, 5, 6} : Finset (ZMod 7)) := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at h ⊢
  rcases h with rfl | rfl | rfl <;> decide

/-- `s − δ` for `s ∈ {0,1,6}`, `δ ∈ {0,1}` stays in `{0,1,5,6}`
(clone). -/
private theorem c65_sub_borrow_mem_0156 {s d : ZMod 7}
    (hs : s ∈ ({0, 1, 6} : Finset (ZMod 7))) (hd : d = 0 ∨ d = 1) :
    s - d ∈ ({0, 1, 5, 6} : Finset (ZMod 7)) := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hs ⊢
  rcases hs with rfl | rfl | rfl <;> rcases hd with rfl | rfl <;> decide

/-- The `j = 3` multiplier table (clone of `Case5mL10.lemma9_ii_table3`):
for all `qx qy : ZMod 7` some `t ∈ {0,5,6}` gives
`q(λx) = qx + 2qy + 5t ∈ {0,1,5,6}` and
`q(λx) − q(λy) = qx + 2qy + 4t ∈ {0,1,6}`. -/
private theorem c65_l9ii3_table :
    ∀ qx qy : ZMod 7, ∃ t : ZMod 7,
      t ∈ ({0, 5, 6} : Finset (ZMod 7)) ∧
      (qx + 2 * qy + 5 * t) ∈ ({0, 1, 5, 6} : Finset (ZMod 7)) ∧
      (qx + 2 * qy + 4 * t) ∈ ({0, 1, 6} : Finset (ZMod 7)) := by
  decide

/-- `apLen ≤ 3` when all pairwise differences lie in `{0,±1,±2}`
(`{0,1,2,5,6}`) — the `remark8_ii` variant used by `lemma9_ii` (`j=3`),
clone of `Case5mC63.remark8_ii'_dec`. -/
private theorem c65_remark8_ii'_dec :
    ∀ B : Finset (ZMod 7),
      (∀ x ∈ B, ∀ y ∈ B, x - y ∈ ({0, 1, 2, 5, 6} : Finset (ZMod 7))) →
      apLen B ≤ 3 := by
  set_option maxRecDepth 16384 in
  decide

private theorem c65_remark8_ii' {B : Finset (ZMod 7)}
    (hB : ∀ x ∈ B, ∀ y ∈ B, x - y ∈ ({0, 1, 2, 5, 6} : Finset (ZMod 7))) :
    apLen B ≤ 3 := c65_remark8_ii'_dec B hB

/-- Bridge for `c65_remark8_ii'` (clone of `Case5mC63.remark8_ii_int`):
pair-residue digits in `{0,1,5,6}` yield `q`-differences in
`{0,1,2,5,6}` via `qdig_eMod_sub`. -/
private theorem c65_remark8_ii_int {m : ℕ} {B : Finset ℕ}
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

/-- `c65_l9ii3` — the `j = 3` case of `lemma9_ii` with the multiplier
*form* exposed: the returned `λ = 1 + k·7^{m−h}` (`k < 7`) is the
`Λ_h` realizer needed for the order-of-application arguments in the
`(ii.2)` `h < m` branch (the abstract `lemma9_ii` hides `λ`'s shape).
Clone of `Case5mC63.c63_l9ii3`. -/
private theorem c65_l9ii3 {m : ℕ} {b1 b2 b3 : ℕ}
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
    obtain ⟨t, ht, htx, hdxy⟩ := c65_l9ii3_table (qdig7 m x) (qdig7 m y)
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
      rw [hlamdef]; exact c65_multLow_low hνm.le hdvx
    have hlowy : (lam * y) % 7 ^ m = y % 7 ^ m := by
      rw [hlamdef]; exact c65_multLow_low hνm.le hdvy
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
      exact c65_qdig_smul_eMod_eq hcast
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
          exact c65_sub_borrow_mem_0156 hdxy (Or.inr rfl)
        · rw [if_neg hδ]
          exact c65_sub_borrow_mem_0156 hdxy (Or.inl rfl)
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
          exact c65_sub_borrow_mem_0156 (c65_neg_mem_016 hdxy) (Or.inr rfl)
        · rw [if_neg hδ]
          exact c65_sub_borrow_mem_0156 (c65_neg_mem_016 hdxy) (Or.inl rfl)
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
        exact c65_neg_sub_one_mem_0156 htx
      · -- (b3,b2): `−λy`
        have hcast : ((lam * eMod7 m b3 b2 : ℕ) : ZMod (7 ^ (m + 1)))
            = ((0 : ℕ) : ZMod _) - ((lam * y : ℕ) : ZMod _) := by
          simp only [Nat.cast_mul, Nat.cast_zero]
          rw [hc32]; ring
        rw [eval hcast, qdig7_zero, Nat.zero_mod,
          if_pos (Nat.pos_of_ne_zero hlowy0), hqy]
        have hsimp : (0 : ZMod 7) - t - 1 = -t - 1 := by ring
        rw [hsimp]
        exact c65_neg_sub_one_mem_056 ht
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
    have hdiff := c65_remark8_ii_int hBLsame hBL
    have hlen : apLen (BL.image (qdig7 m)) ≤ 3 := c65_remark8_ii' hdiff
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

set_option synthInstance.maxSize 16384 in
set_option maxRecDepth 524288 in
set_option maxHeartbeats 3000000 in
/-- §6.5 (ii.2) low subcase `e₄₅ = 0`: `lemma9_ii` (`j = 3`) on the
relabeled triple `(d₂,d₁,d₃)`; `A₄` collapses. -/
private theorem c65_ii2_low_zero {m : ℕ} (hm : 0 < m) {A1 A4 : Finset ℕ}
    (hpos : ∀ d ∈ A1 ∪ A4, 0 < d)
    (hunit : ∀ d ∈ A1 ∪ A4, padicValNat 7 d = 0)
    {s : ZMod 7} (hs : s ≠ 0)
    (hcls1 : ∀ d ∈ A1, runit7 d = s)
    (hcls4 : ∀ d ∈ A4, runit7 d = 4 * s)
    {d1 d2 d3 d4 d5 : ℕ}
    (hA1eq : A1 = {d1, d2, d3}) (hA4eq : A4 = {d4, d5})
    (hp1 : 0 < d1) (hp2 : 0 < d2) (hp3 : 0 < d3)
    (hp4 : 0 < d4) (hp5 : 0 < d5)
    (hu1 : padicValNat 7 d1 = 0) (hu2 : padicValNat 7 d2 = 0)
    (hu3 : padicValNat 7 d3 = 0) (hu4 : padicValNat 7 d4 = 0)
    (hu5 : padicValNat 7 d5 = 0)
    (hr1 : runit7 d1 = s) (hr2 : runit7 d2 = s) (hr3 : runit7 d3 = s)
    (hr4 : runit7 d4 = 4 * s) (hr5 : runit7 d5 = 4 * s)
    (hs4_0 : (4 : ZMod 7) * s ≠ 0)
    (hνeq : padicValNat 7 (eMod7 m d1 d3)
      = padicValNat 7 (eMod7 m d2 d3))
    (hrat : runit7 (eMod7 m d1 d3) = 3 * runit7 (eMod7 m d2 d3))
    (hlm : padicValNat 7 (eMod7 m d2 d3) < m)
    (he45 : eMod7 m d4 d5 = 0) :
    ∃ lam : ℕ, ¬ 7 ∣ lam ∧ good7 m lam (A1 ∪ A4) := by
  classical
  have hset_eq : ({d2, d1, d3} : Finset ℕ) = {d1, d2, d3} :=
    Finset.insert_comm d2 d1 _
  obtain ⟨lam, hlam7, _hqe, _hpairs, _hj2, hlen⟩ := lemma9_ii
    ⟨hp2, hp1, hp3⟩ ⟨hu2, hu1, hu3⟩
    ⟨hr2.trans hr1.symm, hr1.trans hr3.symm⟩
    hνeq.symm (by omega) (Or.inr rfl) (by simpa using hrat)
  have hlam0 : lam ≠ 0 := fun hh => hlam7 (hh ▸ dvd_zero _)
  have hrl : runit7 lam ≠ 0 := runit7_ne_zero (Nat.pos_of_ne_zero hlam0)
  have hlen1 : apLen ((A1.image (fun d => lam * d)).image (qdig7 m)) ≤ 3 := by
    have himg : (A1.image (fun d => lam * d)).image (qdig7 m)
        = ({d2, d1, d3} : Finset ℕ).image (fun d => qdig7 m (lam * d)) := by
      rw [hA1eq, hset_eq, Finset.image_image]; rfl
    rw [himg]; exact hlen
  have hrel45' : residueRelOf (lam * d4) (lam * d5) = residueRel.same := by
    apply rel_same
    · rw [runit7_mul, runit7_mul, hr4, hr5]
    · rw [runit7_mul, hr5]
      exact mul_ne_zero hrl hs4_0
  have he45' : eMod7 m (lam * d4) (lam * d5) = 0 := by
    rw [eMod7_smul hrl, he45, mul_zero, Nat.zero_mod]
  have hq45 : qdig7 m (lam * d4) = qdig7 m (lam * d5) :=
    qdig7_congr (eq_resid_of_eMod7_eq_zero he45' hrel45')
  have hap4 : apLen ((A4.image (fun d => lam * d)).image (qdig7 m)) ≤ 1 := by
    have heq : (A4.image (fun d => lam * d)).image (qdig7 m)
        = ({qdig7 m (lam * d5)} : Finset (ZMod 7)) := by
      rw [hA4eq]
      simp only [Finset.image_insert, Finset.image_singleton]
      rw [hq45]
      ext z; simp
    rw [heq]; exact apLen_singleton_le1 _
  exact c65_finish hm hpos hunit hs hcls1 hcls4 hlam7
    (Or.inr (Or.inr (by omega)))

set_option synthInstance.maxSize 16384 in
set_option maxRecDepth 524288 in
set_option maxHeartbeats 3000000 in
/-- `λ₂ ∈ Λ_{ν₄₅}` preserves every level-`h` `A₁` pair residue
(`residN_multLow7`); the diagonal cases are `e = 0`. -/
private theorem c65_ii2_low_lt_fix {m lam1 lam2 k2 d1 d2 d3 d4 d5 : ℕ}
    (hlam1nd : ¬ 7 ∣ lam1) (hrl1 : runit7 lam1 ≠ 0)
    (hlam2r : runit7 lam2 = 1)
    (hlam2def : lam2
      = 1 + k2 * 7 ^ (m - padicValNat 7 (eMod7 m (lam1 * d4) (lam1 * d5))))
    (hν45' : padicValNat 7 (eMod7 m (lam1 * d4) (lam1 * d5))
      = padicValNat 7 (eMod7 m d4 d5))
    (hν45'lt : padicValNat 7 (eMod7 m (lam1 * d4) (lam1 * d5)) < m)
    (h45lt : padicValNat 7 (eMod7 m d4 d5)
      < padicValNat 7 (eMod7 m d2 d3))
    (hνeq : padicValNat 7 (eMod7 m d1 d3)
      = padicValNat 7 (eMod7 m d2 d3))
    (hν12 : padicValNat 7 (eMod7 m d1 d2)
      = padicValNat 7 (eMod7 m d2 d3))
    (hν21 : padicValNat 7 (eMod7 m d2 d1)
      = padicValNat 7 (eMod7 m d1 d2))
    (hν31 : padicValNat 7 (eMod7 m d3 d1)
      = padicValNat 7 (eMod7 m d1 d3))
    (hν32 : padicValNat 7 (eMod7 m d3 d2)
      = padicValNat 7 (eMod7 m d2 d3)) :
    ∀ x ∈ ({d1, d2, d3} : Finset ℕ), ∀ y ∈ ({d1, d2, d3} : Finset ℕ),
      eMod7 m (lam2 * (lam1 * x)) (lam2 * (lam1 * y))
        = eMod7 m (lam1 * x) (lam1 * y) := by
  intro x hx y hy
  rw [eMod7_mul hlam2r]
  by_cases he0 : eMod7 m (lam1 * x) (lam1 * y) = 0
  · rw [he0]; simp
  · have hνe : padicValNat 7 (eMod7 m (lam1 * x) (lam1 * y))
        = padicValNat 7 (eMod7 m x y) := by
      apply padicValNat_eMod7_smul hlam1nd
      intro h0
      exact he0 (by rw [eMod7_smul hrl1, h0, mul_zero, Nat.zero_mod])
    have hνxy : padicValNat 7 (eMod7 m x y)
        = padicValNat 7 (eMod7 m d2 d3) := by
      rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton]
        at hx hy
      rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
      · exfalso; exact he0 (by rw [eMod7_smul hrl1, eMod7_self',
          mul_zero, Nat.zero_mod])
      · exact hν12
      · exact hνeq
      · exact hν21.trans hν12
      · exfalso; exact he0 (by rw [eMod7_smul hrl1, eMod7_self',
          mul_zero, Nat.zero_mod])
      · rfl
      · exact hν31.trans hνeq
      · exact hν32
      · exfalso; exact he0 (by rw [eMod7_smul hrl1, eMod7_self',
          mul_zero, Nat.zero_mod])
    rw [hlam2def,
      residN_multLow7 hν45'lt (by rw [hνe, hνxy, hν45']; exact h45lt),
      Nat.mod_eq_of_lt (eMod7_lt _ _ _)]


set_option synthInstance.maxSize 16384 in
set_option maxRecDepth 524288 in
set_option maxHeartbeats 3000000 in
/-- `ν(e₄₅) < h` tail: with `lam = lam₂·lam₁`, `lam₁` the `lemma9_ii`
multiplier (pair digits in `{0,1,5,6}`, preserved by `λ₂` via `hfix`),
`λ₂` zeroing `q(e₄₅')` — conclude `good7` via `c65_remark8_ii'` and
`c65_pair_len2'`. -/
private theorem c65_ii2_low_lt_tail {m : ℕ} (hm : 0 < m)
    {A1 A4 : Finset ℕ}
    (hpos : ∀ d ∈ A1 ∪ A4, 0 < d)
    (hunit : ∀ d ∈ A1 ∪ A4, padicValNat 7 d = 0)
    {s : ZMod 7} (hs : s ≠ 0)
    (hcls1 : ∀ d ∈ A1, runit7 d = s)
    (hcls4 : ∀ d ∈ A4, runit7 d = 4 * s)
    {d1 d2 d3 d4 d5 lam1 lam2 k2 : ℕ}
    (hA1eq : A1 = {d1, d2, d3}) (hA4eq : A4 = {d4, d5})
    (hp1 : 0 < d1) (hp2 : 0 < d2) (hp3 : 0 < d3)
    (hr1 : runit7 d1 = s) (hr2 : runit7 d2 = s) (hr3 : runit7 d3 = s)
    (hr4 : runit7 d4 = 4 * s) (hr5 : runit7 d5 = 4 * s)
    (hs4_0 : (4 : ZMod 7) * s ≠ 0)
    (hlam1nd : ¬ 7 ∣ lam1) (hlam1pos : 0 < lam1)
    (hlam2nd : ¬ 7 ∣ lam2) (hlam2pos : 0 < lam2)
    (hlam2r : runit7 lam2 = 1)
    (hlam2def : lam2
      = 1 + k2 * 7 ^ (m - padicValNat 7 (eMod7 m (lam1 * d4) (lam1 * d5))))
    (hk2q : qdig7 m ((1 + k2 * 7 ^ (m - padicValNat 7
        (eMod7 m (lam1 * d4) (lam1 * d5))))
        * eMod7 m (lam1 * d4) (lam1 * d5)) = 0)
    (hpairs1 : ∀ x ∈ ({d2, d1, d3} : Finset ℕ),
      ∀ y ∈ ({d2, d1, d3} : Finset ℕ),
      qdig7 m (eMod7 m (lam1 * x) (lam1 * y))
        ∈ ({0, 1, 5, 6} : Finset (ZMod 7)))
    (hfix : ∀ x ∈ ({d1, d2, d3} : Finset ℕ),
      ∀ y ∈ ({d1, d2, d3} : Finset ℕ),
      eMod7 m (lam2 * (lam1 * x)) (lam2 * (lam1 * y))
        = eMod7 m (lam1 * x) (lam1 * y)) :
    ∃ lam : ℕ, ¬ 7 ∣ lam ∧ good7 m lam (A1 ∪ A4) := by
  classical
  have hrl1 : runit7 lam1 ≠ 0 := runit7_ne_zero hlam1pos
  have hset_eq : ({d2, d1, d3} : Finset ℕ) = {d1, d2, d3} :=
    Finset.insert_comm d2 d1 _

  set lam := lam2 * lam1 with hlamdef
  have hlamnd : ¬ 7 ∣ lam :=
    Nat.prime_seven.not_dvd_mul hlam2nd hlam1nd
  have hposB : ∀ d ∈ ({d1, d2, d3} : Finset ℕ), 0 < d := by
    intro d hd
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl | rfl <;> assumption
  have hclsB : ∀ d ∈ ({d1, d2, d3} : Finset ℕ), runit7 d = s := by
    intro d hd
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl | rfl <;> assumption
  set B := ({d1, d2, d3} : Finset ℕ).image (fun d => lam2 * (lam1 * d))
    with hBdef
  have hBsame : ∀ u ∈ B, ∀ v ∈ B,
      residueRelOf u v = residueRel.same := by
    intro u hu v hv
    obtain ⟨u', hu', rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨v', hv', rfl⟩ := Finset.mem_image.mp hv
    apply rel_same _ (runit7_ne_zero (Nat.mul_pos hlam2pos
      (Nat.mul_pos hlam1pos (hposB v' hv'))))
    rw [runit7_mul, runit7_mul, runit7_mul, runit7_mul, hlam2r,
      one_mul, one_mul, hclsB u' hu', hclsB v' hv']
  have hBpair : ∀ u ∈ B, ∀ v ∈ B,
      qdig7 m (eMod7 m u v) ∈ ({0, 1, 5, 6} : Finset (ZMod 7)) := by
    intro u hu v hv
    obtain ⟨u', hu', rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨v', hv', rfl⟩ := Finset.mem_image.mp hv
    rw [hfix u' hu' v' hv']
    exact hpairs1 u' (by rw [hset_eq]; exact hu')
      v' (by rw [hset_eq]; exact hv')
  have hdiff := c65_remark8_ii_int hBsame hBpair
  have haplen1 : apLen (B.image (qdig7 m)) ≤ 3 := c65_remark8_ii' hdiff
  have hap1 : apLen ((A1.image (fun d => lam * d)).image (qdig7 m))
      ≤ 3 := by
    have himg : (A1.image (fun d => lam * d)).image (qdig7 m)
        = B.image (qdig7 m) := by
      rw [hA1eq, hBdef, Finset.image_image, Finset.image_image]
      apply Finset.image_congr
      intro d _
      show qdig7 m (lam * d) = qdig7 m (lam2 * (lam1 * d))
      rw [hlamdef]
      exact congrArg _ (mul_assoc _ _ _)
    rw [himg]; exact haplen1
  have hrel45'' : residueRelOf (lam2 * (lam1 * d4)) (lam2 * (lam1 * d5))
      = residueRel.same := by
    apply rel_same
    · have e1 : runit7 (lam2 * (lam1 * d4))
          = runit7 lam2 * (runit7 lam1 * runit7 d4) := by
        rw [runit7_mul, runit7_mul]
      have e2 : runit7 (lam2 * (lam1 * d5))
          = runit7 lam2 * (runit7 lam1 * runit7 d5) := by
        rw [runit7_mul, runit7_mul]
      rw [e1, e2, hlam2r, one_mul, one_mul, hr4, hr5]
    · rw [runit7_mul, runit7_mul, hlam2r, one_mul, hr5]
      exact mul_ne_zero hrl1 hs4_0
  have hq45'' : qdig7 m
      (eMod7 m (lam2 * (lam1 * d4)) (lam2 * (lam1 * d5))) = 0 := by
    rw [eMod7_mul hlam2r, qdig7_congr (Nat.mod_mod _ _), hlam2def, hk2q]
  have hap4 : apLen ((A4.image (fun d => lam * d)).image (qdig7 m))
      ≤ 2 := by
    have heq : (A4.image (fun d => lam * d)).image (qdig7 m)
        = ({lam2 * (lam1 * d4), lam2 * (lam1 * d5)} : Finset ℕ).image
          (qdig7 m) := by
      rw [hA4eq]
      simp only [Finset.image_insert, Finset.image_singleton]
      rw [show lam * d4 = lam2 * (lam1 * d4) by
          rw [hlamdef]; exact mul_assoc _ _ _,
        show lam * d5 = lam2 * (lam1 * d5) by
          rw [hlamdef]; exact mul_assoc _ _ _]
    rw [heq]
    exact c65_pair_len2' hrel45'' hq45''
  exact c65_finish hm hpos hunit hs hcls1 hcls4 hlamnd
    (Or.inr (Or.inr (by omega)))


set_option synthInstance.maxSize 16384 in
set_option maxRecDepth 524288 in
set_option maxHeartbeats 3000000 in
/-- §6.5 (ii.2) low subcase `ν(e₄₅) < h`: `lemma9_ii` first, then
`Λ_{ν₄₅}` zeroes `q(e₄₅')`; all `A₁` pair residues sit at level
`h > ν₄₅` and are preserved verbatim by `residN_multLow7`. -/
private theorem c65_ii2_low_lt {m : ℕ} (hm : 0 < m) {A1 A4 : Finset ℕ}
    (hpos : ∀ d ∈ A1 ∪ A4, 0 < d)
    (hunit : ∀ d ∈ A1 ∪ A4, padicValNat 7 d = 0)
    {s : ZMod 7} (hs : s ≠ 0)
    (hcls1 : ∀ d ∈ A1, runit7 d = s)
    (hcls4 : ∀ d ∈ A4, runit7 d = 4 * s)
    {d1 d2 d3 d4 d5 : ℕ}
    (hA1eq : A1 = {d1, d2, d3}) (hA4eq : A4 = {d4, d5})
    (hp1 : 0 < d1) (hp2 : 0 < d2) (hp3 : 0 < d3)
    (hp4 : 0 < d4) (hp5 : 0 < d5)
    (hu1 : padicValNat 7 d1 = 0) (hu2 : padicValNat 7 d2 = 0)
    (hu3 : padicValNat 7 d3 = 0) (hu4 : padicValNat 7 d4 = 0)
    (hu5 : padicValNat 7 d5 = 0)
    (hr1 : runit7 d1 = s) (hr2 : runit7 d2 = s) (hr3 : runit7 d3 = s)
    (hr4 : runit7 d4 = 4 * s) (hr5 : runit7 d5 = 4 * s)
    (hs4_0 : (4 : ZMod 7) * s ≠ 0)
    (hνeq : padicValNat 7 (eMod7 m d1 d3)
      = padicValNat 7 (eMod7 m d2 d3))
    (hrat : runit7 (eMod7 m d1 d3) = 3 * runit7 (eMod7 m d2 d3))
    (hlm : padicValNat 7 (eMod7 m d2 d3) < m)
    (he45 : eMod7 m d4 d5 ≠ 0)
    (h45lt : padicValNat 7 (eMod7 m d4 d5)
      < padicValNat 7 (eMod7 m d2 d3))
    (hν12 : padicValNat 7 (eMod7 m d1 d2)
      = padicValNat 7 (eMod7 m d2 d3))
    (hν21 : padicValNat 7 (eMod7 m d2 d1)
      = padicValNat 7 (eMod7 m d1 d2))
    (hν31 : padicValNat 7 (eMod7 m d3 d1)
      = padicValNat 7 (eMod7 m d1 d3))
    (hν32 : padicValNat 7 (eMod7 m d3 d2)
      = padicValNat 7 (eMod7 m d2 d3)) :
    ∃ lam : ℕ, ¬ 7 ∣ lam ∧ good7 m lam (A1 ∪ A4) := by
  classical
  have hset_eq : ({d2, d1, d3} : Finset ℕ) = {d1, d2, d3} :=
    Finset.insert_comm d2 d1 _
  -- `q(e₄₅')`; all `A₁` pair residues sit at level `h > ν₄₅` and are
  -- preserved verbatim by `residN_multLow7`.
  obtain ⟨lam1, hlam1nd, _hqe1, hpairs1, _hj21, _hlen1'⟩ := lemma9_ii
    ⟨hp2, hp1, hp3⟩ ⟨hu2, hu1, hu3⟩
    ⟨hr2.trans hr1.symm, hr1.trans hr3.symm⟩
    hνeq.symm (by omega) (Or.inr rfl) (by simpa using hrat)
  have hlam1pos : 0 < lam1 :=
    Nat.pos_of_ne_zero (fun hh => hlam1nd (hh ▸ dvd_zero _))
  have hrl1 : runit7 lam1 ≠ 0 := runit7_ne_zero hlam1pos
  have he45' : eMod7 m (lam1 * d4) (lam1 * d5) ≠ 0 :=
    eMod7_smul_ne_zero hlam1nd he45
  have hν45' : padicValNat 7 (eMod7 m (lam1 * d4) (lam1 * d5))
      = padicValNat 7 (eMod7 m d4 d5) := padicValNat_eMod7_smul hlam1nd he45
  have hν45'lt : padicValNat 7 (eMod7 m (lam1 * d4) (lam1 * d5)) < m := by
    rw [hν45']; omega
  obtain ⟨k2, hk2lt, hk2q⟩ := exists_multLow_set_qdig
    (j := padicValNat 7 (eMod7 m (lam1 * d4) (lam1 * d5)))
    (x := eMod7 m (lam1 * d4) (lam1 * d5)) hν45'lt rfl he45'
    (0 : ZMod 7)
  set lam2 : ℕ :=
    1 + k2 * 7 ^ (m - padicValNat 7 (eMod7 m (lam1 * d4) (lam1 * d5)))
    with hlam2def
  have hlam2r : runit7 lam2 = 1 := by
    rw [hlam2def]; exact runit7_multLow hν45'lt
  have hlam2nd : ¬ 7 ∣ lam2 := by
    rw [hlam2def]; exact multLow_not_dvd hν45'lt
  have hlam2pos : 0 < lam2 := by
    rw [hlam2def]; exact Nat.add_pos_left Nat.one_pos _
  -- `λ₂ ∈ Λ_{ν₄₅}` preserves every `A₁` pair residue (level `h > ν₄₅`)
  -- `λ₂ ∈ Λ_{ν₄₅}` preserves every `A₁` pair residue (level `h > ν₄₅`)
  have hfix := c65_ii2_low_lt_fix hlam1nd hrl1 hlam2r hlam2def hν45'
    hν45'lt h45lt hνeq hν12 hν21 hν31 hν32
  exact c65_ii2_low_lt_tail hm hpos hunit hs hcls1 hcls4 hA1eq hA4eq
    hp1 hp2 hp3 hr1 hr2 hr3 hr4 hr5 hs4_0
    hlam1nd hlam1pos hlam2nd hlam2pos hlam2r hlam2def hk2q hpairs1 hfix

set_option synthInstance.maxSize 16384 in
set_option maxRecDepth 524288 in
set_option maxHeartbeats 3000000 in
/-- §6.5 (ii.2) low subcase `ν(e₄₅) = h`: orient `(u,v)` so
`r(e_{uv}) = w·r₁₃`, `w ∈ {1,2,4}`; the matching anchor
`E ∈ {e₁₃, e₃₂, e₂₁}` has `r(E) = w·r₁₃ = r(e_{uv})`, so
`f = (e_{uv} − E) % N` has level `> h` (`level_of_sub_gt`) and is
fixed by `λ₂` first. -/
private theorem c65_ii2_low_eq {m : ℕ} (hm : 0 < m) {A1 A4 : Finset ℕ}
    (hpos : ∀ d ∈ A1 ∪ A4, 0 < d)
    (hunit : ∀ d ∈ A1 ∪ A4, padicValNat 7 d = 0)
    {s : ZMod 7} (hs : s ≠ 0)
    (hcls1 : ∀ d ∈ A1, runit7 d = s)
    (hcls4 : ∀ d ∈ A4, runit7 d = 4 * s)
    {d1 d2 d3 d4 d5 : ℕ}
    (hA1eq : A1 = {d1, d2, d3}) (hA4eq : A4 = {d4, d5})
    (hp1 : 0 < d1) (hp2 : 0 < d2) (hp3 : 0 < d3)
    (hp4 : 0 < d4) (hp5 : 0 < d5)
    (hu1 : padicValNat 7 d1 = 0) (hu2 : padicValNat 7 d2 = 0)
    (hu3 : padicValNat 7 d3 = 0) (hu4 : padicValNat 7 d4 = 0)
    (hu5 : padicValNat 7 d5 = 0)
    (hr1 : runit7 d1 = s) (hr2 : runit7 d2 = s) (hr3 : runit7 d3 = s)
    (hr4 : runit7 d4 = 4 * s) (hr5 : runit7 d5 = 4 * s)
    (hs4_0 : (4 : ZMod 7) * s ≠ 0)
    (hνeq : padicValNat 7 (eMod7 m d1 d3)
      = padicValNat 7 (eMod7 m d2 d3))
    (hrat : runit7 (eMod7 m d1 d3) = 3 * runit7 (eMod7 m d2 d3))
    (hlm : padicValNat 7 (eMod7 m d2 d3) < m)
    (he13 : eMod7 m d1 d3 ≠ 0) (he23 : eMod7 m d2 d3 ≠ 0)
    (he12 : eMod7 m d1 d2 ≠ 0) (he21 : eMod7 m d2 d1 ≠ 0)
    (he31 : eMod7 m d3 d1 ≠ 0) (he32 : eMod7 m d3 d2 ≠ 0)
    (he45 : eMod7 m d4 d5 ≠ 0) (he54 : eMod7 m d5 d4 ≠ 0)
    (hrel45 : residueRelOf d4 d5 = residueRel.same)
    (hrel54 : residueRelOf d5 d4 = residueRel.same)
    (h45eq : padicValNat 7 (eMod7 m d4 d5)
      = padicValNat 7 (eMod7 m d2 d3))
    (hν12 : padicValNat 7 (eMod7 m d1 d2)
      = padicValNat 7 (eMod7 m d2 d3))
    (hν21 : padicValNat 7 (eMod7 m d2 d1)
      = padicValNat 7 (eMod7 m d1 d2))
    (hν31 : padicValNat 7 (eMod7 m d3 d1)
      = padicValNat 7 (eMod7 m d1 d3))
    (hν32 : padicValNat 7 (eMod7 m d3 d2)
      = padicValNat 7 (eMod7 m d2 d3))
    (hr12 : runit7 (eMod7 m d1 d2)
      = runit7 (eMod7 m d1 d3) - runit7 (eMod7 m d2 d3))
    (hr21 : runit7 (eMod7 m d2 d1) = - runit7 (eMod7 m d1 d2))
    (hr31 : runit7 (eMod7 m d3 d1) = - runit7 (eMod7 m d1 d3))
    (hr32 : runit7 (eMod7 m d3 d2) = - runit7 (eMod7 m d2 d3)) :
    ∃ lam : ℕ, ¬ 7 ∣ lam ∧ good7 m lam (A1 ∪ A4) := by
  classical
  have hr13ne : runit7 (eMod7 m d1 d3) ≠ 0 :=
    runit7_ne_zero (Nat.pos_of_ne_zero he13)
  -- `w ∈ {1,2,4}`; the matching anchor `E ∈ {e₁₃, e₃₂, e₂₁}` has
  -- `r(E) = w·r₁₃ = r(e_{uv})`, so `f = (e_{uv} − E) % N` has level
  -- `> h` (`level_of_sub_gt`) and is fixed by `λ₂` first.
  have hν54 : padicValNat 7 (eMod7 m d5 d4)
      = padicValNat 7 (eMod7 m d4 d5) := enu7_sym hrel45 hrel54
  have hr54 : runit7 (eMod7 m d5 d4)
      = - runit7 (eMod7 m d4 d5) := runit7_eMod7_neg hrel45 hrel54
  have hmain : ∀ u v : ℕ, A4 = ({u, v} : Finset ℕ) →
      0 < u → 0 < v → padicValNat 7 u = 0 → padicValNat 7 v = 0 →
      runit7 u = 4 * s → runit7 v = 4 * s →
      eMod7 m u v ≠ 0 →
      padicValNat 7 (eMod7 m u v) = padicValNat 7 (eMod7 m d2 d3) →
      runit7 (eMod7 m u v)
        ∈ ({runit7 (eMod7 m d1 d3), 2 * runit7 (eMod7 m d1 d3),
            4 * runit7 (eMod7 m d1 d3)} : Finset (ZMod 7)) →
      ∃ lam : ℕ, ¬ 7 ∣ lam ∧ good7 m lam (A1 ∪ A4) := by
    intro u v hA4eq' hpu hpv huu huv hru hrv huv0 hνuv hruv
    -- fixed-orientation core: `(b₁,b₂,b₃)` with anchor `E = e(b₂,b₃)`
    -- and `f = (e_{uv} + N − E) % N` at level `> h` (or `f = 0`).
    have hcore : ∀ {b1 b2 b3 : ℕ}, A1 = ({b1, b2, b3} : Finset ℕ) →
        0 < b1 → 0 < b2 → 0 < b3 →
        padicValNat 7 b1 = 0 → padicValNat 7 b2 = 0 →
        padicValNat 7 b3 = 0 →
        runit7 b1 = s → runit7 b2 = s → runit7 b3 = s →
        eMod7 m b1 b3 ≠ 0 → eMod7 m b2 b3 ≠ 0 →
        padicValNat 7 (eMod7 m b1 b3)
          = padicValNat 7 (eMod7 m d2 d3) →
        padicValNat 7 (eMod7 m b2 b3)
          = padicValNat 7 (eMod7 m d2 d3) →
        runit7 (eMod7 m b2 b3)
          = 3 * runit7 (eMod7 m b1 b3) →
        runit7 (eMod7 m u v) = runit7 (eMod7 m b2 b3) →
        ∃ lam : ℕ, ¬ 7 ∣ lam ∧ good7 m lam (A1 ∪ A4) := by
      intro b1 b2 b3 hA1eq' hpb1 hpb2 hpb3 hub1 hub2 hub3
        hrb1 hrb2 hrb3 heb13 heb23 hνb13 hνb23 hratb hrE
      have hN : 0 < 7 ^ (m + 1) := Nat.pow_pos (by norm_num)
      have hElt : eMod7 m b2 b3 < 7 ^ (m + 1) := eMod7_lt _ _ _
      have huvlt : eMod7 m u v < 7 ^ (m + 1) := eMod7_lt _ _ _
      set f := (eMod7 m u v + 7 ^ (m + 1) - eMod7 m b2 b3) % 7 ^ (m + 1)
        with hfdef
      -- `e_{uv} = (E + f) % N`
      have huvE : eMod7 m u v
          = (eMod7 m b2 b3 + f) % 7 ^ (m + 1) := by
        by_cases hcase : eMod7 m u v < eMod7 m b2 b3
        · have hfv : f = eMod7 m u v + 7 ^ (m + 1) - eMod7 m b2 b3 := by
            rw [hfdef]
            exact Nat.mod_eq_of_lt (by omega)
          rw [hfv, show eMod7 m b2 b3
                + (eMod7 m u v + 7 ^ (m + 1) - eMod7 m b2 b3)
                = eMod7 m u v + 7 ^ (m + 1) by omega,
            Nat.add_mod_right, Nat.mod_eq_of_lt huvlt]
        · have hfv : f = eMod7 m u v - eMod7 m b2 b3 := by
            rw [hfdef, show eMod7 m u v + 7 ^ (m + 1) - eMod7 m b2 b3
                = 7 ^ (m + 1) + (eMod7 m u v - eMod7 m b2 b3) by omega,
              Nat.add_mod_left]
            exact Nat.mod_eq_of_lt (by omega)
          rw [hfv, show eMod7 m b2 b3 + (eMod7 m u v - eMod7 m b2 b3)
              = eMod7 m u v by omega]
          exact (Nat.mod_eq_of_lt huvlt).symm
      -- `f = 0` or `ν(f) > h`
      have hflev : f = 0 ∨ padicValNat 7 (eMod7 m d2 d3)
          < padicValNat 7 f := by
        have h := level_of_sub_gt (m := m) (u := eMod7 m u v)
          (v := eMod7 m b2 b3) huv0 heb23 hνuv hνb23 hElt hlm hrE
        rwa [← hfdef] at h
      -- `λ₂` fixes `f` (or `f = 0` already)
      obtain ⟨lam2, hlam2pos, hlam2nd, hlam2r0, hf2⟩ :
          ∃ lam2 : ℕ, 0 < lam2 ∧ ¬ 7 ∣ lam2 ∧ runit7 lam2 ≠ 0 ∧
            (qdig7 m ((lam2 * f) % 7 ^ (m + 1)) = 0 ∨
              (lam2 * f) % 7 ^ (m + 1) = 7 ^ m) := by
        rcases hflev with hf0 | hfh
        · exact ⟨1, Nat.one_pos, by decide,
            runit7_ne_zero (by norm_num : (0 : ℕ) < 1),
            Or.inl (by rw [hf0, mul_zero, Nat.zero_mod, qdig7_zero])⟩
        · have hf0' : f ≠ 0 := by
            intro h0
            rw [h0, padicValNat.zero] at hfh
            exact absurd hfh (Nat.not_lt_zero _)
          have hflt : f < 7 ^ (m + 1) := Nat.mod_lt _ hN
          have hνfle : padicValNat 7 f ≤ m := by
            by_contra hc
            push_neg at hc
            exact hf0' (Nat.eq_zero_of_dvd_of_lt
              ((Nat.pow_dvd_iff_le_padicValNat (by norm_num) hf0').mpr
                (by omega : m + 1 ≤ padicValNat 7 f)) hflt)
          rcases lt_or_eq_of_le hνfle with hνfm | hνfm
          · obtain ⟨k2, hk2lt, hk2q⟩ := exists_multLow_set_qdig
              (j := padicValNat 7 f) (x := f) hνfm rfl hf0' (0 : ZMod 7)
            exact ⟨1 + k2 * 7 ^ (m - padicValNat 7 f),
              Nat.add_pos_left Nat.one_pos _, multLow_not_dvd hνfm,
              by rw [runit7_multLow hνfm]; exact one_ne_zero,
              Or.inl (by rw [qdig7_congr (Nat.mod_mod _ _)]; exact hk2q)⟩
          · obtain ⟨c, hcpos, hc7, hcmod, hqc⟩ :=
              exists_top_scalar_set hνfm hf0' (t := 1) (by decide)
            refine ⟨c, hcpos, fun hd =>
                absurd (Nat.le_of_dvd hcpos hd) (by omega),
                runit7_ne_zero hcpos, Or.inr ?_⟩
            rw [hcmod, show (1 : ZMod 7).val = 1 from by decide, one_mul]
      -- level/unit transport for `mod`-rescaled `e`'s under `λ₂`
      have hνmod : ∀ x : ℕ, x ≠ 0 → padicValNat 7 x ≤ m →
          padicValNat 7 ((lam2 * x) % 7 ^ (m + 1))
            = padicValNat 7 x := by
        intro x hx0 hxm
        have hνl : padicValNat 7 (lam2 * x) = padicValNat 7 x :=
          padicValNat_mul_seven hlam2nd hx0
        have hmod : (lam2 * x) % 7 ^ (m + 1)
            = ((lam2 * x) % 7 ^ (m + 1)) % 7 ^ (m + 1) :=
          (Nat.mod_mod _ _).symm
        exact (padicValNat_eq_of_mod hmod (by rw [hνl]; exact hxm)
          (mul_ne_zero (ne_of_gt hlam2pos) hx0)).symm.trans hνl
      have hrmod : ∀ x : ℕ, x ≠ 0 → padicValNat 7 x ≤ m →
          runit7 ((lam2 * x) % 7 ^ (m + 1))
            = runit7 lam2 * runit7 x := by
        intro x hx0 hxm
        have hνl : padicValNat 7 (lam2 * x) = padicValNat 7 x :=
          padicValNat_mul_seven hlam2nd hx0
        have hmod : (lam2 * x) % 7 ^ (m + 1)
            = ((lam2 * x) % 7 ^ (m + 1)) % 7 ^ (m + 1) :=
          (Nat.mod_mod _ _).symm
        rw [← runit7_eq_of_mod hmod (by rw [hνl]; exact hxm)
          (mul_ne_zero (ne_of_gt hlam2pos) hx0), runit7_mul]
      have hνle : padicValNat 7 (eMod7 m d2 d3) ≤ m := le_of_lt hlm
      have heb13'e : eMod7 m (lam2 * b1) (lam2 * b3)
          = (lam2 * eMod7 m b1 b3) % 7 ^ (m + 1) := eMod7_smul hlam2r0
      have heb23'e : eMod7 m (lam2 * b2) (lam2 * b3)
          = (lam2 * eMod7 m b2 b3) % 7 ^ (m + 1) := eMod7_smul hlam2r0
      have hνb13' : padicValNat 7 (eMod7 m (lam2 * b1) (lam2 * b3))
          = padicValNat 7 (eMod7 m d2 d3) := by
        rw [heb13'e, hνmod _ heb13 (by rw [hνb13]; exact hνle), hνb13]
      have hνb23' : padicValNat 7 (eMod7 m (lam2 * b2) (lam2 * b3))
          = padicValNat 7 (eMod7 m d2 d3) := by
        rw [heb23'e, hνmod _ heb23 (by rw [hνb23]; exact hνle), hνb23]
      have hrb13' : runit7 (eMod7 m (lam2 * b1) (lam2 * b3))
          = runit7 lam2 * runit7 (eMod7 m b1 b3) := by
        rw [heb13'e, hrmod _ heb13 (by rw [hνb13]; exact hνle)]
      have hrb23' : runit7 (eMod7 m (lam2 * b2) (lam2 * b3))
          = runit7 lam2 * runit7 (eMod7 m b2 b3) := by
        rw [heb23'e, hrmod _ heb23 (by rw [hνb23]; exact hνle)]
      obtain ⟨lam9, ⟨k9, hk9lt, hlam9eq⟩, hlam9nd, hqE, _hpairs9,
          hlen9⟩ := c65_l9ii3
        ⟨Nat.mul_pos hlam2pos hpb1, Nat.mul_pos hlam2pos hpb2,
          Nat.mul_pos hlam2pos hpb3⟩
        ⟨by rw [padicValNat_mul_seven hlam2nd (ne_of_gt hpb1), hub1],
         by rw [padicValNat_mul_seven hlam2nd (ne_of_gt hpb2), hub2],
         by rw [padicValNat_mul_seven hlam2nd (ne_of_gt hpb3), hub3]⟩
        ⟨by rw [runit7_mul, runit7_mul, hrb1, hrb2],
         by rw [runit7_mul, runit7_mul, hrb2, hrb3]⟩
        (by rw [hνb13', hνb23']) (by rw [hνb23']; exact hlm)
        (by rw [hrb23', hrb13', hratb]; ring)
      -- `λ₉ = 1 + k₉·7^{m−h}` preserves `f' = (λ₂·f) % N`
      -- (`ν(f') = ν(f) > h`)
      have hlam9r : runit7 lam9 = 1 := by
        rw [hlam9eq]
        exact runit7_multLow (by rw [hνb23']; exact hlm)
      set lam := lam9 * lam2 with hlam
      have hlamnd : ¬ 7 ∣ lam :=
        Nat.prime_seven.not_dvd_mul hlam9nd hlam2nd
      have hffix : (lam9 * ((lam2 * f) % 7 ^ (m + 1))) % 7 ^ (m + 1)
          = (lam2 * f) % 7 ^ (m + 1) := by
        rcases eq_or_ne f 0 with hf0 | hf0
        · rw [hf0]; simp
        · rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, hlam9eq]
          exact residN_multLow7 (by rw [hνb23']; exact hlm)
            (by rw [hνb23', padicValNat_mul_seven hlam2nd hf0]
                rcases hflev with hh | hh
                · exact absurd hh hf0
                · exact hh)
      -- `e_{uv}'' = (E'' + f') % N`
      have heuv' : eMod7 m (lam2 * u) (lam2 * v)
          = (eMod7 m (lam2 * b2) (lam2 * b3)
              + (lam2 * f) % 7 ^ (m + 1)) % 7 ^ (m + 1) := by
        rw [eMod7_smul hlam2r0, eMod7_smul hlam2r0, huvE,
          Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, Nat.mul_add,
          Nat.add_mod]
      have hE''def : eMod7 m (lam9 * (lam2 * b2)) (lam9 * (lam2 * b3))
          = (lam9 * eMod7 m (lam2 * b2) (lam2 * b3)) % 7 ^ (m + 1) :=
        eMod7_mul hlam9r
      have heuv'' : eMod7 m (lam9 * (lam2 * u)) (lam9 * (lam2 * v))
          = (eMod7 m (lam9 * (lam2 * b2)) (lam9 * (lam2 * b3))
              + (lam2 * f) % 7 ^ (m + 1)) % 7 ^ (m + 1) := by
        rw [eMod7_mul hlam9r, heuv',
          Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, Nat.mul_add,
          Nat.add_mod, ← hE''def, hffix]
      -- `q(e_{uv}'') ∈ {0,1,5,6}`
      have hqfin : qdig7 m
          (eMod7 m (lam9 * (lam2 * u)) (lam9 * (lam2 * v)))
          ∈ ({0, 1, 5, 6} : Finset (ZMod 7)) := by
        rw [heuv'']
        rcases hf2 with hq0 | htop
        · have hδ := qdig7_add_016 (m := m)
            (u := eMod7 m (lam9 * (lam2 * b2)) (lam9 * (lam2 * b3)))
            (v := (lam2 * f) % 7 ^ (m + 1))
          simp only [Finset.mem_insert, Finset.mem_singleton] at hδ hqE ⊢
          rcases hδ with hδ | hδ
          · have hq : qdig7 m
                ((eMod7 m (lam9 * (lam2 * b2)) (lam9 * (lam2 * b3))
                  + (lam2 * f) % 7 ^ (m + 1)) % 7 ^ (m + 1))
                = qdig7 m
                  (eMod7 m (lam9 * (lam2 * b2)) (lam9 * (lam2 * b3))) := by
              have hsum : qdig7 m
                    ((eMod7 m (lam9 * (lam2 * b2)) (lam9 * (lam2 * b3))
                      + (lam2 * f) % 7 ^ (m + 1)) % 7 ^ (m + 1))
                    = qdig7 m
                        (eMod7 m (lam9 * (lam2 * b2)) (lam9 * (lam2 * b3)))
                      + qdig7 m ((lam2 * f) % 7 ^ (m + 1)) := by
                linear_combination hδ
              rw [hsum, hq0, add_zero]
            rw [hq]
            rcases hqE with h | h | h <;> rw [h] <;> decide
          · have hq : qdig7 m
                ((eMod7 m (lam9 * (lam2 * b2)) (lam9 * (lam2 * b3))
                  + (lam2 * f) % 7 ^ (m + 1)) % 7 ^ (m + 1))
                = qdig7 m
                    (eMod7 m (lam9 * (lam2 * b2)) (lam9 * (lam2 * b3)))
                  + 1 := by
              have hsum : qdig7 m
                    ((eMod7 m (lam9 * (lam2 * b2)) (lam9 * (lam2 * b3))
                      + (lam2 * f) % 7 ^ (m + 1)) % 7 ^ (m + 1))
                    = qdig7 m
                        (eMod7 m (lam9 * (lam2 * b2)) (lam9 * (lam2 * b3)))
                      + qdig7 m ((lam2 * f) % 7 ^ (m + 1)) + 1 := by
                linear_combination hδ
              rw [hsum, hq0, add_zero]
            rw [hq]
            rcases hqE with h | h | h <;> rw [h] <;> decide
        · rw [htop, qdig7_congr (Nat.mod_mod _ _), qdig7_add_pow]
          simp only [Finset.mem_insert, Finset.mem_singleton] at hqE ⊢
          rcases hqE with h | h | h <;> rw [h] <;> decide
      -- `A₄` arc bound via `c65_pair_len3`
      have hreluv'' : residueRelOf (lam9 * (lam2 * u)) (lam9 * (lam2 * v))
          = residueRel.same := by
        apply rel_same
        · have e1 : runit7 (lam9 * (lam2 * u))
              = runit7 lam9 * (runit7 lam2 * runit7 u) := by
            rw [runit7_mul, runit7_mul]
          have e2 : runit7 (lam9 * (lam2 * v))
              = runit7 lam9 * (runit7 lam2 * runit7 v) := by
            rw [runit7_mul, runit7_mul]
          rw [e1, e2, hlam9r, one_mul, one_mul, hru, hrv]
        · rw [runit7_mul, runit7_mul, hlam9r, one_mul, hrv]
          exact mul_ne_zero hlam2r0 hs4_0
      have hap4 : apLen ((A4.image (fun d => lam * d)).image (qdig7 m))
          ≤ 3 := by
        have heq : (A4.image (fun d => lam * d)).image (qdig7 m)
            = ({lam9 * (lam2 * u), lam9 * (lam2 * v)} : Finset ℕ).image
              (qdig7 m) := by
          rw [hA4eq']
          simp only [Finset.image_insert, Finset.image_singleton]
          rw [show lam * u = lam9 * (lam2 * u) by
              rw [hlam]; exact mul_assoc _ _ _,
            show lam * v = lam9 * (lam2 * v) by
              rw [hlam]; exact mul_assoc _ _ _]
        rw [heq]
        exact c65_pair_len3 hreluv'' hqfin
      -- `A₁` arc bound from `hlen9`
      have hap1 : apLen ((A1.image (fun d => lam * d)).image (qdig7 m))
          ≤ 3 := by
        have hset : ({lam2 * b1, lam2 * b2, lam2 * b3} : Finset ℕ)
            = ({b1, b2, b3} : Finset ℕ).image (fun d => lam2 * d) := by
          rw [Finset.image_insert, Finset.image_insert,
            Finset.image_singleton]
        rw [hset, Finset.image_image] at hlen9
        have hcongr : ({b1, b2, b3} : Finset ℕ).image
              (qdig7 m ∘ fun d => lam * d)
            = ({b1, b2, b3} : Finset ℕ).image
              ((fun d => qdig7 m (lam9 * d)) ∘ (fun d => lam2 * d)) :=
          Finset.image_congr fun d _ => by
            show qdig7 m (lam * d) = qdig7 m (lam9 * (lam2 * d))
            rw [hlam]
            exact congrArg _ (mul_assoc _ _ _)
        rw [hA1eq', Finset.image_image, hcongr]
        exact hlen9
      exact c65_finish hm hpos hunit hs hcls1 hcls4 hlamnd
        (Or.inl ⟨hap1, hap4⟩)
    -- anchor dispatch on `w = r(e_{uv}) / r₁₃`
    have h7 : (7 : ZMod 7) = 0 := by decide
    simp only [Finset.mem_insert, Finset.mem_singleton] at hruv
    rcases hruv with hw | hw | hw
    · -- `w = 1`: anchor `e₁₃`, permutation `(d₂,d₁,d₃)`
      exact hcore (hA1eq.trans (Finset.insert_comm d1 d2 _))
        hp2 hp1 hp3 hu2 hu1 hu3 hr2 hr1 hr3 he23 he13
        rfl hνeq hrat hw
    · -- `w = 2`: anchor `e₃₂`, permutation `(d₁,d₃,d₂)`
      exact hcore (hA1eq.trans (by rw [Finset.pair_comm d2 d3]))
        hp1 hp3 hp2 hu1 hu3 hu2 hr1 hr3 hr2 he12 he32
        hν12 hν32
        (by rw [hr32, hr12]; linear_combination (-3 : ZMod 7) * hrat
            - runit7 (eMod7 m d2 d3) * h7)
        (by rw [hr32, hw]; linear_combination (2 : ZMod 7) * hrat
            + runit7 (eMod7 m d2 d3) * h7)
    · -- `w = 4`: anchor `e₂₁`, permutation `(d₃,d₂,d₁)`
      exact hcore (hA1eq.trans (by rw [Finset.insert_comm d1 d2,
          Finset.pair_comm d1 d3, Finset.insert_comm d2 d3]))
        hp3 hp2 hp1 hu3 hu2 hu1 hr3 hr2 hr1 he31 he21
        (hν31.trans hνeq) (hν21.trans hν12)
        (by rw [hr21, hr31, hr12];
            linear_combination (2 : ZMod 7) * hrat
              + runit7 (eMod7 m d2 d3) * h7)
        (by rw [hr21, hr12, hw];
            linear_combination (5 : ZMod 7) * hrat
              + (2 * runit7 (eMod7 m d2 d3)) * h7)
  -- orient `(u,v) ∈ {(d₄,d₅), (d₅,d₄)}` so the ratio lands in `{1,2,4}`
  have hr45ne : runit7 (eMod7 m d4 d5) ≠ 0 :=
    runit7_ne_zero (Nat.pos_of_ne_zero he45)
  have hmem : ∀ {x y : ℕ}, runit7 (eMod7 m x y) ≠ 0 →
      runit7 (eMod7 m x y) * (runit7 (eMod7 m d1 d3))⁻¹
        ∈ ({1, 2, 4} : Finset (ZMod 7)) →
      runit7 (eMod7 m x y)
        ∈ ({runit7 (eMod7 m d1 d3), 2 * runit7 (eMod7 m d1 d3),
            4 * runit7 (eMod7 m d1 d3)} : Finset (ZMod 7)) := by
    intro x y hxne hw
    have hmul : ∀ w : ZMod 7,
        runit7 (eMod7 m x y) * (runit7 (eMod7 m d1 d3))⁻¹ = w →
        runit7 (eMod7 m x y) = w * runit7 (eMod7 m d1 d3) := by
      intro w hw'
      calc runit7 (eMod7 m x y)
          = runit7 (eMod7 m x y) * (runit7 (eMod7 m d1 d3))⁻¹
              * runit7 (eMod7 m d1 d3) := by
            rw [mul_assoc, inv_mul_cancel₀ hr13ne, mul_one]
        _ = w * runit7 (eMod7 m d1 d3) := by rw [hw']
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw ⊢
    rcases hw with hw | hw | hw
    · exact Or.inl (by rw [hmul 1 hw, one_mul])
    · exact Or.inr (Or.inl (hmul 2 hw))
    · exact Or.inr (Or.inr (hmul 4 hw))
  by_cases hw124 : runit7 (eMod7 m d4 d5) * (runit7 (eMod7 m d1 d3))⁻¹
      ∈ ({1, 2, 4} : Finset (ZMod 7))
  · exact hmain d4 d5 hA4eq hp4 hp5 hu4 hu5 hr4 hr5 he45 h45eq
      (hmem hr45ne hw124)
  · have hw54 : runit7 (eMod7 m d5 d4) * (runit7 (eMod7 m d1 d3))⁻¹
        ∈ ({1, 2, 4} : Finset (ZMod 7)) := by
      rw [hr54]
      have hneg : ∀ w : ZMod 7, w ≠ 0 →
          w ∉ ({1, 2, 4} : Finset (ZMod 7)) →
          -w ∈ ({1, 2, 4} : Finset (ZMod 7)) := by decide
      have hwne : runit7 (eMod7 m d4 d5) * (runit7 (eMod7 m d1 d3))⁻¹
          ≠ 0 := mul_ne_zero hr45ne (inv_ne_zero hr13ne)
      have : - runit7 (eMod7 m d4 d5) * (runit7 (eMod7 m d1 d3))⁻¹
          = - (runit7 (eMod7 m d4 d5) * (runit7 (eMod7 m d1 d3))⁻¹) := by
        ring
      rw [this]
      exact hneg _ hwne hw124
    have hr54ne : runit7 (eMod7 m d5 d4) ≠ 0 :=
      runit7_ne_zero (Nat.pos_of_ne_zero he54)
    exact hmain d5 d4 (hA4eq.trans (Finset.pair_comm d4 d5))
      hp5 hp4 hu5 hu4 hr5 hr4 he54 (hν54.trans h45eq)
      (hmem hr54ne hw54)

set_option synthInstance.maxSize 16384 in
set_option maxRecDepth 524288 in
set_option maxHeartbeats 3000000 in
/-- §6.5 (ii.2) low subcase `ν(e₄₅) > h`: fix `q(e₄₅') ∈ {0,6}` first
(`Λ_{ν₄₅}` or a top scalar `t = 6`), then `c65_l9ii3` on the scaled
triple; the returned `Λ_h` preserves `e₄₅'` verbatim
(`residN_multLow7`, `ν(e₄₅') = ν₄₅ > h`). -/
private theorem c65_ii2_low_gt {m : ℕ} (hm : 0 < m) {A1 A4 : Finset ℕ}
    (hpos : ∀ d ∈ A1 ∪ A4, 0 < d)
    (hunit : ∀ d ∈ A1 ∪ A4, padicValNat 7 d = 0)
    {s : ZMod 7} (hs : s ≠ 0)
    (hcls1 : ∀ d ∈ A1, runit7 d = s)
    (hcls4 : ∀ d ∈ A4, runit7 d = 4 * s)
    {d1 d2 d3 d4 d5 : ℕ}
    (hA1eq : A1 = {d1, d2, d3}) (hA4eq : A4 = {d4, d5})
    (hp1 : 0 < d1) (hp2 : 0 < d2) (hp3 : 0 < d3)
    (hp4 : 0 < d4) (hp5 : 0 < d5)
    (hu1 : padicValNat 7 d1 = 0) (hu2 : padicValNat 7 d2 = 0)
    (hu3 : padicValNat 7 d3 = 0) (hu4 : padicValNat 7 d4 = 0)
    (hu5 : padicValNat 7 d5 = 0)
    (hr1 : runit7 d1 = s) (hr2 : runit7 d2 = s) (hr3 : runit7 d3 = s)
    (hr4 : runit7 d4 = 4 * s) (hr5 : runit7 d5 = 4 * s)
    (hs4_0 : (4 : ZMod 7) * s ≠ 0)
    (hνeq : padicValNat 7 (eMod7 m d1 d3)
      = padicValNat 7 (eMod7 m d2 d3))
    (hrat : runit7 (eMod7 m d1 d3) = 3 * runit7 (eMod7 m d2 d3))
    (hlm : padicValNat 7 (eMod7 m d2 d3) < m)
    (he13 : eMod7 m d1 d3 ≠ 0) (he23 : eMod7 m d2 d3 ≠ 0)
    (he45 : eMod7 m d4 d5 ≠ 0)
    (h45gt : padicValNat 7 (eMod7 m d2 d3)
      < padicValNat 7 (eMod7 m d4 d5)) :
    ∃ lam : ℕ, ¬ 7 ∣ lam ∧ good7 m lam (A1 ∪ A4) := by
  classical
  have hν45le : padicValNat 7 (eMod7 m d4 d5) ≤ m := enu7_le_of_ne he45
  -- top scalar `t = 6`), then `c65_l9ii3` on the scaled triple; the
  -- returned `Λ_h` preserves `e₄₅'` verbatim (`residN_multLow7`,
  -- `ν(e₄₅') = ν₄₅ > h`).
  set e45 := eMod7 m d4 d5 with he45d
  obtain ⟨lam2, hlam2pos, hlam2nd, hlam2r0, he45'eq, hν45', hq45'⟩ :
      ∃ lam2 : ℕ, 0 < lam2 ∧ ¬ 7 ∣ lam2 ∧ runit7 lam2 ≠ 0 ∧
        eMod7 m (lam2 * d4) (lam2 * d5) = (lam2 * e45) % 7 ^ (m + 1) ∧
        padicValNat 7 (eMod7 m (lam2 * d4) (lam2 * d5))
          = padicValNat 7 e45 ∧
        qdig7 m (eMod7 m (lam2 * d4) (lam2 * d5))
          ∈ ({0, 6} : Finset (ZMod 7)) := by
    rcases lt_or_eq_of_le hν45le with hlt | heqν
    · obtain ⟨k2, hk2lt, hk2q⟩ := exists_multLow_set_qdig
        (j := padicValNat 7 e45) (x := e45) hlt rfl he45 (0 : ZMod 7)
      set lam2 := 1 + k2 * 7 ^ (m - padicValNat 7 e45) with hlam2
      have hlam2r : runit7 lam2 = 1 := by
        rw [hlam2]; exact runit7_multLow hlt
      have hlam2pos : 0 < lam2 := by
        rw [hlam2]; exact Nat.add_pos_left Nat.one_pos _
      refine ⟨lam2, hlam2pos,
        by rw [hlam2]; exact multLow_not_dvd hlt,
        by rw [hlam2r]; exact one_ne_zero, eMod7_mul hlam2r, ?_, ?_⟩
      · have hmod : (lam2 * e45) % 7 ^ (m + 1)
            = ((lam2 * e45) % 7 ^ (m + 1)) % 7 ^ (m + 1) :=
          (Nat.mod_mod _ _).symm
        have hνl : padicValNat 7 (lam2 * e45) = padicValNat 7 e45 :=
          padicValNat_mul_seven
            (by rw [hlam2]; exact multLow_not_dvd hlt) he45
        rw [eMod7_mul hlam2r]
        exact (padicValNat_eq_of_mod hmod (by rw [hνl]; exact hν45le)
          (mul_ne_zero (ne_of_gt hlam2pos) he45)).symm.trans hνl
      · rw [eMod7_mul hlam2r, qdig7_congr (Nat.mod_mod _ _), hk2q]
        decide
    · obtain ⟨c, hcpos, hc7', hcmod, hqc⟩ :=
        exists_top_scalar_set heqν he45 (t := 6) (by decide)
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
  -- level bookkeeping for the `λ₂`-rescaled `A₁` differences
  have he13'e : eMod7 m (lam2 * d1) (lam2 * d3)
      = (lam2 * eMod7 m d1 d3) % 7 ^ (m + 1) := eMod7_smul hlam2r0
  have he23'e : eMod7 m (lam2 * d2) (lam2 * d3)
      = (lam2 * eMod7 m d2 d3) % 7 ^ (m + 1) := eMod7_smul hlam2r0
  have hνmod : ∀ x : ℕ, x ≠ 0 → padicValNat 7 x ≤ m →
      padicValNat 7 ((lam2 * x) % 7 ^ (m + 1)) = padicValNat 7 x := by
    intro x hx0 hxm
    have hνl : padicValNat 7 (lam2 * x) = padicValNat 7 x :=
      padicValNat_mul_seven hlam2nd hx0
    have hmod : (lam2 * x) % 7 ^ (m + 1)
        = ((lam2 * x) % 7 ^ (m + 1)) % 7 ^ (m + 1) :=
      (Nat.mod_mod _ _).symm
    exact (padicValNat_eq_of_mod hmod (by rw [hνl]; exact hxm)
      (mul_ne_zero (ne_of_gt hlam2pos) hx0)).symm.trans hνl
  have hrmod : ∀ x : ℕ, x ≠ 0 → padicValNat 7 x ≤ m →
      runit7 ((lam2 * x) % 7 ^ (m + 1)) = runit7 lam2 * runit7 x := by
    intro x hx0 hxm
    have hνl : padicValNat 7 (lam2 * x) = padicValNat 7 x :=
      padicValNat_mul_seven hlam2nd hx0
    have hmod : (lam2 * x) % 7 ^ (m + 1)
        = ((lam2 * x) % 7 ^ (m + 1)) % 7 ^ (m + 1) :=
      (Nat.mod_mod _ _).symm
    rw [← runit7_eq_of_mod hmod (by rw [hνl]; exact hxm)
      (mul_ne_zero (ne_of_gt hlam2pos) hx0), runit7_mul]
  have hν13' : padicValNat 7 (eMod7 m (lam2 * d1) (lam2 * d3))
      = padicValNat 7 (eMod7 m d2 d3) := by
    rw [he13'e,
      hνmod _ he13 (by rw [hνeq]; exact le_of_lt hlm), hνeq]
  have hν23' : padicValNat 7 (eMod7 m (lam2 * d2) (lam2 * d3))
      = padicValNat 7 (eMod7 m d2 d3) := by
    rw [he23'e, hνmod _ he23 (le_of_lt hlm)]
  have hr13' : runit7 (eMod7 m (lam2 * d1) (lam2 * d3))
      = runit7 lam2 * runit7 (eMod7 m d1 d3) := by
    rw [he13'e, hrmod _ he13 (by rw [hνeq]; exact le_of_lt hlm)]
  have hr23' : runit7 (eMod7 m (lam2 * d2) (lam2 * d3))
      = runit7 lam2 * runit7 (eMod7 m d2 d3) := by
    rw [he23'e, hrmod _ he23 (le_of_lt hlm)]
  -- `c65_l9ii3` on `b₁ = lam2·d₂, b₂ = lam2·d₁, b₃ = lam2·d₃`
  obtain ⟨lam9, ⟨k9, hk9lt, hlam9eq⟩, hlam9nd, _hqe, _hpairs, hlen9⟩ :=
    c65_l9ii3
      ⟨Nat.mul_pos hlam2pos hp2, Nat.mul_pos hlam2pos hp1,
        Nat.mul_pos hlam2pos hp3⟩
      ⟨by rw [padicValNat_mul_seven hlam2nd (ne_of_gt hp2), hu2],
        by rw [padicValNat_mul_seven hlam2nd (ne_of_gt hp1), hu1],
        by rw [padicValNat_mul_seven hlam2nd (ne_of_gt hp3), hu3]⟩
      ⟨by rw [runit7_mul, runit7_mul, hr2, hr1],
        by rw [runit7_mul, runit7_mul, hr1, hr3]⟩
      (by rw [hν23', hν13']) (by rw [hν13']; exact hlm)
      (by rw [hr13', hr23', hrat]; ring)
  -- `lam9 = 1 + k9·7^{m−h}` preserves `e45'`
  have hlam9r : runit7 lam9 = 1 := by
    rw [hlam9eq]
    exact runit7_multLow (by rw [hν13']; exact hlm)
  set lam := lam9 * lam2 with hlam
  have hlamnd : ¬ 7 ∣ lam :=
    Nat.prime_seven.not_dvd_mul hlam9nd hlam2nd
  have hfix : eMod7 m (lam9 * (lam2 * d4)) (lam9 * (lam2 * d5))
      = eMod7 m (lam2 * d4) (lam2 * d5) := by
    rw [eMod7_mul hlam9r]
    have h1 : (lam9 * eMod7 m (lam2 * d4) (lam2 * d5)) % 7 ^ (m + 1)
        = eMod7 m (lam2 * d4) (lam2 * d5) % 7 ^ (m + 1) := by
      rw [hlam9eq]
      exact residN_multLow7 (by rw [hν13']; exact hlm)
        (by rw [hν45', hν13']; exact h45gt)
    rw [h1, Nat.mod_eq_of_lt (eMod7_lt _ _ _)]
  have hrel45lam : residueRelOf (lam * d4) (lam * d5)
      = residueRel.same := by
    rw [hlam,
      show lam9 * lam2 * d4 = lam9 * (lam2 * d4) from mul_assoc _ _ _,
      show lam9 * lam2 * d5 = lam9 * (lam2 * d5) from mul_assoc _ _ _]
    apply rel_same
    · have e1 : runit7 (lam9 * (lam2 * d4))
          = runit7 lam9 * (runit7 lam2 * runit7 d4) := by
        rw [runit7_mul, runit7_mul]
      have e2 : runit7 (lam9 * (lam2 * d5))
          = runit7 lam9 * (runit7 lam2 * runit7 d5) := by
        rw [runit7_mul, runit7_mul]
      rw [e1, e2, hlam9r, one_mul, one_mul, hr4, hr5]
    · rw [runit7_mul, runit7_mul, hlam9r, one_mul, hr5]
      exact mul_ne_zero hlam2r0 hs4_0
  have hfin : qdig7 m (eMod7 m (lam * d4) (lam * d5))
      ∈ ({0, 6} : Finset (ZMod 7)) := by
    have h1 : eMod7 m (lam * d4) (lam * d5)
        = eMod7 m (lam2 * d4) (lam2 * d5) := by
      rw [hlam,
        show lam9 * lam2 * d4 = lam9 * (lam2 * d4) from mul_assoc _ _ _,
        show lam9 * lam2 * d5 = lam9 * (lam2 * d5) from mul_assoc _ _ _]
      exact hfix
    rw [h1]; exact hq45'
  have hap4 : apLen ((A4.image (fun d => lam * d)).image (qdig7 m))
      ≤ 2 := by
    have heq : (A4.image (fun d => lam * d)).image (qdig7 m)
        = ({lam * d4, lam * d5} : Finset ℕ).image (qdig7 m) := by
      rw [hA4eq]; simp only [Finset.image_insert, Finset.image_singleton]
    rw [heq]
    exact c65_pair_len2 hrel45lam hfin
  -- `A₁` arc bound transported through the `lam2`-image
  have hap1 : apLen ((A1.image (fun d => lam * d)).image (qdig7 m))
      ≤ 3 := by
    have hset : ({lam2 * d2, lam2 * d1, lam2 * d3} : Finset ℕ)
        = ({d1, d2, d3} : Finset ℕ).image (fun d => lam2 * d) := by
      rw [Finset.image_insert, Finset.image_insert, Finset.image_singleton,
        Finset.insert_comm (lam2 * d2) (lam2 * d1)]
    rw [hset, Finset.image_image] at hlen9
    have hcongr : ({d1, d2, d3} : Finset ℕ).image
          (qdig7 m ∘ fun d => lam * d)
        = ({d1, d2, d3} : Finset ℕ).image
          ((fun d => qdig7 m (lam9 * d)) ∘ (fun d => lam2 * d)) :=
      Finset.image_congr fun d _ => by
        show qdig7 m (lam * d) = qdig7 m (lam9 * (lam2 * d))
        rw [hlam]
        exact congrArg _ (mul_assoc _ _ _)
    rw [hA1eq, Finset.image_image, hcongr]
    exact hlen9
  exact c65_finish hm hpos hunit hs hcls1 hcls4 hlamnd
    (Or.inr (Or.inr (by omega)))

set_option synthInstance.maxSize 16384 in
set_option maxRecDepth 524288 in
set_option maxHeartbeats 3000000 in
/-- Case (ii.2) with `h < m`: dispatch on `ν(e₄₅)` relative to `h` —
`c65_ii2_low_zero` / `c65_ii2_low_lt` / `c65_ii2_low_eq` /
`c65_ii2_low_gt`. -/
private theorem c65_case_ii2_low {m : ℕ} (hm : 0 < m) {A1 A4 : Finset ℕ}
    (hpos : ∀ d ∈ A1 ∪ A4, 0 < d)
    (hunit : ∀ d ∈ A1 ∪ A4, padicValNat 7 d = 0)
    {s : ZMod 7} (hs : s ≠ 0)
    (hcls1 : ∀ d ∈ A1, runit7 d = s)
    (hcls4 : ∀ d ∈ A4, runit7 d = 4 * s)
    {d1 d2 d3 : ℕ} (hA1eq : A1 = {d1, d2, d3})
    {d4 d5 : ℕ} (hA4eq : A4 = {d4, d5})
    (he13 : eMod7 m d1 d3 ≠ 0) (he23 : eMod7 m d2 d3 ≠ 0)
    (hlevel : elevel7 m d1 d3 = elevel7 m d2 d3)
    (hrat : runit7 (eMod7 m d1 d3) = 3 * runit7 (eMod7 m d2 d3))
    (hlm : padicValNat 7 (eMod7 m d2 d3) < m) :
    ∃ lam : ℕ, ¬ 7 ∣ lam ∧ good7 m lam (A1 ∪ A4) := by
  classical
  have hd1mem : d1 ∈ A1 := by rw [hA1eq]; exact Finset.mem_insert_self _ _
  have hd2mem : d2 ∈ A1 := by
    rw [hA1eq]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hd3mem : d3 ∈ A1 := by
    rw [hA1eq]; exact Finset.mem_insert_of_mem
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have hd4mem : d4 ∈ A4 := by rw [hA4eq]; exact Finset.mem_insert_self _ _
  have hd5mem : d5 ∈ A4 := by
    rw [hA4eq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hp1 : 0 < d1 := hpos d1 (Finset.mem_union_left _ hd1mem)
  have hp2 : 0 < d2 := hpos d2 (Finset.mem_union_left _ hd2mem)
  have hp3 : 0 < d3 := hpos d3 (Finset.mem_union_left _ hd3mem)
  have hp4 : 0 < d4 := hpos d4 (Finset.mem_union_right _ hd4mem)
  have hp5 : 0 < d5 := hpos d5 (Finset.mem_union_right _ hd5mem)
  have hu1 : padicValNat 7 d1 = 0 := hunit d1 (Finset.mem_union_left _ hd1mem)
  have hu2 : padicValNat 7 d2 = 0 := hunit d2 (Finset.mem_union_left _ hd2mem)
  have hu3 : padicValNat 7 d3 = 0 := hunit d3 (Finset.mem_union_left _ hd3mem)
  have hu4 : padicValNat 7 d4 = 0 := hunit d4 (Finset.mem_union_right _ hd4mem)
  have hu5 : padicValNat 7 d5 = 0 := hunit d5 (Finset.mem_union_right _ hd5mem)
  have hr1 : runit7 d1 = s := hcls1 d1 hd1mem
  have hr2 : runit7 d2 = s := hcls1 d2 hd2mem
  have hr3 : runit7 d3 = s := hcls1 d3 hd3mem
  have hr4 : runit7 d4 = 4 * s := hcls4 d4 hd4mem
  have hr5 : runit7 d5 = 4 * s := hcls4 d5 hd5mem
  have hs4_0 : (4 : ZMod 7) * s ≠ 0 := mul_ne_zero (by decide) hs
  have hν13 : padicValNat 7 (eMod7 m d1 d3) = elevel7 m d1 d3 :=
    (elevel7_of_ne he13).symm
  have hν23 : padicValNat 7 (eMod7 m d2 d3) = elevel7 m d2 d3 :=
    (elevel7_of_ne he23).symm
  have hνeq : padicValNat 7 (eMod7 m d1 d3)
      = padicValNat 7 (eMod7 m d2 d3) := by rw [hν13, hν23, hlevel]
  -- same-class relations on all pairs
  have hrel13 : residueRelOf d1 d3 = residueRel.same :=
    rel_same (by rw [hr1, hr3]) (by rw [hr3]; exact hs)
  have hrel23 : residueRelOf d2 d3 = residueRel.same :=
    rel_same (by rw [hr2, hr3]) (by rw [hr3]; exact hs)
  have hrel12 : residueRelOf d1 d2 = residueRel.same :=
    rel_same (by rw [hr1, hr2]) (by rw [hr2]; exact hs)
  have hrel31 : residueRelOf d3 d1 = residueRel.same :=
    rel_same (by rw [hr3, hr1]) (by rw [hr1]; exact hs)
  have hrel32 : residueRelOf d3 d2 = residueRel.same :=
    rel_same (by rw [hr3, hr2]) (by rw [hr2]; exact hs)
  have hrel21 : residueRelOf d2 d1 = residueRel.same :=
    rel_same (by rw [hr2, hr1]) (by rw [hr1]; exact hs)
  have hrel45 : residueRelOf d4 d5 = residueRel.same :=
    rel_same (by rw [hr4, hr5]) (by rw [hr5]; exact hs4_0)
  have hrel54 : residueRelOf d5 d4 = residueRel.same :=
    rel_same (by rw [hr5, hr4]) (by rw [hr4]; exact hs4_0)
  -- the third `A₁` pair also sits at level `h` with unit `r₁₃ − r₂₃`
  have hr23ne : runit7 (eMod7 m d2 d3) ≠ 0 :=
    runit7_ne_zero (Nat.pos_of_ne_zero he23)
  have hr13ne : runit7 (eMod7 m d1 d3) ≠ 0 :=
    runit7_ne_zero (Nat.pos_of_ne_zero he13)
  have hrne : runit7 (eMod7 m d1 d3) ≠ runit7 (eMod7 m d2 d3) := by
    intro hcon
    rw [hrat] at hcon
    have hz : (2 : ZMod 7) * runit7 (eMod7 m d2 d3) = 0 := by
      linear_combination hcon
    rcases mul_eq_zero.mp hz with h2 | h0
    · exact absurd h2 (by decide)
    · exact hr23ne h0
  obtain ⟨he12, hν12, hr12⟩ := eMod7_level_of_runit_ne
    hrel13 hrel23 hrel12 he13 he23 hνeq rfl (le_of_lt hlm) hrne
  -- negated-pair data
  obtain ⟨hν32, hr32⟩ := enu7_neg (m := m) hrel23 hrel32
  obtain ⟨hν31, hr31⟩ := enu7_neg (m := m) hrel13 hrel31
  obtain ⟨hν21, hr21⟩ := enu7_neg (m := m) hrel12 hrel21
  have ene_symm : ∀ {x y : ℕ}, residueRelOf x y = residueRel.same →
      residueRelOf y x = residueRel.same →
      eMod7 m x y ≠ 0 → eMod7 m y x ≠ 0 := by
    intro x y hxy hyx hne hcon
    rw [eMod7_neg_eq hxy hyx] at hcon
    have hlt := eMod7_lt m x y
    have hlt2 : 7 ^ (m + 1) - eMod7 m x y < 7 ^ (m + 1) := by
      have hpos : 0 < eMod7 m x y := Nat.pos_of_ne_zero hne
      omega
    rw [Nat.mod_eq_of_lt hlt2] at hcon
    have hpos2 : 0 < 7 ^ (m + 1) - eMod7 m x y := by omega
    exact absurd hcon (ne_of_gt hpos2)
  have he32 : eMod7 m d3 d2 ≠ 0 := ene_symm hrel23 hrel32 he23
  have he31 : eMod7 m d3 d1 ≠ 0 := ene_symm hrel13 hrel31 he13
  have he21 : eMod7 m d2 d1 ≠ 0 := ene_symm hrel12 hrel21 he12
  have hset_eq : ({d2, d1, d3} : Finset ℕ) = {d1, d2, d3} :=
    Finset.insert_comm d2 d1 _
  by_cases he45 : eMod7 m d4 d5 = 0
  · exact c65_ii2_low_zero hm hpos hunit hs hcls1 hcls4 hA1eq hA4eq
      hp1 hp2 hp3 hp4 hp5 hu1 hu2 hu3 hu4 hu5 hr1 hr2 hr3 hr4 hr5 hs4_0
      hνeq hrat hlm he45
  · have he54 : eMod7 m d5 d4 ≠ 0 := ene_symm hrel45 hrel54 he45
    rcases lt_trichotomy (padicValNat 7 (eMod7 m d4 d5))
        (padicValNat 7 (eMod7 m d2 d3)) with h45lt | h45eq | h45gt
    · exact c65_ii2_low_lt hm hpos hunit hs hcls1 hcls4 hA1eq hA4eq
        hp1 hp2 hp3 hp4 hp5 hu1 hu2 hu3 hu4 hu5 hr1 hr2 hr3 hr4 hr5 hs4_0
        hνeq hrat hlm he45 h45lt hν12 hν21 hν31 hν32
    · exact c65_ii2_low_eq hm hpos hunit hs hcls1 hcls4 hA1eq hA4eq
        hp1 hp2 hp3 hp4 hp5 hu1 hu2 hu3 hu4 hu5 hr1 hr2 hr3 hr4 hr5 hs4_0
        hνeq hrat hlm he13 he23 he12 he21 he31 he32 he45 he54 hrel45 hrel54
        h45eq hν12 hν21 hν31 hν32 hr12 hr21 hr31 hr32
    · exact c65_ii2_low_gt hm hpos hunit hs hcls1 hcls4 hA1eq hA4eq
        hp1 hp2 hp3 hp4 hp5 hu1 hu2 hu3 hu4 hu5 hr1 hr2 hr3 hr4 hr5 hs4_0
        hνeq hrat hlm he13 he23 he45 h45gt

/-- **Theorem (paper §6.5).**  For `|A₁| = 3` in unit class `s` and
`|A₄| = 2` in unit class `4s` (`s ∈ {1,2,4}`), there is a multiplier
coprime to `7` making `A₁ ∪ A₄` `good7`.  Assembly mirrors `case63`:
`lemma11` on `A₁`, then dispatch to `c65_case_i` / `c65_case_ii1_*` /
`c65_case_ii2_*` (with the zero-difference degenerations handled by
`c65_case_collision`). -/
theorem case65 {m : ℕ} (hm : 1 < m) {A1 A4 : Finset ℕ}
    (hA1 : A1.card = 3) (hA4 : A4.card = 2)
    (hpos : ∀ d ∈ A1 ∪ A4, 0 < d)
    (hunit : ∀ d ∈ A1 ∪ A4, padicValNat 7 d = 0)
    {s : ZMod 7} (hs : s ∈ ({1, 2, 4} : Finset (ZMod 7)))
    (hcls1 : ∀ d ∈ A1, runit7 d = s)
    (hcls4 : ∀ d ∈ A4, runit7 d = 4 * s) :
    ∃ lam : ℕ, ¬ 7 ∣ lam ∧ good7 m lam (A1 ∪ A4) := by
  have hm2 : 2 ≤ m := by omega
  have hs0 : s ≠ 0 := by
    intro h0
    rw [h0] at hs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with h | h | h <;> exact absurd h (by decide)
  have hpos1 : ∀ d ∈ A1, 0 < d := fun d hd =>
    hpos d (Finset.mem_union_left _ hd)
  have hunit1 : ∀ d ∈ A1, padicValNat 7 d = 0 := fun d hd =>
    hunit d (Finset.mem_union_left _ hd)
  obtain ⟨d1, _hd1, d2, _hd2, d3, _hd3, hA1eq, hdisj⟩ :=
    lemma11 hA1 s hpos1 hunit1 hcls1
  obtain ⟨d4, d5, _hd45, hA4eq⟩ := Finset.card_eq_two.mp hA4
  rcases hdisj with ⟨hlgt, _⟩ | ⟨heq, hratios⟩
  · -- Case (i): `l(e₁₃) > l(e₂₃) = l(e₁₂)`
    exact c65_case_i (by omega) hpos hunit hs0 hcls1 hcls4 hA1eq hA4eq hlgt
  · -- Case (ii): equal levels, ratio `2` or `3`
    by_cases he23_zero : eMod7 m d2 d3 = 0
    · have he13_zero : eMod7 m d1 d3 = 0 := by
        by_contra he13n
        have h1 : elevel7 m d2 d3 = m + 1 := elevel7_of_eq he23_zero
        rw [h1] at heq
        have h2 : elevel7 m d1 d3
            = padicValNat 7 (eMod7 m d1 d3) := elevel7_of_ne he13n
        have h3 : padicValNat 7 (eMod7 m d1 d3) ≤ m := enu7_le_of_ne he13n
        omega
      exact c65_case_collision (by omega) hpos hunit hs0 hcls1 hcls4
        hA1eq hA4eq he13_zero he23_zero
    · have he13_ne : eMod7 m d1 d3 ≠ 0 := by
        intro h0
        have h1 : elevel7 m d1 d3 = m + 1 := elevel7_of_eq h0
        rw [h1] at heq
        have h2 : elevel7 m d2 d3
            = padicValNat 7 (eMod7 m d2 d3) := elevel7_of_ne he23_zero
        have h3 : padicValNat 7 (eMod7 m d2 d3) ≤ m := enu7_le_of_ne he23_zero
        omega
      have hν23le : padicValNat 7 (eMod7 m d2 d3) ≤ m :=
        enu7_le_of_ne he23_zero
      rcases eq_or_lt_of_le hν23le with htop | hlow
      · -- `h = m` (top level)
        have hν13m : padicValNat 7 (eMod7 m d1 d3) = m := by
          have hν13 := (elevel7_of_ne he13_ne).symm
          have hν23 := (elevel7_of_ne he23_zero).symm
          omega
        rcases hratios with hrat2 | ⟨hrat3, _⟩
        · exact c65_case_ii1_top hm2 hpos hunit hs0 hcls1 hcls4 hA1eq hA4eq
            he13_ne he23_zero htop hν13m hrat2
        · exact c65_case_ii2_top (by omega) hpos hunit hs0 hcls1 hcls4
            hA1eq hA4eq he13_ne he23_zero htop hν13m hrat3
      · -- `h < m` (low level)
        rcases hratios with hrat2 | ⟨hrat3, _⟩
        · exact c65_case_ii1_low (by omega) hpos hunit hs0 hcls1 hcls4
            hA1eq hA4eq he13_ne he23_zero heq hrat2 hlow
        · exact c65_case_ii2_low (by omega) hpos hunit hs0 hcls1 hcls4
            hA1eq hA4eq he13_ne he23_zero heq hrat3 hlow
