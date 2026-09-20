/-
Copyright (c) 2026 Research07 contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Research07 contributors
-/
import Research07.LRC7.Case5mBase
import Research07.LRC7.Carry

/-!
# Case lemmas for the `|A| = 5, m ≥ 2` analysis (Barajas–Serra §6)

This file is the "B1/B2" shared-lemma layer of the §6 formalization (see
`_reports/lrc7-sec6-spec.md` §8): paper Lemmas 7, 9, 10, 11, consumed by the
case theorems `case61`–`case66`.

Contents so far (B1 — paper Lemma 7, `ẽ`-avoidance for `twoX` pairs):

* Residue helpers: `runit7_two`, `eMod7_two_mul_left` (the `(2x, y)` pair
  is same-class with the same `2x−y` residue when `r(y) = 2r(x)`),
  `qdig7_eq_runit7_of_top` (`ν(x) = m ⇒ q(x) = r(x)`), plus a private
  `ZMod`-cast copy of `eMod7`'s branch formula.
* `lemma7_i` — `ν(e) < m`: a `Λ_h`-shift (`h = ν(e)`) puts `ẽ(λd,λd')`
  off any `apLen ≤ 4` set `X`.
* `lemma7_ii` — `ν(e) = m`: `λ ∈ Λ₁` with `q(λ·7d) = 6` forces
  `q(2λd) = 2q(λd)+1`, giving `ẽ(λd,λd') ∈ {r(e)−1, r(e)}`.
-/

/-- `runit7 2 = 2`. -/
theorem runit7_two : runit7 2 = 2 := by
  unfold runit7
  rw [padicValNat.eq_zero_of_not_dvd (by decide : ¬ 7 ∣ 2), pow_zero,
    Nat.div_one]
  decide

/-- `ZMod`-cast of `eMod7`: the wrapped residue casts to the corresponding
`ZMod (7^{m+1})` branch expression.  (Local copy — the same helper is
`private` in `Case5mBase.lean`.) -/
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

/-- For a `twoX` pair `(x, y)` (`r(y) = 2r(x)`), the pair `(2x, y)` is
same-class and its (same-branch) difference residue equals `e(x,y)` —
both are `2x − y (mod N)`. -/
theorem eMod7_two_mul_left {m x y : ℕ}
    (hrel : runit7 y = 2 * runit7 x) (hx : 0 < x) :
    eMod7 m (2 * x) y = eMod7 m x y := by
  have hrx : runit7 x ≠ 0 := runit7_ne_zero hx
  have hr2x : runit7 (2 * x) = 2 * runit7 x := by
    rw [runit7_mul, runit7_two]
  have hsame : residueRelOf (2 * x) y = residueRel.same := by
    rw [residueRelOf_eq_same]
    refine ⟨?_, ?_⟩ <;> rw [hr2x, hrel] <;> intro hcon <;>
      · have h0 : (2 : ZMod 7) * runit7 x = 0 := by
          have hsub : 2 * (2 * runit7 x) - 2 * runit7 x
              = (2 : ZMod 7) * runit7 x := by ring
          rw [← hcon, sub_self] at hsub
          exact hsub.symm
        rcases mul_eq_zero.mp h0 with h2 | h
        · exact absurd h2 (by decide)
        · exact hrx h
  obtain ⟨hif1, hif2⟩ := (residueRelOf_eq_same).mp hsame
  have hcast : ((eMod7 m (2 * x) y : ℕ) : ZMod (7 ^ (m + 1))) =
      ((eMod7 m x y : ℕ) : ZMod _) := by
    rw [eMod7_zmod_cast, eMod7_zmod_cast, if_neg hif1, if_neg hif2,
      if_pos hrel]
    push_cast
    ring
  rw [ZMod.natCast_eq_natCast_iff] at hcast
  have hlt1 : eMod7 m (2 * x) y < 7 ^ (m + 1) := by
    unfold eMod7
    split_ifs <;> exact Nat.mod_lt _ (Nat.pow_pos (by norm_num))
  have hlt2 : eMod7 m x y < 7 ^ (m + 1) := by
    unfold eMod7
    split_ifs <;> exact Nat.mod_lt _ (Nat.pow_pos (by norm_num))
  have hcast' : eMod7 m (2 * x) y % 7 ^ (m + 1) = eMod7 m x y % 7 ^ (m + 1) :=
    hcast
  rwa [Nat.mod_eq_of_lt hlt1, Nat.mod_eq_of_lt hlt2] at hcast'

/-- For `ν(x) = m` the leading digit equals the unit part: `q(x) = r(x)`
(the residue is `q·7^m` verbatim, so `x/7^m ≡ q (mod 7)`). -/
theorem qdig7_eq_runit7_of_top {m x : ℕ} (hx : padicValNat 7 x = m) :
    qdig7 m x = runit7 x := by
  have hdiv : x / 7 ^ m = (x % 7 ^ (m + 1)) / 7 ^ m + 7 * (x / 7 ^ (m + 1)) := by
    have hN : (7:ℕ) ^ (m + 1) = 7 * 7 ^ m := pow_succ' 7 m
    have hdecomp : x = x % 7 ^ (m + 1) + 7 ^ m * (7 * (x / 7 ^ (m + 1))) := by
      conv_lhs => rw [← Nat.div_add_mod x (7 ^ (m + 1))]
      rw [hN]
      ring
    have h7m : (0:ℕ) < 7 ^ m := Nat.pow_pos (by norm_num)
    conv_lhs => rw [hdecomp]
    rw [Nat.add_mul_div_left _ _ h7m]
  unfold runit7
  rw [hx, hdiv]
  unfold qdig7
  rw [Nat.cast_add]
  have h7 : ((7 * (x / 7 ^ (m + 1)) : ℕ) : ZMod 7) = 0 := by
    rw [Nat.cast_mul, show ((7 : ℕ) : ZMod 7) = 0 from ZMod.natCast_self 7,
      zero_mul]
  rw [h7, add_zero]

/-! ### Paper Lemma 7 — `ẽ`-avoidance for `twoX` pairs -/

/-- **Lemma 7(i)**: for a `twoX` pair `(d, d')` whose difference residue
`e = 2d − d'` has level `0 < ν(e) < m`, a `Λ_{ν(e)}`-element sets `q(λe)`
so that `ẽ(λd,λd') ∈ q(λe) + {0,1,6}` avoids any `X` with `apLen X ≤ 4`. -/
theorem lemma7_i {m : ℕ} {d d' : ℕ}
    (hd : padicValNat 7 d = 0) (hd' : padicValNat 7 d' = 0)
    (hpos : 0 < d) (hpos' : 0 < d')
    (hrel : runit7 d' = 2 * runit7 d)
    (hν : 0 < padicValNat 7 (eMod7 m d d'))
    (hνm : padicValNat 7 (eMod7 m d d') < m)
    {X : Finset (ZMod 7)} (hX : apLen X ≤ 4) :
    ∃ lam : ℕ, ¬ 7 ∣ lam ∧ etd7 m (lam * d) (lam * d') ∉ X := by
  set e := eMod7 m d d' with he
  have he0 : e ≠ 0 := by
    intro h0
    rw [h0] at hν
    simp at hν
  obtain ⟨x, hx⟩ := exists_not_mem_three hX
  obtain ⟨k, hk7, hkq⟩ := exists_multLow_set_qdig hνm rfl he0 (x - 1)
  refine ⟨1 + k * 7 ^ (m - padicValNat 7 e), multLow_not_dvd hνm, ?_⟩
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
  · -- `x−1 − ẽ = 0` ⇒ `ẽ = x−1`
    have he7 : etd7 m ((1 + k * 7 ^ (m - padicValNat 7 e)) * d)
        ((1 + k * 7 ^ (m - padicValNat 7 e)) * d') = x - 1 :=
      (sub_eq_zero.mp hb).symm
    rw [he7]
    exact hx 1 (by decide)
  · -- `x−1 − ẽ = 1` ⇒ `ẽ = x−1−1 = x−2`
    have he7 : etd7 m ((1 + k * 7 ^ (m - padicValNat 7 e)) * d)
        ((1 + k * 7 ^ (m - padicValNat 7 e)) * d') = x - 2 := by
      have h0 : x - 1 - 1 = etd7 m ((1 + k * 7 ^ (m - padicValNat 7 e)) * d)
          ((1 + k * 7 ^ (m - padicValNat 7 e)) * d') := by
        linear_combination hb
      rw [← h0]
      ring
    rw [he7]
    exact hx 2 (by decide)
  · -- `x−1 − ẽ = 6` ⇒ `ẽ = x−1−6 = x`
    have he7 : etd7 m ((1 + k * 7 ^ (m - padicValNat 7 e)) * d)
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

/-- **Lemma 7(ii)**, `q(λ·7d) = 6` branch: for a `twoX` pair with
`ν(e) = m`, a `Λ₁`-element with `q(λ·7d) = 6` forces `q(2λd) = 2q(λd)+1`,
so `ẽ(λd,λd') ∈ {r(e)−1, r(e)}` — avoiding `X` when
`r(e) ∉ X ∪ (X+1)`.  Needs `m ≥ 2` (so that `Λ₁` acts below `ν(e) = m`
and `ν(7d) = 1 < m`). -/
theorem lemma7_ii {m : ℕ} (hm : 2 ≤ m) {d d' : ℕ}
    (hd : padicValNat 7 d = 0) (hd' : padicValNat 7 d' = 0)
    (hpos : 0 < d) (hpos' : 0 < d')
    (hrel : runit7 d' = 2 * runit7 d)
    (hν : padicValNat 7 (eMod7 m d d') = m)
    {X : Finset (ZMod 7)}
    (hr : runit7 (eMod7 m d d') ∉ X ∪ X.image (· + 1)) :
    ∃ lam : ℕ, ¬ 7 ∣ lam ∧ etd7 m (lam * d) (lam * d') ∉ X := by
  set e := eMod7 m d d' with he
  have h1m : 1 < m := by omega
  obtain ⟨k, hk7, hkq⟩ :=
    exists_multLow_one_set_seven' (by omega : 0 < m) hd hpos 6
  refine ⟨1 + k * 7 ^ (m - 1), multLow_not_dvd h1m, ?_⟩
  set lam := 1 + k * 7 ^ (m - 1) with hlam
  have hlamr : runit7 lam = 1 := runit7_multLow h1m
  -- `q(λ·7d) = 6` ⇒ `q(2λd) = 2q(λd)+1`
  have h7d : qdig7 m (7 * (lam * d)) = 6 := by
    have e' : 7 * (lam * d) = lam * (7 * d) := by ring
    rw [e']
    exact hkq
  have h2d : qdig7 m (2 * (lam * d)) = 2 * qdig7 m (lam * d) + 1 :=
    qdig7_two_eq_smul_add_one (by omega : 0 < m) h7d
  -- residue bookkeeping
  have hrd : runit7 d ≠ 0 := runit7_ne_zero hpos
  have hrld : runit7 (lam * d) = runit7 d := by
    rw [runit7_mul, hlamr, one_mul]
  have hrld' : runit7 (lam * d') = 2 * runit7 d := by
    rw [runit7_mul, hlamr, one_mul, hrel]
  have hr2ld : runit7 (2 * (lam * d)) = 2 * runit7 d := by
    rw [runit7_mul, runit7_two, hrld]
  -- the pair `(2λd, λd')` is same-class
  have hsame : residueRelOf (2 * (lam * d)) (lam * d') = residueRel.same := by
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
  -- `e(2λd, λd') = e` verbatim (`λ` preserves the level-`m` residue)
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
  -- `ẽ(2λd, λd') = q(2λd) − q(λd')` (same branch) and the Lemma-4(ii) bound
  have het2 : etd7 m (2 * (lam * d)) (lam * d') =
      qdig7 m (2 * (lam * d)) - qdig7 m (lam * d') := by
    unfold etd7
    rw [if_neg hif1, if_neg hif2]
  have hbound := qdig_eMod_sub_etd7_same (m := m)
    (x := 2 * (lam * d)) (y := lam * d') hsame
  rw [he2, qdig7_eq_runit7_of_top hν, het2, h2d] at hbound
  -- `r(e) − (2q(λd)+1 − q(λd')) ∈ {0,6}` ⇒ `ẽ ∈ {r(e)−1, r(e)}`
  have het : etd7 m (lam * d) (lam * d') =
      2 * qdig7 m (lam * d) - qdig7 m (lam * d') := by
    unfold etd7
    rw [if_pos (by rw [hrld', hrld])]
  rw [het]
  -- unpack `hr`
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
  · -- `r(e) − (ẽ+1) = 0` ⇒ `ẽ = r(e)−1`
    have he7 : 2 * qdig7 m (lam * d) - qdig7 m (lam * d') = runit7 e - 1 := by
      have h0 : runit7 e = 2 * qdig7 m (lam * d) + 1 - qdig7 m (lam * d') :=
        sub_eq_zero.mp hb
      rw [h0]
      ring
    rw [he7]
    exact hr2'
  · -- `r(e) − (ẽ+1) = 6` ⇒ `ẽ = r(e)`
    have he7 : 2 * qdig7 m (lam * d) - qdig7 m (lam * d') = runit7 e := by
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

#print axioms lemma7_i
#print axioms lemma7_ii
#print axioms eMod7_two_mul_left
#print axioms qdig7_eq_runit7_of_top
