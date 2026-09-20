/-
Copyright (c) 2026 Research07 contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Research07 contributors
-/
import Research07.LRC7.Case5mCases

/-!
# Paper Lemma 9(i) — the 3-compression lemma (Barajas–Serra §6)

For three same-class level-0 elements `B = {b1,b2,b3}` with difference
residues `x = e(b1,b3)`, `y = e(b2,b3)` at *distinct* levels `ν(x) ≠ ν(y)`
(both below `m`), a unit multiplier `λ` (a product of `Λ_{j<m}`-elements,
hence `λ ≡ 1 (mod 7)`) puts every pairwise difference digit in `{0,6}`:
`q(λ·e(bi,bj)) ∈ {0,6}` for all nine ordered pairs, and `ℓ(λB) ≤ 2`
follows by Remark 8(i).

**Signature deviation (demonstrated countermodel, see
`_reports/lrc7-sec6-lemma9i.md`):** the spec's verbatim statement is FALSE
when `ν(x) = m` or `ν(y) = m` — e.g. `m = 2`, `(b1,b2,b3) = (295,8,1)`
gives `x = 294` (`ν = 2 = m`), `y = 7`, and no unit `λ` makes all ordered
pairs land in `{0,6}`: `e(b3,b1) ≡ −x` and at level `m` one has
`λx ≡ t·7^m`, `λ·e(b3,b1) ≡ (7−t)·7^m`, so `q(λx) + q(λe31) = 7` can never
be `{6,6}`. The hypothesis `hνm` below is the minimal fix.

Contents:

* `qdig7_sub_resid` — the exact borrow formula for a wrapped residue
  difference: `q((a%N + N − b%N)%N) = q(a) − q(b) − (f_a < f_b ? 1 : 0)`.
  Drives the `x−y`, `y−x`, `−x`, `−y` pair digits (the `{0,6}` corollary
  and the `a := 0` negation `q(−b) = 6 − q(b)` when `f_b ≠ 0`).
* `eMod7_smul` — `e(cx,cy) ≡ c·e(x,y) (mod N)` for `runit7 c ≠ 0`
  (scalar behavior via the cloned `eMod7_zmod_cast` + branch
  preservation by `mul_left_cancel₀`).
* `lemma9_i` — the main theorem.
-/

private instance : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩

/-! ### Private clones of `Differences.lean`/`Case5mBase.lean` helpers -/

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
branch expression (local copy; `private` in `Case5mBase`/`Case5mCases`). -/
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

/-! ### Small structural helpers -/

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

/-- A `ZMod 7` element outside `{0,…,5}` is `6` (private decide). -/
private theorem eq_six_of_not_mem_five {q : ZMod 7}
    (h : q ∉ ({0, 1, 2, 3, 4, 5} : Finset (ZMod 7))) : q = 6 :=
  (show ∀ t : ZMod 7, t ∉ ({0, 1, 2, 3, 4, 5} : Finset (ZMod 7)) → t = 6
    from by decide) q h

/-- **Exact borrow formula** for the wrapped residue difference
`(a % N + N − b % N)`: writing `a % N = q_a·7^m + f_a`,
`b % N = q_b·7^m + f_b`, the top digit is `q_a − q_b` minus the borrow
`1` iff `f_a < f_b`.  The `{0,6}`-membership corollary is the
`x−y`/`y−x` engine; the `a = 0` case is the negation engine
(`q(−b) = −q(b) − (f_b ≠ 0 ? 1 : 0)`). -/
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

/-! ### `eMod7_smul` — scalar behavior of the difference residue -/

/-- `e(cx, cy) ≡ c·e(x,y) (mod 7^{m+1})` whenever `runit7 c ≠ 0` (the
residue-ratio branches are preserved since multiplication by a unit
scales both `runit7`s uniformly).  `eMod7_mul` is the `runit7 c = 1`
special case. -/
theorem eMod7_smul {m c x y : ℕ} (hc : runit7 c ≠ 0) :
    eMod7 m (c * x) (c * y) = (c * eMod7 m x y) % 7 ^ (m + 1) := by
  have hL : ((eMod7 m (c * x) (c * y) : ℕ) : ZMod (7 ^ (m + 1)))
      = (c * eMod7 m x y : ZMod (7 ^ (m + 1))) := by
    rw [eMod7_zmod_cast, eMod7_zmod_cast]
    simp only [runit7_mul]
    have sc1 : (runit7 c * runit7 y = 2 * (runit7 c * runit7 x)) ↔
        (runit7 y = 2 * runit7 x) := by
      constructor
      · intro h
        apply mul_left_cancel₀ hc
        rwa [show 2 * (runit7 c * runit7 x) = runit7 c * (2 * runit7 x) from
          by ring] at h
      · intro h; rw [h]; ring
    have sc2 : (runit7 c * runit7 x = 2 * (runit7 c * runit7 y)) ↔
        (runit7 x = 2 * runit7 y) := by
      constructor
      · intro h
        apply mul_left_cancel₀ hc
        rwa [show 2 * (runit7 c * runit7 y) = runit7 c * (2 * runit7 y) from
          by ring] at h
      · intro h; rw [h]; ring
    by_cases h1 : runit7 y = 2 * runit7 x
    · rw [ite_eq_left h1, ite_eq_left (sc1.mpr h1)]
      push_cast; ring
    · rw [ite_eq_right h1, ite_eq_right (fun hcon => h1 (sc1.mp hcon))]
      by_cases h2 : runit7 x = 2 * runit7 y
      · rw [ite_eq_left h2, ite_eq_left (sc2.mpr h2)]
        push_cast; ring
      · rw [ite_eq_right h2, ite_eq_right (fun hcon => h2 (sc2.mp hcon))]
        push_cast; ring
  have hlt : eMod7 m (c * x) (c * y) < 7 ^ (m + 1) := by
    unfold eMod7
    split_ifs <;> exact Nat.mod_lt _ (Nat.pow_pos (by norm_num))
  rw [← Nat.cast_mul] at hL
  rw [ZMod.natCast_eq_natCast_iff] at hL
  have hL' : eMod7 m (c * x) (c * y) % 7 ^ (m + 1)
      = (c * eMod7 m x y) % 7 ^ (m + 1) := hL
  rwa [Nat.mod_eq_of_lt hlt] at hL'

/-! ### The main theorem -/

/-- **Paper Lemma 9(i)** (3-compression): three same-class level-0
elements with difference residues `x = e(b1,b3)`, `y = e(b2,b3)` at
distinct levels `< m` admit a unit `λ` with every pairwise difference
digit in `{0,6}` and `ℓ(λB) ≤ 2`.

**Deviation from spec §3.5**: hypothesis `hνm` added — the verbatim
statement is false when `ν(x) = m` or `ν(y) = m` (reversed pair
`e(b3,b1) ≡ −x` then forces `q(λx) + q(λe31) = 7`, never `{6,6}`).
See `_reports/lrc7-sec6-lemma9i.md` for the countermodel. -/
theorem lemma9_i {m : ℕ} {b1 b2 b3 : ℕ}
    (hpos : 0 < b1 ∧ 0 < b2 ∧ 0 < b3)
    (_hunit : padicValNat 7 b1 = 0 ∧ padicValNat 7 b2 = 0 ∧ padicValNat 7 b3 = 0)
    (hsame : runit7 b1 = runit7 b2 ∧ runit7 b2 = runit7 b3)
    (hν : padicValNat 7 (eMod7 m b1 b3) ≠ padicValNat 7 (eMod7 m b2 b3))
    (hνm : padicValNat 7 (eMod7 m b1 b3) < m ∧
      padicValNat 7 (eMod7 m b2 b3) < m)
    (he : eMod7 m b1 b3 ≠ 0 ∧ eMod7 m b2 b3 ≠ 0) :
    ∃ lam : ℕ, ¬ 7 ∣ lam ∧
      (∀ x ∈ ({b1,b2,b3} : Finset ℕ), ∀ y ∈ ({b1,b2,b3} : Finset ℕ),
        qdig7 m (eMod7 m (lam*x) (lam*y)) ∈ ({0,6} : Finset (ZMod 7))) ∧
      apLen (({b1,b2,b3} : Finset ℕ).image (fun d => qdig7 m (lam*d))) ≤ 2 := by
  classical
  set x := eMod7 m b1 b3 with hx
  set y := eMod7 m b2 b3 with hy
  have hx0 : x ≠ 0 := he.1
  have hy0 : y ≠ 0 := he.2
  have hxν : padicValNat 7 x < m := hνm.1
  have hyν : padicValNat 7 y < m := hνm.2
  -- Step 1: `filtered7_mod7` on `D = {x,y}` with `F = {0,…,5}` forces
  -- `q(λx) = q(λy) = 6`; each level `< m` holds at most one of `x,y`.
  set D : Finset ℕ := {x, y} with hD
  have hposD : ∀ d ∈ D, 0 < d := by
    intro d hd
    rcases Finset.mem_insert.mp hd with rfl | hd'
    · exact Nat.pos_of_ne_zero hx0
    · rw [Finset.mem_singleton] at hd'
      subst hd'
      exact Nat.pos_of_ne_zero hy0
  have hmD : ∀ d ∈ D, padicValNat 7 d ≤ m := by
    intro d hd
    rcases Finset.mem_insert.mp hd with rfl | hd'
    · exact enu7_le_of_ne hx0
    · rw [Finset.mem_singleton] at hd'
      subst hd'
      exact enu7_le_of_ne hy0
  have hlow : ∀ j, j < m → ((level7 D j).sum
      fun d => (({0, 1, 2, 3, 4, 5} : Finset (ZMod 7))).card) ≤ 6 := by
    intro j _
    have hcard : (level7 D j).card ≤ 1 := by
      by_cases hxj : padicValNat 7 x = j
      · have hsub : level7 D j ⊆ {x} := by
          intro d hd
          obtain ⟨hdD, hdν⟩ := Finset.mem_filter.mp hd
          rw [Finset.mem_singleton]
          rcases Finset.mem_insert.mp hdD with rfl | hd''
          · rfl
          · rw [Finset.mem_singleton] at hd''
            subst hd''
            exact absurd (hxj.trans hdν.symm) hν
        exact le_trans (Finset.card_le_card hsub)
          (by rw [Finset.card_singleton])
      · have hsub : level7 D j ⊆ {y} := by
          intro d hd
          obtain ⟨hdD, hdν⟩ := Finset.mem_filter.mp hd
          rw [Finset.mem_singleton]
          rcases Finset.mem_insert.mp hdD with rfl | hd''
          · exact absurd hdν hxj
          · exact Finset.mem_singleton.mp hd''
        exact le_trans (Finset.card_le_card hsub)
          (by rw [Finset.card_singleton])
    have hc : (({0, 1, 2, 3, 4, 5} : Finset (ZMod 7))).card = 6 := by decide
    rw [Finset.sum_const, smul_eq_mul, hc]
    omega
  obtain ⟨lam, hlam7, hlammod, hver, hgd⟩ := filtered7_mod7 D hposD hmD
    le_rfl (fun _ => ({0, 1, 2, 3, 4, 5} : Finset (ZMod 7))) hlow
  have hxD : x ∈ D := Finset.mem_insert_self _ _
  have hyD : y ∈ D :=
    Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self _))
  have hqx : qdig7 m (lam * x) = 6 := eq_six_of_not_mem_five (hgd x hxD hxν)
  have hqy : qdig7 m (lam * y) = 6 := eq_six_of_not_mem_five (hgd y hyD hyν)
  have hlamr : runit7 lam = 1 := runit7_eq_one_of_mod7 hlammod
  have hl0 : lam ≠ 0 := by
    rintro rfl
    simp at hlammod
  -- low parts `λx % 7^m`, `λy % 7^m` are nonzero (`ν(λ·) = ν < m`)
  have hfx : (lam * x) % 7 ^ m ≠ 0 := by
    have hval : padicValNat 7 (lam * x) = padicValNat 7 x :=
      padicValNat_mul_seven hlam7 hx0
    have hnd : ¬ 7 ^ m ∣ lam * x := by
      intro hd
      have hle := (Nat.pow_dvd_iff_le_padicValNat (by norm_num)
        (mul_ne_zero hl0 hx0)).mp hd
      rw [hval] at hle
      omega
    rwa [Nat.dvd_iff_mod_eq_zero] at hnd
  have hfy : (lam * y) % 7 ^ m ≠ 0 := by
    have hval : padicValNat 7 (lam * y) = padicValNat 7 y :=
      padicValNat_mul_seven hlam7 hy0
    have hnd : ¬ 7 ^ m ∣ lam * y := by
      intro hd
      have hle := (Nat.pow_dvd_iff_le_padicValNat (by norm_num)
        (mul_ne_zero hl0 hy0)).mp hd
      rw [hval] at hle
      omega
    rwa [Nat.dvd_iff_mod_eq_zero] at hnd
  -- Step 2: residue relations of the (unscaled) pairs
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
  have hxcast : ((x : ℕ) : ZMod (7 ^ (m + 1))) = (b1 : ZMod _) - (b3 : ZMod _) := by
    rw [hx]
    exact eMod7_zmod_cast_same hrel13
  have hycast : ((y : ℕ) : ZMod (7 ^ (m + 1))) = (b2 : ZMod _) - (b3 : ZMod _) := by
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
    rw [eMod7_mul hlamr, qdig7_congr (Nat.mod_mod _ _)]
    exact qdig_smul_eMod_eq hcast
  -- Step 3: the nine ordered pairs
  have key : ∀ u ∈ ({b1, b2, b3} : Finset ℕ),
      ∀ v ∈ ({b1, b2, b3} : Finset ℕ),
      qdig7 m (eMod7 m (lam * u) (lam * v)) ∈ ({0, 6} : Finset (ZMod 7)) := by
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
    · -- (b1,b2): `λe ≡ λx − λy`
      have hcast : ((lam * eMod7 m b1 b2 : ℕ) : ZMod (7 ^ (m + 1)))
          = ((lam * x : ℕ) : ZMod _) - ((lam * y : ℕ) : ZMod _) := by
        rw [Nat.cast_mul, eMod7_zmod_cast_same hrel12,
          Nat.cast_mul, Nat.cast_mul, hxcast, hycast]
        ring
      rw [eval _ _ _ _ hcast, hqx, hqy]
      by_cases hb : (lam * x) % 7 ^ m < (lam * y) % 7 ^ m
      · rw [ite_eq_left hb]
        decide
      · rw [ite_eq_right hb]
        decide
    · -- (b1,b3): `λe ≡ λx − 0`
      have hcast : ((lam * eMod7 m b1 b3 : ℕ) : ZMod (7 ^ (m + 1)))
          = ((lam * x : ℕ) : ZMod _) - ((0 : ℕ) : ZMod _) := by
        rw [Nat.cast_mul, eMod7_zmod_cast_same hrel13]
        ring
      rw [eval _ _ _ _ hcast, hqx, qdig7_zero]
      rw [ite_eq_right (by rw [Nat.zero_mod]; exact Nat.not_lt_zero _)]
      decide
    · -- (b2,b1): `λe ≡ λy − λx`
      have hcast : ((lam * eMod7 m b2 b1 : ℕ) : ZMod (7 ^ (m + 1)))
          = ((lam * y : ℕ) : ZMod _) - ((lam * x : ℕ) : ZMod _) := by
        rw [Nat.cast_mul, eMod7_zmod_cast_same hrel21,
          Nat.cast_mul, Nat.cast_mul, hxcast, hycast]
        ring
      rw [eval _ _ _ _ hcast, hqy, hqx]
      by_cases hb : (lam * y) % 7 ^ m < (lam * x) % 7 ^ m
      · rw [ite_eq_left hb]
        decide
      · rw [ite_eq_right hb]
        decide
    · -- (b2,b2): `λe ≡ 0 − 0`
      have hcast : ((lam * eMod7 m b2 b2 : ℕ) : ZMod (7 ^ (m + 1)))
          = ((0 : ℕ) : ZMod _) - ((0 : ℕ) : ZMod _) := by
        rw [Nat.cast_mul, eMod7_zmod_cast_same hrel22]
        ring
      rw [eval _ _ _ _ hcast, qdig7_zero]
      rw [ite_eq_right (by simp)]
      decide
    · -- (b2,b3): `λe ≡ λy − 0`
      have hcast : ((lam * eMod7 m b2 b3 : ℕ) : ZMod (7 ^ (m + 1)))
          = ((lam * y : ℕ) : ZMod _) - ((0 : ℕ) : ZMod _) := by
        rw [Nat.cast_mul, eMod7_zmod_cast_same hrel23]
        ring
      rw [eval _ _ _ _ hcast, hqy, qdig7_zero]
      rw [ite_eq_right (by rw [Nat.zero_mod]; exact Nat.not_lt_zero _)]
      decide
    · -- (b3,b1): `λe ≡ 0 − λx`, borrow `0 < fx` gives `q = −6 − 1 = 0`
      have hcast : ((lam * eMod7 m b3 b1 : ℕ) : ZMod (7 ^ (m + 1)))
          = ((0 : ℕ) : ZMod _) - ((lam * x : ℕ) : ZMod _) := by
        rw [Nat.cast_mul, eMod7_zmod_cast_same hrel31,
          Nat.cast_mul, hxcast]
        ring
      rw [eval _ _ _ _ hcast, qdig7_zero, hqx]
      rw [ite_eq_left (by rw [Nat.zero_mod]; exact Nat.pos_of_ne_zero hfx)]
      decide
    · -- (b3,b2): `λe ≡ 0 − λy`
      have hcast : ((lam * eMod7 m b3 b2 : ℕ) : ZMod (7 ^ (m + 1)))
          = ((0 : ℕ) : ZMod _) - ((lam * y : ℕ) : ZMod _) := by
        rw [Nat.cast_mul, eMod7_zmod_cast_same hrel32,
          Nat.cast_mul, hycast]
        ring
      rw [eval _ _ _ _ hcast, qdig7_zero, hqy]
      rw [ite_eq_left (by rw [Nat.zero_mod]; exact Nat.pos_of_ne_zero hfy)]
      decide
    · -- (b3,b3): `λe ≡ 0 − 0`
      have hcast : ((lam * eMod7 m b3 b3 : ℕ) : ZMod (7 ^ (m + 1)))
          = ((0 : ℕ) : ZMod _) - ((0 : ℕ) : ZMod _) := by
        rw [Nat.cast_mul, eMod7_zmod_cast_same hrel33]
        ring
      rw [eval _ _ _ _ hcast, qdig7_zero]
      rw [ite_eq_right (by simp)]
      decide
  -- Step 4: `apLen ≤ 2` via `remark8_i_int` + `remark8_i` at `k = 1`.
  have hposB : ∀ d ∈ ({b1, b2, b3} : Finset ℕ), 0 < d := by
    intro d hd
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with h | h | h <;> rw [h]
    · exact hpos.1
    · exact hpos.2.1
    · exact hpos.2.2
  have hr_all : ∀ d ∈ ({b1, b2, b3} : Finset ℕ), runit7 d = runit7 b3 := by
    intro d hd
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with h | h | h <;> rw [h] <;>
      first
        | exact hsame.1.trans hsame.2
        | exact hsame.2
  set BL : Finset ℕ := ({b1, b2, b3} : Finset ℕ).image (lam * ·) with hBLdef
  have hBLsame : ∀ u ∈ BL, ∀ v ∈ BL,
      residueRelOf u v = residueRel.same := by
    intro u hu v hv
    obtain ⟨u', hu', rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨v', hv', rfl⟩ := Finset.mem_image.mp hv
    apply rel_same _ (mul_ne_zero hl0 (ne_of_gt (hposB v' hv')))
    rw [runit7_mul, runit7_mul, hr_all u' hu', hr_all v' hv']
  have hBL : ∀ u ∈ BL, ∀ v ∈ BL,
      qdig7 m (eMod7 m u v) ∈ ({0, 6} : Finset (ZMod 7)) := by
    intro u hu v hv
    obtain ⟨u', hu', rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨v', hv', rfl⟩ := Finset.mem_image.mp hv
    exact key u' hu' v' hv'
  have hdiff : ∀ a ∈ BL.image (qdig7 m), ∀ b ∈ BL.image (qdig7 m),
      a - b ∈ ({0, 1, 6} : Finset (ZMod 7)) :=
    remark8_i_int hBLsame hBL
  have hlen : apLen (BL.image (qdig7 m)) ≤ 2 := by
    have h := remark8_i hdiff (k := 1) (by decide)
    simp only [mul_one] at h
    rw [Finset.image_id'] at h
    have h1 : (1 : ZMod 7).val = 1 := by decide
    rw [h1] at h
    exact h
  have himg : BL.image (qdig7 m)
      = ({b1, b2, b3} : Finset ℕ).image (fun d => qdig7 m (lam * d)) := by
    rw [hBLdef]
    exact Finset.image_image
  rw [himg] at hlen
  exact ⟨lam, hlam7, key, hlen⟩

#print axioms lemma9_i
#print axioms eMod7_smul
