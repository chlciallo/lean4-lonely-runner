import Research07.LRC7.Case5mTop
import Research07.LRC7.Case5mL9b
import Research07.LRC7.Case5mL10

/-!
# §6.2 of Barajas–Serra: the `|A1| = 4`, `|Ar| = 1` subcase

`A1` is a four-element dominant residue class (all `runit7 = s ∈ {1,2,4}`)
and `Ar` is a singleton `{d5}` with `runit7 d5 ∈ {2s, 4s}`.  The paper's
Lemma 10 splits on the difference structure of `A1`; each branch compresses
the digit image into a bounded cyclic interval, and Lemma 5/6 finish.

The key structural fact used throughout: a difference `eMod7 m x y` at
level exactly `m` is verbatim `r·7^m` (`residN_top`), so digit offsets
`q(x) − q(y) = r(e)` are *exact* (`qdig7_add_top_resid`) — no borrow
noise.  This is why Case B (all differences at level `m`) can be handled
by pure `ZMod 7` geometry.
-/

private instance : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩

/-! ### Finite `ZMod 7`/`apLen` decision facts -/

/-- `2·{0,6,3} + {0,1}` lands inside `{0,1,5,6}` (the `q4 = 3` rescale). -/
private theorem case62_dilate2 :
    (Finset.biUnion ({0, 6, 3} : Finset (ZMod 7))
      (fun q => ({2 * q, 2 * q + 1} : Finset (ZMod 7))))
      ⊆ ({0, 1, 5, 6} : Finset (ZMod 7)) := by decide

private theorem case62_apLen_rescaled :
    apLen ({0, 1, 5, 6} : Finset (ZMod 7)) ≤ 4 := by decide

/-- The `{0,u,2u,4u}` shape always fits a 5-interval. -/
private theorem case62_quad_le5 : ∀ u : ZMod 7, u ≠ 0 →
    apLen ({0, u, 2 * u, 4 * u} : Finset (ZMod 7)) ≤ 5 := by decide

/-- The `{0,u,2u,3u}` shape rescales into a 4-interval. -/
private theorem case62_cub_rescale : ∀ u : ZMod 7, u ≠ 0 →
    ∃ c : ZMod 7, c ≠ 0 ∧
      apLen ({0, c * u, 2 * c * u, 3 * c * u} : Finset (ZMod 7)) ≤ 4 := by
  decide

/-- The degenerate `{0,u,w}` shape (case B (i), `e31 = 0`) rescales into
a 4-interval. -/
private theorem case62_pair_rescale : ∀ u w : ZMod 7, u ≠ 0 →
    ∃ c : ZMod 7, c ≠ 0 ∧
      apLen ({0, c * u, c * w} : Finset (ZMod 7)) ≤ 4 := by decide

/-- Every nonzero residue has a `{1,2,4}`-stabilizer image outside
`{0,4,5,6}` (the `{4,6}`-avoidance stabilizer). -/
private theorem case62_stab46 : ∀ r : ZMod 7, r ≠ 0 →
    ∃ c : ZMod 7, c ∈ ({1, 2, 4} : Finset (ZMod 7)) ∧
      c * r ∉ ({0, 4, 5, 6} : Finset (ZMod 7)) := by decide

/-- Every nonzero residue has a `{1,2,4}`-stabilizer image outside
`{2,3,4}` (the `{2,3}`-avoidance stabilizer). -/
private theorem case62_stab23 : ∀ r : ZMod 7, r ≠ 0 →
    ∃ c : ZMod 7, c ∈ ({1, 2, 4} : Finset (ZMod 7)) ∧
      c * r ∉ ({2, 3, 4} : Finset (ZMod 7)) := by decide

/-- Two digits at cyclic distance `0` or `6` fit a 2-interval. -/
private theorem case62_pair06 : ∀ a b : ZMod 7,
    b - a ∈ ({0, 6} : Finset (ZMod 7)) →
    apLen ({a, b} : Finset (ZMod 7)) ≤ 2 := by decide

/-- A two-element digit set always fits a 4-interval. -/
private theorem case62_pair_le4 : ∀ a b : ZMod 7,
    apLen ({a, b} : Finset (ZMod 7)) ≤ 4 := by decide

/-- `apLen` is monotone under inclusion (clone of the private
`Case5mTop.apLen_mono'`). -/
private theorem apLen_mono'' {X Y : Finset (ZMod 7)} (hXY : X ⊆ Y) :
    apLen X ≤ apLen Y := by
  have h7 := apLen_le_seven Y
  obtain ⟨i, hi⟩ := (apLen_le_iff Y (apLen Y) h7).mp le_rfl
  exact (apLen_le_iff X (apLen Y) h7).mpr ⟨i, hXY.trans hi⟩

/-! ### Same-branch helpers -/

/-- Two elements with equal nonzero `runit7` are `same`-related. -/
private theorem case62_rel_same {x y : ℕ} {s : ZMod 7} (hs : s ≠ 0)
    (hx : runit7 x = s) (hy : runit7 y = s) :
    residueRelOf x y = residueRel.same := by
  rw [residueRelOf_eq_same]
  refine ⟨?_, ?_⟩ <;> intro hcon
  · rw [hy, hx] at hcon
    exact hs (neg_eq_zero.mp (by linear_combination hcon))
  · rw [hx, hy] at hcon
    exact hs (neg_eq_zero.mp (by linear_combination hcon))

/-- `eMod7` is bounded by `7^{m+1}`. -/
private theorem case62_eMod7_lt {m x y : ℕ} : eMod7 m x y < 7 ^ (m + 1) := by
  unfold eMod7
  split_ifs <;> exact Nat.mod_lt _ (Nat.pow_pos (by norm_num))

/-- In the `same` branch, `x ≡ y + e (mod 7^{m+1})` on residues. -/
private theorem case62_resid_add {m x y : ℕ}
    (hrel : residueRelOf x y = residueRel.same) :
    x % 7 ^ (m + 1) = (y % 7 ^ (m + 1) + eMod7 m x y) % 7 ^ (m + 1) := by
  have hN : (0 : ℕ) < 7 ^ (m + 1) := Nat.pow_pos (by norm_num)
  have hdef : eMod7 m x y =
      (x % 7 ^ (m + 1) + 7 ^ (m + 1) - y % 7 ^ (m + 1)) % 7 ^ (m + 1) := by
    unfold eMod7
    rw [residueRelOf_eq_same] at hrel
    rw [if_neg hrel.1, if_neg hrel.2]
  set e := eMod7 m x y
  set X := x % 7 ^ (m + 1)
  set Y := y % 7 ^ (m + 1)
  have hX : X < 7 ^ (m + 1) := Nat.mod_lt _ hN
  have hY : Y < 7 ^ (m + 1) := Nat.mod_lt _ hN
  have he : e < 7 ^ (m + 1) := case62_eMod7_lt
  -- `D := X + N − Y`, `D % N = e`, `0 < D < 2N`.
  have hDlt : X + 7 ^ (m + 1) - Y < 2 * 7 ^ (m + 1) := by omega
  have hDpos : 0 < X + 7 ^ (m + 1) - Y := by omega
  have hmod : (X + 7 ^ (m + 1) - Y) % 7 ^ (m + 1) = e := hdef.symm
  -- `D = e` or `D = e + N`
  have hD : X + 7 ^ (m + 1) - Y = e ∨ X + 7 ^ (m + 1) - Y = e + 7 ^ (m + 1) := by
    have hdiv := Nat.mod_add_div (X + 7 ^ (m + 1) - Y) (7 ^ (m + 1))
    rw [hmod] at hdiv
    set w := (X + 7 ^ (m + 1) - Y) / (7 ^ (m + 1))
    have hw : w < 2 := by
      by_contra h2
      push Not at h2
      have : e + 7 ^ (m + 1) * w ≥ 7 ^ (m + 1) * 2 := by
        calc e + 7 ^ (m + 1) * w ≥ 7 ^ (m + 1) * w := Nat.le_add_left _ _
          _ ≥ 7 ^ (m + 1) * 2 := Nat.mul_le_mul_left _ h2
      omega
    interval_cases w
    · left; omega
    · right; omega
  rcases hD with h | h
  · -- `X + N − Y = e` forces `Y + e ≥ N`, `X = Y + e − N`
    have h1 : X = Y + e - 7 ^ (m + 1) := by omega
    have h2 : Y + e ≥ 7 ^ (m + 1) := by omega
    rw [h1]
    rw [Nat.mod_eq_sub_mod (by omega : 7 ^ (m + 1) ≤ Y + e),
      Nat.mod_eq_of_lt (by omega : Y + e - 7 ^ (m + 1) < 7 ^ (m + 1))]
  · -- `X − Y = e`, `X = Y + e < N`
    have h1 : X = Y + e := by omega
    rw [h1]
    rw [Nat.mod_eq_of_lt (by omega : Y + e < 7 ^ (m + 1))]

/-- Exact digit offset for a level-`m` `same`-branch difference:
`q(x) − q(y) = r(e)`.  This is the workhorse for Case B. -/
private theorem case62_qdig_sub_top {m x y : ℕ}
    (hrel : residueRelOf x y = residueRel.same)
    (_he : eMod7 m x y ≠ 0) (hν : padicValNat 7 (eMod7 m x y) = m) :
    qdig7 m x - qdig7 m y = runit7 (eMod7 m x y) := by
  set e := eMod7 m x y with hde
  have helt : e < 7 ^ (m + 1) := case62_eMod7_lt
  have heeq : e = (qdig7 m e).val * 7 ^ m := by
    have := residN_top hν
    rwa [Nat.mod_eq_of_lt helt] at this
  have hcong := case62_resid_add (m := m) hrel
  rw [← hde, heeq] at hcong
  have hqd := qdig7_add_top_resid hcong
  rw [ZMod.natCast_zmod_val, qdig7_eq_runit7_of_top hν] at hqd
  rw [hqd, add_sub_cancel_left]

/-- The `same`-branch `e = 0` residue equality. -/
private theorem case62_resid_eq_of_eMod_eq_zero {m x y : ℕ}
    (hrel : residueRelOf x y = residueRel.same)
    (he : eMod7 m x y = 0) :
    x % 7 ^ (m + 1) = y % 7 ^ (m + 1) := by
  have h := case62_resid_add (m := m) hrel
  rw [he, add_zero] at h
  rwa [Nat.mod_eq_of_lt (Nat.mod_lt _ (Nat.pow_pos (by norm_num)))] at h

/-- A `lam ≡ 1 (mod 7)` multiplier preserves level-`m` residues
verbatim: `(lam·(u·7^m)) % 7^{m+1} = u·7^m` for residues `e < 7^{m+1}`
with `ν(e) = m`. -/
private theorem case62_smul_top_resid {m lam e : ℕ}
    (hlam : lam % 7 = 1) (helt : e < 7 ^ (m + 1))
    (hν : padicValNat 7 e = m) :
    (lam * e) % 7 ^ (m + 1) = e := by
  set u := (qdig7 m e).val with hu
  have heeq : e = u * 7 ^ m := by
    have := residN_top hν
    rw [Nat.mod_eq_of_lt helt, ← hu] at this
    exact this
  -- `lam = 1 + 7·w`
  obtain ⟨w, hw⟩ : ∃ w : ℕ, lam = 1 + 7 * w := by
    refine ⟨lam / 7, ?_⟩
    have h := Nat.div_add_mod lam 7
    rw [hlam] at h
    omega
  -- `lam·e = e + w·u·7^{m+1}`
  have hmul : lam * e = e + w * u * 7 ^ (m + 1) := by
    rw [pow_succ, hw, heeq]
    ring
  rw [hmul, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt helt]

/-- For a `lam ≡ 1 (mod 7)` multiplier, a level-`m` `same`-branch pair
keeps its exact digit offset: `q(lam·x) − q(lam·y) = r(e(x,y))`. -/
private theorem case62_qdig_sub_smul1_top {m lam x y : ℕ}
    (hlam : lam % 7 = 1)
    (hrel : residueRelOf x y = residueRel.same)
    (he : eMod7 m x y ≠ 0) (hν : padicValNat 7 (eMod7 m x y) = m) :
    qdig7 m (lam * x) - qdig7 m (lam * y) = runit7 (eMod7 m x y) := by
  have hlamr : runit7 lam = 1 := runit7_eq_one_of_mod7 hlam
  -- `e(lam·x, lam·y) = (lam·e) % N = e`
  have hrl : residueRelOf (lam * x) (lam * y) = residueRel.same := by
    rw [residueRelOf_eq_same] at hrel ⊢
    rw [runit7_mul, runit7_mul, hlamr]
    simpa using hrel
  have hE : eMod7 m (lam * x) (lam * y) = eMod7 m x y := by
    rw [eMod7_mul hlamr, case62_smul_top_resid hlam case62_eMod7_lt hν]
  have hqd := case62_qdig_sub_top hrl (x := lam * x) (y := lam * y)
    (by rw [hE]; exact he) (by rw [hE]; exact hν)
  rwa [hE] at hqd

/-- Casting a mod-`7^{m+1}` residue to `ZMod 7` is the plain cast. -/
private theorem case62_mod7_cast {m a : ℕ} :
    ((a % 7 ^ (m + 1) : ℕ) : ZMod 7) = (a : ZMod 7) := by
  have h7N : 7 ∣ 7 ^ (m + 1) := ⟨7 ^ m, by rw [pow_succ']⟩
  apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  exact Nat.mod_mod_of_dvd a h7N

/-- The mod-7 value of an `eMod7` residue is the branch expression. -/
private theorem case62_eMod7_cast7 {m x y : ℕ} :
    ((eMod7 m x y : ℕ) : ZMod 7) =
      if runit7 y = 2 * runit7 x then 2 * (x : ZMod 7) - y
      else if runit7 x = 2 * runit7 y then 2 * (y : ZMod 7) - x
      else (x : ZMod 7) - y := by
  have hN : (0 : ℕ) < 7 ^ (m + 1) := Nat.pow_pos (by norm_num)
  have h7N : 7 ∣ 7 ^ (m + 1) := ⟨7 ^ m, by rw [pow_succ']⟩
  have hN0 : (7 : ZMod 7) ^ (m + 1) = 0 := by
    have h7z : (7 : ZMod 7) = 0 := by decide
    rw [h7z]
    exact zero_pow (by omega)
  have hX : ((x % 7 ^ (m + 1) : ℕ) : ZMod 7) = (x : ZMod 7) :=
    case62_mod7_cast
  have hY : ((y % 7 ^ (m + 1) : ℕ) : ZMod 7) = (y : ZMod 7) :=
    case62_mod7_cast
  unfold eMod7
  split_ifs with h1 h2
  · rw [case62_mod7_cast]
    have hle : y % 7 ^ (m + 1) ≤
        2 * (x % 7 ^ (m + 1)) + 7 ^ (m + 1) := by
      have := Nat.mod_lt y hN
      omega
    rw [Nat.cast_sub hle]
    push_cast
    rw [hX, hY, hN0]
    ring
  · rw [case62_mod7_cast]
    have hle : x % 7 ^ (m + 1) ≤
        2 * (y % 7 ^ (m + 1)) + 7 ^ (m + 1) := by
      have := Nat.mod_lt x hN
      omega
    rw [Nat.cast_sub hle]
    push_cast
    rw [hX, hY, hN0]
    ring
  · rw [case62_mod7_cast]
    have hle : y % 7 ^ (m + 1) ≤ x % 7 ^ (m + 1) + 7 ^ (m + 1) := by
      have := Nat.mod_lt y hN
      omega
    rw [Nat.cast_sub hle]
    push_cast
    rw [hX, hY, hN0]
    ring

/-- `(e : ZMod 7) = 0` means `7 ∣ e`. -/
private theorem case62_dvd7_of_cast {m x y : ℕ}
    (h : ((eMod7 m x y : ℕ) : ZMod 7) = 0) : 7 ∣ eMod7 m x y := by
  exact (ZMod.natCast_eq_zero_iff _ _).mp h

/-- For level-0 elements, `runit7` is the mod-7 cast. -/
private theorem case62_runit7_eq_cast {x : ℕ} (hx : padicValNat 7 x = 0) :
    runit7 x = (x : ZMod 7) := by
  unfold runit7
  rw [hx, pow_zero, Nat.div_one]

/-- `7 ∣ e(x,y)` for a `twoX` pair (`r(y) = 2r(x)`): the residue
`2x − y` vanishes mod 7. -/
private theorem case62_dvd7_twoX {m x y : ℕ}
    (hx : padicValNat 7 x = 0) (hy : padicValNat 7 y = 0)
    (hrel : runit7 y = 2 * runit7 x) : 7 ∣ eMod7 m x y := by
  apply case62_dvd7_of_cast
  rw [case62_eMod7_cast7, if_pos hrel]
  rw [case62_runit7_eq_cast hx, case62_runit7_eq_cast hy] at hrel
  rw [hrel]
  ring

/-- `7 ∣ e(x,y)` for a `twoY` pair (`r(x) = 2r(y)`): the residue
`2y − x` vanishes mod 7. -/
private theorem case62_dvd7_twoY {m x y : ℕ}
    (hx : padicValNat 7 x = 0) (hy : padicValNat 7 y = 0)
    (hy0 : 0 < y)
    (hrel : runit7 x = 2 * runit7 y) : 7 ∣ eMod7 m x y := by
  apply case62_dvd7_of_cast
  rw [case62_eMod7_cast7]
  have hrelc : (x : ZMod 7) = 2 * (y : ZMod 7) := by
    rw [← case62_runit7_eq_cast hx, ← case62_runit7_eq_cast hy]
    exact hrel
  have h1 : runit7 y ≠ 2 * runit7 x := by
    intro hcon
    have hconc : (y : ZMod 7) = 2 * (x : ZMod 7) := by
      rw [← case62_runit7_eq_cast hx, ← case62_runit7_eq_cast hy]
      exact hcon
    -- `↑y = 2·↑x = 4·↑y` gives `3·↑y = 0`, hence `↑y = 0`.
    rw [hrelc] at hconc
    have h3 : (3 : ZMod 7) * (y : ZMod 7) = 0 := by
      linear_combination -hconc
    have hr0 : (y : ZMod 7) = 0 := by
      rcases mul_eq_zero.mp h3 with h3z | hyz
      · exact absurd h3z (by decide)
      · exact hyz
    have hr : runit7 y = 0 := by rw [case62_runit7_eq_cast hy]; exact hr0
    exact runit7_ne_zero hy0 hr
  rw [if_neg h1, if_pos hrel]
  rw [hrelc]
  ring

/-- `7 ∣ e(x,y)` for a `same` pair: the residue `x − y` vanishes mod 7. -/
private theorem case62_dvd7_same {m x y : ℕ}
    (hx : padicValNat 7 x = 0) (hy : padicValNat 7 y = 0)
    (hxy : runit7 x = runit7 y)
    (hrel : residueRelOf x y = residueRel.same) : 7 ∣ eMod7 m x y := by
  obtain ⟨h1, h2⟩ := (residueRelOf_eq_same).mp hrel
  apply case62_dvd7_of_cast
  rw [case62_eMod7_cast7, if_neg h1, if_neg h2]
  have hcc : (x : ZMod 7) = (y : ZMod 7) := by
    rw [← case62_runit7_eq_cast hx, ← case62_runit7_eq_cast hy]
    exact hxy
  rw [hcc, sub_self]

/-- `eMod7` in the `same` branch is the wrapped difference (clone). -/
private theorem case62_eMod7_same_eq {m x y : ℕ}
    (h : residueRelOf x y = residueRel.same) :
    eMod7 m x y
      = (x % 7 ^ (m + 1) + 7 ^ (m + 1) - y % 7 ^ (m + 1)) % 7 ^ (m + 1) := by
  obtain ⟨h1, h2⟩ := (residueRelOf_eq_same).mp h
  unfold eMod7
  rw [if_neg h1, if_neg h2]

/-- `eMod7 = 0` in the `same` branch forces equal residues (clone). -/
private theorem case62_eq_resid_of_eMod7_eq_zero {m x y : ℕ}
    (h : eMod7 m x y = 0) (hrel : residueRelOf x y = residueRel.same) :
    x % 7 ^ (m + 1) = y % 7 ^ (m + 1) := by
  rw [case62_eMod7_same_eq hrel] at h
  have hx : x % 7 ^ (m + 1) < 7 ^ (m + 1) :=
    Nat.mod_lt _ (Nat.pow_pos (by norm_num))
  have hy : y % 7 ^ (m + 1) < 7 ^ (m + 1) :=
    Nat.mod_lt _ (Nat.pow_pos (by norm_num))
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
/-- `e(x,y) = 0` with equal units forces `q(c·x) = q(c·y)` for any scalar
`c` with `runit7 c ≠ 0`. -/
private theorem case62_qdig_eq_of_eMod7_zero {m c x y : ℕ}
    (hc : runit7 c ≠ 0)
    (hrel : residueRelOf x y = residueRel.same)
    (he : eMod7 m x y = 0) :
    qdig7 m (c * x) = qdig7 m (c * y) := by
  have hr' : residueRelOf (c * x) (c * y) = residueRel.same := by
    rw [residueRelOf_eq_same] at hrel ⊢
    obtain ⟨h1, h2⟩ := hrel
    rw [runit7_mul, runit7_mul]
    refine ⟨?_, ?_⟩ <;> intro hcon
    · exact h1 (mul_left_cancel₀ hc (by linear_combination hcon))
    · exact h2 (mul_left_cancel₀ hc (by linear_combination hcon))
  have he' : eMod7 m (c * x) (c * y) = 0 := by
    rw [eMod7_smul hc, he, mul_zero, Nat.zero_mod]
  exact qdig7_congr (case62_eq_resid_of_eMod7_eq_zero he' hr')

/-- `ν` is preserved when a level-`m` residue is multiplied by a
`7`-unit scalar (as a residue mod `7^{m+1}`). -/
private theorem case62_nu_smul_top {m c e : ℕ}
    (hc : padicValNat 7 c = 0) (hc0 : c ≠ 0) (he0 : e ≠ 0)
    (helt : e < 7 ^ (m + 1)) (hν : padicValNat 7 e = m) :
    padicValNat 7 ((c * e) % 7 ^ (m + 1)) = m := by
  have : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  have heeq : e = (qdig7 m e).val * 7 ^ m := by
    have := residN_top hν
    rwa [Nat.mod_eq_of_lt helt] at this
  set u := (qdig7 m e).val with hudef
  have hu : u ≠ 0 := by
    intro h0
    rw [heeq, h0, zero_mul] at he0
    exact he0 rfl
  have hu7 : u < 7 := ZMod.val_lt _
  have hc7 : ¬ 7 ∣ c := by
    rcases padicValNat.eq_zero_iff.mp hc with h | h | h
    · norm_num at h
    · exact absurd h hc0
    · exact h
  have hcu7 : ¬ 7 ∣ c * u := by
    intro hdvd
    rcases (Nat.prime_seven.dvd_mul).mp hdvd with h | h
    · exact hc7 h
    · exact hu (Nat.eq_zero_of_dvd_of_lt h hu7)
  have hcu0 : c * u ≠ 0 := Nat.mul_ne_zero hc0 hu
  have hmod : (c * e) % 7 ^ (m + 1) = ((c * u) % 7) * 7 ^ m := by
    conv_lhs => rw [heeq]
    rw [show c * (u * 7 ^ m) = (c * u) * 7 ^ m from by ring, pow_succ',
      Nat.mul_mod_mul_right]
  rw [hmod]
  have hlt : (c * u) % 7 ≠ 0 := fun h0 => hcu7 (Nat.dvd_of_mod_eq_zero h0)
  have hlt7 : (c * u) % 7 < 7 := Nat.mod_lt _ (by norm_num)
  rw [padicValNat_mul_unit7 (Nat.pos_of_ne_zero hlt).ne'
      (pow_ne_zero m (by norm_num : (7 : ℕ) ≠ 0))
      (fun hdvd => hlt (Nat.eq_zero_of_dvd_of_lt hdvd hlt7))]
  exact padicValNat.prime_pow m

/-- `runit7` scales by `c` on level-`m` residues. -/
private theorem case62_runit_smul_top {m c e : ℕ}
    (hc : padicValNat 7 c = 0) (hc0 : c ≠ 0) (he0 : e ≠ 0)
    (helt : e < 7 ^ (m + 1)) (hν : padicValNat 7 e = m) :
    runit7 ((c * e) % 7 ^ (m + 1)) = (c : ZMod 7) * runit7 e := by
  have hν' := case62_nu_smul_top hc hc0 he0 helt hν
  rw [← qdig7_eq_runit7_of_top hν']
  rw [qdig7_congr (Nat.mod_mod _ _), qdig7_multTop hν]

/-- The scaled exact offset: `q(c·x) − q(c·y) = c·r(e(x,y))` for a
level-`m` `same`-branch difference. -/
private theorem case62_qdig_sub_smul_top {m c x y : ℕ}
    (hm : 1 ≤ m)
    (hc : padicValNat 7 c = 0) (hc0 : c ≠ 0)
    (hrel : residueRelOf x y = residueRel.same)
    (he : eMod7 m x y ≠ 0) (hν : padicValNat 7 (eMod7 m x y) = m) :
    qdig7 m (c * x) - qdig7 m (c * y) =
      (c : ZMod 7) * runit7 (eMod7 m x y) := by
  have hrc : runit7 c ≠ 0 := runit7_ne_zero (Nat.pos_of_ne_zero hc0)
  have hrl : residueRelOf (c * x) (c * y) = residueRel.same := by
    rw [residueRelOf_eq_same] at hrel ⊢
    rw [runit7_mul, runit7_mul]
    constructor
    · exact fun hcon => hrel.1 (mul_right_cancel₀ hrc (by linear_combination hcon))
    · exact fun hcon => hrel.2 (mul_right_cancel₀ hrc (by linear_combination hcon))
  have hE : eMod7 m (c * x) (c * y) = (c * eMod7 m x y) % 7 ^ (m + 1) :=
    eMod7_smul hrc
  have hν' : padicValNat 7 (eMod7 m (c * x) (c * y)) = m := by
    rw [hE]
    exact case62_nu_smul_top hc hc0 he case62_eMod7_lt hν
  have he' : eMod7 m (c * x) (c * y) ≠ 0 := by
    intro h0
    rw [h0, padicValNat.zero] at hν'
    omega
  have hqd := case62_qdig_sub_top hrl he' hν'
  rw [hqd, hE, case62_runit_smul_top hc hc0 he case62_eMod7_lt hν]

/-! ### §2 Additional small clones and finite `ZMod 7` facts -/

/-- `runit7 0 = 0` (clone of the private helper used elsewhere). -/
private theorem case62_runit7_zero : runit7 0 = 0 := by
  unfold runit7
  simp

/-- `runit7 x = 0` forces `x = 0`. -/
private theorem case62_eq_zero_of_runit7 {x : ℕ} (h : runit7 x = 0) : x = 0 := by
  rcases Nat.eq_zero_or_pos x with h0 | h0
  · exact h0
  · exact absurd h (runit7_ne_zero h0)

/-- `eMod7 m x x = 0` for positive `x`. -/
private theorem case62_eMod7_self {m x : ℕ} (hx : 0 < x) : eMod7 m x x = 0 := by
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

/-- `qdig7` of a reduced residue is the unreduced digit. -/
private theorem case62_qdig7_mod' {m w : ℕ} :
    qdig7 m (w % 7 ^ (m + 1)) = qdig7 m w :=
  qdig7_congr (Nat.mod_mod _ _)

/-- `qdig7 m 0 = 0`. -/
private theorem case62_qdig7_zero (m : ℕ) : qdig7 m 0 = 0 := by
  unfold qdig7
  simp

/-- The unique bad digit for `{0,6,q}` is `q = 3`. -/
private theorem case62_apLen_triple06 : ∀ q : ZMod 7, q ≠ 3 →
    apLen ({0, 6, q} : Finset (ZMod 7)) ≤ 4 := by
  decide

/-- A singleton digit set has `apLen ≤ 1`. -/
private theorem case62_apLen_single (a : ZMod 7) :
    apLen ({a} : Finset (ZMod 7)) ≤ 1 := by
  have hsub : ({a} : Finset (ZMod 7)) ⊆ cycIv a 1 := by
    intro x hx
    rw [Finset.mem_singleton.mp hx]
    rw [mem_cycIv]
    simp
  exact (apLen_le_iff _ _ (by norm_num : 1 ≤ 7)).mpr ⟨a, hsub⟩

/-- `{0,1,2,4}` has covering length `5` (the (ii.2) offset shape). -/
private theorem case62_apLen_0124 :
    apLen ({0, 1, 2, 4} : Finset (ZMod 7)) = 5 := by
  decide

/-- `{1,2,3,5}` has covering length `5` (translate of `{0,1,2,4}`). -/
private theorem case62_apLen_1235 :
    apLen ({1, 2, 3, 5} : Finset (ZMod 7)) = 5 := by
  decide

/-- `{1,2,3,5}` is exactly the cyclic interval of length `5` at `1`
missing `4`. -/
private theorem case62_mem_cycIv15 : ∀ q : ZMod 7,
    q ∈ ({1, 2, 3, 5} : Finset (ZMod 7)) → q ∈ cycIv 1 5 := by
  decide

/-- `{1,3,4,5}` has covering length `5` (the `{3,5,6}`-offset shape,
normalized with anchor digit `5`). -/
private theorem case62_apLen_1345 :
    apLen ({1, 3, 4, 5} : Finset (ZMod 7)) = 5 := by
  decide

/-- `{1,3,4,5} ⊆ cycIv 1 5`. -/
private theorem case62_mem_cycIv1345 : ∀ q : ZMod 7,
    q ∈ ({1, 3, 4, 5} : Finset (ZMod 7)) → q ∈ cycIv 1 5 := by
  decide

/-- `{1,2,5}` has covering length `5` (the collapsed `{0,1,4}` offset
shape). -/
private theorem case62_apLen_125 :
    apLen ({1, 2, 5} : Finset (ZMod 7)) = 5 := by
  decide

/-- `{1,2,5} ⊆ cycIv 1 5`. -/
private theorem case62_mem_cycIv125 : ∀ q : ZMod 7,
    q ∈ ({1, 2, 5} : Finset (ZMod 7)) → q ∈ cycIv 1 5 := by
  decide

/-- Three points `{a, a+1, b}` with `b − a ≠ 4` always fit a 4-interval
(the only 3-point shape needing `5` is `{a, a+1, a+4}`). -/
private theorem case62_triple_le4 : ∀ a b : ZMod 7, b - a ≠ 4 →
    apLen ({a, a + 1, b} : Finset (ZMod 7)) ≤ 4 := by
  decide

/-- `5 + {0,c,2c,4c} = {1,3,4,5}` for `c ∈ {3,5,6}` (the other
`{0,u,2u,4u}` coset). -/
private theorem case62_offsets_1345 : ∀ c : ZMod 7,
    c ∈ ({3, 5, 6} : Finset (ZMod 7)) →
    ({5, 5 + c, 5 + 2 * c, 5 + 4 * c} : Finset (ZMod 7)) = {1, 3, 4, 5} := by
  decide

/-- For `c ∈ {3,5,6}` the offset `3` is attained by exactly one of
`{c,2c,4c}`. -/
private theorem case62_offset3_mem : ∀ c : ZMod 7,
    c ∈ ({3, 5, 6} : Finset (ZMod 7)) →
    (3 : ZMod 7) ∈ ({c, 2 * c, 4 * c} : Finset (ZMod 7)) := by
  decide


/-- `eMod7 = 0` in the `twoX` branch forces `2x ≡ y (mod 7^{m+1})`. -/
private theorem case62_eq_resid_twoX {m x y : ℕ}
    (h : eMod7 m x y = 0) (hrel : runit7 y = 2 * runit7 x) :
    (2 * x) % 7 ^ (m + 1) = y % 7 ^ (m + 1) := by
  have hN : (0 : ℕ) < 7 ^ (m + 1) := Nat.pow_pos (by norm_num)
  have hx : x % 7 ^ (m + 1) < 7 ^ (m + 1) := Nat.mod_lt _ hN
  have hy : y % 7 ^ (m + 1) < 7 ^ (m + 1) := Nat.mod_lt _ hN
  have h' : (2 * (x % 7 ^ (m + 1)) + 7 ^ (m + 1) - y % 7 ^ (m + 1))
      % 7 ^ (m + 1) = 0 := by
    unfold eMod7 at h
    rwa [if_pos hrel] at h
  have hdvd : 7 ^ (m + 1) ∣
      2 * (x % 7 ^ (m + 1)) + 7 ^ (m + 1) - y % 7 ^ (m + 1) :=
    Nat.dvd_of_mod_eq_zero h'
  obtain ⟨k, hk⟩ := hdvd
  have hpos : 0 < 2 * (x % 7 ^ (m + 1)) + 7 ^ (m + 1) - y % 7 ^ (m + 1) := by
    omega
  have hlt : 2 * (x % 7 ^ (m + 1)) + 7 ^ (m + 1) - y % 7 ^ (m + 1)
      < 3 * 7 ^ (m + 1) := by omega
  have hk12 : k = 1 ∨ k = 2 := by
    rw [hk] at hpos hlt
    rcases k with _ | _ | _ | k
    · simp at hpos
    · exact Or.inl rfl
    · exact Or.inr rfl
    · have hge : 7 ^ (m + 1) * 3 ≤ 7 ^ (m + 1) * (k + 1 + 1 + 1) :=
        Nat.mul_le_mul_left _ (by omega)
      omega
  have hmul : (2 * x) % 7 ^ (m + 1) = (2 * (x % 7 ^ (m + 1))) % 7 ^ (m + 1) := by
    have h2lt : (2 : ℕ) < 7 ^ (m + 1) := by
      calc 2 < 7 := by norm_num
        _ ≤ 7 ^ (m + 1) := Nat.le_self_pow (by norm_num) 7
    rw [Nat.mul_mod, Nat.mod_eq_of_lt h2lt]
  rcases hk12 with hk1 | hk2
  · rw [hk1, mul_one] at hk
    have h2 : 2 * (x % 7 ^ (m + 1)) = y % 7 ^ (m + 1) := by omega
    rw [hmul, h2, Nat.mod_eq_of_lt hy]
  · rw [hk2] at hk
    have h2 : 2 * (x % 7 ^ (m + 1)) = y % 7 ^ (m + 1) + 7 ^ (m + 1) := by
      omega
    rw [hmul, h2, Nat.add_mod_right, Nat.mod_eq_of_lt hy]

/-- Two digits at distance `0` or `1` fit a 2-interval. -/
private theorem case62_pair01 : ∀ a b : ZMod 7,
    b - a ∈ ({0, 1} : Finset (ZMod 7)) →
    apLen ({a, b} : Finset (ZMod 7)) ≤ 2 := by
  decide

/-- `apLen {2,3} ≤ 4` (for `case62_avoid`). -/
private theorem case62_apLen_23 : apLen ({2, 3} : Finset (ZMod 7)) ≤ 4 := by
  decide

/-- `apLen {4,6} ≤ 4`. -/
private theorem case62_apLen_46 : apLen ({4, 6} : Finset (ZMod 7)) ≤ 4 := by
  decide

/-- `apLen {3,4} ≤ 4`. -/
private theorem case62_apLen_34 : apLen ({3, 4} : Finset (ZMod 7)) ≤ 4 := by
  decide

/-- `apLen {0,2} ≤ 4`. -/
private theorem case62_apLen_02 : apLen ({0, 2} : Finset (ZMod 7)) ≤ 4 := by
  decide

/-- Every nonzero residue has a `{1,2,4}`-stabilizer image inside
`{4,5,6}` (the `{0,2}`-avoidance stabilizer). -/
private theorem case62_stab02 : ∀ r : ZMod 7, r ≠ 0 →
    ∃ c : ZMod 7, c ∈ ({1, 2, 4} : Finset (ZMod 7)) ∧
      c * r ∉ ({0, 1, 2, 3} : Finset (ZMod 7)) := by decide

/-- Every nonzero residue has a `{1,2,4}`-stabilizer image inside
`{1,2,6}` (the `{3,4}`-avoidance stabilizer). -/
private theorem case62_stab34 : ∀ r : ZMod 7, r ≠ 0 →
    ∃ c : ZMod 7, c ∈ ({1, 2, 4} : Finset (ZMod 7)) ∧
      c * r ∉ ({3, 4, 5} : Finset (ZMod 7)) := by decide

/-- `{1,2,4}` is closed under multiplication. -/
private theorem case62_mul_124 : ∀ u c : ZMod 7,
    u ∈ ({1, 2, 4} : Finset (ZMod 7)) →
    c ∈ ({1, 2, 4} : Finset (ZMod 7)) →
    u * c ∈ ({1, 2, 4} : Finset (ZMod 7)) := by decide

/-- `{3,5,6}` is closed under `{1,2,4}`-multiplication. -/
private theorem case62_mul_356 : ∀ u c : ZMod 7,
    u ∈ ({1, 2, 4} : Finset (ZMod 7)) →
    c ∈ ({3, 5, 6} : Finset (ZMod 7)) →
    u * c ∈ ({3, 5, 6} : Finset (ZMod 7)) := by decide

/-- For `u ∈ {1,2,4}` and `c₀ ∈ {3,5,6}` there is `v ∈ {c₀,2c₀,4c₀}`
with `u·v = 3`. -/
private theorem case62_offset3u : ∀ u c : ZMod 7,
    u ∈ ({1, 2, 4} : Finset (ZMod 7)) →
    c ∈ ({3, 5, 6} : Finset (ZMod 7)) →
    ∃ v : ZMod 7, v ∈ ({c, 2 * c, 4 * c} : Finset (ZMod 7)) ∧
      u * v = 3 := by decide

/-- `{0,1,w}` has `apLen ≤ 4` unless `w = 4` (then it is `5`). -/
private theorem case62_apLen_01w : ∀ w : ZMod 7, w ≠ 4 →
    apLen ({0, 1, w} : Finset (ZMod 7)) ≤ 4 := by
  decide

/-- `{0,1,2}` has `apLen ≤ 4`. -/
private theorem case62_apLen_012 : apLen ({0, 1, 2} : Finset (ZMod 7)) ≤ 4 := by
  decide

/-- `v / u = 4` when `v = 4u`. -/
private theorem case62_div_four {u v : ZMod 7} (hu : u ≠ 0) (hv : v = 4 * u) :
    v * u⁻¹ = 4 := by
  rw [hv]
  have h : (4 : ZMod 7) * u * u⁻¹ = 4 * (u * u⁻¹) := by ring
  rw [h, mul_inv_cancel₀ hu, mul_one]

/-- `ẽ ∉ {0,2}` pulls back to `ẽ − 3 ∉ {4,6}`. -/
private theorem case62_shift02 : ∀ z : ZMod 7,
    z ∉ ({0, 2} : Finset (ZMod 7)) →
    z - 3 ∉ ({4, 6} : Finset (ZMod 7)) := by
  decide

/-- `ẽ ∉ {3,4}` pushes forward to `ẽ + 6 ∉ {2,3}`. -/
private theorem case62_shift34 : ∀ z : ZMod 7,
    z ∉ ({3, 4} : Finset (ZMod 7)) →
    z + 6 ∉ ({2, 3} : Finset (ZMod 7)) := by
  decide

/-- For distinct nonzero `u, v : ZMod 7` one of the ratio alternatives
`v = 2u | 3u`, `u = 2v | 3v`, or `v = −u` holds. -/
private theorem case62_ratio_pairs : ∀ u v : ZMod 7,
    u ≠ 0 → v ≠ 0 → u ≠ v →
    v = 2 * u ∨ v = 3 * u ∨ u = 2 * v ∨ u = 3 * v ∨ v = -u := by
  decide

/-- A nonempty digit set has positive `apLen`. -/
private theorem case62_apLen_pos {X : Finset (ZMod 7)} (hne : X.Nonempty) :
    0 < apLen X := by
  by_contra h
  push_neg at h
  have h0 : apLen X = 0 := Nat.eq_zero_of_le_zero h
  obtain ⟨i, hi⟩ := (apLen_le_iff X 0 (Nat.zero_le 7)).mp (le_of_eq h0)
  rw [cycIv_zero] at hi
  exact hne.ne_empty (Finset.subset_empty.mp hi)

/-- The ×2 carry bound: `q(2x) ∈ {2q(x), 2q(x)+1}`. -/
private theorem case62_carry2 {m x : ℕ} :
    qdig7 m (2 * x) ∈
      ({2 * qdig7 m x, 2 * qdig7 m x + 1} : Finset (ZMod 7)) := by
  have hv := qdig7_smul_carry (m := m) (c := 2) (x := x) (by norm_num)
    (by norm_num)
  set z := qdig7 m (2 * x) - 2 * qdig7 m x with hz
  have hzv : z.val < 2 := hv
  have hz0 : z = 0 ∨ z = 1 := by
    have hc : z = (z.val : ZMod 7) := (ZMod.natCast_zmod_val z).symm
    have h2 : z.val = 0 ∨ z.val = 1 := by omega
    rcases h2 with h | h
    · left; rw [hc, h]; decide
    · right; rw [hc, h]; decide
  rcases hz0 with h0 | h0
  · rw [sub_eq_zero.mp h0]
    exact Finset.mem_insert.mpr (Or.inl rfl)
  · have hq : qdig7 m (2 * x) = 2 * qdig7 m x + 1 := by
      have := sub_eq_iff_eq_add.mp h0
      rw [this]; ring
    rw [hq]
    exact Finset.mem_insert.mpr
      (Or.inr (Finset.mem_singleton.mpr rfl))

/-- Membership of `q(2x)` in `{2q, 2q+1}` — set form used for images. -/
private theorem case62_mem0156 {z : ZMod 7}
    (hz : z ∈ ({0, 6, 3} : Finset (ZMod 7))) {w : ZMod 7}
    (hw : w ∈ ({2 * z, 2 * z + 1} : Finset (ZMod 7))) :
    w ∈ ({0, 1, 5, 6} : Finset (ZMod 7)) := by
  revert z w hz hw
  decide

/-- `2 * runit7` maps the class set `{s,2s,4s}` to `{2s,4s,s}`. -/
private theorem case62_rot_classes {s : ZMod 7} :
    ({2 * s, 4 * s, 8 * s} : Finset (ZMod 7)) =
      ({2 * s, 4 * s, s} : Finset (ZMod 7)) := by
  have h8 : (8 : ZMod 7) = 1 := by decide
  ext x
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (h | h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · rw [h8, one_mul] at h
      exact Or.inr (Or.inr h)
  · rintro (h | h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · rw [h, h8, one_mul]
      exact Or.inr (Or.inr rfl)

/-- Filter elements are in `A`. -/
private theorem case62_filter_subset {A : Finset ℕ} {p : ℕ → Prop}
    [DecidablePred p] : A.filter p ⊆ A := Finset.filter_subset p A

/-- `good7` composition through an image (`good7_mul` with the `fun`
spelling used here). -/
private theorem case62_good7_of_image {m lam0 lam' : ℕ} {A : Finset ℕ}
    (h : good7 m lam0 (A.image (fun d => lam' * d))) :
    good7 m (lam0 * lam') A :=
  good7_mul h

/-! ### §4 `ẽ`-avoidance with the multiplier pinned to `lam % 7 = 1`

These are verbatim clones of `lemma7_i`/`lemma7_ii` with the extra
conjunct `lam % 7 = 1`, which the later offset-preservation step needs
(the `∃`-conclusions of the public lemmas hide the multiplier shape). -/

/-- Lemma 7(i) plus `lam % 7 = 1`. -/
private theorem case62_avoid {m d d' : ℕ}
    (hd : padicValNat 7 d = 0) (hd' : padicValNat 7 d' = 0)
    (hpos : 0 < d) (hpos' : 0 < d')
    (hrel : runit7 d' = 2 * runit7 d)
    (hν : 0 < padicValNat 7 (eMod7 m d d'))
    (hνm : padicValNat 7 (eMod7 m d d') < m)
    {X : Finset (ZMod 7)} (hX : apLen X ≤ 4) :
    ∃ lam : ℕ, ¬ 7 ∣ lam ∧ lam % 7 = 1 ∧
      etd7 m (lam * d) (lam * d') ∉ X := by
  set e := eMod7 m d d' with he
  have he0 : e ≠ 0 := by
    intro h0
    rw [h0] at hν
    simp at hν
  obtain ⟨x, hx⟩ := exists_not_mem_three hX
  obtain ⟨k, hk7, hkq⟩ := exists_multLow_set_qdig hνm rfl he0 (x - 1)
  refine ⟨1 + k * 7 ^ (m - padicValNat 7 e), multLow_not_dvd hνm,
    multLow_mod7 hνm, ?_⟩
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

/-- Lemma 7(ii) plus `lam % 7 = 1`. -/
private theorem case62_avoid_top {m : ℕ} (hm : 2 ≤ m) {d d' : ℕ}
    (hd : padicValNat 7 d = 0) (hd' : padicValNat 7 d' = 0)
    (hpos : 0 < d) (hpos' : 0 < d')
    (hrel : runit7 d' = 2 * runit7 d)
    (hν : padicValNat 7 (eMod7 m d d') = m)
    {X : Finset (ZMod 7)}
    (hr : runit7 (eMod7 m d d') ∉ X ∪ X.image (· + 1)) :
    ∃ lam : ℕ, ¬ 7 ∣ lam ∧ lam % 7 = 1 ∧
      etd7 m (lam * d) (lam * d') ∉ X := by
  set e := eMod7 m d d' with he
  have h1m : 1 < m := by omega
  obtain ⟨k, hk7, hkq⟩ :=
    exists_multLow_one_set_seven' (by omega : 0 < m) hd hpos 6
  refine ⟨1 + k * 7 ^ (m - 1), multLow_not_dvd h1m, multLow_mod7 h1m, ?_⟩
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

/-- `e = 0` with the low digit killed: `ẽ = 0` exactly.

A `Λ₁`-multiplier `λ = 1 + k·7^{m-1}` can set `digit7 (m-1) (λx) = 0`,
so `(λx) % 7^m < 7^{m-1}`; then `2·((λx)%N) < 2·7^m + 7^m` produces no
borrow and `(λy)%N` is its verbatim double. -/
private theorem case62_avoid_zero {m : ℕ} (hm : 2 ≤ m) {x y : ℕ}
    (hx : padicValNat 7 x = 0) (hy : padicValNat 7 y = 0)
    (hxp : 0 < x)
    (hrel : runit7 y = 2 * runit7 x)
    (he : eMod7 m x y = 0) :
    ∃ lam : ℕ, ¬ 7 ∣ lam ∧ lam % 7 = 1 ∧
      etd7 m (lam * x) (lam * y) = 0 := by
  have h1m : 1 ≤ m := by omega
  have h0m : 0 < m := by omega
  have h1lt : 1 < m := by omega
  have hrx : runit7 x ≠ 0 := runit7_ne_zero hxp
  have hd0 : digit7 0 x = runit7 x := by
    unfold digit7
    rw [pow_zero, Nat.div_one, runit7_of_padic_zero hx]
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr (Nat.mod_mod x 7)
  obtain ⟨k, hk7, hk⟩ : ∃ k : ℕ, k < 7 ∧
      digit7 (m - 1) x + (k : ZMod 7) * digit7 0 x = 0 := by
    have hex : ∀ u : ZMod 7, u ≠ 0 → ∃ v : ZMod 7, v * u = 1 := by decide
    obtain ⟨v, hv⟩ := hex _ (hd0 ▸ hrx)
    refine ⟨((-(digit7 (m - 1) x)) * v).val, ZMod.val_lt _, ?_⟩
    rw [ZMod.natCast_zmod_val, mul_assoc, hv, mul_one, add_neg_cancel]
  have h1' := (digit7_multLow_one (m := m) (k := k) (x := x) h1m).1
  set lam := 1 + k * 7 ^ (m - 1) with hlam
  have hlamr : runit7 lam = 1 := runit7_multLow h1lt
  have hlamnd : ¬ 7 ∣ lam := multLow_not_dvd h1lt
  have hlam7 : lam % 7 = 1 := multLow_mod7 h1lt
  refine ⟨lam, hlamnd, hlam7, ?_⟩
  have hdig : digit7 (m - 1) (lam * x) = 0 := by
    rw [h1', hk]
  -- `f := (λx) % 7^m` has top digit `0`, so `f = (λx) % 7^{m-1} < 7^{m-1}`
  have hf : (lam * x) % 7 ^ m < 7 ^ (m - 1) := by
    have hcast : ((lam * x) / 7 ^ (m - 1)) % 7 = 0 := by
      have hz : digit7 (m - 1) (lam * x) = 0 := hdig
      unfold digit7 at hz
      have hdvd : 7 ∣ (lam * x) / 7 ^ (m - 1) % 7 :=
        (ZMod.natCast_eq_zero_iff _ _).mp hz
      exact Nat.eq_zero_of_dvd_of_lt hdvd (Nat.mod_lt _ (by norm_num))
    have hm1 : (7 : ℕ) ^ m = 7 * 7 ^ (m - 1) := by
      rw [← pow_succ']; congr 1; omega
    have hsplit : (lam * x) % 7 ^ m =
        7 ^ (m - 1) * ((lam * x) % 7 ^ m / 7 ^ (m - 1)) +
          (lam * x) % 7 ^ m % 7 ^ (m - 1) :=
      (Nat.div_add_mod _ _).symm
    have heq : (lam * x) % 7 ^ m = (lam * x) % 7 ^ (m - 1) := by
      rw [hsplit, Nat.mod_mod_of_dvd _
        (pow_dvd_pow 7 (by omega : m - 1 ≤ m)), hm1,
        Nat.mod_mul_left_div_self, hcast, mul_zero, zero_add]
    rw [heq]
    exact Nat.mod_lt _ (Nat.pow_pos (by norm_num))
  have hpow2 : 2 * 7 ^ (m - 1) ≤ 7 ^ m := by
    have h7 : 7 ^ m = 7 * 7 ^ (m - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [h7]
    exact Nat.mul_le_mul_right _ (by norm_num : (2 : ℕ) ≤ 7)
  -- residues of the scaled pair
  have hrlx : runit7 (lam * x) = runit7 x := by
    rw [runit7_mul, hlamr, one_mul]
  have hif : runit7 (lam * y) = 2 * runit7 (lam * x) := by
    rw [runit7_mul, hlamr, one_mul, hrel, hrlx]
  have he' : eMod7 m (lam * x) (lam * y) = 0 := by
    have h := eMod7_mul (m := m) hlamr (x := x) (y := y)
    rw [he, mul_zero, Nat.zero_mod] at h
    exact h
  -- `Y' ≡ 2·X' (mod N)` from `e' = 0` (twoX branch)
  have hrel' : 2 * ((lam * x) % 7 ^ (m + 1)) % 7 ^ (m + 1)
      = (lam * y) % 7 ^ (m + 1) := by
    unfold eMod7 at he'
    rw [if_pos hif] at he'
    have h0 : (2 * ((lam * x) % 7 ^ (m + 1)) + 7 ^ (m + 1)
        - (lam * y) % 7 ^ (m + 1)) % 7 ^ (m + 1) = 0 := he'
    have hdvd : 7 ^ (m + 1) ∣ 2 * ((lam * x) % 7 ^ (m + 1)) + 7 ^ (m + 1)
        - (lam * y) % 7 ^ (m + 1) := Nat.dvd_of_mod_eq_zero h0
    have hylt : (lam * y) % 7 ^ (m + 1) < 7 ^ (m + 1) :=
      Nat.mod_lt _ (Nat.pow_pos (by norm_num))
    have hx' : (lam * x) % 7 ^ (m + 1) < 7 ^ (m + 1) :=
      Nat.mod_lt _ (Nat.pow_pos (by norm_num))
    have hle : (lam * y) % 7 ^ (m + 1)
        ≤ 2 * ((lam * x) % 7 ^ (m + 1)) + 7 ^ (m + 1) := by omega
    obtain ⟨t, ht⟩ := hdvd
    -- `N ∣ (2X' + N − Y')` gives `Y' ≡ 2X' + N ≡ 2X' (mod N)`.
    have hmod : (lam * y) % 7 ^ (m + 1)
        ≡ 2 * ((lam * x) % 7 ^ (m + 1)) + 7 ^ (m + 1) [MOD 7 ^ (m + 1)] := by
      rw [Nat.modEq_iff_dvd]
      refine ⟨(t : ℤ), ?_⟩
      rw [← Nat.cast_sub hle, ht]
      push_cast
      ring
    have hmod' : ((lam * y) % 7 ^ (m + 1)) % 7 ^ (m + 1)
        = (2 * ((lam * x) % 7 ^ (m + 1)) + 7 ^ (m + 1)) % 7 ^ (m + 1) := hmod
    rw [Nat.mod_eq_of_lt hylt, Nat.add_mod_right] at hmod'
    exact hmod'.symm
  -- `Y' = (2X')%N` forces `q(λy) = 2·q(λx)`
  set X' := (lam * x) % 7 ^ (m + 1) with hX'
  set q5 := X' / 7 ^ m with hq5
  have hXdec : X' = q5 * 7 ^ m + (lam * x) % 7 ^ m := by
    have h1 : X' = 7 ^ m * (X' / 7 ^ m) + X' % 7 ^ m :=
      (Nat.div_add_mod _ _).symm
    have h2 : X' % 7 ^ m = (lam * x) % 7 ^ m := by
      rw [hX']
      exact Nat.mod_mod_of_dvd _ (pow_dvd_pow 7 (by omega : m ≤ m + 1))
    rw [h2, ← hq5, mul_comm (7 ^ m) q5] at h1
    exact h1
  have hYeq : (lam * y) % 7 ^ (m + 1)
      = (2 * q5 % 7) * 7 ^ m + 2 * ((lam * x) % 7 ^ m) := by
    have h2f : 2 * ((lam * x) % 7 ^ m) < 7 ^ m := by omega
    have hlt : (2 * q5 % 7) * 7 ^ m + 2 * ((lam * x) % 7 ^ m)
        < 7 ^ (m + 1) := by
      have h1 : (2 * q5 % 7) * 7 ^ m ≤ 6 * 7 ^ m := by
        have hmod6 : 2 * q5 % 7 ≤ 6 := by
          have := Nat.mod_lt (2 * q5) (show (0 : ℕ) < 7 by norm_num)
          omega
        exact Nat.mul_le_mul_right _ hmod6
      have h2 : 7 ^ (m + 1) = 7 * 7 ^ m := pow_succ' 7 m
      omega
    rw [← hrel', hXdec]
    have hdecomp : 2 * (q5 * 7 ^ m + (lam * x) % 7 ^ m)
        = (2 * q5 % 7) * 7 ^ m + 2 * ((lam * x) % 7 ^ m)
          + (2 * q5 / 7) * 7 ^ (m + 1) := by
      have hsplit : 2 * q5 = (2 * q5 % 7) + 7 * (2 * q5 / 7) :=
        (Nat.mod_add_div _ _).symm
      have h7m : 7 ^ (m + 1) = 7 * 7 ^ m := pow_succ' 7 m
      calc 2 * (q5 * 7 ^ m + (lam * x) % 7 ^ m)
          = (2 * q5) * 7 ^ m + 2 * ((lam * x) % 7 ^ m) := by ring
        _ = ((2 * q5 % 7) + 7 * (2 * q5 / 7)) * 7 ^ m
              + 2 * ((lam * x) % 7 ^ m) := by conv_lhs => rw [hsplit]
        _ = (2 * q5 % 7) * 7 ^ m + 7 * (2 * q5 / 7) * 7 ^ m
              + 2 * ((lam * x) % 7 ^ m) := by ring
        _ = (2 * q5 % 7) * 7 ^ m + 2 * ((lam * x) % 7 ^ m)
              + (2 * q5 / 7) * 7 ^ (m + 1) := by
            rw [h7m]; ring
    rw [hdecomp, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlt]
  have hqy2 : ((lam * y) % 7 ^ (m + 1)) / 7 ^ m = 2 * q5 % 7 := by
    rw [hYeq]
    have h2f : 2 * ((lam * x) % 7 ^ m) < 7 ^ m := by omega
    have hP : 0 < 7 ^ m := Nat.pow_pos (by norm_num)
    rw [add_comm ((2 * q5 % 7) * 7 ^ m) _, mul_comm (2 * q5 % 7) (7 ^ m),
      Nat.add_mul_div_left _ _ hP, Nat.div_eq_of_lt h2f, zero_add]
  have hqxeq : qdig7 m (lam * x) = (q5 : ZMod 7) := rfl
  have hqyeq : qdig7 m (lam * y) = 2 * (q5 : ZMod 7) := by
    show (((lam * y) % 7 ^ (m + 1) / 7 ^ m : ℕ) : ZMod 7)
        = 2 * (q5 : ZMod 7)
    rw [hqy2, (ZMod.natCast_eq_natCast_iff _ _ _).mpr (Nat.mod_mod _ _),
      Nat.cast_mul, Nat.cast_ofNat]
  unfold etd7
  rw [if_pos hif, hqxeq, hqyeq]
  ring

/-- For `e = 0` (the `twoX` degenerate pair), a `Λ₁`-multiplier can force
the `×2` carry `q(7λx) = 6`, giving `ẽ = 6` exactly. -/
private theorem case62_avoid_zero_carry {m : ℕ} (hm : 2 ≤ m) {x y : ℕ}
    (hx : padicValNat 7 x = 0) (hy : padicValNat 7 y = 0)
    (hxp : 0 < x) (hyp : 0 < y)
    (hrel : runit7 y = 2 * runit7 x)
    (he : eMod7 m x y = 0) :
    ∃ lam : ℕ, ¬ 7 ∣ lam ∧ lam % 7 = 1 ∧
      etd7 m (lam * x) (lam * y) = 6 := by
  have h1m : 1 < m := by omega
  obtain ⟨k, hk7, hkd⟩ :=
    exists_multLow_one_set_seven' (by omega : 0 < m) hx hxp (6 : ZMod 7)
  set lam := 1 + k * 7 ^ (m - 1) with hlam
  have hlamr : runit7 lam = 1 := runit7_multLow h1m
  have hlamnd : ¬ 7 ∣ lam := multLow_not_dvd h1m
  have hlam7 : lam % 7 = 1 := multLow_mod7 h1m
  refine ⟨lam, hlamnd, hlam7, ?_⟩
  have h7x : qdig7 m (7 * (lam * x)) = 6 := by
    have e' : 7 * (lam * x) = lam * (7 * x) := by ring
    rw [e']; exact hkd
  have h2x : qdig7 m (2 * (lam * x)) = 2 * qdig7 m (lam * x) + 1 :=
    qdig7_two_eq_smul_add_one (by omega : 0 < m) h7x
  have hrlx : runit7 (lam * x) = runit7 x := by
    rw [runit7_mul, hlamr, one_mul]
  have hif : runit7 (lam * y) = 2 * runit7 (lam * x) := by
    rw [runit7_mul, hlamr, one_mul, hrel, hrlx]
  have he' : eMod7 m (lam * x) (lam * y) = 0 := by
    rw [eMod7_mul hlamr, he, mul_zero, Nat.zero_mod]
  have hres : (2 * (lam * x)) % 7 ^ (m + 1) = (lam * y) % 7 ^ (m + 1) :=
    case62_eq_resid_twoX he' hif
  have hqy : qdig7 m (lam * y) = qdig7 m (2 * (lam * x)) :=
    (qdig7_congr hres).symm
  have het : etd7 m (lam * x) (lam * y)
      = 2 * qdig7 m (lam * x) - qdig7 m (lam * y) := by
    unfold etd7
    rw [if_pos hif]
  rw [het, hqy, h2x]
  have h6 : (6 : ZMod 7) = -1 := by decide
  rw [h6]
  ring

/-- The `e ≠ 0` core of the `λ₂` dispatcher. -/
private theorem case62_lam2_avoid_pos {m : ℕ} (hm : 2 ≤ m) {x y : ℕ}
    (hx : padicValNat 7 x = 0) (hy : padicValNat 7 y = 0)
    (hposx : 0 < x) (hposy : 0 < y)
    (hrel : runit7 y = 2 * runit7 x)
    (he0 : eMod7 m x y ≠ 0)
    {X : Finset (ZMod 7)} (hX : apLen X ≤ 4)
    (hstab : ∀ r : ZMod 7, r ≠ 0 →
      ∃ c : ZMod 7, c ∈ ({1, 2, 4} : Finset (ZMod 7)) ∧
        c * r ∉ X ∪ X.image (· + 1)) :
    ∃ lam : ℕ, ¬ 7 ∣ lam ∧ ∃ u : ZMod 7,
      u ∈ ({1, 2, 4} : Finset (ZMod 7)) ∧ runit7 lam = u ∧
      etd7 m (lam * x) (lam * y) ∉ X := by
  set e := eMod7 m x y with hedef
  have h7e : 7 ∣ e := case62_dvd7_twoX hx hy hrel
  have hνpos : 0 < padicValNat 7 e := by
    rcases Nat.eq_zero_or_pos (padicValNat 7 e) with h0 | h0
    · rcases padicValNat.eq_zero_iff.mp h0 with hp1 | h0e | hnd
      · norm_num at hp1
      · exact absurd h0e he0
      · exact absurd h7e hnd
    · exact h0
  have hνle : padicValNat 7 e ≤ m := enu7_le_of_ne he0
  rcases lt_or_eq_of_le hνle with hlt | heq
  · obtain ⟨lam, hnd, hm7, hav⟩ :=
      case62_avoid hx hy hposx hposy hrel hνpos hlt hX
    exact ⟨lam, hnd, 1, Finset.mem_insert_self _ _,
      runit7_eq_one_of_mod7 hm7, hav⟩
  · by_cases hr : runit7 e ∉ X ∪ X.image (· + 1)
    · obtain ⟨lam, hnd, hm7, hav⟩ :=
        case62_avoid_top hm hx hy hposx hposy hrel heq hr
      exact ⟨lam, hnd, 1, Finset.mem_insert_self _ _,
        runit7_eq_one_of_mod7 hm7, hav⟩
    · push_neg at hr
      obtain ⟨cZ, hcZmem, hcav⟩ :=
        hstab (runit7 e) (runit7_ne_zero (Nat.pos_of_ne_zero he0))
      set c := cZ.val with hcdef
      have hcZ0 : cZ ≠ 0 := by
        intro h0; rw [h0] at hcZmem; exact absurd hcZmem (by decide)
      have hcpos : 0 < c :=
        Nat.pos_of_ne_zero (by rwa [hcdef, Ne, ZMod.val_eq_zero])
      have hc7 : ¬ 7 ∣ c := fun hd =>
        hcZ0 ((ZMod.val_eq_zero cZ).mp (Nat.eq_zero_of_dvd_of_lt hd
          (ZMod.val_lt _)))
      have hνc : padicValNat 7 c = 0 := padicValNat.eq_zero_of_not_dvd hc7
      have hrc : runit7 c = cZ := by
        rw [case62_runit7_eq_cast hνc, hcdef, ZMod.natCast_zmod_val]
      have hcx0 : padicValNat 7 (c * x) = 0 := by
        rw [padicValNat_mul_seven hc7 (ne_of_gt hposx)]; exact hx
      have hcy0 : padicValNat 7 (c * y) = 0 := by
        rw [padicValNat_mul_seven hc7 (ne_of_gt hposy)]; exact hy
      have hcposx : 0 < c * x := Nat.mul_pos hcpos hposx
      have hcposy : 0 < c * y := Nat.mul_pos hcpos hposy
      have hrel' : runit7 (c * y) = 2 * runit7 (c * x) := by
        rw [runit7_mul, runit7_mul, hrc, hrel]; ring
      have hE : eMod7 m (c * x) (c * y) = (c * e) % 7 ^ (m + 1) :=
        eMod7_smul (hrc ▸ hcZ0)
      have hν' : padicValNat 7 (eMod7 m (c * x) (c * y)) = m := by
        rw [hE]
        exact case62_nu_smul_top hνc (ne_of_gt hcpos) he0 case62_eMod7_lt
          heq
      have hr' : runit7 (eMod7 m (c * x) (c * y))
          ∉ X ∪ X.image (· + 1) := by
        rw [hE, case62_runit_smul_top hνc (ne_of_gt hcpos) he0
          case62_eMod7_lt heq, hcdef, ZMod.natCast_zmod_val]
        exact hcav
      obtain ⟨lam', hnd', hm7', hav'⟩ :=
        case62_avoid_top hm hcx0 hcy0 hcposx hcposy hrel' hν' hr'
      refine ⟨lam' * c, Nat.prime_seven.not_dvd_mul hnd' hc7, cZ, hcZmem,
        ?_, ?_⟩
      · rw [runit7_mul, runit7_eq_one_of_mod7 hm7', one_mul, hrc]
      · rwa [← mul_assoc lam' c x, ← mul_assoc lam' c y] at hav'

/-- **λ₂ dispatcher**: for a `twoX` pair `(x, y)` and an `apLen ≤ 4` digit
set `X` closed against `0`, find a `Λ`-type multiplier `lam` (unit
`u ∈ {1,2,4}`) with `ẽ(lam·x, lam·y) ∉ X`.  The case split is: `e = 0`
(`case62_avoid_zero`), `0 < ν(e) < m` (`case62_avoid`), `ν(e) = m` with
`r(e)` directly avoidable (`case62_avoid_top`), and `ν(e) = m` with `r(e)`
bad — rescale the pair by `c ∈ {1,2,4}` so that `c·r(e)` is avoidable
(`case62_avoid_top` on the scaled pair, unit `u = c`). -/
private theorem case62_lam2_avoid' {m : ℕ} (hm : 2 ≤ m) {x y : ℕ}
    (hx : padicValNat 7 x = 0) (hy : padicValNat 7 y = 0)
    (hposx : 0 < x) (hposy : 0 < y)
    (hrel : runit7 y = 2 * runit7 x)
    {X : Finset (ZMod 7)} (hX : apLen X ≤ 4) (h0X : (0 : ZMod 7) ∉ X)
    (hstab : ∀ r : ZMod 7, r ≠ 0 →
      ∃ c : ZMod 7, c ∈ ({1, 2, 4} : Finset (ZMod 7)) ∧
        c * r ∉ X ∪ X.image (· + 1)) :
    ∃ lam : ℕ, ¬ 7 ∣ lam ∧ ∃ u : ZMod 7,
      u ∈ ({1, 2, 4} : Finset (ZMod 7)) ∧ runit7 lam = u ∧
      etd7 m (lam * x) (lam * y) ∉ X := by
  by_cases he0 : eMod7 m x y = 0
  · obtain ⟨lam, hnd, hm7, hav⟩ :=
      case62_avoid_zero hm hx hy hposx hrel he0
    exact ⟨lam, hnd, 1, Finset.mem_insert_self _ _,
      runit7_eq_one_of_mod7 hm7, hav ▸ h0X⟩
  · exact case62_lam2_avoid_pos hm hx hy hposx hposy hrel he0 hX hstab

/-! ### §5 The `lemma5` tail: prepare + finish -/

/-- For `s ≠ 0`, the marker `s` is not in its own `{2s,4s}` class set. -/
private theorem case62_cls_ne : ∀ s : ZMod 7, s ≠ 0 →
    s ∉ ({2 * s, 4 * s} : Finset (ZMod 7)) := by
  decide

/-- Membership in the five-element cover with a class restriction. -/
private theorem case62_cover5 {d d1 d2 d3 d4 d5 : ℕ}
    (hcover : d ∈ ({d1, d2, d3, d4, d5} : Finset ℕ)) :
    d = d1 ∨ d = d2 ∨ d = d3 ∨ d = d4 ∨ d = d5 := by
  rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert,
    Finset.mem_insert, Finset.mem_singleton] at hcover
  exact hcover

/-- Membership in the four-element cover. -/
private theorem case62_cover4 {d d1 d2 d3 d4 : ℕ}
    (hcover : d ∈ ({d1, d2, d3, d4} : Finset ℕ)) :
    d = d1 ∨ d = d2 ∨ d = d3 ∨ d = d4 := by
  rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert,
    Finset.mem_singleton] at hcover
  exact hcover

/-- Membership in the three-element cover. -/
private theorem case62_cover3 {d b1 b2 b3 : ℕ}
    (hcover : d ∈ ({b1, b2, b3} : Finset ℕ)) :
    d = b1 ∨ d = b2 ∨ d = b3 := by
  rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hcover
  exact hcover

/-- **Prepare**: given a set `A` whose elements are `d5`-or-`s`-class with
`d5` in `{2s,4s}`, and a scalar `c`, build the `lemma5` inputs for the
scaled set `B = c·A`: the `s₂`-class image lands in a `≤4`-apLen set `Q`,
each of the `{2s₂,4s₂}` classes is a `≤1`-singleton (only `c·d5` can
land there), and exactly one of them is inhabited. -/
private theorem case62_prepare {m : ℕ} {A : Finset ℕ} {c : ℕ}
    (hcpos : 0 < c) {s : ZMod 7} (hs : s ≠ 0)
    {d5 : ℕ} (hd5 : d5 ∈ A)
    (hd5cls : runit7 d5 ∈ ({2 * s, 4 * s} : Finset (ZMod 7)))
    (hother : ∀ d ∈ A, d = d5 ∨ runit7 d = s)
    (hne : ∃ d ∈ A, runit7 d = s)
    {Q : Finset (ZMod 7)} (hQcard : apLen Q ≤ 4)
    (hQ : ∀ d ∈ A, runit7 d = s → qdig7 m (c * d) ∈ Q) :
    ∃ s₂ : ZMod 7, s₂ ≠ 0 ∧
      (∀ d' ∈ A.image (fun d => c * d), runit7 d' ∈
        ({s₂, 2 * s₂, 4 * s₂} : Finset (ZMod 7))) ∧
      apLen (Finset.image (qdig7 m)
          ((A.image (fun d => c * d)).filter fun d' => runit7 d' = s₂)) ≤ 4 ∧
      apLen (Finset.image (qdig7 m)
          ((A.image (fun d => c * d)).filter fun d' => runit7 d' = 2 * s₂)) ≤ 1 ∧
      apLen (Finset.image (qdig7 m)
          ((A.image (fun d => c * d)).filter fun d' => runit7 d' = 4 * s₂)) ≤ 1 ∧
      ((A.image (fun d => c * d)).filter fun d' => runit7 d' = s₂).Nonempty ∧
      (((A.image (fun d => c * d)).filter fun d' => runit7 d' = 2 * s₂) = ∅ ∨
        ((A.image (fun d => c * d)).filter fun d' => runit7 d' = 4 * s₂)
          = ∅) := by
  classical
  set s₂ := runit7 c * s with hs₂
  have hc0 : runit7 c ≠ 0 := runit7_ne_zero hcpos
  have hs₂0 : s₂ ≠ 0 := mul_ne_zero hc0 hs
  set B := A.image (fun d => c * d) with hB
  -- key cancellation: `r(c·d) = a·s₂` forces `r(d) = a·s`.
  have hcancel : ∀ d : ℕ, ∀ a : ZMod 7,
      runit7 (c * d) = a * s₂ → runit7 d = a * s := by
    intro d a h
    have h1 : runit7 c * runit7 d = runit7 c * (a * s) := by
      have h2 : runit7 (c * d) = runit7 c * (a * s) := by
        rw [h, hs₂]; ring
      rwa [runit7_mul] at h2
    exact mul_left_cancel₀ hc0 h1
  refine ⟨s₂, hs₂0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- hcls: every scaled element lands in `{s₂, 2s₂, 4s₂}`
    intro d' hd'
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hd'
    rcases hother d hd with rfl | hrs
    · rcases Finset.mem_insert.mp hd5cls with h | h
      · rw [runit7_mul, h]
        have : runit7 c * (2 * s) = 2 * s₂ := by rw [hs₂]; ring
        rw [this]
        exact Finset.mem_insert.mpr
          (Or.inr (Finset.mem_insert.mpr (Or.inl rfl)))
      · rw [runit7_mul, Finset.mem_singleton.mp h]
        have : runit7 c * (4 * s) = 4 * s₂ := by rw [hs₂]; ring
        rw [this]
        exact Finset.mem_insert.mpr
          (Or.inr (Finset.mem_insert.mpr
            (Or.inr (Finset.mem_singleton.mpr rfl))))
    · rw [runit7_mul, hrs]
      exact Finset.mem_insert.mpr (Or.inl rfl)
  · -- `s₂`-image ⊆ `Q`
    refine le_trans (apLen_mono'' ?_) hQcard
    intro q hq
    obtain ⟨d', hd', rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨hd'mem, hd'r⟩ := Finset.mem_filter.mp hd'
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hd'mem
    have hrd : runit7 d = s := by
      have h := hcancel d 1 (by rw [one_mul]; exact hd'r)
      rwa [one_mul] at h
    exact hQ d hd hrd
  · -- `2s₂`-image ⊆ `{q(c·d5)}`
    refine le_trans (apLen_mono'' ?_) (case62_apLen_single (qdig7 m (c * d5)))
    intro q hq
    obtain ⟨d', hd', rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨hd'mem, hd'r⟩ := Finset.mem_filter.mp hd'
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hd'mem
    have hrd : runit7 d = 2 * s := hcancel d 2 hd'r
    have hd5' : d = d5 := by
      rcases hother d hd with h | h
      · exact h
      · rw [h] at hrd
        exact absurd hrd.symm (by
          intro hcon
          have : s ∈ ({2 * s, 4 * s} : Finset (ZMod 7)) :=
            Finset.mem_insert.mpr (Or.inl hcon.symm)
          exact case62_cls_ne s hs this)
    rw [hd5', Finset.mem_singleton]
  · -- `4s₂`-image ⊆ `{q(c·d5)}`
    refine le_trans (apLen_mono'' ?_) (case62_apLen_single (qdig7 m (c * d5)))
    intro q hq
    obtain ⟨d', hd', rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨hd'mem, hd'r⟩ := Finset.mem_filter.mp hd'
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hd'mem
    have hrd : runit7 d = 4 * s := hcancel d 4 hd'r
    have hd5' : d = d5 := by
      rcases hother d hd with h | h
      · exact h
      · rw [h] at hrd
        exact absurd hrd.symm (by
          intro hcon
          have : s ∈ ({2 * s, 4 * s} : Finset (ZMod 7)) :=
            Finset.mem_insert.mpr
              (Or.inr (Finset.mem_singleton.mpr hcon.symm))
          exact case62_cls_ne s hs this)
    rw [hd5', Finset.mem_singleton]
  · -- `s₂`-filter nonempty
    obtain ⟨d, hd, hdr⟩ := hne
    refine ⟨c * d, Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
    · exact Finset.mem_image.mpr ⟨d, hd, rfl⟩
    · rw [runit7_mul, hdr, hs₂]
  · -- one of `{2s₂,4s₂}`-filters is empty
    rcases Finset.mem_insert.mp hd5cls with h2 | h4
    · -- `r(d5) = 2s` → `4s₂`-filter empty
      right
      rw [Finset.eq_empty_iff_forall_notMem]
      intro d' hd'
      obtain ⟨hd'mem, hd'r⟩ := Finset.mem_filter.mp hd'
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hd'mem
      have hrd : runit7 d = 4 * s := hcancel d 4 hd'r
      rcases hother d hd with rfl | hrs
      · rw [h2] at hrd
        have : (2 : ZMod 7) * s = 4 * s := hrd
        have hs0 : (2 : ZMod 7) * s - 4 * s = 0 := sub_eq_zero.mpr this
        have : (-2 : ZMod 7) * s = 0 := by linear_combination hs0
        rcases mul_eq_zero.mp this with h | h
        · exact absurd h (by decide)
        · exact hs h
      · rw [hrs] at hrd
        have : s ∈ ({2 * s, 4 * s} : Finset (ZMod 7)) :=
          Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr hrd))
        exact case62_cls_ne s hs this
    · -- `r(d5) = 4s` → `2s₂`-filter empty
      left
      rw [Finset.eq_empty_iff_forall_notMem]
      intro d' hd'
      obtain ⟨hd'mem, hd'r⟩ := Finset.mem_filter.mp hd'
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hd'mem
      have hrd : runit7 d = 2 * s := hcancel d 2 hd'r
      rcases hother d hd with rfl | hrs
      · rw [Finset.mem_singleton.mp h4] at hrd
        have : (4 : ZMod 7) * s = 2 * s := hrd
        have hs0 : (4 : ZMod 7) * s - 2 * s = 0 := sub_eq_zero.mpr this
        have : (2 : ZMod 7) * s = 0 := by linear_combination hs0
        rcases mul_eq_zero.mp this with h | h
        · exact absurd h (by decide)
        · exact hs h
      · rw [hrs] at hrd
        have : s ∈ ({2 * s, 4 * s} : Finset (ZMod 7)) :=
          Finset.mem_insert.mpr (Or.inl hrd)
        exact case62_cls_ne s hs this


/-- **Finish**: `lemma5` + `exists_lambda0_of_shift`. Given the prepared
bounds, produce a `Λ₀`-multiplier good on `B`. -/
private theorem case62_finish {m : ℕ} (hm : 0 < m) {B : Finset ℕ}
    (hunit : ∀ d ∈ B, padicValNat 7 d = 0)
    {s : ZMod 7} (hs : s ≠ 0)
    (hcls : ∀ d ∈ B, runit7 d ∈ ({s, 2 * s, 4 * s} : Finset (ZMod 7)))
    (hA1 : apLen ((B.filter fun d => runit7 d = s).image (qdig7 m)) ≤ 4)
    (hA2 : apLen ((B.filter fun d => runit7 d = 2 * s).image (qdig7 m)) ≤ 1)
    (hA4 : apLen ((B.filter fun d => runit7 d = 4 * s).image (qdig7 m)) ≤ 1)
    (hne : (B.filter fun d => runit7 d = s).Nonempty)
    (hempty : (B.filter fun d => runit7 d = 2 * s) = ∅ ∨
        (B.filter fun d => runit7 d = 4 * s) = ∅) :
    ∃ lam ∈ multLow7 m 0, good7 m lam B := by
  classical
  set D1 := (B.filter fun d => runit7 d = s).image (qdig7 m)
  set D2 := (B.filter fun d => runit7 d = 2 * s).image (qdig7 m)
  set D4 := (B.filter fun d => runit7 d = 4 * s).image (qdig7 m)
  have hD1pos : 0 < apLen D1 := case62_apLen_pos (hne.image _)
  have hsum : apLen D1 + apLen D2 + apLen D4 ≤ 5 := by
    rcases hempty with he | he
    · have hz : apLen D2 = 0 := by
        show apLen ((B.filter fun d => runit7 d = 2 * s).image (qdig7 m)) = 0
        rw [he, Finset.image_empty, apLen_empty]
      omega
    · have hz : apLen D4 = 0 := by
        show apLen ((B.filter fun d => runit7 d = 4 * s).image (qdig7 m)) = 0
        rw [he, Finset.image_empty, apLen_empty]
      omega
  have hord : apLen D2 ≤ apLen D1 ∧ apLen D4 ≤ apLen D1 := by omega
  obtain hres | ⟨hl1, hl2, hl4, hexc⟩ :=
    lemma5 (s := 1) (A₁ := D1) (A₂ := D2) (A₄ := D4) (by decide) hord hsum
  · obtain ⟨t, ht⟩ := hres
    exact exists_lambda0_of_shift hm hs hunit hcls t ht
  · -- the (3,1,1) exception needs both small classes nonempty — impossible
    rcases hempty with he | he
    · have hne2 : D2.Nonempty := nonempty_of_apLen_pos (by omega)
      have hne2' := Finset.image_nonempty.mp hne2
      rw [he] at hne2'
      exact (Finset.not_nonempty_empty hne2').elim
    · have hne4 : D4.Nonempty := nonempty_of_apLen_pos (by omega)
      have hne4' := Finset.image_nonempty.mp hne4
      rw [he] at hne4'
      exact (Finset.not_nonempty_empty hne4').elim

/-! ### §6 The wrap: `prepare` + `finish` fused, and the `{0,6}` tail -/

/-- **Wrap**: the full `lemma5` pipeline.  Given a multiplier `c` whose
`s`-class digit image fits a `≤4` cyclic interval `Q`, produce a `7`-unit
`lam` good on `A` (the leftover `d5` occupies exactly one of the
`{2s,4s}` classes). -/
private theorem case62_wrap {m : ℕ} (hm : 0 < m) {A : Finset ℕ}
    (hpos : ∀ d ∈ A, 0 < d)
    (hunit : ∀ d ∈ A, padicValNat 7 d = 0)
    {s : ZMod 7} (hs : s ≠ 0)
    {d5 : ℕ} (hd5 : d5 ∈ A)
    (hd5cls : runit7 d5 ∈ ({2 * s, 4 * s} : Finset (ZMod 7)))
    (hother : ∀ d ∈ A, d = d5 ∨ runit7 d = s)
    (hne : ∃ d ∈ A, runit7 d = s)
    {c : ℕ} (hc : ¬ 7 ∣ c)
    {Q : Finset (ZMod 7)} (hQcard : apLen Q ≤ 4)
    (hQ : ∀ d ∈ A, runit7 d = s → qdig7 m (c * d) ∈ Q) :
    ∃ lam : ℕ, ¬ 7 ∣ lam ∧ good7 m lam A := by
  have hcpos : 0 < c := Nat.pos_of_ne_zero (fun h0 => hc (h0 ▸ dvd_zero _))
  obtain ⟨s₂, hs₂0, hclsB, hA1b, hA2b, hA4b, hneB, hempty⟩ :=
    case62_prepare hcpos hs hd5 hd5cls hother hne hQcard hQ
  set B := A.image (fun d => c * d) with hB
  have hunitB : ∀ d' ∈ B, padicValNat 7 d' = 0 := by
    intro d' hd'
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hd'
    rw [padicValNat_mul_seven hc (ne_of_gt (hpos d hd))]
    exact hunit d hd
  obtain ⟨lam0, hlam0mem, hgood⟩ :=
    case62_finish hm hunitB hs₂0 hclsB hA1b hA2b hA4b hneB hempty
  refine ⟨lam0 * c,
    Nat.prime_seven.not_dvd_mul
      (not_dvd_of_mem_multLow7_zero hm hlam0mem) hc, ?_⟩
  exact case62_good7_of_image hgood

/-- **Tail-5**: the `lemma9`-output pipeline.  `lam'` compresses the
triple `{b1,b2,b3}` (all class `s`) into a `≤2` digit set; `d4` is the
remaining `s`-class element (its digit is unrestricted).  A `Λ₀`-element
sends the triple digits into `{0,6}`, and the whole `s`-class image then
lies in `{0,6,q4}` — `apLen ≤ 4` unless `q4 = 3`, which the `×2` dilation
fixes (carry `{0,1}` lands in `{0,1,5,6}`). -/
private theorem case62_tail5 {m : ℕ} (hm : 0 < m) {A : Finset ℕ}
    (hpos : ∀ d ∈ A, 0 < d)
    (hunit : ∀ d ∈ A, padicValNat 7 d = 0)
    {s : ZMod 7} (hs : s ≠ 0)
    {d5 : ℕ} (hd5 : d5 ∈ A)
    (hd5cls : runit7 d5 ∈ ({2 * s, 4 * s} : Finset (ZMod 7)))
    (hother : ∀ d ∈ A, d = d5 ∨ runit7 d = s)
    (hne : ∃ d ∈ A, runit7 d = s)
    {b1 b2 b3 d4 : ℕ}
    (hb1 : b1 ∈ A) (hb2 : b2 ∈ A) (hb3 : b3 ∈ A) (hd4 : d4 ∈ A)
    (hr1 : runit7 b1 = s) (hr2 : runit7 b2 = s)
    (hr3 : runit7 b3 = s) (hr4 : runit7 d4 = s)
    (hcover : ∀ d ∈ A, runit7 d = s → d ∈ ({b1, b2, b3, d4} : Finset ℕ))
    {lam' : ℕ} (hlam' : ¬ 7 ∣ lam')
    (hap : apLen (({b1, b2, b3} : Finset ℕ).image
      (fun d => qdig7 m (lam' * d))) ≤ 2) :
    ∃ lam : ℕ, ¬ 7 ∣ lam ∧ good7 m lam A := by
  classical
  set T := ({b1, b2, b3} : Finset ℕ).image (fun d => lam' * d) with hT
  have hlam'0 : lam' ≠ 0 := fun h0 => hlam' (h0 ▸ dvd_zero _)
  have hs' : runit7 lam' * s ≠ 0 :=
    mul_ne_zero (runit7_ne_zero (Nat.pos_of_ne_zero hlam'0)) hs
  have hunitT : ∀ d' ∈ T, padicValNat 7 d' = 0 := by
    intro d' hd'
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hd'
    rcases case62_cover3 hd with h | h | h
    · rw [h, padicValNat_mul_seven hlam' (ne_of_gt (hpos b1 hb1))]
      exact hunit b1 hb1
    · rw [h, padicValNat_mul_seven hlam' (ne_of_gt (hpos b2 hb2))]
      exact hunit b2 hb2
    · rw [h, padicValNat_mul_seven hlam' (ne_of_gt (hpos b3 hb3))]
      exact hunit b3 hb3
  have hclsT : ∀ d' ∈ T, runit7 d' = runit7 lam' * s := by
    intro d' hd'
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hd'
    rcases case62_cover3 hd with h | h | h
    · rw [h, runit7_mul, hr1]
    · rw [h, runit7_mul, hr2]
    · rw [h, runit7_mul, hr3]
  have hapT : apLen (T.image (qdig7 m)) ≤ 2 := by
    rw [hT, Finset.image_image]
    exact hap
  obtain ⟨lam0, hlam0mem, h06⟩ :=
    exists_lambda0_qdig_06 hunitT hs' hclsT hapT
  have hlam0nd : ¬ 7 ∣ lam0 := not_dvd_of_mem_multLow7_zero hm hlam0mem
  set c := lam0 * lam' with hc
  have hc7 : ¬ 7 ∣ c := Nat.prime_seven.not_dvd_mul hlam0nd hlam'
  have hq06 : ∀ d ∈ ({b1, b2, b3} : Finset ℕ),
      qdig7 m (c * d) ∈ ({0, 6} : Finset (ZMod 7)) := by
    intro d hd
    have hdT : lam' * d ∈ T := Finset.mem_image.mpr ⟨d, hd, rfl⟩
    have h := h06 _ hdT
    rw [hc, mul_assoc]
    exact h
  have hb1m : b1 ∈ ({b1, b2, b3} : Finset ℕ) := by simp
  have hb2m : b2 ∈ ({b1, b2, b3} : Finset ℕ) := by simp
  have hb3m : b3 ∈ ({b1, b2, b3} : Finset ℕ) := by simp
  set q4 := qdig7 m (c * d4) with hq4
  by_cases hq43 : q4 = 3
  · -- `q4 = 3`: dilate by `2`; the carry `{0,1}` lands inside `{0,1,5,6}`.
    refine case62_wrap hm hpos hunit hs hd5 hd5cls hother hne
      (c := 2 * c) (Nat.prime_seven.not_dvd_mul (by decide) hc7)
      (Q := ({0, 1, 5, 6} : Finset (ZMod 7))) case62_apLen_rescaled ?_
    intro d hd hdr
    have hzd : qdig7 m (c * d) ∈ ({0, 6, 3} : Finset (ZMod 7)) := by
      have hmem := hcover d hd hdr
      rcases case62_cover4 hmem with h | h | h | h
      · rw [h]
        have hz := hq06 b1 hb1m
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz ⊢
        rcases hz with h0 | h6
        · exact Or.inl h0
        · exact Or.inr (Or.inl h6)
      · rw [h]
        have hz := hq06 b2 hb2m
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz ⊢
        rcases hz with h0 | h6
        · exact Or.inl h0
        · exact Or.inr (Or.inl h6)
      · rw [h]
        have hz := hq06 b3 hb3m
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz ⊢
        rcases hz with h0 | h6
        · exact Or.inl h0
        · exact Or.inr (Or.inl h6)
      · rw [h]
        have h3 : qdig7 m (c * d4) = 3 := hq4 ▸ hq43
        rw [h3]
        exact Finset.mem_insert.mpr
          (Or.inr (Finset.mem_insert.mpr (Or.inr
            (Finset.mem_singleton.mpr rfl))))
    have hcarry := case62_carry2 (m := m) (x := c * d)
    rw [show 2 * c * d = 2 * (c * d) from by ring]
    exact case62_mem0156 hzd hcarry
  · -- `q4 ≠ 3`: `{0,6,q4}` has `apLen ≤ 4`.
    refine case62_wrap hm hpos hunit hs hd5 hd5cls hother hne hc7
      (Q := ({0, 6, q4} : Finset (ZMod 7))) ?_ ?_
    · exact case62_apLen_triple06 q4 hq43
    · intro d hd hdr
      have hmem := hcover d hd hdr
      rcases case62_cover4 hmem with h | h | h | h
      · rw [h]
        have hz := hq06 b1 hb1m
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz ⊢
        rcases hz with h0 | h6
        · exact Or.inl h0
        · exact Or.inr (Or.inl h6)
      · rw [h]
        have hz := hq06 b2 hb2m
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz ⊢
        rcases hz with h0 | h6
        · exact Or.inl h0
        · exact Or.inr (Or.inl h6)
      · rw [h]
        have hz := hq06 b3 hb3m
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz ⊢
        rcases hz with h0 | h6
        · exact Or.inl h0
        · exact Or.inr (Or.inl h6)
      · rw [h, ← hq4]
        exact Finset.mem_insert.mpr
          (Or.inr (Finset.mem_insert.mpr (Or.inr
            (Finset.mem_singleton.mpr rfl))))

/-! ### §7 `eMod7` congruence algebra clones (level/unit arithmetic) -/

/-- `ZMod`-cast of `eMod7`: the wrapped residue casts to the branch
expression in `ZMod (7^{m+1})` (clone of the sibling-file version). -/
private theorem case62_eMod7_zmod_cast (m x y : ℕ) :
    ((eMod7 m x y : ℕ) : ZMod (7 ^ (m + 1))) =
      if runit7 y = 2 * runit7 x then 2 * (x : ZMod _) - (y : ZMod _)
      else if runit7 x = 2 * runit7 y then 2 * (y : ZMod _) - (x : ZMod _)
      else (x : ZMod _) - (y : ZMod _) := by
  have hcast : ∀ a : ℕ,
      ((a % 7 ^ (m + 1) : ℕ) : ZMod (7 ^ (m + 1))) = (a : ZMod _) := by
    intro a
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr (Nat.mod_mod a _)
  have hN : ((7 ^ (m + 1) : ℕ) : ZMod (7 ^ (m + 1))) = 0 :=
    ZMod.natCast_self _
  unfold eMod7
  split_ifs with h1 h2
  · rw [hcast, Nat.cast_sub (by
      have : y % 7 ^ (m + 1) < 7 ^ (m + 1) :=
        Nat.mod_lt _ (Nat.pow_pos (by norm_num))
      omega : y % 7 ^ (m + 1) ≤ 2 * (x % 7 ^ (m + 1)) + 7 ^ (m + 1))]
    rw [Nat.cast_add, Nat.cast_mul, hcast x, hcast y, hN, Nat.cast_ofNat]
    ring
  · rw [hcast, Nat.cast_sub (by
      have : x % 7 ^ (m + 1) < 7 ^ (m + 1) :=
        Nat.mod_lt _ (Nat.pow_pos (by norm_num))
      omega : x % 7 ^ (m + 1) ≤ 2 * (y % 7 ^ (m + 1)) + 7 ^ (m + 1))]
    rw [Nat.cast_add, Nat.cast_mul, hcast y, hcast x, hN, Nat.cast_ofNat]
    ring
  · rw [hcast, Nat.cast_sub (by
      have : y % 7 ^ (m + 1) < 7 ^ (m + 1) :=
        Nat.mod_lt _ (Nat.pow_pos (by norm_num))
      omega : y % 7 ^ (m + 1) ≤ x % 7 ^ (m + 1) + 7 ^ (m + 1))]
    rw [Nat.cast_add, hcast x, hcast y, hN]
    ring

/-- `eMod7` casts to a plain difference in the `same` branch. -/
private theorem case62_eMod7_zmod_cast_same {m u v : ℕ}
    (h : residueRelOf u v = residueRel.same) :
    ((eMod7 m u v : ℕ) : ZMod (7 ^ (m + 1)))
      = (u : ZMod _) - (v : ZMod _) := by
  obtain ⟨h1, h2⟩ := (residueRelOf_eq_same).mp h
  rw [case62_eMod7_zmod_cast, if_neg h1, if_neg h2]

/-- `(e(x,y) : ZMod N) = e(x,l) − e(y,l)` for `same` pairs. -/
private theorem case62_eMod7_cast_sub {m x y l : ℕ}
    (hxl : residueRelOf x l = residueRel.same)
    (hyl : residueRelOf y l = residueRel.same)
    (hxy : residueRelOf x y = residueRel.same) :
    ((eMod7 m x y : ℕ) : ZMod (7 ^ (m + 1)))
      = (eMod7 m x l : ZMod _) - (eMod7 m y l : ZMod _) := by
  rw [case62_eMod7_zmod_cast_same hxy, case62_eMod7_zmod_cast_same hxl,
    case62_eMod7_zmod_cast_same hyl]
  ring

/-- As naturals: `e(x,y) = (e(x,l) + N − e(y,l)) % N`. -/
private theorem case62_eMod7_sub_eq {m x y l : ℕ}
    (hxl : residueRelOf x l = residueRel.same)
    (hyl : residueRelOf y l = residueRel.same)
    (hxy : residueRelOf x y = residueRel.same) :
    eMod7 m x y
      = (eMod7 m x l + 7 ^ (m + 1) - eMod7 m y l) % 7 ^ (m + 1) := by
  have h := case62_eMod7_cast_sub (m := m) hxl hyl hxy
  have hcast : ((eMod7 m x y : ℕ) : ZMod (7 ^ (m + 1)))
      = ((eMod7 m x l + 7 ^ (m + 1) - eMod7 m y l : ℕ) : ZMod _) := by
    rw [h]
    have hlt : eMod7 m y l ≤ eMod7 m x l + 7 ^ (m + 1) := by
      have := case62_eMod7_lt (m := m) (x := y) (y := l)
      omega
    rw [Nat.cast_sub hlt, Nat.cast_add, ZMod.natCast_self]
    ring
  rw [ZMod.natCast_eq_natCast_iff'] at hcast
  have hlt : eMod7 m x y < 7 ^ (m + 1) := case62_eMod7_lt
  rwa [Nat.mod_eq_of_lt hlt] at hcast

/-- `e(y,x) = (N − e(x,y)) % N` for `same` pairs (both `0` or negated). -/
private theorem case62_eMod7_neg_eq {m x y : ℕ}
    (hxy : residueRelOf x y = residueRel.same)
    (hyx : residueRelOf y x = residueRel.same) :
    eMod7 m y x = (7 ^ (m + 1) - eMod7 m x y) % 7 ^ (m + 1) := by
  have hcast : ((eMod7 m y x : ℕ) : ZMod (7 ^ (m + 1)))
      = ((7 ^ (m + 1) - eMod7 m x y : ℕ) : ZMod _) := by
    rw [case62_eMod7_zmod_cast_same hyx]
    have hlt : eMod7 m x y < 7 ^ (m + 1) := case62_eMod7_lt
    rw [Nat.cast_sub (by omega : eMod7 m x y ≤ 7 ^ (m + 1)),
      ZMod.natCast_self, case62_eMod7_zmod_cast_same hxy]
    ring
  rw [ZMod.natCast_eq_natCast_iff'] at hcast
  have hlt : eMod7 m y x < 7 ^ (m + 1) := case62_eMod7_lt
  rwa [Nat.mod_eq_of_lt hlt] at hcast

/-- **Block form**: `e ≡ r(e)·7^{ν(e)} (mod 7^{ν(e)+1})` for `e ≠ 0`. -/
private theorem case62_nat_mod_pow_succ_of_padic {e h : ℕ} (he : e ≠ 0)
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
private theorem case62_level_of_mod_block {w h s : ℕ}
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
      exact hndvd
        ((Nat.pow_dvd_iff_le_padicValNat (by norm_num) hw0).mpr hc)
    omega
  refine ⟨hw0, hν, ?_⟩
  unfold runit7
  rw [hν]
  have hdiv : w / 7 ^ h = s + 7 * (w / 7 ^ (h + 1)) := by
    conv_lhs => rw [hw_eq]
    exact Nat.mul_div_cancel_left _ hP
  rw [hdiv, Nat.cast_add, Nat.cast_mul,
    show ((7 : ℕ) : ZMod 7) = 0 from ZMod.natCast_self 7, zero_mul, add_zero]

/-- `(a + c − b) % P` depends only on `a % P`, `b % P` when `P ∣ c`
(and the subtraction does not truncate). -/
private theorem case62_wrap_sub_mod_gen {a b c P : ℕ} (hP : 0 < P)
    (hc : P ∣ c) (hle : b ≤ a + c) :
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
`7^{h+1}` (wrapped subtraction `u − v` inside the modulus). -/
private theorem case62_sub_mod_block {u v h : ℕ} (hu : u ≠ 0) (hv : v ≠ 0)
    (huν : padicValNat 7 u = h) (hvν : padicValNat 7 v = h) :
    (u % 7 ^ (h + 1) + 7 ^ (h + 1) - v % 7 ^ (h + 1)) % 7 ^ (h + 1)
      = (runit7 u - runit7 v).val * 7 ^ h := by
  have hub := case62_nat_mod_pow_succ_of_padic hu huν
  have hvb := case62_nat_mod_pow_succ_of_padic hv hvν
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

/-- The negated residue `N − e` (for `0 < e < N`, `ν(e) ≤ m`) has the
same level as `e` and unit `−r(e)`. -/
private theorem case62_neg_resid_level {m e : ℕ} (he : e ≠ 0)
    (helt : e < 7 ^ (m + 1)) (hνm : padicValNat 7 e ≤ m) :
    padicValNat 7 (7 ^ (m + 1) - e) = padicValNat 7 e ∧
    runit7 (7 ^ (m + 1) - e) = - runit7 e := by
  set h := padicValNat 7 e with hh
  have hub := case62_nat_mod_pow_succ_of_padic he rfl
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
    case62_level_of_mod_block hmod (by omega : 0 < 7 - (runit7 e).val)
      (by omega : 7 - (runit7 e).val < 7)
  refine ⟨hνw, ?_⟩
  rw [hrw]
  rw [Nat.cast_sub (by omega : (runit7 e).val ≤ 7)]
  push_cast
  rw [show (7 : ZMod 7) = 0 from by decide, zero_sub,
    ZMod.natCast_zmod_val]

/-- `e(y,x)` has the same level and negated unit as `e(x,y)` (`same`
pairs). -/
private theorem case62_enu7_neg {m x y : ℕ}
    (hxy : residueRelOf x y = residueRel.same)
    (hyx : residueRelOf y x = residueRel.same) :
    padicValNat 7 (eMod7 m y x) = padicValNat 7 (eMod7 m x y) ∧
    runit7 (eMod7 m y x) = - runit7 (eMod7 m x y) := by
  rw [case62_eMod7_neg_eq hxy hyx]
  rcases eq_or_ne (eMod7 m x y) 0 with he | he
  · rw [he, Nat.sub_zero, Nat.mod_self]
    simp [runit7]
  · set e := eMod7 m x y
    have hlt : e < 7 ^ (m + 1) := case62_eMod7_lt
    have hνm : padicValNat 7 e ≤ m := by
      have hndvd : ¬ 7 ^ (m + 1) ∣ e := by
        intro hd
        exact he (Nat.eq_zero_of_dvd_of_lt hd hlt)
      by_contra hc
      push_neg at hc
      exact hndvd
        ((Nat.pow_dvd_iff_le_padicValNat (by norm_num) he).mpr hc)
    have hw : (7 ^ (m + 1) - e) % 7 ^ (m + 1) = 7 ^ (m + 1) - e := by
      rw [Nat.mod_eq_of_lt (by omega : 7 ^ (m + 1) - e < 7 ^ (m + 1))]
    rw [hw]
    exact case62_neg_resid_level he hlt hνm

/-- `e(y,x)` has the same level as `e(x,y)` (`same` pairs). -/
private theorem case62_enu7_sym {m x y : ℕ}
    (hxy : residueRelOf x y = residueRel.same)
    (hyx : residueRelOf y x = residueRel.same) :
    padicValNat 7 (eMod7 m y x) = padicValNat 7 (eMod7 m x y) :=
  (case62_enu7_neg hxy hyx).1

/-- `e(y,x)` has negated unit (`same` pairs). -/
private theorem case62_runit7_eMod7_neg {m x y : ℕ}
    (hxy : residueRelOf x y = residueRel.same)
    (hyx : residueRelOf y x = residueRel.same) :
    runit7 (eMod7 m y x) = - runit7 (eMod7 m x y) :=
  (case62_enu7_neg hxy hyx).2

/-- **Block value of `e(x,y)`** through a common point `l` when both
`(x,l)`, `(y,l)` pairs have level `h ≤ m`: reads
`(r(e_{xl}) − r(e_{yl}))·7^h` mod `7^{h+1}`. -/
private theorem case62_eMod7_sub_block {m x y l h : ℕ}
    (hxl : residueRelOf x l = residueRel.same)
    (hyl : residueRelOf y l = residueRel.same)
    (hxy : residueRelOf x y = residueRel.same)
    (hxl0 : eMod7 m x l ≠ 0) (hyl0 : eMod7 m y l ≠ 0)
    (hxlν : padicValNat 7 (eMod7 m x l) = h)
    (hylν : padicValNat 7 (eMod7 m y l) = h) (hm : h ≤ m) :
    eMod7 m x y % 7 ^ (h + 1)
      = (runit7 (eMod7 m x l) - runit7 (eMod7 m y l)).val * 7 ^ h := by
  rw [case62_eMod7_sub_eq hxl hyl hxy]
  rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 7 (by omega : h + 1 ≤ m + 1))]
  rw [case62_wrap_sub_mod_gen (Nat.pow_pos (by norm_num))
    (Nat.pow_dvd_pow 7 (by omega : h + 1 ≤ m + 1))
    (by have := case62_eMod7_lt (m := m) (x := y) (y := l); omega)]
  exact case62_sub_mod_block hxl0 hyl0 hxlν hylν

/-- Distinct `r`'s through a common point give `e(x,y)` level `h` and
unit `r(e_{xl}) − r(e_{yl})`. -/
private theorem case62_eMod7_level_of_runit_ne {m x y l h : ℕ}
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
  have hblk := case62_eMod7_sub_block hxl hyl hxy hxl0 hyl0 hxlν hylν hm
  have hs : 0 < (runit7 (eMod7 m x l) - runit7 (eMod7 m y l)).val := by
    rcases Nat.eq_zero_or_pos
        (runit7 (eMod7 m x l) - runit7 (eMod7 m y l)).val with h0 | h0
    · exfalso
      rw [ZMod.val_eq_zero] at h0
      exact hr (sub_eq_zero.mp h0)
    · exact h0
  have hs7 : (runit7 (eMod7 m x l) - runit7 (eMod7 m y l)).val < 7 :=
    ZMod.val_lt _
  obtain ⟨hw0, hνw, hrw⟩ := case62_level_of_mod_block hblk hs hs7
  rw [ZMod.natCast_zmod_val] at hrw
  exact ⟨hw0, hνw, hrw⟩

/-- Equal `r`'s through a common point force `e(x,y) = 0` or level
`> h` (the "collision" alternative). -/
private theorem case62_eMod7_level_gt_of_runit_eq {m x y l h : ℕ}
    (hxl : residueRelOf x l = residueRel.same)
    (hyl : residueRelOf y l = residueRel.same)
    (hxy : residueRelOf x y = residueRel.same)
    (hxl0 : eMod7 m x l ≠ 0) (hyl0 : eMod7 m y l ≠ 0)
    (hxlν : padicValNat 7 (eMod7 m x l) = h)
    (hylν : padicValNat 7 (eMod7 m y l) = h) (hm : h ≤ m)
    (hr : runit7 (eMod7 m x l) = runit7 (eMod7 m y l)) :
    eMod7 m x y = 0 ∨ h < padicValNat 7 (eMod7 m x y) := by
  have hblk := case62_eMod7_sub_block hxl hyl hxy hxl0 hyl0 hxlν hylν hm
  rw [hr, sub_self, ZMod.val_zero, zero_mul] at hblk
  rcases eq_or_ne (eMod7 m x y) 0 with he | he
  · exact Or.inl he
  · right
    have hdvd : 7 ^ (h + 1) ∣ eMod7 m x y := by
      rw [Nat.dvd_iff_mod_eq_zero]
      exact hblk
    have hle' :=
      (Nat.pow_dvd_iff_le_padicValNat (by norm_num) he).mp hdvd
    omega

/-! ### §8 The `(ii.2)` exceptional route (`lemma6`) -/

/-- `{c,2c,4c} = {1,2,4}` for `c ∈ {1,2,4}` (the cube coset). -/
private theorem case62_coset124 : ∀ c : ZMod 7,
    c ∈ ({1, 2, 4} : Finset (ZMod 7)) →
    ({c, 2 * c, 4 * c} : Finset (ZMod 7)) = {1, 2, 4} := by
  decide

/-- `1 + {0,c,2c,4c} = {1,2,3,5}` for `c ∈ {1,2,4}`. -/
private theorem case62_offsets_1235 : ∀ c : ZMod 7,
    c ∈ ({1, 2, 4} : Finset (ZMod 7)) →
    ({1, 1 + c, 1 + 2 * c, 1 + 4 * c} : Finset (ZMod 7)) = {1, 2, 3, 5} := by
  decide

/-- `ν(v·7^m) = m` for `0 < v < 7`. -/
private theorem case62_nu_pow7 {m v : ℕ} (hv : 0 < v) (hv7 : v < 7) :
    padicValNat 7 (v * 7 ^ m) = m := by
  have hv0 : padicValNat 7 v = 0 :=
    padicValNat.eq_zero_of_not_dvd (fun h => by
      have := Nat.le_of_dvd hv h
      omega)
  rw [padicValNat.mul (ne_of_gt hv) (pow_ne_zero m (by norm_num)), hv0,
    padicValNat.prime_pow m, zero_add]

/-- `runit7 (v·7^m) = v` for nonzero `v : ZMod 7`. -/
private theorem case62_runit7_pow7 {m : ℕ} {v : ZMod 7} (hv : v ≠ 0) :
    runit7 (v.val * 7 ^ m) = v := by
  have hvpos : 0 < v.val :=
    Nat.pos_of_ne_zero (by rwa [Ne, ZMod.val_eq_zero])
  unfold runit7
  rw [case62_nu_pow7 hvpos (ZMod.val_lt v),
    Nat.mul_div_cancel _ (Nat.pow_pos (by norm_num)), ZMod.natCast_zmod_val]

/-- **Tail-6**: the `(ii.2)` exceptional route.  After normalisation the
four `s`-class elements sit at offsets `{0,1,2,4}` above `d1` (exact
`k·c₀·7^m` differences, `c₀ ∈ {1,2,4}`), `lam2` is a `≡ 1 (mod 7)`
multiplier that already avoids the `ẽ` obstruction for the `d5` class,
and the `lemma6` `(5,0,1)`/`(5,1,0)` configurations finish the job. -/
private theorem case62_tail6 {m : ℕ} (hm : 2 ≤ m) {A : Finset ℕ}
    (hpos : ∀ d ∈ A, 0 < d)
    (hunit : ∀ d ∈ A, padicValNat 7 d = 0)
    {s : ZMod 7} (hs : s ≠ 0)
    {d5 : ℕ} (hd5 : d5 ∈ A)
    (hd5cls : runit7 d5 ∈ ({2 * s, 4 * s} : Finset (ZMod 7)))
    (hother : ∀ d ∈ A, d = d5 ∨ runit7 d = s)
    (hne : ∃ d ∈ A, runit7 d = s)
    {d1 d2 d3 d4 : ℕ}
    (hd1 : d1 ∈ A) (hd2 : d2 ∈ A) (hd3 : d3 ∈ A) (hd4 : d4 ∈ A)
    (hr1 : runit7 d1 = s) (hr2 : runit7 d2 = s)
    (hr3 : runit7 d3 = s) (hr4 : runit7 d4 = s)
    (hcover : ∀ d ∈ A, runit7 d = s → d ∈ ({d1, d2, d3, d4} : Finset ℕ))
    {c0 : ZMod 7} (hc0 : c0 ∈ ({1, 2, 4} : Finset (ZMod 7)))
    (hν21 : padicValNat 7 (eMod7 m d2 d1) = m)
    (hν31 : padicValNat 7 (eMod7 m d3 d1) = m)
    (hν41 : padicValNat 7 (eMod7 m d4 d1) = m)
    (hr21 : runit7 (eMod7 m d2 d1) = c0)
    (hr31 : runit7 (eMod7 m d3 d1) = 2 * c0)
    (hr41 : runit7 (eMod7 m d4 d1) = 4 * c0)
    {lam2 : ℕ} (hlam2 : ¬ 7 ∣ lam2) (hlam2m : lam2 % 7 = 1)
    (havoid : (runit7 d5 = 4 * s ∧
        etd7 m (lam2 * d5) (lam2 * d1) ∉ ({4, 6} : Finset (ZMod 7)))
      ∨ (runit7 d5 = 2 * s ∧
        etd7 m (lam2 * d1) (lam2 * d5) ∉ ({2, 3} : Finset (ZMod 7)))) :
    ∃ lam : ℕ, ¬ 7 ∣ lam ∧ good7 m lam A := by
  classical
  have hm0 : 0 < m := by omega
  have hc00 : c0 ≠ 0 := by
    intro h0
    rw [h0] at hc0
    exact absurd hc0 (by decide)
  have he21 : eMod7 m d2 d1 ≠ 0 := by
    intro h0
    rw [h0] at hν21
    simp at hν21
    omega
  have he31 : eMod7 m d3 d1 ≠ 0 := by
    intro h0
    rw [h0] at hν31
    simp at hν31
    omega
  have he41 : eMod7 m d4 d1 ≠ 0 := by
    intro h0
    rw [h0] at hν41
    simp at hν41
    omega
  have hs21 : residueRelOf d2 d1 = residueRel.same :=
    case62_rel_same hs hr2 hr1
  have hs31 : residueRelOf d3 d1 = residueRel.same :=
    case62_rel_same hs hr3 hr1
  have hs41 : residueRelOf d4 d1 = residueRel.same :=
    case62_rel_same hs hr4 hr1
  have hlam2r : runit7 lam2 = 1 := runit7_eq_one_of_mod7 hlam2m
  have hlam2pos : 0 < lam2 :=
    Nat.pos_of_ne_zero (fun h0 => hlam2 (h0 ▸ dvd_zero _))
  -- digit offsets under `lam2`
  have hq2 := case62_qdig_sub_smul1_top hlam2m hs21 he21 hν21
  have hq3 := case62_qdig_sub_smul1_top hlam2m hs31 he31 hν31
  have hq4 := case62_qdig_sub_smul1_top hlam2m hs41 he41 hν41
  rw [hr21] at hq2
  rw [hr31] at hq3
  rw [hr41] at hq4
  -- `lam3 ∈ Λ₀` normalises `q(lam2·d1)` to `1`
  have hνz : padicValNat 7 (lam2 * d1) = 0 := by
    rw [padicValNat_mul_seven hlam2 (ne_of_gt (hpos d1 hd1))]
    exact hunit d1 hd1
  obtain ⟨k, hk7, hkn⟩ := exists_multLow_set_qdig (j := 0) hm0 hνz
    (ne_of_gt (Nat.mul_pos hlam2pos (hpos d1 hd1))) 1
  rw [Nat.sub_zero] at hkn
  set lam3 := 1 + k * 7 ^ m with hlam3
  have hlam3r : runit7 lam3 = 1 := runit7_multLow hm0
  have hlam3nd : ¬ 7 ∣ lam3 := multLow_not_dvd hm0
  have hlam3pos : 0 < lam3 :=
    Nat.pos_of_ne_zero (fun h0 => hlam3nd (h0 ▸ dvd_zero _))
  have hv1 : qdig7 m (lam3 * (lam2 * d1)) = 1 := hkn
  set T : ZMod 7 := (k : ZMod 7) * s with hT
  have hT_eq : T = 1 - qdig7 m (lam2 * d1) := by
    have h := qdig7_lambda0 (m := m) (d := lam2 * d1) (k := k) hνz
    have hkn' := hkn
    rw [hlam3] at hkn'
    rw [h] at hkn'
    rw [runit7_mul, hlam2r, one_mul, hr1] at hkn'
    rw [hT, ← hkn']
    ring
  -- the four `s`-class digits are `1 + {0,c0,2c0,4c0} = {1,2,3,5}`
  have hoff : ({1, 1 + c0, 1 + 2 * c0, 1 + 4 * c0} : Finset (ZMod 7))
      = {1, 2, 3, 5} := case62_offsets_1235 c0 hc0
  have hv2 : qdig7 m (lam3 * (lam2 * d2)) = 1 + c0 := by
    have hνi : padicValNat 7 (lam2 * d2) = 0 := by
      rw [padicValNat_mul_seven hlam2 (ne_of_gt (hpos d2 hd2))]
      exact hunit d2 hd2
    have hqq : qdig7 m (lam3 * (lam2 * d2))
        = qdig7 m (lam2 * d2) + (k : ZMod 7) * runit7 (lam2 * d2) := by
      rw [hlam3]
      exact qdig7_lambda0 hνi
    rw [hqq, runit7_mul, hlam2r, one_mul, hr2, ← hT, hT_eq]
    linear_combination hq2
  have hv3 : qdig7 m (lam3 * (lam2 * d3)) = 1 + 2 * c0 := by
    have hνi : padicValNat 7 (lam2 * d3) = 0 := by
      rw [padicValNat_mul_seven hlam2 (ne_of_gt (hpos d3 hd3))]
      exact hunit d3 hd3
    have hqq : qdig7 m (lam3 * (lam2 * d3))
        = qdig7 m (lam2 * d3) + (k : ZMod 7) * runit7 (lam2 * d3) := by
      rw [hlam3]
      exact qdig7_lambda0 hνi
    rw [hqq, runit7_mul, hlam2r, one_mul, hr3, ← hT, hT_eq]
    linear_combination hq3
  have hv4 : qdig7 m (lam3 * (lam2 * d4)) = 1 + 4 * c0 := by
    have hνi : padicValNat 7 (lam2 * d4) = 0 := by
      rw [padicValNat_mul_seven hlam2 (ne_of_gt (hpos d4 hd4))]
      exact hunit d4 hd4
    have hqq : qdig7 m (lam3 * (lam2 * d4))
        = qdig7 m (lam2 * d4) + (k : ZMod 7) * runit7 (lam2 * d4) := by
      rw [hlam3]
      exact qdig7_lambda0 hνi
    rw [hqq, runit7_mul, hlam2r, one_mul, hr4, ← hT, hT_eq]
    linear_combination hq4
  -- the scaled set `C = lam3·lam2·A` and its class filters
  set C := A.image (fun d => lam3 * (lam2 * d)) with hC
  have hunitC : ∀ d' ∈ C, padicValNat 7 d' = 0 := by
    intro d' hd'
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hd'
    rw [padicValNat_mul_seven hlam3nd
      (ne_of_gt (Nat.mul_pos hlam2pos (hpos d hd))),
      padicValNat_mul_seven hlam2 (ne_of_gt (hpos d hd))]
    exact hunit d hd
  have hclsC : ∀ d' ∈ C,
      runit7 d' ∈ ({s, 2 * s, 4 * s} : Finset (ZMod 7)) := by
    intro d' hd'
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hd'
    rw [runit7_mul, runit7_mul, hlam3r, one_mul, hlam2r, one_mul]
    rcases hother d hd with rfl | hcls
    · exact Finset.mem_insert.mpr (Or.inr hd5cls)
    · rw [hcls]
      exact Finset.mem_insert.mpr (Or.inl rfl)
  set A1set := (C.filter fun d' => runit7 d' = s).image (qdig7 m) with hA1set
  set A2set := (C.filter fun d' => runit7 d' = 2 * s).image (qdig7 m)
    with hA2set
  set A4set := (C.filter fun d' => runit7 d' = 4 * s).image (qdig7 m)
    with hA4set
  have hfilter_mem : ∀ i : ℕ, i ∈ ({d1, d2, d3, d4} : Finset ℕ) →
      lam3 * (lam2 * i) ∈ C.filter fun d' => runit7 d' = s := by
    intro i hi
    rcases case62_cover4 hi with h | h | h | h
    · rw [h]
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_image.mpr ⟨d1, hd1, rfl⟩, ?_⟩
      rw [runit7_mul, runit7_mul, hlam3r, one_mul, hlam2r, one_mul]
      exact hr1
    · rw [h]
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_image.mpr ⟨d2, hd2, rfl⟩, ?_⟩
      rw [runit7_mul, runit7_mul, hlam3r, one_mul, hlam2r, one_mul]
      exact hr2
    · rw [h]
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_image.mpr ⟨d3, hd3, rfl⟩, ?_⟩
      rw [runit7_mul, runit7_mul, hlam3r, one_mul, hlam2r, one_mul]
      exact hr3
    · rw [h]
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_image.mpr ⟨d4, hd4, rfl⟩, ?_⟩
      rw [runit7_mul, runit7_mul, hlam3r, one_mul, hlam2r, one_mul]
      exact hr4
  have hA1eq : A1set
      = ({1, 1 + c0, 1 + 2 * c0, 1 + 4 * c0} : Finset (ZMod 7)) := by
    apply Finset.Subset.antisymm
    · intro x hx
      rw [hA1set] at hx
      obtain ⟨d', hd', rfl⟩ := Finset.mem_image.mp hx
      have hd'C := case62_filter_subset hd'
      have hd'r := (Finset.mem_filter.mp hd').2
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hd'C
      rw [runit7_mul, runit7_mul, hlam3r, one_mul, hlam2r, one_mul] at hd'r
      have hmem := hcover d hd hd'r
      rcases case62_cover4 hmem with h | h | h | h
      · rw [h, hv1]
        exact Finset.mem_insert.mpr (Or.inl rfl)
      · rw [h, hv2]
        exact Finset.mem_insert.mpr
          (Or.inr (Finset.mem_insert.mpr (Or.inl rfl)))
      · rw [h, hv3]
        exact Finset.mem_insert.mpr
          (Or.inr (Finset.mem_insert.mpr (Or.inr
            (Finset.mem_insert.mpr (Or.inl rfl)))))
      · rw [h, hv4]
        exact Finset.mem_insert.mpr
          (Or.inr (Finset.mem_insert.mpr (Or.inr
            (Finset.mem_insert.mpr (Or.inr
              (Finset.mem_singleton_self _))))))
    · intro x hx
      rw [hA1set]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact Finset.mem_image.mpr
          ⟨lam3 * (lam2 * d1), hfilter_mem d1 (by simp), hv1⟩
      · exact Finset.mem_image.mpr
          ⟨lam3 * (lam2 * d2), hfilter_mem d2 (by simp), hv2⟩
      · exact Finset.mem_image.mpr
          ⟨lam3 * (lam2 * d3), hfilter_mem d3 (by simp), hv3⟩
      · exact Finset.mem_image.mpr
          ⟨lam3 * (lam2 * d4), hfilter_mem d4 (by simp), hv4⟩
  have hapLen1 : apLen A1set = 5 := by
    rw [hA1eq, hoff]
    exact case62_apLen_1235
  have hA1cyc : A1set ⊆ cycIv 1 (apLen A1set) := by
    rw [hapLen1]
    intro x hx
    rw [hA1eq, hoff] at hx
    exact case62_mem_cycIv15 x hx
  have h1mem : (1 : ZMod 7) ∈ A1set := by
    rw [hA1eq]
    exact Finset.mem_insert.mpr (Or.inl rfl)
  -- `d5`'s class decides the configuration
  have hd5r : runit7 d5 = 2 * s ∨ runit7 d5 = 4 * s := by
    have h := hd5cls
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr h
  -- digit of `d5` under `lam3·lam2`
  have hν5 : padicValNat 7 (lam2 * d5) = 0 := by
    rw [padicValNat_mul_seven hlam2 (ne_of_gt (hpos d5 hd5))]
    exact hunit d5 hd5
  have hq5 : qdig7 m (lam3 * (lam2 * d5))
      = qdig7 m (lam2 * d5) + (k : ZMod 7) * runit7 (lam2 * d5) := by
    rw [hlam3]
    exact qdig7_lambda0 hν5
  have hd5C : lam3 * (lam2 * d5) ∈ C :=
    Finset.mem_image.mpr ⟨d5, hd5, rfl⟩
  rcases hd5r with hd5r | hd5r
  · -- `A₂` configuration: `r(d5) = 2s`, the `(5,1,0)` case of `lemma6`
    have h4empty : (C.filter fun d' => runit7 d' = 4 * s) = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro d' hd'
      rw [Finset.mem_filter] at hd'
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hd'.1
      rw [runit7_mul, runit7_mul, hlam3r, one_mul, hlam2r, one_mul] at hd'
      rcases hother d hd with rfl | hcls
      · rw [hd5r] at hd'
        exact absurd (mul_right_cancel₀ hs hd'.2) (by decide)
      · rw [hcls] at hd'
        exact absurd (mul_right_cancel₀ hs
          (show (1 : ZMod 7) * s = 4 * s by
            rw [one_mul]; exact hd'.2)) (by decide)
    have h2sub : (C.filter fun d' => runit7 d' = 2 * s)
        ⊆ {lam3 * (lam2 * d5)} := by
      intro d' hd'
      rw [Finset.mem_filter] at hd'
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hd'.1
      rw [runit7_mul, runit7_mul, hlam3r, one_mul, hlam2r, one_mul] at hd'
      rcases hother d hd with rfl | hcls
      · exact Finset.mem_singleton_self _
      · rw [hcls] at hd'
        exact absurd (mul_right_cancel₀ hs
          (show (1 : ZMod 7) * s = 2 * s by
            rw [one_mul]; exact hd'.2)) (by decide)
    have hd5mem2 : lam3 * (lam2 * d5)
        ∈ C.filter fun d' => runit7 d' = 2 * s := by
      rw [Finset.mem_filter]
      refine ⟨hd5C, ?_⟩
      rw [runit7_mul, runit7_mul, hlam3r, one_mul, hlam2r, one_mul]
      exact hd5r
    have hA2eq : (C.filter fun d' => runit7 d' = 2 * s)
        = {lam3 * (lam2 * d5)} :=
      Finset.Subset.antisymm h2sub
        (Finset.singleton_subset_iff.mpr hd5mem2)
    have hA2set_eq : A2set = {qdig7 m (lam3 * (lam2 * d5))} := by
      rw [hA2set, hA2eq, Finset.image_singleton]
    -- the `(5,1,0)` side condition: `2 − q(d5''') ∉ {2,3}`
    have hetd : etd7 m (lam2 * d1) (lam2 * d5)
        = 2 * qdig7 m (lam2 * d1) - qdig7 m (lam2 * d5) := by
      unfold etd7
      rw [if_pos (by
        rw [runit7_mul, runit7_mul, hlam2r, one_mul, one_mul, hr1, hd5r])]
    have hside : ∀ d' ∈ A2set,
        (2 - d' : ZMod 7) ∉ ({2, 3} : Finset (ZMod 7)) := by
      intro d' hd'
      rw [hA2set_eq, Finset.mem_singleton] at hd'
      rw [hd']
      have hbad : (2 - qdig7 m (lam3 * (lam2 * d5)) : ZMod 7)
          = etd7 m (lam2 * d1) (lam2 * d5) := by
        rw [hq5, hetd, runit7_mul, hlam2r, one_mul, hd5r]
        have hT2 : (k : ZMod 7) * (2 * s) = 2 * T := by
          rw [hT]
          ring
        rw [hT2, hT_eq]
        ring
      rw [hbad]
      rcases havoid with ⟨h4s, -⟩ | ⟨-, hb⟩
      · exfalso
        rw [hd5r] at h4s
        exact absurd (mul_right_cancel₀ hs h4s) (by decide)
      · exact hb
    have hA2len : apLen A2set = 1 := by
      rw [hA2set_eq]
      exact le_antisymm (case62_apLen_single _)
        (case62_apLen_pos ⟨_, Finset.mem_singleton_self _⟩)
    have hA4len : apLen A4set = 0 := by
      show apLen ((C.filter fun d' => runit7 d' = 4 * s).image (qdig7 m)) = 0
      rw [h4empty, Finset.image_empty, apLen_empty]
    obtain ⟨t, ht⟩ := lemma6 (s := 1) (by decide) h1mem hA1cyc
      (Or.inr (Or.inl ⟨hapLen1, hA2len, hA4len, hside⟩))
    obtain ⟨lam0, hlam0mem, hgood⟩ :=
      exists_lambda0_of_shift hm0 hs hunitC hclsC t ht
    refine ⟨lam0 * (lam3 * lam2),
      Nat.prime_seven.not_dvd_mul
        (not_dvd_of_mem_multLow7_zero hm0 hlam0mem)
        (Nat.prime_seven.not_dvd_mul hlam3nd hlam2), ?_⟩
    have hCeq : C = A.image (fun d => (lam3 * lam2) * d) := by
      rw [hC]
      exact Finset.image_congr fun d _ => (mul_assoc lam3 lam2 d).symm
    rw [hCeq] at hgood
    exact case62_good7_of_image hgood
  · -- `A₄` configuration: `r(d5) = 4s`, the `(5,0,1)` case of `lemma6`
    have h2empty : (C.filter fun d' => runit7 d' = 2 * s) = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro d' hd'
      rw [Finset.mem_filter] at hd'
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hd'.1
      rw [runit7_mul, runit7_mul, hlam3r, one_mul, hlam2r, one_mul] at hd'
      rcases hother d hd with rfl | hcls
      · rw [hd5r] at hd'
        exact absurd (mul_right_cancel₀ hs hd'.2) (by decide)
      · rw [hcls] at hd'
        exact absurd (mul_right_cancel₀ hs
          (show (1 : ZMod 7) * s = 2 * s by
            rw [one_mul]; exact hd'.2)) (by decide)
    have h4sub : (C.filter fun d' => runit7 d' = 4 * s)
        ⊆ {lam3 * (lam2 * d5)} := by
      intro d' hd'
      rw [Finset.mem_filter] at hd'
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hd'.1
      rw [runit7_mul, runit7_mul, hlam3r, one_mul, hlam2r, one_mul] at hd'
      rcases hother d hd with rfl | hcls
      · exact Finset.mem_singleton_self _
      · rw [hcls] at hd'
        exact absurd (mul_right_cancel₀ hs
          (show (1 : ZMod 7) * s = 4 * s by
            rw [one_mul]; exact hd'.2)) (by decide)
    have hd5mem4 : lam3 * (lam2 * d5)
        ∈ C.filter fun d' => runit7 d' = 4 * s := by
      rw [Finset.mem_filter]
      refine ⟨hd5C, ?_⟩
      rw [runit7_mul, runit7_mul, hlam3r, one_mul, hlam2r, one_mul]
      exact hd5r
    have hA4eq : (C.filter fun d' => runit7 d' = 4 * s)
        = {lam3 * (lam2 * d5)} :=
      Finset.Subset.antisymm h4sub
        (Finset.singleton_subset_iff.mpr hd5mem4)
    have hA4set_eq : A4set = {qdig7 m (lam3 * (lam2 * d5))} := by
      rw [hA4set, hA4eq, Finset.image_singleton]
    -- the `(5,0,1)` side condition: `2·q(d5''') − 1 ∉ {4,6}`
    have hetd : etd7 m (lam2 * d5) (lam2 * d1)
        = 2 * qdig7 m (lam2 * d5) - qdig7 m (lam2 * d1) := by
      unfold etd7
      rw [if_pos (by
        rw [runit7_mul, runit7_mul, hlam2r, one_mul, one_mul, hr1, hd5r]
        rw [show (2 : ZMod 7) * (4 * s) = (2 * 4) * s by ring,
          show (2 : ZMod 7) * 4 = 1 by decide, one_mul])]
    have hside : ∀ d' ∈ A4set,
        (2 * d' - 1 : ZMod 7) ∉ ({4, 6} : Finset (ZMod 7)) := by
      intro d' hd'
      rw [hA4set_eq, Finset.mem_singleton] at hd'
      rw [hd']
      have hbad : (2 * qdig7 m (lam3 * (lam2 * d5)) - 1 : ZMod 7)
          = etd7 m (lam2 * d5) (lam2 * d1) := by
        rw [hq5, hetd, runit7_mul, hlam2r, one_mul, hd5r]
        have hT4 : (k : ZMod 7) * (4 * s) = 4 * T := by
          rw [hT]
          ring
        rw [hT4, hT_eq]
        have h7 : (7 : ZMod 7) = 0 := by decide
        have hdiff : 2 * (qdig7 m (lam2 * d5)
              + 4 * (1 - qdig7 m (lam2 * d1))) - 1
            - (2 * qdig7 m (lam2 * d5) - qdig7 m (lam2 * d1))
            = 7 * (1 - qdig7 m (lam2 * d1)) := by ring
        rw [h7, zero_mul] at hdiff
        exact sub_eq_zero.mp hdiff
      rw [hbad]
      rcases havoid with ⟨-, hb⟩ | ⟨h2s, -⟩
      · exact hb
      · exfalso
        rw [hd5r] at h2s
        exact absurd (mul_right_cancel₀ hs h2s) (by decide)
    have hA4len : apLen A4set = 1 := by
      rw [hA4set_eq]
      exact le_antisymm (case62_apLen_single _)
        (case62_apLen_pos ⟨_, Finset.mem_singleton_self _⟩)
    have hA2len : apLen A2set = 0 := by
      show apLen ((C.filter fun d' => runit7 d' = 2 * s).image (qdig7 m)) = 0
      rw [h2empty, Finset.image_empty, apLen_empty]
    obtain ⟨t, ht⟩ := lemma6 (s := 1) (by decide) h1mem hA1cyc
      (Or.inl ⟨hapLen1, hA2len, hA4len, hside⟩)
    obtain ⟨lam0, hlam0mem, hgood⟩ :=
      exists_lambda0_of_shift hm0 hs hunitC hclsC t ht
    refine ⟨lam0 * (lam3 * lam2),
      Nat.prime_seven.not_dvd_mul
        (not_dvd_of_mem_multLow7_zero hm0 hlam0mem)
        (Nat.prime_seven.not_dvd_mul hlam3nd hlam2), ?_⟩
    have hCeq : C = A.image (fun d => (lam3 * lam2) * d) := by
      rw [hC]
      exact Finset.image_congr fun d _ => (mul_assoc lam3 lam2 d).symm
    rw [hCeq] at hgood
    exact case62_good7_of_image hgood

/-- **Tail-6'**: the generalised exceptional route.  The four `s`-class
elements `{a,b₁,b₂,b₃}` have `lam2`-digits `{t, t+v₁, t+v₂, t+v₃}` (a
`apLen = 5` translate inside `cycIv 1 5`), `a'` is the digit-`1` anchor
(`q''(a') = 1`), and `lam2` (unit `u`) already avoids the `ẽ`
obstruction for `d5`.  The `(5,1,0)`/`(5,0,1)` cases of `lemma6`
finish as in `case62_tail6`. -/
private theorem case62_tail6' {m : ℕ} (hm : 2 ≤ m) {A : Finset ℕ}
    (hpos : ∀ d ∈ A, 0 < d)
    (hunit : ∀ d ∈ A, padicValNat 7 d = 0)
    {s : ZMod 7} (hs : s ≠ 0)
    {d5 : ℕ} (hd5 : d5 ∈ A)
    (hd5cls : runit7 d5 ∈ ({2 * s, 4 * s} : Finset (ZMod 7)))
    (hother : ∀ d ∈ A, d = d5 ∨ runit7 d = s)
    (hne : ∃ d ∈ A, runit7 d = s)
    {a b1 b2 b3 a' : ℕ}
    (ha : a ∈ A) (hb1 : b1 ∈ A) (hb2 : b2 ∈ A) (hb3 : b3 ∈ A)
    (ha' : a' ∈ A)
    (hra : runit7 a = s) (hr1 : runit7 b1 = s) (hr2 : runit7 b2 = s)
    (hr3 : runit7 b3 = s) (hra' : runit7 a' = s)
    (hcover : ∀ d ∈ A, runit7 d = s → d ∈ ({a, b1, b2, b3} : Finset ℕ))
    {lam2 : ℕ} (hlam2 : ¬ 7 ∣ lam2)
    {u : ZMod 7} (hlam2u : runit7 lam2 = u) (hu : u ≠ 0)
    {t v1 v2 v3 : ZMod 7}
    (hq1 : qdig7 m (lam2 * b1) - qdig7 m (lam2 * a) = v1)
    (hq2 : qdig7 m (lam2 * b2) - qdig7 m (lam2 * a) = v2)
    (hq3 : qdig7 m (lam2 * b3) - qdig7 m (lam2 * a) = v3)
    (hqa' : qdig7 m (lam2 * a') - qdig7 m (lam2 * a) = 1 - t)
    (hS_len : apLen ({t, t + v1, t + v2, t + v3} : Finset (ZMod 7)) = 5)
    (hS_cyc : ({t, t + v1, t + v2, t + v3} : Finset (ZMod 7))
      ⊆ cycIv 1 5)
    (havoid : (runit7 d5 = 4 * s ∧
        etd7 m (lam2 * d5) (lam2 * a') ∉ ({4, 6} : Finset (ZMod 7)))
      ∨ (runit7 d5 = 2 * s ∧
        etd7 m (lam2 * a') (lam2 * d5) ∉ ({2, 3} : Finset (ZMod 7)))) :
    ∃ lam : ℕ, ¬ 7 ∣ lam ∧ good7 m lam A := by
  classical
  have hm0 : 0 < m := by omega
  have hlam2pos : 0 < lam2 :=
    Nat.pos_of_ne_zero (fun h0 => hlam2 (h0 ▸ dvd_zero _))
  have hus : u * s ≠ 0 := mul_ne_zero hu hs
  -- `lam3 ∈ Λ₀` normalises `q(lam2·a)` to `t`
  have hνz : padicValNat 7 (lam2 * a) = 0 := by
    rw [padicValNat_mul_seven hlam2 (ne_of_gt (hpos a ha))]
    exact hunit a ha
  obtain ⟨k, hk7, hkn⟩ := exists_multLow_set_qdig (j := 0) hm0 hνz
    (ne_of_gt (Nat.mul_pos hlam2pos (hpos a ha))) t
  rw [Nat.sub_zero] at hkn
  set lam3 := 1 + k * 7 ^ m with hlam3
  have hlam3r : runit7 lam3 = 1 := runit7_multLow hm0
  have hlam3nd : ¬ 7 ∣ lam3 := multLow_not_dvd hm0
  have hlam3pos : 0 < lam3 :=
    Nat.pos_of_ne_zero (fun h0 => hlam3nd (h0 ▸ dvd_zero _))
  have hva : qdig7 m (lam3 * (lam2 * a)) = t := hkn
  set T : ZMod 7 := (k : ZMod 7) * (u * s) with hT
  have hT_eq : T = t - qdig7 m (lam2 * a) := by
    have h := qdig7_lambda0 (m := m) (d := lam2 * a) (k := k) hνz
    have hkn' := hkn
    rw [hlam3] at hkn'
    rw [h] at hkn'
    rw [runit7_mul, hlam2u, hra] at hkn'
    rw [hT, ← hkn']
    ring
  -- `q''(x) = q(lam2·x) − q(lam2·a) + t` for `x ∈ A` in class `s`
  have hq'' : ∀ x ∈ A, runit7 x = s →
      qdig7 m (lam3 * (lam2 * x)) =
        (qdig7 m (lam2 * x) - qdig7 m (lam2 * a)) + t := by
    intro x hxA hrx
    have hνi : padicValNat 7 (lam2 * x) = 0 := by
      rw [padicValNat_mul_seven hlam2 (ne_of_gt (hpos x hxA))]
      exact hunit x hxA
    have hqq : qdig7 m (lam3 * (lam2 * x))
        = qdig7 m (lam2 * x) + (k : ZMod 7) * runit7 (lam2 * x) := by
      rw [hlam3]
      exact qdig7_lambda0 hνi
    rw [hqq, runit7_mul, hlam2u, hrx, ← hT, hT_eq]
    ring
  have hv1 : qdig7 m (lam3 * (lam2 * b1)) = t + v1 := by
    rw [hq'' b1 hb1 hr1, hq1]
    ring
  have hv2 : qdig7 m (lam3 * (lam2 * b2)) = t + v2 := by
    rw [hq'' b2 hb2 hr2, hq2]
    ring
  have hv3 : qdig7 m (lam3 * (lam2 * b3)) = t + v3 := by
    rw [hq'' b3 hb3 hr3, hq3]
    ring
  have hva' : qdig7 m (lam3 * (lam2 * a')) = 1 := by
    rw [hq'' a' ha' hra', hqa']
    ring
  -- the scaled set `C = lam3·lam2·A` and its class filters
  set C := A.image (fun d => lam3 * (lam2 * d)) with hC
  have hunitC : ∀ d' ∈ C, padicValNat 7 d' = 0 := by
    intro d' hd'
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hd'
    rw [padicValNat_mul_seven hlam3nd
      (ne_of_gt (Nat.mul_pos hlam2pos (hpos d hd))),
      padicValNat_mul_seven hlam2 (ne_of_gt (hpos d hd))]
    exact hunit d hd
  have hclsC : ∀ d' ∈ C,
      runit7 d' ∈ ({u * s, 2 * (u * s), 4 * (u * s)} : Finset (ZMod 7)) := by
    intro d' hd'
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hd'
    rw [runit7_mul, runit7_mul, hlam3r, one_mul, hlam2u]
    rcases hother d hd with rfl | hcls
    · rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton]
      rcases Finset.mem_insert.mp hd5cls with h2 | h4
      · exact Or.inr (Or.inl (by rw [h2]; ring))
      · exact Or.inr (Or.inr
          (by rw [Finset.mem_singleton.mp h4]; ring))
    · rw [hcls]
      exact Finset.mem_insert.mpr (Or.inl rfl)
  set A1set := (C.filter fun d' => runit7 d' = u * s).image (qdig7 m)
    with hA1set
  set A2set := (C.filter fun d' => runit7 d' = 2 * (u * s)).image (qdig7 m)
    with hA2set
  set A4set := (C.filter fun d' => runit7 d' = 4 * (u * s)).image (qdig7 m)
    with hA4set
  have hfilter_mem : ∀ i : ℕ, i ∈ ({a, b1, b2, b3} : Finset ℕ) →
      lam3 * (lam2 * i) ∈ C.filter fun d' => runit7 d' = u * s := by
    intro i hi
    rcases case62_cover4 hi with h | h | h | h
    · rw [h, Finset.mem_filter]
      refine ⟨Finset.mem_image.mpr ⟨a, ha, rfl⟩, ?_⟩
      rw [runit7_mul, runit7_mul, hlam3r, one_mul, hlam2u, hra]
    · rw [h, Finset.mem_filter]
      refine ⟨Finset.mem_image.mpr ⟨b1, hb1, rfl⟩, ?_⟩
      rw [runit7_mul, runit7_mul, hlam3r, one_mul, hlam2u, hr1]
    · rw [h, Finset.mem_filter]
      refine ⟨Finset.mem_image.mpr ⟨b2, hb2, rfl⟩, ?_⟩
      rw [runit7_mul, runit7_mul, hlam3r, one_mul, hlam2u, hr2]
    · rw [h, Finset.mem_filter]
      refine ⟨Finset.mem_image.mpr ⟨b3, hb3, rfl⟩, ?_⟩
      rw [runit7_mul, runit7_mul, hlam3r, one_mul, hlam2u, hr3]
  have hfa' : lam3 * (lam2 * a') ∈ C.filter fun d' => runit7 d' = u * s := by
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_image.mpr ⟨a', ha', rfl⟩, ?_⟩
    rw [runit7_mul, runit7_mul, hlam3r, one_mul, hlam2u, hra']
  have hA1eq : A1set
      = ({t, t + v1, t + v2, t + v3} : Finset (ZMod 7)) := by
    apply Finset.Subset.antisymm
    · intro x hx
      rw [hA1set] at hx
      obtain ⟨d', hd', rfl⟩ := Finset.mem_image.mp hx
      have hd'C := case62_filter_subset hd'
      have hd'r := (Finset.mem_filter.mp hd').2
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hd'C
      rw [runit7_mul, runit7_mul, hlam3r, one_mul, hlam2u] at hd'r
      have hrd : runit7 d = s := mul_left_cancel₀ hu hd'r
      have hmem := hcover d hd hrd
      rcases case62_cover4 hmem with h | h | h | h
      · rw [h, hva]
        exact Finset.mem_insert.mpr (Or.inl rfl)
      · rw [h, hv1]
        exact Finset.mem_insert.mpr
          (Or.inr (Finset.mem_insert.mpr (Or.inl rfl)))
      · rw [h, hv2]
        exact Finset.mem_insert.mpr
          (Or.inr (Finset.mem_insert.mpr (Or.inr
            (Finset.mem_insert.mpr (Or.inl rfl)))))
      · rw [h, hv3]
        exact Finset.mem_insert.mpr
          (Or.inr (Finset.mem_insert.mpr (Or.inr
            (Finset.mem_insert.mpr (Or.inr
              (Finset.mem_singleton_self _))))))
    · intro x hx
      rw [hA1set]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact Finset.mem_image.mpr
          ⟨lam3 * (lam2 * a), hfilter_mem a (by simp), hva⟩
      · exact Finset.mem_image.mpr
          ⟨lam3 * (lam2 * b1), hfilter_mem b1 (by simp), hv1⟩
      · exact Finset.mem_image.mpr
          ⟨lam3 * (lam2 * b2), hfilter_mem b2 (by simp), hv2⟩
      · exact Finset.mem_image.mpr
          ⟨lam3 * (lam2 * b3), hfilter_mem b3 (by simp), hv3⟩
  have hapLen1 : apLen A1set = 5 := by
    rw [hA1eq]
    exact hS_len
  have hA1cyc : A1set ⊆ cycIv 1 (apLen A1set) := by
    rw [hapLen1, hA1eq]
    exact hS_cyc
  have h1mem : (1 : ZMod 7) ∈ A1set := by
    rw [hA1set]
    exact Finset.mem_image.mpr ⟨lam3 * (lam2 * a'), hfa', hva'⟩
  -- `d5`'s class decides the configuration
  have hd5r : runit7 d5 = 2 * s ∨ runit7 d5 = 4 * s := by
    have h := hd5cls
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hν5 : padicValNat 7 (lam2 * d5) = 0 := by
    rw [padicValNat_mul_seven hlam2 (ne_of_gt (hpos d5 hd5))]
    exact hunit d5 hd5
  have hq5 : qdig7 m (lam3 * (lam2 * d5))
      = qdig7 m (lam2 * d5) + (k : ZMod 7) * runit7 (lam2 * d5) := by
    rw [hlam3]
    exact qdig7_lambda0 hν5
  have hd5C : lam3 * (lam2 * d5) ∈ C :=
    Finset.mem_image.mpr ⟨d5, hd5, rfl⟩
  rcases hd5r with hd5r | hd5r
  · -- `A₂` configuration: `r(d5) = 2s`, the `(5,1,0)` case of `lemma6`
    have h4empty : (C.filter fun d' => runit7 d' = 4 * (u * s)) = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro d' hd'
      rw [Finset.mem_filter] at hd'
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hd'.1
      rw [runit7_mul, runit7_mul, hlam3r, one_mul, hlam2u] at hd'
      rcases hother d hd with rfl | hcls
      · rw [hd5r] at hd'
        have hcontra : u * (2 * s) = 4 * (u * s) := hd'.2
        have hcontra' : (2 : ZMod 7) = 4 :=
          mul_right_cancel₀ hus (by linear_combination hcontra)
        exact absurd hcontra' (by decide)
      · rw [hcls] at hd'
        have hcontra : u * s = 4 * (u * s) := hd'.2
        have hcontra' : (1 : ZMod 7) = 4 :=
          mul_right_cancel₀ hus (by linear_combination hcontra)
        exact absurd hcontra' (by decide)
    have h2sub : (C.filter fun d' => runit7 d' = 2 * (u * s))
        ⊆ {lam3 * (lam2 * d5)} := by
      intro d' hd'
      rw [Finset.mem_filter] at hd'
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hd'.1
      rw [runit7_mul, runit7_mul, hlam3r, one_mul, hlam2u] at hd'
      rcases hother d hd with rfl | hcls
      · exact Finset.mem_singleton_self _
      · rw [hcls] at hd'
        have hcontra : u * s = 2 * (u * s) := hd'.2
        have hcontra' : (1 : ZMod 7) = 2 :=
          mul_right_cancel₀ hus (by linear_combination hcontra)
        exact absurd hcontra' (by decide)
    have hd5mem2 : lam3 * (lam2 * d5)
        ∈ C.filter fun d' => runit7 d' = 2 * (u * s) := by
      rw [Finset.mem_filter]
      refine ⟨hd5C, ?_⟩
      rw [runit7_mul, runit7_mul, hlam3r, one_mul, hlam2u, hd5r]
      ring
    have hA2eq : (C.filter fun d' => runit7 d' = 2 * (u * s))
        = {lam3 * (lam2 * d5)} :=
      Finset.Subset.antisymm h2sub
        (Finset.singleton_subset_iff.mpr hd5mem2)
    have hA2set_eq : A2set = {qdig7 m (lam3 * (lam2 * d5))} := by
      rw [hA2set, hA2eq, Finset.image_singleton]
    -- the `(5,1,0)` side condition: `2 − q(d5''') ∉ {2,3}`
    have hetd : etd7 m (lam2 * a') (lam2 * d5)
        = 2 * qdig7 m (lam2 * a') - qdig7 m (lam2 * d5) := by
      unfold etd7
      rw [if_pos (by
        rw [runit7_mul, runit7_mul, hlam2u, hra', hd5r]
        rw [show u * (2 * s) = 2 * (u * s) by ring])]
    have hside : ∀ d' ∈ A2set,
        (2 - d' : ZMod 7) ∉ ({2, 3} : Finset (ZMod 7)) := by
      intro d' hd'
      rw [hA2set_eq, Finset.mem_singleton] at hd'
      rw [hd']
      have hbad : (2 - qdig7 m (lam3 * (lam2 * d5)) : ZMod 7)
          = etd7 m (lam2 * a') (lam2 * d5) := by
        rw [hq5, hetd, runit7_mul, hlam2u, hd5r]
        rw [show (k : ZMod 7) * (u * (2 * s)) = 2 * T by rw [hT]; ring]
        have hE : qdig7 m (lam2 * a') = qdig7 m (lam2 * a) + (1 - t) := by
          linear_combination hqa'
        rw [hE, hT_eq]
        ring
      rw [hbad]
      rcases havoid with ⟨h4s, -⟩ | ⟨-, hb⟩
      · exfalso
        rw [hd5r] at h4s
        exact absurd (mul_right_cancel₀ hs h4s) (by decide)
      · exact hb
    have hA2len : apLen A2set = 1 := by
      rw [hA2set_eq]
      exact le_antisymm (case62_apLen_single _)
        (case62_apLen_pos ⟨_, Finset.mem_singleton_self _⟩)
    have hA4len : apLen A4set = 0 := by
      show apLen ((C.filter fun d' => runit7 d' = 4 * (u * s)).image
          (qdig7 m)) = 0
      rw [h4empty, Finset.image_empty, apLen_empty]
    obtain ⟨t', ht'⟩ := lemma6 (s := 1) (by decide) h1mem hA1cyc
      (Or.inr (Or.inl ⟨hapLen1, hA2len, hA4len, hside⟩))
    obtain ⟨lam0, hlam0mem, hgood⟩ :=
      exists_lambda0_of_shift hm0 hus hunitC hclsC t' ht'
    refine ⟨lam0 * (lam3 * lam2),
      Nat.prime_seven.not_dvd_mul
        (not_dvd_of_mem_multLow7_zero hm0 hlam0mem)
        (Nat.prime_seven.not_dvd_mul hlam3nd hlam2), ?_⟩
    have hCeq : C = A.image (fun d => (lam3 * lam2) * d) := by
      rw [hC]
      exact Finset.image_congr fun d _ => (mul_assoc lam3 lam2 d).symm
    rw [hCeq] at hgood
    exact case62_good7_of_image hgood
  · -- `A₄` configuration: `r(d5) = 4s`, the `(5,0,1)` case of `lemma6`
    have h2empty : (C.filter fun d' => runit7 d' = 2 * (u * s)) = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro d' hd'
      rw [Finset.mem_filter] at hd'
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hd'.1
      rw [runit7_mul, runit7_mul, hlam3r, one_mul, hlam2u] at hd'
      rcases hother d hd with rfl | hcls
      · rw [hd5r] at hd'
        have hcontra : u * (4 * s) = 2 * (u * s) := hd'.2
        have hcontra' : (4 : ZMod 7) = 2 :=
          mul_right_cancel₀ hus (by linear_combination hcontra)
        exact absurd hcontra' (by decide)
      · rw [hcls] at hd'
        have hcontra : u * s = 2 * (u * s) := hd'.2
        have hcontra' : (1 : ZMod 7) = 2 :=
          mul_right_cancel₀ hus (by linear_combination hcontra)
        exact absurd hcontra' (by decide)
    have h4sub : (C.filter fun d' => runit7 d' = 4 * (u * s))
        ⊆ {lam3 * (lam2 * d5)} := by
      intro d' hd'
      rw [Finset.mem_filter] at hd'
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hd'.1
      rw [runit7_mul, runit7_mul, hlam3r, one_mul, hlam2u] at hd'
      rcases hother d hd with rfl | hcls
      · exact Finset.mem_singleton_self _
      · rw [hcls] at hd'
        have hcontra : u * s = 4 * (u * s) := hd'.2
        have hcontra' : (1 : ZMod 7) = 4 :=
          mul_right_cancel₀ hus (by linear_combination hcontra)
        exact absurd hcontra' (by decide)
    have hd5mem4 : lam3 * (lam2 * d5)
        ∈ C.filter fun d' => runit7 d' = 4 * (u * s) := by
      rw [Finset.mem_filter]
      refine ⟨hd5C, ?_⟩
      rw [runit7_mul, runit7_mul, hlam3r, one_mul, hlam2u, hd5r]
      ring
    have hA4eq : (C.filter fun d' => runit7 d' = 4 * (u * s))
        = {lam3 * (lam2 * d5)} :=
      Finset.Subset.antisymm h4sub
        (Finset.singleton_subset_iff.mpr hd5mem4)
    have hA4set_eq : A4set = {qdig7 m (lam3 * (lam2 * d5))} := by
      rw [hA4set, hA4eq, Finset.image_singleton]
    -- the `(5,0,1)` side condition: `2·q(d5''') − 1 ∉ {4,6}`
    have hetd : etd7 m (lam2 * d5) (lam2 * a')
        = 2 * qdig7 m (lam2 * d5) - qdig7 m (lam2 * a') := by
      unfold etd7
      rw [if_pos (by
        rw [runit7_mul, runit7_mul, hlam2u, hra', hd5r]
        rw [show 2 * (u * (4 * s)) = u * s by
          rw [show u * (4 * s) = 4 * (u * s) by ring]
          have h24 : (2 : ZMod 7) * 4 = 1 := by decide
          linear_combination h24 * (u * s)])]
    have hside : ∀ d' ∈ A4set,
        (2 * d' - 1 : ZMod 7) ∉ ({4, 6} : Finset (ZMod 7)) := by
      intro d' hd'
      rw [hA4set_eq, Finset.mem_singleton] at hd'
      rw [hd']
      have hbad : (2 * qdig7 m (lam3 * (lam2 * d5)) - 1 : ZMod 7)
          = etd7 m (lam2 * d5) (lam2 * a') := by
        rw [hq5, hetd, runit7_mul, hlam2u, hd5r]
        rw [show (k : ZMod 7) * (u * (4 * s)) = 4 * T by rw [hT]; ring]
        have hE : qdig7 m (lam2 * a') = qdig7 m (lam2 * a) + (1 - t) := by
          linear_combination hqa'
        rw [hE, hT_eq]
        have h7 : (7 : ZMod 7) = 0 := by decide
        have hdiff : 2 * (qdig7 m (lam2 * d5)
              + 4 * (t - qdig7 m (lam2 * a))) - 1
            - (2 * qdig7 m (lam2 * d5)
                - (qdig7 m (lam2 * a) + (1 - t)))
            = 7 * (t - qdig7 m (lam2 * a)) := by ring
        rw [h7, zero_mul] at hdiff
        exact sub_eq_zero.mp hdiff
      rw [hbad]
      rcases havoid with ⟨-, hb⟩ | ⟨h2s, -⟩
      · exact hb
      · exfalso
        rw [hd5r] at h2s
        exact absurd (mul_right_cancel₀ hs h2s) (by decide)
    have hA4len : apLen A4set = 1 := by
      rw [hA4set_eq]
      exact le_antisymm (case62_apLen_single _)
        (case62_apLen_pos ⟨_, Finset.mem_singleton_self _⟩)
    have hA2len : apLen A2set = 0 := by
      show apLen ((C.filter fun d' => runit7 d' = 2 * (u * s)).image
          (qdig7 m)) = 0
      rw [h2empty, Finset.image_empty, apLen_empty]
    obtain ⟨t', ht'⟩ := lemma6 (s := 1) (by decide) h1mem hA1cyc
      (Or.inl ⟨hapLen1, hA2len, hA4len, hside⟩)
    obtain ⟨lam0, hlam0mem, hgood⟩ :=
      exists_lambda0_of_shift hm0 hus hunitC hclsC t' ht'
    refine ⟨lam0 * (lam3 * lam2),
      Nat.prime_seven.not_dvd_mul
        (not_dvd_of_mem_multLow7_zero hm0 hlam0mem)
        (Nat.prime_seven.not_dvd_mul hlam3nd hlam2), ?_⟩
    have hCeq : C = A.image (fun d => (lam3 * lam2) * d) := by
      rw [hC]
      exact Finset.image_congr fun d _ => (mul_assoc lam3 lam2 d).symm
    rw [hCeq] at hgood
    exact case62_good7_of_image hgood

/-! ### §9 The `lemma10` case (i): unequal levels -/

/-- **Case (i)**: `ν(e₂₁) > ν(e₃₁)` — the `lemma9_i'` route plus the
`e₃₁ = 0` triangle analysis. -/
private theorem case62_i {m : ℕ} (hm : 2 ≤ m) {A : Finset ℕ}
    (hpos : ∀ d ∈ A, 0 < d)
    (hunit : ∀ d ∈ A, padicValNat 7 d = 0)
    {s : ZMod 7} (hs : s ≠ 0)
    {d5 : ℕ} (hd5 : d5 ∈ A)
    (hd5cls : runit7 d5 ∈ ({2 * s, 4 * s} : Finset (ZMod 7)))
    (hother : ∀ d ∈ A, d = d5 ∨ runit7 d = s)
    (hne : ∃ d ∈ A, runit7 d = s)
    {d1 d2 d3 d4 : ℕ}
    (hd1 : d1 ∈ A) (hd2 : d2 ∈ A) (hd3 : d3 ∈ A) (hd4 : d4 ∈ A)
    (hr1 : runit7 d1 = s) (hr2 : runit7 d2 = s)
    (hr3 : runit7 d3 = s) (hr4 : runit7 d4 = s)
    (hcover : ∀ d ∈ A, runit7 d = s → d ∈ ({d1, d2, d3, d4} : Finset ℕ))
    (huneq : padicValNat 7 (eMod7 m d2 d1) >
      padicValNat 7 (eMod7 m d3 d1)) :
    ∃ lam : ℕ, ¬ 7 ∣ lam ∧ good7 m lam A := by
  classical
  have hm0 : 0 < m := by omega
  have hpos1 : 0 < d1 := hpos d1 hd1
  have hpos2 : 0 < d2 := hpos d2 hd2
  have hpos3 : 0 < d3 := hpos d3 hd3
  have hpos4 : 0 < d4 := hpos d4 hd4
  have hν1 : padicValNat 7 d1 = 0 := hunit d1 hd1
  have hν2 : padicValNat 7 d2 = 0 := hunit d2 hd2
  have hν3 : padicValNat 7 d3 = 0 := hunit d3 hd3
  have hν4 : padicValNat 7 d4 = 0 := hunit d4 hd4
  have he21 : eMod7 m d2 d1 ≠ 0 := by
    intro h0
    rw [h0] at huneq
    simp at huneq
  have h1ne : runit7 (1 : ℕ) ≠ 0 := by
    rw [runit7_eq_one_of_mod7 (by norm_num : (1 : ℕ) % 7 = 1)]
    exact one_ne_zero
  -- the `e31 = 0` congruence (any `7`-unit scalar)
  by_cases he31 : eMod7 m d3 d1 = 0
  · have hs31 : residueRelOf d3 d1 = residueRel.same :=
      case62_rel_same hs hr3 hr1
    have hq3eq : ∀ {c : ℕ}, runit7 c ≠ 0 →
        qdig7 m (c * d3) = qdig7 m (c * d1) := by
      intro c hc
      exact case62_qdig_eq_of_eMod7_zero hc hs31 he31
    by_cases he41 : eMod7 m d4 d1 = 0
    · -- `e31 = e41 = 0`: the image is `{q(d1), q(d2)}` — wrap `c = 1`
      have hs41 : residueRelOf d4 d1 = residueRel.same :=
        case62_rel_same hs hr4 hr1
      have hq3eq1 : qdig7 m (1 * d3) = qdig7 m (1 * d1) := hq3eq h1ne
      have hq4eq1 : qdig7 m (1 * d4) = qdig7 m (1 * d1) :=
        case62_qdig_eq_of_eMod7_zero h1ne hs41 he41
      exact case62_wrap hm0 hpos hunit hs hd5 hd5cls hother hne
        (by decide : ¬ (7 : ℕ) ∣ 1)
        (Q := {qdig7 m (1 * d1), qdig7 m (1 * d2)})
        (case62_pair_le4 _ _)
        (fun d hd hdr => by
          have h := hcover d hd hdr
          rcases case62_cover4 h with h | h | h | h
          · rw [h]
            exact Finset.mem_insert.mpr (Or.inl rfl)
          · rw [h]
            exact Finset.mem_insert.mpr
                (Or.inr (Finset.mem_singleton_self _))
          · rw [h, hq3eq1]
            exact Finset.mem_insert.mpr (Or.inl rfl)
          · rw [h, hq4eq1]
            exact Finset.mem_insert.mpr (Or.inl rfl))
    · -- `e41 ≠ 0`: triangle analysis on `{d2, d4}` through `d1`
      have hs21 : residueRelOf d2 d1 = residueRel.same :=
        case62_rel_same hs hr2 hr1
      have hs41 : residueRelOf d4 d1 = residueRel.same :=
        case62_rel_same hs hr4 hr1
      have hs14 : residueRelOf d1 d4 = residueRel.same :=
        case62_rel_same hs hr1 hr4
      have hs24 : residueRelOf d2 d4 = residueRel.same :=
        case62_rel_same hs hr2 hr4
      have he14ν : padicValNat 7 (eMod7 m d1 d4) =
          padicValNat 7 (eMod7 m d4 d1) := case62_enu7_sym hs41 hs14
      have he14 : eMod7 m d1 d4 ≠ 0 := by
        intro h0
        rw [h0] at he14ν
        simp at he14ν
        have hz : padicValNat 7 (eMod7 m d4 d1) = 0 := by omega
        have h7e : 7 ∣ eMod7 m d4 d1 :=
          case62_dvd7_same hν4 hν1 (hr4.trans hr1.symm) hs41
        rcases padicValNat.eq_zero_iff.mp hz with hp1 | h0e | hnd
        · norm_num at hp1
        · exact he41 h0e
        · exact hnd h7e
      have hr14 : runit7 (eMod7 m d1 d4) = - runit7 (eMod7 m d4 d1) :=
        case62_runit7_eMod7_neg hs41 hs14
      by_cases hνeq : padicValNat 7 (eMod7 m d4 d1) =
          padicValNat 7 (eMod7 m d2 d1)
      · -- common level `ℓ = ν(e21) = ν(e41)`
        set ℓ := padicValNat 7 (eMod7 m d2 d1) with hℓ
        have hℓm : ℓ ≤ m := enu7_le_of_ne he21
        by_cases huv : runit7 (eMod7 m d2 d1) = runit7 (eMod7 m d4 d1)
        · -- equal units: `e24 = 0` or `ν(e24) > ℓ`
          obtain he24 | hgt := case62_eMod7_level_gt_of_runit_eq
            hs21 hs41 hs24 he21 he41 rfl hνeq hℓm huv
          · -- `e24 = 0`: image ⊆ `{q(d1), q(d2)}` — wrap `c = 1`
            have hq3eq1 : qdig7 m (1 * d3) = qdig7 m (1 * d1) := hq3eq h1ne
            have hq4eq1 : qdig7 m (1 * d4) = qdig7 m (1 * d2) := by
              simp only [one_mul]
              exact qdig7_congr
                (case62_eq_resid_of_eMod7_eq_zero he24 hs24).symm
            exact case62_wrap hm0 hpos hunit hs hd5 hd5cls hother hne
              (by decide : ¬ (7 : ℕ) ∣ 1)
              (Q := {qdig7 m (1 * d1), qdig7 m (1 * d2)})
              (case62_pair_le4 _ _)
              (fun d hd hdr => by
                have h := hcover d hd hdr
                rcases case62_cover4 h with h | h | h | h
                · rw [h]
                  exact Finset.mem_insert.mpr (Or.inl rfl)
                · rw [h]
                  exact Finset.mem_insert.mpr
                      (Or.inr (Finset.mem_singleton_self _))
                · rw [h, hq3eq1]
                  exact Finset.mem_insert.mpr (Or.inl rfl)
                · rw [h, hq4eq1]
                  exact Finset.mem_insert.mpr
                      (Or.inr (Finset.mem_singleton_self _)))
          · -- `ν(e24) > ℓ = ν(e14)`: `lemma9_i'` on `(d2, d1, d4)`
            have he24 : eMod7 m d2 d4 ≠ 0 := by
              intro h0
              rw [h0] at hgt
              simp at hgt
            have hν24gt : padicValNat 7 (eMod7 m d1 d4) <
                padicValNat 7 (eMod7 m d2 d4) := by
              rw [he14ν, hνeq]
              exact hgt
            obtain ⟨lam', hlam', -, hap⟩ := lemma9_i'
              ⟨hpos2, hpos1, hpos4⟩
              ⟨hν2, hν1, hν4⟩
              ⟨hr2.trans hr1.symm, hr1.trans hr4.symm⟩
              (ne_of_gt hν24gt) ⟨he24, he14⟩
            have hlam'r : runit7 lam' ≠ 0 :=
              runit7_ne_zero (Nat.pos_of_ne_zero
                (fun h0 => hlam' (h0 ▸ dvd_zero _)))
            have hq3eq' : qdig7 m (lam' * d3) = qdig7 m (lam' * d1) :=
              hq3eq hlam'r
            exact case62_wrap hm0 hpos hunit hs hd5 hd5cls hother hne hlam'
              (Q := ({d2, d1, d4} : Finset ℕ).image
                (fun d => qdig7 m (lam' * d)))
              (le_trans hap (by decide))
              (fun d hd hdr => by
                have h := hcover d hd hdr
                rcases case62_cover4 h with h | h | h | h
                · rw [h]
                  exact Finset.mem_image.mpr ⟨d1, by simp, rfl⟩
                · rw [h]
                  exact Finset.mem_image.mpr ⟨d2, by simp, rfl⟩
                · rw [h, hq3eq']
                  exact Finset.mem_image.mpr ⟨d1, by simp, rfl⟩
                · rw [h]
                  exact Finset.mem_image.mpr ⟨d4, by simp, rfl⟩)
        · -- distinct units: `e24` has level `ℓ` and unit `u − v`
          obtain ⟨he24, hν24, hr24⟩ := case62_eMod7_level_of_runit_ne
            hs21 hs41 hs24 he21 he41 rfl hνeq hℓm huv
          have hu0 : runit7 (eMod7 m d2 d1) ≠ 0 :=
            runit7_ne_zero (Nat.pos_of_ne_zero he21)
          have hv0 : runit7 (eMod7 m d4 d1) ≠ 0 :=
            runit7_ne_zero (Nat.pos_of_ne_zero he41)
          rcases lt_or_eq_of_le hℓm with hlt | heq
          · -- `ℓ < m`: the `lemma9_ii` ratio dispatch
            have hratio := case62_ratio_pairs _ _ hu0 hv0 huv
            rcases hratio with hr | hr | hr | hr | hr
            · -- `v = 2u`: `lemma9_ii` on `(d2, d4, d1)`, `j = 2`
              obtain ⟨lam', hlam', -, -, -, hap⟩ := lemma9_ii
                ⟨hpos2, hpos4, hpos1⟩ ⟨hν2, hν4, hν1⟩
                ⟨hr2.trans hr4.symm, hr4.trans hr1.symm⟩
                hνeq.symm (by rw [hνeq]; exact hlt) (Or.inl rfl)
                (show runit7 (eMod7 m d4 d1) =
                  (2 : ZMod 7) * runit7 (eMod7 m d2 d1) from hr)
              have hlam'r : runit7 lam' ≠ 0 :=
                runit7_ne_zero (Nat.pos_of_ne_zero
                  (fun h0 => hlam' (h0 ▸ dvd_zero _)))
              have hq3eq' : qdig7 m (lam' * d3) = qdig7 m (lam' * d1) :=
                hq3eq hlam'r
              exact case62_wrap hm0 hpos hunit hs hd5 hd5cls hother hne
                hlam'
                (Q := ({d2, d4, d1} : Finset ℕ).image
                  (fun d => qdig7 m (lam' * d)))
                (le_trans hap (by decide))
                (fun d hd hdr => by
                  have h := hcover d hd hdr
                  rcases case62_cover4 h with h | h | h | h
                  · rw [h]
                    exact Finset.mem_image.mpr ⟨d1, by simp, rfl⟩
                  · rw [h]
                    exact Finset.mem_image.mpr ⟨d2, by simp, rfl⟩
                  · rw [h, hq3eq']
                    exact Finset.mem_image.mpr ⟨d1, by simp, rfl⟩
                  · rw [h]
                    exact Finset.mem_image.mpr ⟨d4, by simp, rfl⟩)
            · -- `v = 3u`: `lemma9_ii` on `(d2, d4, d1)`, `j = 3`
              obtain ⟨lam', hlam', -, -, -, hap⟩ := lemma9_ii
                ⟨hpos2, hpos4, hpos1⟩ ⟨hν2, hν4, hν1⟩
                ⟨hr2.trans hr4.symm, hr4.trans hr1.symm⟩
                hνeq.symm (by rw [hνeq]; exact hlt) (Or.inr rfl)
                (show runit7 (eMod7 m d4 d1) =
                  (3 : ZMod 7) * runit7 (eMod7 m d2 d1) from hr)
              have hlam'r : runit7 lam' ≠ 0 :=
                runit7_ne_zero (Nat.pos_of_ne_zero
                  (fun h0 => hlam' (h0 ▸ dvd_zero _)))
              have hq3eq' : qdig7 m (lam' * d3) = qdig7 m (lam' * d1) :=
                hq3eq hlam'r
              exact case62_wrap hm0 hpos hunit hs hd5 hd5cls hother hne
                hlam'
                (Q := ({d2, d4, d1} : Finset ℕ).image
                  (fun d => qdig7 m (lam' * d)))
                (le_trans hap (by decide))
                (fun d hd hdr => by
                  have h := hcover d hd hdr
                  rcases case62_cover4 h with h | h | h | h
                  · rw [h]
                    exact Finset.mem_image.mpr ⟨d1, by simp, rfl⟩
                  · rw [h]
                    exact Finset.mem_image.mpr ⟨d2, by simp, rfl⟩
                  · rw [h, hq3eq']
                    exact Finset.mem_image.mpr ⟨d1, by simp, rfl⟩
                  · rw [h]
                    exact Finset.mem_image.mpr ⟨d4, by simp, rfl⟩)
            · -- `u = 2v`: `lemma9_ii` on `(d4, d2, d1)`, `j = 2`
              obtain ⟨lam', hlam', -, -, -, hap⟩ := lemma9_ii
                ⟨hpos4, hpos2, hpos1⟩ ⟨hν4, hν2, hν1⟩
                ⟨hr4.trans hr2.symm, hr2.trans hr1.symm⟩
                hνeq hlt (Or.inl rfl)
                (show runit7 (eMod7 m d2 d1) =
                  (2 : ZMod 7) * runit7 (eMod7 m d4 d1) from hr)
              have hlam'r : runit7 lam' ≠ 0 :=
                runit7_ne_zero (Nat.pos_of_ne_zero
                  (fun h0 => hlam' (h0 ▸ dvd_zero _)))
              have hq3eq' : qdig7 m (lam' * d3) = qdig7 m (lam' * d1) :=
                hq3eq hlam'r
              exact case62_wrap hm0 hpos hunit hs hd5 hd5cls hother hne
                hlam'
                (Q := ({d4, d2, d1} : Finset ℕ).image
                  (fun d => qdig7 m (lam' * d)))
                (le_trans hap (by decide))
                (fun d hd hdr => by
                  have h := hcover d hd hdr
                  rcases case62_cover4 h with h | h | h | h
                  · rw [h]
                    exact Finset.mem_image.mpr ⟨d1, by simp, rfl⟩
                  · rw [h]
                    exact Finset.mem_image.mpr ⟨d2, by simp, rfl⟩
                  · rw [h, hq3eq']
                    exact Finset.mem_image.mpr ⟨d1, by simp, rfl⟩
                  · rw [h]
                    exact Finset.mem_image.mpr ⟨d4, by simp, rfl⟩)
            · -- `u = 3v`: `lemma9_ii` on `(d4, d2, d1)`, `j = 3`
              obtain ⟨lam', hlam', -, -, -, hap⟩ := lemma9_ii
                ⟨hpos4, hpos2, hpos1⟩ ⟨hν4, hν2, hν1⟩
                ⟨hr4.trans hr2.symm, hr2.trans hr1.symm⟩
                hνeq hlt (Or.inr rfl)
                (show runit7 (eMod7 m d2 d1) =
                  (3 : ZMod 7) * runit7 (eMod7 m d4 d1) from hr)
              have hlam'r : runit7 lam' ≠ 0 :=
                runit7_ne_zero (Nat.pos_of_ne_zero
                  (fun h0 => hlam' (h0 ▸ dvd_zero _)))
              have hq3eq' : qdig7 m (lam' * d3) = qdig7 m (lam' * d1) :=
                hq3eq hlam'r
              exact case62_wrap hm0 hpos hunit hs hd5 hd5cls hother hne
                hlam'
                (Q := ({d4, d2, d1} : Finset ℕ).image
                  (fun d => qdig7 m (lam' * d)))
                (le_trans hap (by decide))
                (fun d hd hdr => by
                  have h := hcover d hd hdr
                  rcases case62_cover4 h with h | h | h | h
                  · rw [h]
                    exact Finset.mem_image.mpr ⟨d1, by simp, rfl⟩
                  · rw [h]
                    exact Finset.mem_image.mpr ⟨d2, by simp, rfl⟩
                  · rw [h, hq3eq']
                    exact Finset.mem_image.mpr ⟨d1, by simp, rfl⟩
                  · rw [h]
                    exact Finset.mem_image.mpr ⟨d4, by simp, rfl⟩)
            · -- `v = −u`: `lemma9_ii` on `(d1, d2, d4)`, `j = 2`
              have hr14' : runit7 (eMod7 m d1 d4) =
                  runit7 (eMod7 m d2 d1) := by
                rw [hr14, hr, neg_neg]
              have hr24' : runit7 (eMod7 m d2 d4) =
                  (2 : ZMod 7) * runit7 (eMod7 m d1 d4) := by
                rw [hr24, hr14', hr]
                ring
              obtain ⟨lam', hlam', -, -, -, hap⟩ := lemma9_ii
                ⟨hpos1, hpos2, hpos4⟩ ⟨hν1, hν2, hν4⟩
                ⟨hr1.trans hr2.symm, hr2.trans hr4.symm⟩
                (by rw [he14ν, hνeq, hν24])
                (by rw [hν24]; exact hlt) (Or.inl rfl) hr24'
              have hlam'r : runit7 lam' ≠ 0 :=
                runit7_ne_zero (Nat.pos_of_ne_zero
                  (fun h0 => hlam' (h0 ▸ dvd_zero _)))
              have hq3eq' : qdig7 m (lam' * d3) = qdig7 m (lam' * d1) :=
                hq3eq hlam'r
              exact case62_wrap hm0 hpos hunit hs hd5 hd5cls hother hne
                hlam'
                (Q := ({d1, d2, d4} : Finset ℕ).image
                  (fun d => qdig7 m (lam' * d)))
                (le_trans hap (by decide))
                (fun d hd hdr => by
                  have h := hcover d hd hdr
                  rcases case62_cover4 h with h | h | h | h
                  · rw [h]
                    exact Finset.mem_image.mpr ⟨d1, by simp, rfl⟩
                  · rw [h]
                    exact Finset.mem_image.mpr ⟨d2, by simp, rfl⟩
                  · rw [h, hq3eq']
                    exact Finset.mem_image.mpr ⟨d1, by simp, rfl⟩
                  · rw [h]
                    exact Finset.mem_image.mpr ⟨d4, by simp, rfl⟩)
          · -- `ℓ = m`: rescale `c` so `{0, c·u, c·v}` fits a 4-interval
            obtain ⟨w, hw0, hapw⟩ := case62_pair_rescale
              (runit7 (eMod7 m d2 d1)) (runit7 (eMod7 m d4 d1)) hu0
            set c := w.val with hcdef
            have hcpos : 0 < c := by
              rw [hcdef]
              exact Nat.pos_of_ne_zero (mt (ZMod.val_eq_zero w).mp hw0)
            have hc7 : ¬ 7 ∣ c := by
              rw [hcdef]
              intro hd
              exact hw0 ((ZMod.val_eq_zero w).mp
                (Nat.eq_zero_of_dvd_of_lt hd (ZMod.val_lt w)))
            have hνc : padicValNat 7 c = 0 :=
              padicValNat.eq_zero_of_not_dvd hc7
            have hrc : (c : ZMod 7) = w := by
              rw [hcdef, ZMod.natCast_zmod_val]
            have hrc0 : runit7 c ≠ 0 := by
              rw [case62_runit7_eq_cast hνc, hrc]
              exact hw0
            have hq2s : qdig7 m (c * d2) - qdig7 m (c * d1)
                = w * runit7 (eMod7 m d2 d1) := by
              have h := case62_qdig_sub_smul_top (by omega) hνc
                (ne_of_gt hcpos) hs21 he21 heq
              rwa [hrc] at h
            have hq4s : qdig7 m (c * d4) - qdig7 m (c * d1)
                = w * runit7 (eMod7 m d4 d1) := by
              have h := case62_qdig_sub_smul_top (by omega) hνc
                (ne_of_gt hcpos) hs41 he41 (hνeq.trans heq)
              rwa [hrc] at h
            have hq3eq' : qdig7 m (c * d3) = qdig7 m (c * d1) := hq3eq hrc0
            exact case62_wrap hm0 hpos hunit hs hd5 hd5cls hother hne hc7
              (Q := ({0, w * runit7 (eMod7 m d2 d1),
                  w * runit7 (eMod7 m d4 d1)} : Finset (ZMod 7)).image
                (· + qdig7 m (c * d1)))
              (by rw [apLen_image_add]; exact hapw)
              (fun d hd hdr => by
                have h := hcover d hd hdr
                rcases case62_cover4 h with h | h | h | h
                · rw [h]
                  refine Finset.mem_image.mpr ⟨0, Finset.mem_insert.mpr
                    (Or.inl rfl), ?_⟩
                  ring
                · rw [h]
                  refine Finset.mem_image.mpr
                    ⟨w * runit7 (eMod7 m d2 d1), ?_, ?_⟩
                  · exact Finset.mem_insert.mpr (Or.inr
                      (Finset.mem_insert.mpr (Or.inl rfl)))
                  · linear_combination -hq2s
                · rw [h, hq3eq']
                  refine Finset.mem_image.mpr ⟨0, Finset.mem_insert.mpr
                    (Or.inl rfl), ?_⟩
                  ring
                · rw [h]
                  refine Finset.mem_image.mpr
                    ⟨w * runit7 (eMod7 m d4 d1), ?_, ?_⟩
                  · exact Finset.mem_insert.mpr (Or.inr
                      (Finset.mem_insert.mpr (Or.inr
                        (Finset.mem_singleton.mpr rfl))))
                  · linear_combination -hq4s)
      · -- `ν(e41) ≠ ν(e21)`: `lemma9_i'` on `(d4, d2, d1)`
        obtain ⟨lam', hlam', -, hap⟩ := lemma9_i'
          ⟨hpos4, hpos2, hpos1⟩ ⟨hν4, hν2, hν1⟩
          ⟨hr4.trans hr2.symm, hr2.trans hr1.symm⟩
          hνeq ⟨he41, he21⟩
        have hlam'r : runit7 lam' ≠ 0 :=
          runit7_ne_zero (Nat.pos_of_ne_zero
            (fun h0 => hlam' (h0 ▸ dvd_zero _)))
        have hq3eq' : qdig7 m (lam' * d3) = qdig7 m (lam' * d1) :=
          hq3eq hlam'r
        exact case62_wrap hm0 hpos hunit hs hd5 hd5cls hother hne hlam'
          (Q := ({d4, d2, d1} : Finset ℕ).image
            (fun d => qdig7 m (lam' * d)))
          (le_trans hap (by decide))
          (fun d hd hdr => by
            have h := hcover d hd hdr
            rcases case62_cover4 h with h | h | h | h
            · rw [h]
              exact Finset.mem_image.mpr ⟨d1, by simp, rfl⟩
            · rw [h]
              exact Finset.mem_image.mpr ⟨d2, by simp, rfl⟩
            · rw [h, hq3eq']
              exact Finset.mem_image.mpr ⟨d1, by simp, rfl⟩
            · rw [h]
              exact Finset.mem_image.mpr ⟨d4, by simp, rfl⟩)
  · -- `e31 ≠ 0`: plain `lemma9_i'` on `(d2, d3, d1)` then `tail5`
    obtain ⟨lam', hlam', -, hap⟩ := lemma9_i'
      ⟨hpos2, hpos3, hpos1⟩ ⟨hν2, hν3, hν1⟩
      ⟨hr2.trans hr3.symm, hr3.trans hr1.symm⟩
      (ne_of_gt huneq) ⟨he21, he31⟩
    exact case62_tail5 hm0 hpos hunit hs hd5 hd5cls hother hne
      hd2 hd3 hd1 hd4 hr2 hr3 hr1 hr4
      (fun d hd hdr => by
        have h := hcover d hd hdr
        rcases case62_cover4 h with h | h | h | h <;> rw [h] <;> simp)
      hlam' hap

/-! ### §10 The `lemma10` case (ii): uniform level, exceptional ratio `4` -/
/-- **Case (ii.4)**: uniform level `h = m` with `r(e₄₁) = 4·r(e₂₁)` —
the exceptional `{0,1,2,4}`-offset route through `case62_tail6'`.
`lam2` is procured by the `λ₂` dispatcher on the pair `(d5, d1)`
(`r(d5) = 4s`) or `(d1, d5)` (`r(d5) = 2s`), with the avoid-set chosen by
the coset of `cu := r(e₂₁)`: `{4,6}`/`{2,3}` for `cu ∈ {1,2,4}` (then
`a' = d1`, `t = 1`) and `{0,2}`/`{3,4}` for `cu ∈ {3,5,6}` (then `t = 5`
and `a'` is the offset-`3` element — the `ẽ` values shift by `−3`/`+6`).
The `e(d5,d1) = 0` degenerate case uses `case62_avoid_zero_carry`. -/
private theorem case62_ii4 {m : ℕ} (hm : 2 ≤ m) {A : Finset ℕ}
    (hpos : ∀ d ∈ A, 0 < d)
    (hunit : ∀ d ∈ A, padicValNat 7 d = 0)
    {s : ZMod 7} (hs : s ≠ 0)
    {d5 : ℕ} (hd5 : d5 ∈ A)
    (hd5cls : runit7 d5 ∈ ({2 * s, 4 * s} : Finset (ZMod 7)))
    (hother : ∀ d ∈ A, d = d5 ∨ runit7 d = s)
    (hne : ∃ d ∈ A, runit7 d = s)
    {d1 d2 d3 d4 : ℕ}
    (hd1 : d1 ∈ A) (hd2 : d2 ∈ A) (hd3 : d3 ∈ A) (hd4 : d4 ∈ A)
    (hr1 : runit7 d1 = s) (hr2 : runit7 d2 = s)
    (hr3 : runit7 d3 = s) (hr4 : runit7 d4 = s)
    (hcover : ∀ d ∈ A, runit7 d = s → d ∈ ({d1, d2, d3, d4} : Finset ℕ))
    (hν21 : padicValNat 7 (eMod7 m d2 d1) = m)
    (hν31 : padicValNat 7 (eMod7 m d3 d1) = m)
    (hν41 : padicValNat 7 (eMod7 m d4 d1) = m)
    (hr3rel : runit7 (eMod7 m d3 d1) = 2 * runit7 (eMod7 m d2 d1))
    (hr4rel : runit7 (eMod7 m d4 d1) = 4 * runit7 (eMod7 m d2 d1)) :
    ∃ lam : ℕ, ¬ 7 ∣ lam ∧ good7 m lam A := by
  classical
  have h1m : 1 ≤ m := by omega
  have hpos1 : 0 < d1 := hpos d1 hd1
  have hpos5 : 0 < d5 := hpos d5 hd5
  have hν1 : padicValNat 7 d1 = 0 := hunit d1 hd1
  have hν5 : padicValNat 7 d5 = 0 := hunit d5 hd5
  have he21 : eMod7 m d2 d1 ≠ 0 := by
    intro h0
    rw [h0] at hν21
    simp at hν21
    omega
  have he31 : eMod7 m d3 d1 ≠ 0 := by
    intro h0
    rw [h0] at hν31
    simp at hν31
    omega
  have he41 : eMod7 m d4 d1 ≠ 0 := by
    intro h0
    rw [h0] at hν41
    simp at hν41
    omega
  have hs21 : residueRelOf d2 d1 = residueRel.same :=
    case62_rel_same hs hr2 hr1
  have hs31 : residueRelOf d3 d1 = residueRel.same :=
    case62_rel_same hs hr3 hr1
  have hs41 : residueRelOf d4 d1 = residueRel.same :=
    case62_rel_same hs hr4 hr1
  have hcu0 : runit7 (eMod7 m d2 d1) ≠ 0 :=
    runit7_ne_zero (Nat.pos_of_ne_zero he21)
  have hcu : runit7 (eMod7 m d2 d1) ∈ ({1, 2, 4} : Finset (ZMod 7)) ∨
      runit7 (eMod7 m d2 d1) ∈ ({3, 5, 6} : Finset (ZMod 7)) := by
    have key : ∀ cu : ZMod 7, cu ≠ 0 →
        cu ∈ ({1, 2, 4} : Finset (ZMod 7)) ∨
          cu ∈ ({3, 5, 6} : Finset (ZMod 7)) := by decide
    exact key _ hcu0
  -- shared `lam2`-post-processing: offsets, units, `u·cu` coset
  have hd5r : runit7 d5 = 2 * s ∨ runit7 d5 = 4 * s := by
    rcases Finset.mem_insert.mp hd5cls with h | h
    · exact Or.inl h
    · exact Or.inr (Finset.mem_singleton.mp h)
  rcases hd5r with hd5r | hd5r
  swap
  · -- **`r(d5) = 4s`**: avoid-pair `(d5, a')`, `ẽ = 2q(d5) − q(a')`
    have hrel51 : runit7 d1 = 2 * runit7 d5 := by
      rw [hr1, hd5r]
      exact (by decide : ∀ a : ZMod 7, a = 2 * (4 * a)) s
    -- local helper: `q(lam2·a') − q(lam2·d1) = 3` and `r(a') = s`
    -- force `ẽ(lam2·d5, lam2·a') = ẽ(lam2·d5, lam2·d1) − 3`.
    have hshift46 : ∀ lam2 : ℕ, runit7 lam2 = 1 → ∀ a' : ℕ,
        runit7 a' = s →
        qdig7 m (lam2 * a') - qdig7 m (lam2 * d1) = 3 →
        etd7 m (lam2 * d5) (lam2 * a')
          = etd7 m (lam2 * d5) (lam2 * d1) - 3 := by
      intro lam2 hlam2u a' hra' hoff3
      have hrela5 : runit7 (lam2 * a') = 2 * runit7 (lam2 * d5) := by
        rw [runit7_mul, runit7_mul, hlam2u, one_mul, hra', hd5r, one_mul]
        exact (by decide : ∀ a : ZMod 7, a = 2 * (4 * a)) s
      have hrel51' : runit7 (lam2 * d1) = 2 * runit7 (lam2 * d5) := by
        rw [runit7_mul, runit7_mul, hlam2u, one_mul, hr1, hd5r, one_mul]
        exact (by decide : ∀ a : ZMod 7, a = 2 * (4 * a)) s
      have hqa'' : qdig7 m (lam2 * a') = qdig7 m (lam2 * d1) + 3 := by
        linear_combination hoff3
      unfold etd7
      rw [if_pos hrela5, if_pos hrel51', hqa'']
      ring
    rcases hcu with hcu | hcu
    · -- `cu ∈ {1,2,4}`: `X = {4,6}`, `a' = d1`, `t = 1`
      obtain ⟨lam2, hlam2, u, humem, hlam2u, hav⟩ :=
        case62_lam2_avoid' hm hν5 hν1 hpos5 hpos1 hrel51
          case62_apLen_46 (by decide)
          (fun r hr => by
            obtain ⟨c, hc, hcr⟩ := case62_stab46 r hr
            exact ⟨c, hc, by
              have hXU : ({4, 6} : Finset (ZMod 7)) ∪
                  ({4, 6} : Finset (ZMod 7)).image (· + 1)
                    = {0, 4, 5, 6} := by decide
              rwa [hXU]⟩)
      have hu : u ≠ 0 := fun h0 => by
        rw [h0] at humem
        exact absurd humem (by decide)
      have hlam2pos : 0 < lam2 :=
        Nat.pos_of_ne_zero (fun h0 => hlam2 (h0 ▸ dvd_zero _))
      have hνlam2 : padicValNat 7 lam2 = 0 :=
        padicValNat.eq_zero_of_not_dvd hlam2
      have hcast : (lam2 : ZMod 7) = u :=
        (case62_runit7_eq_cast hνlam2).symm.trans hlam2u
      have hq2' : qdig7 m (lam2 * d2) - qdig7 m (lam2 * d1)
          = u * runit7 (eMod7 m d2 d1) := by
        have h := case62_qdig_sub_smul_top h1m hνlam2
          (ne_of_gt hlam2pos) hs21 he21 hν21
        rwa [hcast] at h
      have hq3' : qdig7 m (lam2 * d3) - qdig7 m (lam2 * d1)
          = u * runit7 (eMod7 m d3 d1) := by
        have h := case62_qdig_sub_smul_top h1m hνlam2
          (ne_of_gt hlam2pos) hs31 he31 hν31
        rwa [hcast] at h
      have hq4' : qdig7 m (lam2 * d4) - qdig7 m (lam2 * d1)
          = u * runit7 (eMod7 m d4 d1) := by
        have h := case62_qdig_sub_smul_top h1m hνlam2
          (ne_of_gt hlam2pos) hs41 he41 hν41
        rwa [hcast] at h
      have hw124 : u * runit7 (eMod7 m d2 d1) ∈
          ({1, 2, 4} : Finset (ZMod 7)) := case62_mul_124 _ _ humem hcu
      have hv2eq : u * runit7 (eMod7 m d3 d1)
          = 2 * (u * runit7 (eMod7 m d2 d1)) := by
        rw [hr3rel]
        ring
      have hv3eq : u * runit7 (eMod7 m d4 d1)
          = 4 * (u * runit7 (eMod7 m d2 d1)) := by
        rw [hr4rel]
        ring
      have hoff := case62_offsets_1235 _ hw124
      have hS_len : apLen ({1, 1 + u * runit7 (eMod7 m d2 d1),
          1 + u * runit7 (eMod7 m d3 d1),
          1 + u * runit7 (eMod7 m d4 d1)} : Finset (ZMod 7)) = 5 := by
        rw [hv2eq, hv3eq, hoff]
        exact case62_apLen_1235
      have hS_cyc : ({1, 1 + u * runit7 (eMod7 m d2 d1),
          1 + u * runit7 (eMod7 m d3 d1),
          1 + u * runit7 (eMod7 m d4 d1)} : Finset (ZMod 7))
          ⊆ cycIv 1 5 := by
        rw [hv2eq, hv3eq, hoff]
        intro q hq
        exact case62_mem_cycIv15 q hq
      have hqa' : qdig7 m (lam2 * d1) - qdig7 m (lam2 * d1)
          = (1 : ZMod 7) - 1 :=
        (sub_self _).trans (by decide)
      exact case62_tail6' hm hpos hunit hs hd5 hd5cls hother hne
        hd1 hd2 hd3 hd4 hd1 hr1 hr2 hr3 hr4 hr1 hcover hlam2 hlam2u hu
        hq2' hq3' hq4' hqa' hS_len hS_cyc (Or.inl ⟨hd5r, hav⟩)
    · -- `cu ∈ {3,5,6}`: `t = 5`, `a'` = the offset-`3` element
      by_cases he51 : eMod7 m d5 d1 = 0
      · -- `e(d5,d1) = 0`: `ẽ(d5,d1) = 6` (carry), `ẽ(d5,a') = 3 ∉ {4,6}`
        obtain ⟨lam2, hlam2, hlam7, hav⟩ := case62_avoid_zero_carry
          hm hν5 hν1 hpos5 hpos1 hrel51 he51
        have hlam2u : runit7 lam2 = 1 := runit7_eq_one_of_mod7 hlam7
        have hlam2pos : 0 < lam2 :=
          Nat.pos_of_ne_zero (fun h0 => hlam2 (h0 ▸ dvd_zero _))
        have hνlam2 : padicValNat 7 lam2 = 0 :=
          padicValNat.eq_zero_of_not_dvd hlam2
        have hcast : (lam2 : ZMod 7) = 1 :=
          (case62_runit7_eq_cast hνlam2).symm.trans hlam2u
        have hq2' : qdig7 m (lam2 * d2) - qdig7 m (lam2 * d1)
            = 1 * runit7 (eMod7 m d2 d1) := by
          have h := case62_qdig_sub_smul_top h1m hνlam2
            (ne_of_gt hlam2pos) hs21 he21 hν21
          rwa [hcast] at h
        have hq3' : qdig7 m (lam2 * d3) - qdig7 m (lam2 * d1)
            = 1 * runit7 (eMod7 m d3 d1) := by
          have h := case62_qdig_sub_smul_top h1m hνlam2
            (ne_of_gt hlam2pos) hs31 he31 hν31
          rwa [hcast] at h
        have hq4' : qdig7 m (lam2 * d4) - qdig7 m (lam2 * d1)
            = 1 * runit7 (eMod7 m d4 d1) := by
          have h := case62_qdig_sub_smul_top h1m hνlam2
            (ne_of_gt hlam2pos) hs41 he41 hν41
          rwa [hcast] at h
        have hw356 : 1 * runit7 (eMod7 m d2 d1) ∈
            ({3, 5, 6} : Finset (ZMod 7)) := by
          rw [one_mul]
          exact hcu
        have hv2eq : 1 * runit7 (eMod7 m d3 d1)
            = 2 * (1 * runit7 (eMod7 m d2 d1)) := by
          rw [hr3rel]
          ring
        have hv3eq : 1 * runit7 (eMod7 m d4 d1)
            = 4 * (1 * runit7 (eMod7 m d2 d1)) := by
          rw [hr4rel]
          ring
        have hoff := case62_offsets_1345 _ hw356
        have hS_len : apLen ({5, 5 + 1 * runit7 (eMod7 m d2 d1),
            5 + 1 * runit7 (eMod7 m d3 d1),
            5 + 1 * runit7 (eMod7 m d4 d1)} : Finset (ZMod 7)) = 5 := by
          rw [hv2eq, hv3eq, hoff]
          exact case62_apLen_1345
        have hS_cyc : ({5, 5 + 1 * runit7 (eMod7 m d2 d1),
            5 + 1 * runit7 (eMod7 m d3 d1),
            5 + 1 * runit7 (eMod7 m d4 d1)} : Finset (ZMod 7))
            ⊆ cycIv 1 5 := by
          rw [hv2eq, hv3eq, hoff]
          intro q hq
          exact case62_mem_cycIv1345 q hq
        have h3mem := case62_offset3_mem _ hw356
        simp only [Finset.mem_insert, Finset.mem_singleton] at h3mem
        rcases h3mem with h3w | h3w | h3w
        · -- `3 = 1·cu`: `a' := d2`
          have hq_off : qdig7 m (lam2 * d2) - qdig7 m (lam2 * d1)
              = 3 := hq2'.trans h3w.symm
          have hqa' : qdig7 m (lam2 * d2) - qdig7 m (lam2 * d1)
              = (1 : ZMod 7) - 5 := hq_off.trans (by decide)
          have hav' : etd7 m (lam2 * d5) (lam2 * d2) ∉
              ({4, 6} : Finset (ZMod 7)) := by
            rw [hshift46 lam2 hlam2u d2 hr2 hq_off, hav]
            decide
          exact case62_tail6' hm hpos hunit hs hd5 hd5cls hother hne
            hd1 hd2 hd3 hd4 hd2 hr1 hr2 hr3 hr4 hr2 hcover hlam2 hlam2u
            one_ne_zero hq2' hq3' hq4' hqa' hS_len hS_cyc
            (Or.inl ⟨hd5r, hav'⟩)
        · -- `3 = 2·cu`: `a' := d3`
          have hq_off : qdig7 m (lam2 * d3) - qdig7 m (lam2 * d1)
              = 3 := hq3'.trans (hv2eq.trans h3w.symm)
          have hqa' : qdig7 m (lam2 * d3) - qdig7 m (lam2 * d1)
              = (1 : ZMod 7) - 5 := hq_off.trans (by decide)
          have hav' : etd7 m (lam2 * d5) (lam2 * d3) ∉
              ({4, 6} : Finset (ZMod 7)) := by
            rw [hshift46 lam2 hlam2u d3 hr3 hq_off, hav]
            decide
          exact case62_tail6' hm hpos hunit hs hd5 hd5cls hother hne
            hd1 hd2 hd3 hd4 hd3 hr1 hr2 hr3 hr4 hr3 hcover hlam2 hlam2u
            one_ne_zero hq2' hq3' hq4' hqa' hS_len hS_cyc
            (Or.inl ⟨hd5r, hav'⟩)
        · -- `3 = 4·cu`: `a' := d4`
          have hq_off : qdig7 m (lam2 * d4) - qdig7 m (lam2 * d1)
              = 3 := hq4'.trans (hv3eq.trans h3w.symm)
          have hqa' : qdig7 m (lam2 * d4) - qdig7 m (lam2 * d1)
              = (1 : ZMod 7) - 5 := hq_off.trans (by decide)
          have hav' : etd7 m (lam2 * d5) (lam2 * d4) ∉
              ({4, 6} : Finset (ZMod 7)) := by
            rw [hshift46 lam2 hlam2u d4 hr4 hq_off, hav]
            decide
          exact case62_tail6' hm hpos hunit hs hd5 hd5cls hother hne
            hd1 hd2 hd3 hd4 hd4 hr1 hr2 hr3 hr4 hr4 hcover hlam2 hlam2u
            one_ne_zero hq2' hq3' hq4' hqa' hS_len hS_cyc
            (Or.inl ⟨hd5r, hav'⟩)
      · -- `e(d5,d1) ≠ 0`: `lam2_avoid_pos` on `(d5,d1)` with `X = {0,2}`;
        -- `ẽ(d5,a') = ẽ(d5,d1) − 3 ∉ {4,6}` for the offset-`3` anchor.
        obtain ⟨lam2, hlam2, u, humem, hlam2u, hav⟩ :=
          case62_lam2_avoid_pos hm hν5 hν1 hpos5 hpos1 hrel51 he51
            case62_apLen_02
            (fun r hr => by
              obtain ⟨c, hc, hcr⟩ := case62_stab02 r hr
              exact ⟨c, hc, by
                have hXU : ({0, 2} : Finset (ZMod 7)) ∪
                    ({0, 2} : Finset (ZMod 7)).image (· + 1)
                      = {0, 1, 2, 3} := by decide
                rwa [hXU]⟩)
        have hu : u ≠ 0 := fun h0 => by
          rw [h0] at humem
          exact absurd humem (by decide)
        have hlam2pos : 0 < lam2 :=
          Nat.pos_of_ne_zero (fun h0 => hlam2 (h0 ▸ dvd_zero _))
        have hνlam2 : padicValNat 7 lam2 = 0 :=
          padicValNat.eq_zero_of_not_dvd hlam2
        have hcast : (lam2 : ZMod 7) = u :=
          (case62_runit7_eq_cast hνlam2).symm.trans hlam2u
        have hq2' : qdig7 m (lam2 * d2) - qdig7 m (lam2 * d1)
            = u * runit7 (eMod7 m d2 d1) := by
          have h := case62_qdig_sub_smul_top h1m hνlam2
            (ne_of_gt hlam2pos) hs21 he21 hν21
          rwa [hcast] at h
        have hq3' : qdig7 m (lam2 * d3) - qdig7 m (lam2 * d1)
            = u * runit7 (eMod7 m d3 d1) := by
          have h := case62_qdig_sub_smul_top h1m hνlam2
            (ne_of_gt hlam2pos) hs31 he31 hν31
          rwa [hcast] at h
        have hq4' : qdig7 m (lam2 * d4) - qdig7 m (lam2 * d1)
            = u * runit7 (eMod7 m d4 d1) := by
          have h := case62_qdig_sub_smul_top h1m hνlam2
            (ne_of_gt hlam2pos) hs41 he41 hν41
          rwa [hcast] at h
        have hw356 : u * runit7 (eMod7 m d2 d1) ∈
            ({3, 5, 6} : Finset (ZMod 7)) := case62_mul_356 _ _ humem hcu
        have hv2eq : u * runit7 (eMod7 m d3 d1)
            = 2 * (u * runit7 (eMod7 m d2 d1)) := by
          rw [hr3rel]
          ring
        have hv3eq : u * runit7 (eMod7 m d4 d1)
            = 4 * (u * runit7 (eMod7 m d2 d1)) := by
          rw [hr4rel]
          ring
        have hoff := case62_offsets_1345 _ hw356
        have hS_len : apLen ({5, 5 + u * runit7 (eMod7 m d2 d1),
            5 + u * runit7 (eMod7 m d3 d1),
            5 + u * runit7 (eMod7 m d4 d1)} : Finset (ZMod 7)) = 5 := by
          rw [hv2eq, hv3eq, hoff]
          exact case62_apLen_1345
        have hS_cyc : ({5, 5 + u * runit7 (eMod7 m d2 d1),
            5 + u * runit7 (eMod7 m d3 d1),
            5 + u * runit7 (eMod7 m d4 d1)} : Finset (ZMod 7))
            ⊆ cycIv 1 5 := by
          rw [hv2eq, hv3eq, hoff]
          intro q hq
          exact case62_mem_cycIv1345 q hq
        -- the `ẽ`-shift for `lam2` (unit `u`, not `1`)
        have hshift46' : ∀ a' : ℕ, runit7 a' = s →
            qdig7 m (lam2 * a') - qdig7 m (lam2 * d1) = 3 →
            etd7 m (lam2 * d5) (lam2 * a')
              = etd7 m (lam2 * d5) (lam2 * d1) - 3 := by
          intro a' hra' hoff3
          have hrela5 : runit7 (lam2 * a') = 2 * runit7 (lam2 * d5) := by
            rw [runit7_mul, runit7_mul, hlam2u, hra', hd5r]
            exact (by decide : ∀ a b : ZMod 7, a * b = 2 * (a * (4 * b))) u s
          have hrel51' : runit7 (lam2 * d1) = 2 * runit7 (lam2 * d5) := by
            rw [runit7_mul, runit7_mul, hlam2u, hr1, hd5r]
            exact (by decide : ∀ a b : ZMod 7, a * b = 2 * (a * (4 * b))) u s
          have hqa'' : qdig7 m (lam2 * a') = qdig7 m (lam2 * d1) + 3 := by
            linear_combination hoff3
          unfold etd7
          rw [if_pos hrela5, if_pos hrel51', hqa'']
          ring
        have h3mem := case62_offset3_mem _ hw356
        simp only [Finset.mem_insert, Finset.mem_singleton] at h3mem
        rcases h3mem with h3w | h3w | h3w
        · have hq_off : qdig7 m (lam2 * d2) - qdig7 m (lam2 * d1)
              = 3 := hq2'.trans h3w.symm
          have hqa' : qdig7 m (lam2 * d2) - qdig7 m (lam2 * d1)
              = (1 : ZMod 7) - 5 := hq_off.trans (by decide)
          have hav' : etd7 m (lam2 * d5) (lam2 * d2) ∉
              ({4, 6} : Finset (ZMod 7)) := by
            rw [hshift46' d2 hr2 hq_off]
            exact case62_shift02 _ hav
          exact case62_tail6' hm hpos hunit hs hd5 hd5cls hother hne
            hd1 hd2 hd3 hd4 hd2 hr1 hr2 hr3 hr4 hr2 hcover hlam2 hlam2u
            hu hq2' hq3' hq4' hqa' hS_len hS_cyc
            (Or.inl ⟨hd5r, hav'⟩)
        · have hq_off : qdig7 m (lam2 * d3) - qdig7 m (lam2 * d1)
              = 3 := hq3'.trans (hv2eq.trans h3w.symm)
          have hqa' : qdig7 m (lam2 * d3) - qdig7 m (lam2 * d1)
              = (1 : ZMod 7) - 5 := hq_off.trans (by decide)
          have hav' : etd7 m (lam2 * d5) (lam2 * d3) ∉
              ({4, 6} : Finset (ZMod 7)) := by
            rw [hshift46' d3 hr3 hq_off]
            exact case62_shift02 _ hav
          exact case62_tail6' hm hpos hunit hs hd5 hd5cls hother hne
            hd1 hd2 hd3 hd4 hd3 hr1 hr2 hr3 hr4 hr3 hcover hlam2 hlam2u
            hu hq2' hq3' hq4' hqa' hS_len hS_cyc
            (Or.inl ⟨hd5r, hav'⟩)
        · have hq_off : qdig7 m (lam2 * d4) - qdig7 m (lam2 * d1)
              = 3 := hq4'.trans (hv3eq.trans h3w.symm)
          have hqa' : qdig7 m (lam2 * d4) - qdig7 m (lam2 * d1)
              = (1 : ZMod 7) - 5 := hq_off.trans (by decide)
          have hav' : etd7 m (lam2 * d5) (lam2 * d4) ∉
              ({4, 6} : Finset (ZMod 7)) := by
            rw [hshift46' d4 hr4 hq_off]
            exact case62_shift02 _ hav
          exact case62_tail6' hm hpos hunit hs hd5 hd5cls hother hne
            hd1 hd2 hd3 hd4 hd4 hr1 hr2 hr3 hr4 hr4 hcover hlam2 hlam2u
            hu hq2' hq3' hq4' hqa' hS_len hS_cyc
            (Or.inl ⟨hd5r, hav'⟩)
  · -- **`r(d5) = 2s`**: avoid-pair `(a', d5)`, `ẽ = 2q(a') − q(d5)`
    have hrel15 : runit7 d5 = 2 * runit7 d1 := by
      rw [hd5r, hr1]
    -- local helper: `q(lam2·a') − q(lam2·d1) = 3` forces
    -- `ẽ(lam2·a', lam2·d5) = ẽ(lam2·d1, lam2·d5) + 6`.
    have hshift23 : ∀ a' : ℕ, runit7 a' = s →
        ∀ lam2 : ℕ, ∀ u : ZMod 7, runit7 lam2 = u →
        qdig7 m (lam2 * a') - qdig7 m (lam2 * d1) = 3 →
        etd7 m (lam2 * a') (lam2 * d5)
          = etd7 m (lam2 * d1) (lam2 * d5) + 6 := by
      intro a' hra' lam2 u hlam2u hoff3
      have hrela5 : runit7 (lam2 * d5) = 2 * runit7 (lam2 * a') := by
        rw [runit7_mul, runit7_mul, hlam2u, hd5r, hra']
        ring
      have hrel15' : runit7 (lam2 * d5) = 2 * runit7 (lam2 * d1) := by
        rw [runit7_mul, runit7_mul, hlam2u, hd5r, hr1]
        ring
      have hqa'' : qdig7 m (lam2 * a') = qdig7 m (lam2 * d1) + 3 := by
        linear_combination hoff3
      unfold etd7
      rw [if_pos hrela5, if_pos hrel15', hqa'']
      ring
    rcases hcu with hcu | hcu
    · -- `cu ∈ {1,2,4}`: `X = {2,3}`, `a' = d1`, `t = 1`
      obtain ⟨lam2, hlam2, u, humem, hlam2u, hav⟩ :=
        case62_lam2_avoid' hm hν1 hν5 hpos1 hpos5 hrel15
          case62_apLen_23 (by decide)
          (fun r hr => by
            obtain ⟨c, hc, hcr⟩ := case62_stab23 r hr
            exact ⟨c, hc, by
              have hXU : ({2, 3} : Finset (ZMod 7)) ∪
                  ({2, 3} : Finset (ZMod 7)).image (· + 1)
                    = {2, 3, 4} := by decide
              rwa [hXU]⟩)
      have hu : u ≠ 0 := fun h0 => by
        rw [h0] at humem
        exact absurd humem (by decide)
      have hlam2pos : 0 < lam2 :=
        Nat.pos_of_ne_zero (fun h0 => hlam2 (h0 ▸ dvd_zero _))
      have hνlam2 : padicValNat 7 lam2 = 0 :=
        padicValNat.eq_zero_of_not_dvd hlam2
      have hcast : (lam2 : ZMod 7) = u :=
        (case62_runit7_eq_cast hνlam2).symm.trans hlam2u
      have hq2' : qdig7 m (lam2 * d2) - qdig7 m (lam2 * d1)
          = u * runit7 (eMod7 m d2 d1) := by
        have h := case62_qdig_sub_smul_top h1m hνlam2
          (ne_of_gt hlam2pos) hs21 he21 hν21
        rwa [hcast] at h
      have hq3' : qdig7 m (lam2 * d3) - qdig7 m (lam2 * d1)
          = u * runit7 (eMod7 m d3 d1) := by
        have h := case62_qdig_sub_smul_top h1m hνlam2
          (ne_of_gt hlam2pos) hs31 he31 hν31
        rwa [hcast] at h
      have hq4' : qdig7 m (lam2 * d4) - qdig7 m (lam2 * d1)
          = u * runit7 (eMod7 m d4 d1) := by
        have h := case62_qdig_sub_smul_top h1m hνlam2
          (ne_of_gt hlam2pos) hs41 he41 hν41
        rwa [hcast] at h
      have hw124 : u * runit7 (eMod7 m d2 d1) ∈
          ({1, 2, 4} : Finset (ZMod 7)) := case62_mul_124 _ _ humem hcu
      have hv2eq : u * runit7 (eMod7 m d3 d1)
          = 2 * (u * runit7 (eMod7 m d2 d1)) := by
        rw [hr3rel]
        ring
      have hv3eq : u * runit7 (eMod7 m d4 d1)
          = 4 * (u * runit7 (eMod7 m d2 d1)) := by
        rw [hr4rel]
        ring
      have hoff := case62_offsets_1235 _ hw124
      have hS_len : apLen ({1, 1 + u * runit7 (eMod7 m d2 d1),
          1 + u * runit7 (eMod7 m d3 d1),
          1 + u * runit7 (eMod7 m d4 d1)} : Finset (ZMod 7)) = 5 := by
        rw [hv2eq, hv3eq, hoff]
        exact case62_apLen_1235
      have hS_cyc : ({1, 1 + u * runit7 (eMod7 m d2 d1),
          1 + u * runit7 (eMod7 m d3 d1),
          1 + u * runit7 (eMod7 m d4 d1)} : Finset (ZMod 7))
          ⊆ cycIv 1 5 := by
        rw [hv2eq, hv3eq, hoff]
        intro q hq
        exact case62_mem_cycIv15 q hq
      have hqa' : qdig7 m (lam2 * d1) - qdig7 m (lam2 * d1)
          = (1 : ZMod 7) - 1 :=
        (sub_self _).trans (by decide)
      exact case62_tail6' hm hpos hunit hs hd5 hd5cls hother hne
        hd1 hd2 hd3 hd4 hd1 hr1 hr2 hr3 hr4 hr1 hcover hlam2 hlam2u hu
        hq2' hq3' hq4' hqa' hS_len hS_cyc (Or.inr ⟨hd5r, hav⟩)
    · -- `cu ∈ {3,5,6}`: `X = {3,4}` on `(d1,d5)`; `t = 5`, `a'` = offset-`3`
      obtain ⟨lam2, hlam2, u, humem, hlam2u, hav⟩ :=
        case62_lam2_avoid' hm hν1 hν5 hpos1 hpos5 hrel15
          case62_apLen_34 (by decide)
          (fun r hr => by
            obtain ⟨c, hc, hcr⟩ := case62_stab34 r hr
            exact ⟨c, hc, by
              have hXU : ({3, 4} : Finset (ZMod 7)) ∪
                  ({3, 4} : Finset (ZMod 7)).image (· + 1)
                    = {3, 4, 5} := by decide
              rwa [hXU]⟩)
      have hu : u ≠ 0 := fun h0 => by
        rw [h0] at humem
        exact absurd humem (by decide)
      have hlam2pos : 0 < lam2 :=
        Nat.pos_of_ne_zero (fun h0 => hlam2 (h0 ▸ dvd_zero _))
      have hνlam2 : padicValNat 7 lam2 = 0 :=
        padicValNat.eq_zero_of_not_dvd hlam2
      have hcast : (lam2 : ZMod 7) = u :=
        (case62_runit7_eq_cast hνlam2).symm.trans hlam2u
      have hq2' : qdig7 m (lam2 * d2) - qdig7 m (lam2 * d1)
          = u * runit7 (eMod7 m d2 d1) := by
        have h := case62_qdig_sub_smul_top h1m hνlam2
          (ne_of_gt hlam2pos) hs21 he21 hν21
        rwa [hcast] at h
      have hq3' : qdig7 m (lam2 * d3) - qdig7 m (lam2 * d1)
          = u * runit7 (eMod7 m d3 d1) := by
        have h := case62_qdig_sub_smul_top h1m hνlam2
          (ne_of_gt hlam2pos) hs31 he31 hν31
        rwa [hcast] at h
      have hq4' : qdig7 m (lam2 * d4) - qdig7 m (lam2 * d1)
          = u * runit7 (eMod7 m d4 d1) := by
        have h := case62_qdig_sub_smul_top h1m hνlam2
          (ne_of_gt hlam2pos) hs41 he41 hν41
        rwa [hcast] at h
      have hw356 : u * runit7 (eMod7 m d2 d1) ∈
          ({3, 5, 6} : Finset (ZMod 7)) := case62_mul_356 _ _ humem hcu
      have hv2eq : u * runit7 (eMod7 m d3 d1)
          = 2 * (u * runit7 (eMod7 m d2 d1)) := by
        rw [hr3rel]
        ring
      have hv3eq : u * runit7 (eMod7 m d4 d1)
          = 4 * (u * runit7 (eMod7 m d2 d1)) := by
        rw [hr4rel]
        ring
      have hoff := case62_offsets_1345 _ hw356
      have hS_len : apLen ({5, 5 + u * runit7 (eMod7 m d2 d1),
          5 + u * runit7 (eMod7 m d3 d1),
          5 + u * runit7 (eMod7 m d4 d1)} : Finset (ZMod 7)) = 5 := by
        rw [hv2eq, hv3eq, hoff]
        exact case62_apLen_1345
      have hS_cyc : ({5, 5 + u * runit7 (eMod7 m d2 d1),
          5 + u * runit7 (eMod7 m d3 d1),
          5 + u * runit7 (eMod7 m d4 d1)} : Finset (ZMod 7))
          ⊆ cycIv 1 5 := by
        rw [hv2eq, hv3eq, hoff]
        intro q hq
        exact case62_mem_cycIv1345 q hq
      have h3mem := case62_offset3_mem _ hw356
      simp only [Finset.mem_insert, Finset.mem_singleton] at h3mem
      rcases h3mem with h3w | h3w | h3w
      · have hq_off : qdig7 m (lam2 * d2) - qdig7 m (lam2 * d1)
            = 3 := hq2'.trans h3w.symm
        have hqa' : qdig7 m (lam2 * d2) - qdig7 m (lam2 * d1)
            = (1 : ZMod 7) - 5 := hq_off.trans (by decide)
        have hav' : etd7 m (lam2 * d2) (lam2 * d5) ∉
            ({2, 3} : Finset (ZMod 7)) := by
          rw [hshift23 d2 hr2 lam2 u hlam2u hq_off]
          exact case62_shift34 _ hav
        exact case62_tail6' hm hpos hunit hs hd5 hd5cls hother hne
          hd1 hd2 hd3 hd4 hd2 hr1 hr2 hr3 hr4 hr2 hcover hlam2 hlam2u
          hu hq2' hq3' hq4' hqa' hS_len hS_cyc
          (Or.inr ⟨hd5r, hav'⟩)
      · have hq_off : qdig7 m (lam2 * d3) - qdig7 m (lam2 * d1)
            = 3 := hq3'.trans (hv2eq.trans h3w.symm)
        have hqa' : qdig7 m (lam2 * d3) - qdig7 m (lam2 * d1)
            = (1 : ZMod 7) - 5 := hq_off.trans (by decide)
        have hav' : etd7 m (lam2 * d3) (lam2 * d5) ∉
            ({2, 3} : Finset (ZMod 7)) := by
          rw [hshift23 d3 hr3 lam2 u hlam2u hq_off]
          exact case62_shift34 _ hav
        exact case62_tail6' hm hpos hunit hs hd5 hd5cls hother hne
          hd1 hd2 hd3 hd4 hd3 hr1 hr2 hr3 hr4 hr3 hcover hlam2 hlam2u
          hu hq2' hq3' hq4' hqa' hS_len hS_cyc
          (Or.inr ⟨hd5r, hav'⟩)
      · have hq_off : qdig7 m (lam2 * d4) - qdig7 m (lam2 * d1)
            = 3 := hq4'.trans (hv3eq.trans h3w.symm)
        have hqa' : qdig7 m (lam2 * d4) - qdig7 m (lam2 * d1)
            = (1 : ZMod 7) - 5 := hq_off.trans (by decide)
        have hav' : etd7 m (lam2 * d4) (lam2 * d5) ∉
            ({2, 3} : Finset (ZMod 7)) := by
          rw [hshift23 d4 hr4 lam2 u hlam2u hq_off]
          exact case62_shift34 _ hav
        exact case62_tail6' hm hpos hunit hs hd5 hd5cls hother hne
          hd1 hd2 hd3 hd4 hd4 hr1 hr2 hr3 hr4 hr4 hcover hlam2 hlam2u
          hu hq2' hq3' hq4' hqa' hS_len hS_cyc
          (Or.inr ⟨hd5r, hav'⟩)


/-! ### §11 The `lemma10` case (ii): uniform level -/

/-- **Case (ii)**: uniform edge level `h` with `r(e₃₁) = 2·r(e₂₁)` and
`r(e₄₁) ∈ {3,4}·r(e₂₁)`.  `e₂₁ = 0` collapses all residues to `d₁`'s
(wrap `c = 1`); `h < m` is `lemma9_ii` at `j = 2` into `case62_tail5`;
`h = m` with ratio `3` is the `{0,u,2u,3u}` rescale into `case62_wrap`;
ratio `4` is `case62_ii4`. -/
private theorem case62_ii {m : ℕ} (hm : 2 ≤ m) {A A1 : Finset ℕ}
    (hpos : ∀ d ∈ A, 0 < d)
    (hunit : ∀ d ∈ A, padicValNat 7 d = 0)
    {s : ZMod 7} (hs : s ≠ 0)
    {d5 : ℕ} (hd5 : d5 ∈ A)
    (hd5cls : runit7 d5 ∈ ({2 * s, 4 * s} : Finset (ZMod 7)))
    (hother : ∀ d ∈ A, d = d5 ∨ runit7 d = s)
    (hne : ∃ d ∈ A, runit7 d = s)
    {d1 d2 d3 d4 : ℕ}
    (hd1 : d1 ∈ A) (hd2 : d2 ∈ A) (hd3 : d3 ∈ A) (hd4 : d4 ∈ A)
    (hd1' : d1 ∈ A1) (hd2' : d2 ∈ A1) (hd3' : d3 ∈ A1) (hd4' : d4 ∈ A1)
    (h21 : d2 ≠ d1) (h31 : d3 ≠ d1) (h41 : d4 ≠ d1)
    (hr1 : runit7 d1 = s) (hr2 : runit7 d2 = s)
    (hr3 : runit7 d3 = s) (hr4 : runit7 d4 = s)
    (hcover : ∀ d ∈ A, runit7 d = s → d ∈ ({d1, d2, d3, d4} : Finset ℕ))
    {h : ℕ}
    (huni : ∀ x ∈ A1, ∀ y ∈ A1, x ≠ y → eMod7 m x y ≠ 0 →
      padicValNat 7 (eMod7 m x y) = h)
    (hr3rel : runit7 (eMod7 m d3 d1) = 2 * runit7 (eMod7 m d2 d1))
    (hr4rel : runit7 (eMod7 m d4 d1) = 3 * runit7 (eMod7 m d2 d1) ∨
      runit7 (eMod7 m d4 d1) = 4 * runit7 (eMod7 m d2 d1)) :
    ∃ lam : ℕ, ¬ 7 ∣ lam ∧ good7 m lam A := by
  classical
  have hm0 : 0 < m := by omega
  have h1m : 1 ≤ m := by omega
  have hpos1 : 0 < d1 := hpos d1 hd1
  have hpos2 : 0 < d2 := hpos d2 hd2
  have hpos3 : 0 < d3 := hpos d3 hd3
  have hν1 : padicValNat 7 d1 = 0 := hunit d1 hd1
  have hν2 : padicValNat 7 d2 = 0 := hunit d2 hd2
  have hν3 : padicValNat 7 d3 = 0 := hunit d3 hd3
  have h1ne : runit7 (1 : ℕ) ≠ 0 := by
    rw [runit7_eq_one_of_mod7 (by norm_num : (1 : ℕ) % 7 = 1)]
    exact one_ne_zero
  have hs21 : residueRelOf d2 d1 = residueRel.same :=
    case62_rel_same hs hr2 hr1
  have hs31 : residueRelOf d3 d1 = residueRel.same :=
    case62_rel_same hs hr3 hr1
  have hs41 : residueRelOf d4 d1 = residueRel.same :=
    case62_rel_same hs hr4 hr1
  by_cases he21 : eMod7 m d2 d1 = 0
  · -- `e21 = 0`: `r(e21) = 0` forces `e31 = e41 = 0`; all digits collapse.
    have hre21 : runit7 (eMod7 m d2 d1) = 0 := by
      rw [he21]
      exact case62_runit7_zero
    have he31 : eMod7 m d3 d1 = 0 := by
      apply case62_eq_zero_of_runit7
      rw [hr3rel, hre21, mul_zero]
    have he41 : eMod7 m d4 d1 = 0 := by
      apply case62_eq_zero_of_runit7
      rcases hr4rel with h4 | h4 <;> rw [h4, hre21, mul_zero]
    have hq2eq : qdig7 m (1 * d2) = qdig7 m (1 * d1) :=
      case62_qdig_eq_of_eMod7_zero h1ne hs21 he21
    have hq3eq : qdig7 m (1 * d3) = qdig7 m (1 * d1) :=
      case62_qdig_eq_of_eMod7_zero h1ne hs31 he31
    have hq4eq : qdig7 m (1 * d4) = qdig7 m (1 * d1) :=
      case62_qdig_eq_of_eMod7_zero h1ne hs41 he41
    exact case62_wrap hm0 hpos hunit hs hd5 hd5cls hother hne
      (by decide : ¬ (7 : ℕ) ∣ 1)
      (Q := {qdig7 m (1 * d1)})
      (le_trans (case62_apLen_single _) (by norm_num))
      (fun d hd hdr => by
        have h := hcover d hd hdr
        rcases case62_cover4 h with h | h | h | h
        · rw [h]
          exact Finset.mem_singleton_self _
        · rw [h, hq2eq]
          exact Finset.mem_singleton_self _
        · rw [h, hq3eq]
          exact Finset.mem_singleton_self _
        · rw [h, hq4eq]
          exact Finset.mem_singleton_self _)
  · -- `e21 ≠ 0`: every edge has level `h`, and `h ≤ m`.
    have hν21 : padicValNat 7 (eMod7 m d2 d1) = h :=
      huni d2 hd2' d1 hd1' h21 he21
    have hre21 : runit7 (eMod7 m d2 d1) ≠ 0 :=
      runit7_ne_zero (Nat.pos_of_ne_zero he21)
    have he31 : eMod7 m d3 d1 ≠ 0 := by
      intro h0
      apply hre21
      have h0' : runit7 (eMod7 m d3 d1) = 0 := by
        rw [h0]
        exact case62_runit7_zero
      rw [hr3rel] at h0'
      rcases mul_eq_zero.mp h0' with h2 | h2
      · exact absurd h2 (by decide)
      · exact h2
    have he41 : eMod7 m d4 d1 ≠ 0 := by
      intro h0
      apply hre21
      have h0' : runit7 (eMod7 m d4 d1) = 0 := by
        rw [h0]
        exact case62_runit7_zero
      rcases hr4rel with h4 | h4
      · rw [h4] at h0'
        rcases mul_eq_zero.mp h0' with h2 | h2
        · exact absurd h2 (by decide)
        · exact h2
      · rw [h4] at h0'
        rcases mul_eq_zero.mp h0' with h2 | h2
        · exact absurd h2 (by decide)
        · exact h2
    have hν31 : padicValNat 7 (eMod7 m d3 d1) = h :=
      huni d3 hd3' d1 hd1' h31 he31
    have hν41 : padicValNat 7 (eMod7 m d4 d1) = h :=
      huni d4 hd4' d1 hd1' h41 he41
    have hle : h ≤ m := by
      rw [← hν21]
      exact enu7_le_of_ne he21
    rcases lt_or_eq_of_le hle with hlt | heq
    · -- `h < m`: `lemma9_ii` on `(d2, d3, d1)` at `j = 2`, then tail5.
      obtain ⟨lam', hlam', -, -, -, hap⟩ := lemma9_ii (j := 2)
        ⟨hpos2, hpos3, hpos1⟩ ⟨hν2, hν3, hν1⟩
        ⟨hr2.trans hr3.symm, hr3.trans hr1.symm⟩
        (hν21.trans hν31.symm) (by rw [hν31]; exact hlt)
        (Or.inl rfl) hr3rel
      exact case62_tail5 hm0 hpos hunit hs hd5 hd5cls hother hne
        hd2 hd3 hd1 hd4 hr2 hr3 hr1 hr4
        (fun d hd hdr => by
          have h := hcover d hd hdr
          rcases case62_cover4 h with h | h | h | h <;> rw [h] <;> simp)
        hlam' hap
    · -- `h = m`: exact offsets; split on the `e₄₁` ratio.
      rcases hr4rel with hr4rel | hr4rel
      · -- ratio `3`: `case62_cub_rescale` then `case62_wrap`.
        obtain ⟨w, hw0, hapw⟩ :=
          case62_cub_rescale (runit7 (eMod7 m d2 d1)) hre21
        set c := w.val with hcdef
        have hcpos : 0 < c :=
          Nat.pos_of_ne_zero (mt (ZMod.val_eq_zero w).mp hw0)
        have hc7 : ¬ 7 ∣ c := by
          intro hd
          exact hw0 ((ZMod.val_eq_zero w).mp
            (Nat.eq_zero_of_dvd_of_lt hd (ZMod.val_lt w)))
        have hνc : padicValNat 7 c = 0 := padicValNat.eq_zero_of_not_dvd hc7
        have hrc : (c : ZMod 7) = w := by
          rw [hcdef, ZMod.natCast_zmod_val]
        have hq2s : qdig7 m (c * d2) - qdig7 m (c * d1)
            = w * runit7 (eMod7 m d2 d1) := by
          have h := case62_qdig_sub_smul_top h1m hνc
            (ne_of_gt hcpos) hs21 he21 (hν21.trans heq)
          rwa [hrc] at h
        have hq3s : qdig7 m (c * d3) - qdig7 m (c * d1)
            = w * runit7 (eMod7 m d3 d1) := by
          have h := case62_qdig_sub_smul_top h1m hνc
            (ne_of_gt hcpos) hs31 he31 (hν31.trans heq)
          rwa [hrc] at h
        have hq4s : qdig7 m (c * d4) - qdig7 m (c * d1)
            = w * runit7 (eMod7 m d4 d1) := by
          have h := case62_qdig_sub_smul_top h1m hνc
            (ne_of_gt hcpos) hs41 he41 (hν41.trans heq)
          rwa [hrc] at h
        have hq3s' : qdig7 m (c * d3) - qdig7 m (c * d1)
            = 2 * w * runit7 (eMod7 m d2 d1) := by
          rw [hq3s, hr3rel]
          ring
        have hq4s' : qdig7 m (c * d4) - qdig7 m (c * d1)
            = 3 * w * runit7 (eMod7 m d2 d1) := by
          rw [hq4s, hr4rel]
          ring
        exact case62_wrap hm0 hpos hunit hs hd5 hd5cls hother hne hc7
          (Q := ({0, w * runit7 (eMod7 m d2 d1),
              2 * w * runit7 (eMod7 m d2 d1),
              3 * w * runit7 (eMod7 m d2 d1)} : Finset (ZMod 7)).image
            (· + qdig7 m (c * d1)))
          (by rw [apLen_image_add]; exact hapw)
          (fun d hd hdr => by
            have h := hcover d hd hdr
            rcases case62_cover4 h with h | h | h | h
            · rw [h]
              refine Finset.mem_image.mpr
                ⟨0, Finset.mem_insert.mpr (Or.inl rfl), ?_⟩
              ring
            · rw [h]
              refine Finset.mem_image.mpr
                ⟨w * runit7 (eMod7 m d2 d1), ?_, ?_⟩
              · exact Finset.mem_insert.mpr
                  (Or.inr (Finset.mem_insert.mpr (Or.inl rfl)))
              · linear_combination -hq2s
            · rw [h]
              refine Finset.mem_image.mpr
                ⟨2 * w * runit7 (eMod7 m d2 d1), ?_, ?_⟩
              · exact Finset.mem_insert.mpr (Or.inr
                  (Finset.mem_insert.mpr (Or.inr
                    (Finset.mem_insert.mpr (Or.inl rfl)))))
              · linear_combination -hq3s'
            · rw [h]
              refine Finset.mem_image.mpr
                ⟨3 * w * runit7 (eMod7 m d2 d1), ?_, ?_⟩
              · exact Finset.mem_insert.mpr (Or.inr
                  (Finset.mem_insert.mpr (Or.inr
                    (Finset.mem_insert.mpr (Or.inr
                      (Finset.mem_singleton.mpr rfl))))))
              · linear_combination -hq4s')
      · -- ratio `4`: `case62_ii4`.
        exact case62_ii4 hm hpos hunit hs hd5 hd5cls hother hne
          hd1 hd2 hd3 hd4 hr1 hr2 hr3 hr4 hcover
          (hν21.trans heq) (hν31.trans heq) (hν41.trans heq)
          hr3rel hr4rel

/-! ### §12 The public theorem -/

/-- **§6.2** (Barajas–Serra): four elements in the most-popular unit class
`s` plus one leftover in `{2s, 4s}` admit a `7`-unit multiplier good on the
union.  `lemma10` splits on the edge-level pattern: case (i) `ν(e₂₁) >
ν(e₃₁)` is `case62_i`; case (ii) uniform level with the `2`-`{3,4}` ratio
pattern is `case62_ii`. -/
theorem case62 {m : ℕ} (hm : 2 ≤ m) {A1 Ar : Finset ℕ}
    (hA1 : A1.card = 4) (hAr : Ar.card = 1)
    (hpos : ∀ d ∈ A1 ∪ Ar, 0 < d)
    (hunit : ∀ d ∈ A1 ∪ Ar, padicValNat 7 d = 0)
    {s : ZMod 7} (hs : s ∈ ({1, 2, 4} : Finset (ZMod 7)))
    (hcls1 : ∀ d ∈ A1, runit7 d = s)
    (hclsAr : ∀ d ∈ Ar, runit7 d ∈ ({2 * s, 4 * s} : Finset (ZMod 7))) :
    ∃ lam : ℕ, ¬ 7 ∣ lam ∧ good7 m lam (A1 ∪ Ar) := by
  classical
  obtain ⟨d5, hAr_eq⟩ := Finset.card_eq_one.mp hAr
  set A := A1 ∪ Ar with hA
  have hd5Ar : d5 ∈ Ar := hAr_eq ▸ Finset.mem_singleton_self d5
  have hd5 : d5 ∈ A := Finset.mem_union_right A1 hd5Ar
  have hd5cls : runit7 d5 ∈ ({2 * s, 4 * s} : Finset (ZMod 7)) :=
    hclsAr d5 hd5Ar
  have hs0 : s ≠ 0 := by
    fin_cases hs <;> decide
  have hother : ∀ d ∈ A, d = d5 ∨ runit7 d = s := by
    intro d hd
    rcases Finset.mem_union.mp hd with hd1 | hdr
    · exact Or.inr (hcls1 d hd1)
    · exact Or.inl (Finset.mem_singleton.mp (hAr_eq ▸ hdr))
  obtain ⟨d0, hd0⟩ := Finset.card_pos.mp (by omega : 0 < A1.card)
  have hne : ∃ d ∈ A, runit7 d = s :=
    ⟨d0, Finset.mem_union_left Ar hd0, hcls1 d0 hd0⟩
  obtain ⟨d1, hd1', d2, hd2', d3, hd3', d4, hd4',
    h12, h13, h14, h23, h24, h34, hdisj⟩ :=
    lemma10 (le_of_eq hA1.symm)
      (fun d hd => hpos d (Finset.mem_union_left Ar hd))
      (fun d hd => hunit d (Finset.mem_union_left Ar hd)) s hcls1
  have hd1 : d1 ∈ A := Finset.mem_union_left Ar hd1'
  have hd2 : d2 ∈ A := Finset.mem_union_left Ar hd2'
  have hd3 : d3 ∈ A := Finset.mem_union_left Ar hd3'
  have hd4 : d4 ∈ A := Finset.mem_union_left Ar hd4'
  have hr1 : runit7 d1 = s := hcls1 d1 hd1'
  have hr2 : runit7 d2 = s := hcls1 d2 hd2'
  have hr3 : runit7 d3 = s := hcls1 d3 hd3'
  have hr4 : runit7 d4 = s := hcls1 d4 hd4'
  -- `A1 = {d1, d2, d3, d4}`: four distinct elements in a 4-element set.
  have hcard4 : ({d1, d2, d3, d4} : Finset ℕ).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [h12, h13, h14]),
      Finset.card_insert_of_notMem (by simp [h23, h24]),
      Finset.card_insert_of_notMem (by simp [h34]),
      Finset.card_singleton]
  have hsub : ({d1, d2, d3, d4} : Finset ℕ) ⊆ A1 := by
    intro x hx
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert,
      Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  have hA1eq : A1 = ({d1, d2, d3, d4} : Finset ℕ) :=
    (Finset.eq_of_subset_of_card_le hsub
      (le_of_eq (hA1.trans hcard4.symm))).symm
  -- every `s`-class element of `A` lies in `A1`, hence in `{d1,d2,d3,d4}`.
  have hcover : ∀ d ∈ A, runit7 d = s →
      d ∈ ({d1, d2, d3, d4} : Finset ℕ) := by
    intro d hd hdr
    have hdA1 : d ∈ A1 := by
      rcases Finset.mem_union.mp hd with h1 | hAr'
      · exact h1
      · rw [hAr_eq, Finset.mem_singleton] at hAr'
        exfalso
        rw [hAr'] at hdr
        rw [hdr] at hd5cls
        simp only [Finset.mem_insert, Finset.mem_singleton] at hd5cls
        rcases hd5cls with h2 | h4
        · exact hs0 (by linear_combination -h2)
        · have h3 : (3 : ZMod 7) * s = 0 := by linear_combination -h4
          rcases mul_eq_zero.mp h3 with h30 | hs'
          · exact absurd h30 (by decide)
          · exact hs0 hs'
    exact hA1eq ▸ hdA1
  rcases hdisj with huneq | ⟨h, huni, hr3rel, hr4rel⟩
  · exact case62_i hm hpos hunit hs0 hd5 hd5cls hother hne
      hd1 hd2 hd3 hd4 hr1 hr2 hr3 hr4 hcover huneq
  · exact case62_ii hm hpos hunit hs0 hd5 hd5cls hother hne
      hd1 hd2 hd3 hd4 hd1' hd2' hd3' hd4' h12.symm h13.symm h14.symm
      hr1 hr2 hr3 hr4 hcover huni hr3rel hr4rel
