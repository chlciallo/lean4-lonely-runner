/-
Copyright (c) 2026 Research07 contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Research07 contributors
-/
import Research07.LRC7.Filtering

/-!
# §7 of Barajas–Serra: `|A| = 5`, `m = 1` — shared definitions

Base layer for the finite enumeration (`FiniteStage1` / `FiniteStage2`).
Only residues matter: `|λd|_N` depends on `d % N`, and only up to sign,
since `|N − r|_N = |r|_N`.

* **Stage 1 (`ZMod 49`).**  Each `d ∈ A` determines a pair-class
  `{a, −a}` mod 49, encoded by `pairRep49 d = min (d%49) (49−d%49) ∈ {1,…,24}`.
  A 5-subset `Q` of the 24 pair-reps is *good* when some unit
  `λ ∈ U_49/{±1}` (`units21`, one representative per sign pair) has
  `|λa|_49 ≥ 7` for all `a ∈ Q`; otherwise it is *bad*.  `badSets49` lists
  the 63 bad sets explicitly (three `U_49/{±1}` orbits — the paper's three
  exceptional sets), `normBad49` their 15 representatives containing `1`.
* **Stage 2 (`ZMod 98`).**  For every bad `Q`, every `≤ 5`-subset `T` of
  the lifted residues `lifts98 Q = {a, 49 − a : a ∈ Q}` and every
  `d6`-residue `r ∈ {7,…,42}` (`d6res`), provided `T ∪ {r}` contains an
  odd element (the paper's `gcd(D) = 1` side condition — all-even
  residue sets genuinely fail), some `λ ∈ {1,…,49}` — not necessarily a
  unit — has `|λt|_98 ≥ 14` for all `t ∈ T` and `|λr|_98 ≥ 14`.
* **Bridge.**  `rep98 d = min (d%98) (98−d%98)` satisfies
  `rep98 d ∈ {pairRep49 d, 49 − pairRep49 d}` and
  `|λd|_98 = |λ·rep98 d|_98`; similarly `|λd|_49 = |λ·pairRep49 d|_49`.
-/

/-- Canonical representative of the pair `{d, −d}` in `ZMod 49`:
`min (d % 49) (49 − d % 49) ∈ {0,…,24}`. -/
def pairRep49 (d : ℕ) : ℕ := min (d % 49) (49 - d % 49)

/-- Sign-class representative of a residue mod 98:
`min (d % 98) (98 − d % 98) ∈ {0,…,49}`. -/
def rep98 (d : ℕ) : ℕ := min (d % 98) (98 - d % 98)

/-- The 24 pair-classes mod 49, named by their smaller representative. -/
def reps49 : Finset ℕ := Finset.Icc 1 24

/-- Representatives of `U_49/{±1}`: residues in `{1,…,24}` prime to 7.
Since `|λa|_49 = |(49 − λ)a|_49`, checking these 21 multipliers is
equivalent to checking all 42 units. -/
def units21 : Finset ℕ := (Finset.Icc 1 24).filter fun a => a % 7 ≠ 0

/-- The bad pair-sets, listed explicitly: the 63 bad 5-subsets of `reps49`,
i.e. the three `U_49/{±1}` orbits of the paper's representatives
`{1,3,4,5,18}`, `{1,4,6,10,11}`, `{1,4,6,10,22}` (independently verified).
Listed literally so the count and the paper correspondence are auditable
without re-running the enumeration. -/
def badSets49 : Finset (Finset ℕ) := {
    {1, 3, 4, 5, 18}, {1, 3, 8, 19, 22}, {1, 4, 6, 10, 11}, {1, 4, 6, 10, 22}, {1, 4, 18, 20, 22}, {1, 5, 6, 19, 20}, {1, 5, 8, 9, 13},
    {1, 5, 12, 19, 20}, {1, 6, 15, 16, 18}, {1, 8, 10, 17, 18}, {1, 8, 17, 18, 20}, {1, 9, 10, 16, 19}, {1, 11, 12, 13, 20}, {1, 12, 15, 22, 23},
    {1, 12, 19, 22, 23}, {2, 3, 5, 11, 24}, {2, 3, 5, 19, 24}, {2, 5, 6, 11, 16}, {2, 5, 8, 9, 13}, {2, 5, 8, 12, 20}, {2, 6, 8, 10, 13},
    {2, 8, 12, 20, 22}, {2, 9, 10, 11, 12}, {2, 9, 10, 11, 24}, {2, 9, 13, 15, 16}, {2, 9, 22, 23, 24}, {2, 10, 16, 18, 23}, {2, 11, 17, 18, 20},
    {2, 12, 13, 17, 19}, {2, 13, 15, 16, 20}, {3, 4, 13, 17, 20}, {3, 5, 9, 12, 15}, {3, 5, 11, 12, 17}, {3, 8, 9, 17, 24}, {3, 8, 11, 13, 15},
    {3, 8, 11, 15, 18}, {3, 8, 13, 17, 20}, {3, 10, 11, 13, 16}, {3, 10, 15, 22, 24}, {3, 12, 16, 18, 19}, {3, 12, 17, 18, 19}, {4, 5, 9, 16, 24},
    {4, 9, 10, 16, 24}, {4, 9, 13, 15, 22}, {4, 9, 17, 19, 23}, {4, 10, 12, 17, 22}, {4, 10, 16, 18, 23}, {4, 11, 15, 23, 24}, {4, 12, 16, 20, 23},
    {4, 17, 18, 19, 23}, {4, 18, 20, 22, 24}, {5, 8, 15, 20, 24}, {5, 8, 18, 19, 23}, {5, 11, 12, 17, 23}, {6, 8, 9, 15, 23}, {6, 9, 15, 16, 23},
    {6, 10, 15, 22, 24}, {6, 10, 18, 19, 24}, {6, 11, 13, 15, 24}, {6, 11, 13, 17, 24}, {6, 13, 16, 19, 22}, {6, 16, 19, 22, 23}, {6, 17, 20, 22, 23}
  }

/-- The 15 bad pair-sets containing `1` — the normalized representatives of
`badSets49`: every bad 5-set scales to one of these via `a ↦ rep(μ·a)` with
`μ ≡ ±u⁻¹`, `u` a unit element of the set. -/
def normBad49 : Finset (Finset ℕ) := {
    {1, 3, 4, 5, 18}, {1, 3, 8, 19, 22}, {1, 4, 6, 10, 11}, {1, 4, 6, 10, 22}, {1, 4, 18, 20, 22},
    {1, 5, 6, 19, 20}, {1, 5, 8, 9, 13}, {1, 5, 12, 19, 20}, {1, 6, 15, 16, 18}, {1, 8, 10, 17, 18},
    {1, 8, 17, 18, 20}, {1, 9, 10, 16, 19}, {1, 11, 12, 13, 20}, {1, 12, 15, 22, 23}, {1, 12, 19, 22, 23}
  }

/-- The 15 normalized bad tails: sorted `Q ∖ {1}` of each `normBad49`
member, as literal 4-tuples (cheaper to decide than a 15-way disjunction). -/
def normBadTails : Finset (ℕ × ℕ × ℕ × ℕ) :=
  {(3, 4, 5, 18), (3, 8, 19, 22), (4, 6, 10, 11), (4, 6, 10, 22), (4, 18, 20, 22),
   (5, 6, 19, 20), (5, 8, 9, 13), (5, 12, 19, 20), (6, 15, 16, 18),
   (8, 10, 17, 18), (8, 17, 18, 20), (9, 10, 16, 19), (11, 12, 13, 20),
   (12, 15, 22, 23), (12, 19, 22, 23)}

/-- Coverage table mod 49: `(λ, mask)` with bit `x` of `mask` set iff
`7 ≤ |λx|_49`, for `λ ∈ units21` and `x ∈ {0,…,49}`.  Precomputed so the
kernel checks bits instead of re-evaluating `absModN` in the enumeration. -/
def maskTable49 : Finset (ℕ × ℕ) := {
    (1, 8796093022080), (2, 70368479936496), (3, 140705275609080), (4, 280993814530044), (5, 279549219172860), (6, 278163506396412), (8, 553944429612990),
    (9, 536273772935070), (10, 544789169142750), (11, 509002878016974), (12, 525419940867822), (13, 525273350502126), (15, 491953530526710), (16, 482528837987766),
    (17, 482680696077750), (18, 490097505400566), (19, 542538045577950), (20, 544648959192030), (22, 420835251451386), (23, 386936824225770), (24, 375345781926570)
  }

/-- All mod-98 lifts of a mod-49 pair-set: `{a, 49 − a}` for `a ∈ Q`
(up to sign these are the only residues mod 98 reducing to the pair). -/
def lifts98 (Q : Finset ℕ) : Finset ℕ := Q.biUnion fun a => {a, 49 - a}

/-- The possible sign-class representatives of `d6` mod 98:
`d6 % 98` is a nonzero multiple of 7 different from 49, and
`min r (98 − r)` maps the twelve residues onto these six. -/
def d6res : Finset ℕ := {7, 14, 21, 28, 35, 42}

/-! ### Residue lemmas -/

/-- `absModN` only sees the residue `x % N`. -/
theorem absModN_congr_res {a b N : ℕ} (h : a % N = b % N) :
    absModN a N = absModN b N := by
  unfold absModN
  rw [h]

/-- `|k·d|_N` depends only on `d % N`. -/
theorem absModN_mul_mod (k d N : ℕ) :
    absModN (k * d) N = absModN (k * (d % N)) N :=
  absModN_congr_res ((Nat.mod_modEq d N).mul_left k).symm

/-- Sign flip inside the product: `|k·(N − r)|_N = |k·r|_N` for `r ≤ N`. -/
theorem absModN_mul_neg (k r N : ℕ) (hN : 0 < N) (hr : r ≤ N) :
    absModN (k * (N - r)) N = absModN (k * r) N := by
  have hs : (k * r) % N ≤ N := (Nat.mod_lt _ hN).le
  have hmod : (k * (N - r)) % N = (N - (k * r) % N) % N := by
    rw [← ZMod.natCast_eq_natCast_iff', Nat.cast_mul, Nat.cast_sub hr,
      ZMod.natCast_self, Nat.cast_sub hs, ZMod.natCast_self, ZMod.natCast_mod,
      Nat.cast_mul]
    ring
  have habs : absModN (k * (N - r)) N = absModN (N - (k * r) % N) N :=
    absModN_congr_res hmod
  rw [habs]
  unfold absModN
  rcases eq_or_ne ((k * r) % N) 0 with h0 | h0
  · rw [h0, Nat.sub_zero, Nat.mod_self]
    simp
  · have hslt : (k * r) % N < N := Nat.mod_lt _ hN
    have h1 : (N - (k * r) % N) % N = N - (k * r) % N :=
      Nat.mod_eq_of_lt (by omega)
    rw [h1, Nat.sub_sub_self hslt.le, min_comm]

/-- Modulus scaling: `|c·x|_{c·M} = c·|x|_M` (any `c > 0`). -/
theorem absModN_mul_scale (c x M : ℕ) (_hc : 0 < c) (hM : 0 < M) :
    absModN (c * x) (c * M) = c * absModN x M := by
  unfold absModN
  have hrx : x % M < M := Nat.mod_lt _ hM
  rw [Nat.mul_mod_mul_left]
  rcases le_or_gt (x % M) (M - x % M) with hle | hgt
  · have h1 : c * (x % M) ≤ c * M - c * (x % M) := by
      have : c * (x % M) + c * (x % M) ≤ c * M :=
        calc c * (x % M) + c * (x % M) = c * ((x % M) + (x % M)) := by ring
          _ ≤ c * M := Nat.mul_le_mul_left _ (by omega)
      omega
    rw [Nat.min_eq_left h1, Nat.min_eq_left hle]
  · have h3 : c * M - c * (x % M) ≤ c * (x % M) := by
      have : c * M ≤ c * (x % M) + c * (x % M) :=
        calc c * M = c * ((M - x % M) + (x % M)) := by
              rw [Nat.sub_add_cancel hrx.le]
          _ = c * (M - x % M) + c * (x % M) := by ring
          _ ≤ c * (x % M) + c * (x % M) :=
              Nat.add_le_add_right (Nat.mul_le_mul_left _ hgt.le) _
      omega
    rw [Nat.min_eq_right h3, Nat.min_eq_right hgt.le]
    have h4 : c * (M - x % M) + c * (x % M) = c * M := by
      rw [← Nat.left_distrib, Nat.sub_add_cancel hrx.le]
    omega

/-- `|λd|_49` equals `|λ·pairRep49 d|_49`. -/
theorem absModN_pairRep49 (lam d : ℕ) :
    absModN (lam * d) 49 = absModN (lam * pairRep49 d) 49 := by
  rw [absModN_mul_mod]
  unfold pairRep49
  rcases le_or_gt (d % 49) (49 - d % 49) with h | h
  · rw [min_eq_left h]
  · rw [min_eq_right h.le]
    exact (absModN_mul_neg lam (d % 49) 49 (by norm_num)
      (Nat.mod_lt _ (by norm_num)).le).symm

/-- `|λd|_98` equals `|λ·rep98 d|_98`. -/
theorem absModN_rep98 (lam d : ℕ) :
    absModN (lam * d) 98 = absModN (lam * rep98 d) 98 := by
  rw [absModN_mul_mod]
  unfold rep98
  rcases le_or_gt (d % 98) (98 - d % 98) with h | h
  · rw [min_eq_left h]
  · rw [min_eq_right h.le]
    exact (absModN_mul_neg lam (d % 98) 98 (by norm_num)
      (Nat.mod_lt _ (by norm_num)).le).symm

/-- `rep98` preserves parity (`98` is even). -/
theorem rep98_parity (d : ℕ) : rep98 d % 2 = d % 2 := by
  have h1 : d % 98 % 2 = d % 2 := Nat.mod_mod_of_dvd d (by norm_num)
  have hx : d % 98 < 98 := Nat.mod_lt _ (by norm_num)
  unfold rep98
  rcases le_or_gt (d % 98) (98 - d % 98) with h | h
  · rw [min_eq_left h]
    exact h1
  · rw [min_eq_right h.le]
    omega

/-- For `7 ∤ d`, the pair representative lies in `reps49`. -/
theorem pairRep49_mem_reps {d : ℕ} (hd : ¬ 7 ∣ d) :
    pairRep49 d ∈ reps49 := by
  have hr0 : d % 49 ≠ 0 := by
    intro h
    have h7 : d % 7 = 0 := by
      have h1 : d % 49 % 7 = d % 7 := Nat.mod_mod_of_dvd d (by norm_num)
      omega
    exact hd (Nat.dvd_iff_mod_eq_zero.mpr h7)
  have h48 : d % 49 < 49 := Nat.mod_lt _ (by norm_num)
  have hb : 1 ≤ pairRep49 d ∧ pairRep49 d ≤ 24 := by
    unfold pairRep49
    rcases le_or_gt (d % 49) (49 - d % 49) with hle | hle
    · rw [min_eq_left hle]
      omega
    · rw [min_eq_right hle.le]
      omega
  exact Finset.mem_Icc.mpr hb

/-- `rep98 d` is always one of the two lifts `{a, 49 − a}` of the pair-class
`a = pairRep49 d`.  (Holds for every `d`, no hypotheses needed.) -/
theorem rep98_spec (d : ℕ) :
    rep98 d = pairRep49 d ∨ rep98 d = 49 - pairRep49 d := by
  have hmod : d % 98 % 49 = d % 49 := Nat.mod_mod_of_dvd d (by norm_num)
  have hx98 : d % 98 < 98 := Nat.mod_lt _ (by norm_num)
  have hr49 : d % 49 < 49 := Nat.mod_lt _ (by norm_num)
  have hxcase : d % 98 = d % 49 ∨ d % 98 = d % 49 + 49 := by
    have h := Nat.div_add_mod (d % 98) 49
    rw [hmod] at h
    omega
  unfold rep98 pairRep49
  rcases le_or_gt (d % 49) (49 - d % 49) with hle | hle
  · rw [min_eq_left hle]
    rcases hxcase with hx | hx <;> rw [hx]
    · left
      exact min_eq_left (by omega)
    · right
      rw [min_eq_right (by omega)]
      omega
  · rw [min_eq_right hle.le]
    rcases hxcase with hx | hx <;> rw [hx]
    · right
      rw [min_eq_left (by omega)]
      omega
    · left
      rw [min_eq_right (by omega)]
      omega

/-- `rep98 d` lies in the lift set of any `Q` containing `pairRep49 d`. -/
theorem rep98_mem_lifts {Q : Finset ℕ} {d : ℕ} (h : pairRep49 d ∈ Q) :
    rep98 d ∈ lifts98 Q := by
  rw [lifts98, Finset.mem_biUnion]
  refine ⟨pairRep49 d, h, ?_⟩
  rcases rep98_spec d with h1 | h1 <;> rw [h1] <;> simp

/-- `ν₇ d6 = 1` forces `rep98 d6 ∈ {7,…,42}`: `d6 % 98` is a nonzero
multiple of 7 other than 49, and `min r (98−r)` folds the twelve residues
onto the six small ones. -/
theorem rep98_d6_mem {d6 : ℕ} (hd6 : padicValNat 7 d6 = 1) (hd6pos : 0 < d6) :
    rep98 d6 ∈ d6res := by
  have hd6ne : d6 ≠ 0 := Nat.ne_of_gt hd6pos
  have h7dvd : 7 ∣ d6 := by
    have h := (Nat.pow_dvd_iff_le_padicValNat (by norm_num) hd6ne).mpr
      (show 1 ≤ padicValNat 7 d6 by rw [hd6])
    rwa [pow_one] at h
  have h49ndvd : ¬ 49 ∣ d6 := by
    intro h
    have h2 := (Nat.pow_dvd_iff_le_padicValNat (by norm_num) hd6ne).mp
      (show (7 : ℕ) ^ 2 ∣ d6 by rwa [show (49 : ℕ) = 7 ^ 2 by norm_num] at h)
    rw [hd6] at h2
    norm_num at h2
  have hr7 : d6 % 98 % 7 = 0 := by
    rw [Nat.mod_mod_of_dvd _ (by norm_num : 7 ∣ 98)]
    exact Nat.dvd_iff_mod_eq_zero.mp h7dvd
  have hr98 : d6 % 98 < 98 := Nat.mod_lt _ (by norm_num)
  have hr0 : d6 % 98 ≠ 0 := by
    intro h
    exact h49ndvd (dvd_trans (by norm_num : 49 ∣ 98) (Nat.dvd_of_mod_eq_zero h))
  have hr49 : d6 % 98 ≠ 49 := by
    intro h
    apply h49ndvd
    have h1 : d6 = 98 * (d6 / 98) + d6 % 98 := (Nat.div_add_mod d6 98).symm
    rw [h] at h1
    exact ⟨2 * (d6 / 98) + 1, by omega⟩
  obtain ⟨k, hk⟩ : 7 ∣ d6 % 98 := Nat.dvd_iff_mod_eq_zero.mpr hr7
  have hk13 : k ≤ 13 := by omega
  have hk1 : 1 ≤ k := by omega
  have hk7 : k ≠ 7 := by omega
  unfold rep98 d6res
  rw [hk]
  interval_cases k <;> first | exact absurd rfl hk7 | decide

/-! ### `pairRep49` congruence and scaling lemmas -/

/-- `pairRep49` only sees the residue: congruent inputs give equal reps. -/
theorem pairRep49_congr {x y : ℕ} (h : x % 49 = y % 49) :
    pairRep49 x = pairRep49 y := by
  unfold pairRep49
  rw [h]

/-- `pairRep49` only sees the `±`-class: antipodal residues give equal reps. -/
theorem pairRep49_neg {x y : ℕ} (h : x % 49 + y % 49 = 49) :
    pairRep49 x = pairRep49 y := by
  have hxl : x % 49 < 49 := Nat.mod_lt _ (by norm_num)
  unfold pairRep49
  have hy : y % 49 = 49 - x % 49 := by omega
  rw [hy, Nat.sub_sub_self hxl.le, min_comm]

/-- `x ≡ −y` in `ZMod 49` makes the residues sum to 49 (nonzero case). -/
theorem mod_add_eq_49_of_zmod_neg {x y : ℕ} (h : (x : ZMod 49) = -(y : ZMod 49))
    (hy : y % 49 ≠ 0) : x % 49 + y % 49 = 49 := by
  have hxy : (x + y) % 49 = 0 := by
    have h2 : ((x + y : ℕ) : ZMod 49) = 0 := by
      push_cast
      rw [h, neg_add_cancel]
    exact Nat.mod_eq_zero_of_dvd ((ZMod.natCast_eq_zero_iff _ _).mp h2)
  have hxl : x % 49 < 49 := Nat.mod_lt _ (by norm_num)
  have hyl : y % 49 < 49 := Nat.mod_lt _ (by norm_num)
  have hdiv : 49 ∣ x % 49 + y % 49 := by
    have h' : (x % 49 + y % 49) % 49 = 0 := by
      have := hxy
      rwa [Nat.add_mod] at this
    exact Nat.dvd_of_mod_eq_zero h'
  obtain ⟨k, hk⟩ := hdiv
  omega

/-- `pairRep49` of an antipodal residue (`x ≡ −y` in `ZMod 49`). -/
theorem pairRep49_of_zmod_neg {x y : ℕ} (h : (x : ZMod 49) = -(y : ZMod 49)) :
    pairRep49 x = pairRep49 y := by
  rcases eq_or_ne (y % 49) 0 with hy | hy
  · have hx : x % 49 = 0 := by
      have hyz : ((y : ℕ) : ZMod 49) = 0 :=
        (ZMod.natCast_eq_zero_iff _ _).mpr (Nat.dvd_of_mod_eq_zero hy)
      have hxz : ((x : ℕ) : ZMod 49) = 0 := by rw [h, hyz]; exact neg_zero
      exact Nat.mod_eq_zero_of_dvd ((ZMod.natCast_eq_zero_iff _ _).mp hxz)
    unfold pairRep49
    rw [hx, hy]
  · exact pairRep49_neg (mod_add_eq_49_of_zmod_neg h hy)

/-- Composing scalings: `rep(μ · rep(ν·a)) = rep(μ·ν·a)`. -/
theorem pairRep49_mul_rep (μ ν a : ℕ) :
    pairRep49 (μ * pairRep49 (ν * a)) = pairRep49 (μ * (ν * a)) := by
  have hna : (ν * a) % 49 < 49 := Nat.mod_lt _ (by norm_num)
  unfold pairRep49
  rcases le_or_gt ((ν * a) % 49) (49 - (ν * a) % 49) with hc | hc
  · rw [min_eq_left hc]
    exact pairRep49_congr ((Nat.mod_modEq (ν * a) 49).mul_left μ)
  · rw [min_eq_right hc.le]
    apply pairRep49_of_zmod_neg
    rw [Nat.cast_mul, Nat.cast_sub hna.le, ZMod.natCast_self, Nat.cast_mul,
      ZMod.natCast_mod]
    ring

/-- A nonzero residue mod 49 has its pair rep in `reps49`. -/
theorem pairRep49_mem_reps' {x : ℕ} (hx : x % 49 ≠ 0) :
    pairRep49 x ∈ reps49 := by
  have h49 : x % 49 < 49 := Nat.mod_lt _ (by norm_num)
  have hb : 1 ≤ pairRep49 x ∧ pairRep49 x ≤ 24 := by
    unfold pairRep49
    rcases le_or_gt (x % 49) (49 - x % 49) with hle | hle
    · rw [min_eq_left hle]; omega
    · rw [min_eq_right hle.le]; omega
  exact Finset.mem_Icc.mpr hb

/-- For a representative `a ∈ {1,…,24}`, `rep a = a`. -/
theorem pairRep49_self {a : ℕ} (ha : a ∈ reps49) : pairRep49 a = a := by
  have ha' := Finset.mem_Icc.mp ha
  unfold pairRep49
  rw [Nat.mod_eq_of_lt (by omega : a < 49)]
  exact min_eq_left (by omega)

/-- `rep μ ∈ units21` whenever `μ` is a unit mod 49. -/
theorem pairRep49_mem_units21 {μ : ℕ} (hμ : μ % 7 ≠ 0) (hμ0 : μ % 49 ≠ 0) :
    pairRep49 μ ∈ units21 := by
  have hm : pairRep49 μ ∈ reps49 := pairRep49_mem_reps' hμ0
  have hμ49 : μ % 49 % 7 = μ % 7 := Nat.mod_mod_of_dvd μ (by norm_num)
  have h49 : μ % 49 < 49 := Nat.mod_lt _ (by norm_num)
  have h7 : pairRep49 μ % 7 ≠ 0 := by
    unfold pairRep49
    rcases le_or_gt (μ % 49) (49 - μ % 49) with hle | hle
    · rw [min_eq_left hle]; omega
    · rw [min_eq_right hle.le]; omega
  exact Finset.mem_filter.mpr ⟨hm, h7⟩

/-- `pairRep49 x = pairRep49 y` forces `x ≡ ±y`. -/
theorem pairRep49_eq_iff {x y : ℕ} :
    pairRep49 x = pairRep49 y ↔
      x % 49 = y % 49 ∨ x % 49 + y % 49 = 49 := by
  unfold pairRep49
  have hxl : x % 49 < 49 := Nat.mod_lt _ (by norm_num)
  have hyl : y % 49 < 49 := Nat.mod_lt _ (by norm_num)
  constructor
  · intro h
    rcases le_or_gt (x % 49) (49 - x % 49) with h1 | h1 <;>
    rcases le_or_gt (y % 49) (49 - y % 49) with h2 | h2
    · rw [min_eq_left h1, min_eq_left h2] at h; exact Or.inl h
    · rw [min_eq_left h1, min_eq_right h2.le] at h; exact Or.inr (by omega)
    · rw [min_eq_right h1.le, min_eq_left h2] at h; exact Or.inr (by omega)
    · rw [min_eq_right h1.le, min_eq_right h2.le] at h; exact Or.inl (by omega)
  · rintro (h | h)
    · rw [h]
    · have hy : y % 49 = 49 - x % 49 := by omega
      rw [hy, Nat.sub_sub_self hxl.le, min_comm]

/-- Scaling by a unit is injective on pair reps (a rep collision means
`a ≡ ±b`, impossible inside `{1,…,24}`). -/
theorem pairRep49_mul_injOn {μ : ℕ} (hμ : μ % 7 ≠ 0) :
    Set.InjOn (fun a => pairRep49 (μ * a)) (↑reps49) := by
  intro a ha b hb hab
  have ha' := Finset.mem_Icc.mp ha
  have hb' := Finset.mem_Icc.mp hb
  have hcop : Nat.Coprime μ 49 := by
    have h7 : Nat.Coprime μ 7 :=
      ((Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 7)).mpr
        (fun h => hμ (Nat.dvd_iff_mod_eq_zero.mp h))).symm
    rwa [show (49 : ℕ) = 7 ^ 2 by norm_num,
      Nat.coprime_pow_right_iff (show 0 < 2 by norm_num)]
  have hunit : IsUnit (μ : ZMod 49) := (ZMod.isUnit_iff_coprime μ 49).mpr hcop
  rcases (pairRep49_eq_iff.mp hab) with hmod | hneg
  · have hz : (μ : ZMod 49) * a = (μ : ZMod 49) * b := by
      have h2 : ((μ * a : ℕ) : ZMod 49) = (μ * b : ℕ) :=
        (ZMod.natCast_eq_natCast_iff' _ _ _).mpr hmod
      rwa [Nat.cast_mul, Nat.cast_mul] at h2
    have h3 : (a : ZMod 49) = b := hunit.mul_left_cancel hz
    have h4 : a % 49 = b % 49 := (ZMod.natCast_eq_natCast_iff' _ _ _).mp h3
    rw [Nat.mod_eq_of_lt (by omega : a < 49), Nat.mod_eq_of_lt (by omega : b < 49)] at h4
    exact h4
  · have hsum : (μ * a + μ * b) % 49 = 0 := by
      rw [Nat.add_mod, hneg]
    have hmul : (μ * (a + b)) % 49 = 0 := by rw [mul_add]; exact hsum
    have hdvd : 49 ∣ a + b :=
      hcop.symm.dvd_of_dvd_mul_left (Nat.dvd_of_mod_eq_zero hmul)
    obtain ⟨k, hk⟩ := hdvd
    omega

/-- `rep(μ·a) ∈ reps49` for unit `μ` and `a ∈ reps49` nonzero mod 49. -/
theorem pairRep49_mul_mem_reps {μ a : ℕ} (hμ : μ % 7 ≠ 0) (ha : a ∈ reps49) :
    pairRep49 (μ * a) ∈ reps49 := by
  have ha' := Finset.mem_Icc.mp ha
  have hcop : Nat.Coprime μ 49 := by
    have h7 : Nat.Coprime μ 7 :=
      ((Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 7)).mpr
        (fun h => hμ (Nat.dvd_iff_mod_eq_zero.mp h))).symm
    rwa [show (49 : ℕ) = 7 ^ 2 by norm_num,
      Nat.coprime_pow_right_iff (show 0 < 2 by norm_num)]
  apply pairRep49_mem_reps'
  intro h
  have hdvd : 49 ∣ a := hcop.symm.dvd_of_dvd_mul_left (Nat.dvd_of_mod_eq_zero h)
  obtain ⟨k, hk⟩ := hdvd
  omega

/-- Every unit rep has an inverse rep: `rep(ν·u) = 1`. (441-case check.) -/
theorem units21_inv : ∀ u ∈ units21, ∃ ν ∈ units21, pairRep49 (ν * u) = 1 := by
  decide

/-- `absModN` of a `pairRep49`-rescaled element equals the original. -/
theorem absModN_mul_rep49 (μ ν a : ℕ) :
    absModN (μ * pairRep49 (ν * a)) 49 = absModN (μ * (ν * a)) 49 := by
  have hna : (ν * a) % 49 < 49 := Nat.mod_lt _ (by norm_num)
  unfold pairRep49
  rcases le_or_gt ((ν * a) % 49) (49 - (ν * a) % 49) with hc | hc
  · rw [min_eq_left hc]
    exact (absModN_mul_mod μ (ν * a) 49).symm
  · rw [min_eq_right hc.le]
    exact (absModN_mul_neg μ ((ν * a) % 49) 49 (by norm_num) hna.le).trans
      (absModN_mul_mod μ (ν * a) 49).symm

/-- `absModN` sees only the rep of the multiplier: `|rep(k)·a| = |k·a|`. -/
theorem absModN_rep49_mul (k a : ℕ) :
    absModN (pairRep49 k * a) 49 = absModN (k * a) 49 := by
  have hkl : k % 49 < 49 := Nat.mod_lt _ (by norm_num)
  unfold pairRep49
  rcases le_or_gt (k % 49) (49 - k % 49) with hc | hc
  · rw [min_eq_left hc]
    apply absModN_congr_res
    exact (Nat.mod_modEq k 49).mul_right a
  · rw [min_eq_right hc.le]
    rw [Nat.mul_comm (49 - k % 49) a]
    refine (absModN_mul_neg a (k % 49) 49 (by norm_num) hkl.le).trans ?_
    apply absModN_congr_res
    calc (a * (k % 49)) % 49 = (k % 49 * a) % 49 := by rw [Nat.mul_comm]
      _ = (k * a) % 49 := (Nat.mod_modEq k 49).mul_right a

set_option maxRecDepth 1000000 in
/-- Audit: the bad pair-sets are exactly the 63 sets counted independently
(the three `U_49/{±1}` orbits of the paper). -/
theorem badSets49_card : badSets49.card = 63 := by
  decide +kernel
