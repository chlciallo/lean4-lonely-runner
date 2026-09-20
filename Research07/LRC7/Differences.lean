/-
Copyright (c) 2026 Research07 contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Research07 contributors
-/
import Research07.LRC7.Filtering

/-!
# Difference machinery for the `|A| = 5, m > 1` case (paper §6)

The paper's `e(x,y)` and `ẽ(x,y)` combine two same-class elements into a
single difference whose `q`-digit controls the pair's covering length.
For elements with residues in `{1,2,4}` the ratio `r(y)/r(x) ∈ {1,2,4}`:

```
e(x,y) = 2x−y  if r(y)=2r(x)      ẽ(x,y) = 2q(x)−q(y)
       = 2y−x  if r(x)=2r(y)              = 2q(y)−q(x)
       = x−y   if r(y)=r(x)               = q(x)−q(y)
```

(`r(y)=4r(x)` implies `r(x)=2r(y)` since `2·4≡1`, so the three cases cover
all pairs.)  `e` is modeled as a residue modulo `N = 7^{m+1}` (`eMod7`),
and `ẽ` directly on `ZMod 7` digits (`etd7`).  All three are defined by
if-chains on the `runit7` conditions so that proofs can use `split_ifs`.

Main contents:

* `residueRelOf x y` — which of the three ratio cases applies.
* `eMod7 m x y` — `e(x,y)` as a natural residue mod `7^{m+1}`.
* `etd7 m x y` — `ẽ(x,y)` in `ZMod 7`.
* Lemma 4: `ẽ` is invariant under `Λ_i` for `i ≤` the common level
  (`etd7_multLow_same`, `etd7_multLow_low`), and `q(e) − ẽ ∈ {0,±1}`
  (`{0,−1}` in the same-`r` case).  NOTE: the sign convention here is
  `q(e) − ẽ ∈ {0,6}` for equal residues — this is the convention actually
  used by the paper in Lemma 9 (the statement in Lemma 4(ii) of the paper
  has the sign flipped).
-/

/-- The residue-ratio class of a pair: `r(y) ∈ {r(x), 2r(x), 4r(x)}`. -/
inductive residueRel : Type
  | same   -- r(y) = r(x)   → e = x−y,  ẽ = q(x)−q(y)
  | twoX   -- r(y) = 2r(x)  → e = 2x−y, ẽ = 2q(x)−q(y)
  | twoY   -- r(x) = 2r(y)  → e = 2y−x, ẽ = 2q(y)−q(x)
  deriving DecidableEq, Repr

/-- The residue-ratio class of `x y` (for elements with `r ∈ {1,2,4}` every
pair falls in exactly one class). -/
def residueRelOf (x y : ℕ) : residueRel :=
  if runit7 y = 2 * runit7 x then residueRel.twoX
  else if runit7 x = 2 * runit7 y then residueRel.twoY
  else residueRel.same

/-- `e(x,y)` as a residue modulo `7^{m+1}` (the combination may "go
negative"; the residue wraps it correctly). -/
def eMod7 (m x y : ℕ) : ℕ :=
  if runit7 y = 2 * runit7 x then
    (2 * (x % 7 ^ (m + 1)) + 7 ^ (m + 1) - (y % 7 ^ (m + 1))) % 7 ^ (m + 1)
  else if runit7 x = 2 * runit7 y then
    (2 * (y % 7 ^ (m + 1)) + 7 ^ (m + 1) - (x % 7 ^ (m + 1))) % 7 ^ (m + 1)
  else
    ((x % 7 ^ (m + 1)) + 7 ^ (m + 1) - (y % 7 ^ (m + 1))) % 7 ^ (m + 1)

/-- `ẽ(x,y)` in `ZMod 7`. -/
def etd7 (m x y : ℕ) : ZMod 7 :=
  if runit7 y = 2 * runit7 x then 2 * qdig7 m x - qdig7 m y
  else if runit7 x = 2 * runit7 y then 2 * qdig7 m y - qdig7 m x
  else qdig7 m x - qdig7 m y

/-- The paper's hypothesis on residue ratios: `r(y)/r(x) ∈ {1,2,4}`,
phrased as the three `e`-cases. -/
def ratioCases (x y : ℕ) : Prop :=
  runit7 y = runit7 x ∨ runit7 y = 2 * runit7 x ∨ runit7 x = 2 * runit7 y

/-- `residueRelOf x y = twoX` iff `r(y) = 2r(x)`. -/
theorem residueRelOf_eq_twoX {x y : ℕ} :
    residueRelOf x y = residueRel.twoX ↔ runit7 y = 2 * runit7 x := by
  unfold residueRelOf
  by_cases h : runit7 y = 2 * runit7 x
  · rw [if_pos h]
    exact ⟨fun _ => h, fun _ => rfl⟩
  · rw [if_neg h]
    by_cases h' : runit7 x = 2 * runit7 y
    · rw [if_pos h']
      exact ⟨fun hh => absurd hh (by decide), fun hh => absurd hh h⟩
    · rw [if_neg h']
      exact ⟨fun hh => absurd hh (by decide), fun hh => absurd hh h⟩

/-- `residueRelOf x y = twoY` iff `r(x) = 2r(y)` and `r(y) ≠ 2r(x)`. -/
theorem residueRelOf_eq_twoY {x y : ℕ} :
    residueRelOf x y = residueRel.twoY ↔
      runit7 y ≠ 2 * runit7 x ∧ runit7 x = 2 * runit7 y := by
  unfold residueRelOf
  by_cases h : runit7 y = 2 * runit7 x
  · rw [if_pos h]
    exact ⟨fun hh => absurd hh (by decide), fun hh => absurd h hh.1⟩
  · rw [if_neg h]
    by_cases h' : runit7 x = 2 * runit7 y
    · rw [if_pos h']
      exact ⟨fun _ => ⟨h, h'⟩, fun _ => rfl⟩
    · rw [if_neg h']
      exact ⟨fun hh => absurd hh (by decide), fun hh => absurd hh.2 h'⟩

/-- `residueRelOf x y = same` iff neither `2`-ratio holds (which forces
`r(y) = r(x)` under `ratioCases`). -/
theorem residueRelOf_eq_same {x y : ℕ} :
    residueRelOf x y = residueRel.same ↔
      runit7 y ≠ 2 * runit7 x ∧ runit7 x ≠ 2 * runit7 y := by
  unfold residueRelOf
  by_cases h : runit7 y = 2 * runit7 x
  · rw [if_pos h]
    exact ⟨fun hh => absurd hh (by decide), fun hh => absurd h hh.1⟩
  · rw [if_neg h]
    by_cases h' : runit7 x = 2 * runit7 y
    · rw [if_pos h']
      exact ⟨fun hh => absurd hh (by decide), fun hh => absurd h' hh.2⟩
    · rw [if_neg h']
      exact ⟨fun _ => ⟨h, h'⟩, fun _ => rfl⟩

/-- In the `same` branch the residues are actually equal, provided the
pair satisfies `ratioCases`. -/
theorem runit7_eq_of_rel_same {x y : ℕ}
    (h : residueRelOf x y = residueRel.same) (hr : ratioCases x y) :
    runit7 y = runit7 x := by
  obtain ⟨h1, h2⟩ := (residueRelOf_eq_same).mp h
  rcases hr with h1' | h2' | h3'
  · exact h1'
  · exact absurd h2' h1
  · exact absurd h3' h2

/-! ### `Λ_j` multiplier arithmetic -/

/-- `Λ_j` elements are `≡ 1 (mod 7)` for `j < m`. -/
theorem multLow_mod7 {m j k : ℕ} (hjm : j < m) :
    (1 + k * 7 ^ (m - j)) % 7 = 1 := by
  obtain ⟨e, he⟩ : ∃ e, m - j = e + 1 := ⟨m - j - 1, by omega⟩
  have h7k : 7 ∣ k * 7 ^ (m - j) :=
    dvd_mul_of_dvd_right (by rw [he, pow_succ']; exact dvd_mul_right 7 _) k
  obtain ⟨t, ht⟩ := h7k
  rw [ht, Nat.add_mod]
  simp

/-- `Λ_j` elements are not divisible by `7` for `j < m`. -/
theorem multLow_not_dvd {m j k : ℕ} (hjm : j < m) :
    ¬ 7 ∣ (1 + k * 7 ^ (m - j)) := by
  intro hdvd
  have h := multLow_mod7 hjm (k := k)
  rw [Nat.dvd_iff_mod_eq_zero] at hdvd
  omega

/-- `runit7` of a `Λ_j` element is `1` for `j < m`. -/
theorem runit7_multLow {m j k : ℕ} (hjm : j < m) :
    runit7 (1 + k * 7 ^ (m - j)) = 1 := by
  unfold runit7
  have h0 : padicValNat 7 (1 + k * 7 ^ (m - j)) = 0 :=
    padicValNat.eq_zero_of_not_dvd (multLow_not_dvd hjm)
  rw [h0, pow_zero, Nat.div_one]
  exact (ZMod.natCast_eq_natCast_iff' _ _ _).mpr (multLow_mod7 hjm)

/-- Multiplying by a `Λ_j` element preserves `runit7` of a level-`j`
element: `r(λx) = r(x)`. -/
theorem runit7_multLow_apply {m j k x : ℕ} (hjm : j < m) (hx : padicValNat 7 x = j) :
    runit7 ((1 + k * 7 ^ (m - j)) * x) = runit7 x := by
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [mul_zero]
  set u := Nat.divMaxPow x 7 with hu
  have hx_eq : x = u * 7 ^ j := by
    have h := Nat.divMaxPow_mul_pow_padicValNat 7 x
    rw [hx, ← hu] at h
    exact h.symm
  have hval : padicValNat 7 ((1 + k * 7 ^ (m - j)) * x) = j := by
    rw [padicValNat_mul_seven (multLow_not_dvd hjm) hx0, hx]
  unfold runit7
  rw [hval, hx, hx_eq]
  have hLHS : (1 + k * 7 ^ (m - j)) * (u * 7 ^ j) / 7 ^ j
      = (1 + k * 7 ^ (m - j)) * u := by
    rw [show (1 + k * 7 ^ (m - j)) * (u * 7 ^ j)
        = ((1 + k * 7 ^ (m - j)) * u) * 7 ^ j by ring,
      Nat.mul_div_cancel _ (Nat.pow_pos (by norm_num))]
  rw [hLHS, Nat.mul_div_cancel _ (Nat.pow_pos (by norm_num))]
  have hmod : (1 + k * 7 ^ (m - j)) * u % 7 = u % 7 := by
    obtain ⟨t, ht⟩ : 7 ∣ k * 7 ^ (m - j) := by
      apply dvd_mul_of_dvd_right _ k
      obtain ⟨e, he⟩ : ∃ e, m - j = e + 1 := ⟨m - j - 1, by omega⟩
      rw [he, pow_succ']
      exact dvd_mul_right 7 _
    rw [ht]
    have hexp : (1 + 7 * t) * u = u + 7 * (t * u) := by ring
    rw [hexp, Nat.add_mul_mod_self_left]
  exact (ZMod.natCast_eq_natCast_iff' _ _ _).mpr hmod

/-- `residueRel` is preserved by `Λ_j` multipliers at the common level. -/
theorem residueRel_multLow {m j k x y : ℕ} (hjm : j < m)
    (hx : padicValNat 7 x = j) (hy : padicValNat 7 y = j) :
    residueRelOf ((1 + k * 7 ^ (m - j)) * x) ((1 + k * 7 ^ (m - j)) * y)
      = residueRelOf x y := by
  have hrx := runit7_multLow_apply (k := k) hjm hx
  have hry := runit7_multLow_apply (k := k) hjm hy
  unfold residueRelOf
  rw [hrx, hry]

/-- **Lemma 4(i), same-level case**: a `Λ_j` multiplier at the common level
`j` of `x,y` shifts both `q`'s by `k·r`, leaving `ẽ` invariant (for pairs
satisfying `ratioCases`). -/
theorem etd7_multLow_same {m j k x y : ℕ} (hjm : j < m)
    (hx : padicValNat 7 x = j) (hy : padicValNat 7 y = j)
    (hrr : ratioCases x y) :
    etd7 m ((1 + k * 7 ^ (m - j)) * x) ((1 + k * 7 ^ (m - j)) * y)
      = etd7 m x y := by
  have hqx := qdig7_multLow (k := k) hjm hx
  have hqy := qdig7_multLow (k := k) hjm hy
  have hrx := runit7_multLow_apply (k := k) hjm hx
  have hry := runit7_multLow_apply (k := k) hjm hy
  unfold etd7
  rw [hrx, hry]
  split_ifs with h1 h2
  · rw [hqx, hqy, h1]
    ring
  · rw [hqx, hqy, h2]
    ring
  · rcases hrr with hr1 | hr2 | hr3
    · rw [hqx, hqy, hr1]
      ring
    · exact absurd hr2 h1
    · exact absurd hr3 h2

/-! ### Residues determine valuation and unit digit (for `ν ≤ m`) -/

/-- `padicValNat` of an element `≤ m` is determined by its residue
mod `7^{m+1}`: `a ≡ b (mod 7^{m+1})` and `ν(a) ≤ m` imply `ν(b) = ν(a)`. -/
theorem padicValNat_eq_of_mod {m a b : ℕ}
    (h : a % 7 ^ (m + 1) = b % 7 ^ (m + 1))
    (ha : padicValNat 7 a ≤ m) (ha0 : a ≠ 0) :
    padicValNat 7 a = padicValNat 7 b := by
  set ν := padicValNat 7 a with hν
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [Nat.zero_mod] at h
    have hdvd : 7 ^ (m + 1) ∣ a := Nat.dvd_iff_mod_eq_zero.mpr h
    have hle : m + 1 ≤ padicValNat 7 a :=
      (Nat.pow_dvd_iff_le_padicValNat (by norm_num) ha0).mp hdvd
    omega
  have hZ : ((7 : ℤ) ^ (m + 1)) ∣ (a : ℤ) - b := by
    have hmod : ((a % 7 ^ (m + 1) : ℕ) : ℤ) = ((b % 7 ^ (m + 1) : ℕ) : ℤ) := by
      exact_mod_cast h
    rw [Int.natCast_mod, Int.natCast_mod] at hmod
    have hme : (b : ℤ) ≡ a [ZMOD ((7 ^ (m + 1) : ℕ) : ℤ)] := hmod.symm
    have hcast : ((7 ^ (m + 1) : ℕ) : ℤ) = (7 : ℤ) ^ (m + 1) := by
      push_cast
      ring
    rw [hcast] at hme
    exact (Int.modEq_iff_dvd).mp hme
  have hνa : (7 : ℤ) ^ ν ∣ (a : ℤ) :=
    Int.ofNat_dvd.mpr
      ((Nat.pow_dvd_iff_le_padicValNat (by norm_num) ha0).mpr le_rfl)
  have hνdiff : (7 : ℤ) ^ ν ∣ (a : ℤ) - b :=
    dvd_trans (pow_dvd_pow _ (by omega : ν ≤ m + 1)) hZ
  have hνb : (7 : ℤ) ^ ν ∣ (b : ℤ) := by
    have heq : (b : ℤ) = a - ((a : ℤ) - b) := by ring
    rw [heq]
    exact Int.dvd_sub hνa hνdiff
  have hle1 : ν ≤ padicValNat 7 b :=
    (Nat.pow_dvd_iff_le_padicValNat (by norm_num) hb0).mp
      (Int.ofNat_dvd.mp hνb)
  have hle2 : padicValNat 7 b ≤ ν := by
    by_contra hlt
    push Not at hlt
    have hν1b : (7 : ℤ) ^ (ν + 1) ∣ (b : ℤ) :=
      Int.ofNat_dvd.mpr
        ((Nat.pow_dvd_iff_le_padicValNat (by norm_num) hb0).mpr hlt)
    have hν1diff : (7 : ℤ) ^ (ν + 1) ∣ (a : ℤ) - b :=
      dvd_trans (pow_dvd_pow _ (by omega : ν + 1 ≤ m + 1)) hZ
    have hν1a : (7 : ℤ) ^ (ν + 1) ∣ (a : ℤ) := by
      have heq : (a : ℤ) = b + ((a : ℤ) - b) := by ring
      rw [heq]
      exact Int.dvd_add hν1b hν1diff
    have : ν + 1 ≤ padicValNat 7 a :=
      (Nat.pow_dvd_iff_le_padicValNat (by norm_num) ha0).mp
        (Int.ofNat_dvd.mp hν1a)
    omega
  omega

/-- `runit7` of an element `≤ m` is determined by its residue
mod `7^{m+1}`. -/
theorem runit7_eq_of_mod {m a b : ℕ}
    (h : a % 7 ^ (m + 1) = b % 7 ^ (m + 1))
    (ha : padicValNat 7 a ≤ m) (ha0 : a ≠ 0) :
    runit7 a = runit7 b := by
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [Nat.zero_mod] at h
    have hdvd : 7 ^ (m + 1) ∣ a := Nat.dvd_iff_mod_eq_zero.mpr h
    have hle : m + 1 ≤ padicValNat 7 a :=
      (Nat.pow_dvd_iff_le_padicValNat (by norm_num) ha0).mp hdvd
    omega
  have hν : padicValNat 7 b = padicValNat 7 a :=
    (padicValNat_eq_of_mod h ha ha0).symm
  obtain ⟨c, hc⟩ : ∃ c, b = a + c * 7 ^ (m + 1) ∨
      a = b + c * 7 ^ (m + 1) := by
    rcases le_total a b with hab | hab
    · obtain ⟨c, hcb⟩ := (Nat.modEq_iff_dvd' hab).mp h
      refine ⟨c, Or.inl ?_⟩
      rw [mul_comm c (7 ^ (m + 1))]
      omega
    · obtain ⟨c, hcb⟩ := (Nat.modEq_iff_dvd' hab).mp h.symm
      refine ⟨c, Or.inr ?_⟩
      rw [mul_comm c (7 ^ (m + 1))]
      omega
  rcases hc with hc | hc
  · -- `b = a + c·7^{m+1}`: then `b / 7^ν = a / 7^ν + c·7^{m+1−ν}`.
    subst hc
    have hν' : padicValNat 7 (a + c * 7 ^ (m + 1)) = padicValNat 7 a := hν
    have hdvd : 7 ^ padicValNat 7 a ∣ a :=
      (Nat.pow_dvd_iff_le_padicValNat (by norm_num) ha0).mpr le_rfl
    have hfac : c * 7 ^ (m + 1)
        = (c * 7 ^ (m + 1 - padicValNat 7 a)) * 7 ^ padicValNat 7 a := by
      rw [mul_assoc, ← pow_add,
        Nat.sub_add_cancel (by omega : padicValNat 7 a ≤ m + 1)]
    have hdiv : (a + c * 7 ^ (m + 1)) / 7 ^ padicValNat 7 a
        = a / 7 ^ padicValNat 7 a + c * 7 ^ (m + 1 - padicValNat 7 a) := by
      rw [hfac]
      exact Nat.add_mul_div_right _ _ (Nat.pow_pos (by norm_num))
    unfold runit7
    rw [hν', hdiv, ZMod.natCast_eq_natCast_iff']
    have hmod : (a / 7 ^ padicValNat 7 a
          + c * 7 ^ (m + 1 - padicValNat 7 a)) % 7
        = (a / 7 ^ padicValNat 7 a) % 7 := by
      obtain ⟨t, ht⟩ : 7 ∣ c * 7 ^ (m + 1 - padicValNat 7 a) := by
        apply dvd_mul_of_dvd_right _ c
        obtain ⟨e, he⟩ : ∃ e, m + 1 - padicValNat 7 a = e + 1 :=
          ⟨m - padicValNat 7 a, by omega⟩
        rw [he, pow_succ']
        exact dvd_mul_right 7 _
      rw [ht, Nat.add_mod]
      simp
    exact hmod.symm
  · -- `a = b + c·7^{m+1}` (symmetric)
    subst hc
    have hν' : padicValNat 7 b = padicValNat 7 (b + c * 7 ^ (m + 1)) := hν
    have hdvd : 7 ^ padicValNat 7 b ∣ b :=
      (Nat.pow_dvd_iff_le_padicValNat (by norm_num) hb0).mpr le_rfl
    have hfac : c * 7 ^ (m + 1)
        = (c * 7 ^ (m + 1 - padicValNat 7 b)) * 7 ^ padicValNat 7 b := by
      rw [mul_assoc, ← pow_add,
        Nat.sub_add_cancel (by omega : padicValNat 7 b ≤ m + 1)]
    have hdiv : (b + c * 7 ^ (m + 1)) / 7 ^ padicValNat 7 b
        = b / 7 ^ padicValNat 7 b + c * 7 ^ (m + 1 - padicValNat 7 b) := by
      rw [hfac]
      exact Nat.add_mul_div_right _ _ (Nat.pow_pos (by norm_num))
    unfold runit7
    rw [← hν', hdiv, ZMod.natCast_eq_natCast_iff']
    have hmod : (b / 7 ^ padicValNat 7 b
          + c * 7 ^ (m + 1 - padicValNat 7 b)) % 7
        = (b / 7 ^ padicValNat 7 b) % 7 := by
      obtain ⟨t, ht⟩ : 7 ∣ c * 7 ^ (m + 1 - padicValNat 7 b) := by
        apply dvd_mul_of_dvd_right _ c
        obtain ⟨e, he⟩ : ∃ e, m + 1 - padicValNat 7 b = e + 1 :=
          ⟨m - padicValNat 7 b, by omega⟩
        rw [he, pow_succ']
        exact dvd_mul_right 7 _
      rw [ht, Nat.add_mod]
      simp
    exact hmod

/-- `residueRel` is preserved under verbatim congruence (both valuations
`≤ m`). -/
theorem residueRel_eq_of_mod {m x y x' y' : ℕ}
    (hx : x % 7 ^ (m + 1) = x' % 7 ^ (m + 1))
    (hy : y % 7 ^ (m + 1) = y' % 7 ^ (m + 1))
    (hxm : padicValNat 7 x ≤ m) (hx0 : x ≠ 0)
    (hym : padicValNat 7 y ≤ m) (hy0 : y ≠ 0) :
    residueRelOf x y = residueRelOf x' y' := by
  have hrx := runit7_eq_of_mod hx hxm hx0
  have hry := runit7_eq_of_mod hy hym hy0
  unfold residueRelOf
  rw [← hrx, ← hry]

/-- **Lemma 4(i), verbatim case**: `Λ_j` with `j <` both levels preserves
residues mod `7^{m+1}`, hence `ẽ`. -/
theorem etd7_multLow_low {m j k x y : ℕ} (hjm : j < m)
    (hx : j < padicValNat 7 x) (hy : j < padicValNat 7 y)
    (hxm : padicValNat 7 x ≤ m) (hx0 : x ≠ 0)
    (hym : padicValNat 7 y ≤ m) (hy0 : y ≠ 0) :
    etd7 m ((1 + k * 7 ^ (m - j)) * x) ((1 + k * 7 ^ (m - j)) * y)
      = etd7 m x y := by
  have hxres := residN_multLow7 (k := k) hjm hx
  have hyres := residN_multLow7 (k := k) hjm hy
  have hxm' : padicValNat 7 ((1 + k * 7 ^ (m - j)) * x) ≤ m := by
    rw [padicValNat_mul_seven (multLow_not_dvd hjm) hx0]
    exact hxm
  have hym' : padicValNat 7 ((1 + k * 7 ^ (m - j)) * y) ≤ m := by
    rw [padicValNat_mul_seven (multLow_not_dvd hjm) hy0]
    exact hym
  have hx0' : (1 + k * 7 ^ (m - j)) * x ≠ 0 :=
    mul_ne_zero (by omega) hx0
  have hy0' : (1 + k * 7 ^ (m - j)) * y ≠ 0 :=
    mul_ne_zero (by omega) hy0
  have hrx : runit7 ((1 + k * 7 ^ (m - j)) * x) = runit7 x :=
    runit7_eq_of_mod hxres hxm' hx0'
  have hry : runit7 ((1 + k * 7 ^ (m - j)) * y) = runit7 y :=
    runit7_eq_of_mod hyres hym' hy0'
  unfold etd7
  rw [hrx, hry, qdig7_congr hxres, qdig7_congr hyres]

/-! ### Digit arithmetic for `eMod7` (Lemma 4(ii)) -/

/-- `(a·7^m + b) / 7^m = a` when `b < 7^m`. -/
private theorem mul_pow_add_div {a b m : ℕ} (hb : b < 7 ^ m) :
    (a * 7 ^ m + b) / 7 ^ m = a := by
  have hP : 0 < 7 ^ m := Nat.pow_pos (by norm_num)
  rw [add_comm (a * 7 ^ m) b, mul_comm a (7 ^ m),
    Nat.add_mul_div_left _ _ hP, Nat.div_eq_of_lt hb, zero_add]

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

/-- **Lemma 4(ii), equal-residue case**: for `r(x) = r(y)` (`e = x−y`),
`q(e) − ẽ ∈ {0, 6}` — the borrow at the top digit is `0` or `1`.
Sign convention as used by the paper in Lemma 9. -/
theorem qdig_eMod_sub_etd7_same {m x y : ℕ}
    (hrel : residueRelOf x y = residueRel.same) :
    qdig7 m (eMod7 m x y) - etd7 m x y ∈ ({0, 6} : Finset (ZMod 7)) := by
  obtain ⟨hne1, hne2⟩ := (residueRelOf_eq_same).mp hrel
  obtain ⟨q1, f1, hX, hq1, hf1⟩ := residue_decomp (m := m) (x := x)
  obtain ⟨q2, f2, hY, hq2, hf2⟩ := residue_decomp (m := m) (x := y)
  have hP : 0 < 7 ^ m := Nat.pow_pos (by norm_num)
  have hN : 0 < 7 ^ (m + 1) := Nat.pow_pos (by norm_num)
  have hNe : (7 : ℕ) ^ (m + 1) = 7 * 7 ^ m := pow_succ' 7 m
  have hE : eMod7 m x y
      = (x % 7 ^ (m + 1) + 7 ^ (m + 1) - y % 7 ^ (m + 1)) % 7 ^ (m + 1) := by
    unfold eMod7
    rw [if_neg hne1, if_neg hne2]
  have hEt : etd7 m x y = (q1 : ZMod 7) - q2 := by
    unfold etd7
    rw [if_neg hne1, if_neg hne2]
    show qdig7 m x - qdig7 m y = _
    unfold qdig7
    rw [hX, hY, mul_pow_add_div hf1, mul_pow_add_div hf2]
  rw [hE, hEt, qdig7_eMod_of]
  by_cases hb : f1 < f2
  · -- borrow: `X + N − Y = (q1 + 6 − q2)·P + (f1 + P − f2)`
    have hexp : (q1 + 6 - q2) * 7 ^ m = q1 * 7 ^ m + 6 * 7 ^ m - q2 * 7 ^ m := by
      rw [Nat.sub_mul, Nat.add_mul]
    have hB : q2 * 7 ^ m ≤ 6 * 7 ^ m :=
      Nat.mul_le_mul (by omega : q2 ≤ 6) (le_refl (7 ^ m))
    have hcalc : x % 7 ^ (m + 1) + 7 ^ (m + 1) - y % 7 ^ (m + 1)
        = (q1 + 6 - q2) * 7 ^ m + (f1 + 7 ^ m - f2) := by
      rw [hX, hY, hNe, hexp]
      omega
    rw [hcalc, mul_pow_add_div (by omega : f1 + 7 ^ m - f2 < 7 ^ m)]
    have hq : ((q1 + 6 - q2 : ℕ) : ZMod 7) = (q1 : ZMod 7) - q2 - 1 := by
      rw [natCast_sub_add (by omega : q2 ≤ q1 + 6)]
      have h6 : ((6 : ℕ) : ZMod 7) = -1 := by decide
      rw [h6]
      ring
    rw [hq]
    have he : (q1 : ZMod 7) - q2 - 1 - ((q1 : ZMod 7) - q2) = -1 := by ring
    rw [he]
    decide
  · have hexp : (q1 + 7 - q2) * 7 ^ m = q1 * 7 ^ m + 7 * 7 ^ m - q2 * 7 ^ m := by
      rw [Nat.sub_mul, Nat.add_mul]
    have hB : q2 * 7 ^ m ≤ 6 * 7 ^ m :=
      Nat.mul_le_mul (by omega : q2 ≤ 6) (le_refl (7 ^ m))
    have hcalc : x % 7 ^ (m + 1) + 7 ^ (m + 1) - y % 7 ^ (m + 1)
        = (q1 + 7 - q2) * 7 ^ m + (f1 - f2) := by
      rw [hX, hY, hNe, hexp]
      omega
    rw [hcalc, mul_pow_add_div (by omega : f1 - f2 < 7 ^ m)]
    have hq : ((q1 + 7 - q2 : ℕ) : ZMod 7) = (q1 : ZMod 7) - q2 := by
      rw [natCast_sub_add (by omega : q2 ≤ q1 + 7)]
      have h7 : ((7 : ℕ) : ZMod 7) = 0 := by decide
      rw [h7]
      ring
    rw [hq]
    have he : (q1 : ZMod 7) - q2 - ((q1 : ZMod 7) - q2) = 0 := by ring
    rw [he]
    decide
