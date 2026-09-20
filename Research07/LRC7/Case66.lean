import Research07.LRC7.Case5mL10
import Research07.LRC7.Case5mL9b
import Research07.LRC7.Case5mTop

/-!
# §6.6 of Barajas–Serra: `|A₁| = 2` — the `(2,2,1)` configuration

`A₁ = {d1,d2}` (class `s`), `A₂ = {d3,d4}` (class `2s`), `A₄ = {d5}`
(class `4s`).  The goal is condition (15): `ℓ(A₁), ℓ(A₂) ≤ 2` after a
common unit multiplier, after which a `(2,2,1)`-shift lemma produces the
final `Λ₀` multiplier.

Case split on `e12 = e(d1,d2)`, `e34 = e(d3,d4)` (both `same`-branch
since `s ≠ 2s`, `s ≠ 4s` for `s ∈ {1,2,4}`):

* `ν(e12) ≠ ν(e34)` — independent setters.
* `ν(e12) = ν(e34)`, `r(e12) = r(e34)` — the `f = e12 − e34` trick.
* `ν(e12) = ν(e34) < m`, `r(e12) = 2r(e34)` (or symmetric) — the
  delicate `f = e12 − 2e34` trick with a two-step multiplier and carry
  analysis.
* `ν(e12) = ν(e34) = m`, `r(e12) = 2r(e34)` — case (a) of the paper:
  `Λ₀`-anchoring `q(λ_k d2) = k` plus `Lemma 7`/ε-pair machinery on
  `e24, e25`.
* `ν(e12) = ν(e34) = m`, `r(e34) = 2r(e12)` — case (b).
-/

private instance : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩

namespace LRC7Case66

open Finset

/-! ### §0 Basic residue/digit helpers -/

/-- `eMod7` is already a residue `< 7^{m+1}`. -/
theorem eMod7_lt (m x y : ℕ) : eMod7 m x y < 7 ^ (m + 1) := by
  unfold eMod7
  split_ifs <;> exact Nat.mod_lt _ (Nat.pow_pos (by norm_num))

/-- `qdig7` sees only the mod-`7^{m+1}` residue of a product. -/
theorem qdig7_mul_resid {m a e : ℕ} :
    qdig7 m (a * (e % 7 ^ (m + 1))) = qdig7 m (a * e) := by
  apply qdig7_congr
  rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]

/-- `qdig7` of a mod-`N` value. -/
theorem qdig7_of_resid {m e : ℕ} :
    qdig7 m (e % 7 ^ (m + 1)) = qdig7 m e :=
  qdig7_congr (Nat.mod_mod _ _)

/-- Casting a wrapped residue into `ZMod M` when `M ∣ N`. -/
theorem natCast_zmod_of_dvd {M N : ℕ} (hd : M ∣ N) (a : ℕ) :
    ((a % N : ℕ) : ZMod M) = (a : ZMod M) := by
  rw [ZMod.natCast_eq_natCast_iff' _ _ _]
  exact Nat.mod_mod_of_dvd a hd

/-- `ZMod`-cast of `eMod7`: the wrapped residue casts to the branch
expression (local copy; `private` in `Case5mBase`/`Case5mL9`/`L10`). -/
theorem eMod7_zmod_cast' (m x y : ℕ) :
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

/-- `e(cx, cy) ≡ c·e(x,y) (mod 7^{m+1})` whenever `runit7 c ≠ 0` (the
residue-ratio branches are preserved since multiplication by a unit
scales both `runit7`s uniformly). -/
theorem eMod7_smul {m c x y : ℕ} (hc : runit7 c ≠ 0) :
    eMod7 m (c * x) (c * y) = (c * eMod7 m x y) % 7 ^ (m + 1) := by
  have hL : ((eMod7 m (c * x) (c * y) : ℕ) : ZMod (7 ^ (m + 1)))
      = (c * eMod7 m x y : ZMod (7 ^ (m + 1))) := by
    rw [eMod7_zmod_cast', eMod7_zmod_cast']
    simp only [runit7_mul]
    have sc1 : (runit7 c * runit7 y = 2 * (runit7 c * runit7 x)) ↔
        (runit7 y = 2 * runit7 x) := by
      constructor
      · intro h
        apply mul_left_cancel₀ hc
        rwa [show 2 * (runit7 c * runit7 x) = runit7 c * (2 * runit7 x)
          from by ring] at h
      · intro h; rw [h]; ring
    have sc2 : (runit7 c * runit7 x = 2 * (runit7 c * runit7 y)) ↔
        (runit7 x = 2 * runit7 y) := by
      constructor
      · intro h
        apply mul_left_cancel₀ hc
        rwa [show 2 * (runit7 c * runit7 y) = runit7 c * (2 * runit7 y)
          from by ring] at h
      · intro h; rw [h]; ring
    by_cases h1 : runit7 y = 2 * runit7 x
    · rw [if_pos h1, if_pos (sc1.mpr h1)]
      push_cast; ring
    · rw [if_neg h1, if_neg (fun hcon => h1 (sc1.mp hcon))]
      by_cases h2 : runit7 x = 2 * runit7 y
      · rw [if_pos h2, if_pos (sc2.mpr h2)]
        push_cast; ring
      · rw [if_neg h2, if_neg (fun hcon => h2 (sc2.mp hcon))]
        push_cast; ring
  have hlt : eMod7 m (c * x) (c * y) < 7 ^ (m + 1) := eMod7_lt _ _ _
  rw [← Nat.cast_mul] at hL
  rw [ZMod.natCast_eq_natCast_iff] at hL
  have hL' : eMod7 m (c * x) (c * y) % 7 ^ (m + 1)
      = (c * eMod7 m x y) % 7 ^ (m + 1) := hL
  rwa [Nat.mod_eq_of_lt hlt] at hL'

/-- `eMod7` respects `mod`-congruence of its arguments (with matching
`runit7`): only the residues `x % N`, `y % N` and the unit digits
enter. -/
theorem eMod7_congr' {m x y x' y' : ℕ}
    (hx : x % 7 ^ (m + 1) = x' % 7 ^ (m + 1))
    (hy : y % 7 ^ (m + 1) = y' % 7 ^ (m + 1))
    (hrx : runit7 x = runit7 x') (hry : runit7 y = runit7 y') :
    eMod7 m x y = eMod7 m x' y' := by
  unfold eMod7
  rw [hx, hy, hrx, hry]

/-- Equal `runit7` forces the `same` branch. -/
theorem rel_same_of_eq {u v : ℕ} (h : runit7 u = runit7 v) (hv : v ≠ 0) :
    residueRelOf u v = residueRel.same := by
  rw [residueRelOf_eq_same]
  have hv' : runit7 v ≠ 0 := runit7_ne_zero (Nat.pos_of_ne_zero hv)
  rw [h]
  constructor <;> intro hcon <;> exact hv' (by linear_combination -hcon)

/-- Symmetry of `eMod7`/`etd7` on `twoX` pairs: doubling goes to the
smaller-residue element either way. -/
theorem eMod7_comm_of_two {m x y : ℕ} (h : runit7 y = 2 * runit7 x)
    (hx0 : x ≠ 0) : eMod7 m x y = eMod7 m y x := by
  have hx : runit7 x ≠ 0 := runit7_ne_zero (Nat.pos_of_ne_zero hx0)
  have h2 : runit7 x ≠ 2 * runit7 y := by
    rw [h]
    intro hcon
    have h3 : (3 : ZMod 7) * runit7 x = 0 := by
      linear_combination -hcon
    rcases mul_eq_zero.mp h3 with h3' | h3'
    · exact absurd h3' (by decide)
    · exact hx h3'
  unfold eMod7
  rw [if_pos h, if_neg h2, if_pos h]

/-- `etd7` is symmetric on `twoX` pairs. -/
theorem etd7_comm_of_two {m x y : ℕ} (h : runit7 y = 2 * runit7 x)
    (hx0 : x ≠ 0) : etd7 m x y = etd7 m y x := by
  have hx : runit7 x ≠ 0 := runit7_ne_zero (Nat.pos_of_ne_zero hx0)
  have h2 : runit7 x ≠ 2 * runit7 y := by
    rw [h]
    intro hcon
    have h3 : (3 : ZMod 7) * runit7 x = 0 := by
      linear_combination -hcon
    rcases mul_eq_zero.mp h3 with h3' | h3'
    · exact absurd h3' (by decide)
    · exact hx h3'
  unfold etd7
  rw [if_pos h, if_neg h2, if_pos h]

/-- `q(e) = r(e)` when `ν(e) = m` (wrap of `qdig7_eq_runit7_of_top`). -/
theorem qdig7_eq_runit7_of_ne {m e : ℕ}
    (hν : padicValNat 7 e = m) : qdig7 m e = runit7 e :=
  qdig7_eq_runit7_of_top hν

/-- Block form at level `ν(e)+1`: `e % 7^{ν+1} = r(e)·7^ν`
(`Case5mL10.nat_mod_pow_succ_of_padic`, made non-private). -/
theorem mod_pow_succ_of_padic {e h : ℕ} (he : e ≠ 0)
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
level exactly `h` and unit digit `s`
(`Case5mL10.level_of_mod_block`, made non-private). -/
theorem level_of_mod_block {w h s : ℕ}
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
    show ((7 : ℕ) : ZMod 7) = 0 from ZMod.natCast_self 7,
    zero_mul, add_zero]

/-- Sum of two level-`h` naturals reads `(r(u)+r(v))·7^h` mod `7^{h+1}`. -/
theorem add_mod_block {u v h : ℕ} (hu : u ≠ 0) (hv : v ≠ 0)
    (huν : padicValNat 7 u = h) (hvν : padicValNat 7 v = h) :
    (u + v) % 7 ^ (h + 1) = (runit7 u + runit7 v).val * 7 ^ h := by
  have hvv : (runit7 u + runit7 v).val
      = ((runit7 u).val + (runit7 v).val) % 7 := ZMod.val_add _ _
  rw [Nat.add_mod, mod_pow_succ_of_padic hu huν,
    mod_pow_succ_of_padic hv hvν, ← Nat.add_mul, pow_succ',
    Nat.mul_mod_mul_right, hvv]

/-- Difference of two level-`h` naturals reads `(r(u)−r(v))·7^h` mod
`7^{h+1}` (wrapped subtraction `u − v` inside the modulus). -/
theorem sub_mod_block {u v h : ℕ} (hu : u ≠ 0) (hv : v ≠ 0)
    (huν : padicValNat 7 u = h) (hvν : padicValNat 7 v = h) :
    (u % 7 ^ (h + 1) + 7 ^ (h + 1) - v % 7 ^ (h + 1)) % 7 ^ (h + 1)
      = (runit7 u - runit7 v).val * 7 ^ h := by
  have hub := mod_pow_succ_of_padic hu huν
  have hvb := mod_pow_succ_of_padic hv hvν
  have hru7 : (runit7 u).val < 7 := ZMod.val_lt _
  have hrv7 : (runit7 v).val < 7 := ZMod.val_lt _
  have hvv : (runit7 u - runit7 v).val
      = ((runit7 u).val + 7 - (runit7 v).val) % 7 := by
    have hcast : (runit7 u - runit7 v : ZMod 7)
        = (((runit7 u).val + 7 - (runit7 v).val : ℕ) : ZMod 7) := by
      rw [Nat.cast_sub
          (by omega : (runit7 v).val ≤ (runit7 u).val + 7)]
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
theorem wrap_sub_mod_gen {a b c P : ℕ} (hP : 0 < P) (hc : P ∣ c)
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

/-- The negated residue `N − e` (for `0 < e < N`, `ν(e) ≤ m`) has the
same level as `e` and unit `−r(e)`.  This powers the "renaming" step
(`d1 ↔ d2` swaps) that normalizes `r(e) ∈ {1,2,4}`. -/
theorem neg_resid {m e : ℕ} (he : e ≠ 0) (hlt : e < 7 ^ (m + 1))
    (hν : padicValNat 7 e ≤ m) :
    padicValNat 7 ((7 ^ (m + 1) - e) % 7 ^ (m + 1)) = padicValNat 7 e ∧
    runit7 ((7 ^ (m + 1) - e) % 7 ^ (m + 1)) = - runit7 e := by
  have hN0 : (0 : ℕ) < 7 ^ (m + 1) := Nat.pow_pos (by norm_num)
  set j := padicValNat 7 e with hj
  have hde : Nat.divMaxPow e 7 * 7 ^ j = e := by
    rw [hj]
    exact Nat.divMaxPow_mul_pow_padicValNat 7 e
  set u := Nat.divMaxPow e 7 with hu
  have hu7 : ¬ 7 ∣ u := by
    rw [hu]
    exact Nat.not_dvd_divMaxPow (by norm_num) he
  have hN' : 7 ^ (m + 1) = 7 ^ (m + 1 - j) * 7 ^ j := by
    rw [← pow_add]
    congr 1
    omega
  have hult : u < 7 ^ (m + 1 - j) := by
    have h1 : u * 7 ^ j < 7 ^ (m + 1 - j) * 7 ^ j := by
      rw [hde, ← hN']
      exact hlt
    exact Nat.lt_of_mul_lt_mul_right h1
  have hvpos : 0 < 7 ^ (m + 1 - j) - u := Nat.sub_pos_of_lt hult
  have hv7 : ¬ 7 ∣ 7 ^ (m + 1 - j) - u := by
    intro hd
    have hsub : 7 ^ (m + 1 - j) - (7 ^ (m + 1 - j) - u)
        = u := Nat.sub_sub_self hult.le
    have hd7 : 7 ∣ 7 ^ (m + 1 - j) :=
      dvd_pow_self 7 (by omega : m + 1 - j ≠ 0)
    have h7u : 7 ∣ u := hsub ▸ Nat.dvd_sub hd7 hd
    exact hu7 h7u
  have hNsub : 7 ^ (m + 1) - e = (7 ^ (m + 1 - j) - u) * 7 ^ j := by
    rw [hN', ← hde, ← Nat.sub_mul]
  have hlt' : 7 ^ (m + 1) - e < 7 ^ (m + 1) :=
    Nat.sub_lt hN0 (Nat.pos_of_ne_zero he)
  rw [Nat.mod_eq_of_lt hlt', hNsub]
  have hνv : padicValNat 7 ((7 ^ (m + 1 - j) - u) * 7 ^ j) = j := by
    rw [padicValNat.mul hvpos.ne' (Nat.pow_pos (by norm_num)).ne',
      padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd hv7,
      zero_add]
  refine ⟨hνv, ?_⟩
  have hre : runit7 e = (u : ZMod 7) := by
    unfold runit7
    rw [← hj]
    conv_lhs => arg 1; arg 1; rw [← hde]
    rw [Nat.mul_div_cancel _ (Nat.pow_pos (by norm_num))]
  rw [hre]
  unfold runit7
  rw [hνv, Nat.mul_div_cancel _ (Nat.pow_pos (by norm_num))]
  have hsum : u + (7 ^ (m + 1 - j) - u) = 7 ^ (m + 1 - j) :=
    Nat.add_sub_cancel' hult.le
  have hcast :
      ((u + (7 ^ (m + 1 - j) - u) : ℕ) : ZMod 7) = 0 := by
    rw [hsum]
    have h7 : ((7 : ℕ) : ZMod 7) = 0 := ZMod.natCast_self 7
    rw [show (7 : ℕ) ^ (m + 1 - j) = 7 * 7 ^ (m - j) by
      rw [← pow_succ']
      congr 1
      omega, Nat.cast_mul, h7, zero_mul]
  have hneg : (u : ZMod 7) + ((7 ^ (m + 1 - j) - u : ℕ) : ZMod 7) = 0 := by
    have := hcast
    rwa [Nat.cast_add] at this
  linear_combination hneg

/-- `eMod7` of a `same`-pair is negated under swapping. -/
theorem eMod7_same_swap {m x y : ℕ}
    (hxy : residueRelOf x y = residueRel.same)
    (hyx : residueRelOf y x = residueRel.same) :
    eMod7 m y x = (7 ^ (m + 1) - eMod7 m x y) % 7 ^ (m + 1) := by
  obtain ⟨h1, h2⟩ := residueRelOf_eq_same.mp hxy
  obtain ⟨h1', h2'⟩ := residueRelOf_eq_same.mp hyx
  have hN0 : (0 : ℕ) < 7 ^ (m + 1) := Nat.pow_pos (by norm_num)
  set N := 7 ^ (m + 1) with hN
  have hEx : eMod7 m x y = (x % N + N - y % N) % N := by
    unfold eMod7
    rw [if_neg h1, if_neg h2]
  have hEy : eMod7 m y x = (y % N + N - x % N) % N := by
    unfold eMod7
    rw [if_neg h1', if_neg h2']
  have hlt : eMod7 m x y < N := eMod7_lt m x y
  have hlt' : eMod7 m y x < N := eMod7_lt m y x
  have hcast : ((eMod7 m y x : ℕ) : ZMod N)
      = (((N - eMod7 m x y) % N : ℕ) : ZMod N) := by
    have hc : ∀ c : ℕ, ((c % N : ℕ) : ZMod N) = (c : ZMod N) := fun c =>
      (ZMod.natCast_eq_natCast_iff' _ _ _).mpr (Nat.mod_modEq _ _)
    have hab : x % N < N := Nat.mod_lt _ hN0
    have hbb : y % N < N := Nat.mod_lt _ hN0
    rw [hEy, hc, hc, Nat.cast_sub (le_of_lt hlt), ZMod.natCast_self,
      zero_sub, hEx, hc,
      Nat.cast_sub (by omega : y % N ≤ x % N + N),
      Nat.cast_sub (by omega : x % N ≤ y % N + N)]
    push_cast
    rw [ZMod.natCast_self]
    ring
  rw [ZMod.natCast_eq_natCast_iff'] at hcast
  rwa [Nat.mod_eq_of_lt hlt',
    Nat.mod_eq_of_lt (Nat.mod_lt _ hN0)] at hcast

/-- `qdig7` of `u + c·w` splits into digits plus the low-block carry. -/
theorem qdig7_add_smul {m u w c : ℕ} :
    qdig7 m (u + c * w)
      = qdig7 m u + (c : ZMod 7) * qdig7 m w
        + (((u % 7 ^ m + c * (w % 7 ^ m)) / 7 ^ m : ℕ) : ZMod 7) := by
  rw [qdig7_eq_cast_div, qdig7_eq_cast_div, qdig7_eq_cast_div]
  have hP : (0 : ℕ) < 7 ^ m := Nat.pow_pos (by norm_num)
  have hdiv : (u + c * w) / 7 ^ m
      = u / 7 ^ m + c * (w / 7 ^ m)
        + (u % 7 ^ m + c * (w % 7 ^ m)) / 7 ^ m := by
    have hde : u + c * w
        = u % 7 ^ m + c * (w % 7 ^ m)
          + 7 ^ m * (u / 7 ^ m + c * (w / 7 ^ m)) := by
      conv_lhs => rw [← Nat.div_add_mod u (7 ^ m)]
      conv_lhs => arg 2; arg 2; rw [← Nat.div_add_mod w (7 ^ m)]
      ring
    rw [hde, Nat.add_mul_div_left _ _ hP]
    ring
  rw [hdiv]
  push_cast
  ring

/-- `qdig7` of `u + w` splits into digits plus the low-block carry. -/
theorem qdig7_add {m u w : ℕ} :
    qdig7 m (u + w)
      = qdig7 m u + qdig7 m w
        + (((u % 7 ^ m + w % 7 ^ m) / 7 ^ m : ℕ) : ZMod 7) := by
  have := qdig7_add_smul (m := m) (u := u) (w := w) (c := 1)
  simpa using this

/-- The low block of `(1 + k·7^{m−j})·x` below `7^m` is `x`'s, for
`j = ν(x) ≤ m`.  The shifted part `k·7^{m−j}·x` is divisible by `7^m`. -/
theorem multLow_low_part {m j k x : ℕ} (hx : padicValNat 7 x = j)
    (hx0 : x ≠ 0) (hjm : j ≤ m) :
    ((1 + k * 7 ^ (m - j)) * x) % 7 ^ m = x % 7 ^ m := by
  have hdvd : 7 ^ m ∣ k * 7 ^ (m - j) * x := by
    have hxd : 7 ^ j ∣ x :=
      (Nat.pow_dvd_iff_le_padicValNat (by norm_num) hx0).mpr (by omega)
    obtain ⟨y, rfl⟩ := hxd
    have hsplit : 7 ^ m = 7 ^ (m - j) * 7 ^ j := by
      rw [← pow_add]
      congr 1
      omega
    rw [hsplit]
    exact ⟨k * y, by ring⟩
  obtain ⟨z, hz⟩ := hdvd
  rw [add_mul, one_mul, hz]
  exact Nat.add_mul_mod_self_left x (7 ^ m) z

/-- Under `Λ_h` with `h < m`, the mod-`7^m` part of a level-`h` element
is fixed. -/
theorem multLow_shift_qdig {m h k x : ℕ} (hhm : h < m)
    (hx : padicValNat 7 x = h) (hx0 : x ≠ 0) :
    ((1 + k * 7 ^ (m - h)) * x) % 7 ^ m = x % 7 ^ m :=
  multLow_low_part hx hx0 (le_of_lt hhm)

/-- `Λ_j` preserves a residue verbatim when `j < ν(x)`. -/
theorem residN_multLow7' {m j k x : ℕ} (hjm : j < m)
    (hx : j < padicValNat 7 x) :
    (1 + k * 7 ^ (m - j)) * x % 7 ^ (m + 1) = x % 7 ^ (m + 1) :=
  residN_multLow7 hjm hx

/-- A `Λ_j`-element applied below a level-`m` residue leaves it fixed:
`(1+k·7^{m−j})·(t·7^m) ≡ t·7^m` since `2m−j ≥ m+1` for `j ≤ m−1`. -/
theorem lambda_low_top_resid {m j k t : ℕ} (hjm : j < m) (ht : t < 7) :
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

/-- For `m ≥ 2`, `Λ₁` preserves a level-`m` residue `t·7^m`:
`j = 1 ≤ m − 1` so `m−1+m ≥ m+1`. -/
theorem lambda1_top_resid {m k t : ℕ} (hm : 2 ≤ m) (ht : t < 7) :
    (1 + k * 7 ^ (m - 1)) * (t * 7 ^ m) % 7 ^ (m + 1) = t * 7 ^ m :=
  lambda_low_top_resid (by omega : 1 < m) ht

/-- The `Λ₀`-wrapped top residue is verbatim:
`(1+k·7^m)·(t·7^m) ≡ t·7^m`. -/
theorem lambda0_top_resid {m k t : ℕ} (hm : 1 ≤ m) (ht : t < 7) :
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

/-- The `Λ₀` shift on a wrapped residue `t·7^m` (`t < 7`): `q`
unchanged. -/
theorem qdig7_lambda0_resid {m k t : ℕ} (hm : 1 ≤ m) (ht : t < 7) :
    qdig7 m ((1 + k * 7 ^ m) * (t * 7 ^ m) % 7 ^ (m + 1))
      = qdig7 m (t * 7 ^ m) := by
  apply qdig7_congr
  rw [lambda0_top_resid hm ht]

/-! ### §2 Below-top machinery: the `f = e12 − c·e34` construction -/

/-- The wrapped difference `f = (u + N − (c·v)%N) % N` reads
`(r(u) − c·r(v))·7^h` mod `7^{h+1}` for level-`h` residues `u,v`
(`h < m`, `c < 7`). -/
private theorem sub_smul_mod_block {m u v c h f : ℕ} (hhm : h < m)
    (hu : u ≠ 0) (hv : v ≠ 0)
    (huν : padicValNat 7 u = h) (hvν : padicValNat 7 v = h)
    (hult : u < 7 ^ (m + 1)) (hvlt : v < 7 ^ (m + 1)) (hc : c < 7)
    (hf : f = (u + 7 ^ (m + 1) - (c * v) % 7 ^ (m + 1)) % 7 ^ (m + 1)) :
    f % 7 ^ (h + 1) = (runit7 u - (c : ZMod 7) * runit7 v).val * 7 ^ h := by
  have hP : (0 : ℕ) < 7 ^ (h + 1) := Nat.pow_pos (by norm_num)
  have hN : (0 : ℕ) < 7 ^ (m + 1) := Nat.pow_pos (by norm_num)
  have hPN : 7 ^ (h + 1) ∣ 7 ^ (m + 1) := Nat.pow_dvd_pow 7 (by omega)
  -- `(f : ZMod (7^{h+1})) = u − c·v`
  have hfZ : (f : ZMod (7 ^ (h + 1)))
      = (u : ZMod _) - (c : ZMod _) * (v : ZMod _) := by
    rw [hf]
    have hcast : ∀ a : ℕ, ((a % 7 ^ (m + 1) : ℕ) : ZMod (7 ^ (h + 1)))
        = (a : ZMod _) := fun a => natCast_zmod_of_dvd hPN a
    have hN0 : ((7 ^ (m + 1) : ℕ) : ZMod (7 ^ (h + 1))) = 0 := by
      rw [← natCast_zmod_of_dvd hPN (7 ^ (m + 1)), Nat.mod_self,
        Nat.cast_zero]
    rw [hcast]
    rw [Nat.cast_sub (by
      have hlt : (c * v) % 7 ^ (m + 1) < 7 ^ (m + 1) := Nat.mod_lt _ hN
      omega : (c * v) % 7 ^ (m + 1) ≤ u + 7 ^ (m + 1))]
    rw [Nat.cast_add, hN0, hcast, Nat.cast_mul]
    ring
  -- `f % 7^{h+1}` as a wrapped subtraction of residues
  have hfP : f % 7 ^ (h + 1)
      = (u % 7 ^ (h + 1) + 7 ^ (h + 1) - (c * v) % 7 ^ (h + 1))
        % 7 ^ (h + 1) := by
    apply (ZMod.natCast_eq_natCast_iff' _ _ _).mp
    rw [hfZ]
    rw [Nat.cast_sub (by
      have hlt : (c * v) % 7 ^ (h + 1) < 7 ^ (h + 1) := Nat.mod_lt _ hP
      omega : (c * v) % 7 ^ (h + 1)
        ≤ u % 7 ^ (h + 1) + 7 ^ (h + 1))]
    rw [Nat.cast_add, ZMod.natCast_mod, ZMod.natCast_self,
      ZMod.natCast_mod, Nat.cast_mul]
    ring
  -- expand the residue blocks
  have hub := mod_pow_succ_of_padic hu huν
  have hvb := mod_pow_succ_of_padic hv hvν
  have hcvP : (c * v) % 7 ^ (h + 1) = (c * (runit7 v).val % 7) * 7 ^ h := by
    have h1 : (c * v) % 7 ^ (h + 1) = (c * (v % 7 ^ (h + 1))) % 7 ^ (h + 1) :=
      Nat.ModEq.symm (Nat.ModEq.mul_left c (Nat.mod_modEq _ _))
    rw [h1, hvb, ← Nat.mul_assoc, pow_succ', Nat.mul_mod_mul_right]
  rw [hfP, hub, hcvP]
  -- `(r12·7^h + 7^{h+1} − k·7^h) % 7^{h+1}` with `k = (c·r34) % 7 < 7`
  set k := c * (runit7 v).val % 7 with hk
  have hk7 : k < 7 := Nat.mod_lt _ (by norm_num)
  have hru7 : (runit7 u).val < 7 := ZMod.val_lt _
  have hcomb : (runit7 u).val * 7 ^ h + 7 ^ (h + 1) - k * 7 ^ h
      = ((runit7 u).val + 7 - k) * 7 ^ h := by
    rw [pow_succ', Nat.sub_mul, Nat.add_mul]
  have hval : ((runit7 u).val + 7 - k) % 7
      = (runit7 u - (c : ZMod 7) * runit7 v).val := by
    have hcast : ((runit7 u - (c : ZMod 7) * runit7 v : ZMod 7))
        = ((((runit7 u).val + 7 - k : ℕ)) : ZMod 7) := by
      rw [Nat.cast_sub (by omega : k ≤ (runit7 u).val + 7)]
      push_cast
      rw [show (7 : ZMod 7) = 0 from by decide, add_zero,
        ZMod.natCast_zmod_val]
      -- `(c·r34).val = k`
      have hkv : ((c : ZMod 7) * runit7 v).val = k := by
        rw [hk, ZMod.val_mul, ZMod.val_natCast]
        simp [Nat.mod_eq_of_lt hc]
      rw [← hkv, ZMod.natCast_zmod_val]
    rw [hcast, ZMod.val_natCast]
  rw [hcomb, pow_succ', Nat.mul_mod_mul_right, hval]

/-- Consequently `7^{h+1} ∣ f` when `r(u) = c·r(v)`. -/
private theorem sub_smul_dvd_pow {m u v c h f : ℕ} (hhm : h < m)
    (hu : u ≠ 0) (hv : v ≠ 0)
    (huν : padicValNat 7 u = h) (hvν : padicValNat 7 v = h)
    (hult : u < 7 ^ (m + 1)) (hvlt : v < 7 ^ (m + 1)) (hc : c < 7)
    (hf : f = (u + 7 ^ (m + 1) - (c * v) % 7 ^ (m + 1)) % 7 ^ (m + 1))
    (hr : runit7 u = (c : ZMod 7) * runit7 v) :
    7 ^ (h + 1) ∣ f := by
  rw [Nat.dvd_iff_mod_eq_zero]
  rw [sub_smul_mod_block hhm hu hv huν hvν hult hvlt hc hf]
  rw [hr, sub_self, ZMod.val_zero, zero_mul]

/-- If `f = (e12 + N − (c·e34)%N) % N` then `e12 ≡ f + c·e34`, so
`q(λe12) = q(λf) + c·q(λe34) + C` with `C` the low-block carry. -/
private theorem qdig7_e_decomp {m c e12 e34 f : ℕ} (lam : ℕ)
    (hf : f = (e12 + 7 ^ (m + 1) - (c * e34) % 7 ^ (m + 1)) % 7 ^ (m + 1)) :
    qdig7 m (lam * e12)
      = qdig7 m (lam * f) + (c : ZMod 7) * qdig7 m (lam * e34)
        + ((((lam * f) % 7 ^ m + c * ((lam * e34) % 7 ^ m)) / 7 ^ m : ℕ)
            : ZMod 7) := by
  have hN : (0 : ℕ) < 7 ^ (m + 1) := Nat.pow_pos (by norm_num)
  have hcon : (lam * e12) % 7 ^ (m + 1)
      = ((lam * f) % 7 ^ (m + 1) + c * ((lam * e34) % 7 ^ (m + 1)))
        % 7 ^ (m + 1) := by
    have hfZ : (f : ZMod (7 ^ (m + 1)))
        = (e12 : ZMod (7 ^ (m + 1)))
          - (c : ZMod (7 ^ (m + 1))) * (e34 : ZMod (7 ^ (m + 1))) := by
      rw [hf]
      have hcast : ∀ a : ℕ, ((a % 7 ^ (m + 1) : ℕ) : ZMod (7 ^ (m + 1)))
          = (a : ZMod _) := fun a =>
        (ZMod.natCast_eq_natCast_iff _ _ _).mpr (Nat.mod_modEq _ _)
      rw [hcast]
      rw [Nat.cast_sub (by
        have hlt : (c * e34) % 7 ^ (m + 1) < 7 ^ (m + 1) := Nat.mod_lt _ hN
        omega : (c * e34) % 7 ^ (m + 1) ≤ e12 + 7 ^ (m + 1))]
      push_cast
      have h7 : (7 : ZMod (7 ^ (m + 1))) = ((7 : ℕ) : ZMod (7 ^ (m + 1))) := by
        norm_num
      rw [hcast, h7, ← Nat.cast_pow, ZMod.natCast_self, add_zero,
        Nat.cast_mul]
    have hme : (lam * f + c * (lam * e34)) ≡ lam * e12 [MOD 7 ^ (m + 1)] := by
      have hz : ((lam * f + c * (lam * e34) : ℕ) : ZMod (7 ^ (m + 1)))
          = ((lam * e12 : ℕ) : ZMod (7 ^ (m + 1))) := by
        push_cast
        rw [hfZ]
        ring
      exact (ZMod.natCast_eq_natCast_iff _ _ _).mp hz
    have hme2 : (lam * f) % 7 ^ (m + 1) + c * ((lam * e34) % 7 ^ (m + 1))
        ≡ lam * f + c * (lam * e34) [MOD 7 ^ (m + 1)] :=
      Nat.ModEq.add (Nat.mod_modEq _ _)
        (Nat.ModEq.mul_left c (Nat.mod_modEq _ _))
    exact (hme2.trans hme).symm
  rw [qdig7_congr hcon, qdig7_add_smul]
  simp only [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 7 (Nat.le_succ m)),
    qdig7_of_resid]

/-- Set `q(λx) = 6` for `ν(x) = j ≤ m`, `x ≠ 0`: `Λ_j` when `j < m`,
top-scalar when `j = m`. -/
private theorem exists_unit_set_qdig_six {m x : ℕ} (hm : 0 < m)
    (hx0 : x ≠ 0) {j : ℕ} (hν : padicValNat 7 x = j) (hjm : j ≤ m) :
    ∃ lam : ℕ, ¬ 7 ∣ lam ∧ qdig7 m (lam * x) = 6 := by
  rcases eq_or_ne j m with rfl | hjm'
  · obtain ⟨c, hcpos, hc7, _, hq⟩ :=
      exists_top_scalar_set hν hx0 (by decide : (6 : ZMod 7) ≠ 0)
    refine ⟨c, ?_, hq⟩
    exact fun hdvd => absurd (Nat.eq_zero_of_dvd_of_lt hdvd hc7)
      (ne_of_gt hcpos)
  · have hjlt : j < m := lt_of_le_of_ne hjm hjm'
    have hr : runit7 x ≠ 0 := runit7_ne_zero (Nat.pos_of_ne_zero hx0)
    set t : ZMod 7 := (6 - qdig7 m x) * (runit7 x)⁻¹
    refine ⟨1 + t.val * 7 ^ (m - j), multLow_not_dvd hjlt, ?_⟩
    rw [qdig7_multLow hjlt hν, ZMod.natCast_zmod_val]
    have ht : ((6 - qdig7 m x) * (runit7 x)⁻¹) * runit7 x
        = 6 - qdig7 m x := by
      rw [mul_assoc, inv_mul_cancel₀ hr, mul_one]
    linear_combination ht

/-- `Λ_j` digit-setter to an arbitrary target `t`. -/
private theorem exists_multLow_set_qdig {m j x : ℕ} (hjm : j < m)
    (hx : padicValNat 7 x = j) (hx0 : x ≠ 0) (t : ZMod 7) :
    ∃ k < 7, qdig7 m ((1 + k * 7 ^ (m - j)) * x) = t := by
  have hr : runit7 x ≠ 0 := runit7_ne_zero (Nat.pos_of_ne_zero hx0)
  set kk : ZMod 7 := (t - qdig7 m x) * (runit7 x)⁻¹
  refine ⟨kk.val, ZMod.val_lt _, ?_⟩
  rw [qdig7_multLow hjm hx, ZMod.natCast_zmod_val]
  have ht : kk * runit7 x = t - qdig7 m x := by
    rw [mul_assoc, inv_mul_cancel₀ hr, mul_one]
  linear_combination ht

/-- The `Λ_h` second step: `lam = 1 + k₂·7^{m−h}` sets `q(lam·(λ₁e34)) = t`,
preserves `q(λ₁f)` and both mod-`7^m` low parts (for the carry). -/
private theorem case66_step2 {m h lam₁ f e34 : ℕ} (hhm : h < m)
    (hνf : h < padicValNat 7 f) (hf0 : f ≠ 0)
    (hν1 : padicValNat 7 (lam₁ * e34) = h) (he0 : lam₁ * e34 ≠ 0)
    (t : ZMod 7) :
    ∃ lam : ℕ, ¬ 7 ∣ lam ∧ qdig7 m (lam * (lam₁ * e34)) = t
      ∧ (lam * (lam₁ * f)) % 7 ^ (m + 1) = (lam₁ * f) % 7 ^ (m + 1)
      ∧ (lam * (lam₁ * e34)) % 7 ^ m = (lam₁ * e34) % 7 ^ m
      ∧ (lam * (lam₁ * f)) % 7 ^ m = (lam₁ * f) % 7 ^ m := by
  set k₂ := ((t - qdig7 m (lam₁ * e34)) * (runit7 (lam₁ * e34))⁻¹).val
  have hr1 : runit7 (lam₁ * e34) ≠ 0 := runit7_ne_zero (Nat.pos_of_ne_zero he0)
  refine ⟨1 + k₂ * 7 ^ (m - h), multLow_not_dvd hhm, ?_, ?_, ?_, ?_⟩
  · rw [qdig7_multLow hhm hν1, ZMod.natCast_zmod_val]
    have ht2 : ((t - qdig7 m (lam₁ * e34)) * (runit7 (lam₁ * e34))⁻¹)
        * runit7 (lam₁ * e34) = t - qdig7 m (lam₁ * e34) := by
      rw [mul_assoc, inv_mul_cancel₀ hr1, mul_one]
    linear_combination ht2
  · exact residN_multLow7' (k := k₂) hhm (by
      have hlam0 : lam₁ ≠ 0 := fun hh => he0 (by rw [hh, zero_mul])
      rw [padicValNat.mul hlam0 hf0]; omega)
  · exact multLow_low_part hν1 he0 (le_of_lt hhm)
  · have h := residN_multLow7' (k := k₂) hhm (by
      have hlam0 : lam₁ ≠ 0 := fun hh => he0 (by rw [hh, zero_mul])
      rw [padicValNat.mul hlam0 hf0]; omega)
    have h' := congrArg (· % 7 ^ m) h
    rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 7 (Nat.le_succ m)),
      Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 7 (Nat.le_succ m))] at h'
    exact h'

/-! ### §1 The `(2,2,1)` finish

The common closing argument: once a unit multiplier `lam₁` makes both
pair-differences `e(λ₁d₁,λ₁d₂)`, `e(λ₁d₃,λ₁d₄)` land at `q ∈ {0,6}`, the
two `q`-images have `apLen ≤ 2` and the singleton has `apLen = 1`, so
`lemma5` (three-class compression) + `exists_lambda0_of_shift` produce
the final `Λ₀` multiplier.  When `apLen X₂ > apLen X₁` the classes are
re-labelled with `s'' = 2·s'`. -/

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
  apply rel_same_of_eq
  · rw [runit7_mul, runit7_mul, hxy]
  · exact mul_ne_zero (fun h => hlam (h ▸ dvd_zero _)) hy

/-- The `(2,2,1)` finish: if `lam₁` puts both pair `q(e)`'s in `{0,6}`,
`lemma5` + `exists_lambda0_of_shift` close the goal. -/
private theorem case66_finish {m : ℕ} (hm : 0 < m)
    {A1 A2 A4 : Finset ℕ}
    (hpos : ∀ d ∈ A1 ∪ A2 ∪ A4, 0 < d)
    (hunit : ∀ d ∈ A1 ∪ A2 ∪ A4, padicValNat 7 d = 0)
    {s : ZMod 7} (hs : s ∈ ({1, 2, 4} : Finset (ZMod 7)))
    (hcls1 : ∀ d ∈ A1, runit7 d = s)
    (hcls2 : ∀ d ∈ A2, runit7 d = 2 * s)
    (hcls4 : ∀ d ∈ A4, runit7 d = 4 * s)
    {d1 d2 d3 d4 d5 : ℕ}
    (hA1eq : A1 = {d1, d2}) (hA2eq : A2 = {d3, d4}) (hA4eq : A4 = {d5})
    {lam₁ : ℕ} (hlam₁ : ¬ 7 ∣ lam₁)
    (hq12 : qdig7 m (eMod7 m (lam₁ * d1) (lam₁ * d2))
      ∈ ({0, 6} : Finset (ZMod 7)))
    (hq34 : qdig7 m (eMod7 m (lam₁ * d3) (lam₁ * d4))
      ∈ ({0, 6} : Finset (ZMod 7))) :
    ∃ lam : ℕ, ¬ 7 ∣ lam ∧ good7 m lam (A1 ∪ A2 ∪ A4) := by
  classical
  have hs0 : s ≠ 0 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl | rfl <;> decide
  -- membership of the extracted elements
  have hd1 : d1 ∈ A1 := by rw [hA1eq]; exact Finset.mem_insert_self _ _
  have hd2 : d2 ∈ A1 := by
    rw [hA1eq]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hd3 : d3 ∈ A2 := by rw [hA2eq]; exact Finset.mem_insert_self _ _
  have hd4 : d4 ∈ A2 := by
    rw [hA2eq]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hd5 : d5 ∈ A4 := by rw [hA4eq]; exact Finset.mem_singleton_self _
  have hd1u : d1 ∈ A1 ∪ A2 ∪ A4 :=
    Finset.mem_union_left _ (Finset.mem_union_left _ hd1)
  have hd2u : d2 ∈ A1 ∪ A2 ∪ A4 :=
    Finset.mem_union_left _ (Finset.mem_union_left _ hd2)
  have hd3u : d3 ∈ A1 ∪ A2 ∪ A4 :=
    Finset.mem_union_left _ (Finset.mem_union_right _ hd3)
  have hd4u : d4 ∈ A1 ∪ A2 ∪ A4 :=
    Finset.mem_union_left _ (Finset.mem_union_right _ hd4)
  have hd5u : d5 ∈ A1 ∪ A2 ∪ A4 := Finset.mem_union_right _ hd5
  have hd2pos : d2 ≠ 0 := ne_of_gt (hpos d2 hd2u)
  have hd4pos : d4 ≠ 0 := ne_of_gt (hpos d4 hd4u)
  have hd5pos : d5 ≠ 0 := ne_of_gt (hpos d5 hd5u)
  -- the `q`-images after `lam₁`
  set X1 := (A1.image (fun d => lam₁ * d)).image (qdig7 m) with hX1
  set X2 := (A2.image (fun d => lam₁ * d)).image (qdig7 m) with hX2
  set X4 := (A4.image (fun d => lam₁ * d)).image (qdig7 m) with hX4
  have hX1eq : X1 = ({qdig7 m (lam₁ * d1), qdig7 m (lam₁ * d2)}
      : Finset (ZMod 7)) := by
    rw [hX1, hA1eq]
    simp only [Finset.image_insert, Finset.image_singleton]
  have hX2eq : X2 = ({qdig7 m (lam₁ * d3), qdig7 m (lam₁ * d4)}
      : Finset (ZMod 7)) := by
    rw [hX2, hA2eq]
    simp only [Finset.image_insert, Finset.image_singleton]
  have hX4eq : X4 = ({qdig7 m (lam₁ * d5)} : Finset (ZMod 7)) := by
    rw [hX4, hA4eq]
    simp only [Finset.image_singleton]
  -- `apLen` bounds
  have hrel12 : residueRelOf (lam₁ * d1) (lam₁ * d2) = residueRel.same :=
    rel_same_of_mul hlam₁ (by rw [hcls1 d1 hd1, hcls1 d2 hd2]) hd2pos
  have hrel34 : residueRelOf (lam₁ * d3) (lam₁ * d4) = residueRel.same :=
    rel_same_of_mul hlam₁ (by rw [hcls2 d3 hd3, hcls2 d4 hd4]) hd4pos
  have hapX1 : apLen X1 ≤ 2 := by rw [hX1eq]; exact apLen_pair_of_qe hrel12 hq12
  have hapX2 : apLen X2 ≤ 2 := by rw [hX2eq]; exact apLen_pair_of_qe hrel34 hq34
  have hapX4 : apLen X4 ≤ 1 := by rw [hX4eq]; exact apLen_singleton_le1 _
  have hX1ne : X1.Nonempty := by rw [hX1eq]; exact Finset.insert_nonempty _ _
  have hapX1pos : 1 ≤ apLen X1 := apLen_pos_of_nonempty hX1ne
  have hX2ne : X2.Nonempty := by rw [hX2eq]; exact Finset.insert_nonempty _ _
  have hapX2pos : 1 ≤ apLen X2 := apLen_pos_of_nonempty hX2ne
  -- the multiplier-adjusted union `B` and its class data
  set B := (A1 ∪ A2 ∪ A4).image (fun d => lam₁ * d) with hB
  set s' : ZMod 7 := runit7 lam₁ * s with hs'
  have hlam₁0 : lam₁ ≠ 0 := fun hh => hlam₁ (hh ▸ dvd_zero _)
  have hrl1 : runit7 lam₁ ≠ 0 := runit7_ne_zero (Nat.pos_of_ne_zero hlam₁0)
  have hs'0 : s' ≠ 0 := by rw [hs']; exact mul_ne_zero hrl1 hs0
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
      · rw [hcls1 d₀ hd₁]; exact Finset.mem_insert_self _ _
      · rw [hcls2 d₀ hd₂]
        have : runit7 lam₁ * (2 * s) = 2 * s' := by rw [hs']; ring
        rw [this]
        exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    · rw [hcls4 d₀ hd₄]
      have : runit7 lam₁ * (4 * s) = 4 * s' := by rw [hs']; ring
      rw [this]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_singleton_self _))
  -- the three class filters on `B`
  have hfilt1 : (B.filter (fun d => runit7 d = s')).image (qdig7 m) = X1 := by
    have hf : B.filter (fun d => runit7 d = s')
        = A1.image (fun d => lam₁ * d) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨hBx, hrx⟩
        obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hBx
        rw [runit7_mul, hs'] at hrx
        have htd : runit7 d = s := mul_left_cancel₀ hrl1 hrx
        rcases Finset.mem_union.mp hd with h12 | h4
        · rcases Finset.mem_union.mp h12 with h1 | h2
          · exact ⟨d, h1, rfl⟩
          · rw [hcls2 d h2] at htd
            exact absurd (by linear_combination htd) hs0
        · rw [hcls4 d h4] at htd
          have hz : (3 : ZMod 7) * s = 0 := by linear_combination htd
          rcases mul_eq_zero.mp hz with h3 | h0
          · exact absurd h3 (by decide)
          · exact absurd h0 hs0
      · rintro ⟨d, h1, rfl⟩
        refine ⟨Finset.mem_image.mpr ⟨d,
          Finset.mem_union_left _ (Finset.mem_union_left _ h1), rfl⟩, ?_⟩
        rw [runit7_mul, hcls1 d h1, hs']
    rw [hf]
  have hfilt2 : (B.filter (fun d => runit7 d = 2 * s')).image (qdig7 m)
      = X2 := by
    have hf : B.filter (fun d => runit7 d = 2 * s')
        = A2.image (fun d => lam₁ * d) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨hBx, hrx⟩
        obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hBx
        rw [runit7_mul, hs'] at hrx
        have htd : runit7 d = 2 * s := by
          have hr' : runit7 lam₁ * runit7 d = runit7 lam₁ * (2 * s) := by
            rw [hrx]; ring
          exact mul_left_cancel₀ hrl1 hr'
        rcases Finset.mem_union.mp hd with h12 | h4
        · rcases Finset.mem_union.mp h12 with h1 | h2
          · rw [hcls1 d h1] at htd
            exact absurd (by linear_combination -htd) hs0
          · exact ⟨d, h2, rfl⟩
        · rw [hcls4 d h4] at htd
          have hz : (2 : ZMod 7) * s = 0 := by linear_combination htd
          rcases mul_eq_zero.mp hz with h2 | h0
          · exact absurd h2 (by decide)
          · exact absurd h0 hs0
      · rintro ⟨d, h2, rfl⟩
        refine ⟨Finset.mem_image.mpr ⟨d,
          Finset.mem_union_left _ (Finset.mem_union_right _ h2), rfl⟩, ?_⟩
        rw [runit7_mul, hcls2 d h2, hs']; ring
    rw [hf]
  have hfilt4 : (B.filter (fun d => runit7 d = 4 * s')).image (qdig7 m)
      = X4 := by
    have hf : B.filter (fun d => runit7 d = 4 * s')
        = A4.image (fun d => lam₁ * d) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨hBx, hrx⟩
        obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hBx
        rw [runit7_mul, hs'] at hrx
        have htd : runit7 d = 4 * s := by
          have hr' : runit7 lam₁ * runit7 d = runit7 lam₁ * (4 * s) := by
            rw [hrx]; ring
          exact mul_left_cancel₀ hrl1 hr'
        rcases Finset.mem_union.mp hd with h12 | h4
        · rcases Finset.mem_union.mp h12 with h1 | h2
          · rw [hcls1 d h1] at htd
            have hz : (3 : ZMod 7) * s = 0 := by linear_combination -htd
            rcases mul_eq_zero.mp hz with h3 | h0
            · exact absurd h3 (by decide)
            · exact absurd h0 hs0
          · rw [hcls2 d h2] at htd
            have hz : (2 : ZMod 7) * s = 0 := by linear_combination -htd
            rcases mul_eq_zero.mp hz with h2 | h0
            · exact absurd h2 (by decide)
            · exact absurd h0 hs0
        · exact ⟨d, h4, rfl⟩
      · rintro ⟨d, h4, rfl⟩
        refine ⟨Finset.mem_image.mpr ⟨d, Finset.mem_union_right _ h4, rfl⟩,
          ?_⟩
        rw [runit7_mul, hcls4 d h4, hs']; ring
    rw [hf]
  -- case split on the `apLen` ordering
  by_cases hord : apLen X2 ≤ apLen X1
  · -- `A₁` is the longest: `lemma5 s` on `(X1, X2, X4)`
    have hsum : apLen X1 + apLen X2 + apLen X4 ≤ 5 := by omega
    rcases lemma5 s hs ⟨hord, by omega⟩ hsum with ⟨t, ht⟩ | ⟨h3, _, _, _⟩
    · obtain ⟨lam0, hlam0mem, hgood0⟩ :=
        exists_lambda0_of_shift hm hs'0 hunitB hclsB t (by
          rw [hfilt1, hfilt2, hfilt4]
          exact ht)
      refine ⟨lam0 * lam₁,
        Nat.prime_seven.not_dvd_mul (not_dvd_of_mem_multLow7_zero hm hlam0mem)
          hlam₁, ?_⟩
      exact good7_mul hgood0
    · omega
  · -- `apLen X2 > apLen X1`: `apLen X1 = 1`, `apLen X2 = 2`; re-label with
    -- `s'' = 2·s'` so `X2` becomes the `s''`-class.
    have hX1eq1 : apLen X1 = 1 := by omega
    have hX2eq2 : apLen X2 = 2 := by omega
    have hsum : apLen X2 + apLen X4 + apLen X1 ≤ 5 := by omega
    set s'' : ZMod 7 := 2 * s' with hs''
    have hs''0 : s'' ≠ 0 := by rw [hs'']; exact mul_ne_zero (by decide) hs'0
    have hclsB' : ∀ d ∈ B,
        runit7 d ∈ ({s'', 2 * s'', 4 * s''} : Finset (ZMod 7)) := by
      intro d hd
      have h := hclsB d hd
      simp only [Finset.mem_insert, Finset.mem_singleton] at h ⊢
      rcases h with h1 | h2 | h4
      · refine Or.inr (Or.inr ?_)
        rw [h1, hs'', ← mul_assoc,
          show (4 : ZMod 7) * 2 = 1 from by decide, one_mul]
      · exact Or.inl h2
      · refine Or.inr (Or.inl ?_)
        rw [h4, hs'']
        ring
    rcases lemma5 s hs ⟨by omega, by omega⟩ hsum with ⟨t, ht⟩ | ⟨h3, _, _, _⟩
    · -- `X2+t ∪ X4+2t ∪ X1+4t`; re-cast filters at `s''`
      have h4s'' : (4 : ZMod 7) * s'' = s' := by
        rw [hs'', ← mul_assoc,
          show (4 : ZMod 7) * 2 = 1 from by decide, one_mul]
      have h2s'' : (2 : ZMod 7) * s'' = 4 * s' := by rw [hs'']; ring
      obtain ⟨lam0, hlam0mem, hgood0⟩ :=
        exists_lambda0_of_shift hm hs''0 hunitB hclsB' t (by
          rw [show (B.filter fun d => runit7 d = 2 * s'')
              = B.filter fun d => runit7 d = 4 * s' from by rw [h2s''],
            show (B.filter fun d => runit7 d = 4 * s'')
              = B.filter fun d => runit7 d = s' from by rw [h4s''],
            hfilt2, hfilt4, hfilt1]
          exact ht)
      refine ⟨lam0 * lam₁,
        Nat.prime_seven.not_dvd_mul (not_dvd_of_mem_multLow7_zero hm hlam0mem)
          hlam₁, ?_⟩
      exact good7_mul hgood0
    · omega

/-! ### §3 The `lam₁`-locating machinery and public `case66` -/

/-- `q(N − e) = 6 − q(e)` when `e`'s low block `e % 7^m` is nonzero
(i.e. `ν(e) < m`): transfers `qdig7 ∈ {0,6}` across a pair swap. -/
private theorem qdig7_neg_low {m e : ℕ}
    (hlt : e < 7 ^ (m + 1)) (hlow : e % 7 ^ m ≠ 0) :
    qdig7 m ((7 ^ (m + 1) - e) % 7 ^ (m + 1)) = 6 - qdig7 m e := by
  have hP : 0 < 7 ^ m := Nat.pow_pos (by norm_num)
  have he0 : e ≠ 0 := by
    rintro rfl
    exact hlow (by simp)
  have h7 : 7 ^ (m + 1) = 7 * 7 ^ m := pow_succ' 7 m
  have hq7 : e / 7 ^ m < 7 := by
    have hle : e / 7 ^ m * 7 ^ m ≤ e := Nat.div_mul_le_self e _
    by_contra h
    push_neg at h
    have : 7 * 7 ^ m ≤ e / 7 ^ m * 7 ^ m := Nat.mul_le_mul_right _ h
    omega
  have hr0 : 0 < e % 7 ^ m := Nat.pos_of_ne_zero hlow
  have hrlt : e % 7 ^ m < 7 ^ m := Nat.mod_lt e hP
  have hq6 : e / 7 ^ m ≤ 6 := Nat.le_of_lt_succ hq7
  have hsub : 7 ^ (m + 1) - e
      = (6 - e / 7 ^ m) * 7 ^ m + (7 ^ m - e % 7 ^ m) := by
    have hrP : e % 7 ^ m ≤ 7 ^ m := le_of_lt hrlt
    have hdec : e = e / 7 ^ m * 7 ^ m + e % 7 ^ m := by
      have h := (Nat.div_add_mod e (7 ^ m)).symm
      rwa [mul_comm (7 ^ m) (e / 7 ^ m)] at h
    have key : 7 * 7 ^ m
        = (6 - e / 7 ^ m) * 7 ^ m + (7 ^ m - e % 7 ^ m) + e := by
      have h1 : (6 - e / 7 ^ m) * 7 ^ m + e / 7 ^ m * 7 ^ m
          = 6 * 7 ^ m := by
        rw [← add_mul, Nat.sub_add_cancel hq6]
      have h2 : 7 ^ m - e % 7 ^ m + e % 7 ^ m = 7 ^ m :=
        Nat.sub_add_cancel hrP
      omega
    rw [h7]
    exact (Nat.sub_eq_iff_eq_add (by omega : e ≤ 7 * 7 ^ m)).mpr key
  have hdiv : (7 ^ (m + 1) - e) / 7 ^ m = 6 - e / 7 ^ m := by
    rw [hsub, add_comm ((6 - e / 7 ^ m) * 7 ^ m),
      mul_comm (6 - e / 7 ^ m) (7 ^ m), Nat.add_mul_div_left _ _ hP,
      Nat.div_eq_of_lt (by omega : 7 ^ m - e % 7 ^ m < 7 ^ m), zero_add]
  have hmem : 7 ^ (m + 1) - e < 7 ^ (m + 1) :=
    Nat.sub_lt (Nat.pow_pos (by norm_num)) (Nat.pos_of_ne_zero he0)
  rw [qdig7_eq_cast_div, Nat.mod_eq_of_lt hmem, hdiv, qdig7_eq_cast_div,
    Nat.cast_sub hq6]
  norm_num

/-- Nonzero residue `< N` has level `≤ m`. -/
private theorem padic_le_of_lt {m e : ℕ} (he0 : e ≠ 0)
    (hlt : e < 7 ^ (m + 1)) : padicValNat 7 e ≤ m := by
  by_contra h
  push_neg at h
  have hdvd : 7 ^ (m + 1) ∣ e :=
    (Nat.pow_dvd_iff_le_padicValNat (by norm_num) he0).mpr (by omega)
  have := Nat.le_of_dvd (Nat.pos_of_ne_zero he0) hdvd
  omega

/-- Set `q(λx) = t` for any `t ≠ 0`, `ν(x) = j ≤ m`, `x ≠ 0`:
`Λ_j` when `j < m`, top-scalar when `j = m`. -/
private theorem exists_unit_set_qdig {m x : ℕ} (hm : 0 < m) (hx0 : x ≠ 0)
    {j : ℕ} (hν : padicValNat 7 x = j) (hjm : j ≤ m)
    {t : ZMod 7} (ht : t ≠ 0) :
    ∃ lam : ℕ, ¬ 7 ∣ lam ∧ qdig7 m (lam * x) = t := by
  rcases eq_or_ne j m with rfl | hjm'
  · obtain ⟨c, hcpos, hc7, _, hq⟩ := exists_top_scalar_set hν hx0 ht
    refine ⟨c, ?_, hq⟩
    exact fun hdvd => absurd (Nat.eq_zero_of_dvd_of_lt hdvd hc7)
      (ne_of_gt hcpos)
  · obtain ⟨k, _, hk⟩ :=
      exists_multLow_set_qdig (lt_of_le_of_ne hjm hjm') hν hx0 t
    exact ⟨1 + k * 7 ^ (m - j), multLow_not_dvd (lt_of_le_of_ne hjm hjm'), hk⟩

/-- `ν(e_a) < ν(e_b)`: set `q(e_b) = 6` first (higher level), then `Λ`
on `e_a` preserving the `e_b` residue. -/
private theorem case66_two_level {m : ℕ} (hm : 0 < m)
    {ea eb ha hb : ℕ} (hea : padicValNat 7 ea = ha)
    (heb : padicValNat 7 eb = hb) (hea0 : ea ≠ 0) (heb0 : eb ≠ 0)
    (hle : ha < hb) (hbm : hb ≤ m) :
    ∃ lam₁ : ℕ, ¬ 7 ∣ lam₁ ∧ qdig7 m (lam₁ * ea) = 0 ∧
      qdig7 m (lam₁ * eb) = 6 := by
  obtain ⟨la, hla, hqa⟩ :=
    exists_unit_set_qdig hm heb0 heb hbm (t := 6) (by decide)
  have ha_lt_m : ha < m := lt_of_lt_of_le hle hbm
  have hla0 : la ≠ 0 := fun h => hla (h ▸ dvd_zero _)
  have hν1 : padicValNat 7 (la * ea) = ha := by
    rw [padicValNat_mul_seven hla hea0, hea]
  have hea1 : la * ea ≠ 0 := mul_ne_zero hla0 hea0
  obtain ⟨lb, hlb, hqb, hpre, _, _⟩ :=
    case66_step2 (m := m) (h := ha) (lam₁ := la) (f := eb) (e34 := ea)
      ha_lt_m (by rwa [heb]) heb0 hν1 hea1 0
  refine ⟨lb * la, Nat.prime_seven.not_dvd_mul hlb hla, ?_, ?_⟩
  · rw [mul_assoc]; exact hqb
  · rw [mul_assoc, qdig7_congr hpre, hqa]

/-- Equal level `h < m`, equal `r` (`c = 1`): `f = e_a − e_b` has
`ν(f) > h`; set `q(λf) = 6` then `q(λe_b) = 0` via `Λ_h` preserving
both low blocks — the carry `C ∈ {0,1}` keeps `q(λe_a) ∈ {0,6}`
(paper: `q(f) = 6`, `q(e34) = 0`, Lemma 4). -/
private theorem case66_same_r {m : ℕ} (hm : 2 ≤ m)
    {ea eb h : ℕ} (hea : padicValNat 7 ea = h) (heb : padicValNat 7 eb = h)
    (hea0 : ea ≠ 0) (heb0 : eb ≠ 0)
    (healt : ea < 7 ^ (m + 1)) (heblt : eb < 7 ^ (m + 1))
    (hhm : h < m) (hr : runit7 ea = runit7 eb) :
    ∃ lam₁ : ℕ, ¬ 7 ∣ lam₁ ∧
      qdig7 m (lam₁ * ea) ∈ ({0, 6} : Finset (ZMod 7)) ∧
      qdig7 m (lam₁ * eb) ∈ ({0, 6} : Finset (ZMod 7)) := by
  classical
  have hP : 0 < 7 ^ m := Nat.pow_pos (by norm_num)
  have hN : 0 < 7 ^ (m + 1) := Nat.pow_pos (by norm_num)
  set f := (ea + 7 ^ (m + 1) - eb) % 7 ^ (m + 1) with hf0def
  have hf' : f = (ea + 7 ^ (m + 1)
      - (1 * eb) % 7 ^ (m + 1)) % 7 ^ (m + 1) := by
    rw [hf0def, one_mul, Nat.mod_eq_of_lt heblt]
  have hdvd : 7 ^ (h + 1) ∣ f :=
    sub_smul_dvd_pow hhm hea0 heb0 hea heb healt heblt (by norm_num) hf'
      (by rw [Nat.cast_one, one_mul]; exact hr)
  by_cases hf0 : f = 0
  · -- `e_a ≡ e_b [MOD N]`: one setter fixes both.
    obtain ⟨lam, hlam, hq⟩ :=
      exists_unit_set_qdig_six (by omega : 0 < m) heb0 heb (le_of_lt hhm)
    have heab : ea ≡ eb [MOD 7 ^ (m + 1)] := by
      have hfZ : ((f : ℕ) : ZMod (7 ^ (m + 1)))
          = (ea : ZMod (7 ^ (m + 1))) - eb := by
        rw [hf0def]
        have hcast : ∀ a : ℕ, ((a % 7 ^ (m + 1) : ℕ) : ZMod (7 ^ (m + 1)))
            = (a : ZMod _) := fun a =>
          (ZMod.natCast_eq_natCast_iff _ _ _).mpr (Nat.mod_modEq _ _)
        rw [hcast, Nat.cast_sub (by omega)]
        push_cast
        rw [show (7 : ZMod (7 ^ (m + 1))) = ((7 : ℕ) : ZMod (7 ^ (m + 1))) from
          by norm_num, ← Nat.cast_pow, ZMod.natCast_self]
        ring
      rw [hf0, Nat.cast_zero] at hfZ
      exact (ZMod.natCast_eq_natCast_iff _ _ _).mp (sub_eq_zero.mp hfZ.symm)
    have hcon : (lam * ea) % 7 ^ (m + 1) = (lam * eb) % 7 ^ (m + 1) :=
      Nat.ModEq.mul_left lam heab
    refine ⟨lam, hlam, ?_, ?_⟩
    · rw [qdig7_congr hcon, hq]; decide
    · rw [hq]; decide
  · have hνf : h < padicValNat 7 f := by
      have := (Nat.pow_dvd_iff_le_padicValNat (by norm_num) hf0).mp hdvd
      omega
    have hνfm : padicValNat 7 f ≤ m :=
      padic_le_of_lt hf0 (Nat.mod_lt _ hN)
    obtain ⟨la, hla, hqa⟩ :=
      exists_unit_set_qdig_six (by omega : 0 < m) hf0 rfl hνfm
    have hla0 : la ≠ 0 := fun hh => hla (hh ▸ dvd_zero _)
    have hν1 : padicValNat 7 (la * eb) = h := by
      rw [padicValNat_mul_seven hla heb0, heb]
    have heb1 : la * eb ≠ 0 := mul_ne_zero hla0 heb0
    obtain ⟨lb, hlb, hqb, hpre, hlowe, hlowf⟩ :=
      case66_step2 hhm hνf hf0 hν1 heb1 (0 : ZMod 7)
    refine ⟨lb * la, Nat.prime_seven.not_dvd_mul hlb hla, ?_, ?_⟩
    · have hdec := qdig7_e_decomp (m := m) (c := 1) (lam := lb * la) hf'
      rw [hdec]
      have hqf : qdig7 m (lb * la * f) = 6 := by
        rw [mul_assoc, qdig7_congr hpre, hqa]
      have hqeb : qdig7 m (lb * la * eb) = 0 := by
        rw [mul_assoc]; exact hqb
      have hlow1 : (lb * la * f) % 7 ^ m = (la * f) % 7 ^ m := by
        rw [mul_assoc]; exact hlowf
      have hlow2 : (lb * la * eb) % 7 ^ m = (la * eb) % 7 ^ m := by
        rw [mul_assoc]; exact hlowe
      rw [hqf, hqeb, hlow1, hlow2]
      have hC2 : ((la * f) % 7 ^ m + 1 * ((la * eb) % 7 ^ m)) / 7 ^ m < 2 :=
        Nat.div_lt_of_lt_mul (by
          have h1 := Nat.mod_lt (la * f) hP
          have h2 := Nat.mod_lt (la * eb) hP
          omega)
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp
          (by omega : ((la * f) % 7 ^ m + 1 * ((la * eb) % 7 ^ m)) / 7 ^ m ≤ 1)
        with hC | hC <;> rw [hC] <;> decide
    · have hqeb : qdig7 m (lb * la * eb) = 0 := by
        rw [mul_assoc]; exact hqb
      rw [hqeb]; decide

/-- Equal level `h < m`, `r(e_b) = 2·r(e_a)`: paper Lemma 9(ii) applied
to the residue pair. Set `e = e(e_a, e_b) = 2e_a − e_b`; after `λ₁`
with `q(λ₁e) ∈ {0,6}` the digit `etv = 2q(λ₁e_a) − q(λ₁e_b)` lies in
`{0,5,6}` and is `Λ_h`-invariant (since `2r(e_a) − r(e_b) = 0`), so a
second `Λ_h` sets `q(λ₂λ₁e_a) ∈ {0,6}` forcing `q(λ₂λ₁e_b) ∈ {0,6}`. -/
private theorem case66_twoX {m : ℕ} (hm : 2 ≤ m)
    {ea eb h : ℕ} (hea : padicValNat 7 ea = h) (heb : padicValNat 7 eb = h)
    (hea0 : ea ≠ 0) (heb0 : eb ≠ 0)
    (healt : ea < 7 ^ (m + 1)) (heblt : eb < 7 ^ (m + 1))
    (hhm : h < m) (hr : runit7 eb = 2 * runit7 ea) :
    ∃ lam₁ : ℕ, ¬ 7 ∣ lam₁ ∧
      qdig7 m (lam₁ * ea) ∈ ({0, 6} : Finset (ZMod 7)) ∧
      qdig7 m (lam₁ * eb) ∈ ({0, 6} : Finset (ZMod 7)) := by
  classical
  have hN : 0 < 7 ^ (m + 1) := Nat.pow_pos (by norm_num)
  have hP : 0 < 7 ^ m := Nat.pow_pos (by norm_num)
  set e := eMod7 m ea eb with he
  have hev : e = (2 * (ea % 7 ^ (m + 1)) + 7 ^ (m + 1)
      - eb % 7 ^ (m + 1)) % 7 ^ (m + 1) := by
    rw [he, eMod7, if_pos hr]
  by_cases he0 : e = 0
  · -- `2·e_a ≡ e_b [MOD N]`: `q(λe_b) = 2·q(λe_a) + C''`, `C'' ∈ {0,1}`
    -- fixed by `Λ_h`'s low-block preservation; pick `t` accordingly.
    have heab : (2 * ea) ≡ eb [MOD 7 ^ (m + 1)] := by
      have hfZ : ((e : ℕ) : ZMod (7 ^ (m + 1)))
          = 2 * (ea : ZMod (7 ^ (m + 1))) - eb := by
        rw [hev]
        have hcast : ∀ a : ℕ, ((a % 7 ^ (m + 1) : ℕ) : ZMod (7 ^ (m + 1)))
            = (a : ZMod _) := fun a =>
          (ZMod.natCast_eq_natCast_iff _ _ _).mpr (Nat.mod_modEq _ _)
        rw [hcast]
        rw [Nat.cast_sub (by
          have h1 := Nat.mod_lt ea hN; have h2 := Nat.mod_lt eb hN; omega)]
        rw [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
        rw [hcast, hcast]
        rw [ZMod.natCast_self]
        ring
      rw [he0, Nat.cast_zero] at hfZ
      have hmod : ((2 * ea : ℕ) : ZMod (7 ^ (m + 1))) = eb := by
        rw [Nat.cast_mul, Nat.cast_ofNat]
        exact sub_eq_zero.mp hfZ.symm
      exact (ZMod.natCast_eq_natCast_iff _ _ _).mp hmod
    set C := (2 * (ea % 7 ^ m)) / 7 ^ m with hCdef
    have hC2 : C < 2 := by
      rw [hCdef]
      exact Nat.div_lt_of_lt_mul (by
        have := Nat.mod_lt ea hP; omega)
    set t : ZMod 7 := 6 * (C : ZMod 7) with ht
    obtain ⟨k, hk7, hkq⟩ := exists_multLow_set_qdig hhm hea hea0 t
    refine ⟨1 + k * 7 ^ (m - h), multLow_not_dvd hhm, ?_, ?_⟩
    · rw [hkq, ht]
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (by omega : C ≤ 1)
        with hCv | hCv <;> rw [hCv] <;> decide
    · have hcon : ((1 + k * 7 ^ (m - h)) * eb) % 7 ^ (m + 1)
          = (2 * ((1 + k * 7 ^ (m - h)) * ea)) % 7 ^ (m + 1) := by
        have h2 := Nat.ModEq.mul_left (1 + k * 7 ^ (m - h)) heab.symm
        have heq : (1 + k * 7 ^ (m - h)) * (2 * ea)
            = 2 * ((1 + k * 7 ^ (m - h)) * ea) := by ring
        rwa [heq] at h2
      rw [qdig7_congr hcon]
      have hx2 : 2 * ((1 + k * 7 ^ (m - h)) * ea)
          = (1 + k * 7 ^ (m - h)) * ea + (1 + k * 7 ^ (m - h)) * ea :=
        two_mul _
      rw [hx2, qdig7_add]
      have hlow : ((1 + k * 7 ^ (m - h)) * ea) % 7 ^ m = ea % 7 ^ m :=
        multLow_low_part hea hea0 (le_of_lt hhm)
      rw [hlow, hkq, ← two_mul (ea % 7 ^ m), ← hCdef, ht]
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (by omega : C ≤ 1)
        with hCv | hCv <;> rw [hCv] <;> decide
  · have hνe : padicValNat 7 e ≤ m := padic_le_of_lt he0 (eMod7_lt m ea eb)
    obtain ⟨la, hla, hqa⟩ :=
      exists_unit_set_qdig_six (by omega : 0 < m) he0 rfl hνe
    have hla0 : la ≠ 0 := fun hh => hla (hh ▸ dvd_zero _)
    have hrX : runit7 (la * eb) = 2 * runit7 (la * ea) := by
      rw [runit7_mul, runit7_mul, hr]; ring
    have hsub := qdig_eMod_sub_etd7 (m := m) (x := la * ea) (y := la * eb)
    have het : etd7 m (la * ea) (la * eb)
        = 2 * qdig7 m (la * ea) - qdig7 m (la * eb) := by
      unfold etd7; rw [if_pos hrX]
    have hesmul : eMod7 m (la * ea) (la * eb)
        = (la * e) % 7 ^ (m + 1) := by
      rw [eMod7_smul (runit7_ne_zero (Nat.pos_of_ne_zero hla0)), he]
    rw [hesmul, qdig7_of_resid, hqa, het] at hsub
    set etv : ZMod 7 := 2 * qdig7 m (la * ea) - qdig7 m (la * eb) with hetv
    have hetvmem : etv ∈ ({0, 5, 6} : Finset (ZMod 7)) := by
      rcases Finset.mem_insert.mp hsub with h0 | hrest
      · have h6 : etv = 6 := by linear_combination -h0
        rw [h6]; decide
      rcases Finset.mem_insert.mp hrest with h1 | h6'
      · have h5 : etv = 5 := by linear_combination -h1
        rw [h5]; decide
      · rw [Finset.mem_singleton] at h6'
        have h0' : etv = 0 := by linear_combination -h6'
        rw [h0']; decide
    set t' : ZMod 7 := if etv = 0 then 0 else 6 with ht'
    have hν1 : padicValNat 7 (la * ea) = h := by
      rw [padicValNat_mul_seven hla hea0, hea]
    have hne1 : la * ea ≠ 0 := mul_ne_zero hla0 hea0
    obtain ⟨k, hk7, hkt⟩ := exists_multLow_set_qdig hhm hν1 hne1 t'
    have hν2 : padicValNat 7 (la * eb) = h := by
      rw [padicValNat_mul_seven hla heb0, heb]
    have hqb : qdig7 m ((1 + k * 7 ^ (m - h)) * (la * eb))
        = qdig7 m (la * eb) + (k : ZMod 7) * runit7 (la * eb) :=
      qdig7_multLow hhm hν2
    have hqa' : qdig7 m ((1 + k * 7 ^ (m - h)) * (la * ea))
        = qdig7 m (la * ea) + (k : ZMod 7) * runit7 (la * ea) :=
      qdig7_multLow hhm hν1
    refine ⟨(1 + k * 7 ^ (m - h)) * la,
      Nat.prime_seven.not_dvd_mul (multLow_not_dvd hhm) hla, ?_, ?_⟩
    · rw [mul_assoc, hkt]
      by_cases hetv0 : etv = 0
      · rw [ht', hetv0]; decide
      · rw [ht', if_neg hetv0]; decide
    · rw [mul_assoc]
      have hk' : (k : ZMod 7) * runit7 (la * ea) = t' - qdig7 m (la * ea) := by
        linear_combination hkt - hqa'
      have hqe : qdig7 m ((1 + k * 7 ^ (m - h)) * (la * eb))
          = 2 * t' - etv := by
        rw [hqb, hrX]
        linear_combination 2 * hk' + hetv
      rw [hqe]
      rcases Finset.mem_insert.mp hetvmem with h0 | hrest
      · rw [ht', h0]; decide
      rcases Finset.mem_insert.mp hrest with h5 | h6
      · rw [ht', h5]; decide
      · rw [Finset.mem_singleton] at h6
        rw [ht', h6]; decide

/-- Equal level `h < m`: the ratio `r(e_a)/r(e_b) ∈ {1,2,4}` dispatch
(same-`r` or the two `twoX` directions). -/
private theorem case66_eq_level {m : ℕ} (hm : 2 ≤ m)
    {ea eb h : ℕ} (hea : padicValNat 7 ea = h) (heb : padicValNat 7 eb = h)
    (hea0 : ea ≠ 0) (heb0 : eb ≠ 0)
    (healt : ea < 7 ^ (m + 1)) (heblt : eb < 7 ^ (m + 1))
    (hhm : h < m)
    (hr : runit7 ea = runit7 eb ∨ runit7 eb = 2 * runit7 ea
      ∨ runit7 ea = 2 * runit7 eb) :
    ∃ lam₁ : ℕ, ¬ 7 ∣ lam₁ ∧
      qdig7 m (lam₁ * ea) ∈ ({0, 6} : Finset (ZMod 7)) ∧
      qdig7 m (lam₁ * eb) ∈ ({0, 6} : Finset (ZMod 7)) := by
  rcases hr with hrr | hrr | hrr
  · exact case66_same_r hm hea heb hea0 heb0 healt heblt hhm hrr
  · exact case66_twoX hm hea heb hea0 heb0 healt heblt hhm hrr
  · obtain ⟨l, hl, hqa, hqb⟩ :=
      case66_twoX hm heb hea heb0 hea0 heblt healt hhm hrr
    exact ⟨l, hl, hqb, hqa⟩


/-- Units of `ZMod 7` split into the `{1,2,4}` coset and its negative. -/
private theorem zmod7_unit_split {a b : ZMod 7} (ha : a ≠ 0) (hb : b ≠ 0) :
    (b = a ∨ b = 2 * a ∨ b = 4 * a) ∨
    (b = 3 * a ∨ b = 5 * a ∨ b = 6 * a) := by
  have h : ∀ c : ZMod 7, c ≠ 0 →
      c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 ∨ c = 6 := by
    intro c hc
    have h1 : c ∈ (Finset.univ : Finset (ZMod 7)) \ {0} := by
      rw [Finset.mem_sdiff]
      exact ⟨Finset.mem_univ _, by simpa using hc⟩
    have h2 : (Finset.univ : Finset (ZMod 7)) \ {0}
        = ({1, 2, 3, 4, 5, 6} : Finset (ZMod 7)) := by decide
    rw [h2] at h1
    simpa [Finset.mem_insert, Finset.mem_singleton] using h1
  set c := b * a⁻¹ with hceq
  have hc0 : c ≠ 0 := mul_ne_zero hb (inv_ne_zero ha)
  have hbc : c * a = b := by
    rw [hceq, mul_assoc, inv_mul_cancel₀ ha, mul_one]
  rcases h c hc0 with hh | hh | hh | hh | hh | hh <;> rw [hh] at hbc <;>
    first
      | (left; left; simpa using hbc.symm)
      | (left; right; left; simpa using hbc.symm)
      | (left; right; right; simpa using hbc.symm)
      | (right; left; simpa using hbc.symm)
      | (right; right; left; simpa using hbc.symm)
      | (right; right; right; simpa using hbc.symm)

/-- Swapping a same-class pair negates the `qdig` (valid for `ν(e) < m`). -/
private theorem qdig7_eMod7_swap {m lam x y : ℕ}
    (hlam : ¬ 7 ∣ lam) (hx0 : x ≠ 0) (hy0 : y ≠ 0)
    (hxy : runit7 x = runit7 y)
    (he0 : eMod7 m x y ≠ 0)
    (hν : padicValNat 7 (eMod7 m x y) < m) :
    qdig7 m (eMod7 m (lam * y) (lam * x))
      = 6 - qdig7 m (eMod7 m (lam * x) (lam * y)) := by
  have hlam0 : lam ≠ 0 := fun h => hlam (h ▸ dvd_zero _)
  have hrl : runit7 lam ≠ 0 := runit7_ne_zero (Nat.pos_of_ne_zero hlam0)
  have hswap : eMod7 m (lam * y) (lam * x)
      = (7 ^ (m + 1) - eMod7 m (lam * x) (lam * y)) % 7 ^ (m + 1) :=
    eMod7_same_swap (rel_same_of_mul hlam hxy hy0)
      (rel_same_of_mul hlam hxy.symm hx0)
  rw [hswap]
  apply qdig7_neg_low (eMod7_lt _ _ _)
  rw [eMod7_smul hrl,
    Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 7 (Nat.le_succ m))]
  intro hcon
  have hdvd : 7 ^ m ∣ lam * eMod7 m x y := Nat.dvd_of_mod_eq_zero hcon
  have hνe : padicValNat 7 (lam * eMod7 m x y)
      = padicValNat 7 (eMod7 m x y) := padicValNat_mul_seven hlam he0
  have hle := (Nat.pow_dvd_iff_le_padicValNat (by norm_num)
    (mul_ne_zero hlam0 he0)).mp hdvd
  omega

/-- Barajas–Serra §6.6: `|A1| = |A2| = 2`, `|A4| = 1` (`hc66` shape).
The delicate `ν = m` branch is taken as the parameter `hc66top`
(implemented by `case66_top` below). -/
theorem case66 {m : ℕ} (hm : 2 ≤ m) {A1 A2 A4 : Finset ℕ}
    (hA1 : A1.card = 2) (hA2 : A2.card = 2) (hA4 : A4.card = 1)
    (hpos : ∀ d ∈ A1 ∪ A2 ∪ A4, 0 < d)
    (hunit : ∀ d ∈ A1 ∪ A2 ∪ A4, padicValNat 7 d = 0)
    {s : ZMod 7} (hs : s ∈ ({1, 2, 4} : Finset (ZMod 7)))
    (hcls1 : ∀ d ∈ A1, runit7 d = s)
    (hcls2 : ∀ d ∈ A2, runit7 d = 2 * s)
    (hcls4 : ∀ d ∈ A4, runit7 d = 4 * s)
    (hc66top :
      ∀ {d1 d2 d3 d4 d5 : ℕ}, d1 ≠ d2 → d3 ≠ d4 →
        0 < d1 → 0 < d2 → 0 < d3 → 0 < d4 → 0 < d5 →
        padicValNat 7 d1 = 0 → padicValNat 7 d2 = 0 →
        padicValNat 7 d3 = 0 → padicValNat 7 d4 = 0 →
        padicValNat 7 d5 = 0 →
        ∀ {s' : ZMod 7}, s' ∈ ({1, 2, 4} : Finset (ZMod 7)) →
        runit7 d1 = s' → runit7 d2 = s' →
        runit7 d3 = 2 * s' → runit7 d4 = 2 * s' → runit7 d5 = 4 * s' →
        eMod7 m d1 d2 ≠ 0 → eMod7 m d3 d4 ≠ 0 →
        padicValNat 7 (eMod7 m d1 d2) = m →
        padicValNat 7 (eMod7 m d3 d4) = m →
        ∃ lam : ℕ, ¬ 7 ∣ lam ∧
          good7 m lam ({d1, d2, d3, d4, d5} : Finset ℕ)) :
    ∃ lam : ℕ, ¬ 7 ∣ lam ∧ good7 m lam (A1 ∪ A2 ∪ A4) := by
  classical
  obtain ⟨d1, d2, hd12, hA1eq⟩ := Finset.card_eq_two.mp hA1
  obtain ⟨d3, d4, hd34, hA2eq⟩ := Finset.card_eq_two.mp hA2
  obtain ⟨d5, hA4eq⟩ := Finset.card_eq_one.mp hA4
  have hd1 : d1 ∈ A1 := by rw [hA1eq]; exact Finset.mem_insert_self _ _
  have hd2 : d2 ∈ A1 := by
    rw [hA1eq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hd3 : d3 ∈ A2 := by rw [hA2eq]; exact Finset.mem_insert_self _ _
  have hd4 : d4 ∈ A2 := by
    rw [hA2eq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hd5 : d5 ∈ A4 := by rw [hA4eq]; exact Finset.mem_singleton_self _
  have hd1p : 0 < d1 :=
    hpos d1 (Finset.mem_union_left _ (Finset.mem_union_left _ hd1))
  have hd2p : 0 < d2 :=
    hpos d2 (Finset.mem_union_left _ (Finset.mem_union_left _ hd2))
  have hd3p : 0 < d3 :=
    hpos d3 (Finset.mem_union_left _ (Finset.mem_union_right _ hd3))
  have hd4p : 0 < d4 :=
    hpos d4 (Finset.mem_union_left _ (Finset.mem_union_right _ hd4))
  have hd5p : 0 < d5 := hpos d5 (Finset.mem_union_right _ hd5)
  have hd1u : padicValNat 7 d1 = 0 :=
    hunit d1 (Finset.mem_union_left _ (Finset.mem_union_left _ hd1))
  have hd2u : padicValNat 7 d2 = 0 :=
    hunit d2 (Finset.mem_union_left _ (Finset.mem_union_left _ hd2))
  have hd3u : padicValNat 7 d3 = 0 :=
    hunit d3 (Finset.mem_union_left _ (Finset.mem_union_right _ hd3))
  have hd4u : padicValNat 7 d4 = 0 :=
    hunit d4 (Finset.mem_union_left _ (Finset.mem_union_right _ hd4))
  have hd5u : padicValNat 7 d5 = 0 :=
    hunit d5 (Finset.mem_union_right _ hd5)
  have hd1n : d1 ≠ 0 := ne_of_gt hd1p
  have hd2n : d2 ≠ 0 := ne_of_gt hd2p
  have hd3n : d3 ≠ 0 := ne_of_gt hd3p
  have hd4n : d4 ≠ 0 := ne_of_gt hd4p
  have hd5n : d5 ≠ 0 := ne_of_gt hd5p
  -- `qdig (lam·e)` conditions lift to the scaled pair `qdig (e(λx, λy))`
  have hconv : ∀ (lam x y : ℕ), ¬ 7 ∣ lam →
      qdig7 m (lam * eMod7 m x y) ∈ ({0, 6} : Finset (ZMod 7)) →
      qdig7 m (eMod7 m (lam * x) (lam * y))
        ∈ ({0, 6} : Finset (ZMod 7)) := by
    intro lam x y hl hq
    have hrl : runit7 lam ≠ 0 := runit7_ne_zero
      (Nat.pos_of_ne_zero (fun h => hl (h ▸ dvd_zero _)))
    rw [eMod7_smul hrl, qdig7_of_resid]
    exact hq
  set e12 := eMod7 m d1 d2 with he12
  set e34 := eMod7 m d3 d4 with he34
  by_cases htop : padicValNat 7 e12 = m ∧ padicValNat 7 e34 = m
  · -- delicate top branch: `hc66top` supplies `good7` directly
    have h12 : e12 ≠ 0 := by
      intro h0
      rw [h0, padicValNat.zero] at htop
      exact absurd htop.1 (by omega)
    have h34 : e34 ≠ 0 := by
      intro h0
      rw [h0, padicValNat.zero] at htop
      exact absurd htop.2 (by omega)
    obtain ⟨lam, hlam, hgood⟩ := hc66top hd12 hd34 hd1p hd2p hd3p hd4p hd5p
      hd1u hd2u hd3u hd4u hd5u hs (hcls1 d1 hd1) (hcls1 d2 hd2)
      (hcls2 d3 hd3) (hcls2 d4 hd4) (hcls4 d5 hd5) h12 h34 htop.1 htop.2
    refine ⟨lam, hlam, ?_⟩
    have hAe : A1 ∪ A2 ∪ A4 = ({d1, d2, d3, d4, d5} : Finset ℕ) := by
      rw [hA1eq, hA2eq, hA4eq]
      ext x
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto
    rwa [hAe]
  suffices h : ∃ lam₁ : ℕ, ¬ 7 ∣ lam₁ ∧
      qdig7 m (eMod7 m (lam₁ * d1) (lam₁ * d2))
        ∈ ({0, 6} : Finset (ZMod 7)) ∧
      qdig7 m (eMod7 m (lam₁ * d3) (lam₁ * d4))
        ∈ ({0, 6} : Finset (ZMod 7)) by
    obtain ⟨lam₁, hl1, hq12, hq34⟩ := h
    exact case66_finish (by omega : 0 < m) hpos hunit hs hcls1 hcls2 hcls4
      hA1eq hA2eq hA4eq hl1 hq12 hq34
  by_cases h12 : e12 = 0
  · by_cases h34 : e34 = 0
    · refine ⟨1, by decide, ?_, ?_⟩
      · rw [one_mul, one_mul]
        show qdig7 m e12 ∈ ({0, 6} : Finset (ZMod 7))
        rw [h12]
        simp [qdig7]
      · rw [one_mul, one_mul]
        show qdig7 m e34 ∈ ({0, 6} : Finset (ZMod 7))
        rw [h34]
        simp [qdig7]
    · obtain ⟨lam, hlam, hq⟩ := exists_unit_set_qdig_six (by omega : 0 < m)
        h34 rfl (padic_le_of_lt h34 (eMod7_lt m d3 d4))
      refine ⟨lam, hlam, ?_, ?_⟩
      · apply hconv _ _ _ hlam
        show qdig7 m (lam * e12) ∈ ({0, 6} : Finset (ZMod 7))
        rw [h12, mul_zero]
        simp [qdig7]
      · exact hconv _ _ _ hlam (by rw [hq]; decide)
  · by_cases h34 : e34 = 0
    · obtain ⟨lam, hlam, hq⟩ := exists_unit_set_qdig_six (by omega : 0 < m)
        h12 rfl (padic_le_of_lt h12 (eMod7_lt m d1 d2))
      refine ⟨lam, hlam, ?_, ?_⟩
      · exact hconv _ _ _ hlam (by rw [hq]; decide)
      · apply hconv _ _ _ hlam
        show qdig7 m (lam * e34) ∈ ({0, 6} : Finset (ZMod 7))
        rw [h34, mul_zero]
        simp [qdig7]
    · have hν12 : padicValNat 7 e12 ≤ m :=
        padic_le_of_lt h12 (eMod7_lt m d1 d2)
      have hν34 : padicValNat 7 e34 ≤ m :=
        padic_le_of_lt h34 (eMod7_lt m d3 d4)
      rcases lt_trichotomy (padicValNat 7 e12) (padicValNat 7 e34)
        with hlt | heq | hgt
      · obtain ⟨lam, hlam, hq1, hq2⟩ := case66_two_level (by omega : 0 < m)
          rfl rfl h12 h34 hlt hν34
        exact ⟨lam, hlam, hconv _ _ _ hlam (by rw [hq1]; decide),
          hconv _ _ _ hlam (by rw [hq2]; decide)⟩
      · rcases eq_or_lt_of_le hν12 with hνm | hνlt
        · have hν34m : padicValNat 7 e34 = m := by omega
          exact absurd ⟨hνm, hν34m⟩ htop
        · have hν34lt : padicValNat 7 e34 < m := by omega
          have hr12 : runit7 e12 ≠ 0 :=
            runit7_ne_zero (Nat.pos_of_ne_zero h12)
          have hr34 : runit7 e34 ≠ 0 :=
            runit7_ne_zero (Nat.pos_of_ne_zero h34)
          have h34eq : runit7 d3 = runit7 d4 := by
            rw [hcls2 d3 hd3, hcls2 d4 hd4]
          rcases zmod7_unit_split hr12 hr34 with hg | hb
          · rcases hg with h | h | h
            · obtain ⟨lam, hlam, hq1, hq2⟩ := case66_eq_level hm rfl
                heq.symm h12 h34 (eMod7_lt _ _ _) (eMod7_lt _ _ _)
                hνlt (Or.inl h.symm)
              exact ⟨lam, hlam, hconv _ _ _ hlam hq1, hconv _ _ _ hlam hq2⟩
            · obtain ⟨lam, hlam, hq1, hq2⟩ := case66_eq_level hm rfl
                heq.symm h12 h34 (eMod7_lt _ _ _) (eMod7_lt _ _ _)
                hνlt (Or.inr (Or.inl h))
              exact ⟨lam, hlam, hconv _ _ _ hlam hq1, hconv _ _ _ hlam hq2⟩
            · have hrr : runit7 e12 = 2 * runit7 e34 := by
                rw [h, ← mul_assoc, show (2 : ZMod 7) * 4 = 1 from by decide,
                  one_mul]
              obtain ⟨lam, hlam, hq1, hq2⟩ := case66_eq_level hm rfl
                heq.symm h12 h34 (eMod7_lt _ _ _) (eMod7_lt _ _ _)
                hνlt (Or.inr (Or.inr hrr))
              exact ⟨lam, hlam, hconv _ _ _ hlam hq1, hconv _ _ _ hlam hq2⟩
          · set e34' := eMod7 m d4 d3 with he34'
            have hrel34 : residueRelOf d3 d4 = residueRel.same :=
              rel_same_of_eq h34eq hd4n
            have hrel43 : residueRelOf d4 d3 = residueRel.same :=
              rel_same_of_eq h34eq.symm hd3n
            have hswap : e34' = (7 ^ (m + 1) - e34) % 7 ^ (m + 1) := by
              rw [he34']
              exact eMod7_same_swap hrel34 hrel43
            have h34'0 : e34' ≠ 0 := by
              rw [hswap]
              intro hcon
              have hdvd : 7 ^ (m + 1) ∣ 7 ^ (m + 1) - e34 :=
                Nat.dvd_of_mod_eq_zero hcon
              have hpos34 : 0 < e34 := Nat.pos_of_ne_zero h34
              have hsub : 0 < 7 ^ (m + 1) - e34 :=
                Nat.sub_pos_of_lt (eMod7_lt m d3 d4)
              have hle := Nat.le_of_dvd hsub hdvd
              have hlt34 := eMod7_lt m d3 d4
              omega
            have h34'lt : e34' < 7 ^ (m + 1) := eMod7_lt m d4 d3
            have hν34' : padicValNat 7 e34' = padicValNat 7 e34 := by
              rw [hswap]
              exact (neg_resid h34 (eMod7_lt m d3 d4) hν34).1
            have hr34' : runit7 e34' = - runit7 e34 := by
              rw [hswap]
              exact (neg_resid h34 (eMod7_lt m d3 d4) hν34).2
            have hν34'lt : padicValNat 7 e34' < m := by omega
            have hfin : ∀ lam : ℕ, ¬ 7 ∣ lam →
                qdig7 m (lam * e34') ∈ ({0, 6} : Finset (ZMod 7)) →
                qdig7 m (eMod7 m (lam * d3) (lam * d4))
                  ∈ ({0, 6} : Finset (ZMod 7)) := by
              intro lam hl hq
              have hq' := hconv lam d4 d3 hl hq
              have hsw := qdig7_eMod7_swap hl hd3n hd4n h34eq h34 hν34lt
              rw [hsw] at hq'
              simp only [Finset.mem_insert, Finset.mem_singleton] at hq' ⊢
              rcases hq' with hh | hh
              · right
                linear_combination -hh
              · left
                linear_combination -hh
            rcases hb with h | h | h
            · have hrr : runit7 e12 = 2 * runit7 e34' := by
                rw [hr34', h, mul_neg, ← mul_assoc,
                  show (2 : ZMod 7) * 3 = -1 from by decide, neg_one_mul,
                  neg_neg]
              obtain ⟨lam, hlam, hq1, hq2⟩ := case66_eq_level hm rfl
                (hν34'.trans heq.symm) h12 h34'0
                (eMod7_lt _ _ _) h34'lt hνlt (Or.inr (Or.inr hrr))
              exact ⟨lam, hlam, hconv _ _ _ hlam hq1, hfin _ hlam hq2⟩
            · have hrr : runit7 e34' = 2 * runit7 e12 := by
                rw [hr34', h, ← neg_mul,
                  show (-(5 : ZMod 7)) = 2 from by decide]
              obtain ⟨lam, hlam, hq1, hq2⟩ := case66_eq_level hm rfl
                (hν34'.trans heq.symm) h12 h34'0
                (eMod7_lt _ _ _) h34'lt hνlt (Or.inr (Or.inl hrr))
              exact ⟨lam, hlam, hconv _ _ _ hlam hq1, hfin _ hlam hq2⟩
            · have hrr : runit7 e12 = runit7 e34' := by
                rw [hr34', h, ← neg_mul,
                  show (-(6 : ZMod 7)) = 1 from by decide, one_mul]
              obtain ⟨lam, hlam, hq1, hq2⟩ := case66_eq_level hm rfl
                (hν34'.trans heq.symm) h12 h34'0
                (eMod7_lt _ _ _) h34'lt hνlt (Or.inl hrr)
              exact ⟨lam, hlam, hconv _ _ _ hlam hq1, hfin _ hlam hq2⟩
      · obtain ⟨lam, hlam, hq1, hq2⟩ := case66_two_level (by omega : 0 < m)
          rfl rfl h34 h12 hgt hν12
        exact ⟨lam, hlam, hconv _ _ _ hlam (by rw [hq2]; decide),
          hconv _ _ _ hlam (by rw [hq1]; decide)⟩


/-! ### §4 The delicate `ν(e12) = ν(e34) = m` branch

Both pair-differences are pure top residues `r·7^m`.  After within-pair
swaps we take `r12, r34 ∈ {1,2,4}`; `r12 = r34` is closed by a single
scalar through `case66_finish`; `r12 = 2·r34` (case a) and `r34 = 2·r12`
(case b) use the `λk = 1 + k·7^m` family together with Lemma-7/ε machinery
on `e24, e25` (paper §6.6 last paragraph). -/

/-- `q(t·7^m) = t` for `t < 7`. -/
private theorem qdig7_top_resid {m t : ℕ} (ht : t < 7) :
    qdig7 m (t * 7 ^ m) = (t : ZMod 7) := by
  rw [qdig7_eq_cast_div, Nat.mul_div_cancel _ (Nat.pow_pos (by norm_num))]

/-- **σ-linkage (unified)**: for `e = (a·u + N − v) % N` with `a ∈ {1,2}`
and `e ≡ 0 (mod 7^m)` — the `twoX`/`twoY`/`same` top-residue cases — the
digit combination `a·q(u) − q(v)` equals `e/7^m − ⌊a·(u % 7^m)/7^m⌋`.
The subtracted term is the borrow `σ ∈ {0,1}` (`= 0` when `a = 1`). -/
private theorem etd_combo_of_low {m u v a e : ℕ} (ha : a = 1 ∨ a = 2)
    (he : e = (a * (u % 7 ^ (m + 1)) + 7 ^ (m + 1) - v % 7 ^ (m + 1))
      % 7 ^ (m + 1))
    (he0 : e % 7 ^ m = 0) :
    (a : ZMod 7) * qdig7 m u - qdig7 m v
      = ((e / 7 ^ m : ℕ) : ZMod 7)
        - ((a * (u % 7 ^ m) / 7 ^ m : ℕ) : ZMod 7) := by
  have hP : (0 : ℕ) < 7 ^ m := Nat.pow_pos (by norm_num)
  have hN : (0 : ℕ) < 7 ^ (m + 1) := Nat.pow_pos (by norm_num)
  have hPN : 7 ^ m ∣ 7 ^ (m + 1) := Nat.pow_dvd_pow 7 (Nat.le_succ m)
  have hN7 : 7 ^ (m + 1) = 7 * 7 ^ m := pow_succ' 7 m
  have hN7b : 7 ^ (m + 1) = 7 ^ m * 7 := pow_succ 7 m
  -- digit decompositions `u' = A·P + g`, `v' = B·P + h`
  set Au := (u % 7 ^ (m + 1)) / 7 ^ m with hAu
  set gu := (u % 7 ^ (m + 1)) % 7 ^ m with hgu
  have hu' : u % 7 ^ (m + 1) = Au * 7 ^ m + gu := by
    rw [mul_comm]; exact (Nat.div_add_mod _ _).symm
  have hAu7 : Au < 7 := by
    rw [hAu, Nat.div_lt_iff_lt_mul hP, ← hN7]
    exact Nat.mod_lt _ hN
  have hgu7 : gu < 7 ^ m := Nat.mod_lt _ hP
  set Av := (v % 7 ^ (m + 1)) / 7 ^ m with hAv
  set gv := (v % 7 ^ (m + 1)) % 7 ^ m with hgv
  have hv' : v % 7 ^ (m + 1) = Av * 7 ^ m + gv := by
    rw [mul_comm]; exact (Nat.div_add_mod _ _).symm
  have hAv7 : Av < 7 := by
    rw [hAv, Nat.div_lt_iff_lt_mul hP, ← hN7]
    exact Nat.mod_lt _ hN
  have hgv7 : gv < 7 ^ m := Nat.mod_lt _ hP
  -- low-part constraint: `gv = (a·gu) % 7^m`
  have hgv_eq : gv = (a * gu) % 7 ^ m := by
    have hcast : ((e : ℕ) : ZMod (7 ^ m)) = 0 := by
      have h1 : ((e % 7 ^ m : ℕ) : ZMod (7 ^ m))
          = ((e : ℕ) : ZMod (7 ^ m)) := by rw [ZMod.natCast_mod]
      rw [← h1, he0]; simp
    rw [he, natCast_zmod_of_dvd hPN] at hcast
    rw [Nat.cast_sub (by
      have hlt : v % 7 ^ (m + 1) < 7 ^ (m + 1) := Nat.mod_lt _ hN
      omega : v % 7 ^ (m + 1) ≤ a * (u % 7 ^ (m + 1)) + 7 ^ (m + 1))] at hcast
    rw [Nat.cast_add] at hcast
    have hN0 : ((7 ^ (m + 1) : ℕ) : ZMod (7 ^ m)) = 0 := by
      rw [← natCast_zmod_of_dvd hPN (7 ^ (m + 1)), Nat.mod_self, Nat.cast_zero]
    have hugu : ((u % 7 ^ (m + 1) : ℕ) : ZMod (7 ^ m)) = (gu : ZMod _) := by
      rw [hgu, ZMod.natCast_mod]
    have hvgv : ((v % 7 ^ (m + 1) : ℕ) : ZMod (7 ^ m)) = (gv : ZMod _) := by
      rw [hgv, ZMod.natCast_mod]
    rw [hN0, add_zero, Nat.cast_mul, hugu, hvgv] at hcast
    -- `a·gu − gv = 0` in `ZMod P`
    have hmod : gv % 7 ^ m = (a * gu) % 7 ^ m := by
      have hz : ((gv : ℕ) : ZMod (7 ^ m)) = ((a * gu : ℕ) : ZMod _) := by
        push_cast
        linear_combination -hcast
      exact (ZMod.natCast_eq_natCast_iff' _ _ _).mp hz
    rwa [Nat.mod_eq_of_lt hgv7] at hmod
  -- `σ = ⌊a·gu/P⌋`, and `a·gu = gv + σ·P`
  set σ := a * gu / 7 ^ m with hσ
  have hσP : a * gu = gv + σ * 7 ^ m := by
    have h1 := Nat.div_add_mod (a * gu) (7 ^ m)
    rw [mul_comm (7 ^ m) (a * gu / 7 ^ m)] at h1
    rw [hσ, hgv_eq]
    omega
  have hσ1 : σ < 2 := by
    have h2 : a * gu < 7 ^ m * 2 := by
      rcases ha with rfl | rfl
      · rw [one_mul]; omega
      · omega
    rw [hσ]
    exact Nat.div_lt_of_lt_mul h2
  -- the full wrapped sum reads `(a·Au + σ + 7 − Av)·P`
  have hsum' : a * (u % 7 ^ (m + 1)) + 7 ^ (m + 1) - v % 7 ^ (m + 1)
      = (a * Au + σ + 7 - Av) * 7 ^ m := by
    rw [hu', hv', hN7, mul_add, ← mul_assoc, hσP]
    have hexp : (a * Au + σ + 7 - Av) * 7 ^ m
        = a * Au * 7 ^ m + σ * 7 ^ m + 7 * 7 ^ m - Av * 7 ^ m := by
      rw [Nat.sub_mul, Nat.add_mul, Nat.add_mul]
    rw [hexp]
    have := hgu7
    have := hAv7
    omega
  have he' : e = ((a * Au + σ + 7 - Av) % 7) * 7 ^ m := by
    rw [he, hsum', hN7, Nat.mul_mod_mul_right]
  have heP : e / 7 ^ m = (a * Au + σ + 7 - Av) % 7 := by
    rw [he', Nat.mul_div_cancel _ hP]
  -- `q(u) = Au`, `q(v) = Av` in `ZMod 7`
  have hqu : qdig7 m u = (Au : ZMod 7) := by
    rw [qdig7_eq_cast_div, hAu, hN7b, Nat.mod_mul_right_div_self]
    exact (ZMod.natCast_mod _ _).symm
  have hqv : qdig7 m v = (Av : ZMod 7) := by
    rw [qdig7_eq_cast_div, hAv, hN7b, Nat.mod_mul_right_div_self]
    exact (ZMod.natCast_mod _ _).symm
  have hePZ : ((e / 7 ^ m : ℕ) : ZMod 7) = (a : ZMod 7) * Au - Av + σ := by
    rw [heP, ZMod.natCast_mod]
    have hle : Av ≤ a * Au + σ + 7 := by
      have h7 : (7 : ℕ) ≤ a * Au + σ + 7 := Nat.le_add_left _ _
      omega
    rw [Nat.cast_sub hle]
    push_cast
    rw [show (7 : ZMod 7) = 0 from by decide, add_zero]
    ring
  have hσZ : ((a * (u % 7 ^ m) / 7 ^ m : ℕ) : ZMod 7) = (σ : ZMod 7) := by
    have hug : u % 7 ^ m = gu := by
      rw [hgu]; exact (Nat.mod_mod_of_dvd _ hPN).symm
    rw [hug, hσ]
  rw [hqu, hqv, hePZ, hσZ]
  ring

/-- `same`-pair linkage: `e ≡ 0 (mod 7^m)` forces `ẽ = e/7^m` exactly. -/
private theorem etd7_same_of_low {m x y : ℕ}
    (hrel : residueRelOf x y = residueRel.same)
    (he : eMod7 m x y % 7 ^ m = 0) :
    etd7 m x y = ((eMod7 m x y / 7 ^ m : ℕ) : ZMod 7) := by
  obtain ⟨h1, h2⟩ := (residueRelOf_eq_same).mp hrel
  have hE : eMod7 m x y
      = (1 * (x % 7 ^ (m + 1)) + 7 ^ (m + 1) - y % 7 ^ (m + 1))
        % 7 ^ (m + 1) := by
    unfold eMod7
    rw [if_neg h1, if_neg h2, one_mul]
  have hEt : etd7 m x y = qdig7 m x - qdig7 m y := by
    unfold etd7
    rw [if_neg h1, if_neg h2]
  rw [hEt]
  have key := etd_combo_of_low (a := 1) (Or.inl rfl) hE he
  simp only [Nat.cast_one, one_mul] at key
  rw [key]
  have hz : x % 7 ^ m / 7 ^ m = 0 :=
    Nat.div_eq_of_lt (Nat.mod_lt _ (Nat.pow_pos (by norm_num)))
  rw [hz]
  simp

/-- `twoX` σ-linkage: `ẽ = e/7^m − σ` with `σ = ⌊2·(x%7^m)/7^m⌋`. -/
private theorem etd7_twoX_of_low {m x y : ℕ}
    (h : runit7 y = 2 * runit7 x) (he : eMod7 m x y % 7 ^ m = 0) :
    etd7 m x y = ((eMod7 m x y / 7 ^ m : ℕ) : ZMod 7)
      - ((2 * (x % 7 ^ m) / 7 ^ m : ℕ) : ZMod 7) := by
  have hE : eMod7 m x y
      = (2 * (x % 7 ^ (m + 1)) + 7 ^ (m + 1) - y % 7 ^ (m + 1))
        % 7 ^ (m + 1) := by
    unfold eMod7
    rw [if_pos h]
  have hEt : etd7 m x y = 2 * qdig7 m x - qdig7 m y := by
    unfold etd7
    rw [if_pos h]
  rw [hEt]
  exact etd_combo_of_low (a := 2) (Or.inr rfl) hE he

/-- `twoY` σ-linkage: `ẽ = e/7^m − σ` with `σ = ⌊2·(y%7^m)/7^m⌋`. -/
private theorem etd7_twoY_of_low {m x y : ℕ}
    (h : runit7 x = 2 * runit7 y) (h' : runit7 y ≠ 2 * runit7 x)
    (he : eMod7 m x y % 7 ^ m = 0) :
    etd7 m x y = ((eMod7 m x y / 7 ^ m : ℕ) : ZMod 7)
      - ((2 * (y % 7 ^ m) / 7 ^ m : ℕ) : ZMod 7) := by
  have hE : eMod7 m x y
      = (2 * (y % 7 ^ (m + 1)) + 7 ^ (m + 1) - x % 7 ^ (m + 1))
        % 7 ^ (m + 1) := by
    unfold eMod7
    rw [if_neg h', if_pos h]
  have hEt : etd7 m x y = 2 * qdig7 m y - qdig7 m x := by
    unfold etd7
    rw [if_neg h', if_pos h]
  rw [hEt]
  exact etd_combo_of_low (a := 2) (u := y) (v := x) (Or.inr rfl) hE he

/-- Doubled low block: `2·(W·7^{m−1} + u)/7^m = (2W + ⌊2u/7^{m−1}⌋)/7`. -/
private theorem two_mul_low_div {m W u : ℕ} (hm : 1 ≤ m)
    (hW : W < 7) (hu : u < 7 ^ (m - 1)) :
    2 * (W * 7 ^ (m - 1) + u) / 7 ^ m
      = (2 * W + 2 * u / 7 ^ (m - 1)) / 7 := by
  have hP : (0 : ℕ) < 7 ^ (m - 1) := Nat.pow_pos (by norm_num)
  have hm7 : 7 ^ m = 7 ^ (m - 1) * 7 := by
    rw [← pow_succ]
    congr 1
    omega
  have hv : 2 * u % 7 ^ (m - 1) < 7 ^ (m - 1) := Nat.mod_lt _ hP
  have hde : 2 * (W * 7 ^ (m - 1) + u)
      = (2 * W + 2 * u / 7 ^ (m - 1)) * 7 ^ (m - 1)
        + 2 * u % 7 ^ (m - 1) := by
    have h2u := Nat.div_add_mod (2 * u) (7 ^ (m - 1))
    have hexp : (2 * W + 2 * u / 7 ^ (m - 1)) * 7 ^ (m - 1)
        = 2 * (W * 7 ^ (m - 1)) + 7 ^ (m - 1) * (2 * u / 7 ^ (m - 1)) := by
      ring
    rw [hexp]
    omega
  rw [hde, hm7, ← Nat.div_div_eq_div_mul, add_comm _ (2 * u % 7 ^ (m - 1)),
    Nat.add_mul_div_right _ _ hP, Nat.div_eq_of_lt hv, zero_add]

/-- For a `twoY` pair with `e ≡ 0 (mod 7^m)`, the low blocks satisfy
`x % 7^m = (2·(y % 7^m)) % 7^m`. -/
private theorem low_link_twoY {m x y : ℕ}
    (h : runit7 x = 2 * runit7 y) (h' : runit7 y ≠ 2 * runit7 x)
    (he : eMod7 m x y % 7 ^ m = 0) :
    x % 7 ^ m = (2 * (y % 7 ^ m)) % 7 ^ m := by
  have hP : (0 : ℕ) < 7 ^ m := Nat.pow_pos (by norm_num)
  have hN : (0 : ℕ) < 7 ^ (m + 1) := Nat.pow_pos (by norm_num)
  have hPN : 7 ^ m ∣ 7 ^ (m + 1) := Nat.pow_dvd_pow 7 (Nat.le_succ m)
  have hE : eMod7 m x y
      = (2 * (y % 7 ^ (m + 1)) + 7 ^ (m + 1) - x % 7 ^ (m + 1))
        % 7 ^ (m + 1) := by
    unfold eMod7
    rw [if_neg h', if_pos h]
  have hcast : ((eMod7 m x y : ℕ) : ZMod (7 ^ m)) = 0 := by
    have h1 : ((eMod7 m x y % 7 ^ m : ℕ) : ZMod (7 ^ m))
        = ((eMod7 m x y : ℕ) : ZMod (7 ^ m)) := by rw [ZMod.natCast_mod]
    rw [← h1, he]; simp
  rw [hE, natCast_zmod_of_dvd hPN] at hcast
  rw [Nat.cast_sub (by
    have hlt : x % 7 ^ (m + 1) < 7 ^ (m + 1) := Nat.mod_lt _ hN
    omega : x % 7 ^ (m + 1) ≤ 2 * (y % 7 ^ (m + 1)) + 7 ^ (m + 1))] at hcast
  rw [Nat.cast_add] at hcast
  have hN0 : ((7 ^ (m + 1) : ℕ) : ZMod (7 ^ m)) = 0 := by
    rw [← natCast_zmod_of_dvd hPN (7 ^ (m + 1)), Nat.mod_self, Nat.cast_zero]
  have hxx : ((x % 7 ^ (m + 1) : ℕ) : ZMod (7 ^ m))
      = ((x % 7 ^ m : ℕ) : ZMod _) := by
    rw [natCast_zmod_of_dvd hPN x, ← ZMod.natCast_mod]
  have hyy : ((y % 7 ^ (m + 1) : ℕ) : ZMod (7 ^ m))
      = ((y % 7 ^ m : ℕ) : ZMod _) := by
    rw [natCast_zmod_of_dvd hPN y, ← ZMod.natCast_mod]
  rw [hN0, add_zero, Nat.cast_mul, hyy, hxx] at hcast
  have hmod : (x % 7 ^ m) % 7 ^ m = (2 * (y % 7 ^ m)) % 7 ^ m := by
    have hz : ((x % 7 ^ m : ℕ) : ZMod (7 ^ m))
        = ((2 * (y % 7 ^ m) : ℕ) : ZMod _) := by
      push_cast
      linear_combination -hcast
    exact (ZMod.natCast_eq_natCast_iff' _ _ _).mp hz
  rwa [Nat.mod_eq_of_lt (Nat.mod_lt _ hP)] at hmod

/-- `Λ₁`-shifted elements keep the `mod-7^{m−1}` part. -/
private theorem multLow1_mod_low {m k x : ℕ} :
    (1 + k * 7 ^ (m - 1)) * x % 7 ^ (m - 1) = x % 7 ^ (m - 1) := by
  rw [add_mul, one_mul]
  have hdvd : k * 7 ^ (m - 1) * x = 7 ^ (m - 1) * (k * x) := by ring
  rw [hdvd, Nat.add_mul_mod_self_left]

/-- The corner `w = 4b + 2a` realizes `(σ₁, σ₂) = (a, b)` for all carry
parameters `cm, c2 ∈ {0,1}` — the 16-case enumeration. -/
private theorem sigma_eps_magic (cm c2 a b : ℕ)
    (hcm : cm < 2) (hc2 : c2 < 2) (ha : a < 2) (hb : b < 2) :
    (2 * (4 * b + 2 * a) + cm) / 7 = b ∧
    (2 * ((2 * (4 * b + 2 * a) + cm) % 7) + c2) / 7 = a := by
  interval_cases a <;> interval_cases b <;> interval_cases cm <;>
    interval_cases c2 <;> decide

/-- Single-`σ` corner: `w = 4a` realizes `σ = a` for all `cm ∈ {0,1}`. -/
private theorem sigma_single (cm a : ℕ) (hcm : cm < 2) (ha : a < 2) :
    (2 * (4 * a) + cm) / 7 = a := by
  interval_cases a <;> interval_cases cm <;> decide

/-- Negation normalization: a nonzero residue or its negative lies in
`{1,2,4}`. -/
private theorem neg_mem124 {r : ZMod 7} (hr : r ≠ 0) :
    r ∈ ({1, 2, 4} : Finset (ZMod 7))
      ∨ -r ∈ ({1, 2, 4} : Finset (ZMod 7)) := by
  have h : ∀ r : ZMod 7, r = 0 ∨ r ∈ ({1, 2, 4} : Finset (ZMod 7))
      ∨ -r ∈ ({1, 2, 4} : Finset (ZMod 7)) := by decide
  rcases h r with h0 | h1 | h2
  · exact absurd h0 hr
  · exact Or.inl h1
  · exact Or.inr h2

/-- §6.6(a): `r ∈ {1,2,3}` makes `(x,y)` safe for `x ∈ {r−1, r}`. -/
private theorem case66a_auto_dec : ∀ r x y : ZMod 7,
    r ∈ ({1, 2, 3} : Finset (ZMod 7)) →
      x ∈ ({r - 1, r} : Finset (ZMod 7)) → (x, y) ∉ bad66a := by
  decide

/-- §6.6(a): `r ∈ {4,5}`, `x ∈ {r−1,r}`, `y ∉ {2,4}` is safe. -/
private theorem case66a_safeA_dec : ∀ r x y : ZMod 7,
    r ∈ ({4, 5} : Finset (ZMod 7)) →
      x ∈ ({r - 1, r} : Finset (ZMod 7)) →
      y ∉ ({2, 4} : Finset (ZMod 7)) → (x, y) ∉ bad66a := by
  decide

/-- §6.6(a): `r ∈ {0,6}`, `x ∈ {r−1,r}`, `y ∉ {4,6}` is safe. -/
private theorem case66a_safeB_dec : ∀ r x y : ZMod 7,
    r ∈ ({0, 6} : Finset (ZMod 7)) →
      x ∈ ({r - 1, r} : Finset (ZMod 7)) →
      y ∉ ({4, 6} : Finset (ZMod 7)) → (x, y) ∉ bad66a := by
  decide

/-- §6.6(a): `x ∉ {4,5,6}` suffices. -/
private theorem case66a_notbad_x_dec : ∀ x y : ZMod 7,
    x ∉ ({4, 5, 6} : Finset (ZMod 7)) → (x, y) ∉ bad66a := by
  decide

/-- §6.6(b): `a ∈ {r−1, r}` with `r ∈ {0,1,6}` avoids `{2,4}`. -/
private theorem case66b_auto_dec : ∀ r a : ZMod 7,
    r ∈ ({0, 1, 6} : Finset (ZMod 7)) →
      a ∈ ({r - 1, r} : Finset (ZMod 7)) →
      a ∉ ({2, 4} : Finset (ZMod 7)) := by
  decide

/-- §6.6(b): `σ = 1` rescues `r ∈ {2,4}` (`a = r−1 ∈ {1,3}`). -/
private theorem case66b_sig1_dec : ∀ r a : ZMod 7,
    r ∈ ({2, 4} : Finset (ZMod 7)) → a = r - 1 →
      a ∉ ({2, 4} : Finset (ZMod 7)) := by
  decide

/-- §6.6(b): `σ = 0` rescues `r ∈ {3,5}` (`a = r`). -/
private theorem case66b_sig0_dec : ∀ r a : ZMod 7,
    r ∈ ({3, 5} : Finset (ZMod 7)) → a = r →
      a ∉ ({2, 4} : Finset (ZMod 7)) := by
  decide

/-- Explicit-`Λ` form of `lemma7_i`: for a `twoX` pair with
`0 < ν(e) < m`, a `Λ_{ν(e)}` element puts `ẽ` outside any
`apLen ≤ 4` set. -/
private theorem exists_multLow_etd7_avoid {m : ℕ} {d d' : ℕ}
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

/-! ### §5 The `ν = m` delicate branch: `case66a/b` finishers, then `case66_top`

The `case66a`/`case66b` finishers realize the finite `λ_k` models of
`case66a_bad`/`case66b_good` on concrete elements, producing `good7`
directly.  The `qdig ∈ {0,6}` route is mathematically unavailable here:
for pure-top pair residues `e = r·7^m` one has `q(e(λx,λy)) = r(λ)·r`,
so `{0,6}` membership forces `r(λ) = 6·r⁻¹` for *both* pairs, which only
works when `r12 = r34`. -/

/-- §6.6(a) finisher: with `e12 = 2·7^m`, `e34 = 7^m` and
`(ẽ(d2,d4), ẽ(d2,d5)) ∉ bad66a`, some `λ = λk·λ₀` is good — the
`{k,k+2, 2k−x, 2k−x+1, 4y+4k}` model. -/
private theorem case66a_finish {m : ℕ} (hm : 2 ≤ m)
    {d1 d2 d3 d4 d5 : ℕ}
    (hp1 : 0 < d1) (hp2 : 0 < d2) (hp3 : 0 < d3) (hp4 : 0 < d4) (hp5 : 0 < d5)
    (hu1 : padicValNat 7 d1 = 0) (hu2 : padicValNat 7 d2 = 0)
    (hu3 : padicValNat 7 d3 = 0) (hu4 : padicValNat 7 d4 = 0)
    (hu5 : padicValNat 7 d5 = 0)
    {s : ZMod 7} (hs0 : s ≠ 0)
    (h1 : runit7 d1 = s) (h2 : runit7 d2 = s)
    (h3 : runit7 d3 = 2 * s) (h4 : runit7 d4 = 2 * s) (h5 : runit7 d5 = 4 * s)
    (he12 : eMod7 m d1 d2 = 2 * 7 ^ m) (he34 : eMod7 m d3 d4 = 7 ^ m)
    {x y : ZMod 7} (hx : x = etd7 m d2 d4) (hy : y = etd7 m d2 d5)
    (hnb : (x, y) ∉ bad66a) :
    ∃ lam : ℕ, ¬ 7 ∣ lam ∧ good7 m lam ({d1, d2, d3, d4, d5} : Finset ℕ) := by
  classical
  obtain ⟨k, -, hkv⟩ :
      ∃ k ∈ ({1, 2, 3} : Finset (ZMod 7)),
        avoids06 ({k, k + 2, 2 * k - x, 2 * k - x + 1, 4 * y + 4 * k}
          : Finset (ZMod 7)) := by
    by_contra hcon
    push_neg at hcon
    exact hnb (case66a_bad hcon)
  have hr2 : runit7 d2 ≠ 0 := runit7_ne_zero hp2
  set K : ZMod 7 := -qdig7 m d2 * (runit7 d2)⁻¹ with hK
  have hKr : K * runit7 d2 = -qdig7 m d2 := by
    rw [hK, mul_assoc, inv_mul_cancel₀ hr2, mul_one]
  set jk : ZMod 7 := k * (runit7 d2)⁻¹ with hjk
  have hjkr : jk * runit7 d2 = k := by
    rw [hjk, mul_assoc, inv_mul_cancel₀ hr2, mul_one]
  set lam0 : ℕ := 1 + K.val * 7 ^ m with hlam0
  set lamk : ℕ := 1 + jk.val * 7 ^ m with hlamk
  have hlam0nd : ¬ 7 ∣ lam0 := multLow_not_dvd (by omega : 0 < m)
  have hlamknd : ¬ 7 ∣ lamk := multLow_not_dvd (by omega : 0 < m)
  have hlam0r : runit7 lam0 = 1 := runit7_multLow (by omega : 0 < m)
  -- `q(λ₀·d) = q(d) + K·r(d)`; `r(λ₀·d) = r(d)`; `ν(λ₀·d) = 0`
  have hq0 : ∀ d : ℕ, padicValNat 7 d = 0 →
      qdig7 m (lam0 * d) = qdig7 m d + K * runit7 d := by
    intro d hd
    rw [hlam0, qdig7_lambda0 hd, ZMod.natCast_zmod_val]
  have hν0 : ∀ d : ℕ, padicValNat 7 d = 0 → 0 < d →
      padicValNat 7 (lam0 * d) = 0 := by
    intro d hd hdp
    rw [padicValNat_mul_seven hlam0nd (ne_of_gt hdp), hd]
  have hr0 : ∀ d : ℕ, padicValNat 7 d = 0 →
      runit7 (lam0 * d) = runit7 d := by
    intro d hd
    rw [runit7_mul, hlam0r, one_mul]
  have hq : ∀ d : ℕ, padicValNat 7 d = 0 → 0 < d →
      qdig7 m (lamk * (lam0 * d)) = qdig7 m d + (K + jk) * runit7 d := by
    intro d hd hdp
    rw [hlamk, qdig7_lambda0 (hν0 d hd hdp), hq0 d hd, hr0 d hd,
      ZMod.natCast_zmod_val]
    push_cast
    ring
  -- pair-difference digits via σ-linkage (same-pairs have σ = 0)
  have hsame12 : residueRelOf d1 d2 = residueRel.same :=
    rel_same_of_eq (by rw [h1, h2]) (ne_of_gt hp2)
  have hsame34 : residueRelOf d3 d4 = residueRel.same :=
    rel_same_of_eq (by rw [h3, h4]) (ne_of_gt hp4)
  obtain ⟨hne21, hne12⟩ := (residueRelOf_eq_same).mp hsame12
  obtain ⟨hne43, hne34'⟩ := (residueRelOf_eq_same).mp hsame34
  have hEt12 : etd7 m d1 d2 = qdig7 m d1 - qdig7 m d2 := by
    unfold etd7
    rw [if_neg hne21, if_neg hne12]
  have hEt34 : etd7 m d3 d4 = qdig7 m d3 - qdig7 m d4 := by
    unfold etd7
    rw [if_neg hne43, if_neg hne34']
  have he12mod : eMod7 m d1 d2 % 7 ^ m = 0 := by
    rw [he12]
    exact Nat.mul_mod_left _ _
  have he34mod : eMod7 m d3 d4 % 7 ^ m = 0 := by
    rw [he34, Nat.mod_self]
  have hq12 : qdig7 m d1 - qdig7 m d2 = 2 := by
    rw [← hEt12, etd7_same_of_low hsame12 he12mod, he12,
      Nat.mul_div_cancel _ (Nat.pow_pos (by norm_num))]
    norm_num
  have hq34 : qdig7 m d3 - qdig7 m d4 = 1 := by
    rw [← hEt34, etd7_same_of_low hsame34 he34mod, he34,
      Nat.div_self (Nat.pow_pos (by norm_num))]
    norm_num
  -- cross-difference digits: `x = 2q₂−q₄` (twoX), `y = 2q₅−q₂` (twoY)
  have htx : x = 2 * qdig7 m d2 - qdig7 m d4 := by
    rw [hx]
    unfold etd7
    rw [if_pos (by rw [h4, h2] : runit7 d4 = 2 * runit7 d2)]
  have hne : runit7 d5 ≠ 2 * runit7 d2 := by
    rw [h5, h2]
    intro hcon
    have h2s : (2 : ZMod 7) * s = 0 := by linear_combination hcon
    have hs : s = 4 * (2 * s) := by
      rw [← mul_assoc, show (4 : ZMod 7) * 2 = 1 from by decide, one_mul]
    rw [h2s, mul_zero] at hs
    exact hs0 hs
  have hr25 : runit7 d2 = 2 * runit7 d5 := by
    rw [h2, h5, ← mul_assoc, show (2 : ZMod 7) * 4 = 1 from by decide, one_mul]
  have hty : y = 2 * qdig7 m d5 - qdig7 m d2 := by
    rw [hy]
    unfold etd7
    rw [if_neg hne, if_pos hr25]
  -- per-element evaluations
  rw [h2] at hKr hjkr
  have hK4 : K * (2 * s) = -2 * qdig7 m d2 := by
    linear_combination (2 : ZMod 7) * hKr
  have hjk4 : jk * (2 * s) = 2 * k := by
    linear_combination (2 : ZMod 7) * hjkr
  have hK5 : K * (4 * s) = -4 * qdig7 m d2 := by
    linear_combination (4 : ZMod 7) * hKr
  have hjk5 : jk * (4 * s) = 4 * k := by
    linear_combination (4 : ZMod 7) * hjkr
  have hq1v : qdig7 m d1 = qdig7 m d2 + 2 := by linear_combination hq12
  have hq4v : qdig7 m d4 = 2 * qdig7 m d2 - x := by linear_combination htx
  have hq3v : qdig7 m d3 = 2 * qdig7 m d2 - x + 1 := by
    linear_combination hq34 + hq4v
  have hq5v : qdig7 m d5 = 4 * (y + qdig7 m d2) := by
    have h2q5 : 2 * qdig7 m d5 = y + qdig7 m d2 := by
      linear_combination -hty
    have h4 : qdig7 m d5 = 4 * (2 * qdig7 m d5) := by
      rw [← mul_assoc, show (4 : ZMod 7) * 2 = 1 from by decide, one_mul]
    rw [h4, h2q5]
  have hq1f : qdig7 m (lamk * (lam0 * d1)) = k + 2 := by
    rw [hq d1 hu1 hp1, h1, add_mul, hKr, hjkr, hq1v]
    ring
  have hq2f : qdig7 m (lamk * (lam0 * d2)) = k := by
    rw [hq d2 hu2 hp2, h2, add_mul, hKr, hjkr]
    ring
  have hq3f : qdig7 m (lamk * (lam0 * d3)) = 2 * k - x + 1 := by
    rw [hq d3 hu3 hp3, h3, add_mul, hK4, hjk4, hq3v]
    ring
  have hq4f : qdig7 m (lamk * (lam0 * d4)) = 2 * k - x := by
    rw [hq d4 hu4 hp4, h4, add_mul, hK4, hjk4, hq4v]
    ring
  have hq5f : qdig7 m (lamk * (lam0 * d5)) = 4 * y + 4 * k := by
    rw [hq d5 hu5 hp5, h5, add_mul, hK5, hjk5, hq5v]
    ring
  refine ⟨lamk * lam0, Nat.Prime.not_dvd_mul Nat.prime_seven hlamknd hlam0nd,
    fun d hd => ?_⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl <;>
    rw [mul_assoc]
  · exact hkv _ (by rw [hq1f]; simp)
  · exact hkv _ (by rw [hq2f]; simp)
  · exact hkv _ (by rw [hq3f]; simp)
  · exact hkv _ (by rw [hq4f]; simp)
  · exact hkv _ (by rw [hq5f]; simp)

/-- §6.6(b) finisher: with `e12 = 7^m`, `e34 = 2·7^m` and
`ẽ(d2,d4) ∉ {2,4}`, some `λ = λk·λ₀` is good — the
`{k, k+2, 4x+4k, 4x+4k+1, 2k−y}` model anchored at `d4`. -/
private theorem case66b_finish {m : ℕ} (hm : 2 ≤ m)
    {d1 d2 d3 d4 d5 : ℕ}
    (hp1 : 0 < d1) (hp2 : 0 < d2) (hp3 : 0 < d3) (hp4 : 0 < d4) (hp5 : 0 < d5)
    (hu1 : padicValNat 7 d1 = 0) (hu2 : padicValNat 7 d2 = 0)
    (hu3 : padicValNat 7 d3 = 0) (hu4 : padicValNat 7 d4 = 0)
    (hu5 : padicValNat 7 d5 = 0)
    {s : ZMod 7} (hs0 : s ≠ 0)
    (h1 : runit7 d1 = s) (h2 : runit7 d2 = s)
    (h3 : runit7 d3 = 2 * s) (h4 : runit7 d4 = 2 * s) (h5 : runit7 d5 = 4 * s)
    (he12 : eMod7 m d1 d2 = 7 ^ m) (he34 : eMod7 m d3 d4 = 2 * 7 ^ m)
    {x y : ZMod 7} (hx : x = etd7 m d2 d4) (hy : y = etd7 m d4 d5)
    (ha : x ∉ ({2, 4} : Finset (ZMod 7))) :
    ∃ lam : ℕ, ¬ 7 ∣ lam ∧ good7 m lam ({d1, d2, d3, d4, d5} : Finset ℕ) := by
  classical
  obtain ⟨k, -, hkv⟩ := case66b_good (a := x) (b := y) ha
  have hr4 : runit7 d4 ≠ 0 := runit7_ne_zero hp4
  set K : ZMod 7 := -qdig7 m d4 * (runit7 d4)⁻¹ with hK
  have hKr : K * runit7 d4 = -qdig7 m d4 := by
    rw [hK, mul_assoc, inv_mul_cancel₀ hr4, mul_one]
  set jk : ZMod 7 := k * (runit7 d4)⁻¹ with hjk
  have hjkr : jk * runit7 d4 = k := by
    rw [hjk, mul_assoc, inv_mul_cancel₀ hr4, mul_one]
  set lam0 : ℕ := 1 + K.val * 7 ^ m with hlam0
  set lamk : ℕ := 1 + jk.val * 7 ^ m with hlamk
  have hlam0nd : ¬ 7 ∣ lam0 := multLow_not_dvd (by omega : 0 < m)
  have hlamknd : ¬ 7 ∣ lamk := multLow_not_dvd (by omega : 0 < m)
  have hlam0r : runit7 lam0 = 1 := runit7_multLow (by omega : 0 < m)
  have hq0 : ∀ d : ℕ, padicValNat 7 d = 0 →
      qdig7 m (lam0 * d) = qdig7 m d + K * runit7 d := by
    intro d hd
    rw [hlam0, qdig7_lambda0 hd, ZMod.natCast_zmod_val]
  have hν0 : ∀ d : ℕ, padicValNat 7 d = 0 → 0 < d →
      padicValNat 7 (lam0 * d) = 0 := by
    intro d hd hdp
    rw [padicValNat_mul_seven hlam0nd (ne_of_gt hdp), hd]
  have hr0 : ∀ d : ℕ, padicValNat 7 d = 0 →
      runit7 (lam0 * d) = runit7 d := by
    intro d hd
    rw [runit7_mul, hlam0r, one_mul]
  have hq : ∀ d : ℕ, padicValNat 7 d = 0 → 0 < d →
      qdig7 m (lamk * (lam0 * d)) = qdig7 m d + (K + jk) * runit7 d := by
    intro d hd hdp
    rw [hlamk, qdig7_lambda0 (hν0 d hd hdp), hq0 d hd, hr0 d hd,
      ZMod.natCast_zmod_val]
    push_cast
    ring
  -- pair-difference digits via σ-linkage (same-pairs have σ = 0)
  have hsame12 : residueRelOf d1 d2 = residueRel.same :=
    rel_same_of_eq (by rw [h1, h2]) (ne_of_gt hp2)
  have hsame34 : residueRelOf d3 d4 = residueRel.same :=
    rel_same_of_eq (by rw [h3, h4]) (ne_of_gt hp4)
  obtain ⟨hne21, hne12⟩ := (residueRelOf_eq_same).mp hsame12
  obtain ⟨hne43, hne34'⟩ := (residueRelOf_eq_same).mp hsame34
  have hEt12 : etd7 m d1 d2 = qdig7 m d1 - qdig7 m d2 := by
    unfold etd7
    rw [if_neg hne21, if_neg hne12]
  have hEt34 : etd7 m d3 d4 = qdig7 m d3 - qdig7 m d4 := by
    unfold etd7
    rw [if_neg hne43, if_neg hne34']
  have he12mod : eMod7 m d1 d2 % 7 ^ m = 0 := by
    rw [he12, Nat.mod_self]
  have he34mod : eMod7 m d3 d4 % 7 ^ m = 0 := by
    rw [he34]
    exact Nat.mul_mod_left _ _
  have hq12 : qdig7 m d1 - qdig7 m d2 = 1 := by
    rw [← hEt12, etd7_same_of_low hsame12 he12mod, he12,
      Nat.div_self (Nat.pow_pos (by norm_num))]
    norm_num
  have hq34 : qdig7 m d3 - qdig7 m d4 = 2 := by
    rw [← hEt34, etd7_same_of_low hsame34 he34mod, he34,
      Nat.mul_div_cancel _ (Nat.pow_pos (by norm_num))]
    norm_num
  -- cross-difference digits: `x = 2q₂−q₄` (twoX), `y = 2q₄−q₅` (twoX)
  have htx : x = 2 * qdig7 m d2 - qdig7 m d4 := by
    rw [hx]
    unfold etd7
    rw [if_pos (by rw [h4, h2] : runit7 d4 = 2 * runit7 d2)]
  have hty : y = 2 * qdig7 m d4 - qdig7 m d5 := by
    rw [hy]
    unfold etd7
    rw [if_pos (by rw [h5, h4]; ring : runit7 d5 = 2 * runit7 d4)]
  -- per-element evaluations (anchor `d4`, `r(d4) = 2s`)
  rw [h4] at hKr hjkr
  have h42 : (4 : ZMod 7) * 2 = 1 := by decide
  have hK2 : K * s = -4 * qdig7 m d4 := by
    have h2 : (2 : ZMod 7) * (K * s) = -qdig7 m d4 := by
      rw [← mul_left_comm]; exact hKr
    have h := congrArg (fun z : ZMod 7 => (4 : ZMod 7) * z) h2
    rw [← mul_assoc, h42, one_mul] at h
    rw [h]; ring
  have hjk2 : jk * s = 4 * k := by
    have h2 : (2 : ZMod 7) * (jk * s) = k := by
      rw [← mul_left_comm]; exact hjkr
    have h := congrArg (fun z : ZMod 7 => (4 : ZMod 7) * z) h2
    rwa [← mul_assoc, h42, one_mul] at h
  have hK5 : K * (4 * s) = -2 * qdig7 m d4 := by
    linear_combination (2 : ZMod 7) * hKr
  have hjk5 : jk * (4 * s) = 2 * k := by
    linear_combination (2 : ZMod 7) * hjkr
  have hq3v : qdig7 m d3 = qdig7 m d4 + 2 := by linear_combination hq34
  have hq2v : qdig7 m d2 = 4 * (x + qdig7 m d4) := by
    have h2 : (2 : ZMod 7) * qdig7 m d2 = x + qdig7 m d4 := by
      linear_combination -htx
    have h := congrArg (fun z : ZMod 7 => (4 : ZMod 7) * z) h2
    rwa [← mul_assoc, h42, one_mul] at h
  have hq1v : qdig7 m d1 = 4 * (x + qdig7 m d4) + 1 := by
    linear_combination hq12 + hq2v
  have hq5v : qdig7 m d5 = 2 * qdig7 m d4 - y := by
    linear_combination hty
  have hq4f : qdig7 m (lamk * (lam0 * d4)) = k := by
    rw [hq d4 hu4 hp4, h4, add_mul, hKr, hjkr]
    ring
  have hq3f : qdig7 m (lamk * (lam0 * d3)) = k + 2 := by
    rw [hq d3 hu3 hp3, h3, add_mul, hKr, hjkr, hq3v]
    ring
  have hq2f : qdig7 m (lamk * (lam0 * d2)) = 4 * x + 4 * k := by
    rw [hq d2 hu2 hp2, h2, add_mul, hK2, hjk2, hq2v]
    ring
  have hq1f : qdig7 m (lamk * (lam0 * d1)) = 4 * x + 4 * k + 1 := by
    rw [hq d1 hu1 hp1, h1, add_mul, hK2, hjk2, hq1v]
    ring
  have hq5f : qdig7 m (lamk * (lam0 * d5)) = 2 * k - y := by
    rw [hq d5 hu5 hp5, h5, add_mul, hK5, hjk5, hq5v]
    ring
  refine ⟨lamk * lam0, Nat.Prime.not_dvd_mul Nat.prime_seven hlamknd hlam0nd,
    fun d hd => ?_⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl <;>
    rw [mul_assoc]
  · exact hkv _ (by rw [hq1f]; simp)
  · exact hkv _ (by rw [hq2f]; simp)
  · exact hkv _ (by rw [hq3f]; simp)
  · exact hkv _ (by rw [hq4f]; simp)
  · exact hkv _ (by rw [hq5f]; simp)

/-- `twoY` symmetry: for `r(x) = 2r(y)` (and not vice versa),
`ẽ(x,y) = ẽ(y,x) = 2q(y) − q(x)`. -/
private theorem etd7_twoY_eq {m x y : ℕ}
    (h : runit7 x = 2 * runit7 y) (h' : runit7 y ≠ 2 * runit7 x) :
    etd7 m x y = etd7 m y x := by
  unfold etd7
  rw [if_neg h', if_pos h, if_pos h]

/-- `Λ₁` low-block decomposition (C63 clone): `(1+k·7^{m-1})·x mod 7^m`
keeps the lower `m−1` digits of `x` and puts
`(x_{m-1}+k·x₀) mod 7` in position `m−1`. -/
private theorem multLow1_lo {m k x : ℕ} (hm : 1 ≤ m) :
    (1 + k * 7 ^ (m - 1)) * x % 7 ^ m
      = x % 7 ^ (m - 1) +
        ((x / 7 ^ (m - 1)) % 7 + k * (x % 7)) % 7 * 7 ^ (m - 1) := by
  have hm1 : 7 ^ m = 7 ^ (m - 1) * 7 := by
    rw [← pow_succ]; congr 1; omega
  have hP : (0 : ℕ) < 7 ^ (m - 1) := Nat.pow_pos (by norm_num)
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
      have h := ((Nat.mod_modEq ((x / 7 ^ (m - 1)) % 7 + k * (x % 7)) 7).symm).mul_left'
        (7 ^ (m - 1))
      rwa [mul_comm (7 ^ (m - 1))
          (((x / 7 ^ (m - 1)) % 7 + k * (x % 7)) % 7),
        mul_comm (7 ^ (m - 1)) ((x / 7 ^ (m - 1)) % 7 + k * (x % 7))] at h
    exact step1.trans ((Nat.ModEq.refl _).add e6)
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

/-- The `m−1` digit of a `Λ₁`-shift is `q(λ·7x)`: casting bridge via
`mod_mul_div`. -/
private theorem multLow1_mid_eq {m k x : ℕ} (hm : 1 ≤ m) :
    (((1 + k * 7 ^ (m - 1)) * x) % 7 ^ m) / 7 ^ (m - 1)
      = (((1 + k * 7 ^ (m - 1)) * x) / 7 ^ (m - 1)) % 7 := by
  have hm1 : 7 ^ m = 7 ^ (m - 1) * 7 := by
    rw [← pow_succ]; congr 1; omega
  rw [hm1]
  exact mod_mul_div (Nat.pow_pos (by norm_num)) (by norm_num)

/-- §6.6(b): every `p` admits `ε ∈ {0,1}` with `p − ε ∉ {2,4}`. -/
private theorem case66b_eps_dec : ∀ p : ZMod 7,
    ∃ ε : ZMod 7, ε ∈ ({0, 1} : Finset (ZMod 7)) ∧
      p - ε ∉ ({2, 4} : Finset (ZMod 7)) := by
  decide

/-- §6.6(a): `apLen` bounds for the avoid-sets. -/
private theorem case66a_apLen456 : apLen ({4, 5, 6} : Finset (ZMod 7)) ≤ 4 := by
  decide

private theorem case66a_apLen24 : apLen ({2, 4} : Finset (ZMod 7)) ≤ 4 := by
  decide

private theorem case66a_apLen46 : apLen ({4, 6} : Finset (ZMod 7)) ≤ 4 := by
  decide

/-- `ν(e) < m` from `e % 7^m ≠ 0` (with `e < 7^{m+1}`). -/
private theorem padic_lt_of_mod_ne {m e : ℕ} (he0 : e ≠ 0)
    (hlt : e < 7 ^ (m + 1)) (hmod : e % 7 ^ m ≠ 0) :
    padicValNat 7 e < m := by
  have hle := padic_le_of_lt he0 hlt
  by_contra hcon
  push_neg at hcon
  have hdvd : 7 ^ m ∣ e :=
    (Nat.pow_dvd_iff_le_padicValNat (by norm_num) he0).mpr (by omega)
  exact hmod (Nat.dvd_iff_mod_eq_zero.mp hdvd)

/-- Variant of `exists_multLow_etd7_avoid` keyed on `e ≠ 0` and `ν(e) < m`
instead of the explicit valuation hypothesis (for `lemma7_i` dispatch). -/
private theorem exists_multLow_etd7_avoid' {m : ℕ} {d d' : ℕ}
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

/-- §6.6(a) reduction: a `Λ_j`-shift (`j < m`) preserves the normalized
top residues and unit classes, so any `bad66a`-free shifted `(x,y)`
reduces to `case66a_finish`. -/
private theorem case66a_red {m : ℕ} (hm : 2 ≤ m)
    {d1 d2 d3 d4 d5 : ℕ}
    (hp1 : 0 < d1) (hp2 : 0 < d2) (hp3 : 0 < d3) (hp4 : 0 < d4) (hp5 : 0 < d5)
    (hu1 : padicValNat 7 d1 = 0) (hu2 : padicValNat 7 d2 = 0)
    (hu3 : padicValNat 7 d3 = 0) (hu4 : padicValNat 7 d4 = 0)
    (hu5 : padicValNat 7 d5 = 0)
    {s : ZMod 7} (hs0 : s ≠ 0)
    (h1 : runit7 d1 = s) (h2 : runit7 d2 = s)
    (h3 : runit7 d3 = 2 * s) (h4 : runit7 d4 = 2 * s) (h5 : runit7 d5 = 4 * s)
    (he12 : eMod7 m d1 d2 = 2 * 7 ^ m) (he34 : eMod7 m d3 d4 = 7 ^ m)
    {k j : ℕ} (hjm : j < m)
    (hnb : (etd7 m ((1 + k * 7 ^ (m - j)) * d2) ((1 + k * 7 ^ (m - j)) * d4),
            etd7 m ((1 + k * 7 ^ (m - j)) * d2) ((1 + k * 7 ^ (m - j)) * d5))
            ∉ bad66a) :
    ∃ lam : ℕ, ¬ 7 ∣ lam ∧ good7 m lam ({d1, d2, d3, d4, d5} : Finset ℕ) := by
  set lam' := 1 + k * 7 ^ (m - j) with hlam'
  have hlam'nd : ¬ 7 ∣ lam' := multLow_not_dvd hjm
  have hlam'pos : 0 < lam' := by rw [hlam']; positivity
  have hlam'r : runit7 lam' = 1 := runit7_multLow hjm
  have hpos : ∀ d : ℕ, 0 < d → 0 < lam' * d := fun _ hd =>
    Nat.mul_pos hlam'pos hd
  have hu : ∀ d : ℕ, d ≠ 0 → padicValNat 7 d = 0 →
      padicValNat 7 (lam' * d) = 0 := fun _ hd0 hd => by
    rw [padicValNat_mul_seven hlam'nd hd0, hd]
  have hr : ∀ d : ℕ, runit7 (lam' * d) = runit7 d := fun _ => by
    rw [runit7_mul, hlam'r, one_mul]
  have he12' : eMod7 m (lam' * d1) (lam' * d2) = 2 * 7 ^ m := by
    rw [eMod7_mul hlam'r, he12, hlam']
    exact lambda_low_top_resid hjm (by norm_num : (2 : ℕ) < 7)
  have he34' : eMod7 m (lam' * d3) (lam' * d4) = 7 ^ m := by
    rw [eMod7_mul hlam'r, he34, hlam', ← one_mul (7 ^ m)]
    exact lambda_low_top_resid hjm (show (1 : ℕ) < 7 by norm_num)
  obtain ⟨lam2, hl2nd, hgood⟩ := case66a_finish hm
    (hpos _ hp1) (hpos _ hp2) (hpos _ hp3) (hpos _ hp4) (hpos _ hp5)
    (hu _ (ne_of_gt hp1) hu1) (hu _ (ne_of_gt hp2) hu2)
    (hu _ (ne_of_gt hp3) hu3) (hu _ (ne_of_gt hp4) hu4)
    (hu _ (ne_of_gt hp5) hu5)
    hs0 (by rw [hr, h1]) (by rw [hr, h2]) (by rw [hr, h3]) (by rw [hr, h4])
    (by rw [hr, h5]) he12' he34' rfl rfl hnb
  have himg : ({d1, d2, d3, d4, d5} : Finset ℕ).image (lam' * ·)
      = {lam' * d1, lam' * d2, lam' * d3, lam' * d4, lam' * d5} := by
    simp only [Finset.image_insert, Finset.image_singleton]
  rw [← himg] at hgood
  exact ⟨lam2 * lam', Nat.Prime.not_dvd_mul Nat.prime_seven hl2nd hlam'nd,
    good7_mul hgood⟩

/-- §6.6(b) reduction: the analogous `Λ_j`-shift reduction to
`case66b_finish`, needing only `x' ∉ {2,4}`. -/
private theorem case66b_red {m : ℕ} (hm : 2 ≤ m)
    {d1 d2 d3 d4 d5 : ℕ}
    (hp1 : 0 < d1) (hp2 : 0 < d2) (hp3 : 0 < d3) (hp4 : 0 < d4) (hp5 : 0 < d5)
    (hu1 : padicValNat 7 d1 = 0) (hu2 : padicValNat 7 d2 = 0)
    (hu3 : padicValNat 7 d3 = 0) (hu4 : padicValNat 7 d4 = 0)
    (hu5 : padicValNat 7 d5 = 0)
    {s : ZMod 7} (hs0 : s ≠ 0)
    (h1 : runit7 d1 = s) (h2 : runit7 d2 = s)
    (h3 : runit7 d3 = 2 * s) (h4 : runit7 d4 = 2 * s) (h5 : runit7 d5 = 4 * s)
    (he12 : eMod7 m d1 d2 = 7 ^ m) (he34 : eMod7 m d3 d4 = 2 * 7 ^ m)
    {k j : ℕ} (hjm : j < m)
    (ha : etd7 m ((1 + k * 7 ^ (m - j)) * d2) ((1 + k * 7 ^ (m - j)) * d4)
            ∉ ({2, 4} : Finset (ZMod 7))) :
    ∃ lam : ℕ, ¬ 7 ∣ lam ∧ good7 m lam ({d1, d2, d3, d4, d5} : Finset ℕ) := by
  set lam' := 1 + k * 7 ^ (m - j) with hlam'
  have hlam'nd : ¬ 7 ∣ lam' := multLow_not_dvd hjm
  have hlam'pos : 0 < lam' := by rw [hlam']; positivity
  have hlam'r : runit7 lam' = 1 := runit7_multLow hjm
  have hpos : ∀ d : ℕ, 0 < d → 0 < lam' * d := fun _ hd =>
    Nat.mul_pos hlam'pos hd
  have hu : ∀ d : ℕ, d ≠ 0 → padicValNat 7 d = 0 →
      padicValNat 7 (lam' * d) = 0 := fun _ hd0 hd => by
    rw [padicValNat_mul_seven hlam'nd hd0, hd]
  have hr : ∀ d : ℕ, runit7 (lam' * d) = runit7 d := fun _ => by
    rw [runit7_mul, hlam'r, one_mul]
  have he12' : eMod7 m (lam' * d1) (lam' * d2) = 7 ^ m := by
    rw [eMod7_mul hlam'r, he12, hlam', ← one_mul (7 ^ m)]
    exact lambda_low_top_resid hjm (show (1 : ℕ) < 7 by norm_num)
  have he34' : eMod7 m (lam' * d3) (lam' * d4) = 2 * 7 ^ m := by
    rw [eMod7_mul hlam'r, he34, hlam']
    exact lambda_low_top_resid hjm (by norm_num : (2 : ℕ) < 7)
  obtain ⟨lam2, hl2nd, hgood⟩ := case66b_finish hm
    (hpos _ hp1) (hpos _ hp2) (hpos _ hp3) (hpos _ hp4) (hpos _ hp5)
    (hu _ (ne_of_gt hp1) hu1) (hu _ (ne_of_gt hp2) hu2)
    (hu _ (ne_of_gt hp3) hu3) (hu _ (ne_of_gt hp4) hu4)
    (hu _ (ne_of_gt hp5) hu5)
    hs0 (by rw [hr, h1]) (by rw [hr, h2]) (by rw [hr, h3]) (by rw [hr, h4])
    (by rw [hr, h5]) he12' he34' rfl rfl ha
  have himg : ({d1, d2, d3, d4, d5} : Finset ℕ).image (lam' * ·)
      = {lam' * d1, lam' * d2, lam' * d3, lam' * d4, lam' * d5} := by
    simp only [Finset.image_insert, Finset.image_singleton]
  rw [← himg] at hgood
  exact ⟨lam2 * lam', Nat.Prime.not_dvd_mul Nat.prime_seven hl2nd hlam'nd,
    good7_mul hgood⟩

private theorem zmod7_split_a : ∀ r : ZMod 7,
    r ∈ ({1, 2, 3} : Finset (ZMod 7)) ∨
      r ∈ ({4, 5} : Finset (ZMod 7)) ∨ r ∈ ({0, 6} : Finset (ZMod 7)) := by
  decide

private theorem zmod7_split_b : ∀ r : ZMod 7,
    r ∈ ({0, 1, 6} : Finset (ZMod 7)) ∨
      r ∈ ({2, 4} : Finset (ZMod 7)) ∨ r ∈ ({3, 5} : Finset (ZMod 7)) := by
  decide

private theorem zmod7_ratio124 : ∀ a b : ZMod 7,
    a ∈ ({1, 2, 4} : Finset (ZMod 7)) →
      b ∈ ({1, 2, 4} : Finset (ZMod 7)) →
        a = b ∨ a = 2 * b ∨ b = 2 * a := by
  decide

private theorem etd7_twoX_mem {m x y : ℕ}
    (hrel : runit7 y = 2 * runit7 x)
    (hlow : eMod7 m x y % 7 ^ m = 0) :
    etd7 m x y ∈
      ({((eMod7 m x y / 7 ^ m : ℕ) : ZMod 7) - 1,
        ((eMod7 m x y / 7 ^ m : ℕ) : ZMod 7)} : Finset (ZMod 7)) := by
  have hP : 0 < 7 ^ m := Nat.pow_pos (by norm_num)
  set sigma := 2 * (x % 7 ^ m) / 7 ^ m with hsigma
  have hsigma_lt : sigma < 2 := by
    rw [hsigma]
    apply Nat.div_lt_of_lt_mul
    have hxlt := Nat.mod_lt x hP
    omega
  have hsigma_cases : sigma = 0 ∨ sigma = 1 :=
    Nat.le_one_iff_eq_zero_or_eq_one.mp (by omega)
  rw [etd7_twoX_of_low hrel hlow, ← hsigma]
  rcases hsigma_cases with hzero | hone
  · rw [hzero]
    simp
  · rw [hone]
    simp

private theorem eMod7_multLow_top {m j k x y : ℕ} (hjm : j < m)
    (hlow : eMod7 m x y % 7 ^ m = 0) :
    eMod7 m ((1 + k * 7 ^ (m - j)) * x)
        ((1 + k * 7 ^ (m - j)) * y) = eMod7 m x y := by
  have hP : 0 < 7 ^ m := Nat.pow_pos (by norm_num)
  have hN : 0 < 7 ^ (m + 1) := Nat.pow_pos (by norm_num)
  have he_lt := eMod7_lt m x y
  have he_eq : eMod7 m x y = (eMod7 m x y / 7 ^ m) * 7 ^ m := by
    have hdiv := Nat.div_add_mod (eMod7 m x y) (7 ^ m)
    rw [hlow, add_zero] at hdiv
    simpa [mul_comm] using hdiv.symm
  have ht : eMod7 m x y / 7 ^ m < 7 := by
    rw [Nat.div_lt_iff_lt_mul hP]
    simpa [pow_succ'] using he_lt
  rw [eMod7_mul (runit7_multLow hjm), he_eq]
  exact lambda_low_top_resid hjm ht

private theorem etd7_multLow_top_mem {m j k x y : ℕ} (hjm : j < m)
    (hrel : runit7 y = 2 * runit7 x)
    (hlow : eMod7 m x y % 7 ^ m = 0) :
    etd7 m ((1 + k * 7 ^ (m - j)) * x)
        ((1 + k * 7 ^ (m - j)) * y) ∈
      ({((eMod7 m x y / 7 ^ m : ℕ) : ZMod 7) - 1,
        ((eMod7 m x y / 7 ^ m : ℕ) : ZMod 7)} : Finset (ZMod 7)) := by
  have hlamr := runit7_multLow (k := k) hjm
  have hrel' : runit7 ((1 + k * 7 ^ (m - j)) * y) =
      2 * runit7 ((1 + k * 7 ^ (m - j)) * x) := by
    rw [runit7_mul, runit7_mul, hlamr, one_mul, one_mul, hrel]
  have heq := eMod7_multLow_top (k := k) hjm hlow
  have hlow' : eMod7 m ((1 + k * 7 ^ (m - j)) * x)
        ((1 + k * 7 ^ (m - j)) * y) % 7 ^ m = 0 := by
    rw [heq, hlow]
  simpa [heq] using etd7_twoX_mem hrel' hlow'

private theorem exists_multLow1_set_mid {m d w : ℕ} (hm : 1 ≤ m)
    (hd : padicValNat 7 d = 0) (hd0 : 0 < d) (hw : w < 7) :
    ∃ k : ℕ, k < 7 ∧
      ((1 + k * 7 ^ (m - 1)) * d % 7 ^ m) / 7 ^ (m - 1) = w := by
  obtain ⟨k, hk7, hq⟩ := exists_multLow_one_set_seven'
    (by omega : 0 < m) hd hd0 (w : ZMod 7)
  refine ⟨k, hk7, ?_⟩
  have hq' : qdig7 m (7 * ((1 + k * 7 ^ (m - 1)) * d)) = (w : ZMod 7) := by
    rw [show 7 * ((1 + k * 7 ^ (m - 1)) * d) =
      (1 + k * 7 ^ (m - 1)) * (7 * d) by ring]
    exact hq
  rw [qdig7_seven m _ (by omega : 0 < m)] at hq'
  rw [multLow1_mid_eq hm]
  unfold digit7 at hq'
  have hval := congrArg ZMod.val hq'
  rw [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_mod, Nat.mod_eq_of_lt hw] at hval
  exact hval

private theorem sigma_multLow1 {m k x W : ℕ} (hm : 1 ≤ m)
    (hW : ((1 + k * 7 ^ (m - 1)) * x % 7 ^ m) / 7 ^ (m - 1) = W) :
    2 * ((1 + k * 7 ^ (m - 1)) * x % 7 ^ m) / 7 ^ m =
      (2 * W + 2 * (x % 7 ^ (m - 1)) / 7 ^ (m - 1)) / 7 := by
  set W0 := ((x / 7 ^ (m - 1)) % 7 + k * (x % 7)) % 7 with hW0
  have hu : x % 7 ^ (m - 1) < 7 ^ (m - 1) :=
    Nat.mod_lt _ (Nat.pow_pos (by norm_num))
  have hW0lt : W0 < 7 := by
    rw [hW0]
    exact Nat.mod_lt _ (by norm_num)
  have hdecomp := multLow1_lo (x := x) (k := k) hm
  rw [← hW0] at hdecomp
  have hdiv : (x % 7 ^ (m - 1) + W0 * 7 ^ (m - 1)) / 7 ^ (m - 1) = W0 := by
    rw [Nat.add_mul_div_right _ _ (Nat.pow_pos (by norm_num)),
      Nat.div_eq_of_lt hu, zero_add]
  have hWW0 : W = W0 := by
    rw [hdecomp, hdiv] at hW
    exact hW.symm
  rw [hWW0, hdecomp, add_comm]
  exact two_mul_low_div hm hW0lt hu

private theorem case66_sigma_force {m d d' : ℕ} (hm : 2 ≤ m)
    (hd : padicValNat 7 d = 0) (hd0 : 0 < d)
    (hrel : runit7 d' = 2 * runit7 d)
    (hlow : eMod7 m d d' % 7 ^ m = 0)
    {eps : ZMod 7} (heps : eps ∈ ({0, 1} : Finset (ZMod 7))) :
    ∃ k : ℕ, k < 7 ∧
      etd7 m ((1 + k * 7 ^ (m - 1)) * d)
        ((1 + k * 7 ^ (m - 1)) * d') =
          ((eMod7 m d d' / 7 ^ m : ℕ) : ZMod 7) - eps := by
  have heps_val : eps.val < 2 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at heps
    rcases heps with rfl | rfl <;> decide
  obtain ⟨k, hk7, hW⟩ := exists_multLow1_set_mid (m := m) (by omega : 1 ≤ m) hd hd0
    (by omega : 4 * eps.val < 7)
  refine ⟨k, hk7, ?_⟩
  have h1m : 1 < m := by omega
  have heq := eMod7_multLow_top (x := d) (y := d') (k := k) h1m hlow
  have hlow' : eMod7 m ((1 + k * 7 ^ (m - 1)) * d)
        ((1 + k * 7 ^ (m - 1)) * d') % 7 ^ m = 0 := by
    rw [heq, hlow]
  have hlamr := runit7_multLow (k := k) h1m
  have hrel' : runit7 ((1 + k * 7 ^ (m - 1)) * d') =
      2 * runit7 ((1 + k * 7 ^ (m - 1)) * d) := by
    rw [runit7_mul, runit7_mul, hlamr, one_mul, one_mul, hrel]
  have hcm : 2 * (d % 7 ^ (m - 1)) / 7 ^ (m - 1) < 2 := by
    apply Nat.div_lt_of_lt_mul
    have hlt := Nat.mod_lt d (Nat.pow_pos (by norm_num) : 0 < 7 ^ (m - 1))
    omega
  have hsig : 2 * (((1 + k * 7 ^ (m - 1)) * d) % 7 ^ m) / 7 ^ m = eps.val := by
    rw [sigma_multLow1 (by omega : 1 ≤ m) hW]
    exact sigma_single _ _ hcm heps_val
  rw [etd7_twoX_of_low hrel' hlow', heq, hsig, ZMod.natCast_zmod_val]

private theorem double_low_mod {P w u : ℕ} (hP : 0 < P)
    (hw : w < 7) (hu : u < P) :
    (2 * (w * P + u)) % (P * 7) =
      (2 * u) % P + ((2 * w + 2 * u / P) % 7) * P := by
  set cm := 2 * u / P with hcm
  set u2 := (2 * u) % P with hu2
  set W2 := (2 * w + cm) % 7 with hW2
  set Q := (2 * w + cm) / 7 with hQ
  have h2u : 2 * u = u2 + P * cm := by
    rw [hcm, hu2]
    exact (Nat.mod_add_div (2 * u) P).symm
  have hA : 2 * w + cm = W2 + 7 * Q := by
    rw [hW2, hQ]
    exact (Nat.mod_add_div (2 * w + cm) 7).symm
  have hexp : 2 * (w * P + u) =
      (u2 + W2 * P) + (P * 7) * Q := by
    calc
      2 * (w * P + u) = 2 * w * P + 2 * u := by ring
      _ = u2 + (2 * w + cm) * P := by rw [h2u]; ring
      _ = u2 + (W2 + 7 * Q) * P := by rw [hA]
      _ = (u2 + W2 * P) + (P * 7) * Q := by ring
  have hu2lt : u2 < P := by rw [hu2]; exact Nat.mod_lt _ hP
  have hW2lt : W2 < 7 := by rw [hW2]; exact Nat.mod_lt _ (by norm_num)
  have hbase : u2 + W2 * P < P * 7 := by
    nlinarith
  rw [hexp, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hbase, hu2, hW2, hcm]

private theorem case66a_corner {m d2 d4 d5 : ℕ} (hm : 2 ≤ m)
    (hd5 : padicValNat 7 d5 = 0) (hd5pos : 0 < d5)
    (hrel24 : runit7 d4 = 2 * runit7 d2)
    (hrel25 : runit7 d2 = 2 * runit7 d5)
    (hrel25' : runit7 d5 ≠ 2 * runit7 d2)
    (hlow24 : eMod7 m d2 d4 % 7 ^ m = 0)
    (hlow25 : eMod7 m d2 d5 % 7 ^ m = 0)
    {eps1 eps2 : ZMod 7}
    (heps1 : eps1 ∈ ({0, 1} : Finset (ZMod 7)))
    (heps2 : eps2 ∈ ({0, 1} : Finset (ZMod 7)))
    (hnb : (((eMod7 m d2 d4 / 7 ^ m : ℕ) : ZMod 7) - eps1,
      ((eMod7 m d2 d5 / 7 ^ m : ℕ) : ZMod 7) - eps2) ∉ bad66a) :
    ∃ k : ℕ, k < 7 ∧
      (etd7 m ((1 + k * 7 ^ (m - 1)) * d2)
          ((1 + k * 7 ^ (m - 1)) * d4),
       etd7 m ((1 + k * 7 ^ (m - 1)) * d2)
          ((1 + k * 7 ^ (m - 1)) * d5)) ∉ bad66a := by
  have heps1val : eps1.val < 2 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at heps1
    rcases heps1 with rfl | rfl <;> decide
  have heps2val : eps2.val < 2 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at heps2
    rcases heps2 with rfl | rfl <;> decide
  set w := 4 * eps2.val + 2 * eps1.val with hw
  have hw7 : w < 7 := by rw [hw]; omega
  obtain ⟨k, hk7, hW5⟩ := exists_multLow1_set_mid (m := m)
    (by omega : 1 ≤ m) hd5 hd5pos hw7
  refine ⟨k, hk7, ?_⟩
  set lam := 1 + k * 7 ^ (m - 1) with hlam
  have h1m : 1 < m := by omega
  have hlamr : runit7 lam = 1 := by rw [hlam]; exact runit7_multLow h1m
  have hrel24s : runit7 (lam * d4) = 2 * runit7 (lam * d2) := by
    rw [runit7_mul, runit7_mul, hlamr, one_mul, one_mul, hrel24]
  have hrel25s : runit7 (lam * d2) = 2 * runit7 (lam * d5) := by
    rw [runit7_mul, runit7_mul, hlamr, one_mul, one_mul, hrel25]
  have hrel25s' : runit7 (lam * d5) ≠ 2 * runit7 (lam * d2) := by
    rw [runit7_mul, runit7_mul, hlamr, one_mul, one_mul]
    exact hrel25'
  have heq24 := eMod7_multLow_top (x := d2) (y := d4) (k := k) h1m hlow24
  have heq25 := eMod7_multLow_top (x := d2) (y := d5) (k := k) h1m hlow25
  have hlow24s : eMod7 m (lam * d2) (lam * d4) % 7 ^ m = 0 := by
    rw [heq24, hlow24]
  have hlow25s : eMod7 m (lam * d2) (lam * d5) % 7 ^ m = 0 := by
    rw [heq25, hlow25]
  set P := 7 ^ (m - 1) with hP
  set u5 := d5 % P with hu5
  set cm5 := 2 * u5 / P with hcm5
  set u2 := (2 * u5) % P with hu2
  set W2 := (2 * w + cm5) % 7 with hW2
  set c2 := 2 * u2 / P with hc2
  have hPpos : 0 < P := by rw [hP]; positivity
  have hu5lt : u5 < P := by rw [hu5]; exact Nat.mod_lt _ hPpos
  have hcm5lt : cm5 < 2 := by
    rw [hcm5]
    apply Nat.div_lt_of_lt_mul
    omega
  have hu2lt : u2 < P := by rw [hu2]; exact Nat.mod_lt _ hPpos
  have hc2lt : c2 < 2 := by
    rw [hc2]
    apply Nat.div_lt_of_lt_mul
    omega
  have hW2lt : W2 < 7 := by rw [hW2]; exact Nat.mod_lt _ (by norm_num)
  have hmagic := sigma_eps_magic cm5 c2 eps1.val eps2.val
    hcm5lt hc2lt heps1val heps2val
  have hsig5 : 2 * ((lam * d5) % 7 ^ m) / 7 ^ m = eps2.val := by
    rw [hlam, sigma_multLow1 (by omega : 1 ≤ m) hW5, hw,
      ← hP, ← hu5, ← hcm5]
    exact hmagic.1
  have hW5' : ((lam * d5) % 7 ^ m) / P = w := by
    simpa [lam, P] using hW5
  have hlow5' : ((lam * d5) % 7 ^ m) % P = u5 := by
    calc
      ((lam * d5) % 7 ^ m) % P = (lam * d5) % P :=
        Nat.mod_mod_of_dvd _ (by rw [hP]; exact Nat.pow_dvd_pow 7 (by omega))
      _ = d5 % P := by simpa [lam, P] using (multLow1_mod_low (m := m) (k := k) (x := d5))
      _ = u5 := hu5.symm
  have hL5 : (lam * d5) % 7 ^ m = w * P + u5 := by
    calc
      (lam * d5) % 7 ^ m = P * (((lam * d5) % 7 ^ m) / P) +
          ((lam * d5) % 7 ^ m) % P := (Nat.div_add_mod _ P).symm
      _ = w * P + u5 := by rw [hW5', hlow5']; ring
  have hlink25 := low_link_twoY hrel25s hrel25s' hlow25s
  have hPm : 7 ^ m = P * 7 := by
    rw [hP, ← pow_succ]
    congr 1
    omega
  have hL2 : (lam * d2) % 7 ^ m = u2 + W2 * P := by
    rw [hlink25, hL5, hPm]
    simpa [hu2, hW2, hcm5] using double_low_mod hPpos hw7 hu5lt
  have hsig2 : 2 * ((lam * d2) % 7 ^ m) / 7 ^ m = eps1.val := by
    rw [hL2, add_comm, hP, two_mul_low_div (by omega : 1 ≤ m) hW2lt hu2lt,
      ← hc2, hW2]
    exact hmagic.2
  have hx : etd7 m (lam * d2) (lam * d4) =
      ((eMod7 m d2 d4 / 7 ^ m : ℕ) : ZMod 7) - eps1 := by
    rw [etd7_twoX_of_low hrel24s hlow24s, heq24, hsig2,
      ZMod.natCast_zmod_val]
  have hy : etd7 m (lam * d2) (lam * d5) =
      ((eMod7 m d2 d5 / 7 ^ m : ℕ) : ZMod 7) - eps2 := by
    rw [etd7_twoY_of_low hrel25s hrel25s' hlow25s, heq25, hsig5,
      ZMod.natCast_zmod_val]
  rwa [hlam, hx, hy]

private theorem case66b_go {m : ℕ} (hm : 2 ≤ m)
    {d1 d2 d3 d4 d5 : ℕ}
    (hp1 : 0 < d1) (hp2 : 0 < d2) (hp3 : 0 < d3) (hp4 : 0 < d4) (hp5 : 0 < d5)
    (hu1 : padicValNat 7 d1 = 0) (hu2 : padicValNat 7 d2 = 0)
    (hu3 : padicValNat 7 d3 = 0) (hu4 : padicValNat 7 d4 = 0)
    (hu5 : padicValNat 7 d5 = 0)
    {s : ZMod 7} (hs0 : s ≠ 0)
    (h1 : runit7 d1 = s) (h2 : runit7 d2 = s)
    (h3 : runit7 d3 = 2 * s) (h4 : runit7 d4 = 2 * s) (h5 : runit7 d5 = 4 * s)
    (he12 : eMod7 m d1 d2 = 7 ^ m) (he34 : eMod7 m d3 d4 = 2 * 7 ^ m) :
    ∃ lam : ℕ, ¬ 7 ∣ lam ∧ good7 m lam ({d1, d2, d3, d4, d5} : Finset ℕ) := by
  have hrel24 : runit7 d4 = 2 * runit7 d2 := by rw [h4, h2]
  set e24 := eMod7 m d2 d4 with he24
  by_cases he0 : e24 = 0
  · have hlow : eMod7 m d2 d4 % 7 ^ m = 0 := by rw [← he24, he0]; simp
    have hx := etd7_twoX_mem hrel24 hlow
    have hx' : etd7 m d2 d4 ∈ ({(0 : ZMod 7) - 1, 0} : Finset (ZMod 7)) := by
      simpa [← he24, he0] using hx
    have ha := case66b_auto_dec (0 : ZMod 7) (etd7 m d2 d4) (by decide) hx'
    exact case66b_red hm hp1 hp2 hp3 hp4 hp5 hu1 hu2 hu3 hu4 hu5 hs0
      h1 h2 h3 h4 h5 he12 he34 (k := 0) (j := 0) (by omega) (by simpa using ha)
  · by_cases hlow : eMod7 m d2 d4 % 7 ^ m = 0
    · obtain ⟨eps, heps, hsafe⟩ :=
        case66b_eps_dec (((eMod7 m d2 d4 / 7 ^ m : ℕ) : ZMod 7))
      obtain ⟨k, hk7, hsig⟩ := case66_sigma_force hm hu2 hp2 hrel24 hlow heps
      apply case66b_red hm hp1 hp2 hp3 hp4 hp5 hu1 hu2 hu3 hu4 hu5 hs0
        h1 h2 h3 h4 h5 he12 he34 (k := k) (j := 1) (by omega)
      rw [hsig]
      exact hsafe
    · have hνm : padicValNat 7 (eMod7 m d2 d4) < m :=
        padic_lt_of_mod_ne (by rwa [← he24]) (eMod7_lt _ _ _) hlow
      obtain ⟨k, hk7, havoid⟩ := exists_multLow_etd7_avoid'
        hu2 hu4 hp2 hp4 hrel24 (by rwa [← he24]) hνm case66a_apLen24
      exact case66b_red hm hp1 hp2 hp3 hp4 hp5 hu1 hu2 hu3 hu4 hu5 hs0
        h1 h2 h3 h4 h5 he12 he34 (k := k)
        (j := padicValNat 7 (eMod7 m d2 d4)) hνm havoid

private theorem case66a_go {m : ℕ} (hm : 2 ≤ m)
    {d1 d2 d3 d4 d5 : ℕ}
    (hp1 : 0 < d1) (hp2 : 0 < d2) (hp3 : 0 < d3) (hp4 : 0 < d4) (hp5 : 0 < d5)
    (hu1 : padicValNat 7 d1 = 0) (hu2 : padicValNat 7 d2 = 0)
    (hu3 : padicValNat 7 d3 = 0) (hu4 : padicValNat 7 d4 = 0)
    (hu5 : padicValNat 7 d5 = 0)
    {s : ZMod 7} (hs0 : s ≠ 0)
    (h1 : runit7 d1 = s) (h2 : runit7 d2 = s)
    (h3 : runit7 d3 = 2 * s) (h4 : runit7 d4 = 2 * s) (h5 : runit7 d5 = 4 * s)
    (he12 : eMod7 m d1 d2 = 2 * 7 ^ m) (he34 : eMod7 m d3 d4 = 7 ^ m) :
    ∃ lam : ℕ, ¬ 7 ∣ lam ∧ good7 m lam ({d1, d2, d3, d4, d5} : Finset ℕ) := by
  have hrel24 : runit7 d4 = 2 * runit7 d2 := by rw [h4, h2]
  have hrel25 : runit7 d2 = 2 * runit7 d5 := by
    rw [h2, h5, ← mul_assoc, show (2 : ZMod 7) * 4 = 1 from by decide, one_mul]
  have hrel25' : runit7 d5 ≠ 2 * runit7 d2 := by
    rw [h5, h2]
    intro hcon
    have h2s : (2 : ZMod 7) * s = 0 := by linear_combination hcon
    have hs : s = 4 * (2 * s) := by
      rw [← mul_assoc, show (4 : ZMod 7) * 2 = 1 from by decide, one_mul]
    rw [h2s, mul_zero] at hs
    exact hs0 hs
  set e24 := eMod7 m d2 d4 with he24
  set e25 := eMod7 m d2 d5 with he25
  by_cases hlow24 : eMod7 m d2 d4 % 7 ^ m = 0
  · set r24 : ZMod 7 := ((eMod7 m d2 d4 / 7 ^ m : ℕ) : ZMod 7) with hr24
    have hx0 := etd7_twoX_mem hrel24 hlow24
    rw [← hr24] at hx0
    rcases zmod7_split_a r24 with hrauto | hrA | hrB
    · have hnb := case66a_auto_dec r24 (etd7 m d2 d4) (etd7 m d2 d5) hrauto hx0
      exact case66a_red hm hp1 hp2 hp3 hp4 hp5 hu1 hu2 hu3 hu4 hu5 hs0
        h1 h2 h3 h4 h5 he12 he34 (k := 0) (j := 0) (by omega) (by simpa using hnb)
    · by_cases hlow25 : eMod7 m d2 d5 % 7 ^ m = 0
      · set r25 : ZMod 7 := ((eMod7 m d2 d5 / 7 ^ m : ℕ) : ZMod 7) with hr25
        obtain ⟨eps1, eps2, heps1, heps2, hsafe⟩ := case66a_eps r24 r25
        obtain ⟨k, hk7, hnb⟩ := case66a_corner hm hu5 hp5 hrel24 hrel25 hrel25'
          hlow24 hlow25 heps1 heps2 (by simpa [hr24, hr25] using hsafe)
        exact case66a_red hm hp1 hp2 hp3 hp4 hp5 hu1 hu2 hu3 hu4 hu5 hs0
          h1 h2 h3 h4 h5 he12 he34 (k := k) (j := 1) (by omega) hnb
      · have he250 : eMod7 m d2 d5 ≠ 0 := by intro h; rw [h] at hlow25; simp at hlow25
        have hν25 : padicValNat 7 (eMod7 m d2 d5) < m :=
          padic_lt_of_mod_ne he250 (eMod7_lt _ _ _) hlow25
        have hecomm : eMod7 m d5 d2 = eMod7 m d2 d5 :=
          eMod7_comm_of_two hrel25 (ne_of_gt hp5)
        have hν52 : padicValNat 7 (eMod7 m d5 d2) < m := by rw [hecomm]; exact hν25
        obtain ⟨k, hk7, hy⟩ := exists_multLow_etd7_avoid' hu5 hu2 hp5 hp2 hrel25
          (by rw [hecomm]; exact he250) hν52 case66a_apLen24
        have hlamr := runit7_multLow (k := k) hν52
        have hrels : runit7 ((1 + k * 7 ^ (m - padicValNat 7 (eMod7 m d5 d2))) * d2) =
            2 * runit7 ((1 + k * 7 ^ (m - padicValNat 7 (eMod7 m d5 d2))) * d5) := by
          rw [runit7_mul, runit7_mul, hlamr, one_mul, one_mul, hrel25]
        have hcomm := etd7_comm_of_two (m := m) hrels
          (mul_ne_zero (by positivity) (ne_of_gt hp5))
        rw [hcomm] at hy
        have hx := etd7_multLow_top_mem (k := k) hν52 hrel24 hlow24
        have hnb := case66a_safeA_dec r24 _ _ hrA (by simpa [hr24] using hx) hy
        exact case66a_red hm hp1 hp2 hp3 hp4 hp5 hu1 hu2 hu3 hu4 hu5 hs0
          h1 h2 h3 h4 h5 he12 he34 (k := k)
          (j := padicValNat 7 (eMod7 m d5 d2)) hν52 hnb
    · by_cases hlow25 : eMod7 m d2 d5 % 7 ^ m = 0
      · set r25 : ZMod 7 := ((eMod7 m d2 d5 / 7 ^ m : ℕ) : ZMod 7) with hr25
        obtain ⟨eps1, eps2, heps1, heps2, hsafe⟩ := case66a_eps r24 r25
        obtain ⟨k, hk7, hnb⟩ := case66a_corner hm hu5 hp5 hrel24 hrel25 hrel25'
          hlow24 hlow25 heps1 heps2 (by simpa [hr24, hr25] using hsafe)
        exact case66a_red hm hp1 hp2 hp3 hp4 hp5 hu1 hu2 hu3 hu4 hu5 hs0
          h1 h2 h3 h4 h5 he12 he34 (k := k) (j := 1) (by omega) hnb
      · have he250 : eMod7 m d2 d5 ≠ 0 := by intro h; rw [h] at hlow25; simp at hlow25
        have hν25 : padicValNat 7 (eMod7 m d2 d5) < m :=
          padic_lt_of_mod_ne he250 (eMod7_lt _ _ _) hlow25
        have hecomm : eMod7 m d5 d2 = eMod7 m d2 d5 :=
          eMod7_comm_of_two hrel25 (ne_of_gt hp5)
        have hν52 : padicValNat 7 (eMod7 m d5 d2) < m := by rw [hecomm]; exact hν25
        obtain ⟨k, hk7, hy⟩ := exists_multLow_etd7_avoid' hu5 hu2 hp5 hp2 hrel25
          (by rw [hecomm]; exact he250) hν52 case66a_apLen46
        have hlamr := runit7_multLow (k := k) hν52
        have hrels : runit7 ((1 + k * 7 ^ (m - padicValNat 7 (eMod7 m d5 d2))) * d2) =
            2 * runit7 ((1 + k * 7 ^ (m - padicValNat 7 (eMod7 m d5 d2))) * d5) := by
          rw [runit7_mul, runit7_mul, hlamr, one_mul, one_mul, hrel25]
        have hcomm := etd7_comm_of_two (m := m) hrels
          (mul_ne_zero (by positivity) (ne_of_gt hp5))
        rw [hcomm] at hy
        have hx := etd7_multLow_top_mem (k := k) hν52 hrel24 hlow24
        have hnb := case66a_safeB_dec r24 _ _ hrB (by simpa [hr24] using hx) hy
        exact case66a_red hm hp1 hp2 hp3 hp4 hp5 hu1 hu2 hu3 hu4 hu5 hs0
          h1 h2 h3 h4 h5 he12 he34 (k := k)
          (j := padicValNat 7 (eMod7 m d5 d2)) hν52 hnb
  · have he240 : eMod7 m d2 d4 ≠ 0 := by intro h; rw [h] at hlow24; simp at hlow24
    have hν24 : padicValNat 7 (eMod7 m d2 d4) < m :=
      padic_lt_of_mod_ne he240 (eMod7_lt _ _ _) hlow24
    obtain ⟨k, hk7, hx⟩ := exists_multLow_etd7_avoid' hu2 hu4 hp2 hp4 hrel24
      he240 hν24 case66a_apLen456
    have hnb :
        (etd7 m ((1 + k * 7 ^ (m - padicValNat 7 (eMod7 m d2 d4))) * d2)
            ((1 + k * 7 ^ (m - padicValNat 7 (eMod7 m d2 d4))) * d4),
         etd7 m ((1 + k * 7 ^ (m - padicValNat 7 (eMod7 m d2 d4))) * d2)
            ((1 + k * 7 ^ (m - padicValNat 7 (eMod7 m d2 d4))) * d5)) ∉ bad66a :=
      case66a_notbad_x_dec _ _ hx
    exact case66a_red hm hp1 hp2 hp3 hp4 hp5 hu1 hu2 hu3 hu4 hu5 hs0
      h1 h2 h3 h4 h5 he12 he34 (k := k)
      (j := padicValNat 7 (eMod7 m d2 d4)) hν24 hnb

private theorem smul_top_resid {m c e : ℕ} (hc : ¬ 7 ∣ c)
    (he0 : e ≠ 0) (hν : padicValNat 7 e = m) {t : ZMod 7}
    (ht : (c : ZMod 7) * runit7 e = t) :
    (c * e) % 7 ^ (m + 1) = t.val * 7 ^ m := by
  have hνce : padicValNat 7 (c * e) = m := by
    rw [padicValNat_mul_seven hc he0, hν]
  have h := residN_top hνce
  rw [qdig7_multTop hν, ht] at h
  exact h

private theorem case66a {m : ℕ} (hm : 2 ≤ m)
    {d1 d2 d3 d4 d5 : ℕ}
    (hp1 : 0 < d1) (hp2 : 0 < d2) (hp3 : 0 < d3) (hp4 : 0 < d4) (hp5 : 0 < d5)
    (hu1 : padicValNat 7 d1 = 0) (hu2 : padicValNat 7 d2 = 0)
    (hu3 : padicValNat 7 d3 = 0) (hu4 : padicValNat 7 d4 = 0)
    (hu5 : padicValNat 7 d5 = 0)
    {s : ZMod 7} (hs0 : s ≠ 0)
    (h1 : runit7 d1 = s) (h2 : runit7 d2 = s)
    (h3 : runit7 d3 = 2 * s) (h4 : runit7 d4 = 2 * s) (h5 : runit7 d5 = 4 * s)
    (he12 : eMod7 m d1 d2 ≠ 0) (he34 : eMod7 m d3 d4 ≠ 0)
    (hν12 : padicValNat 7 (eMod7 m d1 d2) = m)
    (hν34 : padicValNat 7 (eMod7 m d3 d4) = m)
    (hrat : runit7 (eMod7 m d1 d2) = 2 * runit7 (eMod7 m d3 d4)) :
    ∃ lam : ℕ, ¬ 7 ∣ lam ∧ good7 m lam ({d1, d2, d3, d4, d5} : Finset ℕ) := by
  obtain ⟨c, hcpos, hc7, hc34, hqc34⟩ := exists_top_scalar_set hν34 he34
    (t := (1 : ZMod 7)) (by decide)
  have hcnd : ¬ 7 ∣ c := fun hd => absurd (Nat.le_of_dvd hcpos hd) (by omega)
  have hcu : padicValNat 7 c = 0 := padicValNat.eq_zero_of_not_dvd hcnd
  have hrc : runit7 c = (c : ZMod 7) := runit7_of_padic_zero hcu
  have hrc0 : runit7 c ≠ 0 := runit7_ne_zero hcpos
  have hc34z : (c : ZMod 7) * runit7 (eMod7 m d3 d4) = 1 := by
    have h := qdig7_multTop (l := c) hν34
    rw [hqc34] at h
    exact h.symm
  have hc12z : (c : ZMod 7) * runit7 (eMod7 m d1 d2) = 2 := by
    rw [hrat]
    calc
      (c : ZMod 7) * (2 * runit7 (eMod7 m d3 d4)) =
          2 * ((c : ZMod 7) * runit7 (eMod7 m d3 d4)) := by ring
      _ = 2 := by rw [hc34z, mul_one]
  have he12c : eMod7 m (c * d1) (c * d2) = 2 * 7 ^ m := by
    rw [eMod7_smul hrc0]
    have h := smul_top_resid hcnd he12 hν12 hc12z
    norm_num at h ⊢
    exact h
  have he34c : eMod7 m (c * d3) (c * d4) = 7 ^ m := by
    rw [eMod7_smul hrc0]
    rw [show (1 : ZMod 7).val = 1 by decide, one_mul] at hc34
    exact hc34
  set sc : ZMod 7 := runit7 c * s with hsc
  have hsc0 : sc ≠ 0 := mul_ne_zero hrc0 hs0
  have hposc : ∀ d : ℕ, 0 < d → 0 < c * d := fun _ hd => Nat.mul_pos hcpos hd
  have huc : ∀ d : ℕ, d ≠ 0 → padicValNat 7 d = 0 →
      padicValNat 7 (c * d) = 0 := fun _ hd0 hd => by
    rw [padicValNat_mul_seven hcnd hd0, hd]
  have hr1 : runit7 (c * d1) = sc := by rw [runit7_mul, h1, hsc]
  have hr2 : runit7 (c * d2) = sc := by rw [runit7_mul, h2, hsc]
  have hr3 : runit7 (c * d3) = 2 * sc := by rw [runit7_mul, h3, hsc]; ring
  have hr4 : runit7 (c * d4) = 2 * sc := by rw [runit7_mul, h4, hsc]; ring
  have hr5 : runit7 (c * d5) = 4 * sc := by rw [runit7_mul, h5, hsc]; ring
  obtain ⟨lam, hlam, hgood⟩ := case66a_go hm
    (hposc _ hp1) (hposc _ hp2) (hposc _ hp3) (hposc _ hp4) (hposc _ hp5)
    (huc _ (ne_of_gt hp1) hu1) (huc _ (ne_of_gt hp2) hu2)
    (huc _ (ne_of_gt hp3) hu3) (huc _ (ne_of_gt hp4) hu4)
    (huc _ (ne_of_gt hp5) hu5) hsc0 hr1 hr2 hr3 hr4 hr5 he12c he34c
  have himg : ({d1, d2, d3, d4, d5} : Finset ℕ).image (c * ·) =
      {c * d1, c * d2, c * d3, c * d4, c * d5} := by
    simp only [Finset.image_insert, Finset.image_singleton]
  rw [← himg] at hgood
  exact ⟨lam * c, Nat.Prime.not_dvd_mul Nat.prime_seven hlam hcnd, good7_mul hgood⟩

private theorem case66b {m : ℕ} (hm : 2 ≤ m)
    {d1 d2 d3 d4 d5 : ℕ}
    (hp1 : 0 < d1) (hp2 : 0 < d2) (hp3 : 0 < d3) (hp4 : 0 < d4) (hp5 : 0 < d5)
    (hu1 : padicValNat 7 d1 = 0) (hu2 : padicValNat 7 d2 = 0)
    (hu3 : padicValNat 7 d3 = 0) (hu4 : padicValNat 7 d4 = 0)
    (hu5 : padicValNat 7 d5 = 0)
    {s : ZMod 7} (hs0 : s ≠ 0)
    (h1 : runit7 d1 = s) (h2 : runit7 d2 = s)
    (h3 : runit7 d3 = 2 * s) (h4 : runit7 d4 = 2 * s) (h5 : runit7 d5 = 4 * s)
    (he12 : eMod7 m d1 d2 ≠ 0) (he34 : eMod7 m d3 d4 ≠ 0)
    (hν12 : padicValNat 7 (eMod7 m d1 d2) = m)
    (hν34 : padicValNat 7 (eMod7 m d3 d4) = m)
    (hrat : runit7 (eMod7 m d3 d4) = 2 * runit7 (eMod7 m d1 d2)) :
    ∃ lam : ℕ, ¬ 7 ∣ lam ∧ good7 m lam ({d1, d2, d3, d4, d5} : Finset ℕ) := by
  obtain ⟨c, hcpos, hc7, hc12, hqc12⟩ := exists_top_scalar_set hν12 he12
    (t := (1 : ZMod 7)) (by decide)
  have hcnd : ¬ 7 ∣ c := fun hd => absurd (Nat.le_of_dvd hcpos hd) (by omega)
  have hcu : padicValNat 7 c = 0 := padicValNat.eq_zero_of_not_dvd hcnd
  have hrc : runit7 c = (c : ZMod 7) := runit7_of_padic_zero hcu
  have hrc0 : runit7 c ≠ 0 := runit7_ne_zero hcpos
  have hc12z : (c : ZMod 7) * runit7 (eMod7 m d1 d2) = 1 := by
    have h := qdig7_multTop (l := c) hν12
    rw [hqc12] at h
    exact h.symm
  have hc34z : (c : ZMod 7) * runit7 (eMod7 m d3 d4) = 2 := by
    rw [hrat]
    calc
      (c : ZMod 7) * (2 * runit7 (eMod7 m d1 d2)) =
          2 * ((c : ZMod 7) * runit7 (eMod7 m d1 d2)) := by ring
      _ = 2 := by rw [hc12z, mul_one]
  have he12c : eMod7 m (c * d1) (c * d2) = 7 ^ m := by
    rw [eMod7_smul hrc0]
    rw [show (1 : ZMod 7).val = 1 by decide, one_mul] at hc12
    exact hc12
  have he34c : eMod7 m (c * d3) (c * d4) = 2 * 7 ^ m := by
    rw [eMod7_smul hrc0]
    have h := smul_top_resid hcnd he34 hν34 hc34z
    norm_num at h ⊢
    exact h
  set sc : ZMod 7 := runit7 c * s with hsc
  have hsc0 : sc ≠ 0 := mul_ne_zero hrc0 hs0
  have hposc : ∀ d : ℕ, 0 < d → 0 < c * d := fun _ hd => Nat.mul_pos hcpos hd
  have huc : ∀ d : ℕ, d ≠ 0 → padicValNat 7 d = 0 →
      padicValNat 7 (c * d) = 0 := fun _ hd0 hd => by
    rw [padicValNat_mul_seven hcnd hd0, hd]
  have hr1 : runit7 (c * d1) = sc := by rw [runit7_mul, h1, hsc]
  have hr2 : runit7 (c * d2) = sc := by rw [runit7_mul, h2, hsc]
  have hr3 : runit7 (c * d3) = 2 * sc := by rw [runit7_mul, h3, hsc]; ring
  have hr4 : runit7 (c * d4) = 2 * sc := by rw [runit7_mul, h4, hsc]; ring
  have hr5 : runit7 (c * d5) = 4 * sc := by rw [runit7_mul, h5, hsc]; ring
  obtain ⟨lam, hlam, hgood⟩ := case66b_go hm
    (hposc _ hp1) (hposc _ hp2) (hposc _ hp3) (hposc _ hp4) (hposc _ hp5)
    (huc _ (ne_of_gt hp1) hu1) (huc _ (ne_of_gt hp2) hu2)
    (huc _ (ne_of_gt hp3) hu3) (huc _ (ne_of_gt hp4) hu4)
    (huc _ (ne_of_gt hp5) hu5) hsc0 hr1 hr2 hr3 hr4 hr5 he12c he34c
  have himg : ({d1, d2, d3, d4, d5} : Finset ℕ).image (c * ·) =
      {c * d1, c * d2, c * d3, c * d4, c * d5} := by
    simp only [Finset.image_insert, Finset.image_singleton]
  rw [← himg] at hgood
  exact ⟨lam * c, Nat.Prime.not_dvd_mul Nat.prime_seven hlam hcnd, good7_mul hgood⟩

private theorem case66_swap_top {m x y : ℕ} (hm : 0 < m)
    (hx : 0 < x) (hy : 0 < y)
    (hr : runit7 x = runit7 y)
    (he : eMod7 m x y ≠ 0)
    (hν : padicValNat 7 (eMod7 m x y) = m) :
    eMod7 m y x ≠ 0 ∧
      padicValNat 7 (eMod7 m y x) = m ∧
      runit7 (eMod7 m y x) = -runit7 (eMod7 m x y) := by
  have hxy := rel_same_of_eq hr (ne_of_gt hy)
  have hyx := rel_same_of_eq hr.symm (ne_of_gt hx)
  have hswap := eMod7_same_swap (m := m) hxy hyx
  have hneg := neg_resid he (eMod7_lt m x y) (by omega : padicValNat 7 (eMod7 m x y) ≤ m)
  have hval : padicValNat 7 (eMod7 m y x) = m := by
    rw [hswap]
    exact hneg.1.trans hν
  have hne : eMod7 m y x ≠ 0 := by
    intro h0
    rw [h0, padicValNat.zero] at hval
    omega
  refine ⟨hne, hval, ?_⟩
  rw [hswap]
  exact hneg.2

private theorem case66_top_core {m : ℕ} (hm : 2 ≤ m)
    {d1 d2 d3 d4 d5 : ℕ}
    (hp1 : 0 < d1) (hp2 : 0 < d2) (hp3 : 0 < d3) (hp4 : 0 < d4) (hp5 : 0 < d5)
    (hu1 : padicValNat 7 d1 = 0) (hu2 : padicValNat 7 d2 = 0)
    (hu3 : padicValNat 7 d3 = 0) (hu4 : padicValNat 7 d4 = 0)
    (hu5 : padicValNat 7 d5 = 0)
    {s : ZMod 7} (hs : s ∈ ({1, 2, 4} : Finset (ZMod 7)))
    (h1 : runit7 d1 = s) (h2 : runit7 d2 = s)
    (h3 : runit7 d3 = 2 * s) (h4 : runit7 d4 = 2 * s) (h5 : runit7 d5 = 4 * s)
    (he12 : eMod7 m d1 d2 ≠ 0) (he34 : eMod7 m d3 d4 ≠ 0)
    (hν12 : padicValNat 7 (eMod7 m d1 d2) = m)
    (hν34 : padicValNat 7 (eMod7 m d3 d4) = m)
    (hr12 : runit7 (eMod7 m d1 d2) ∈ ({1, 2, 4} : Finset (ZMod 7)))
    (hr34 : runit7 (eMod7 m d3 d4) ∈ ({1, 2, 4} : Finset (ZMod 7))) :
    ∃ lam : ℕ, ¬ 7 ∣ lam ∧ good7 m lam ({d1, d2, d3, d4, d5} : Finset ℕ) := by
  have hs0 : s ≠ 0 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl | rfl <;> decide
  rcases zmod7_ratio124 _ _ hr12 hr34 with heq | hrat | hrat
  · obtain ⟨c, hcpos, hc7, hc12, hqc12⟩ := exists_top_scalar_set hν12 he12
      (t := (6 : ZMod 7)) (by decide)
    have hcnd : ¬ 7 ∣ c := fun hd => absurd (Nat.le_of_dvd hcpos hd) (by omega)
    have hrc0 : runit7 c ≠ 0 := runit7_ne_zero hcpos
    have hc12z : (c : ZMod 7) * runit7 (eMod7 m d1 d2) = 6 := by
      have h := qdig7_multTop (l := c) hν12
      rw [hqc12] at h
      exact h.symm
    have hq34raw : qdig7 m (c * eMod7 m d3 d4) = 6 := by
      rw [qdig7_multTop hν34, ← heq, hc12z]
    have hq12 : qdig7 m (eMod7 m (c * d1) (c * d2)) ∈
        ({0, 6} : Finset (ZMod 7)) := by
      rw [eMod7_smul hrc0, qdig7_of_resid, hqc12]
      decide
    have hq34 : qdig7 m (eMod7 m (c * d3) (c * d4)) ∈
        ({0, 6} : Finset (ZMod 7)) := by
      rw [eMod7_smul hrc0, qdig7_of_resid, hq34raw]
      decide
    let A1 : Finset ℕ := {d1, d2}
    let A2 : Finset ℕ := {d3, d4}
    let A4 : Finset ℕ := {d5}
    have hpos : ∀ d ∈ A1 ∪ A2 ∪ A4, 0 < d := by
      intro d hd
      simp only [A1, A2, A4, Finset.mem_union, Finset.mem_insert,
        Finset.mem_singleton] at hd
      rcases hd with ((rfl | rfl) | (rfl | rfl)) | rfl <;> assumption
    have hunit : ∀ d ∈ A1 ∪ A2 ∪ A4, padicValNat 7 d = 0 := by
      intro d hd
      simp only [A1, A2, A4, Finset.mem_union, Finset.mem_insert,
        Finset.mem_singleton] at hd
      rcases hd with ((rfl | rfl) | (rfl | rfl)) | rfl <;> assumption
    have hcls1 : ∀ d ∈ A1, runit7 d = s := by
      intro d hd
      simp only [A1, Finset.mem_insert, Finset.mem_singleton] at hd
      rcases hd with rfl | rfl <;> assumption
    have hcls2 : ∀ d ∈ A2, runit7 d = 2 * s := by
      intro d hd
      simp only [A2, Finset.mem_insert, Finset.mem_singleton] at hd
      rcases hd with rfl | rfl <;> assumption
    have hcls4 : ∀ d ∈ A4, runit7 d = 4 * s := by
      intro d hd
      simp only [A4, Finset.mem_singleton] at hd
      subst d
      exact h5
    obtain ⟨lam, hlam, hgood⟩ := case66_finish (by omega : 0 < m)
      hpos hunit hs hcls1 hcls2 hcls4 (A1 := A1) (A2 := A2) (A4 := A4)
      (d1 := d1) (d2 := d2) (d3 := d3) (d4 := d4) (d5 := d5)
      rfl rfl rfl hcnd hq12 hq34
    have hset : A1 ∪ A2 ∪ A4 = ({d1, d2, d3, d4, d5} : Finset ℕ) := by
      ext d
      simp only [A1, A2, A4, Finset.mem_union, Finset.mem_insert,
        Finset.mem_singleton]
      tauto
    rw [hset] at hgood
    exact ⟨lam, hlam, hgood⟩
  · exact case66a hm hp1 hp2 hp3 hp4 hp5 hu1 hu2 hu3 hu4 hu5 hs0
      h1 h2 h3 h4 h5 he12 he34 hν12 hν34 hrat
  · exact case66b hm hp1 hp2 hp3 hp4 hp5 hu1 hu2 hu3 hu4 hu5 hs0
      h1 h2 h3 h4 h5 he12 he34 hν12 hν34 hrat

theorem case66_top {m : ℕ} (hm : 2 ≤ m) :
    ∀ {d1 d2 d3 d4 d5 : ℕ}, d1 ≠ d2 → d3 ≠ d4 →
      0 < d1 → 0 < d2 → 0 < d3 → 0 < d4 → 0 < d5 →
      padicValNat 7 d1 = 0 → padicValNat 7 d2 = 0 →
      padicValNat 7 d3 = 0 → padicValNat 7 d4 = 0 →
      padicValNat 7 d5 = 0 →
      ∀ {s' : ZMod 7}, s' ∈ ({1, 2, 4} : Finset (ZMod 7)) →
      runit7 d1 = s' → runit7 d2 = s' →
      runit7 d3 = 2 * s' → runit7 d4 = 2 * s' → runit7 d5 = 4 * s' →
      eMod7 m d1 d2 ≠ 0 → eMod7 m d3 d4 ≠ 0 →
      padicValNat 7 (eMod7 m d1 d2) = m →
      padicValNat 7 (eMod7 m d3 d4) = m →
      ∃ lam : ℕ, ¬ 7 ∣ lam ∧
        good7 m lam ({d1, d2, d3, d4, d5} : Finset ℕ) := by
  intro d1 d2 d3 d4 d5 hd12 hd34 hp1 hp2 hp3 hp4 hp5
    hu1 hu2 hu3 hu4 hu5 s hs h1 h2 h3 h4 h5 he12 he34 hν12 hν34
  have hr12nz : runit7 (eMod7 m d1 d2) ≠ 0 :=
    runit7_ne_zero (Nat.pos_of_ne_zero he12)
  have hr34nz : runit7 (eMod7 m d3 d4) ≠ 0 :=
    runit7_ne_zero (Nat.pos_of_ne_zero he34)
  rcases neg_mem124 hr12nz with hr12 | hr12
  · rcases neg_mem124 hr34nz with hr34 | hr34
    · exact case66_top_core hm hp1 hp2 hp3 hp4 hp5 hu1 hu2 hu3 hu4 hu5 hs
        h1 h2 h3 h4 h5 he12 he34 hν12 hν34 hr12 hr34
    · obtain ⟨he43, hν43, hr43⟩ := case66_swap_top (by omega : 0 < m)
        hp3 hp4 (by rw [h3, h4]) he34 hν34
      obtain ⟨lam, hlam, hgood⟩ := case66_top_core hm
        hp1 hp2 hp4 hp3 hp5 hu1 hu2 hu4 hu3 hu5 hs
        h1 h2 h4 h3 h5 he12 he43 hν12 hν43 hr12 (by rwa [hr43])
      have hset : ({d1, d2, d4, d3, d5} : Finset ℕ) = {d1, d2, d3, d4, d5} := by
        rw [Finset.insert_comm d4 d3]
      rw [hset] at hgood
      exact ⟨lam, hlam, hgood⟩
  · obtain ⟨he21, hν21, hr21⟩ := case66_swap_top (by omega : 0 < m)
      hp1 hp2 (by rw [h1, h2]) he12 hν12
    rcases neg_mem124 hr34nz with hr34 | hr34
    · obtain ⟨lam, hlam, hgood⟩ := case66_top_core hm
        hp2 hp1 hp3 hp4 hp5 hu2 hu1 hu3 hu4 hu5 hs
        h2 h1 h3 h4 h5 he21 he34 hν21 hν34 (by rwa [hr21]) hr34
      have hset : ({d2, d1, d3, d4, d5} : Finset ℕ) = {d1, d2, d3, d4, d5} := by
        rw [Finset.insert_comm d2 d1]
      rw [hset] at hgood
      exact ⟨lam, hlam, hgood⟩
    · obtain ⟨he43, hν43, hr43⟩ := case66_swap_top (by omega : 0 < m)
        hp3 hp4 (by rw [h3, h4]) he34 hν34
      obtain ⟨lam, hlam, hgood⟩ := case66_top_core hm
        hp2 hp1 hp4 hp3 hp5 hu2 hu1 hu4 hu3 hu5 hs
        h2 h1 h4 h3 h5 he21 he43 hν21 hν43 (by rwa [hr21]) (by rwa [hr43])
      have hset : ({d2, d1, d4, d3, d5} : Finset ℕ) = {d1, d2, d3, d4, d5} := by
        rw [Finset.insert_comm d2 d1, Finset.insert_comm d4 d3]
      rw [hset] at hgood
      exact ⟨lam, hlam, hgood⟩

end LRC7Case66
