/-
Copyright (c) 2026 Research07 contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Research07 contributors
-/
import Research07.LRC3.Circ

/-!
# Discrete infrastructure for the five-runner case

Modular-arithmetic layer for the Barajas–Serra proof (arXiv:0710.4495, §2–3)
of the lonely runner conjecture for four integer speeds. Fix `p = 5`,
`m = max ν₅(D)`, `N = 5^{m+1}`.

* `residN x N = x % N`, `absModN x N = min (x%N, N − x%N)` — circular
  distance to `0` in `ℤ/N`.
* `level D j` — elements of `D` with `padicValNat 5 d = j`.
* `qdig m x : ZMod 5` — leading base-5 digit of `x`'s residue mod `5^{m+1}`.
* `runit x : ZMod 5` — unit part of `x` mod 5.
* `multLow m j = {1 + k·5^{m−j}}`, `multTop = {1,2,3,4}` — the multiplier
  families `Λ_{j,5}` of the paper.

Key facts (paper eqs. (2),(3),(4),(5)): low multipliers preserve residues of
higher-level elements and cyclically shift the leading digit of same-level
elements; the goodness condition `|x|_N ≥ 5^m` is the digit condition
`qdig ∈ {1,2,3}` for non-top elements and is automatic for top-level ones.
-/

/-- Residue of `x` modulo `N` in `{0, …, N−1}`. -/
def residN (x N : ℕ) : ℕ := x % N

/-- Circular distance from `x` to `0` in `ℤ/N`: `min (x%N) (N − x%N)`. -/
def absModN (x N : ℕ) : ℕ := min (x % N) (N - x % N)

/-- The `j`-th 5-adic level of `D`: elements with `padicValNat 5 d = j`. -/
def level (D : Finset ℕ) (j : ℕ) : Finset ℕ :=
  D.filter fun d => padicValNat 5 d = j

/-- Leading base-5 digit of `x % 5^{m+1}`, valued in `ZMod 5`. -/
def qdig (m x : ℕ) : ZMod 5 := (↑((x % 5 ^ (m + 1)) / 5 ^ m) : ZMod 5)

/-- Unit part of `x` modulo 5: the trailing nonzero base-5 digit. -/
def runit (x : ℕ) : ZMod 5 := (↑(x / 5 ^ padicValNat 5 x) : ZMod 5)

/-- Multiplier family `Λ_{j,5}` for `j < m`: `{1 + k·5^{m−j} : k ∈ range 5}`. -/
def multLow (m j : ℕ) : Finset ℕ :=
  (Finset.range 5).image fun k => 1 + k * 5 ^ (m - j)

/-- Multiplier family `Λ_{m,5}`: `{1,2,3,4}`. -/
def multTop : Finset ℕ := {1, 2, 3, 4}

/-- The unit part of a positive integer is a nonzero residue. -/
theorem runit_ne_zero {x : ℕ} (hx : 0 < x) : runit x ≠ 0 := by
  sorry

/-- Elements at the top level stay at distance `≥ 5^m` under unit multipliers
(their residue is `c·5^m` with `c ∈ {1,…,4}`, and `min c (5−c) ≥ 1`). -/
theorem absModN_top_ge {m d lam : ℕ} (hd : padicValNat 5 d = m) (hpos : 0 < d)
    (hlam : ¬ 5 ∣ lam) :
    5 ^ m ≤ absModN (lam * d) (5 ^ (m + 1)) := by
  sorry

/-- For non-top elements `ν₅(d) < m` and unit multipliers, the distance
condition `|λd|_N ≥ 5^m` is equivalent to the digit condition
`qdig (λd) ∈ {1,2,3}`. The boundary residue `4·5^m` is excluded since it
would have 5-adic valuation `m`. -/
theorem absModN_ge_iff_qdig {m d lam : ℕ} (hd : padicValNat 5 d < m)
    (hpos : 0 < d) (hlam : ¬ 5 ∣ lam) :
    5 ^ m ≤ absModN (lam * d) (5 ^ (m + 1)) ↔
      1 ≤ (qdig m (lam * d)).val ∧ (qdig m (lam * d)).val ≤ 3 := by
  sorry

/-- Preservation identity (paper eq. (2)): a multiplier from `Λ_{j,5}` leaves
the residue of any element at level `> j` unchanged modulo `5^{m+1}`. -/
theorem residN_multLow {m j k x : ℕ} (hjm : j < m) (hx : j < padicValNat 5 x) :
    (1 + k * 5 ^ (m - j)) * x % 5 ^ (m + 1) = x % 5 ^ (m + 1) := by
  sorry

/-- Shift identity (paper eq. (3)): a `Λ_{j,5}`-multiplier shifts the leading
digit of a level-`j` element by `k · runit x`. -/
theorem qdig_multLow {m j k x : ℕ} (hjm : j < m) (hx : padicValNat 5 x = j) :
    qdig m ((1 + k * 5 ^ (m - j)) * x) = qdig m x + (k : ZMod 5) * runit x := by
  sorry

/-- Top-level identity: multiplying a level-`m` element by `l` scales its
digit by `l`. -/
theorem qdig_multTop {m l x : ℕ} (hx : padicValNat 5 x = m) :
    qdig m (l * x) = (l : ZMod 5) * runit x := by
  sorry

/-- Carry bound (paper eq. (5)): the leading digit of `(j+1)·x` differs from
`qdig (j·x) + qdig x` by a carry of at most `1`. -/
theorem qdig_add_one (m j x : ℕ) :
    (qdig m ((j + 1) * x) - qdig m (j * x) - qdig m x).val ≤ 1 := by
  sorry

/-- Sign flip preserves the circular distance: `|N − x % N|_N = |x|_N`. -/
theorem absModN_neg {x N : ℕ} (hN : 0 < N) (hx : x % N ≠ 0) :
    absModN (N - x % N) N = absModN x N := by
  sorry

/-- Bridge: for `t = λ/N`, `circ (t·d) = |λd|_N / N`. -/
theorem circ_mul_div_eq_absModN (lam d N : ℕ) (hN : 0 < N) :
    circ ((lam * d : ℝ) / N) = (absModN (lam * d) N : ℝ) / N := by
  sorry

/-- Package: `|λd|_N ≥ 5^m` gives `circ (λd/5^{m+1}) ≥ 1/5`. -/
theorem circ_ge_fifth {m lam d : ℕ}
    (h : 5 ^ m ≤ absModN (lam * d) (5 ^ (m + 1))) :
    (1 / 5 : ℝ) ≤ circ ((lam * d : ℝ) / (5 ^ (m + 1) : ℕ)) := by
  sorry
