/-
Copyright (c) 2026 Research07 contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Research07 contributors
-/
import Research07.LRC7.Filtering

/-!
# The case `|A| = 4` (Barajas–Serra §5)

Four unit-level elements `A ⊆ D₇(0)` with residues in `{1,2,4}` plus one
element `d5` at level `i₀ ∈ (0, m]`.  The paper builds two multiplier
families

* `λ'_j = j·u'·(1 + 7^{m−i₀})`, `1 ≤ j ≤ 5`, where `u'·u ≡ 1 (mod 7^{m+1−i₀})`
  and `d5 = u·7^{i₀}` — eq. (8) gives `|λ'_j d5|_N ≥ 7^m`;
* `λ_k = 1 + k·7^m ∈ Λ₀`, `0 ≤ k ≤ 6` — preserves `d5`'s residue verbatim
  (`residN_multLow7`, `ν(d5) > 0`) and shifts `qdig` by `k·runit7` (eq. (10)).

The digit dynamics is eq. (9): `q(λ'_{j+1}·d) ∈ q(λ'_j·d) + q(λ'_1·d) + {0,1}`
(`qdig7_add_one`), and eq. (10) (`qdig7_multLow` with `j = 0`).

Three sub-cases by the size of the most popular congruence class `A_s`,
`s ∈ {1,2,4}`: `|A_s| = 4`, `3`, `2`.  Each is a finite `ZMod 7` digit chase,
implemented via `decide`-checked combinatorial lemmas below.
-/

private instance : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩

-- The nested `∀`/`→` decidable propositions in `prop2i`/`prop2ii` exceed the
-- default `synthInstance.maxSize`; raise it (same pattern as `maxRecDepth`
-- in `FiniteBase.lean`).
set_option synthInstance.maxSize 4096

/-! ## `ZMod 7` combinatorial layer -/

/-- Membership in a cyclic interval is translation-equivariant. -/
theorem mem_cycIv_add {i a : ZMod 7} {L : ℕ} {x : ZMod 7} :
    x ∈ cycIv i L ↔ x + a ∈ cycIv (i + a) L := by
  simp only [cycIv, Finset.mem_filter, Finset.mem_univ, true_and]
  have : x + a - (i + a) = x - i := by ring
  rw [this]

/-- A cyclic interval of length `≤ 5` starting at `1` avoids `{0, 6}`. -/
theorem not_mem_bad_of_mem_cycIv {x : ZMod 7} {L : ℕ} (hL : L ≤ 5)
    (h : x ∈ cycIv 1 L) : x ∉ ({0, 6} : Finset (ZMod 7)) := by
  simp only [cycIv, Finset.mem_filter, Finset.mem_univ, true_and] at h
  simp only [Finset.mem_insert, Finset.mem_singleton]
  rintro (rfl | rfl)
  · have hv : ((0 : ZMod 7) - 1).val = 6 := by decide
    omega
  · have hv : ((6 : ZMod 7) - 1).val = 5 := by decide
    omega

/-- The two shift candidates for a leftover element: `z` and `z + r` cannot
both lie in `{0,6}` when `r ∈ {2,4}`. -/
theorem pair_avoid {z r : ZMod 7} (hr : r = 2 ∨ r = 4) :
    z ∉ ({0, 6} : Finset (ZMod 7)) ∨ z + r ∉ ({0, 6} : Finset (ZMod 7)) := by
  rcases hr with rfl | rfl <;> revert z <;> decide

/-- Four candidate shifts for two leftover elements with `r₃ = r₄ = 2`. -/
theorem quad_avoid_22 (z3 z4 : ZMod 7) :
    ∃ i ∈ ({0, 1, 2, 3} : Finset (ZMod 7)),
      z3 + i * 2 ∉ ({0, 6} : Finset (ZMod 7)) ∧
      z4 + i * 2 ∉ ({0, 6} : Finset (ZMod 7)) := by
  fin_cases z3 <;> fin_cases z4 <;> decide

/-- Four candidate shifts for two leftover elements with `r₃ = 2`, `r₄ = 4`. -/
theorem quad_avoid_24 (z3 z4 : ZMod 7) :
    ∃ i ∈ ({0, 1, 2, 3} : Finset (ZMod 7)),
      z3 + i * 2 ∉ ({0, 6} : Finset (ZMod 7)) ∧
      z4 + i * 4 ∉ ({0, 6} : Finset (ZMod 7)) := by
  fin_cases z3 <;> fin_cases z4 <;> decide

/-- A 4-element subset hitting every 2-interval is a difference-2 AP. -/
theorem shape4 {x0 x1 x2 x3 : ZMod 7}
    (h : ∀ i : ZMod 7, (({x0, x1, x2, x3} : Finset (ZMod 7)) ∩ cycIv i 2).Nonempty) :
    ∃ x : ZMod 7, ({x0, x1, x2, x3} : Finset (ZMod 7)) = {x, x + 2, x + 4, x + 6} := by
  suffices H : ∀ x0 x1 x2 x3 : ZMod 7,
      (∀ i : ZMod 7, (({x0, x1, x2, x3} : Finset (ZMod 7)) ∩
        cycIv i 2).Nonempty) →
      ∃ x : ZMod 7, ({x0, x1, x2, x3} : Finset (ZMod 7)) =
        {x, x + 2, x + 4, x + 6} by
    exact H x0 x1 x2 x3 h
  decide

/-- A 3-element subset contained in no 4-interval has one of the two
archetypal shapes `{x, x+1, x+4}` or `{x, x+2, x+4}`. -/
theorem shape3 {x0 x1 x2 : ZMod 7}
    (h : ∀ i : ZMod 7, ¬ ({x0, x1, x2} : Finset (ZMod 7)) ⊆ cycIv i 4) :
    (∃ x : ZMod 7, ({x0, x1, x2} : Finset (ZMod 7)) = {x, x + 1, x + 4}) ∨
    (∃ x : ZMod 7, ({x0, x1, x2} : Finset (ZMod 7)) = {x, x + 2, x + 4}) := by
  suffices H : ∀ x0 x1 x2 : ZMod 7,
      (∀ i : ZMod 7, ¬ ({x0, x1, x2} : Finset (ZMod 7)) ⊆ cycIv i 4) →
      (∃ x : ZMod 7, ({x0, x1, x2} : Finset (ZMod 7)) = {x, x + 1, x + 4}) ∨
      (∃ x : ZMod 7, ({x0, x1, x2} : Finset (ZMod 7)) = {x, x + 2, x + 4}) by
    exact H x0 x1 x2 h
  decide

/-- A pair contained in no 2-interval has difference outside `{0,1,6}`. -/
theorem pair_dist {x0 x1 : ZMod 7}
    (h : ∀ i : ZMod 7, ¬ ({x0, x1} : Finset (ZMod 7)) ⊆ cycIv i 2) :
    x1 - x0 ∉ ({0, 1, 6} : Finset (ZMod 7)) := by
  suffices H : ∀ x0 x1 : ZMod 7,
      (∀ i : ZMod 7, ¬ ({x0, x1} : Finset (ZMod 7)) ⊆ cycIv i 2) →
      x1 - x0 ∉ ({0, 1, 6} : Finset (ZMod 7)) by
    exact H x0 x1 h
  decide

/-- `|Aₛ| = 4` propagation: from `q₁(A) = {0,2,4,6}` (normalized) the `j = 3`
digits still hit every 2-interval only if the `j = 4` digits collapse into a
4-interval — contradicting `apLen ≥ 6`. -/
theorem prop4 (b0 b1 b2 b3 : ZMod 7)
    (hb0 : b0 ∈ ({0, 1, 2} : Finset (ZMod 7)))
    (hb1 : b1 ∈ ({6, 0, 1} : Finset (ZMod 7)))
    (hb2 : b2 ∈ ({5, 6, 0} : Finset (ZMod 7)))
    (hb3 : b3 ∈ ({4, 5, 6} : Finset (ZMod 7)))
    (hhit : ∀ i : ZMod 7, (({b0, b1, b2, b3} : Finset (ZMod 7)) ∩
      cycIv i 2).Nonempty)
    (c0 c1 c2 c3 : ZMod 7)
    (hc0 : c0 - b0 ∈ ({0, 1} : Finset (ZMod 7)))
    (hc1 : c1 - b1 - 2 ∈ ({0, 1} : Finset (ZMod 7)))
    (hc2 : c2 - b2 - 4 ∈ ({0, 1} : Finset (ZMod 7)))
    (hc3 : c3 - b3 - 6 ∈ ({0, 1} : Finset (ZMod 7))) :
    ∃ i : ZMod 7, ({c0, c1, c2, c3} : Finset (ZMod 7)) ⊆ cycIv i 5 := by
  suffices H : ∀ b0 : ZMod 7, b0 ∈ ({0, 1, 2} : Finset (ZMod 7)) →
      ∀ b1 : ZMod 7, b1 ∈ ({6, 0, 1} : Finset (ZMod 7)) →
      ∀ b2 : ZMod 7, b2 ∈ ({5, 6, 0} : Finset (ZMod 7)) →
      ∀ b3 : ZMod 7, b3 ∈ ({4, 5, 6} : Finset (ZMod 7)) →
      (∀ i : ZMod 7, (({b0, b1, b2, b3} : Finset (ZMod 7)) ∩
        cycIv i 2).Nonempty) →
      ∀ c0 : ZMod 7, c0 - b0 ∈ ({0, 1} : Finset (ZMod 7)) →
      ∀ c1 : ZMod 7, c1 - b1 - 2 ∈ ({0, 1} : Finset (ZMod 7)) →
      ∀ c2 : ZMod 7, c2 - b2 - 4 ∈ ({0, 1} : Finset (ZMod 7)) →
      ∀ c3 : ZMod 7, c3 - b3 - 6 ∈ ({0, 1} : Finset (ZMod 7)) →
      ∃ i : ZMod 7, ({c0, c1, c2, c3} : Finset (ZMod 7)) ⊆ cycIv i 5 by
    exact H b0 hb0 b1 hb1 b2 hb2 b3 hb3 hhit c0 hc0 c1 hc1 c2 hc2 c3 hc3
  decide

/-- `|Aₛ| = 3` propagation, pattern `{0,1,4}`: the `j = 2` digits already sit
in a 4-interval. -/
theorem prop3a (b0 b1 b2 : ZMod 7)
    (hb0 : b0 ∈ ({0, 1} : Finset (ZMod 7)))
    (hb1 : b1 ∈ ({2, 3} : Finset (ZMod 7)))
    (hb2 : b2 ∈ ({1, 2} : Finset (ZMod 7))) :
    ∃ i : ZMod 7, ({b0, b1, b2} : Finset (ZMod 7)) ⊆ cycIv i 4 := by
  suffices H : ∀ b0 : ZMod 7, b0 ∈ ({0, 1} : Finset (ZMod 7)) →
      ∀ b1 : ZMod 7, b1 ∈ ({2, 3} : Finset (ZMod 7)) →
      ∀ b2 : ZMod 7, b2 ∈ ({1, 2} : Finset (ZMod 7)) →
      ∃ i : ZMod 7, ({b0, b1, b2} : Finset (ZMod 7)) ⊆ cycIv i 4 by
    exact H b0 hb0 b1 hb1 b2 hb2
  decide

/-- `|Aₛ| = 3` propagation, pattern `{0,2,4}`: the `j = 4` digits sit in a
4-interval once the `j = 3` digits still hit `{2,3,4}` and `{3,4,5}`. -/
theorem prop3b (b0 b1 b2 : ZMod 7)
    (hb0 : b0 ∈ ({0, 1, 2} : Finset (ZMod 7)))
    (hb1 : b1 ∈ ({6, 0, 1} : Finset (ZMod 7)))
    (hb2 : b2 ∈ ({5, 6, 0} : Finset (ZMod 7)))
    (hh1 : (({b0, b1, b2} : Finset (ZMod 7)) ∩ ({2, 3, 4} : Finset (ZMod 7))).Nonempty)
    (hh2 : (({b0, b1, b2} : Finset (ZMod 7)) ∩ ({3, 4, 5} : Finset (ZMod 7))).Nonempty)
    (c0 c1 c2 : ZMod 7)
    (hc0 : c0 - b0 ∈ ({0, 1} : Finset (ZMod 7)))
    (hc1 : c1 - b1 - 2 ∈ ({0, 1} : Finset (ZMod 7)))
    (hc2 : c2 - b2 - 4 ∈ ({0, 1} : Finset (ZMod 7))) :
    ∃ i : ZMod 7, ({c0, c1, c2} : Finset (ZMod 7)) ⊆ cycIv i 4 := by
  suffices H : ∀ b0 : ZMod 7, b0 ∈ ({0, 1, 2} : Finset (ZMod 7)) →
      ∀ b1 : ZMod 7, b1 ∈ ({6, 0, 1} : Finset (ZMod 7)) →
      ∀ b2 : ZMod 7, b2 ∈ ({5, 6, 0} : Finset (ZMod 7)) →
      (({b0, b1, b2} : Finset (ZMod 7)) ∩ ({2, 3, 4} : Finset (ZMod 7))).Nonempty →
      (({b0, b1, b2} : Finset (ZMod 7)) ∩ ({3, 4, 5} : Finset (ZMod 7))).Nonempty →
      ∀ c0 : ZMod 7, c0 - b0 ∈ ({0, 1} : Finset (ZMod 7)) →
      ∀ c1 : ZMod 7, c1 - b1 - 2 ∈ ({0, 1} : Finset (ZMod 7)) →
      ∀ c2 : ZMod 7, c2 - b2 - 4 ∈ ({0, 1} : Finset (ZMod 7)) →
      ∃ i : ZMod 7, ({c0, c1, c2} : Finset (ZMod 7)) ⊆ cycIv i 4 by
    exact H b0 hb0 b1 hb1 b2 hb2 hh1 hh2 c0 hc0 c1 hc1 c2 hc2
  decide

/-- `|Aₛ| = 2` propagation, pattern `{0,2}`: `j = 3` gives one of
`(1,6), (2,0), (2,6)`; the first two die at `j = 4`, the last forces
`(3,1)` and dies at `j = 5`. -/
theorem prop2i (b0 b1 : ZMod 7)
    (hb0 : b0 ∈ ({0, 1, 2} : Finset (ZMod 7)))
    (hb1 : b1 ∈ ({6, 0, 1} : Finset (ZMod 7)))
    (hd : b1 - b0 ∉ ({0, 1, 6} : Finset (ZMod 7)))
    (c0 c1 : ZMod 7)
    (hc0 : c0 - b0 ∈ ({0, 1} : Finset (ZMod 7)))
    (hc1 : c1 - b1 - 2 ∈ ({0, 1} : Finset (ZMod 7)))
    (hdc : c1 - c0 ∉ ({0, 1, 6} : Finset (ZMod 7)))
    (e0 e1 : ZMod 7)
    (he0 : e0 - c0 ∈ ({0, 1} : Finset (ZMod 7)))
    (he1 : e1 - c1 - 2 ∈ ({0, 1} : Finset (ZMod 7))) :
    e1 - e0 ∈ ({0, 1, 6} : Finset (ZMod 7)) := by
  suffices H : ∀ b0 : ZMod 7, b0 ∈ ({0, 1, 2} : Finset (ZMod 7)) →
      ∀ b1 : ZMod 7, b1 ∈ ({6, 0, 1} : Finset (ZMod 7)) →
      b1 - b0 ∉ ({0, 1, 6} : Finset (ZMod 7)) →
      ∀ c0 : ZMod 7, c0 - b0 ∈ ({0, 1} : Finset (ZMod 7)) →
      ∀ c1 : ZMod 7, c1 - b1 - 2 ∈ ({0, 1} : Finset (ZMod 7)) →
      c1 - c0 ∉ ({0, 1, 6} : Finset (ZMod 7)) →
      ∀ e0 : ZMod 7, e0 - c0 ∈ ({0, 1} : Finset (ZMod 7)) →
      ∀ e1 : ZMod 7, e1 - c1 - 2 ∈ ({0, 1} : Finset (ZMod 7)) →
      e1 - e0 ∈ ({0, 1, 6} : Finset (ZMod 7)) by
    exact H b0 hb0 b1 hb1 hd c0 hc0 c1 hc1 hdc e0 he0 e1 he1
  decide

/-- `|Aₛ| = 2` propagation, pattern `{0,3}`: `j = 2` forces `(1,6)`, `j = 3`
forces `(1,3)`, and the `2 + 3` decomposition of `j = 5` lands in `{2,3}²`. -/
theorem prop2ii (b0 b1 : ZMod 7)
    (hb0 : b0 ∈ ({0, 1} : Finset (ZMod 7)))
    (hb1 : b1 ∈ ({6, 0} : Finset (ZMod 7)))
    (hd : b1 - b0 ∉ ({0, 1, 6} : Finset (ZMod 7)))
    (c0 c1 : ZMod 7)
    (hc0 : c0 - b0 ∈ ({0, 1} : Finset (ZMod 7)))
    (hc1 : c1 - b1 - 3 ∈ ({0, 1} : Finset (ZMod 7)))
    (hdc : c1 - c0 ∉ ({0, 1, 6} : Finset (ZMod 7)))
    (e0 e1 : ZMod 7)
    (he0 : e0 - b0 - c0 ∈ ({0, 1} : Finset (ZMod 7)))
    (he1 : e1 - b1 - c1 ∈ ({0, 1} : Finset (ZMod 7))) :
    e1 - e0 ∈ ({0, 1, 6} : Finset (ZMod 7)) := by
  suffices H : ∀ b0 : ZMod 7, b0 ∈ ({0, 1} : Finset (ZMod 7)) →
      ∀ b1 : ZMod 7, b1 ∈ ({6, 0} : Finset (ZMod 7)) →
      b1 - b0 ∉ ({0, 1, 6} : Finset (ZMod 7)) →
      ∀ c0 : ZMod 7, c0 - b0 ∈ ({0, 1} : Finset (ZMod 7)) →
      ∀ c1 : ZMod 7, c1 - b1 - 3 ∈ ({0, 1} : Finset (ZMod 7)) →
      c1 - c0 ∉ ({0, 1, 6} : Finset (ZMod 7)) →
      ∀ e0 : ZMod 7, e0 - b0 - c0 ∈ ({0, 1} : Finset (ZMod 7)) →
      ∀ e1 : ZMod 7, e1 - b1 - c1 ∈ ({0, 1} : Finset (ZMod 7)) →
      e1 - e0 ∈ ({0, 1, 6} : Finset (ZMod 7)) by
    exact H b0 hb0 b1 hb1 hd c0 hc0 c1 hc1 hdc e0 he0 e1 he1
  decide

/-- Membership in `{0,1}` is the same as `val ≤ 1`. -/
theorem mem_pair_iff_val {z : ZMod 7} :
    z ∈ ({0, 1} : Finset (ZMod 7)) ↔ z.val ≤ 1 := by
  revert z
  decide

/-- A `val ≤ 1` step: `a ∈ cycIv 0 j` and `b ∈ {0,1}` give `a + b ∈ cycIv 0 (j+1)`
when `j + 1 ≤ 7`. -/
theorem cycIv_zero_add {a b : ZMod 7} {j l : ℕ} (hj : j + l ≤ 7)
    (ha : a ∈ cycIv 0 j) (hb : b ∈ cycIv 0 l) : a + b ∈ cycIv 0 (j + l) := by
  simp only [cycIv, Finset.mem_filter, Finset.mem_univ, true_and, sub_zero]
    at ha hb ⊢
  have hav := ZMod.val_lt a
  have hbv := ZMod.val_lt b
  have hsum : a.val + b.val < 7 := by omega
  have : (a + b).val = a.val + b.val := ZMod.val_add_of_lt hsum
  omega
