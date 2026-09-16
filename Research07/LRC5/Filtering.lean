/-
Copyright (c) 2026 Research07 contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Research07 contributors
-/
import Research07.LRC5.Discrete

/-!
# Prime Filtering (descending-level multiplier lemma)

The specialized content of the Prime Filtering Lemma of Barajas–Serra
(Lemma 2 / Corollary 3 of arXiv:0710.4495) at `p = 5`, as needed for the
`|D| = 4` case.

Idea: process levels `i₀−1, i₀−2, …, 0` downwards. At level `j`, the
multiplier `1 + k·5^{m−j}` shifts the leading digit of every level-`j`
element by `k·runit(d)` — a bijection of `ZMod 5` since `runit(d) ≠ 0`.
Exactly two `k`'s per element are bad (those landing on digits `0` or `4`),
so `2·|level j| ≤ 4 < 5` guarantees a `k` good for the whole level, while
residues at levels `> j` are preserved verbatim.
-/

/-- Per-level choice: among the five shifts `k ∈ {0,…,4}`, at most
`2·|S|` are bad, hence one is simultaneously good when `2·|S| ≤ 4`. -/
theorem exists_k_all_good {m j : ℕ} (hjm : j < m) (S : Finset ℕ)
    (hS : ∀ d ∈ S, padicValNat 5 d = j) (hcard : 2 * S.card ≤ 4) :
    ∃ k : ℕ, k < 5 ∧ ∀ d ∈ S,
      1 ≤ (qdig m ((1 + k * 5 ^ (m - j)) * d)).val ∧
      (qdig m ((1 + k * 5 ^ (m - j)) * d)).val ≤ 3 := by
  sorry

/-- **Filtered multiplier construction** (Prime Filtering specialized to the
`{0,4}`-avoidance task): if every level below `i₀` has at most 2 elements,
some unit `λ` (a product of `Λ_j`-multipliers, hence `5 ∤ λ`) puts every
sub-`i₀` element's digit in `{1,2,3}` and preserves residues at levels
`≥ i₀` verbatim. -/
theorem filtered_multiplier (D : Finset ℕ) (hpos : ∀ d ∈ D, 0 < d) {m i₀ : ℕ}
    (hm : ∀ d ∈ D, padicValNat 5 d ≤ m) (hi₀ : i₀ ≤ m)
    (hlow : ∀ j, j < i₀ → 2 * (level D j).card ≤ 4) :
    ∃ lam : ℕ, ¬ 5 ∣ lam ∧
      (∀ d ∈ D, i₀ ≤ padicValNat 5 d →
        (lam * d) % 5 ^ (m + 1) = d % 5 ^ (m + 1)) ∧
      ∀ d ∈ D, padicValNat 5 d < i₀ →
        1 ≤ (qdig m (lam * d)).val ∧ (qdig m (lam * d)).val ≤ 3 := by
  sorry
