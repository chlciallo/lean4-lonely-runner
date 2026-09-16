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

NOTE on `exists_k_all_good`: the statement carries the side condition
`∀ d ∈ S, 0 < d`.  This is forced, because `padicValNat 5 0 = 0` would
otherwise let `d = 0` sit at level `j = 0`, where `qdig m (μ·0) = 0` is
never good; it is also the hypothesis needed to apply `runit_ne_zero`.
-/

/-- `qdig` depends only on the residue of `x` modulo `5^{m+1}`. -/
private theorem qdig_congr {m a b : ℕ} (h : a % 5 ^ (m + 1) = b % 5 ^ (m + 1)) :
    qdig m a = qdig m b := by
  unfold qdig
  rw [h]

/-- Multiplying by a non-multiple of `5` preserves the `5`-adic valuation. -/
private theorem padicValNat_mul_five {lam d : ℕ} (hlam : ¬ 5 ∣ lam) (hd : d ≠ 0) :
    padicValNat 5 (lam * d) = padicValNat 5 d := by
  have hlam0 : lam ≠ 0 := by rintro rfl; exact hlam (dvd_zero 5)
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  rw [padicValNat.mul hlam0 hd, padicValNat.eq_zero_of_not_dvd hlam, zero_add]

/-- Per-level choice: among the five shifts `k ∈ {0,…,4}`, at most
`2·|S|` are bad, hence one is simultaneously good when `2·|S| ≤ 4`. -/
theorem exists_k_all_good {m j : ℕ} (hjm : j < m) (S : Finset ℕ)
    (hS : ∀ d ∈ S, padicValNat 5 d = j) (hSpos : ∀ d ∈ S, 0 < d)
    (hcard : 2 * S.card ≤ 4) :
    ∃ k : ℕ, k < 5 ∧ ∀ d ∈ S,
      1 ≤ (qdig m ((1 + k * 5 ^ (m - j)) * d)).val ∧
      (qdig m ((1 + k * 5 ^ (m - j)) * d)).val ≤ 3 := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  -- For each `d`, `k ↦ qdig m d + k·runit d` is a bijection of `ZMod 5`,
  -- since `runit d ≠ 0` and `ZMod 5` is a field.
  have hbij : ∀ d ∈ S,
      Function.Bijective (fun k : ZMod 5 => qdig m d + k * runit d) := by
    intro d hd
    have hb : runit d ≠ 0 := runit_ne_zero (hSpos d hd)
    rw [← Finite.injective_iff_bijective]
    intro a b hab
    exact mul_right_cancel₀ hb (add_left_cancel hab)
  -- Consequently exactly two of the five shifts are bad for `d`
  -- (those landing on the digits `0` and `4`).
  have hbadcard : ∀ d ∈ S,
      (Finset.univ.filter (fun k : ZMod 5 =>
        ¬ (1 ≤ (qdig m d + k * runit d).val ∧
          (qdig m d + k * runit d).val ≤ 3))).card = 2 := by
    intro d hd
    rw [Finset.card_filter]
    calc (∑ k : ZMod 5, (if ¬ (1 ≤ (qdig m d + k * runit d).val ∧
              (qdig m d + k * runit d).val ≤ 3) then (1 : ℕ) else 0))
        = ∑ v : ZMod 5, (if ¬ (1 ≤ v.val ∧ v.val ≤ 3) then (1 : ℕ) else 0) :=
          Function.Bijective.sum_comp (hbij d hd)
            (fun v : ZMod 5 => if ¬ (1 ≤ v.val ∧ v.val ≤ 3) then (1 : ℕ) else 0)
      _ = 2 := by decide
  -- The union over `d ∈ S` of the bad-shift sets has size `≤ 2·|S| ≤ 4 < 5`.
  have hU : (S.biUnion (fun d => Finset.univ.filter (fun k : ZMod 5 =>
      ¬ (1 ≤ (qdig m d + k * runit d).val ∧
        (qdig m d + k * runit d).val ≤ 3)))).card ≤ 4 := by
    refine le_trans Finset.card_biUnion_le ?_
    calc ∑ d ∈ S, (Finset.univ.filter (fun k : ZMod 5 =>
            ¬ (1 ≤ (qdig m d + k * runit d).val ∧
              (qdig m d + k * runit d).val ≤ 3))).card
        = ∑ _d ∈ S, (2 : ℕ) :=
          Finset.sum_congr rfl fun d hd => hbadcard d hd
      _ = 2 * S.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ 4 := hcard
  -- So some `K : ZMod 5` is good for every `d ∈ S` simultaneously.
  have hnon : ((Finset.univ : Finset (ZMod 5)) \ S.biUnion (fun d =>
      Finset.univ.filter (fun k : ZMod 5 =>
        ¬ (1 ≤ (qdig m d + k * runit d).val ∧
          (qdig m d + k * runit d).val ≤ 3)))).Nonempty := by
    rw [← Finset.card_pos, Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    have hcu : (Finset.univ : Finset (ZMod 5)).card = 5 := by
      rw [Finset.card_univ, ZMod.card]
    omega
  obtain ⟨K, hK⟩ := hnon
  rw [Finset.mem_sdiff] at hK
  obtain ⟨hKu, hKB⟩ := hK
  have hgoodK : ∀ d ∈ S,
      1 ≤ (qdig m d + K * runit d).val ∧ (qdig m d + K * runit d).val ≤ 3 := by
    intro d hd
    have hKd : K ∉ Finset.univ.filter (fun k : ZMod 5 =>
        ¬ (1 ≤ (qdig m d + k * runit d).val ∧
          (qdig m d + k * runit d).val ≤ 3)) :=
      fun hmem => hKB (Finset.mem_biUnion.mpr ⟨d, hd, hmem⟩)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hKd
    exact hKd
  -- Take the natural lift `k = K.val < 5` of `K`.
  refine ⟨K.val, ZMod.val_lt K, fun d hd => ?_⟩
  have hq := qdig_multLow (k := K.val) hjm (hS d hd)
  rw [hq, ZMod.natCast_zmod_val K]
  exact hgoodK d hd

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
  classical
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  -- Induction on `t`: after handling levels `i₀−1 … i₀−t`, the partial
  -- multiplier `Lam` is good on levels `≥ i₀ − t` and verbatim on `≥ i₀`.
  have key : ∀ t : ℕ, t ≤ i₀ → ∃ lam : ℕ, ¬ 5 ∣ lam ∧
      (∀ d ∈ D, i₀ ≤ padicValNat 5 d →
        (lam * d) % 5 ^ (m + 1) = d % 5 ^ (m + 1)) ∧
      ∀ d ∈ D, i₀ - t ≤ padicValNat 5 d → padicValNat 5 d < i₀ →
        1 ≤ (qdig m (lam * d)).val ∧ (qdig m (lam * d)).val ≤ 3 := by
    intro t
    induction t with
    | zero =>
      intro _
      refine ⟨1, by decide, ?_, ?_⟩
      · intro d _ _; rw [one_mul]
      · intro d _ h1 h2; simp at h1; omega
    | succ t ih =>
      intro ht
      obtain ⟨Lam, hLam5, hver, hgd⟩ := ih (Nat.le_of_succ_le ht)
      have hLam0 : Lam ≠ 0 := by rintro rfl; exact hLam5 (dvd_zero 5)
      -- Process level `j = i₀ − (t+1)` via `exists_k_all_good` applied to
      -- the shifted level set `(Lam * ·) '' level D j`.
      set j := i₀ - (t + 1) with hj
      have hji : j < i₀ := by omega
      have hjm : j < m := by omega
      have hSval : ∀ x ∈ (level D j).image (fun d => Lam * d),
          padicValNat 5 x = j := by
        intro x hx
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
        obtain ⟨haD, haν⟩ := Finset.mem_filter.mp ha
        rw [padicValNat_mul_five hLam5 (ne_of_gt (hpos a haD)), haν]
      have hSpos : ∀ x ∈ (level D j).image (fun d => Lam * d), 0 < x := by
        intro x hx
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
        obtain ⟨haD, -⟩ := Finset.mem_filter.mp ha
        exact Nat.mul_pos (Nat.pos_of_ne_zero hLam0) (hpos a haD)
      have hScard : 2 * ((level D j).image (fun d => Lam * d)).card ≤ 4 := by
        have h1 : ((level D j).image (fun d => Lam * d)).card ≤ (level D j).card :=
          Finset.card_image_le
        have h2 := hlow j hji
        omega
      obtain ⟨k, hk5, hkg⟩ := exists_k_all_good hjm
        ((level D j).image (fun d => Lam * d)) hSval hSpos hScard
      -- The level-`j` multiplier `μ = 1 + k·5^{m−j}` is a unit mod 5.
      have h5pow : (5 : ℕ) ∣ 5 ^ (m - j) := by
        obtain ⟨e, he⟩ : ∃ e, m - j = e + 1 := ⟨m - j - 1, by omega⟩
        rw [he, pow_succ']
        exact dvd_mul_right 5 _
      have h5k : 5 ∣ k * 5 ^ (m - j) := dvd_mul_of_dvd_right h5pow k
      have hμ5 : ¬ 5 ∣ 1 + k * 5 ^ (m - j) := by
        intro h
        have h1 : 5 ∣ (1 + k * 5 ^ (m - j)) - k * 5 ^ (m - j) := Nat.dvd_sub h h5k
        rw [Nat.add_sub_cancel] at h1
        exact absurd (Nat.dvd_one.mp h1) (by decide)
      have hLam'5 : ¬ 5 ∣ (1 + k * 5 ^ (m - j)) * Lam :=
        Nat.Prime.not_dvd_mul Nat.prime_five hμ5 hLam5
      refine ⟨(1 + k * 5 ^ (m - j)) * Lam, hLam'5, ?_, ?_⟩
      · -- Levels `≥ i₀`: `μ` preserves the residue verbatim
        -- (`residN_multLow`, since `ν₅ (Lam·d) = ν₅ d ≥ i₀ > j`).
        intro d hd hν
        have hd0 : d ≠ 0 := ne_of_gt (hpos d hd)
        have hx : padicValNat 5 (Lam * d) = padicValNat 5 d :=
          padicValNat_mul_five hLam5 hd0
        have hjx : j < padicValNat 5 (Lam * d) := by rw [hx]; omega
        have h1 := residN_multLow (k := k) hjm hjx
        rw [mul_assoc, h1, hver d hd hν]
      · -- Levels `j ≤ ν₅ d < i₀`: new level via `hkg`, old levels preserved.
        intro d hd hνj hνi
        have hd0 : d ≠ 0 := ne_of_gt (hpos d hd)
        rcases eq_or_lt_of_le hνj with hEq | hLt
        · -- `ν₅ d = j`: `d` lies at the level just processed.
          have hdl : d ∈ level D j := Finset.mem_filter.mpr ⟨hd, hEq.symm⟩
          have hxS : Lam * d ∈ (level D j).image (fun d => Lam * d) :=
            Finset.mem_image.mpr ⟨d, hdl, rfl⟩
          have hg := hkg (Lam * d) hxS
          rwa [mul_assoc]
        · -- `ν₅ d > j`: `μ` preserves `Lam·d`'s residue, hence its digit.
          have hx : padicValNat 5 (Lam * d) = padicValNat 5 d :=
            padicValNat_mul_five hLam5 hd0
          have hjx : j < padicValNat 5 (Lam * d) := by rw [hx]; exact hLt
          have h1 := residN_multLow (k := k) hjm hjx
          have hqd : qdig m (((1 + k * 5 ^ (m - j)) * Lam) * d) = qdig m (Lam * d) := by
            apply qdig_congr
            rw [mul_assoc]; exact h1
          rw [hqd]
          exact hgd d hd (by omega) hνi
  -- `t = i₀` covers all levels `< i₀`; levels `≥ i₀` are verbatim.
  obtain ⟨lam, hlam5, hver, hgd⟩ := key i₀ le_rfl
  exact ⟨lam, hlam5, hver, fun d hd hlt => hgd d hd (by omega) hlt⟩
