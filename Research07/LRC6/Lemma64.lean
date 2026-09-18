/-
Copyright (c) 2026 Research07 contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Research07 contributors
-/
import Mathlib
import Research07.LRC6.Setup

/-!
# Renault Lemma 6.4 (combinatorial core, two-even case, safe domain)

Renault's Lemma 6.4: for three positions `x₃, x₄, x₅` already in `[1/6,5/6]`,
at least one of three alternatives holds:
(1) `λ = 2` puts all `⟨2xᵢ⟩` in `(1/6,5/6)`;
(2) some `α ∈ {1,5}` puts all `⟨xᵢ + α/6⟩` in `(1/6,5/6)`;
(3) some `(λ,α)` with `λ ∈ {3,5}`, `α ∈ {0,…,5}` puts all `⟨λxᵢ + α/6⟩` in
    `[1/6,5/6]`.

Self-contained interval-covering lemma over `ℝ`/`Int.fract`.
-/

noncomputable section

/-- `Int.fract z = z - n` when `z ∈ [n, n+1)` for integer-valued `n`. -/
private lemma fract_eq_sub (z : ℝ) (n : ℝ) (hn : ∃ k : ℤ, n = k)
    (h0 : n ≤ z) (h1 : z < n + 1) :
    Int.fract z = z - n := by
  obtain ⟨k, rfl⟩ := hn
  rw [Int.fract_eq_iff]
  exact ⟨by linarith, by linarith, k, by ring⟩

/-- For `y ∈ [0,1)` and `k ≤ 5`, `fract (y + k/6)` is `1/6`-safe iff
`y + k/6` lies in a safe arc `[1/6,5/6] ∪ [7/6,11/6]`. -/
private lemma safe6 {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y < 1) (k : ℝ) (hk : 0 ≤ k ∧ k ≤ 5) :
    Int.fract (y + k / 6) ∈ Set.Icc (1 / 6) (5 / 6) ↔
      (1 / 6 ≤ y + k / 6 ∧ y + k / 6 ≤ 5 / 6) ∨
        (7 / 6 ≤ y + k / 6 ∧ y + k / 6 ≤ 11 / 6) := by
  have h0 : 0 ≤ y + k / 6 := by linarith [hk.1]
  have h2 : y + k / 6 < 2 := by linarith [hk.2]
  rcases lt_or_ge (y + k / 6) 1 with hlt | hge
  · rw [Int.fract_eq_self.mpr ⟨h0, hlt⟩, Set.mem_Icc]
    constructor
    · intro h; exact Or.inl h
    · rintro (h | h)
      · exact h
      · exfalso; linarith
  · have hfz : Int.fract (y + k / 6) = y + k / 6 - 1 :=
      fract_eq_sub (y + k / 6) 1 ⟨1, by norm_num⟩ (by linarith) (by linarith)
    rw [hfz, Set.mem_Icc]
    constructor
    · rintro ⟨h3, h4⟩
      exact Or.inr ⟨by linarith, by linarith⟩
    · rintro (h | h)
      · exfalso; linarith
      · exact ⟨by linarith, by linarith⟩

/-- If `fract (y + k/6)` is unsafe, `y + k/6` lies in a bad band. -/
private lemma unsafe6 {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y < 1) (k : ℝ) (hk : 0 ≤ k ∧ k ≤ 5)
    (h : Int.fract (y + k / 6) ∉ Set.Icc (1 / 6) (5 / 6)) :
    (y + k / 6 < 1 / 6 ∨ 5 / 6 < y + k / 6) ∧
      (y + k / 6 < 7 / 6 ∨ 11 / 6 < y + k / 6) := by
  have h' := mt (safe6 hy0 hy1 k hk).mpr h
  rw [not_or] at h'
  obtain ⟨hA, hB⟩ := h'
  constructor
  · rcases not_and_or.mp hA with t | t
    · exact Or.inl (lt_of_not_ge t)
    · exact Or.inr (lt_of_not_ge t)
  · rcases not_and_or.mp hB with t | t
    · exact Or.inl (lt_of_not_ge t)
    · exact Or.inr (lt_of_not_ge t)

/-- `⟨2x⟩ ∉ (1/6,5/6)` forces `x ∈ [5/12,7/12]` on the safe domain. -/
private lemma key_mid {x : ℝ} (hx : x ∈ Set.Icc (1 / 6) (5 / 6))
    (h : Int.fract (2 * x) ∉ Set.Ioo (1 / 6) (5 / 6)) :
    x ∈ Set.Icc (5 / 12) (7 / 12) := by
  obtain ⟨hx1, hx2⟩ := Set.mem_Icc.mp hx
  rw [Set.mem_Ioo, not_and_or] at h
  by_cases h2x : 2 * x < 1
  · rw [Int.fract_eq_self.mpr ⟨by linarith, h2x⟩] at h
    rcases h with h | h <;> rw [not_lt] at h
    · exact ⟨by linarith, by linarith⟩
    · exact ⟨by linarith, by linarith⟩
  · have hf2 : Int.fract (2 * x) = 2 * x - 1 :=
      fract_eq_sub (2 * x) 1 ⟨1, by norm_num⟩ (by linarith) (by linarith)
    rw [hf2] at h
    rcases h with h | h <;> rw [not_lt] at h
    · exact ⟨by linarith, by linarith⟩
    · exfalso; linarith

/-- `⟨x + 1/6⟩ ∉ (1/6,5/6)` forces `x ≥ 2/3` on the safe domain. -/
private lemma key_hi {x : ℝ} (hx : x ∈ Set.Icc (1 / 6) (5 / 6))
    (h : Int.fract (x + 1 / 6) ∉ Set.Ioo (1 / 6) (5 / 6)) : 2 / 3 ≤ x := by
  obtain ⟨hx1, hx2⟩ := Set.mem_Icc.mp hx
  rw [Set.mem_Ioo, not_and_or] at h
  by_cases h2x : x + 1 / 6 < 1
  · rw [Int.fract_eq_self.mpr ⟨by linarith, h2x⟩] at h
    rcases h with h | h <;> rw [not_lt] at h <;> linarith
  · linarith

/-- `⟨x + 5/6⟩ ∉ (1/6,5/6)` forces `x ≤ 1/3` on the safe domain. -/
private lemma key_lo {x : ℝ} (hx : x ∈ Set.Icc (1 / 6) (5 / 6))
    (h : Int.fract (x + 5 / 6) ∉ Set.Ioo (1 / 6) (5 / 6)) : x ≤ 1 / 3 := by
  obtain ⟨hx1, hx2⟩ := Set.mem_Icc.mp hx
  rw [Set.mem_Ioo, not_and_or] at h
  have hf5 : Int.fract (x + 5 / 6) = x + 5 / 6 - 1 :=
    fract_eq_sub (x + 5 / 6) 1 ⟨1, by norm_num⟩ (by linarith) (by linarith)
  rw [hf5] at h
  rcases h with h | h <;> rw [not_lt] at h <;> linarith

set_option maxHeartbeats 400000 in
/-- The combinatorial heart of Lemma 6.4.  If `a` sits in the middle
`[5/12,7/12]`, `b` in `[1/6,1/3]` and `c` in `[2/3,5/6]`, then some
`(λ,α) ∈ {3,5} × {0,…,5}` makes all three shifted positions `1/6`-safe —
contradicting failure of alternative (3). -/
private lemma lemma6_4_core {a b c : ℝ}
    (ha : a ∈ Set.Icc (5 / 12) (7 / 12)) (hb : b ∈ Set.Icc (1 / 6) (1 / 3))
    (hc : c ∈ Set.Icc (2 / 3) (5 / 6))
    (hf : ∀ lam al : ℕ, (lam = 3 ∨ lam = 5) → al ≤ 5 →
        ¬(Int.fract ((lam : ℝ) * a + (al : ℝ) / 6) ∈ Set.Icc (1 / 6) (5 / 6) ∧
          Int.fract ((lam : ℝ) * b + (al : ℝ) / 6) ∈ Set.Icc (1 / 6) (5 / 6) ∧
          Int.fract ((lam : ℝ) * c + (al : ℝ) / 6) ∈ Set.Icc (1 / 6) (5 / 6))) :
    False := by
  obtain ⟨ha1, ha2⟩ := Set.mem_Icc.mp ha
  obtain ⟨hb1, hb2⟩ := Set.mem_Icc.mp hb
  obtain ⟨hc1, hc2⟩ := Set.mem_Icc.mp hc
  -- ⟨3a⟩ = 3a - 1 ∈ [1/4, 3/4];  ⟨3c⟩ = 3c - 2 ∈ [0, 1/2].
  have hfa : Int.fract (3 * a) = 3 * a - 1 :=
    fract_eq_sub (3 * a) 1 ⟨1, by norm_num⟩ (by linarith) (by linarith)
  have hfc : Int.fract (3 * c) = 3 * c - 2 :=
    fract_eq_sub (3 * c) 2 ⟨2, by norm_num⟩ (by linarith) (by linarith)
  have hfb : Int.fract (3 * b) = 3 * b ∨ Int.fract (3 * b) = 3 * b - 1 := by
    rcases lt_or_ge (3 * b) 1 with h | h
    · exact Or.inl (Int.fract_eq_self.mpr ⟨by linarith, h⟩)
    · exact Or.inr (fract_eq_sub (3 * b) 1 ⟨1, by norm_num⟩ (by linarith) (by linarith))
  -- ⟨3b⟩ ∈ [1/2, 1) ∪ {0}.
  have hvb : (1 / 2 ≤ Int.fract (3 * b) ∧ Int.fract (3 * b) < 1) ∨
      Int.fract (3 * b) = 0 := by
    rcases hfb with h | h
    · left
      exact ⟨by linarith, Int.fract_lt_one (3 * b)⟩
    · right
      have h0 := Int.fract_nonneg (3 * b)
      linarith
  have hu0 := Int.fract_nonneg (3 * a)
  have hu1 := Int.fract_lt_one (3 * a)
  have hv0 := Int.fract_nonneg (3 * b)
  have hv1 := Int.fract_lt_one (3 * b)
  have hw0 := Int.fract_nonneg (3 * c)
  have hw1 := Int.fract_lt_one (3 * c)
  -- ⟨3a⟩ is always `1/6`-safe.
  have hsa : Int.fract (3 * a) ∈ Set.Icc (1 / 6) (5 / 6) := by
    rw [hfa]
    exact ⟨by linarith, by linarith⟩
  -- Failure of (3, α), rewritten as shifts of the fractional parts.
  have F : ∀ k : ℝ, (∃ n : ℕ, k = n) → k ≤ 5 →
      ¬(Int.fract (Int.fract (3 * a) + k / 6) ∈ Set.Icc (1 / 6) (5 / 6) ∧
        Int.fract (Int.fract (3 * b) + k / 6) ∈ Set.Icc (1 / 6) (5 / 6) ∧
        Int.fract (Int.fract (3 * c) + k / 6) ∈ Set.Icc (1 / 6) (5 / 6)) := by
    intro k hkn hk hmem
    obtain ⟨n, rfl⟩ := hkn
    have hn5 : n ≤ 5 := by exact_mod_cast hk
    refine hf 3 n (Or.inl rfl) hn5 ?_
    simp only [Nat.cast_ofNat]
    rw [fract_self_add (3 * a) ((n : ℝ) / 6), fract_self_add (3 * b) ((n : ℝ) / 6),
      fract_self_add (3 * c) ((n : ℝ) / 6)]
    exact hmem
  -- Failure of (5, α).
  have G : ∀ k : ℝ, (∃ n : ℕ, k = n) → k ≤ 5 →
      ¬(Int.fract (Int.fract (5 * a) + k / 6) ∈ Set.Icc (1 / 6) (5 / 6) ∧
        Int.fract (Int.fract (5 * b) + k / 6) ∈ Set.Icc (1 / 6) (5 / 6) ∧
        Int.fract (Int.fract (5 * c) + k / 6) ∈ Set.Icc (1 / 6) (5 / 6)) := by
    intro k hkn hk hmem
    obtain ⟨n, rfl⟩ := hkn
    have hn5 : n ≤ 5 := by exact_mod_cast hk
    refine hf 5 n (Or.inr rfl) hn5 ?_
    simp only [Nat.cast_ofNat]
    rw [fract_self_add (5 * a) ((n : ℝ) / 6), fract_self_add (5 * b) ((n : ℝ) / 6),
      fract_self_add (5 * c) ((n : ℝ) / 6)]
    exact hmem
  -- (3,0) fails, so ⟨3b⟩ or ⟨3c⟩ is unsafe.
  have hF0 : ¬(Int.fract (3 * b) ∈ Set.Icc (1 / 6) (5 / 6) ∧
      Int.fract (3 * c) ∈ Set.Icc (1 / 6) (5 / 6)) := by
    have h := F 0 ⟨0, by norm_num⟩ (by norm_num)
    simp only [zero_div, add_zero, Int.fract_fract] at h
    exact fun hbc => h ⟨hsa, hbc⟩
  by_cases hbsafe : Int.fract (3 * b) ∈ Set.Icc (1 / 6) (5 / 6)
  · -- ===== Case B: ⟨3c⟩ < 1/6 =====
    have hcsafe : Int.fract (3 * c) ∉ Set.Icc (1 / 6) (5 / 6) :=
      fun hcc => hF0 ⟨hbsafe, hcc⟩
    have hw16 : Int.fract (3 * c) < 1 / 6 :=
      lt_of_not_ge (fun hge => hcsafe ⟨hge, by linarith [hfc]⟩)
    -- α = 4 ⇒ u < 1/2.
    have s4w : Int.fract (Int.fract (3 * c) + (4 : ℝ) / 6) ∈ Set.Icc (1 / 6) (5 / 6) :=
      (safe6 hw0 hw1 4 (by norm_num)).mpr (Or.inl ⟨by linarith, by linarith⟩)
    have s4v : Int.fract (Int.fract (3 * b) + (4 : ℝ) / 6) ∈ Set.Icc (1 / 6) (5 / 6) := by
      rcases hvb with ⟨hv1', hv2'⟩ | hv0'
      · exact (safe6 hv0 hv1 4 (by norm_num)).mpr (Or.inr ⟨by linarith, by linarith⟩)
      · rw [hv0']
        exact (safe6 le_rfl (by norm_num) 4 (by norm_num)).mpr
          (Or.inl ⟨by norm_num, by norm_num⟩)
    have u4 : Int.fract (Int.fract (3 * a) + (4 : ℝ) / 6) ∉ Set.Icc (1 / 6) (5 / 6) :=
      fun hu' => F 4 ⟨4, by norm_num⟩ (by norm_num) ⟨hu', s4v, s4w⟩
    obtain ⟨u4a, u4b⟩ := unsafe6 hu0 hu1 4 (by norm_num) u4
    have huB : Int.fract (3 * a) < 1 / 2 := by
      rcases u4a with h | h <;> rcases u4b with h' | h' <;> linarith
    -- α = 2 ⇒ v ∈ (1/2, 5/6).
    have s2w : Int.fract (Int.fract (3 * c) + (2 : ℝ) / 6) ∈ Set.Icc (1 / 6) (5 / 6) :=
      (safe6 hw0 hw1 2 (by norm_num)).mpr (Or.inl ⟨by linarith [hfc], by linarith [hfc]⟩)
    have s2u : Int.fract (Int.fract (3 * a) + (2 : ℝ) / 6) ∈ Set.Icc (1 / 6) (5 / 6) :=
      (safe6 hu0 hu1 2 (by norm_num)).mpr (Or.inl ⟨by linarith [hfa], by linarith [hfa]⟩)
    have v2 : Int.fract (Int.fract (3 * b) + (2 : ℝ) / 6) ∉ Set.Icc (1 / 6) (5 / 6) :=
      fun hv' => F 2 ⟨2, by norm_num⟩ (by norm_num) ⟨s2u, hv', s2w⟩
    obtain ⟨v2a, v2b⟩ := unsafe6 hv0 hv1 2 (by norm_num) v2
    have hvB : 1 / 2 < Int.fract (3 * b) ∧ Int.fract (3 * b) < 5 / 6 := by
      rcases v2a with h | h <;> rcases v2b with h' | h' <;> constructor <;> linarith
    -- α = 1 ⇒ v > 2/3.
    have s1w : Int.fract (Int.fract (3 * c) + (1 : ℝ) / 6) ∈ Set.Icc (1 / 6) (5 / 6) :=
      (safe6 hw0 hw1 1 (by norm_num)).mpr (Or.inl ⟨by linarith [hfc], by linarith [hfc]⟩)
    have s1u : Int.fract (Int.fract (3 * a) + (1 : ℝ) / 6) ∈ Set.Icc (1 / 6) (5 / 6) :=
      (safe6 hu0 hu1 1 (by norm_num)).mpr (Or.inl ⟨by linarith [hfa], by linarith [hfa]⟩)
    have v1 : Int.fract (Int.fract (3 * b) + (1 : ℝ) / 6) ∉ Set.Icc (1 / 6) (5 / 6) :=
      fun hv' => F 1 ⟨1, by norm_num⟩ (by norm_num) ⟨s1u, hv', s1w⟩
    obtain ⟨v1a, v1b⟩ := unsafe6 hv0 hv1 1 (by norm_num) v1
    have hvB2 : 2 / 3 < Int.fract (3 * b) := by
      rcases v1a with h | h <;> rcases v1b with h' | h' <;> linarith
    -- α = 3 ⇒ u > 1/3.
    have s3w : Int.fract (Int.fract (3 * c) + (3 : ℝ) / 6) ∈ Set.Icc (1 / 6) (5 / 6) :=
      (safe6 hw0 hw1 3 (by norm_num)).mpr (Or.inl ⟨by linarith [hfc], by linarith [hfc]⟩)
    have s3v : Int.fract (Int.fract (3 * b) + (3 : ℝ) / 6) ∈ Set.Icc (1 / 6) (5 / 6) :=
      (safe6 hv0 hv1 3 (by norm_num)).mpr (Or.inr ⟨by linarith [hvB2], by linarith [hvB.2]⟩)
    have u3 : Int.fract (Int.fract (3 * a) + (3 : ℝ) / 6) ∉ Set.Icc (1 / 6) (5 / 6) :=
      fun hu' => F 3 ⟨3, by norm_num⟩ (by norm_num) ⟨hu', s3v, s3w⟩
    obtain ⟨u3a, u3b⟩ := unsafe6 hu0 hu1 3 (by norm_num) u3
    have huB2 : 1 / 3 < Int.fract (3 * a) := by
      rcases u3a with h | h <;> rcases u3b with h' | h' <;> linarith
    -- α = 5 ⇒ w > 0.
    have s5u : Int.fract (Int.fract (3 * a) + (5 : ℝ) / 6) ∈ Set.Icc (1 / 6) (5 / 6) :=
      (safe6 hu0 hu1 5 (by norm_num)).mpr (Or.inr ⟨by linarith [huB2], by linarith [huB]⟩)
    have s5v : Int.fract (Int.fract (3 * b) + (5 : ℝ) / 6) ∈ Set.Icc (1 / 6) (5 / 6) :=
      (safe6 hv0 hv1 5 (by norm_num)).mpr (Or.inr ⟨by linarith [hvB2], by linarith [hvB.2]⟩)
    have w5 : Int.fract (Int.fract (3 * c) + (5 : ℝ) / 6) ∉ Set.Icc (1 / 6) (5 / 6) :=
      fun hw' => F 5 ⟨5, by norm_num⟩ (by norm_num) ⟨s5u, s5v, hw'⟩
    obtain ⟨w5a, w5b⟩ := unsafe6 hw0 hw1 5 (by norm_num) w5
    have hwB : 0 < Int.fract (3 * c) := by
      rcases w5a with h | h <;> rcases w5b with h' | h' <;> linarith
    -- Bounds: a ∈ (4/9,1/2), b ∈ (2/9,5/18), c ∈ (2/3,13/18).
    have hA : 4 / 9 < a ∧ a < 1 / 2 := ⟨by linarith [hfa], by linarith [hfa]⟩
    have hB : 2 / 9 < b ∧ b < 5 / 18 := by
      rcases hfb with h | h
      · exact ⟨by linarith [h], by linarith [h]⟩
      · exfalso; linarith [h]
    have hC : 2 / 3 < c ∧ c < 13 / 18 := ⟨by linarith [hfc], by linarith [hfc]⟩
    -- (λ,α) = (5,1) makes all three safe — contradiction.
    have g5a : Int.fract (5 * a) = 5 * a - 2 :=
      fract_eq_sub (5 * a) 2 ⟨2, by norm_num⟩ (by linarith [hA]) (by linarith [hA])
    have g5b : Int.fract (5 * b) = 5 * b - 1 :=
      fract_eq_sub (5 * b) 1 ⟨1, by norm_num⟩ (by linarith [hB]) (by linarith [hB])
    have g5c : Int.fract (5 * c) = 5 * c - 3 :=
      fract_eq_sub (5 * c) 3 ⟨3, by norm_num⟩ (by linarith [hC]) (by linarith [hC])
    have t1a : Int.fract (Int.fract (5 * a) + (1 : ℝ) / 6) ∈ Set.Icc (1 / 6) (5 / 6) := by
      rw [g5a]
      exact (safe6 (by linarith [hA]) (by linarith [hA]) 1 (by norm_num)).mpr
        (Or.inl ⟨by linarith [hA], by linarith [hA]⟩)
    have t1b : Int.fract (Int.fract (5 * b) + (1 : ℝ) / 6) ∈ Set.Icc (1 / 6) (5 / 6) := by
      rw [g5b]
      exact (safe6 (by linarith [hB]) (by linarith [hB]) 1 (by norm_num)).mpr
        (Or.inl ⟨by linarith [hB], by linarith [hB]⟩)
    have t1c : Int.fract (Int.fract (5 * c) + (1 : ℝ) / 6) ∈ Set.Icc (1 / 6) (5 / 6) := by
      rw [g5c]
      exact (safe6 (by linarith [hC]) (by linarith [hC]) 1 (by norm_num)).mpr
        (Or.inl ⟨by linarith [hC], by linarith [hC]⟩)
    exact G 1 ⟨1, by norm_num⟩ (by norm_num) ⟨t1a, t1b, t1c⟩
  · -- ===== Case A: ⟨3b⟩ ∈ (5/6,1) ∪ {0} =====
    have hvcase : 5 / 6 < Int.fract (3 * b) ∨ Int.fract (3 * b) = 0 := by
      rcases hvb with ⟨hv1', hv2'⟩ | hv0'
      · exact Or.inl (lt_of_not_ge (fun hle => hbsafe ⟨by linarith, hle⟩))
      · exact Or.inr hv0'
    -- α = 2 ⇒ u > 1/2.
    have s2v : Int.fract (Int.fract (3 * b) + (2 : ℝ) / 6) ∈ Set.Icc (1 / 6) (5 / 6) := by
      rcases hvcase with hv | hv
      · exact (safe6 hv0 hv1 2 (by norm_num)).mpr (Or.inr ⟨by linarith, by linarith⟩)
      · rw [hv]
        exact (safe6 le_rfl (by norm_num) 2 (by norm_num)).mpr
          (Or.inl ⟨by norm_num, by norm_num⟩)
    have s2w : Int.fract (Int.fract (3 * c) + (2 : ℝ) / 6) ∈ Set.Icc (1 / 6) (5 / 6) :=
      (safe6 hw0 hw1 2 (by norm_num)).mpr (Or.inl ⟨by linarith [hfc], by linarith [hfc]⟩)
    have u2 : Int.fract (Int.fract (3 * a) + (2 : ℝ) / 6) ∉ Set.Icc (1 / 6) (5 / 6) :=
      fun hu' => F 2 ⟨2, by norm_num⟩ (by norm_num) ⟨hu', s2v, s2w⟩
    obtain ⟨u2a, u2b⟩ := unsafe6 hu0 hu1 2 (by norm_num) u2
    have huA : 1 / 2 < Int.fract (3 * a) := by
      rcases u2a with h | h <;> rcases u2b with h' | h' <;> linarith
    -- α = 4 ⇒ w > 1/6.
    have s4v : Int.fract (Int.fract (3 * b) + (4 : ℝ) / 6) ∈ Set.Icc (1 / 6) (5 / 6) := by
      rcases hvcase with hv | hv
      · exact (safe6 hv0 hv1 4 (by norm_num)).mpr (Or.inr ⟨by linarith, by linarith⟩)
      · rw [hv]
        exact (safe6 le_rfl (by norm_num) 4 (by norm_num)).mpr
          (Or.inl ⟨by norm_num, by norm_num⟩)
    have s4u : Int.fract (Int.fract (3 * a) + (4 : ℝ) / 6) ∈ Set.Icc (1 / 6) (5 / 6) :=
      (safe6 hu0 hu1 4 (by norm_num)).mpr (Or.inr ⟨by linarith [hfa], by linarith [hfa]⟩)
    have w4 : Int.fract (Int.fract (3 * c) + (4 : ℝ) / 6) ∉ Set.Icc (1 / 6) (5 / 6) :=
      fun hw' => F 4 ⟨4, by norm_num⟩ (by norm_num) ⟨s4u, s4v, hw'⟩
    obtain ⟨w4a, w4b⟩ := unsafe6 hw0 hw1 4 (by norm_num) w4
    have hwA : 1 / 6 < Int.fract (3 * c) := by
      rcases w4a with h | h <;> rcases w4b with h' | h' <;> linarith
    -- α = 5 ⇒ w < 1/3.
    have s5v : Int.fract (Int.fract (3 * b) + (5 : ℝ) / 6) ∈ Set.Icc (1 / 6) (5 / 6) := by
      rcases hvcase with hv | hv
      · exact (safe6 hv0 hv1 5 (by norm_num)).mpr (Or.inr ⟨by linarith, by linarith⟩)
      · rw [hv]
        exact (safe6 le_rfl (by norm_num) 5 (by norm_num)).mpr
          (Or.inl ⟨by norm_num, by norm_num⟩)
    have s5u : Int.fract (Int.fract (3 * a) + (5 : ℝ) / 6) ∈ Set.Icc (1 / 6) (5 / 6) :=
      (safe6 hu0 hu1 5 (by norm_num)).mpr (Or.inr ⟨by linarith [hfa], by linarith [hfa]⟩)
    have w5 : Int.fract (Int.fract (3 * c) + (5 : ℝ) / 6) ∉ Set.Icc (1 / 6) (5 / 6) :=
      fun hw' => F 5 ⟨5, by norm_num⟩ (by norm_num) ⟨s5u, s5v, hw'⟩
    obtain ⟨w5a, w5b⟩ := unsafe6 hw0 hw1 5 (by norm_num) w5
    have hwA2 : Int.fract (3 * c) < 1 / 3 := by
      rcases w5a with h | h <;> rcases w5b with h' | h' <;> linarith
    -- α = 3 ⇒ u < 2/3.
    have s3v : Int.fract (Int.fract (3 * b) + (3 : ℝ) / 6) ∈ Set.Icc (1 / 6) (5 / 6) := by
      rcases hvcase with hv | hv
      · exact (safe6 hv0 hv1 3 (by norm_num)).mpr (Or.inr ⟨by linarith, by linarith⟩)
      · rw [hv]
        exact (safe6 le_rfl (by norm_num) 3 (by norm_num)).mpr
          (Or.inl ⟨by norm_num, by norm_num⟩)
    have s3w : Int.fract (Int.fract (3 * c) + (3 : ℝ) / 6) ∈ Set.Icc (1 / 6) (5 / 6) :=
      (safe6 hw0 hw1 3 (by norm_num)).mpr (Or.inl ⟨by linarith [hfc], by linarith [hfc]⟩)
    have u3 : Int.fract (Int.fract (3 * a) + (3 : ℝ) / 6) ∉ Set.Icc (1 / 6) (5 / 6) :=
      fun hu' => F 3 ⟨3, by norm_num⟩ (by norm_num) ⟨hu', s3v, s3w⟩
    obtain ⟨u3a, u3b⟩ := unsafe6 hu0 hu1 3 (by norm_num) u3
    have huA2 : Int.fract (3 * a) < 2 / 3 := by
      rcases u3a with h | h <;> rcases u3b with h' | h' <;> linarith
    -- α = 1 ⇒ v ≠ 0, hence v > 5/6.
    have s1u : Int.fract (Int.fract (3 * a) + (1 : ℝ) / 6) ∈ Set.Icc (1 / 6) (5 / 6) :=
      (safe6 hu0 hu1 1 (by norm_num)).mpr (Or.inl ⟨by linarith [hfa], by linarith [hfa]⟩)
    have s1w : Int.fract (Int.fract (3 * c) + (1 : ℝ) / 6) ∈ Set.Icc (1 / 6) (5 / 6) :=
      (safe6 hw0 hw1 1 (by norm_num)).mpr (Or.inl ⟨by linarith [hfc], by linarith [hfc]⟩)
    have v1 : Int.fract (Int.fract (3 * b) + (1 : ℝ) / 6) ∉ Set.Icc (1 / 6) (5 / 6) :=
      fun hv' => F 1 ⟨1, by norm_num⟩ (by norm_num) ⟨s1u, hv', s1w⟩
    obtain ⟨v1a, v1b⟩ := unsafe6 hv0 hv1 1 (by norm_num) v1
    have hvA : 5 / 6 < Int.fract (3 * b) := by
      rcases v1a with h | h <;> rcases v1b with h' | h' <;>
        rcases hvcase with hv | hv <;> linarith
    -- Bounds: a ∈ (1/2,5/9), b ∈ (5/18,1/3), c ∈ (13/18,7/9).
    have hA : 1 / 2 < a ∧ a < 5 / 9 := ⟨by linarith [hfa], by linarith [hfa]⟩
    have hB : 5 / 18 < b ∧ b < 1 / 3 := by
      rcases hfb with h | h
      · exact ⟨by linarith [h], by linarith [h]⟩
      · exfalso; linarith [h]
    have hC : 13 / 18 < c ∧ c < 7 / 9 := ⟨by linarith [hfc], by linarith [hfc]⟩
    -- (λ,α) = (5,5) makes all three safe — contradiction.
    have g5a : Int.fract (5 * a) = 5 * a - 2 :=
      fract_eq_sub (5 * a) 2 ⟨2, by norm_num⟩ (by linarith [hA]) (by linarith [hA])
    have g5b : Int.fract (5 * b) = 5 * b - 1 :=
      fract_eq_sub (5 * b) 1 ⟨1, by norm_num⟩ (by linarith [hB]) (by linarith [hB])
    have g5c : Int.fract (5 * c) = 5 * c - 3 :=
      fract_eq_sub (5 * c) 3 ⟨3, by norm_num⟩ (by linarith [hC]) (by linarith [hC])
    have t5a : Int.fract (Int.fract (5 * a) + (5 : ℝ) / 6) ∈ Set.Icc (1 / 6) (5 / 6) := by
      rw [g5a]
      exact (safe6 (by linarith [hA]) (by linarith [hA]) 5 (by norm_num)).mpr
        (Or.inr ⟨by linarith [hA], by linarith [hA]⟩)
    have t5b : Int.fract (Int.fract (5 * b) + (5 : ℝ) / 6) ∈ Set.Icc (1 / 6) (5 / 6) := by
      rw [g5b]
      exact (safe6 (by linarith [hB]) (by linarith [hB]) 5 (by norm_num)).mpr
        (Or.inr ⟨by linarith [hB], by linarith [hB]⟩)
    have t5c : Int.fract (Int.fract (5 * c) + (5 : ℝ) / 6) ∈ Set.Icc (1 / 6) (5 / 6) := by
      rw [g5c]
      exact (safe6 (by linarith [hC]) (by linarith [hC]) 5 (by norm_num)).mpr
        (Or.inr ⟨by linarith [hC], by linarith [hC]⟩)
    exact G 5 ⟨5, by norm_num⟩ (by norm_num) ⟨t5a, t5b, t5c⟩

set_option maxHeartbeats 400000 in
/-- Renault Lemma 6.4. -/
theorem lemma6_4 {x₃ x₄ x₅ : ℝ}
    (h3 : x₃ ∈ Set.Icc (1 / 6) (5 / 6)) (h4 : x₄ ∈ Set.Icc (1 / 6) (5 / 6))
    (h5 : x₅ ∈ Set.Icc (1 / 6) (5 / 6)) :
    (Int.fract (2 * x₃) ∈ Set.Ioo (1 / 6) (5 / 6) ∧
        Int.fract (2 * x₄) ∈ Set.Ioo (1 / 6) (5 / 6) ∧
        Int.fract (2 * x₅) ∈ Set.Ioo (1 / 6) (5 / 6))
    ∨
    (∃ al : ℕ, (al = 1 ∨ al = 5) ∧
        Int.fract (x₃ + (al : ℝ) / 6) ∈ Set.Ioo (1 / 6) (5 / 6) ∧
        Int.fract (x₄ + (al : ℝ) / 6) ∈ Set.Ioo (1 / 6) (5 / 6) ∧
        Int.fract (x₅ + (al : ℝ) / 6) ∈ Set.Ioo (1 / 6) (5 / 6))
    ∨
    (∃ lam al : ℕ, (lam = 3 ∨ lam = 5) ∧ al ≤ 5 ∧
        Int.fract ((lam : ℝ) * x₃ + (al : ℝ) / 6) ∈ Set.Icc (1 / 6) (5 / 6) ∧
        Int.fract ((lam : ℝ) * x₄ + (al : ℝ) / 6) ∈ Set.Icc (1 / 6) (5 / 6) ∧
        Int.fract ((lam : ℝ) * x₅ + (al : ℝ) / 6) ∈ Set.Icc (1 / 6) (5 / 6)) := by
  by_contra h
  -- Negations of the three alternatives.
  have nA : ¬(Int.fract (2 * x₃) ∈ Set.Ioo (1 / 6) (5 / 6) ∧
      Int.fract (2 * x₄) ∈ Set.Ioo (1 / 6) (5 / 6) ∧
      Int.fract (2 * x₅) ∈ Set.Ioo (1 / 6) (5 / 6)) := fun t => h (Or.inl t)
  have nB : ∀ al : ℕ, (al = 1 ∨ al = 5) →
      ¬(Int.fract (x₃ + (al : ℝ) / 6) ∈ Set.Ioo (1 / 6) (5 / 6) ∧
        Int.fract (x₄ + (al : ℝ) / 6) ∈ Set.Ioo (1 / 6) (5 / 6) ∧
        Int.fract (x₅ + (al : ℝ) / 6) ∈ Set.Ioo (1 / 6) (5 / 6)) := by
    intro al hal t
    exact h (Or.inr (Or.inl ⟨al, hal, t⟩))
  have nC : ∀ lam al : ℕ, (lam = 3 ∨ lam = 5) → al ≤ 5 →
      ¬(Int.fract ((lam : ℝ) * x₃ + (al : ℝ) / 6) ∈ Set.Icc (1 / 6) (5 / 6) ∧
        Int.fract ((lam : ℝ) * x₄ + (al : ℝ) / 6) ∈ Set.Icc (1 / 6) (5 / 6) ∧
        Int.fract ((lam : ℝ) * x₅ + (al : ℝ) / 6) ∈ Set.Icc (1 / 6) (5 / 6)) := by
    intro lam al hl hle t
    exact h (Or.inr (Or.inr ⟨lam, al, hl, hle, t⟩))
  obtain ⟨hx3, hx3'⟩ := Set.mem_Icc.mp h3
  obtain ⟨hx4, hx4'⟩ := Set.mem_Icc.mp h4
  obtain ⟨hx5, hx5'⟩ := Set.mem_Icc.mp h5
  -- Failure of (1): some runner sits in the middle third.
  have Dmid : x₃ ∈ Set.Icc (5 / 12) (7 / 12) ∨ x₄ ∈ Set.Icc (5 / 12) (7 / 12) ∨
      x₅ ∈ Set.Icc (5 / 12) (7 / 12) := by
    by_contra hd
    push Not at hd
    obtain ⟨d3, d4, d5⟩ := hd
    apply nA
    refine ⟨?_, ?_, ?_⟩ <;> by_contra q
    · exact d3 (key_mid h3 q)
    · exact d4 (key_mid h4 q)
    · exact d5 (key_mid h5 q)
  -- Failure of (2) at α = 1: some runner is high.
  have Dhi : 2 / 3 ≤ x₃ ∨ 2 / 3 ≤ x₄ ∨ 2 / 3 ≤ x₅ := by
    by_contra hd
    push Not at hd
    obtain ⟨d3, d4, d5⟩ := hd
    apply nB 1 (Or.inl rfl)
    simp only [Nat.cast_one]
    refine ⟨?_, ?_, ?_⟩ <;> by_contra q
    · exact absurd (key_hi h3 q) (not_le.mpr d3)
    · exact absurd (key_hi h4 q) (not_le.mpr d4)
    · exact absurd (key_hi h5 q) (not_le.mpr d5)
  -- Failure of (2) at α = 5: some runner is low.
  have Dlo : x₃ ≤ 1 / 3 ∨ x₄ ≤ 1 / 3 ∨ x₅ ≤ 1 / 3 := by
    by_contra hd
    push Not at hd
    obtain ⟨d3, d4, d5⟩ := hd
    apply nB 5 (Or.inr rfl)
    simp only [Nat.cast_ofNat]
    refine ⟨?_, ?_, ?_⟩ <;> by_contra q
    · exact absurd (key_lo h3 q) (not_le.mpr d3)
    · exact absurd (key_lo h4 q) (not_le.mpr d4)
    · exact absurd (key_lo h5 q) (not_le.mpr d5)
  -- The three witnesses must be distinct runners: 27 cases, 6 viable.
  rcases Dmid with m3 | m4 | m5 <;>
    rcases Dhi with g3 | g4 | g5 <;>
    rcases Dlo with l3 | l4 | l5 <;>
    simp only [Set.mem_Icc] at * <;>
    first
    | linarith
    | exact lemma6_4_core m3 ⟨hx4, l4⟩ ⟨g5, hx5'⟩
        (fun lam al hl hle t => nC lam al hl hle ⟨t.1, t.2.1, t.2.2⟩)
    | exact lemma6_4_core m3 ⟨hx5, l5⟩ ⟨g4, hx4'⟩
        (fun lam al hl hle t => nC lam al hl hle ⟨t.1, t.2.2, t.2.1⟩)
    | exact lemma6_4_core m4 ⟨hx3, l3⟩ ⟨g5, hx5'⟩
        (fun lam al hl hle t => nC lam al hl hle ⟨t.2.1, t.1, t.2.2⟩)
    | exact lemma6_4_core m4 ⟨hx5, l5⟩ ⟨g3, hx3'⟩
        (fun lam al hl hle t => nC lam al hl hle ⟨t.2.2, t.1, t.2.1⟩)
    | exact lemma6_4_core m5 ⟨hx3, l3⟩ ⟨g4, hx4'⟩
        (fun lam al hl hle t => nC lam al hl hle ⟨t.2.1, t.2.2, t.1⟩)
    | exact lemma6_4_core m5 ⟨hx4, l4⟩ ⟨g3, hx3'⟩
        (fun lam al hl hle t => nC lam al hl hle ⟨t.2.2, t.2.1, t.1⟩)

end
