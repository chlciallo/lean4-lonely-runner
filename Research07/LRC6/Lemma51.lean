/-
Copyright (c) 2026 Research07 contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Research07 contributors
-/
import Mathlib
import Research07.LRC6.Setup

/-!
# Renault Lemma 5.1 (combinatorial core, unique-even case)

Renault's Lemma 5.1: for three positions `x₃, x₄, x₅ ∈ [0,1)`, either some
`(λ,α)` with `λ ∈ {2,…,5}`, `α ∈ {1,…,5}` puts all `⟨λxᵢ + α/6⟩` in `[1/6,5/6]`,
or some `α ∈ {1,2,4}` puts all `⟨xᵢ + α/6⟩` in the open `(1/6,5/6)`.

This is a self-contained interval-covering lemma over `ℝ`/`Int.fract`.
-/

noncomputable section

/-- If `k ≤ y < k+1` for `k : ℤ`, then `fract y = y - k`. -/
private lemma fract_eq_sub_of_mem {y : ℝ} {k : ℤ} (h1 : (k : ℝ) ≤ y)
    (h2 : y < (k : ℝ) + 1) : Int.fract y = y - (k : ℝ) := by
  rw [Int.fract_eq_iff]
  refine ⟨by linarith, by linarith, k, ?_⟩
  ring

/-- The bad-arc conversion: for `u ∈ [0,1)` and `al ∈ {1,…,5}`,
`fract (u + al/6) ∉ [1/6,5/6]` iff `u` lies in the open third
`((5-al)/6, (7-al)/6)`.  This is the `⟨λxᵢ + α/6⟩ ∈ (5/6,1/6) ⇔
⟨λxᵢ⟩ ∈ ((5-α)/6,(7-α)/6)` shift of Renault's proof. -/
private lemma bad_iff {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) {al : ℕ}
    (ha1 : 1 ≤ al) (ha5 : al ≤ 5) :
    Int.fract (u + (al : ℝ) / 6) ∉ Set.Icc (1 / 6) (5 / 6) ↔
      u ∈ Set.Ioo ((5 - (al : ℝ)) / 6) ((7 - (al : ℝ)) / 6) := by
  have ha1' : (1 : ℝ) ≤ al := by exact_mod_cast ha1
  have ha5' : (al : ℝ) ≤ 5 := by exact_mod_cast ha5
  set y := u + (al : ℝ) / 6 with hy
  have hy1 : (1 : ℝ) / 6 ≤ y := by rw [hy]; linarith
  have hy2 : y < (11 : ℝ) / 6 := by rw [hy]; linarith
  have key : Int.fract y ∈ Set.Icc (1 / 6) (5 / 6) ↔
      (y ∈ Set.Icc ((1 : ℝ) / 6) (5 / 6)) ∨ (y ∈ Set.Icc ((7 : ℝ) / 6) (11 / 6)) := by
    constructor
    · intro h
      rw [Set.mem_Icc] at h
      obtain ⟨h1', h2'⟩ := h
      have hfl : y - (⌊y⌋ : ℝ) = Int.fract y := Int.self_sub_floor y
      have hklo : (-1 : ℝ) < (⌊y⌋ : ℝ) := by linarith
      have hkhi : (⌊y⌋ : ℝ) < 2 := by linarith
      have k0 : ⌊y⌋ = 0 ∨ ⌊y⌋ = 1 := by
        have e1 : ⌊y⌋ < 2 := by exact_mod_cast hkhi
        have e2 : -1 < ⌊y⌋ := by exact_mod_cast hklo
        omega
      rcases k0 with hkk | hkk
      · left
        rw [hkk] at hfl
        norm_num at hfl
        rw [Set.mem_Icc]; constructor <;> linarith
      · right
        rw [hkk] at hfl
        norm_num at hfl
        rw [Set.mem_Icc]; constructor <;> linarith
    · rintro (h | h)
      · rw [Set.mem_Icc] at h
        obtain ⟨h1', h2'⟩ := h
        rw [Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩, Set.mem_Icc]
        exact ⟨h1', h2'⟩
      · rw [Set.mem_Icc] at h
        obtain ⟨h1', h2'⟩ := h
        have hf : Int.fract y = y - 1 := by
          have hh : Int.fract (y - 1) = Int.fract y := by
            have h0 := Int.fract_sub_intCast y (1 : ℤ)
            rw [Int.cast_one] at h0
            exact h0
          rw [Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩] at hh
          linarith
        rw [hf, Set.mem_Icc]
        constructor <;> linarith
  rw [key, Set.mem_Ioo]
  constructor
  · intro h
    rw [not_or, Set.mem_Icc, Set.mem_Icc] at h
    obtain ⟨hA, hB⟩ := h
    have hygt : (5 : ℝ) / 6 < y := by
      by_contra hc
      rw [not_lt] at hc
      exact hA ⟨hy1, hc⟩
    have hylt : y < (7 : ℝ) / 6 := by
      by_contra hc
      rw [not_lt] at hc
      exact hB ⟨hc, hy2.le⟩
    rw [hy] at hygt hylt
    constructor <;> linarith
  · rintro ⟨h1', h2'⟩
    have hyg : (5 : ℝ) / 6 < y ∧ y < (7 : ℝ) / 6 := by rw [hy]; constructor <;> linarith
    rw [not_or, Set.mem_Icc, Set.mem_Icc]
    constructor
    · rintro ⟨hp1, hp2⟩; linarith [hyg.1]
    · rintro ⟨hq1, hq2⟩; linarith [hyg.2]

/-- Backward propagation: `fract (lam·x) ∈ Ioo p q` puts `x` in a preimage
interval `((n+p)/lam,(n+q)/lam)` for some `0 ≤ n < lam`. -/
private lemma mul_preimage {x : ℝ} {lam : ℕ} (hl : 0 < lam)
    (hx : x ∈ Set.Ico 0 1) {p q : ℝ}
    (h : Int.fract ((lam : ℝ) * x) ∈ Set.Ioo p q) :
    ∃ n : ℤ, 0 ≤ n ∧ n < (lam : ℤ) ∧
      x ∈ Set.Ioo (((n : ℝ) + p) / lam) (((n : ℝ) + q) / lam) := by
  rw [Set.mem_Ioo] at h
  obtain ⟨h1, h2⟩ := h
  have hl' : (0 : ℝ) < lam := by exact_mod_cast hl
  have hx0 : 0 ≤ x := hx.1
  have hx1 : x < 1 := hx.2
  refine ⟨⌊(lam : ℝ) * x⌋, ?_, ?_, ?_⟩
  · apply Int.floor_nonneg.mpr
    exact mul_nonneg hl'.le hx0
  · have h1' : (lam : ℝ) * x < lam := by
      calc (lam : ℝ) * x < (lam : ℝ) * 1 := mul_lt_mul_of_pos_left hx1 hl'
        _ = lam := by ring
    have hfl := Int.floor_le ((lam : ℝ) * x)
    have hlt : (⌊(lam : ℝ) * x⌋ : ℝ) < lam := by linarith
    exact_mod_cast hlt
  · rw [Set.mem_Ioo]
    have hfl : (lam : ℝ) * x - (⌊(lam : ℝ) * x⌋ : ℝ) = Int.fract ((lam : ℝ) * x) :=
      Int.self_sub_floor _
    constructor
    · rw [div_lt_iff₀ hl']
      have hnf : (⌊(lam : ℝ) * x⌋ : ℝ) = (lam : ℝ) * x - Int.fract ((lam : ℝ) * x) := by
        linarith
      nlinarith
    · rw [lt_div_iff₀ hl']
      have hnf : (⌊(lam : ℝ) * x⌋ : ℝ) = (lam : ℝ) * x - Int.fract ((lam : ℝ) * x) := by
        linarith
      nlinarith

/-- The `lam = 2` preimage: `fract (2x) ∈ Ioo p q` iff `x` lies in one of the two
preimage halves. -/
private lemma preimage2 {x : ℝ} (hx : x ∈ Set.Ico 0 1) {p q : ℝ}
    (h : Int.fract (2 * x) ∈ Set.Ioo p q) :
    x ∈ Set.Ioo (p / 2) (q / 2) ∨ x ∈ Set.Ioo ((1 + p) / 2) ((1 + q) / 2) := by
  rw [Set.mem_Ioo] at h
  obtain ⟨h1, h2⟩ := h
  have hx0 : 0 ≤ x := hx.1
  have hx1 : x < 1 := hx.2
  have hfl : 2 * x - (⌊2 * x⌋ : ℝ) = Int.fract (2 * x) := Int.self_sub_floor _
  have hk : ⌊2 * x⌋ = 0 ∨ ⌊2 * x⌋ = 1 := by
    have hge : 0 ≤ ⌊2 * x⌋ := Int.floor_nonneg.mpr (mul_nonneg (by norm_num) hx0)
    have hlt : (⌊2 * x⌋ : ℝ) < 2 := by
      have hfl2 := Int.floor_le (2 * x)
      linarith
    have e1 : ⌊2 * x⌋ < 2 := by exact_mod_cast hlt
    omega
  rcases hk with hkk | hkk
  · left
    rw [hkk] at hfl
    norm_num at hfl
    rw [Set.mem_Ioo]
    constructor <;> linarith
  · right
    rw [hkk] at hfl
    norm_num at hfl
    rw [Set.mem_Ioo]
    constructor <;> linarith

/-- Forward propagation: on a branch `x ∈ Ioo a b` lying inside
`[n/lam, (n+1)/lam]`, `fract (lam·x) ∈ Ioo (lam·a - n) (lam·b - n)`. -/
private lemma fract_mul_Ioo {x : ℝ} {lam : ℕ} (hl : 0 < lam) {n : ℤ} {a b : ℝ}
    (h1 : (n : ℝ) ≤ (lam : ℝ) * a) (h2 : (lam : ℝ) * b ≤ (n : ℝ) + 1)
    (hx : x ∈ Set.Ioo a b) :
    Int.fract ((lam : ℝ) * x) ∈ Set.Ioo ((lam : ℝ) * a - (n : ℝ)) ((lam : ℝ) * b - (n : ℝ)) := by
  rw [Set.mem_Ioo] at hx ⊢
  obtain ⟨hxa, hxb⟩ := hx
  have hl' : (0 : ℝ) < lam := by exact_mod_cast hl
  have hL : (lam : ℝ) * a < (lam : ℝ) * x := mul_lt_mul_of_pos_left hxa hl'
  have hR : (lam : ℝ) * x < (lam : ℝ) * b := mul_lt_mul_of_pos_left hxb hl'
  have hfr : Int.fract ((lam : ℝ) * x) = (lam : ℝ) * x - (n : ℝ) := by
    apply fract_eq_sub_of_mem <;> linarith
  rw [hfr]
  constructor <;> linarith

/-- Exhibiting property (2): if `x ∈ Ioo a b` and `a + al/6, b + al/6` sit
strictly inside `(n+1/6, n+5/6)`, then `fract (x + al/6) ∈ Ioo (1/6) (5/6)`. -/
private lemma fract_add6_Ioo {x : ℝ} {al : ℕ} {n : ℤ} {a b : ℝ}
    (hlo : (n : ℝ) + 1 / 6 ≤ a + (al : ℝ) / 6) (hhi : b + (al : ℝ) / 6 ≤ (n : ℝ) + 5 / 6)
    (hx : x ∈ Set.Ioo a b) :
    Int.fract (x + (al : ℝ) / 6) ∈ Set.Ioo (1 / 6) (5 / 6) := by
  rw [Set.mem_Ioo] at hx ⊢
  obtain ⟨hxa, hxb⟩ := hx
  have hfr : Int.fract (x + (al : ℝ) / 6) = x + (al : ℝ) / 6 - (n : ℝ) := by
    apply fract_eq_sub_of_mem <;> linarith
  rw [hfr]
  constructor <;> linarith

/-- The six-permutation disjunction expressing "exactly one of `a,b,c` lies in
each open third `(0,1/3)`, `(1/3,2/3)`, `(2/3,1)`".  `abbrev` (reducible) so that
`rcases`/`exact` see through it. -/
private abbrev Thirds (a b c : ℝ) : Prop :=
  (a ∈ Set.Ioo 0 (1 / 3) ∧ b ∈ Set.Ioo (1 / 3) (2 / 3) ∧ c ∈ Set.Ioo (2 / 3) 1) ∨
  (a ∈ Set.Ioo 0 (1 / 3) ∧ c ∈ Set.Ioo (1 / 3) (2 / 3) ∧ b ∈ Set.Ioo (2 / 3) 1) ∨
  (b ∈ Set.Ioo 0 (1 / 3) ∧ a ∈ Set.Ioo (1 / 3) (2 / 3) ∧ c ∈ Set.Ioo (2 / 3) 1) ∨
  (b ∈ Set.Ioo 0 (1 / 3) ∧ c ∈ Set.Ioo (1 / 3) (2 / 3) ∧ a ∈ Set.Ioo (2 / 3) 1) ∨
  (c ∈ Set.Ioo 0 (1 / 3) ∧ a ∈ Set.Ioo (1 / 3) (2 / 3) ∧ b ∈ Set.Ioo (2 / 3) 1) ∨
  (c ∈ Set.Ioo 0 (1 / 3) ∧ b ∈ Set.Ioo (1 / 3) (2 / 3) ∧ a ∈ Set.Ioo (2 / 3) 1)

/-- Renault's counting: three values in `[0,1)`, each bad-arc `B_al`
(`al ∈ {1,…,5}`) containing one of them, forces exactly one value in each open
third — a bijection `runner ↔ third`. -/
private lemma one_per_third {a b c : ℝ}
    (_ha : a ∈ Set.Ico 0 1) (_hb : b ∈ Set.Ico 0 1) (_hc : c ∈ Set.Ico 0 1)
    (hT1 : a ∈ Set.Ioo 0 (1 / 3) ∨ b ∈ Set.Ioo 0 (1 / 3) ∨ c ∈ Set.Ioo 0 (1 / 3))
    (hT2 : a ∈ Set.Ioo (1 / 3) (2 / 3) ∨ b ∈ Set.Ioo (1 / 3) (2 / 3) ∨
      c ∈ Set.Ioo (1 / 3) (2 / 3))
    (hT3 : a ∈ Set.Ioo (2 / 3) 1 ∨ b ∈ Set.Ioo (2 / 3) 1 ∨ c ∈ Set.Ioo (2 / 3) 1) :
    Thirds a b c := by
  rcases hT1 with h1 | h1 | h1 <;> rcases hT2 with h2 | h2 | h2 <;>
    rcases hT3 with h3 | h3 | h3 <;>
    first
      | exact Or.inl ⟨h1, h2, h3⟩
      | exact Or.inr (Or.inl ⟨h1, h2, h3⟩)
      | exact Or.inr (Or.inr (Or.inl ⟨h1, h2, h3⟩))
      | exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2, h3⟩)))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2, h3⟩))))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h1, h2, h3⟩))))
      | (exfalso; rw [Set.mem_Ioo] at h1 h2 h3; linarith)

/-- `fract (a + y) = fract (a + fract y)`. -/
private lemma fract_add_int_right (a y : ℝ) :
    Int.fract (a + y) = Int.fract (a + Int.fract y) := by
  have h : a + y = (a + Int.fract y) + (⌊y⌋ : ℝ) := by
    have h2 := Int.self_sub_fract y
    linarith
  rw [h, Int.fract_add_intCast]

/-- `⟨4x⟩ = ⟨x + ⟨3x⟩⟩`. -/
private lemma fract4_eq (x : ℝ) :
    Int.fract ((4 : ℝ) * x) = Int.fract (x + Int.fract ((3 : ℝ) * x)) := by
  rw [show (4 : ℝ) * x = x + (3 : ℝ) * x by ring, fract_add_int_right]

/-- `⟨5x⟩ = ⟨x + ⟨4x⟩⟩`. -/
private lemma fract5_eq' (x : ℝ) :
    Int.fract ((5 : ℝ) * x) = Int.fract (x + Int.fract ((4 : ℝ) * x)) := by
  rw [show (5 : ℝ) * x = x + (4 : ℝ) * x by ring, fract_add_int_right]

/-- `⟨5x⟩ = ⟨⟨3x⟩ + ⟨2x⟩⟩`. -/
private lemma fract5_eq (x : ℝ) :
    Int.fract ((5 : ℝ) * x) =
      Int.fract (Int.fract ((3 : ℝ) * x) + Int.fract ((2 : ℝ) * x)) := by
  rw [show (5 : ℝ) * x = (3 : ℝ) * x + (2 : ℝ) * x by ring, fract_self_add,
    fract_add_int_right]

/-- Forward propagation for a sum: if `u ∈ Ioo a b`, `v ∈ Ioo c d` and
`a+c, b+d ⊆ [n, n+1]`, then `fract (u+v) ∈ Ioo (a+c-n) (b+d-n)`. -/
private lemma fract_add_Ioo {u v : ℝ} {n : ℤ} {a b c d : ℝ}
    (h1 : (n : ℝ) ≤ a + c) (h2 : b + d ≤ (n : ℝ) + 1)
    (hu : u ∈ Set.Ioo a b) (hv : v ∈ Set.Ioo c d) :
    Int.fract (u + v) ∈ Set.Ioo (a + c - (n : ℝ)) (b + d - (n : ℝ)) := by
  rw [Set.mem_Ioo] at hu hv ⊢
  obtain ⟨hua, hub⟩ := hu
  obtain ⟨hvc, hvd⟩ := hv
  have hfr : Int.fract (u + v) = u + v - (n : ℝ) := by
    apply fract_eq_sub_of_mem <;> linarith
  rw [hfr]
  constructor <;> linarith

/-- A sum `s ∈ (a, b)` crossing `1` wraps: `fract s ≤ b-1` or `a < fract s`. -/
private lemma fract_wrap {s a b : ℝ} (ha : 0 ≤ a) (hb2 : b ≤ 2)
    (h1 : a < s) (h2 : s < b) :
    Int.fract s ≤ b - 1 ∨ a < Int.fract s := by
  by_cases hs : s < 1
  · right
    rw [Int.fract_eq_self.mpr ⟨by linarith, hs⟩]
    exact h1
  · left
    have hfr : Int.fract s = s - 1 := by
      have h := fract_eq_sub_of_mem (k := 1) (y := s)
        (by push_cast; exact not_lt.mp hs) (by push_cast; linarith)
      rwa [Int.cast_one] at h
    rw [hfr]
    linarith

/-- Branch selection: if `u` lies in `Ioo a b ∪ Ioo c d` and `fract (lam·u)`
lies in `Ioo p q` disjoint from the image `(lam·c-n, lam·d-n)` of the second
branch, then `u ∈ Ioo a b`. -/
private lemma branch_pick {u : ℝ} {lam : ℕ} (hl : 0 < lam) {n : ℤ} {a b c d p q : ℝ}
    (h1 : (n : ℝ) ≤ (lam : ℝ) * c) (h2 : (lam : ℝ) * d ≤ (n : ℝ) + 1)
    (hd : (lam : ℝ) * d - (n : ℝ) ≤ p ∨ q ≤ (lam : ℝ) * c - (n : ℝ))
    (hpre : u ∈ Set.Ioo a b ∨ u ∈ Set.Ioo c d)
    (hf : Int.fract ((lam : ℝ) * u) ∈ Set.Ioo p q) :
    u ∈ Set.Ioo a b := by
  rcases hpre with h | h
  · exact h
  · exfalso
    have hJ := fract_mul_Ioo hl h1 h2 h
    rw [Set.mem_Ioo] at hJ hf
    rcases hd with hd | hd <;> linarith [hJ.1, hJ.2, hf.1, hf.2]

/-- `Thirds` eliminator: which value lies in `(0,1/3)`, with the other two
bounded below by `1/3`. -/
private lemma thirds_T1 {a b c : ℝ} (h : Thirds a b c) :
    (a ∈ Set.Ioo 0 (1 / 3) ∧ (1 / 3 : ℝ) < b ∧ (1 / 3 : ℝ) < c) ∨
    (b ∈ Set.Ioo 0 (1 / 3) ∧ (1 / 3 : ℝ) < a ∧ (1 / 3 : ℝ) < c) ∨
    (c ∈ Set.Ioo 0 (1 / 3) ∧ (1 / 3 : ℝ) < a ∧ (1 / 3 : ℝ) < b) := by
  rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ |
    ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;>
    rw [Set.mem_Ioo] at h1 h2 h3
  · exact Or.inl ⟨h1, h2.1, by linarith [h3.1]⟩
  · exact Or.inl ⟨h1, by linarith [h3.1], h2.1⟩
  · exact Or.inr (Or.inl ⟨h1, h2.1, by linarith [h3.1]⟩)
  · exact Or.inr (Or.inl ⟨h1, by linarith [h3.1], h2.1⟩)
  · exact Or.inr (Or.inr ⟨h1, h2.1, by linarith [h3.1]⟩)
  · exact Or.inr (Or.inr ⟨h1, by linarith [h3.1], h2.1⟩)

/-- `Thirds` eliminator: which value lies in `(2/3,1)`, with the other two
bounded above by `2/3`. -/
private lemma thirds_T3 {a b c : ℝ} (h : Thirds a b c) :
    (a ∈ Set.Ioo (2 / 3) 1 ∧ b < (2 / 3 : ℝ) ∧ c < (2 / 3 : ℝ)) ∨
    (b ∈ Set.Ioo (2 / 3) 1 ∧ a < (2 / 3 : ℝ) ∧ c < (2 / 3 : ℝ)) ∨
    (c ∈ Set.Ioo (2 / 3) 1 ∧ a < (2 / 3 : ℝ) ∧ b < (2 / 3 : ℝ)) := by
  rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ |
    ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;>
    rw [Set.mem_Ioo] at h1 h2 h3
  · exact Or.inr (Or.inr ⟨h3, by linarith [h1.2], h2.2⟩)
  · exact Or.inr (Or.inl ⟨h3, by linarith [h1.2], h2.2⟩)
  · exact Or.inr (Or.inr ⟨h3, h2.2, by linarith [h1.2]⟩)
  · exact Or.inl ⟨h3, by linarith [h1.2], h2.2⟩
  · exact Or.inr (Or.inl ⟨h3, h2.2, by linarith [h1.2]⟩)
  · exact Or.inl ⟨h3, h2.2, by linarith [h1.2]⟩

/-- No two of `a,c` may both lie in the closed middle third `[1/3,2/3]`. -/
private lemma thirds_T2_unique {a b c : ℝ} (h : Thirds a b c)
    (ha : a ∈ Set.Icc (1 / 3) (2 / 3)) (hc : c ∈ Set.Icc (1 / 3) (2 / 3)) :
    False := by
  rw [Set.mem_Icc] at ha hc
  rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ |
    ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;>
    rw [Set.mem_Ioo] at h1 h2 h3 <;>
    linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, ha.1, ha.2, hc.1, hc.2]

/-- A `fract` value below `2/3` cannot occupy the upper `(3/4,1)` preimage
branch, so it lies in `(1/4,1/2)`. -/
private lemma low_branch {f : ℝ} (hlt : f < (2 / 3 : ℝ))
    (h : f ∈ Set.Ioo (3 / 4) 1 ∨ f ∈ Set.Ioo (1 / 4) (1 / 2)) :
    f ∈ Set.Ioo (1 / 4) (1 / 2) := by
  rcases h with h | h
  · exfalso
    rw [Set.mem_Ioo] at h
    linarith [h.1, hlt]
  · exact h

/-- λ = 2, case (a): the `T1`-runner has `⟨2u⟩ ∈ (0,1/6)`.  Here `u,v,w` are the
three runners in role order (`u` the `(0,1/3)`-runner, `v` the `(1/3,2/3)`-runner,
`w` the `(2/3,1)`-runner at λ = 2).  `hbad` is the bad-arc disjunction for the
negated property (1); `hgood` is the negated property (2). -/
private lemma lam2_caseA {u v w : ℝ}
    (hu : u ∈ Set.Ico 0 1) (hv : v ∈ Set.Ico 0 1) (hw : w ∈ Set.Ico 0 1)
    (hbad : ∀ (lam al : ℕ), 2 ≤ lam → lam ≤ 5 → 1 ≤ al → al ≤ 5 →
        Int.fract ((lam : ℝ) * u) ∈ Set.Ioo ((5 - (al : ℝ)) / 6) ((7 - (al : ℝ)) / 6) ∨
        Int.fract ((lam : ℝ) * v) ∈ Set.Ioo ((5 - (al : ℝ)) / 6) ((7 - (al : ℝ)) / 6) ∨
        Int.fract ((lam : ℝ) * w) ∈ Set.Ioo ((5 - (al : ℝ)) / 6) ((7 - (al : ℝ)) / 6))
    (hgood : ∀ (al : ℕ), (al = 1 ∨ al = 2 ∨ al = 4) →
        Int.fract (u + (al : ℝ) / 6) ∈ Set.Ioo (1 / 6) (5 / 6) →
        Int.fract (v + (al : ℝ) / 6) ∈ Set.Ioo (1 / 6) (5 / 6) →
        Int.fract (w + (al : ℝ) / 6) ∈ Set.Ioo (1 / 6) (5 / 6) → False)
    (hAu : Int.fract (2 * u) ∈ Set.Ioo 0 (1 / 6))
    (hvT : Int.fract (2 * v) ∈ Set.Ioo (1 / 3) (2 / 3))
    (hwT : Int.fract (2 * w) ∈ Set.Ioo (2 / 3) 1) : False := by
  -- The one-per-third structure at λ = 3, built from `hbad`.
  have hT : Thirds (Int.fract (3 * u)) (Int.fract (3 * v)) (Int.fract (3 * w)) := by
    have c1 := hbad 3 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have c2 := hbad 3 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have c3 := hbad 3 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    norm_num at c1 c2 c3
    apply one_per_third
    · exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
    · exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
    · exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
    · rcases c1 with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    · rcases c2 with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    · rcases c3 with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
  -- Case-(a) refinements: `⟨2v⟩ ∈ (1/3,1/2)` and `⟨2w⟩ ∈ (2/3,5/6)`.
  have hv2 : Int.fract (2 * v) ∈ Set.Ioo (1 / 3) (1 / 2) := by
    have c := hbad 2 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    norm_num at c
    rcases c with h | h | h
    · exfalso
      rw [Set.mem_Ioo] at hAu
      linarith [h.1, hAu.2]
    · rw [Set.mem_Ioo] at hvT
      exact ⟨hvT.1, h.2⟩
    · exfalso
      rw [Set.mem_Ioo] at hwT
      linarith [h.2, hwT.1]
  have hw2 : Int.fract (2 * w) ∈ Set.Ioo (2 / 3) (5 / 6) := by
    have c := hbad 2 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    norm_num at c
    rcases c with h | h | h
    · exfalso
      rw [Set.mem_Ioo] at hAu
      linarith [h.1, hAu.2]
    · exfalso
      rw [Set.mem_Ioo] at hv2
      linarith [h.1, hv2.2]
    · rw [Set.mem_Ioo] at hwT
      exact ⟨hwT.1, h.2⟩
  -- λ = 2 preimages.
  have pu : u ∈ Set.Ioo 0 (1 / 12) ∨ u ∈ Set.Ioo (1 / 2) (7 / 12) := by
    rcases preimage2 hu hAu with h | h
    · exact Or.inl (Set.Ioo_subset_Ioo (by norm_num) (by norm_num) h)
    · exact Or.inr (Set.Ioo_subset_Ioo (by norm_num) (by norm_num) h)
  have pv : v ∈ Set.Ioo (1 / 6) (1 / 4) ∨ v ∈ Set.Ioo (2 / 3) (3 / 4) := by
    rcases preimage2 hv hv2 with h | h
    · exact Or.inl (Set.Ioo_subset_Ioo (by norm_num) (by norm_num) h)
    · exact Or.inr (Set.Ioo_subset_Ioo (by norm_num) (by norm_num) h)
  have pw : w ∈ Set.Ioo (1 / 3) (5 / 12) ∨ w ∈ Set.Ioo (5 / 6) (11 / 12) := by
    rcases preimage2 hw hw2 with h | h
    · exact Or.inl (Set.Ioo_subset_Ioo (by norm_num) (by norm_num) h)
    · exact Or.inr (Set.Ioo_subset_Ioo (by norm_num) (by norm_num) h)
  -- λ = 3 forward images: each `⟨3·⟩ ∈ (0,1/4) ∪ (1/2,3/4)`.
  have fu3 : Int.fract (3 * u) ∈ Set.Ioo 0 (1 / 4) ∨
      Int.fract (3 * u) ∈ Set.Ioo (1 / 2) (3 / 4) := by
    rcases pu with h | h
    · exact Or.inl (Set.Ioo_subset_Ioo (by norm_num) (by norm_num)
        (fract_mul_Ioo (by norm_num : (0 : ℕ) < 3) (n := 0) (by norm_num) (by norm_num) h))
    · exact Or.inr (Set.Ioo_subset_Ioo (by norm_num) (by norm_num)
        (fract_mul_Ioo (by norm_num : (0 : ℕ) < 3) (n := 1) (by norm_num) (by norm_num) h))
  have fv3 : Int.fract (3 * v) ∈ Set.Ioo (1 / 2) (3 / 4) ∨
      Int.fract (3 * v) ∈ Set.Ioo 0 (1 / 4) := by
    rcases pv with h | h
    · exact Or.inl (Set.Ioo_subset_Ioo (by norm_num) (by norm_num)
        (fract_mul_Ioo (by norm_num : (0 : ℕ) < 3) (n := 0) (by norm_num) (by norm_num) h))
    · exact Or.inr (Set.Ioo_subset_Ioo (by norm_num) (by norm_num)
        (fract_mul_Ioo (by norm_num : (0 : ℕ) < 3) (n := 2) (by norm_num) (by norm_num) h))
  have fw3 : Int.fract (3 * w) ∈ Set.Ioo 0 (1 / 4) ∨
      Int.fract (3 * w) ∈ Set.Ioo (1 / 2) (3 / 4) := by
    rcases pw with h | h
    · exact Or.inl (Set.Ioo_subset_Ioo (by norm_num) (by norm_num)
        (fract_mul_Ioo (by norm_num : (0 : ℕ) < 3) (n := 1) (by norm_num) (by norm_num) h))
    · exact Or.inr (Set.Ioo_subset_Ioo (by norm_num) (by norm_num)
        (fract_mul_Ioo (by norm_num : (0 : ℕ) < 3) (n := 2) (by norm_num) (by norm_num) h))
  -- Exactly one runner lies in `(0,1/3)` at λ = 3; three subcases.
  rcases thirds_T1 hT with ⟨huT1, hvgt, hwgt⟩ | ⟨hvT1, hugt, hwgt⟩ |
    ⟨hwT1, hugt, hvgt⟩
  · -- `⟨3u⟩ ∈ (0,1/3)`: forces `u ∈ (0,1/12)`, `v ∈ (1/6,1/4)`, `w ∈ (5/6,11/12)`;
    -- then `α = 2` satisfies property (2).
    have huI : u ∈ Set.Ioo 0 (1 / 12) :=
      branch_pick (lam := 3) (by norm_num) (n := 1) (by norm_num) (by norm_num)
        (Or.inr (by norm_num)) pu huT1
    have hvI : v ∈ Set.Ioo (1 / 6) (1 / 4) :=
      branch_pick (lam := 3) (by norm_num) (n := 2) (by norm_num) (by norm_num)
        (Or.inl (by norm_num)) pv ⟨hvgt, Int.fract_lt_one _⟩
    have hwI : w ∈ Set.Ioo (5 / 6) (11 / 12) :=
      branch_pick (lam := 3) (by norm_num) (n := 1) (by norm_num) (by norm_num)
        (Or.inl (by norm_num)) pw.symm ⟨hwgt, Int.fract_lt_one _⟩
    exact hgood 2 (Or.inr (Or.inl rfl))
      (fract_add6_Ioo (al := 2) (n := 0) (by norm_num) (by norm_num) huI)
      (fract_add6_Ioo (al := 2) (n := 0) (by norm_num) (by norm_num) hvI)
      (fract_add6_Ioo (al := 2) (n := 1) (by norm_num) (by norm_num) hwI)
  · -- `⟨3v⟩ ∈ (0,1/3)`: `u ∈ (1/2,7/12)`, `v ∈ (2/3,3/4)`, `w ∈ (5/6,11/12)`; `α = 4`.
    have huI : u ∈ Set.Ioo (1 / 2) (7 / 12) :=
      branch_pick (lam := 3) (by norm_num) (n := 0) (by norm_num) (by norm_num)
        (Or.inl (by norm_num)) pu.symm ⟨hugt, Int.fract_lt_one _⟩
    have hvI : v ∈ Set.Ioo (2 / 3) (3 / 4) :=
      branch_pick (lam := 3) (by norm_num) (n := 0) (by norm_num) (by norm_num)
        (Or.inr (by norm_num)) pv.symm hvT1
    have hwI : w ∈ Set.Ioo (5 / 6) (11 / 12) :=
      branch_pick (lam := 3) (by norm_num) (n := 1) (by norm_num) (by norm_num)
        (Or.inl (by norm_num)) pw.symm ⟨hwgt, Int.fract_lt_one _⟩
    exact hgood 4 (Or.inr (Or.inr rfl))
      (fract_add6_Ioo (al := 4) (n := 1) (by norm_num) (by norm_num) huI)
      (fract_add6_Ioo (al := 4) (n := 1) (by norm_num) (by norm_num) hvI)
      (fract_add6_Ioo (al := 4) (n := 1) (by norm_num) (by norm_num) hwI)
  · -- `⟨3w⟩ ∈ (0,1/3)`: `u ∈ (1/2,7/12)`, `v ∈ (1/6,1/4)`, `w ∈ (1/3,5/12)`; `α = 1`.
    have huI : u ∈ Set.Ioo (1 / 2) (7 / 12) :=
      branch_pick (lam := 3) (by norm_num) (n := 0) (by norm_num) (by norm_num)
        (Or.inl (by norm_num)) pu.symm ⟨hugt, Int.fract_lt_one _⟩
    have hvI : v ∈ Set.Ioo (1 / 6) (1 / 4) :=
      branch_pick (lam := 3) (by norm_num) (n := 2) (by norm_num) (by norm_num)
        (Or.inl (by norm_num)) pv ⟨hvgt, Int.fract_lt_one _⟩
    have hwI : w ∈ Set.Ioo (1 / 3) (5 / 12) :=
      branch_pick (lam := 3) (by norm_num) (n := 2) (by norm_num) (by norm_num)
        (Or.inr (by norm_num)) pw hwT1
    exact hgood 1 (Or.inl rfl)
      (fract_add6_Ioo (al := 1) (n := 0) (by norm_num) (by norm_num) huI)
      (fract_add6_Ioo (al := 1) (n := 0) (by norm_num) (by norm_num) hvI)
      (fract_add6_Ioo (al := 1) (n := 0) (by norm_num) (by norm_num) hwI)

/-- λ = 2, case (b): the `T3`-runner has `⟨2u⟩ ∈ (5/6,1)`.  Role order: `u` the
`(2/3,1)`-runner, `v` the `(1/3,2/3)`-runner, `w` the `(0,1/3)`-runner at λ = 2. -/
private lemma lam2_caseB {u v w : ℝ}
    (hu : u ∈ Set.Ico 0 1) (hv : v ∈ Set.Ico 0 1) (hw : w ∈ Set.Ico 0 1)
    (hbad : ∀ (lam al : ℕ), 2 ≤ lam → lam ≤ 5 → 1 ≤ al → al ≤ 5 →
        Int.fract ((lam : ℝ) * u) ∈ Set.Ioo ((5 - (al : ℝ)) / 6) ((7 - (al : ℝ)) / 6) ∨
        Int.fract ((lam : ℝ) * v) ∈ Set.Ioo ((5 - (al : ℝ)) / 6) ((7 - (al : ℝ)) / 6) ∨
        Int.fract ((lam : ℝ) * w) ∈ Set.Ioo ((5 - (al : ℝ)) / 6) ((7 - (al : ℝ)) / 6))
    (hgood : ∀ (al : ℕ), (al = 1 ∨ al = 2 ∨ al = 4) →
        Int.fract (u + (al : ℝ) / 6) ∈ Set.Ioo (1 / 6) (5 / 6) →
        Int.fract (v + (al : ℝ) / 6) ∈ Set.Ioo (1 / 6) (5 / 6) →
        Int.fract (w + (al : ℝ) / 6) ∈ Set.Ioo (1 / 6) (5 / 6) → False)
    (hAu : Int.fract (2 * u) ∈ Set.Ioo (5 / 6) 1)
    (hvT : Int.fract (2 * v) ∈ Set.Ioo (1 / 3) (2 / 3))
    (hwT : Int.fract (2 * w) ∈ Set.Ioo 0 (1 / 3)) : False := by
  have hT : Thirds (Int.fract (3 * u)) (Int.fract (3 * v)) (Int.fract (3 * w)) := by
    have c1 := hbad 3 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have c2 := hbad 3 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have c3 := hbad 3 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    norm_num at c1 c2 c3
    apply one_per_third
    · exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
    · exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
    · exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
    · rcases c1 with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    · rcases c2 with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    · rcases c3 with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
  -- Case-(b) refinements: `⟨2v⟩ ∈ (1/2,2/3)` and `⟨2w⟩ ∈ (1/6,1/3)`.
  have hv2 : Int.fract (2 * v) ∈ Set.Ioo (1 / 2) (2 / 3) := by
    have c := hbad 2 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    norm_num at c
    rcases c with h | h | h
    · exfalso
      rw [Set.mem_Ioo] at hAu
      linarith [h.2, hAu.1]
    · rw [Set.mem_Ioo] at hvT
      exact ⟨h.1, hvT.2⟩
    · exfalso
      rw [Set.mem_Ioo] at hwT
      linarith [h.1, hwT.2]
  have hw2 : Int.fract (2 * w) ∈ Set.Ioo (1 / 6) (1 / 3) := by
    have c := hbad 2 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    norm_num at c
    rcases c with h | h | h
    · exfalso
      rw [Set.mem_Ioo] at hAu
      linarith [h.2, hAu.1]
    · exfalso
      rw [Set.mem_Ioo] at hv2
      linarith [h.2, hv2.1]
    · rw [Set.mem_Ioo] at hwT
      exact ⟨h.1, hwT.2⟩
  -- λ = 2 preimages.
  have pu : u ∈ Set.Ioo (5 / 12) (1 / 2) ∨ u ∈ Set.Ioo (11 / 12) 1 := by
    rcases preimage2 hu hAu with h | h
    · exact Or.inl (Set.Ioo_subset_Ioo (by norm_num) (by norm_num) h)
    · exact Or.inr (Set.Ioo_subset_Ioo (by norm_num) (by norm_num) h)
  have pv : v ∈ Set.Ioo (1 / 4) (1 / 3) ∨ v ∈ Set.Ioo (3 / 4) (5 / 6) := by
    rcases preimage2 hv hv2 with h | h
    · exact Or.inl (Set.Ioo_subset_Ioo (by norm_num) (by norm_num) h)
    · exact Or.inr (Set.Ioo_subset_Ioo (by norm_num) (by norm_num) h)
  have pw : w ∈ Set.Ioo (1 / 12) (1 / 6) ∨ w ∈ Set.Ioo (7 / 12) (2 / 3) := by
    rcases preimage2 hw hw2 with h | h
    · exact Or.inl (Set.Ioo_subset_Ioo (by norm_num) (by norm_num) h)
    · exact Or.inr (Set.Ioo_subset_Ioo (by norm_num) (by norm_num) h)
  -- λ = 3 forward images: each `⟨3·⟩ ∈ (1/4,1/2) ∪ (3/4,1)`.
  have fu3 : Int.fract (3 * u) ∈ Set.Ioo (1 / 4) (1 / 2) ∨
      Int.fract (3 * u) ∈ Set.Ioo (3 / 4) 1 := by
    rcases pu with h | h
    · exact Or.inl (Set.Ioo_subset_Ioo (by norm_num) (by norm_num)
        (fract_mul_Ioo (by norm_num : (0 : ℕ) < 3) (n := 1) (by norm_num) (by norm_num) h))
    · exact Or.inr (Set.Ioo_subset_Ioo (by norm_num) (by norm_num)
        (fract_mul_Ioo (by norm_num : (0 : ℕ) < 3) (n := 2) (by norm_num) (by norm_num) h))
  have fv3 : Int.fract (3 * v) ∈ Set.Ioo (3 / 4) 1 ∨
      Int.fract (3 * v) ∈ Set.Ioo (1 / 4) (1 / 2) := by
    rcases pv with h | h
    · exact Or.inl (Set.Ioo_subset_Ioo (by norm_num) (by norm_num)
        (fract_mul_Ioo (by norm_num : (0 : ℕ) < 3) (n := 0) (by norm_num) (by norm_num) h))
    · exact Or.inr (Set.Ioo_subset_Ioo (by norm_num) (by norm_num)
        (fract_mul_Ioo (by norm_num : (0 : ℕ) < 3) (n := 2) (by norm_num) (by norm_num) h))
  have fw3 : Int.fract (3 * w) ∈ Set.Ioo (1 / 4) (1 / 2) ∨
      Int.fract (3 * w) ∈ Set.Ioo (3 / 4) 1 := by
    rcases pw with h | h
    · exact Or.inl (Set.Ioo_subset_Ioo (by norm_num) (by norm_num)
        (fract_mul_Ioo (by norm_num : (0 : ℕ) < 3) (n := 0) (by norm_num) (by norm_num) h))
    · exact Or.inr (Set.Ioo_subset_Ioo (by norm_num) (by norm_num)
        (fract_mul_Ioo (by norm_num : (0 : ℕ) < 3) (n := 1) (by norm_num) (by norm_num) h))
  -- Exactly one runner lies in `(2/3,1)` at λ = 3; three subcases.
  rcases thirds_T3 hT with ⟨huT3, hvlt, hwlt⟩ | ⟨hvT3, hult, hwlt⟩ |
    ⟨hwT3, hult, hvlt⟩
  · -- `⟨3u⟩ ∈ (2/3,1)`: `u ∈ (11/12,1)`, `v ∈ (3/4,5/6)`, `w ∈ (1/12,1/6)`; `α = 4`.
    have huI : u ∈ Set.Ioo (11 / 12) 1 :=
      branch_pick (lam := 3) (by norm_num) (n := 1) (by norm_num) (by norm_num)
        (Or.inl (by norm_num)) pu.symm huT3
    have hvI : v ∈ Set.Ioo (3 / 4) (5 / 6) :=
      branch_pick (lam := 3) (by norm_num) (n := 0) (by norm_num) (by norm_num)
        (Or.inr (by norm_num)) pv.symm (low_branch hvlt fv3)
    have hwI : w ∈ Set.Ioo (1 / 12) (1 / 6) :=
      branch_pick (lam := 3) (by norm_num) (n := 1) (by norm_num) (by norm_num)
        (Or.inr (by norm_num)) pw (low_branch hwlt fw3.symm)
    exact hgood 4 (Or.inr (Or.inr rfl))
      (fract_add6_Ioo (al := 4) (n := 1) (by norm_num) (by norm_num) huI)
      (fract_add6_Ioo (al := 4) (n := 1) (by norm_num) (by norm_num) hvI)
      (fract_add6_Ioo (al := 4) (n := 0) (by norm_num) (by norm_num) hwI)
  · -- `⟨3v⟩ ∈ (2/3,1)`: `u ∈ (5/12,1/2)`, `v ∈ (1/4,1/3)`, `w ∈ (1/12,1/6)`; `α = 1`.
    have huI : u ∈ Set.Ioo (5 / 12) (1 / 2) :=
      branch_pick (lam := 3) (by norm_num) (n := 2) (by norm_num) (by norm_num)
        (Or.inr (by norm_num)) pu (low_branch hult fu3.symm)
    have hvI : v ∈ Set.Ioo (1 / 4) (1 / 3) :=
      branch_pick (lam := 3) (by norm_num) (n := 2) (by norm_num) (by norm_num)
        (Or.inl (by norm_num)) pv hvT3
    have hwI : w ∈ Set.Ioo (1 / 12) (1 / 6) :=
      branch_pick (lam := 3) (by norm_num) (n := 1) (by norm_num) (by norm_num)
        (Or.inr (by norm_num)) pw (low_branch hwlt fw3.symm)
    exact hgood 1 (Or.inl rfl)
      (fract_add6_Ioo (al := 1) (n := 0) (by norm_num) (by norm_num) huI)
      (fract_add6_Ioo (al := 1) (n := 0) (by norm_num) (by norm_num) hvI)
      (fract_add6_Ioo (al := 1) (n := 0) (by norm_num) (by norm_num) hwI)
  · -- `⟨3w⟩ ∈ (2/3,1)`: the hard subcase.  `w ∈ (7/12,2/3)`, `u ∈ (5/12,1/2)`,
    -- `v ∈ (3/4,5/6)`; `⟨3u⟩,⟨3v⟩ ∈ (1/4,1/2)` and `⟨3w⟩ ∈ (3/4,5/6)`.
    have huI : u ∈ Set.Ioo (5 / 12) (1 / 2) :=
      branch_pick (lam := 3) (by norm_num) (n := 2) (by norm_num) (by norm_num)
        (Or.inr (by norm_num)) pu (low_branch hult fu3.symm)
    have hvI : v ∈ Set.Ioo (3 / 4) (5 / 6) :=
      branch_pick (lam := 3) (by norm_num) (n := 0) (by norm_num) (by norm_num)
        (Or.inr (by norm_num)) pv.symm (low_branch hvlt fv3)
    have hwI : w ∈ Set.Ioo (7 / 12) (2 / 3) :=
      branch_pick (lam := 3) (by norm_num) (n := 0) (by norm_num) (by norm_num)
        (Or.inl (by norm_num)) pw.symm hwT3
    have hfu3 : Int.fract (3 * u) ∈ Set.Ioo (1 / 4) (1 / 2) := by
      rcases fu3 with h | h
      · exact h
      · exfalso
        rw [Set.mem_Ioo] at h
        linarith [h.1, hult]
    have hfv3 : Int.fract (3 * v) ∈ Set.Ioo (1 / 4) (1 / 2) := by
      rcases fv3 with h | h
      · exfalso
        rw [Set.mem_Ioo] at h
        linarith [h.1, hvlt]
      · exact h
    have hfw3a : Int.fract (3 * w) ∈ Set.Ioo (3 / 4) 1 :=
      Set.Ioo_subset_Ioo (by norm_num) (by norm_num)
        (fract_mul_Ioo (by norm_num : (0 : ℕ) < 3) (n := 1) (by norm_num) (by norm_num) hwI)
    -- `B₂ = (1/2,5/6)` at λ = 3 can only contain `⟨3w⟩`: `⟨3w⟩ ∈ (3/4,5/6)`.
    have hfw3 : Int.fract (3 * w) ∈ Set.Ioo (3 / 4) (5 / 6) := by
      have c := hbad 3 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      norm_num at c
      rcases c with h | h | h
      · exfalso
        rw [Set.mem_Ioo] at hfu3
        linarith [h.1, hfu3.2]
      · exfalso
        rw [Set.mem_Ioo] at hfv3
        linarith [h.1, hfv3.2]
      · rw [Set.mem_Ioo] at hfw3a
        exact ⟨hfw3a.1, h.2⟩
    -- Only two permutations at λ = 3 remain: `u` or `v` is the `(0,1/3)`-runner.
    rcases hT with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ |
      ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · -- `⟨3u⟩ ∈ (0,1/3)`, `⟨3v⟩ ∈ (1/3,2/3)`: `⟨5·⟩ = ⟨⟨3·⟩ + ⟨2·⟩⟩` gives
      -- `⟨5u⟩ ∈ (1/12,1/3)`, `⟨5v⟩`, `⟨5w⟩` wrap below `1/6` or above `5/6`.
      have hfu3' : Int.fract (3 * u) ∈ Set.Ioo (1 / 4) (1 / 3) := by
        rw [Set.mem_Ioo] at h1
        exact ⟨hfu3.1, h1.2⟩
      have hfv3' : Int.fract (3 * v) ∈ Set.Ioo (1 / 3) (1 / 2) := by
        rw [Set.mem_Ioo] at h2
        exact ⟨h2.1, hfv3.2⟩
      have hfu5 : Int.fract (5 * u) ∈ Set.Ioo (1 / 12) (1 / 3) := by
        rw [fract5_eq]
        exact Set.Ioo_subset_Ioo (by norm_num) (by norm_num)
          (fract_add_Ioo (n := 1) (by norm_num) (by norm_num) hfu3' hAu)
      have hfv5 : Int.fract (5 * v) ≤ 1 / 6 ∨ 5 / 6 < Int.fract (5 * v) := by
        rw [fract5_eq]
        rw [Set.mem_Ioo] at hfv3' hv2
        rcases fract_wrap (s := Int.fract (3 * v) + Int.fract (2 * v)) (a := 5 / 6)
          (b := 7 / 6) (by norm_num) (by norm_num)
          (by linarith [hfv3'.1, hv2.1]) (by linarith [hfv3'.2, hv2.2]) with h | h
        · left; linarith [h]
        · right; exact h
      have hfw5 : Int.fract (5 * w) ≤ 1 / 6 ∨ 11 / 12 < Int.fract (5 * w) := by
        rw [fract5_eq]
        rw [Set.mem_Ioo] at hfw3 hw2
        rcases fract_wrap (s := Int.fract (3 * w) + Int.fract (2 * w)) (a := 11 / 12)
          (b := 7 / 6) (by norm_num) (by norm_num)
          (by linarith [hfw3.1, hw2.1]) (by linarith [hfw3.2, hw2.2]) with h | h
        · left; linarith [h]
        · right; exact h
      have c := hbad 5 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      norm_num at c
      rcases c with h | h | h
      · rw [Set.mem_Ioo] at hfu5
        linarith [h.1, hfu5.2]
      · rcases hfv5 with h5 | h5 <;> linarith [h.1, h.2, h5]
      · rcases hfw5 with h5 | h5 <;> linarith [h.1, h.2, h5]
    · -- impossible: `⟨3w⟩` cannot be in `T2` and `T3`.
      exfalso
      rw [Set.mem_Ioo] at h2 hwT3
      linarith [h2.2, hwT3.1]
    · -- `⟨3v⟩ ∈ (0,1/3)`, `⟨3u⟩ ∈ (1/3,2/3)`: `⟨4v⟩ ∈ (0,1/6)`, `⟨4u⟩ ∈ (3/4,1)`,
      -- `⟨4w⟩ ∈ (1/3,1/2)`; case (a) at λ = 4 refines `⟨4u⟩ ∈ (3/4,5/6)`, then
      -- `⟨5u⟩ ∈ (1/6,1/3)`, `⟨5v⟩ ∈ (3/4,1)`, `⟨5w⟩` wraps: no `T2`-runner at λ = 5.
      have hfv3' : Int.fract (3 * v) ∈ Set.Ioo (1 / 4) (1 / 3) := by
        rw [Set.mem_Ioo] at h1
        exact ⟨hfv3.1, h1.2⟩
      have hfu3' : Int.fract (3 * u) ∈ Set.Ioo (1 / 3) (1 / 2) := by
        rw [Set.mem_Ioo] at h2
        exact ⟨h2.1, hfu3.2⟩
      have hfu4 : Int.fract (4 * u) ∈ Set.Ioo (3 / 4) 1 := by
        rw [fract4_eq]
        exact Set.Ioo_subset_Ioo (by norm_num) (by norm_num)
          (fract_add_Ioo (n := 0) (by norm_num) (by norm_num) huI hfu3')
      have hfv4 : Int.fract (4 * v) ∈ Set.Ioo 0 (1 / 6) := by
        rw [fract4_eq]
        exact Set.Ioo_subset_Ioo (by norm_num) (by norm_num)
          (fract_add_Ioo (n := 1) (by norm_num) (by norm_num) hvI hfv3')
      have hfw4 : Int.fract (4 * w) ∈ Set.Ioo (1 / 3) (1 / 2) := by
        rw [fract4_eq]
        exact Set.Ioo_subset_Ioo (by norm_num) (by norm_num)
          (fract_add_Ioo (n := 1) (by norm_num) (by norm_num) hwI hfw3)
      have hfu4' : Int.fract (4 * u) ∈ Set.Ioo (3 / 4) (5 / 6) := by
        have c := hbad 4 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        norm_num at c
        rcases c with h | h | h
        · rw [Set.mem_Ioo] at hfu4
          exact ⟨hfu4.1, h.2⟩
        · exfalso
          rw [Set.mem_Ioo] at hfv4
          linarith [h.1, hfv4.2]
        · exfalso
          rw [Set.mem_Ioo] at hfw4
          linarith [h.1, hfw4.2]
      have hfu5 : Int.fract (5 * u) ∈ Set.Ioo (1 / 6) (1 / 3) := by
        rw [fract5_eq']
        exact Set.Ioo_subset_Ioo (by norm_num) (by norm_num)
          (fract_add_Ioo (n := 1) (by norm_num) (by norm_num) huI hfu4')
      have hfv5 : Int.fract (5 * v) ∈ Set.Ioo (3 / 4) 1 := by
        rw [fract5_eq']
        exact Set.Ioo_subset_Ioo (by norm_num) (by norm_num)
          (fract_add_Ioo (n := 0) (by norm_num) (by norm_num) hvI hfv4)
      have hfw5 : Int.fract (5 * w) ≤ 1 / 6 ∨ 11 / 12 < Int.fract (5 * w) := by
        rw [fract5_eq']
        rw [Set.mem_Ioo] at hwI hfw4
        rcases fract_wrap (s := w + Int.fract (4 * w)) (a := 11 / 12) (b := 7 / 6)
          (by norm_num) (by norm_num)
          (by linarith [hwI.1, hfw4.1]) (by linarith [hwI.2, hfw4.2]) with h | h
        · left; linarith [h]
        · right; exact h
      have c := hbad 5 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      norm_num at c
      rcases c with h | h | h
      · rw [Set.mem_Ioo] at hfu5
        linarith [h.1, hfu5.2]
      · rw [Set.mem_Ioo] at hfv5
        linarith [h.2, hfv5.1]
      · rcases hfw5 with h5 | h5 <;> linarith [h.1, h.2, h5]
    · exfalso
      rw [Set.mem_Ioo] at h2 hwT3
      linarith [h2.2, hwT3.1]
    · exfalso
      rw [Set.mem_Ioo] at h1 hwT3
      linarith [h1.2, hwT3.1]
    · exfalso
      rw [Set.mem_Ioo] at h1 hwT3
      linarith [h1.2, hwT3.1]

/-- λ = 2, case (c): no runner has `⟨2·⟩ ∈ (0,1/6) ∪ (5/6,1)`.  Role order:
`u` the `(0,1/3)`-runner, `v` the `(1/3,2/3)`-runner, `w` the `(2/3,1)`-runner
at λ = 2.  Then `⟨2u⟩ ∈ [1/6,1/3)` and `⟨2w⟩ ∈ (2/3,5/6]`, so both
`⟨4u⟩, ⟨4w⟩ ∈ [1/3,2/3]` — two runners in the closed middle third at λ = 4,
contradicting the one-per-third structure. -/
private lemma lam2_caseC {u v w : ℝ}
    (_hu : u ∈ Set.Ico 0 1) (_hv : v ∈ Set.Ico 0 1) (_hw : w ∈ Set.Ico 0 1)
    (hbad : ∀ (lam al : ℕ), 2 ≤ lam → lam ≤ 5 → 1 ≤ al → al ≤ 5 →
        Int.fract ((lam : ℝ) * u) ∈ Set.Ioo ((5 - (al : ℝ)) / 6) ((7 - (al : ℝ)) / 6) ∨
        Int.fract ((lam : ℝ) * v) ∈ Set.Ioo ((5 - (al : ℝ)) / 6) ((7 - (al : ℝ)) / 6) ∨
        Int.fract ((lam : ℝ) * w) ∈ Set.Ioo ((5 - (al : ℝ)) / 6) ((7 - (al : ℝ)) / 6))
    (hu2 : Int.fract (2 * u) ∈ Set.Ico (1 / 6) (1 / 3))
    (hw2 : Int.fract (2 * w) ∈ Set.Ioc (2 / 3) (5 / 6)) : False := by
  have hT : Thirds (Int.fract (4 * u)) (Int.fract (4 * v)) (Int.fract (4 * w)) := by
    have c1 := hbad 4 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have c2 := hbad 4 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have c3 := hbad 4 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    norm_num at c1 c2 c3
    apply one_per_third
    · exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
    · exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
    · exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
    · rcases c1 with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    · rcases c2 with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    · rcases c3 with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
  have e4u : Int.fract (4 * u) = Int.fract (2 * Int.fract (2 * u)) := by
    rw [show (4 : ℝ) * u = 2 * u + 2 * u by ring, fract_self_add, fract_add_int_right]
    congr 1
    ring
  have e4w : Int.fract (4 * w) = Int.fract (2 * Int.fract (2 * w)) := by
    rw [show (4 : ℝ) * w = 2 * w + 2 * w by ring, fract_self_add, fract_add_int_right]
    congr 1
    ring
  have h4u : Int.fract (4 * u) ∈ Set.Icc (1 / 3) (2 / 3) := by
    rw [e4u]
    rw [Set.mem_Ico] at hu2
    have hself : Int.fract (2 * Int.fract (2 * u)) = 2 * Int.fract (2 * u) :=
      Int.fract_eq_self.mpr ⟨by linarith [hu2.1], by linarith [hu2.2]⟩
    rw [hself, Set.mem_Icc]
    constructor <;> linarith [hu2.1, hu2.2]
  have h4w : Int.fract (4 * w) ∈ Set.Icc (1 / 3) (2 / 3) := by
    rw [e4w]
    rw [Set.mem_Ioc] at hw2
    have hself : Int.fract (2 * Int.fract (2 * w)) = 2 * Int.fract (2 * w) - 1 := by
      have h := fract_eq_sub_of_mem (k := 1) (y := 2 * Int.fract (2 * w))
        (by push_cast; linarith [hw2.1]) (by push_cast; linarith [hw2.2])
      rwa [Int.cast_one] at h
    rw [hself, Set.mem_Icc]
    constructor <;> linarith [hw2.1, hw2.2]
  exact thirds_T2_unique hT h4u h4w

/-- The λ = 2 trichotomy.  With `u` the `(0,1/3)`-runner, `v` the `(1/3,2/3)`-runner
and `w` the `(2/3,1)`-runner at λ = 2, exactly one of Renault's cases (a), (b), (c)
holds; each is contradictory. -/
private lemma lam2_analysis {u v w : ℝ}
    (hu : u ∈ Set.Ico 0 1) (hv : v ∈ Set.Ico 0 1) (hw : w ∈ Set.Ico 0 1)
    (hbad : ∀ (lam al : ℕ), 2 ≤ lam → lam ≤ 5 → 1 ≤ al → al ≤ 5 →
        Int.fract ((lam : ℝ) * u) ∈ Set.Ioo ((5 - (al : ℝ)) / 6) ((7 - (al : ℝ)) / 6) ∨
        Int.fract ((lam : ℝ) * v) ∈ Set.Ioo ((5 - (al : ℝ)) / 6) ((7 - (al : ℝ)) / 6) ∨
        Int.fract ((lam : ℝ) * w) ∈ Set.Ioo ((5 - (al : ℝ)) / 6) ((7 - (al : ℝ)) / 6))
    (hgood : ∀ (al : ℕ), (al = 1 ∨ al = 2 ∨ al = 4) →
        Int.fract (u + (al : ℝ) / 6) ∈ Set.Ioo (1 / 6) (5 / 6) →
        Int.fract (v + (al : ℝ) / 6) ∈ Set.Ioo (1 / 6) (5 / 6) →
        Int.fract (w + (al : ℝ) / 6) ∈ Set.Ioo (1 / 6) (5 / 6) → False)
    (h1T : Int.fract (2 * u) ∈ Set.Ioo 0 (1 / 3))
    (h2T : Int.fract (2 * v) ∈ Set.Ioo (1 / 3) (2 / 3))
    (h3T : Int.fract (2 * w) ∈ Set.Ioo (2 / 3) 1) : False := by
  by_cases ha : Int.fract (2 * u) < 1 / 6
  · -- Case (a): `u` is the `(0,1/6)`-runner.
    exact lam2_caseA hu hv hw hbad hgood ⟨h1T.1, ha⟩ h2T h3T
  · by_cases hb : (5 : ℝ) / 6 < Int.fract (2 * w)
    · -- Case (b): `w` is the `(5/6,1)`-runner; `lam2_caseB` takes roles (T3,T2,T1).
      exact lam2_caseB hw hv hu
        (fun lam al hl2 hl5 ha1 ha5 => by
          rcases hbad lam al hl2 hl5 ha1 ha5 with hh | hh | hh <;>
            first | exact Or.inl hh | exact Or.inr (Or.inl hh) | exact Or.inr (Or.inr hh))
        (fun al hm iw iv iu => hgood al hm iu iv iw)
        ⟨hb, h3T.2⟩ h2T h1T
    · -- Case (c): `⟨2u⟩ ∈ [1/6,1/3)`, `⟨2w⟩ ∈ (2/3,5/6]`.
      exact lam2_caseC hu hv hw hbad ⟨not_lt.mp ha, h1T.2⟩ ⟨h3T.1, not_lt.mp hb⟩

/-- Renault Lemma 5.1.  The first disjunct covers `λ ≥ 2` improving moves; the
second is the `λ = 1` strict-interior alternative used for the `s + η`
perturbation. -/
theorem lemma5_1 {x₃ x₄ x₅ : ℝ}
    (h3 : x₃ ∈ Set.Ico 0 1) (h4 : x₄ ∈ Set.Ico 0 1) (h5 : x₅ ∈ Set.Ico 0 1) :
    (∃ lam al : ℕ, 2 ≤ lam ∧ lam ≤ 5 ∧ 1 ≤ al ∧ al ≤ 5 ∧
        Int.fract ((lam : ℝ) * x₃ + (al : ℝ) / 6) ∈ Set.Icc (1 / 6) (5 / 6) ∧
        Int.fract ((lam : ℝ) * x₄ + (al : ℝ) / 6) ∈ Set.Icc (1 / 6) (5 / 6) ∧
        Int.fract ((lam : ℝ) * x₅ + (al : ℝ) / 6) ∈ Set.Icc (1 / 6) (5 / 6))
    ∨
    (∃ al : ℕ, (al = 1 ∨ al = 2 ∨ al = 4) ∧
        Int.fract (x₃ + (al : ℝ) / 6) ∈ Set.Ioo (1 / 6) (5 / 6) ∧
        Int.fract (x₄ + (al : ℝ) / 6) ∈ Set.Ioo (1 / 6) (5 / 6) ∧
        Int.fract (x₅ + (al : ℝ) / 6) ∈ Set.Ioo (1 / 6) (5 / 6)) := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨h1, h2⟩ := hcon
  -- For each `(λ, α)`, property (1) fails: some runner's `⟨λxᵢ + α/6⟩` misses
  -- `[1/6,5/6]`, i.e. `⟨λxᵢ⟩` lies in the bad arc `((5-α)/6,(7-α)/6)`.
  have hbad : ∀ (lam al : ℕ), 2 ≤ lam → lam ≤ 5 → 1 ≤ al → al ≤ 5 →
      Int.fract ((lam : ℝ) * x₃) ∈ Set.Ioo ((5 - (al : ℝ)) / 6) ((7 - (al : ℝ)) / 6) ∨
      Int.fract ((lam : ℝ) * x₄) ∈ Set.Ioo ((5 - (al : ℝ)) / 6) ((7 - (al : ℝ)) / 6) ∨
      Int.fract ((lam : ℝ) * x₅) ∈ Set.Ioo ((5 - (al : ℝ)) / 6) ((7 - (al : ℝ)) / 6) := by
    intro lam al hl2 hl5 ha1 ha5
    by_contra hno
    rw [not_or, not_or] at hno
    obtain ⟨nb3, nb4, nb5⟩ := hno
    apply h1
    refine ⟨lam, al, hl2, hl5, ha1, ha5, ?_, ?_, ?_⟩
    · rw [fract_self_add]
      by_contra hmem
      exact nb3 ((bad_iff (Int.fract_nonneg _) (Int.fract_lt_one _) ha1 ha5).mp hmem)
    · rw [fract_self_add]
      by_contra hmem
      exact nb4 ((bad_iff (Int.fract_nonneg _) (Int.fract_lt_one _) ha1 ha5).mp hmem)
    · rw [fract_self_add]
      by_contra hmem
      exact nb5 ((bad_iff (Int.fract_nonneg _) (Int.fract_lt_one _) ha1 ha5).mp hmem)
  -- Property (2) fails for each `α ∈ {1,2,4}`.
  have hgood : ∀ (al : ℕ), (al = 1 ∨ al = 2 ∨ al = 4) →
      Int.fract (x₃ + (al : ℝ) / 6) ∈ Set.Ioo (1 / 6) (5 / 6) →
      Int.fract (x₄ + (al : ℝ) / 6) ∈ Set.Ioo (1 / 6) (5 / 6) →
      Int.fract (x₅ + (al : ℝ) / 6) ∈ Set.Ioo (1 / 6) (5 / 6) → False :=
    fun al hm i3 i4 i5 => h2 ⟨al, hm, i3, i4, i5⟩
  -- Renault's counting: at each `λ`, the bad arcs `B₅ = (0,1/3)`,
  -- `B₃ = (1/3,2/3)`, `B₁ = (2/3,1)` each contain a runner, forcing the
  -- one-per-third bijection.
  have hthird : ∀ (lam : ℕ), 2 ≤ lam → lam ≤ 5 →
      Thirds (Int.fract ((lam : ℝ) * x₃)) (Int.fract ((lam : ℝ) * x₄))
        (Int.fract ((lam : ℝ) * x₅)) := by
    intro lam hl2 hl5
    have c1 := hbad lam 5 hl2 hl5 (by norm_num) (by norm_num)
    have c2 := hbad lam 3 hl2 hl5 (by norm_num) (by norm_num)
    have c3 := hbad lam 1 hl2 hl5 (by norm_num) (by norm_num)
    norm_num at c1 c2 c3
    apply one_per_third
    · exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
    · exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
    · exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
    · rcases c1 with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    · rcases c2 with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    · rcases c3 with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
  -- The one-per-third structure at λ = 2, dispatched over the six permutations.
  have hT : Thirds (Int.fract (2 * x₃)) (Int.fract (2 * x₄)) (Int.fract (2 * x₅)) :=
    hthird 2 (by norm_num) (by norm_num)
  rcases hT with ⟨h1T, h2T, h3T⟩ | ⟨h1T, h2T, h3T⟩ | ⟨h1T, h2T, h3T⟩ |
    ⟨h1T, h2T, h3T⟩ | ⟨h1T, h2T, h3T⟩ | ⟨h1T, h2T, h3T⟩
  · -- `⟨2x₃⟩ ∈ (0,1/3)`, `⟨2x₄⟩ ∈ (1/3,2/3)`, `⟨2x₅⟩ ∈ (2/3,1)`.
    exact lam2_analysis h3 h4 h5 hbad hgood h1T h2T h3T
  · -- `⟨2x₃⟩ ∈ (0,1/3)`, `⟨2x₅⟩ ∈ (1/3,2/3)`, `⟨2x₄⟩ ∈ (2/3,1)`.
    exact lam2_analysis h3 h5 h4
      (fun lam al hl2 hl5 ha1 ha5 => by
        rcases hbad lam al hl2 hl5 ha1 ha5 with hh | hh | hh <;>
          first | exact Or.inl hh | exact Or.inr (Or.inl hh) | exact Or.inr (Or.inr hh))
      (fun al hm a b c => hgood al hm a c b)
      h1T h2T h3T
  · -- `⟨2x₄⟩ ∈ (0,1/3)`, `⟨2x₃⟩ ∈ (1/3,2/3)`, `⟨2x₅⟩ ∈ (2/3,1)`.
    exact lam2_analysis h4 h3 h5
      (fun lam al hl2 hl5 ha1 ha5 => by
        rcases hbad lam al hl2 hl5 ha1 ha5 with hh | hh | hh <;>
          first | exact Or.inl hh | exact Or.inr (Or.inl hh) | exact Or.inr (Or.inr hh))
      (fun al hm a b c => hgood al hm b a c)
      h1T h2T h3T
  · -- `⟨2x₄⟩ ∈ (0,1/3)`, `⟨2x₅⟩ ∈ (1/3,2/3)`, `⟨2x₃⟩ ∈ (2/3,1)`.
    exact lam2_analysis h4 h5 h3
      (fun lam al hl2 hl5 ha1 ha5 => by
        rcases hbad lam al hl2 hl5 ha1 ha5 with hh | hh | hh <;>
          first | exact Or.inl hh | exact Or.inr (Or.inl hh) | exact Or.inr (Or.inr hh))
      (fun al hm a b c => hgood al hm c a b)
      h1T h2T h3T
  · -- `⟨2x₅⟩ ∈ (0,1/3)`, `⟨2x₃⟩ ∈ (1/3,2/3)`, `⟨2x₄⟩ ∈ (2/3,1)`.
    exact lam2_analysis h5 h3 h4
      (fun lam al hl2 hl5 ha1 ha5 => by
        rcases hbad lam al hl2 hl5 ha1 ha5 with hh | hh | hh <;>
          first | exact Or.inl hh | exact Or.inr (Or.inl hh) | exact Or.inr (Or.inr hh))
      (fun al hm a b c => hgood al hm b c a)
      h1T h2T h3T
  · -- `⟨2x₅⟩ ∈ (0,1/3)`, `⟨2x₄⟩ ∈ (1/3,2/3)`, `⟨2x₃⟩ ∈ (2/3,1)`.
    exact lam2_analysis h5 h4 h3
      (fun lam al hl2 hl5 ha1 ha5 => by
        rcases hbad lam al hl2 hl5 ha1 ha5 with hh | hh | hh <;>
          first | exact Or.inl hh | exact Or.inr (Or.inl hh) | exact Or.inr (Or.inr hh))
      (fun al hm a b c => hgood al hm c b a)
      h1T h2T h3T

end
