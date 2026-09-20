/-
Copyright (c) 2026 Research07 contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Research07 contributors
-/
import Research07.LRC7.Finite
import Research07.LRC7.Compress

/-!
# The integer case `n = 7` — outer case tree (Barajas–Serra §4)

The final assembly: every `D` with `|D| ≤ 6` positive elements admits a
multiplier `λ` and modulus `M` (`7 ∣ M`) putting every element at distance
`≥ M/7`.  `lrc7_int` then converts to the `circ` statement via
`circ_ge_seventh`.

Structure (paper §4 overview):

* **Preprocessing.**  Divide `D` by `7^a`, `a = min ν₇(D)`.  The quotient
  `D₀` has minimum level `0`; a multiplier for `D₀` lifts to one for `D`
  scaled by `7^a` (`absModN_pow7_scale`).
* **Case tree on `D₀`** (`m₀ = max ν₇(D₀)`):
  * `m₀ = 0`: all units, `λ = 1`.
  * every level `< m₀` has `≤ 3` elements: `filtered7_good`
    (`F = {0,6}`, per-level budget `2·|level| ≤ 6`) covers the low levels;
    `absModN_top_ge7` covers level `m₀`.
  * otherwise a unique level `j₀ < m₀` has `4` or `5` elements:
    * `j₀ > 0` (necessarily `4`): `D' = {d/7^{j₀} : ν₇ d ≥ j₀}` is four
      units plus one element at level `m₀ − j₀`; §5 (`lrc7_case4`) yields
      a unit `λ'`; lifting scales `M'` by `7^{j₀}`; elements below `j₀`
      are then fixed by `filtered7_good` at `i₀ = j₀` applied to `λ'·D₀`.
    * `j₀ = 0`, `|A| = 4`: §5 (`lrc7_case4`) directly.
    * `j₀ = 0`, `|A| = 5`: the leftover element sits at level `m₀`;
      `m₀ = 1` is §7 (`lrc7_m1`), `m₀ > 1` is §6 (`lrc7_case5m`).
-/

/-! ### Level bookkeeping -/

theorem mem_level7 {D : Finset ℕ} {d j : ℕ} :
    d ∈ level7 D j ↔ d ∈ D ∧ padicValNat 7 d = j :=
  Finset.mem_filter

/-- Dividing by `7^a` drops the level by `a`. -/
theorem padicValNat_div_pow {a d : ℕ} (h : 7 ^ a ∣ d) (hd : 0 < d) :
    padicValNat 7 (d / 7 ^ a) = padicValNat 7 d - a := by
  have hd7 : d / 7 ^ a ≠ 0 :=
    Nat.ne_of_gt (Nat.div_pos (Nat.le_of_dvd hd h) (Nat.pow_pos (by norm_num)))
  have hdeq : d = 7 ^ a * (d / 7 ^ a) := (Nat.mul_div_cancel' h).symm
  have hmul : padicValNat 7 d = a + padicValNat 7 (d / 7 ^ a) := by
    conv_lhs => rw [hdeq]
    rw [padicValNat.mul (by norm_num : (7 ^ a : ℕ) ≠ 0) hd7,
      padicValNat.prime_pow]
  omega

/-- If `a ≤ ν₇ d` for every `d ∈ D`, division by `7^a` maps `level7 D (j+a)`
onto `level7 (D/7^a) j`. -/
theorem level7_image_div_pow {D : Finset ℕ} {a j : ℕ}
    (ha : ∀ d ∈ D, a ≤ padicValNat 7 d) (hpos : ∀ d ∈ D, 0 < d) :
    level7 (D.image (· / 7 ^ a)) j = (level7 D (j + a)).image (· / 7 ^ a) := by
  ext x
  simp only [mem_level7, Finset.mem_image]
  constructor
  · rintro ⟨⟨x', hx'D, rfl⟩, hxν⟩
    have h7a : 7 ^ a ∣ x' :=
      (Nat.pow_dvd_iff_le_padicValNat (by norm_num)
        (Nat.ne_of_gt (hpos x' hx'D))).mpr (ha x' hx'D)
    rw [padicValNat_div_pow h7a (hpos x' hx'D)] at hxν
    exact ⟨x', ⟨hx'D, by have := ha x' hx'D; omega⟩, rfl⟩
  · rintro ⟨x', ⟨hx'D, hx'ν⟩, rfl⟩
    have h7a : 7 ^ a ∣ x' :=
      (Nat.pow_dvd_iff_le_padicValNat (by norm_num)
        (Nat.ne_of_gt (hpos x' hx'D))).mpr (ha x' hx'D)
    exact ⟨⟨x', hx'D, rfl⟩, by
      rw [padicValNat_div_pow h7a (hpos x' hx'D), hx'ν]
      exact Nat.add_sub_cancel j a⟩

/-- Division by `7^a` is injective when `7^a` divides every element. -/
theorem div_pow_injOn {D : Finset ℕ} {a : ℕ}
    (ha : ∀ d ∈ D, a ≤ padicValNat 7 d) (hpos : ∀ d ∈ D, 0 < d) :
    Set.InjOn (· / 7 ^ a) D := by
  intro x hx y hy hxy
  have hx7 : 7 ^ a ∣ x :=
    (Nat.pow_dvd_iff_le_padicValNat (by norm_num)
      (Nat.ne_of_gt (hpos x hx))).mpr (ha x hx)
  have hy7 : 7 ^ a ∣ y :=
    (Nat.pow_dvd_iff_le_padicValNat (by norm_num)
      (Nat.ne_of_gt (hpos y hy))).mpr (ha y hy)
  have := congrArg (7 ^ a * ·) hxy
  rwa [Nat.mul_div_cancel' hx7, Nat.mul_div_cancel' hy7] at this

/-- `padicValNat` of a `7`-unit multiple equals that of the base. -/
theorem padicValNat_mul_unit7' {lam d : ℕ} (hlam : ¬ 7 ∣ lam) (hd : 0 < d) :
    padicValNat 7 (lam * d) = padicValNat 7 d :=
  padicValNat_mul_unit7 (fun h => hlam (h ▸ dvd_zero 7)) (Nat.ne_of_gt hd) hlam

/-- The levels of `D` partition it: `D = ⋃_{j ≤ m} level7 D j`. -/
theorem level7_biUnion {D : Finset ℕ} {m : ℕ}
    (hm : ∀ d ∈ D, padicValNat 7 d ≤ m) :
    (Finset.range (m + 1)).biUnion (level7 D) = D := by
  ext d
  simp only [Finset.mem_biUnion, Finset.mem_range, mem_level7]
  constructor
  · rintro ⟨j, -, hd, -⟩; exact hd
  · intro hd; exact ⟨padicValNat 7 d, by have := hm d hd; omega, hd, rfl⟩

/-- Three distinct levels of `D` contribute at least the sum of their
cards to `|D|`. -/
theorem card_le_of_levels {D : Finset ℕ} {j₁ j₂ j₃ : ℕ}
    (h12 : j₁ ≠ j₂) (h13 : j₁ ≠ j₃) (h23 : j₂ ≠ j₃) :
    (level7 D j₁).card + (level7 D j₂).card + (level7 D j₃).card ≤ D.card := by
  have hd12 : Disjoint (level7 D j₁) (level7 D j₂) := by
    rw [Finset.disjoint_left]; intro x hx1 hx2
    rw [mem_level7] at hx1 hx2; exact h12 (hx1.2.symm.trans hx2.2)
  have hd123 : Disjoint (level7 D j₁ ∪ level7 D j₂) (level7 D j₃) := by
    rw [Finset.disjoint_left]; intro x hx1 hx3
    rw [Finset.mem_union] at hx1
    rw [mem_level7] at hx3
    rcases hx1 with h1 | h2
    · rw [mem_level7] at h1; exact h13 (h1.2.symm.trans hx3.2)
    · rw [mem_level7] at h2; exact h23 (h2.2.symm.trans hx3.2)
  have hsub : level7 D j₁ ∪ level7 D j₂ ∪ level7 D j₃ ⊆ D := by
    intro x hx
    rcases Finset.mem_union.mp hx with h12 | h3
    · rcases Finset.mem_union.mp h12 with h1 | h2
      · exact (mem_level7.mp h1).1
      · exact (mem_level7.mp h2).1
    · exact (mem_level7.mp h3).1
  rw [← Finset.card_union_of_disjoint hd12,
    ← Finset.card_union_of_disjoint hd123]
  exact Finset.card_le_card hsub

/-! ### The case tree -/

/-- Multipliers of modulus `7^{m+1}` are a sufficient invariant for the
case tree: `7^{m+1}/7 = 7^m`. -/
private theorem pow7_div (m : ℕ) : 7 ^ (m + 1) / 7 = 7 ^ m := by
  rw [pow_succ']
  exact Nat.mul_div_cancel_left _ (by norm_num)

/-- The case tree on a set `D₀` whose minimum level is `0`, parameterized
by the §5 (`hc4`) and §6 (`hc6`) leaves so it compiles independently.
Conclusion is in lifted `(λ, M)` form: `M/7 ≤ |λd|_M` for all `d`. -/
private theorem exists_mult_aux
    (hc4 : ∀ {m : ℕ} (D : Finset ℕ), (∀ d ∈ D, 0 < d) →
      (∀ d ∈ D, padicValNat 7 d ≤ m) → 0 < m →
      (∃ d ∈ D, padicValNat 7 d = m) →
      (level7 D 0).card = 4 → D.card ≤ 6 →
      ∃ lam : ℕ, 0 < lam ∧ ¬ 7 ∣ lam ∧
        ∀ d ∈ D, 7 ^ m ≤ absModN (lam * d) (7 ^ (m + 1)))
    (hc6 : ∀ {m : ℕ} (A : Finset ℕ), A.card = 5 →
      (∀ d ∈ A, 0 < d) → (∀ d ∈ A, ¬ 7 ∣ d) →
      ∀ d6 : ℕ, padicValNat 7 d6 = m → 0 < d6 → 1 < m →
      ∃ lam : ℕ, 0 < lam ∧
        ∀ d ∈ A ∪ {d6}, 7 ^ m ≤ absModN (lam * d) (7 ^ (m + 1)))
    {D₀ : Finset ℕ} (hpos : ∀ d ∈ D₀, 0 < d) (hcard : D₀.card ≤ 6)
    (h0 : ∃ d ∈ D₀, padicValNat 7 d = 0) :
    ∃ lam M : ℕ, 0 < lam ∧ 0 < M ∧ 7 ∣ M ∧
      ∀ d ∈ D₀, M / 7 ≤ absModN (lam * d) M := by
  classical
  obtain ⟨u0, hu0D, hu0ν⟩ := h0
  have hD₀ne : D₀.Nonempty := ⟨u0, hu0D⟩
  obtain ⟨dm, hmD, hdmle⟩ := Finset.exists_max_image D₀ (padicValNat 7) hD₀ne
  set m₀ := padicValNat 7 dm with hm₀def
  have hm₀le : ∀ d ∈ D₀, padicValNat 7 d ≤ m₀ := hdmle
  have hdmν : padicValNat 7 dm = m₀ := rfl
  have hmDpos : 0 < dm := hpos dm hmD
  have h0card : 1 ≤ (level7 D₀ 0).card :=
    Finset.card_pos.mpr ⟨u0, Finset.mem_filter.mpr ⟨hu0D, hu0ν⟩⟩
  have hmcard : 1 ≤ (level7 D₀ m₀).card :=
    Finset.card_pos.mpr ⟨dm, Finset.mem_filter.mpr ⟨hmD, hdmν⟩⟩
  rcases Nat.eq_zero_or_pos m₀ with hm0 | hm0
  · -- `m₀ = 0`: all elements are units; `λ = 1`, `M = 7`.
    refine ⟨1, 7, one_pos, by norm_num, dvd_refl 7, ?_⟩
    intro d hd
    have hν : padicValNat 7 d = 0 := by have := hm₀le d hd; omega
    have h7nd : ¬ 7 ∣ d := by
      intro h
      have h1 : 1 ≤ padicValNat 7 d :=
        (Nat.pow_dvd_iff_le_padicValNat (by norm_num)
          (Nat.ne_of_gt (hpos d hd))).mp (by rwa [pow_one])
      omega
    have hr1 : 1 ≤ d % 7 :=
      Nat.pos_of_ne_zero (fun h => h7nd (Nat.dvd_iff_mod_eq_zero.mpr h))
    have hr6 : d % 7 ≤ 6 := by
      have := Nat.mod_lt d (by norm_num : 0 < 7); omega
    have h1 : (1 : ℕ) ≤ absModN d 7 := by
      unfold absModN
      omega
    rw [one_mul]
    calc 7 / 7 = 1 := by norm_num
      _ ≤ absModN d 7 := h1
  · by_cases hA : ∀ j < m₀, (level7 D₀ j).card ≤ 3
    · -- Branch A: every level below `m₀` has `≤ 3` elements — Λ-filtering.
      obtain ⟨lam, hlam7, hver, hgd⟩ := filtered7_good D₀ hpos hm₀le le_rfl
        (fun j hj => by have := hA j hj; omega)
      refine ⟨lam, 7 ^ (m₀ + 1),
        Nat.pos_of_ne_zero (fun h => hlam7 (by rw [h]; exact dvd_zero 7)),
        Nat.pow_pos (by norm_num), ⟨7 ^ m₀, by rw [pow_succ, mul_comm]⟩, ?_⟩
      intro d hd
      rw [pow7_div]
      rcases lt_or_eq_of_le (hm₀le d hd) with hlt | heq
      · exact (absModN_ge_iff_qdig7 hlt (hpos d hd) hlam7).mpr (hgd d hd hlt)
      · exact absModN_top_ge7 heq (hpos d hd) hlam7
    · push Not at hA
      obtain ⟨j₀, hj₀m, hj₀card⟩ := hA
      have hj₀4 : 4 ≤ (level7 D₀ j₀).card := by omega
      rcases Nat.eq_zero_or_pos j₀ with hj₀ | hj₀
      · subst hj₀
        -- `j₀ = 0`: `|A| ∈ {4, 5}`; `4` → §5, `5` → §6/§7.
        have hdis0m : Disjoint (level7 D₀ 0) (level7 D₀ m₀) := by
          rw [Finset.disjoint_left]
          intro x hx0 hxm
          rw [mem_level7] at hx0 hxm
          omega
        have hcard0m : (level7 D₀ 0).card + (level7 D₀ m₀).card ≤ 6 :=
          calc (level7 D₀ 0).card + (level7 D₀ m₀).card
              = (level7 D₀ 0 ∪ level7 D₀ m₀).card :=
                (Finset.card_union_of_disjoint hdis0m).symm
            _ ≤ D₀.card := Finset.card_le_card
                  (Finset.union_subset
                    (Finset.filter_subset _ _) (Finset.filter_subset _ _))
            _ ≤ 6 := hcard
        have hA45 : (level7 D₀ 0).card = 4 ∨ (level7 D₀ 0).card = 5 := by
          omega
        rcases hA45 with hA4 | hA5
        · -- `|A| = 4`: §5 directly.
          obtain ⟨lam, hlam, hlam7, hcov⟩ :=
            hc4 D₀ hpos hm₀le hm0 ⟨dm, hmD, hdmν⟩ hA4 hcard
          exact ⟨lam, 7 ^ (m₀ + 1), hlam, Nat.pow_pos (by norm_num),
            ⟨7 ^ m₀, by rw [pow_succ, mul_comm]⟩,
            fun d hd => pow7_div m₀ ▸ hcov d hd⟩
        · -- `|A| = 5`: the leftover element is the unique level-`m₀` one.
          have hmc1 : (level7 D₀ m₀).card = 1 := by omega
          have hmsing : level7 D₀ m₀ = {dm} := by
            obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hmc1
            have hdmm : dm ∈ level7 D₀ m₀ :=
              Finset.mem_filter.mpr ⟨hmD, hdmν⟩
            rw [hx, Finset.mem_singleton] at hdmm
            rw [hx, ← hdmm]
          set A := level7 D₀ 0 with hAdef
          have hAsub : A ⊆ D₀ := Finset.filter_subset _ _
          have hposA : ∀ d ∈ A, 0 < d := fun d hd => hpos d (hAsub hd)
          have hunitA : ∀ d ∈ A, ¬ 7 ∣ d := by
            intro d hd h7
            have hνd : padicValNat 7 d = 0 := (Finset.mem_filter.mp hd).2
            have h1 : 1 ≤ padicValNat 7 d :=
              (Nat.pow_dvd_iff_le_padicValNat (by norm_num)
                (Nat.ne_of_gt (hposA d hd))).mp (by rwa [pow_one])
            omega
          -- Every `d ∈ D₀` has level `0` or `m₀`.
          have hD₀eq : ∀ d ∈ D₀, d ∈ A ∪ {dm} := by
            intro d hd
            have hdν : padicValNat 7 d ≤ m₀ := hm₀le d hd
            rcases Nat.eq_zero_or_pos (padicValNat 7 d) with hν0 | hνpos
            · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hd, hν0⟩)
            · rcases eq_or_lt_of_le hdν with hνm | hνlt
              · exact Finset.mem_union_right _
                  (hmsing ▸ Finset.mem_filter.mpr ⟨hd, hνm⟩)
              · exfalso
                have hcd : 1 ≤ (level7 D₀ (padicValNat 7 d)).card :=
                  Finset.card_pos.mpr ⟨d, Finset.mem_filter.mpr ⟨hd, rfl⟩⟩
                have hsum := card_le_of_levels (D := D₀)
                  (show (0:ℕ) ≠ padicValNat 7 d by omega)
                  (show (0:ℕ) ≠ m₀ by omega)
                  (show padicValNat 7 d ≠ m₀ by omega)
                rw [← hAdef] at hsum
                omega
          rcases Nat.lt_or_ge m₀ 2 with hm | hm
          · -- `m₀ = 1`: §7 (`lrc7_m1`).
            have hm₁ : padicValNat 7 dm = 1 := by omega
            obtain ⟨lam, M, hlam, hM, hM7, hcov⟩ :=
              lrc7_m1 A hA5 hposA hunitA dm hm₁ hmDpos
            exact ⟨lam, M, hlam, hM, hM7, fun d hd => hcov d (hD₀eq d hd)⟩
          · -- `m₀ > 1`: §6 (`lrc7_case5m`).
            obtain ⟨lam, hlam, hcov⟩ :=
              hc6 A hA5 hposA hunitA dm hdmν hmDpos (by omega)
            exact ⟨lam, 7 ^ (m₀ + 1), hlam, Nat.pow_pos (by norm_num),
              ⟨7 ^ m₀, by rw [pow_succ, mul_comm]⟩,
              fun d hd => pow7_div m₀ ▸ hcov d (hD₀eq d hd)⟩
      · -- `j₀ > 0`: `|level j₀| = 4`, `|level 0| = |level m₀| = 1`, and the
        -- three levels exhaust `D₀`.
        have h01 : (0:ℕ) ≠ j₀ := by omega
        have h02 : (0:ℕ) ≠ m₀ := by omega
        have hjm : j₀ ≠ m₀ := ne_of_lt hj₀m
        have hsum := card_le_of_levels (D := D₀) h01 h02 hjm
        have hc0 : (level7 D₀ 0).card = 1 := by omega
        have hcj : (level7 D₀ j₀).card = 4 := by omega
        have hcm : (level7 D₀ m₀).card = 1 := by omega
        have hunion : level7 D₀ 0 ∪ level7 D₀ j₀ ∪ level7 D₀ m₀ = D₀ := by
          apply Finset.eq_of_subset_of_card_le
          · exact Finset.union_subset
              (Finset.union_subset
                (Finset.filter_subset _ _) (Finset.filter_subset _ _))
              (Finset.filter_subset _ _)
          · have hd1 : Disjoint (level7 D₀ 0) (level7 D₀ j₀) := by
              rw [Finset.disjoint_left]; intro x hx1 hx2
              rw [mem_level7] at hx1 hx2; omega
            have hd2 : Disjoint (level7 D₀ 0 ∪ level7 D₀ j₀)
                (level7 D₀ m₀) := by
              rw [Finset.disjoint_left]; intro x hx1 hx2
              rw [Finset.mem_union] at hx1
              rw [mem_level7] at hx2
              rcases hx1 with h | h <;> rw [mem_level7] at h <;> omega
            rw [Finset.card_union_of_disjoint hd2,
              Finset.card_union_of_disjoint hd1, hc0, hcj, hcm]
            exact hcard
        -- Every `d ∈ D₀` has level in `{0, j₀, m₀}`.
        have hνmem : ∀ d ∈ D₀, padicValNat 7 d = 0 ∨ padicValNat 7 d = j₀ ∨
            padicValNat 7 d = m₀ := by
          intro d hd
          have hd' : d ∈ level7 D₀ 0 ∪ level7 D₀ j₀ ∪ level7 D₀ m₀ := by
            rw [hunion]; exact hd
          rcases Finset.mem_union.mp hd' with h | h
          · rcases Finset.mem_union.mp h with h0' | hj'
            · exact Or.inl (mem_level7.mp h0').2
            · exact Or.inr (Or.inl (mem_level7.mp hj').2)
          · exact Or.inr (Or.inr (mem_level7.mp h).2)
        -- `D'` = levels `≥ j₀` divided by `7^{j₀}`: four units plus one
        -- level-`m₀ − j₀` element.
        set U := level7 D₀ j₀ ∪ level7 D₀ m₀ with hUdef
        have hUsub : U ⊆ D₀ := Finset.union_subset
          (Finset.filter_subset _ _) (Finset.filter_subset _ _)
        have hUν : ∀ d ∈ U, j₀ ≤ padicValNat 7 d := by
          intro d hd
          rcases Finset.mem_union.mp hd with h | h <;>
            rw [mem_level7] at h <;> omega
        have hUpos : ∀ d ∈ U, 0 < d := fun d hd => hpos d (hUsub hd)
        set D' := U.image (· / 7 ^ j₀) with hD'def
        have hD'pos : ∀ d ∈ D', 0 < d := by
          intro x hx
          obtain ⟨y, hyU, rfl⟩ := Finset.mem_image.mp hx
          exact Nat.div_pos (Nat.le_of_dvd (hUpos y hyU)
            ((Nat.pow_dvd_iff_le_padicValNat (by norm_num)
              (Nat.ne_of_gt (hUpos y hyU))).mpr (hUν y hyU)))
            (Nat.pow_pos (by norm_num))
        have hD'card : D'.card = 5 := by
          rw [hD'def, Finset.card_image_of_injOn (div_pow_injOn hUν hUpos)]
          have hd1 : Disjoint (level7 D₀ j₀) (level7 D₀ m₀) := by
            rw [Finset.disjoint_left]; intro x hx1 hx2
            rw [mem_level7] at hx1 hx2; omega
          rw [Finset.card_union_of_disjoint hd1, hcj, hcm]
        have hD'ν : ∀ d ∈ D', padicValNat 7 d ≤ m₀ - j₀ := by
          intro x hx
          obtain ⟨y, hyU, rfl⟩ := Finset.mem_image.mp hx
          have h7a : 7 ^ j₀ ∣ y :=
            (Nat.pow_dvd_iff_le_padicValNat (by norm_num)
              (Nat.ne_of_gt (hUpos y hyU))).mpr (hUν y hyU)
          rw [padicValNat_div_pow h7a (hUpos y hyU)]
          have hyν : padicValNat 7 y ≤ m₀ := hm₀le y (hUsub hyU)
          omega
        have hD'0 : (level7 D' 0).card = 4 := by
          have hlev : level7 D' 0 =
              (level7 D₀ j₀).image (· / 7 ^ j₀) := by
            rw [hD'def, level7_image_div_pow hUν hUpos]
            congr 1
            ext x
            simp only [mem_level7, Nat.zero_add]
            constructor
            · rintro ⟨hxU, hν⟩
              rcases Finset.mem_union.mp hxU with h | h
              · exact ⟨(Finset.mem_filter.mp h).1, hν⟩
              · rw [mem_level7] at h; omega
            · rintro ⟨hxD, hν⟩
              exact ⟨Finset.mem_union_left _
                (Finset.mem_filter.mpr ⟨hxD, hν⟩), hν⟩
          rw [hlev]
          have hinj : Set.InjOn (· / 7 ^ j₀) (level7 D₀ j₀) :=
            div_pow_injOn
              (fun d hd => le_of_eq (mem_level7.mp hd).2.symm)
              (fun d hd => hpos d (Finset.mem_filter.mp hd).1)
          rw [Finset.card_image_of_injOn hinj, hcj]
        have hD'max : ∃ d ∈ D', padicValNat 7 d = m₀ - j₀ := by
          refine ⟨dm / 7 ^ j₀, Finset.mem_image.mpr ⟨dm, ?_, rfl⟩, ?_⟩
          · exact Finset.mem_union_right _
              (Finset.mem_filter.mpr ⟨hmD, hdmν⟩)
          · have h7a : 7 ^ j₀ ∣ dm :=
              (Nat.pow_dvd_iff_le_padicValNat (by norm_num)
                (Nat.ne_of_gt hmDpos)).mpr (by omega)
            rw [padicValNat_div_pow h7a hmDpos, hdmν]
        -- §5 gives a unit multiplier `λ'` for `D'`.
        obtain ⟨lam', hlam'pos, hlam'7, hcov'⟩ :=
          hc4 D' hD'pos hD'ν (by omega) hD'max hD'0 (by omega)
        -- Lift: elements at level `≥ j₀` are covered at modulus `7^{m₀+1}`.
        have hN₀eq : 7 ^ j₀ * 7 ^ (m₀ - j₀ + 1) = 7 ^ (m₀ + 1) := by
          rw [← pow_add]; congr 1; omega
        have hhigh : ∀ d ∈ D₀, j₀ ≤ padicValNat 7 d →
            7 ^ m₀ ≤ absModN (lam' * d) (7 ^ (m₀ + 1)) := by
          intro d hd hdν
          have hdU : d ∈ U := by
            rcases hνmem d hd with h | h | h
            · omega
            · exact Finset.mem_union_left _
                (Finset.mem_filter.mpr ⟨hd, h⟩)
            · exact Finset.mem_union_right _
                (Finset.mem_filter.mpr ⟨hd, h⟩)
          set e := d / 7 ^ j₀ with he
          have heD' : e ∈ D' := Finset.mem_image.mpr ⟨d, hdU, he⟩
          have hcov := hcov' e heD'
          have h7a : 7 ^ j₀ ∣ d :=
            (Nat.pow_dvd_iff_le_padicValNat (by norm_num)
              (Nat.ne_of_gt (hpos d hd))).mpr hdν
          have hdeq : d = 7 ^ j₀ * e := (Nat.mul_div_cancel' h7a).symm
          have hmule : lam' * d = 7 ^ j₀ * (lam' * e) := by rw [hdeq]; ring
          have habs : absModN (lam' * d) (7 ^ (m₀ + 1)) =
              7 ^ j₀ * absModN (lam' * e) (7 ^ (m₀ - j₀ + 1)) := by
            rw [hmule, ← hN₀eq]
            exact absModN_pow7_scale j₀ (lam' * e) _
              (Nat.pow_pos (by norm_num))
          rw [habs]
          calc 7 ^ m₀ = 7 ^ j₀ * 7 ^ (m₀ - j₀) := by
                rw [← pow_add]; congr 1; omega
            _ ≤ 7 ^ j₀ * absModN (lam' * e) (7 ^ (m₀ - j₀ + 1)) :=
                Nat.mul_le_mul_left _ hcov
        -- Filter the elements below `j₀` on `λ'·D₀`.
        set D₀' := D₀.image (· * lam') with hD₀'def
        have hmulinj : Set.InjOn (· * lam') D₀ :=
          fun x _ y _ h => Nat.mul_right_cancel hlam'pos h
        have hD₀'pos : ∀ x ∈ D₀', 0 < x := by
          intro x hx
          obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
          exact Nat.mul_pos (hpos y hy) hlam'pos
        have hD₀'le : ∀ x ∈ D₀', padicValNat 7 x ≤ m₀ := by
          intro x hx
          obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
          rw [mul_comm y, padicValNat_mul_unit7' hlam'7 (hpos y hy)]
          exact hm₀le y hy
        have hD₀'lev : ∀ j, level7 D₀' j =
            (level7 D₀ j).image (· * lam') := by
          intro j
          ext x
          simp only [mem_level7, Finset.mem_image, hD₀'def]
          constructor
          · rintro ⟨⟨y, hy, rfl⟩, hν⟩
            have hνy : padicValNat 7 y = j := by
              have h := padicValNat_mul_unit7' hlam'7 (hpos y hy)
              rw [mul_comm] at h
              omega
            exact ⟨y, ⟨hy, hνy⟩, rfl⟩
          · rintro ⟨y, hy, rfl⟩
            refine ⟨⟨y, hy.1, rfl⟩, ?_⟩
            rw [mul_comm y, padicValNat_mul_unit7' hlam'7 (hpos y hy.1)]
            exact hy.2
        have hlow' : ∀ j, j < j₀ → 2 * (level7 D₀' j).card ≤ 6 := by
          intro j hj
          have hinj' : Set.InjOn (· * lam') (level7 D₀ j) :=
            Set.InjOn.mono (Finset.filter_subset _ _) hmulinj
          rw [hD₀'lev, Finset.card_image_of_injOn hinj']
          rcases Nat.eq_zero_or_pos j with rfl | hjp
          · rw [hc0]
            omega
          · have hempty : level7 D₀ j = ∅ := by
              rw [Finset.eq_empty_iff_forall_notMem]
              intro x hx
              rw [mem_level7] at hx
              rcases hνmem x hx.1 with h | h | h <;> omega
            rw [hempty, Finset.card_empty]
            omega
        obtain ⟨mu, hmu7, hmuver, hmugd⟩ :=
          filtered7_good D₀' hD₀'pos hD₀'le hj₀m.le hlow'
        -- Final multiplier `mu * lam'`.
        have hmu7' : ¬ 7 ∣ mu * lam' := by
          intro h
          rcases (Nat.Prime.dvd_mul Nat.prime_seven).mp h with h | h
          · exact hmu7 h
          · exact hlam'7 h
        have hposmu : 0 < mu :=
          Nat.pos_of_ne_zero (fun h => hmu7 (h ▸ dvd_zero 7))
        refine ⟨mu * lam', 7 ^ (m₀ + 1), Nat.mul_pos hposmu hlam'pos,
          Nat.pow_pos (by norm_num),
          ⟨7 ^ m₀, by rw [pow_succ, mul_comm]⟩, ?_⟩
        intro d hd
        rw [pow7_div]
        set x := lam' * d with hx
        have hxD' : x ∈ D₀' := Finset.mem_image.mpr ⟨d, hd, mul_comm _ _⟩
        have hxν : padicValNat 7 x = padicValNat 7 d :=
          padicValNat_mul_unit7' hlam'7 (hpos d hd)
        have hposx : 0 < x := hD₀'pos x hxD'
        have hgoal : (mu * lam') * d = mu * x := by rw [hx]; ring
        rw [hgoal]
        rcases lt_or_ge (padicValNat 7 d) j₀ with hlt | hge
        · -- Below `j₀`: digit of `mu·x` is good.
          have hb := hmugd x hxD' (by rw [hxν]; exact hlt)
          have hνx : padicValNat 7 x < m₀ := by rw [hxν]; omega
          exact (absModN_ge_iff_qdig7 hνx hposx hmu7).mpr hb
        · -- At or above `j₀`: `mu` preserves the residue.
          have hver := hmuver x hxD' (by rw [hxν]; exact hge)
          rw [absModN_congr_res hver]
          exact hhigh d hd hge

/-- Divide `D` by `7^a` with `a = min ν₇(D)`, solve on the quotient,
lift the multiplier back scaled by `7^a`. -/
private theorem exists_multiplier7_of
    (hc4 : ∀ {m : ℕ} (D : Finset ℕ), (∀ d ∈ D, 0 < d) →
      (∀ d ∈ D, padicValNat 7 d ≤ m) → 0 < m →
      (∃ d ∈ D, padicValNat 7 d = m) →
      (level7 D 0).card = 4 → D.card ≤ 6 →
      ∃ lam : ℕ, 0 < lam ∧ ¬ 7 ∣ lam ∧
        ∀ d ∈ D, 7 ^ m ≤ absModN (lam * d) (7 ^ (m + 1)))
    (hc6 : ∀ {m : ℕ} (A : Finset ℕ), A.card = 5 →
      (∀ d ∈ A, 0 < d) → (∀ d ∈ A, ¬ 7 ∣ d) →
      ∀ d6 : ℕ, padicValNat 7 d6 = m → 0 < d6 → 1 < m →
      ∃ lam : ℕ, 0 < lam ∧
        ∀ d ∈ A ∪ {d6}, 7 ^ m ≤ absModN (lam * d) (7 ^ (m + 1)))
    (D : Finset ℕ) (hpos : ∀ d ∈ D, 0 < d) (hcard : D.card ≤ 6) :
    ∃ lam M : ℕ, 0 < lam ∧ 0 < M ∧ 7 ∣ M ∧
      ∀ d ∈ D, M / 7 ≤ absModN (lam * d) M := by
  classical
  rcases D.eq_empty_or_nonempty with rfl | hDne
  · exact ⟨1, 7, one_pos, by norm_num, dvd_refl 7,
      fun d hd => absurd hd (Finset.notMem_empty d)⟩
  obtain ⟨d0, hd0D, hd0min⟩ :=
    Finset.exists_min_image D (padicValNat 7) hDne
  set a := padicValNat 7 d0 with ha_def
  have ha_le : ∀ d ∈ D, a ≤ padicValNat 7 d := hd0min
  set D₀ := D.image (· / 7 ^ a) with hD₀def
  have hD₀pos : ∀ x ∈ D₀, 0 < x := by
    intro x hx
    obtain ⟨y, hyD, rfl⟩ := Finset.mem_image.mp hx
    exact Nat.div_pos (Nat.le_of_dvd (hpos y hyD)
      ((Nat.pow_dvd_iff_le_padicValNat (by norm_num)
        (Nat.ne_of_gt (hpos y hyD))).mpr (ha_le y hyD)))
      (Nat.pow_pos (by norm_num))
  have hD₀card : D₀.card ≤ 6 := by
    rw [hD₀def, Finset.card_image_of_injOn (div_pow_injOn ha_le hpos)]
    exact hcard
  have h0 : ∃ x ∈ D₀, padicValNat 7 x = 0 := by
    refine ⟨d0 / 7 ^ a, Finset.mem_image.mpr ⟨d0, hd0D, rfl⟩, ?_⟩
    have h7a : 7 ^ a ∣ d0 :=
      (Nat.pow_dvd_iff_le_padicValNat (by norm_num)
        (Nat.ne_of_gt (hpos d0 hd0D))).mpr (le_refl a)
    rw [padicValNat_div_pow h7a (hpos d0 hd0D)]
    exact Nat.sub_self _
  obtain ⟨lam, M', hlam, hM', hM'7, hcov⟩ :=
    exists_mult_aux hc4 hc6 hD₀pos hD₀card h0
  refine ⟨lam, 7 ^ a * M', hlam,
    Nat.mul_pos (Nat.pow_pos (by norm_num)) hM',
    dvd_mul_of_dvd_right hM'7 (7 ^ a), ?_⟩
  intro d hd
  have h7a : 7 ^ a ∣ d :=
    (Nat.pow_dvd_iff_le_padicValNat (by norm_num)
      (Nat.ne_of_gt (hpos d hd))).mpr (ha_le d hd)
  have hdeq : d = 7 ^ a * (d / 7 ^ a) := (Nat.mul_div_cancel' h7a).symm
  have heD₀ : d / 7 ^ a ∈ D₀ := Finset.mem_image.mpr ⟨d, hd, rfl⟩
  have hmuleq : lam * d = 7 ^ a * (lam * (d / 7 ^ a)) := by
    conv_lhs => rw [hdeq]
    ring
  have hMdiv : 7 ^ a * M' / 7 = 7 ^ a * (M' / 7) :=
    Nat.mul_div_assoc (7 ^ a) hM'7
  rw [hMdiv]
  calc 7 ^ a * (M' / 7) ≤ 7 ^ a * absModN (lam * (d / 7 ^ a)) M' :=
        Nat.mul_le_mul_left _ (hcov _ heD₀)
    _ = absModN (7 ^ a * (lam * (d / 7 ^ a))) (7 ^ a * M') :=
        (absModN_pow7_scale a _ M' hM').symm
    _ = absModN (lam * d) (7 ^ a * M') := by rw [← hmuleq]

/-- **ℝ-bridge**: a `(lam, M)` multiplier certificate yields `t = lam / M`
with `circ (t * d) ≥ 1/7` for every `d ∈ D`. -/
theorem lrc7_int_of (D : Finset ℕ)
    (h : ∃ lam M : ℕ, 0 < lam ∧ 0 < M ∧ 7 ∣ M ∧
      ∀ d ∈ D, M / 7 ≤ absModN (lam * d) M) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ D, (1 / 7 : ℝ) ≤ circ (t * d) := by
  obtain ⟨lam, M, hlam, hM, hM7, hdist⟩ := h
  refine ⟨(lam : ℝ) / M, div_pos (Nat.cast_pos.mpr hlam) (Nat.cast_pos.mpr hM),
    fun d hd => ?_⟩
  have h' := circ_ge_seventh hM7 hM (hdist d hd)
  rwa [← div_mul_eq_mul_div] at h'

/-- Integer seven-runner theorem, parameterized by the §5 (`hc4`) and §6
(`hc6`) leaves; `Main.lean` instantiates them with `lrc7_case4`/`lrc7_case5m`. -/
theorem lrc7_int_of_leaves
    (hc4 : ∀ {m : ℕ} (D : Finset ℕ), (∀ d ∈ D, 0 < d) →
      (∀ d ∈ D, padicValNat 7 d ≤ m) → 0 < m →
      (∃ d ∈ D, padicValNat 7 d = m) →
      (level7 D 0).card = 4 → D.card ≤ 6 →
      ∃ lam : ℕ, 0 < lam ∧ ¬ 7 ∣ lam ∧
        ∀ d ∈ D, 7 ^ m ≤ absModN (lam * d) (7 ^ (m + 1)))
    (hc6 : ∀ {m : ℕ} (A : Finset ℕ), A.card = 5 →
      (∀ d ∈ A, 0 < d) → (∀ d ∈ A, ¬ 7 ∣ d) →
      ∀ d6 : ℕ, padicValNat 7 d6 = m → 0 < d6 → 1 < m →
      ∃ lam : ℕ, 0 < lam ∧
        ∀ d ∈ A ∪ {d6}, 7 ^ m ≤ absModN (lam * d) (7 ^ (m + 1)))
    (D : Finset ℕ) (hpos : ∀ d ∈ D, 0 < d) (hcard : D.card ≤ 6) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ D, (1 / 7 : ℝ) ≤ circ (t * d) :=
  lrc7_int_of D (exists_multiplier7_of hc4 hc6 D hpos hcard)
