/-
Copyright (c) 2026 Research07 contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Research07 contributors
-/
import Research07.LRC7.Discrete

/-!
# Compression toolkit for the seven-runner case (paper §6)

Purely `ZMod 7` combinatorial lemmas from Barajas–Serra, *The lonely runner
with seven runners*, EJC 15(1) (2008) #R48, §6. The integer bridge
(`qdig7`, `Λ₀` multipliers `1 + 7^m·k·s⁻¹`) lives in the callers; here
everything is stated on residue sets `A₁ A₂ A₄ : Finset (ZMod 7)`.

Model (paper → Lean):
* `A₁,A₂,A₄` model `q(A₁),q(A₂),q(A₄)` for the congruence classes
  `s, 2s, 4s` (`s ∈ {1,2,4}` is kept as a hypothesis marker for callers).
* A `Λ₀`-multiplier `λ_k = 1 + 7^m·k·s⁻¹` shifts `q(d) ↦ q(d) + j·k` on
  class-`j·s` elements (paper eq. (10)); hence the conclusion shift pattern
  `A₁ + t ∪ A₂ + 2t ∪ A₄ + 4t`, `t : ZMod 7` — the parameter `t` is the
  `Λ₀` index `k` (equivalently the unnormalized family `1 + 7^m·k` gives
  shifts `k·s`, which ranges over all of `ZMod 7` for `s ≠ 0`).
* `avoids06 X` models `q(λA) ∩ {0,6} = ∅`.
* `apLen X` (= `ℓ(X)`) is from `Research07.LRC7.Discrete`.

Contents:
* `exists_shift_avoid` — a set covered by an interval of length `≤ 5` has a
  translate avoiding `{0,6}` (`{0,6}` is cyclically adjacent).
* `remark8_i`, `remark8_ii` — paper Remark 8 (Z₇-level difference model:
  pairwise residue differences in `{0,±1}` resp. `{0,±1,±2}`).
* `lemma5` — paper Lemma 5, including the longest-class ordering hypothesis
  (`hord`, the paper's "class with larger length" convention) and the
  `(3,1,1)` exceptional disjunct.
* `lemma6` — paper Lemma 6: six length-triple cases with `ẽ` side-conditions.
* `lemma12` — paper Lemma 12: `|A₁| = 3`, `|A₂| = 2` multiplier counting.

Finite `decide` certificates live in `private` core lemmas; public theorems
are the covering-interval reductions (`apLen_le_iff` + monotonicity).
-/

/-- The forbidden leading-digit set `{0,6}` (paper §5/§6 target). -/
def bad06 : Finset (ZMod 7) := {0, 6}

/-- `avoids06 X` — every element of `X` lies outside `{0,6}`
(models the paper's `q(λA) ∩ {0,6} = ∅`). -/
def avoids06 (X : Finset (ZMod 7)) : Prop := ∀ x ∈ X, x ∉ bad06

instance (X : Finset (ZMod 7)) : Decidable (avoids06 X) :=
  inferInstanceAs (Decidable (∀ x ∈ X, x ∉ bad06))

theorem avoids06_mono {X Y : Finset (ZMod 7)} (hXY : X ⊆ Y) (hY : avoids06 Y) :
    avoids06 X := fun x hx => hY x (hXY hx)

theorem avoids06_union {X Y : Finset (ZMod 7)} :
    avoids06 (X ∪ Y) ↔ avoids06 X ∧ avoids06 Y := by
  constructor
  · intro h
    exact ⟨fun x hx => h x (Finset.mem_union_left _ hx),
      fun x hx => h x (Finset.mem_union_right _ hx)⟩
  · rintro ⟨hX, hY⟩ x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact hX x hx
    · exact hY x hx

theorem avoids06_empty : avoids06 (∅ : Finset (ZMod 7)) := fun _ h => by simp at h

/-- Three-way union split (right-nested, matching `X ∪ Y ∪ Z`). -/
theorem avoids06_union3 {X Y Z : Finset (ZMod 7)} :
    avoids06 (X ∪ Y ∪ Z) ↔ avoids06 X ∧ avoids06 Y ∧ avoids06 Z := by
  rw [avoids06_union, avoids06_union, and_assoc]

theorem mem_cycIv {i x : ZMod 7} {L : ℕ} : x ∈ cycIv i L ↔ (x - i).val < L := by
  simp [cycIv]

theorem cycIv_zero (i : ZMod 7) : cycIv i 0 = ∅ := by
  ext x; simp [mem_cycIv]

private theorem eq_zero_of_val_eq_zero {x : ZMod 7} (h : x.val = 0) : x = 0 := by
  have e : ((x.val : ℕ) : ZMod 7) = (0 : ZMod 7) := by rw [h]; decide
  rwa [ZMod.natCast_zmod_val] at e

private theorem eq_one_of_val_eq_one {x : ZMod 7} (h : x.val = 1) : x = 1 := by
  have e : ((x.val : ℕ) : ZMod 7) = (1 : ZMod 7) := by rw [h]; decide
  rwa [ZMod.natCast_zmod_val] at e

theorem cycIv_one (i : ZMod 7) : cycIv i 1 = {i} := by
  ext x
  rw [mem_cycIv]
  constructor
  · intro h
    have h0 : (x - i).val = 0 := by omega
    rw [Finset.mem_singleton]
    exact sub_eq_zero.mp (eq_zero_of_val_eq_zero h0)
  · intro h
    rw [Finset.mem_singleton] at h
    rw [h]; simp

theorem cycIv_two (i : ZMod 7) : cycIv i 2 = {i, i + 1} := by
  ext x
  rw [mem_cycIv]
  constructor
  · intro h
    have h2 : (x - i).val = 0 ∨ (x - i).val = 1 := by omega
    rcases h2 with h2 | h2
    · have hxi : x - i = 0 := eq_zero_of_val_eq_zero h2
      rw [sub_eq_zero.mp hxi]
      exact Finset.mem_insert_self _ _
    · have hxi : x - i = 1 := eq_one_of_val_eq_one h2
      rw [show x = i + 1 by rw [← hxi]; ring]
      exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self _))
  · intro h
    rw [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with rfl | rfl
    · simp
    · have e : (i + 1 - i : ZMod 7) = 1 := by ring
      rw [e]; decide

theorem cycIv_image_add (i t : ZMod 7) (L : ℕ) :
    (cycIv i L).image (· + t) = cycIv (i + t) L := by
  ext x
  simp only [Finset.mem_image, mem_cycIv]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have e : y + t - (i + t) = y - i := by ring
    rwa [e]
  · intro h
    refine ⟨x - t, ?_, by ring⟩
    have e : x - t - i = x - (i + t) := by ring
    rwa [e]

/-- Transport: if `X ⊆ cycIv i L` and the shifted interval avoids `{0,6}`,
then the shifted `X` avoids `{0,6}` too. -/
theorem avoids06_of_subset_shift {X : Finset (ZMod 7)} {i t : ZMod 7} {L : ℕ}
    (hX : X ⊆ cycIv i L) (h : avoids06 (cycIv (i + t) L)) :
    avoids06 (X.image (· + t)) :=
  avoids06_mono ((Finset.image_subset_image hX).trans
    (cycIv_image_add i t L ▸ Finset.Subset.refl _)) h

theorem cycIv_seven (i : ZMod 7) : cycIv i 7 = Finset.univ := by
  ext x
  rw [mem_cycIv]
  exact iff_of_true (ZMod.val_lt _) (Finset.mem_univ x)

theorem apLen_le_seven (X : Finset (ZMod 7)) : apLen X ≤ 7 := by
  rw [apLen_le_iff X 7 le_rfl]
  exact ⟨0, by rw [cycIv_seven]; exact Finset.subset_univ X⟩

theorem apLen_empty : apLen (∅ : Finset (ZMod 7)) = 0 := by
  apply Nat.eq_zero_of_le_zero
  rw [apLen_le_iff ∅ 0 (by norm_num)]
  exact ⟨0, Finset.empty_subset _⟩

theorem nonempty_of_apLen_pos {X : Finset (ZMod 7)} (h : 0 < apLen X) :
    X.Nonempty := by
  rcases Finset.eq_empty_or_nonempty X with rfl | hne
  · rw [apLen_empty] at h; exact absurd h (lt_irrefl _)
  · exact hne

theorem eq_singleton_of_apLen_one {X : Finset (ZMod 7)} (h : apLen X = 1) :
    ∃ i : ZMod 7, X = {i} := by
  obtain ⟨i, hi⟩ := (apLen_le_iff X 1 (by norm_num)).mp (h ▸ le_rfl)
  rw [cycIv_one] at hi
  have hne : X.Nonempty := nonempty_of_apLen_pos (h ▸ by norm_num)
  rcases Finset.subset_singleton_iff.mp hi with hX | hX
  · rw [hX] at hne; exact absurd hne (by simp)
  · exact ⟨i, hX⟩

theorem card_le_one_imp_apLen_le_one {X : Finset (ZMod 7)} (h : X.card ≤ 1) :
    apLen X ≤ 1 := by
  rcases Finset.eq_empty_or_nonempty X with rfl | ⟨a, ha⟩
  · rw [apLen_empty]; norm_num
  · have hsub : X ⊆ {a} := fun b hb =>
        Finset.mem_singleton.mpr (Finset.card_le_one.mp h a ha b hb).symm
    rw [apLen_le_iff X 1 (by norm_num)]
    exact ⟨a, by rwa [cycIv_one]⟩

theorem one_lt_card_of_apLen_ge_two {X : Finset (ZMod 7)} (h : 2 ≤ apLen X) :
    1 < X.card := by
  by_contra hc
  push Not at hc
  have := card_le_one_imp_apLen_le_one hc
  omega

theorem add_one_ne_self (i : ZMod 7) : i + 1 ≠ i := by
  intro h
  have h1 : i + 1 = i + 0 := by rw [h, add_zero]
  exact absurd (add_left_cancel_iff.mp h1) (by decide)

/-- A cyclic interval `{1,…,L}` of length `≤ 5` avoids `{0,6}`. -/
private theorem avoids06_cycIv_one {L : ℕ} (hL : L ≤ 5) :
    avoids06 (cycIv 1 L) := by
  intro x hx
  rw [mem_cycIv] at hx
  simp only [bad06, Finset.mem_insert, Finset.mem_singleton, not_or]
  refine ⟨?_, ?_⟩ <;> rintro rfl
  · have e : ((0 : ZMod 7) - 1).val = 6 := by decide
    rw [e] at hx; omega
  · have e : ((6 : ZMod 7) - 1).val = 5 := by decide
    rw [e] at hx; omega

/-- Shift lemma (paper's basic `Λ₀` move): a residue set covered by a cyclic
interval of length `≤ 5` has a translate by `t` avoiding `{0,6}` — the
complement `{1,2,3,4,5}` is a cyclic interval of length `5`. -/
theorem exists_shift_avoid {X : Finset (ZMod 7)} {i : ZMod 7} {L : ℕ}
    (hL : L ≤ 5) (hX : X ⊆ cycIv i L) :
    ∃ t : ZMod 7, avoids06 (X.image (· + t)) := by
  refine ⟨1 - i, avoids06_of_subset_shift hX ?_⟩
  rw [show i + (1 - i) = 1 by ring]
  exact avoids06_cycIv_one hL

/-! ### Remark 8 (paper) — `ZMod 7` finite checks

Paper statement: `q(X−X) ⊂ {0,6} ⇒ ℓ(k·X) ≤ k+1` and
`q(X−X) ⊂ {0,1,5,6} ⇒ ℓ(X) ≤ 3`. The Z₇-level model uses residue
differences: `∀ x y ∈ B, x − y ∈ {0,±1}` resp. `{0,±1,±2}`. -/

private theorem remark8_i_dec :
    ∀ B : Finset (ZMod 7),
      (∀ x ∈ B, ∀ y ∈ B, x - y ∈ ({0, 1, 6} : Finset (ZMod 7))) →
      ∀ k : ZMod 7, k ≠ 0 → apLen (B.image (· * k)) ≤ k.val + 1 := by
  set_option maxRecDepth 16384 in
  decide

/-- **Remark 8 (i)**: if all pairwise differences of `B` lie in `{0,±1}`, then
each nonzero dilation `k·B` has `apLen ≤ k+1` (paper: `1 ≤ k ≤ 6`, i.e.
`k ≠ 0` in `ZMod 7`). -/
theorem remark8_i {B : Finset (ZMod 7)}
    (hB : ∀ x ∈ B, ∀ y ∈ B, (x - y : ZMod 7) ∈ ({0, 1, 6} : Finset (ZMod 7)))
    {k : ZMod 7} (hk : k ≠ 0) :
    apLen (B.image (· * k)) ≤ k.val + 1 := remark8_i_dec B hB k hk

private theorem remark8_ii_dec :
    ∀ B : Finset (ZMod 7),
      (∀ x ∈ B, ∀ y ∈ B, x - y ∈ ({0, 1, 5, 6} : Finset (ZMod 7))) →
      apLen B ≤ 3 := by
  set_option maxRecDepth 16384 in
  decide

/-- **Remark 8 (ii)**: if all pairwise differences of `B` lie in `{0,±1,±2}`,
then `apLen B ≤ 3`. -/
theorem remark8_ii {B : Finset (ZMod 7)}
    (hB : ∀ x ∈ B, ∀ y ∈ B, x - y ∈ ({0, 1, 5, 6} : Finset (ZMod 7))) :
    apLen B ≤ 3 := remark8_ii_dec B hB

#print axioms remark8_i
#print axioms remark8_ii

/-! ### Lemma 5 (paper) — the `Λ₀`-compression finishing lemma

Paper: `ℓ(A₁)+ℓ(A₂)+ℓ(A₄) ≤ 5 ⇒ ∃λ ∈ Λ₀ : q(λA) ∩ {0,6} = ∅`, unless
`(ℓ) = (3,1,1)` and `ẽ(d,d') ∈ {2,4}` for each `d ∈ A₂, d' ∈ A₄`.

The Z₇ model: with `t` the `Λ₀` shift on `A₁` (`A₂` shifts by `2t`, `A₄` by
`4t`), either some `t` makes the union avoid `{0,6}`, or we are in the
`(3,1,1)` shape with `2d − d' ∈ {2,4}` for all `d ∈ A₂, d' ∈ A₄`
(the `ẽ` expression `2q(d) − q(d')` for `r(d') = 2r(d)`).

The ordering hypothesis `hord : apLen A₂ ≤ apLen A₁ ∧ apLen A₄ ≤ apLen A₁`
encodes the paper's "A₁ a class with larger length" convention — without it
the `(1,1,3)`/`(1,3,1)` shapes are genuine counterexamples (verified by
exhaustive check). -/

private theorem lemma5_core :
    ∀ l₁ ∈ Finset.range 6, ∀ l₂ ∈ Finset.range 6, ∀ l₄ ∈ Finset.range 6,
      l₁ + l₂ + l₄ ≤ 5 →
      l₂ ≤ l₁ → l₄ ≤ l₁ → ∀ j₂ j₄ : ZMod 7,
      (∃ u : ZMod 7, avoids06 (cycIv u l₁) ∧
          avoids06 (cycIv (j₂ + 2 * u) l₂) ∧
          avoids06 (cycIv (j₄ + 4 * u) l₄)) ∨
      (l₁ = 3 ∧ l₂ = 1 ∧ l₄ = 1 ∧
        (2 * j₂ - j₄ : ZMod 7) ∈ ({2, 4} : Finset (ZMod 7))) := by
  set_option maxRecDepth 32768 in
  decide

/-- **Lemma 5**: three-class compression. See module docstring for the
`Λ₀`-shift convention; `s` is the congruence class of `A₁`
(`s ∈ {1,2,4}`, caller-side marker used to build `λ_k = 1+7^m·k·s⁻¹`). -/
theorem lemma5 {A₁ A₂ A₄ : Finset (ZMod 7)} (s : ZMod 7)
    (_hs : s ∈ ({1, 2, 4} : Finset (ZMod 7)))
    (hord : apLen A₂ ≤ apLen A₁ ∧ apLen A₄ ≤ apLen A₁)
    (h : apLen A₁ + apLen A₂ + apLen A₄ ≤ 5) :
    (∃ t : ZMod 7, avoids06
        ((A₁.image (· + t)) ∪ (A₂.image (· + 2 * t)) ∪ (A₄.image (· + 4 * t)))) ∨
    (apLen A₁ = 3 ∧ apLen A₂ = 1 ∧ apLen A₄ = 1 ∧
      ∀ d ∈ A₂, ∀ d' ∈ A₄, (2 * d - d' : ZMod 7) ∈ ({2, 4} : Finset (ZMod 7))) := by
  have hl1 : apLen A₁ ≤ 5 := by omega
  have hl2 : apLen A₂ ≤ 5 := by omega
  have hl4 : apLen A₄ ≤ 5 := by omega
  obtain ⟨i₁, hi₁⟩ := (apLen_le_iff A₁ (apLen A₁) (apLen_le_seven _)).mp le_rfl
  obtain ⟨i₂, hi₂⟩ := (apLen_le_iff A₂ (apLen A₂) (apLen_le_seven _)).mp le_rfl
  obtain ⟨i₄, hi₄⟩ := (apLen_le_iff A₄ (apLen A₄) (apLen_le_seven _)).mp le_rfl
  have hc := lemma5_core (apLen A₁) (Finset.mem_range.mpr (by omega))
      (apLen A₂) (Finset.mem_range.mpr (by omega))
      (apLen A₄) (Finset.mem_range.mpr (by omega)) h hord.1 hord.2
      (i₂ - 2 * i₁) (i₄ - 4 * i₁)
  rcases hc with ⟨u, hu1, hu2, hu4⟩ | ⟨e1, e2, e4, he⟩
  · refine Or.inl ⟨u - i₁, ?_⟩
    rw [avoids06_union3]
    refine ⟨?_, ?_, ?_⟩
    · refine avoids06_of_subset_shift hi₁ ?_
      rw [show i₁ + (u - i₁) = u by ring]
      exact hu1
    · refine avoids06_of_subset_shift hi₂ ?_
      rw [show i₂ + 2 * (u - i₁) = (i₂ - 2 * i₁) + 2 * u by ring]
      exact hu2
    · refine avoids06_of_subset_shift hi₄ ?_
      rw [show i₄ + 4 * (u - i₁) = (i₄ - 4 * i₁) + 4 * u by ring]
      exact hu4
  · have hl1' : apLen A₁ = 3 := e1
    have hl2' : apLen A₂ = 1 := e2
    have hl4' : apLen A₄ = 1 := e4
    have hA2 : A₂ = {i₂} := by
      have hne := nonempty_of_apLen_pos (by omega : 0 < apLen A₂)
      rw [hl2', cycIv_one] at hi₂
      rcases Finset.subset_singleton_iff.mp hi₂ with hX | hX
      · rw [hX] at hne; exact absurd hne (by simp)
      · exact hX
    have hA4 : A₄ = {i₄} := by
      have hne := nonempty_of_apLen_pos (by omega : 0 < apLen A₄)
      rw [hl4', cycIv_one] at hi₄
      rcases Finset.subset_singleton_iff.mp hi₄ with hX | hX
      · rw [hX] at hne; exact absurd hne (by simp)
      · exact hX
    refine Or.inr ⟨hl1', hl2', hl4', ?_⟩
    intro d hd d' hd'
    rw [hA2, Finset.mem_singleton] at hd
    rw [hA4, Finset.mem_singleton] at hd'
    rw [hd, hd']
    have e : (2 : ZMod 7) * i₂ - i₄ = 2 * (i₂ - 2 * i₁) - (i₄ - 4 * i₁) := by ring
    rw [e]; exact he

/-! ### Lemma 6 (paper) — specific length triples

Paper: `q(A₁) ⊂ {1,…,ℓ(A₁)}`, `d ∈ A₁` with `q(d) = 1` ⇒ `∃λ ∈ Λ₀` covering
when one of the length-triple conditions holds, with `ẽ` side-conditions.
Our `ẽ` expressions use the normalized anchor `q(d) = 1`:
`ẽ(d,d') = 2q(d') − 1` for `d' ∈ A₄`, `ẽ(d,d') = 2 − q(d')` for `d' ∈ A₂`. -/

private theorem lemma6_core_501 :
    ∀ i₄ : ZMod 7, (2 * i₄ - 1 : ZMod 7) ∉ ({4, 6} : Finset (ZMod 7)) →
      ∃ u : ZMod 7, avoids06 (cycIv (1 + u) 5) ∧
        avoids06 (cycIv (i₄ + 4 * u) 1) := by
  decide

private theorem lemma6_core_510 :
    ∀ i₂ : ZMod 7, (2 - i₂ : ZMod 7) ∉ ({2, 3} : Finset (ZMod 7)) →
      ∃ u : ZMod 7, avoids06 (cycIv (1 + u) 5) ∧
        avoids06 (cycIv (i₂ + 2 * u) 1) := by
  decide

private theorem lemma6_core_402 :
    ∀ i₄ : ZMod 7, ∃ u : ZMod 7, avoids06 (cycIv (1 + u) 4) ∧
      avoids06 (cycIv (i₄ + 4 * u) 2) := by
  decide

private theorem lemma6_core_420 :
    ∀ i₂ : ZMod 7, (2 - i₂ : ZMod 7) ≠ 4 →
      ∃ u : ZMod 7, avoids06 (cycIv (1 + u) 4) ∧
        avoids06 (cycIv (i₂ + 2 * u) 2) := by
  decide

private theorem lemma6_core_330 :
    ∀ i₂ : ZMod 7, ∃ u : ZMod 7, avoids06 (cycIv (1 + u) 3) ∧
      avoids06 (cycIv (i₂ + 2 * u) 3) := by
  decide

private theorem lemma6_core_303 :
    ∀ i₄ : ZMod 7, ∃ u : ZMod 7, avoids06 (cycIv (1 + u) 3) ∧
      avoids06 (cycIv (i₄ + 4 * u) 3) := by
  decide

private theorem eq_empty_of_apLen_zero {X : Finset (ZMod 7)} (h : apLen X = 0) :
    X = ∅ := by
  obtain ⟨i, hi⟩ := (apLen_le_iff X 0 (by norm_num)).mp (h ▸ le_rfl)
  rw [cycIv_zero] at hi
  exact Finset.subset_empty.mp hi

private theorem avoids06_shift_empty (t : ZMod 7) :
    avoids06 ((∅ : Finset (ZMod 7)).image (· + t)) := fun _ h => by
  simp at h

/-- **Lemma 6**: the six length-triple cases of paper Lemma 6.
`hA1` is the normalization `q(A₁) ⊂ {1,…,ℓ(A₁)}`; `hd` supplies the anchor
element `d ∈ A₁` with `q(d) = 1` (used by callers to form the `ẽ`
expressions). -/
theorem lemma6 {A₁ A₂ A₄ : Finset (ZMod 7)} (s : ZMod 7)
    (_hs : s ∈ ({1, 2, 4} : Finset (ZMod 7)))
    (_hd : (1 : ZMod 7) ∈ A₁)
    (hA1 : A₁ ⊆ cycIv 1 (apLen A₁))
    (h : (apLen A₁ = 5 ∧ apLen A₂ = 0 ∧ apLen A₄ = 1 ∧
            ∀ d' ∈ A₄, (2 * d' - 1 : ZMod 7) ∉ ({4, 6} : Finset (ZMod 7)))
       ∨ (apLen A₁ = 5 ∧ apLen A₂ = 1 ∧ apLen A₄ = 0 ∧
            ∀ d' ∈ A₂, (2 - d' : ZMod 7) ∉ ({2, 3} : Finset (ZMod 7)))
       ∨ (apLen A₁ = 4 ∧ apLen A₂ = 0 ∧ apLen A₄ = 2)
       ∨ (apLen A₁ = 4 ∧ apLen A₂ = 2 ∧ apLen A₄ = 0 ∧
            ∀ d' ∈ A₂, (d' + 1 : ZMod 7) ∈ A₂ → (2 - d' : ZMod 7) ≠ 4)
       ∨ (apLen A₁ = 3 ∧ apLen A₂ = 3 ∧ apLen A₄ = 0)
       ∨ (apLen A₁ = 3 ∧ apLen A₂ = 0 ∧ apLen A₄ = 3)) :
    ∃ t : ZMod 7, avoids06
      ((A₁.image (· + t)) ∪ (A₂.image (· + 2 * t)) ∪ (A₄.image (· + 4 * t))) := by
  rcases h with ⟨h1, h2, h4, he⟩ | ⟨h1, h2, h4, he⟩ | ⟨h1, h2, h4⟩ |
      ⟨h1, h2, h4, he⟩ | ⟨h1, h2, h4⟩ | ⟨h1, h2, h4⟩
  · -- (5,0,1), ẽ(d,d') = 2q(d')−1 ∉ {4,6} for d' ∈ A₄
    rw [h1] at hA1
    obtain ⟨i₄, hi₄⟩ := (apLen_le_iff A₄ 1 (by norm_num)).mp (h4 ▸ le_rfl)
    have hne : A₄.Nonempty := nonempty_of_apLen_pos (by omega)
    have hA4 : A₄ = {i₄} := by
      have hi₄' : A₄ ⊆ {i₄} := by rwa [cycIv_one] at hi₄
      rcases Finset.subset_singleton_iff.mp hi₄' with hX | hX
      · rw [hX] at hne; exact absurd hne (by simp)
      · exact hX
    have he' : (2 * i₄ - 1 : ZMod 7) ∉ ({4, 6} : Finset (ZMod 7)) :=
      he i₄ (by rw [hA4]; exact Finset.mem_singleton_self i₄)
    obtain ⟨u, hu1, hu4⟩ := lemma6_core_501 i₄ he'
    refine ⟨u, ?_⟩
    rw [avoids06_union3]
    refine ⟨avoids06_of_subset_shift hA1 hu1, ?_, avoids06_of_subset_shift hi₄ hu4⟩
    · rw [eq_empty_of_apLen_zero h2]
      exact avoids06_shift_empty _
  · -- (5,1,0), ẽ(d,d') = 2−q(d') ∉ {2,3} for d' ∈ A₂
    rw [h1] at hA1
    obtain ⟨i₂, hi₂⟩ := (apLen_le_iff A₂ 1 (by norm_num)).mp (h2 ▸ le_rfl)
    have hne : A₂.Nonempty := nonempty_of_apLen_pos (by omega)
    have hA2 : A₂ = {i₂} := by
      have hi₂' : A₂ ⊆ {i₂} := by rwa [cycIv_one] at hi₂
      rcases Finset.subset_singleton_iff.mp hi₂' with hX | hX
      · rw [hX] at hne; exact absurd hne (by simp)
      · exact hX
    have he' : (2 - i₂ : ZMod 7) ∉ ({2, 3} : Finset (ZMod 7)) :=
      he i₂ (by rw [hA2]; exact Finset.mem_singleton_self i₂)
    obtain ⟨u, hu1, hu2⟩ := lemma6_core_510 i₂ he'
    refine ⟨u, ?_⟩
    rw [avoids06_union3]
    refine ⟨avoids06_of_subset_shift hA1 hu1, avoids06_of_subset_shift hi₂ hu2, ?_⟩
    · rw [eq_empty_of_apLen_zero h4]
      exact avoids06_shift_empty _
  · -- (4,0,2), no side condition
    rw [h1] at hA1
    obtain ⟨i₄, hi₄⟩ := (apLen_le_iff A₄ 2 (by norm_num)).mp (h4 ▸ le_rfl)
    obtain ⟨u, hu1, hu4⟩ := lemma6_core_402 i₄
    refine ⟨u, ?_⟩
    rw [avoids06_union3]
    refine ⟨avoids06_of_subset_shift hA1 hu1, ?_, avoids06_of_subset_shift hi₄ hu4⟩
    · rw [eq_empty_of_apLen_zero h2]
      exact avoids06_shift_empty _
  · -- (4,2,0), ẽ(d,d') = 2−q(d') ≠ 4 for the lower element d' of A₂
    rw [h1] at hA1
    obtain ⟨i₂, hi₂⟩ := (apLen_le_iff A₂ 2 (by norm_num)).mp (h2 ▸ le_rfl)
    have hA2 : A₂ = {i₂, i₂ + 1} := by
      have hcard : 1 < A₂.card := one_lt_card_of_apLen_ge_two (by omega)
      have hi₂' : A₂ ⊆ {i₂, i₂ + 1} := by rwa [cycIv_two] at hi₂
      refine Finset.eq_of_subset_of_card_le hi₂' ?_
      rw [Finset.card_pair (add_one_ne_self i₂).symm]
      exact hcard
    have hi₂mem : i₂ ∈ A₂ := by rw [hA2]; exact Finset.mem_insert_self _ _
    have hi₂1mem : i₂ + 1 ∈ A₂ := by
      rw [hA2]; exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self _))
    have he' : (2 - i₂ : ZMod 7) ≠ 4 := he i₂ hi₂mem hi₂1mem
    obtain ⟨u, hu1, hu2⟩ := lemma6_core_420 i₂ he'
    refine ⟨u, ?_⟩
    rw [avoids06_union3]
    refine ⟨avoids06_of_subset_shift hA1 hu1, avoids06_of_subset_shift hi₂ hu2, ?_⟩
    · rw [eq_empty_of_apLen_zero h4]
      exact avoids06_shift_empty _
  · -- (3,3,0), no side condition
    rw [h1] at hA1
    obtain ⟨i₂, hi₂⟩ := (apLen_le_iff A₂ 3 (by norm_num)).mp (h2 ▸ le_rfl)
    obtain ⟨u, hu1, hu2⟩ := lemma6_core_330 i₂
    refine ⟨u, ?_⟩
    rw [avoids06_union3]
    refine ⟨avoids06_of_subset_shift hA1 hu1, avoids06_of_subset_shift hi₂ hu2, ?_⟩
    · rw [eq_empty_of_apLen_zero h4]
      exact avoids06_shift_empty _
  · -- (3,0,3), no side condition
    rw [h1] at hA1
    obtain ⟨i₄, hi₄⟩ := (apLen_le_iff A₄ 3 (by norm_num)).mp (h4 ▸ le_rfl)
    obtain ⟨u, hu1, hu4⟩ := lemma6_core_303 i₄
    refine ⟨u, ?_⟩
    rw [avoids06_union3]
    refine ⟨avoids06_of_subset_shift hA1 hu1, ?_, avoids06_of_subset_shift hi₄ hu4⟩
    · rw [eq_empty_of_apLen_zero h2]
      exact avoids06_shift_empty _

#print axioms lemma5
#print axioms lemma6

/-! ### Lemma 12 (paper) — `|A₁| = 3`, `|A₂| = 2` multiplier counting

Paper: `d ∈ A₁` anchors `q(A₁) ⊂ {q(d),…,q(d)+ℓ(A₁)−1}`, `d' ∈ A₂`.
(i) `ℓ(A₁) ≤ 3`: three good multipliers `k ∈ {0,1,2}` for `A₁`, at most one
bad for each of the two `A₂` elements.
(ii) `ℓ(A₁) = 4` and `ẽ(d,d') ∈ {0,1,6}` (i.e. `2−q(d') ∈ {0,1,6}`): `d'` is
good at `k = 0,1`, the second element spoils at most one. -/

private theorem lemma12_core_i :
    ∀ A₂ : Finset (ZMod 7), A₂.card ≤ 2 → ∀ m ∈ Finset.range 4,
      ∃ k ∈ ({0, 1, 2} : Finset (ZMod 7)),
        avoids06 (cycIv (1 + k) m) ∧ avoids06 (A₂.image (· + 2 * k)) := by
  set_option maxRecDepth 16384 in
  decide

private theorem lemma12_core_ii :
    ∀ A₂ : Finset (ZMod 7), A₂.card ≤ 2 →
      (∃ d' ∈ A₂, (2 - d' : ZMod 7) ∈ ({0, 1, 6} : Finset (ZMod 7))) →
      ∃ k ∈ ({0, 1, 2} : Finset (ZMod 7)),
        avoids06 (cycIv (1 + k) 4) ∧ avoids06 (A₂.image (· + 2 * k)) := by
  set_option maxRecDepth 16384 in
  decide

/-- **Lemma 12**: `|A₁| = 3`, `|A₂| = 2` (modeled as `A₂.card ≤ 2`).
`hd` is the anchor element with `q(d) = 1` and `hA1` the normalized
covering `q(A₁) ⊂ {1,…,ℓ(A₁)}`; `h` is the case disjunction
`ℓ(A₁) ≤ 3` or `ℓ(A₁) = 4` with `ẽ(d,d') = 2−q(d') ∈ {0,1,6}` for some
`d' ∈ A₂`. -/
theorem lemma12 {A₁ A₂ : Finset (ZMod 7)} (s : ZMod 7)
    (_hs : s ∈ ({1, 2, 4} : Finset (ZMod 7)))
    (_hd : (1 : ZMod 7) ∈ A₁)
    (hA2 : A₂.card ≤ 2)
    (hA1 : A₁ ⊆ cycIv 1 (apLen A₁))
    (h : apLen A₁ ≤ 3 ∨ (apLen A₁ = 4 ∧
        ∃ d' ∈ A₂, (2 - d' : ZMod 7) ∈ ({0, 1, 6} : Finset (ZMod 7)))) :
    ∃ k ∈ ({0, 1, 2} : Finset (ZMod 7)),
      avoids06 ((A₁.image (· + k)) ∪ (A₂.image (· + 2 * k))) := by
  rcases h with hl | ⟨hl, he⟩
  · have hl4 : apLen A₁ < 4 := by omega
    obtain ⟨k, hk, h1k, h2k⟩ :=
      lemma12_core_i A₂ hA2 (apLen A₁) (Finset.mem_range.mpr hl4)
    refine ⟨k, hk, ?_⟩
    rw [avoids06_union]
    exact ⟨avoids06_of_subset_shift hA1 h1k, h2k⟩
  · rw [hl] at hA1
    obtain ⟨k, hk, h1k, h2k⟩ := lemma12_core_ii A₂ hA2 he
    refine ⟨k, hk, ?_⟩
    rw [avoids06_union]
    exact ⟨avoids06_of_subset_shift hA1 h1k, h2k⟩

#print axioms lemma12
#print axioms exists_shift_avoid
