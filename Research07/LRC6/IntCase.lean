/-
Copyright (c) 2026 Research07 contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Research07 contributors
-/
import Mathlib
import Research07.LRC6.Setup
import Research07.LRC6.Extremize
import Research07.LRC6.Driver
import Research07.LRC6.Reduction
import Research07.LRC6.Signed
import Research07.LRC6.Prop31
import Research07.LRC6.Prop41
import Research07.LRC6.Prop54
import Research07.LRC6.Prop66

/-!
# integer case dispatch for `n = 6`

Under `hfail D` (no good time exists), Renault's Sections 3–6 give a
contradiction for every residue configuration:

* `(D.filter (3 ∣ ·)).card = 3` → Lemma 2.3 (`lemma2_3`)
* `= 2` → Proposition 3.1 (`prop3_1`)
* `= 1` → the unique multiple of 3 is the multiple of 6 (Lemma 2.1);
  the other four speeds have residues `±1`/`±2`, and the parity count of the
  `±2`-guards dispatches to Prop 5.4 (0), Prop 6.6 (1), Prop 4.1 (≥2).
  `even_le_three` (Lemma 2.1 for `l = 2`) caps the total at 3, so `≥2`
  `±2`-guards means exactly two, fitting `prop4_1`'s hypotheses.

The gcd reduction `lrc6_case` scales an arbitrary `D` by `D.gcd id`;
`mult3_le_three` and `even_le_three` need `gcd = 1`.
-/

noncomputable section

/-- Under `hfail` and `gcd = 1`, at most three speeds are even
(Lemma 2.1's `l = 2` bound). -/
theorem even_le_three {D : Finset ℕ} (hpos : ∀ d ∈ D, 0 < d) (hcard : D.card ≤ 5)
    (hgcd : D.gcd id = 1) (hf : hfail D) :
    (D.filter fun d => 2 ∣ d).card ≤ 3 := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨T, hTD, hTcard⟩ := Finset.le_card_iff_exists_subset_card.mp
    (show 4 ≤ (D.filter fun d => 2 ∣ d).card by omega)
  have hTD' : T ⊆ D := fun d hd => (Finset.mem_filter.mp (hTD hd)).1
  have hTeven : ∀ d ∈ T, 2 ∣ d :=
    fun d hd => (Finset.mem_filter.mp (hTD hd)).2
  obtain ⟨τ, _, hτ⟩ := lrc5_int T (fun d hd => hpos d (hTD' hd)) (le_of_eq hTcard)
  have hTsafe : ∀ d ∈ T, safe6 d τ :=
    fun d hd => safe6_of_circ_ge_fifth (hτ d hd)
  -- `D \ T` has at most one element `d₀`.
  have hDT : (D \ T).card ≤ 1 := by
    have := Finset.card_sdiff_add_card_eq_card hTD'
    omega
  obtain ⟨d₀, hd₀, hd₀u⟩ := hf τ
  have hd₀T : d₀ ∉ T := fun h => hd₀u (hTsafe d₀ h)
  have hd₀mem : d₀ ∈ D \ T := Finset.mem_sdiff.mpr ⟨hd₀, hd₀T⟩
  -- `d₀` is also unsafe at `τ + 1/2` if it is even; but then all of `D` is
  -- even, contradicting `gcd = 1`.
  by_cases hev : 2 ∣ d₀
  · -- every `d ∈ D` is even: `d ∈ T` is even, `d ∈ D\T` equals `d₀`.
    have hall : ∀ d ∈ D, 2 ∣ d := by
      intro d hd
      by_cases hdt : d ∈ T
      · exact hTeven d hdt
      · have : d ∈ D \ T := Finset.mem_sdiff.mpr ⟨hd, hdt⟩
        have : d = d₀ := Finset.card_le_one.mp hDT d this d₀ hd₀mem
        rw [this]; exact hev
    have hg2 : 2 ∣ D.gcd id :=
      Finset.dvd_gcd (fun d hd => hall d hd)
    rw [hgcd] at hg2
    exact absurd hg2 (by norm_num)
  · -- `d₀` odd: at `τ + 1/2` every `d ∈ T` stays safe, so the witness of
    -- `hfail (τ+1/2)` is again `d₀` — impossible since the two bad arcs are
    -- disjoint.
    have hTsafe' : ∀ d ∈ T, safe6 d (τ + 1 / 2) :=
      fun d hd => (safe6_half_shift_of_dvd (hTeven d hd) τ).mpr (hTsafe d hd)
    obtain ⟨d₁, hd₁, hd₁u⟩ := hf (τ + 1 / 2)
    have hd₁T : d₁ ∉ T := fun h => hd₁u (hTsafe' d₁ h)
    have hd₁mem : d₁ ∈ D \ T := Finset.mem_sdiff.mpr ⟨hd₁, hd₁T⟩
    have heq : d₁ = d₀ := Finset.card_le_one.mp hDT d₁ hd₁mem d₀ hd₀mem
    rw [heq] at hd₁u
    -- `d₀` unsafe at `τ` and `τ + 1/2` simultaneously.
    have h2 : d₀ % 2 = 1 := by
      by_contra hc
      have : d₀ % 2 = 0 := by omega
      exact hev (Nat.dvd_of_mod_eq_zero this)
    obtain ⟨m, hm⟩ : ∃ m : ℕ, d₀ = 2 * m + 1 := ⟨d₀ / 2, by omega⟩
    have e : (d₀ : ℝ) * (τ + 1 / 2) =
        ((m : ℤ) : ℝ) + ((d₀ : ℝ) * τ + 1 / 2) := by
      rw [hm]; push_cast; ring
    unfold safe6 at hd₁u
    rw [e, Int.fract_intCast_add] at hd₁u
    -- `x ∈ (5/6,1/6)` ⇒ `x + 1/2 ∈ [1/3,2/3]` — contradiction.
    have hu := unsafe_arc hd₀u
    have hfn := Int.fract_nonneg ((d₀ : ℝ) * τ)
    have hf1 := Int.fract_lt_one ((d₀ : ℝ) * τ)
    have hself := Int.self_sub_fract ((d₀ : ℝ) * τ)
    have hf2 : Int.fract ((d₀ : ℝ) * τ + 1 / 2) ∈ Set.Icc (1 / 6) (5 / 6) := by
      rcases hu with h | h
      · -- `fract < 1/6` ⇒ `fract + 1/2 ∈ (1/2, 2/3)`
        have e2 : Int.fract ((d₀ : ℝ) * τ + 1 / 2) =
            Int.fract ((d₀ : ℝ) * τ) + 1 / 2 := by
          rw [Int.fract_eq_iff]
          refine ⟨by linarith, by linarith, ⌊(d₀ : ℝ) * τ⌋, ?_⟩
          push_cast at hself ⊢
          linarith
        rw [e2]
        exact Set.mem_Icc.mpr ⟨by linarith, by linarith⟩
      · -- `fract > 5/6` ⇒ `fract + 1/2 - 1 ∈ (1/3, 1/2)`
        have e2 : Int.fract ((d₀ : ℝ) * τ + 1 / 2) =
            Int.fract ((d₀ : ℝ) * τ) + 1 / 2 - 1 := by
          rw [Int.fract_eq_iff]
          refine ⟨by linarith, by linarith, ⌊(d₀ : ℝ) * τ⌋ + 1, ?_⟩
          push_cast at hself ⊢
          linarith
        rw [e2]
        exact Set.mem_Icc.mpr ⟨by linarith, by linarith⟩
    exact hd₁u hf2

/-- A speed `≡ ±2 (mod 6)` is even. -/
private theorem dvd_two_of_modeq {d : ℕ} {e : ℤ} (he : e = 2 ∨ e = -2)
    (h : (d : ℤ) ≡ e [ZMOD 6]) : 2 ∣ d := by
  rcases he with rfl | rfl
  · have h' : (d : ℤ) % 6 = 2 := h
    have hd2 : (2 : ℤ) ∣ d := by omega
    exact_mod_cast hd2
  · have h' : (d : ℤ) % 6 = -2 % 6 := h
    norm_num at h'
    have hd2 : (2 : ℤ) ∣ d := by omega
    exact_mod_cast hd2

/-- A speed `≡ ±1 (mod 6)` is odd. -/
private theorem not_dvd_two_of_modeq {d : ℕ} {e : ℤ} (he : e = 1 ∨ e = -1)
    (h : (d : ℤ) ≡ e [ZMOD 6]) : ¬ 2 ∣ d := by
  rcases he with rfl | rfl
  · have h' : (d : ℤ) % 6 = 1 := h
    rintro ⟨k, hk⟩
    have hk' : (d : ℤ) = 2 * (k : ℤ) := by exact_mod_cast hk
    omega
  · have h' : (d : ℤ) % 6 = -1 % 6 := h
    norm_num at h'
    rintro ⟨k, hk⟩
    have hk' : (d : ℤ) = 2 * (k : ℤ) := by exact_mod_cast hk
    omega

/-- The `hfail` contradiction under `gcd = 1`: Renault's full case split. -/
theorem lrc6_case_gcd {D : Finset ℕ} (hpos : ∀ d ∈ D, 0 < d) (hcard : D.card = 5)
    (hgcd : D.gcd id = 1) (hf : hfail D) : False := by
  classical
  set S := D.filter fun d => 3 ∣ d with hS
  have hSle : S.card ≤ 3 :=
    mult3_le_three hpos (le_of_eq hcard) hgcd hf
  obtain ⟨w, hwD, hw3⟩ := hfail_exists_dvd hf (l := 3) (by norm_num) (by norm_num)
  have hSge : 1 ≤ S.card :=
    Finset.card_pos.mpr ⟨w, Finset.mem_filter.mpr ⟨hwD, hw3⟩⟩
  interval_cases hScard : S.card
  · -- exactly one multiple of 3: it is the multiple of 6; parity split.
    obtain ⟨v₁, hv₁S⟩ := Finset.card_eq_one.mp hScard
    -- `v₁` is the unique multiple of 3; the `l = 6` witness lies in `S`.
    obtain ⟨w6, hw6D, hw6⟩ := hfail_exists_dvd hf (l := 6) (by norm_num) (by norm_num)
    have hw6S : w6 ∈ S :=
      Finset.mem_filter.mpr ⟨hw6D, dvd_trans (by norm_num : (3:ℕ) ∣ 6) hw6⟩
    have hw6eq : w6 = v₁ := by rw [hv₁S] at hw6S; simpa using hw6S
    have hv₁6 : 6 ∣ v₁ := hw6eq ▸ hw6
    have hv₁D : v₁ ∈ D := hw6eq ▸ hw6D
    have hv₁pos : 0 < v₁ := hpos v₁ hv₁D
    -- guards = D \ {v₁}: four runners with residues `±1`/`±2`.
    set G := D.erase v₁ with hG
    have hGcard : G.card = 4 := by
      rw [Finset.card_erase_of_mem hv₁D, hcard]
    have hGres : ∀ d ∈ G, (d : ℤ) ≡ 1 [ZMOD 6] ∨ (d : ℤ) ≡ -1 [ZMOD 6] ∨
        (d : ℤ) ≡ 2 [ZMOD 6] ∨ (d : ℤ) ≡ -2 [ZMOD 6] := by
      intro d hd
      have hdv : d ≠ v₁ := (Finset.mem_erase.mp hd).1
      have hdD : d ∈ D := (Finset.mem_erase.mp hd).2
      have hd3 : ¬ 3 ∣ d := by
        intro h3
        have : d ∈ S := Finset.mem_filter.mpr ⟨hdD, h3⟩
        rw [hv₁S] at this
        exact hdv (Finset.mem_singleton.mp this)
      -- `d mod 6 ∈ {1,2,4,5}` since `3 ∤ d`.
      have hmod : d % 6 = 1 ∨ d % 6 = 2 ∨ d % 6 = 4 ∨ d % 6 = 5 := by
        have hlt : d % 6 < 6 := Nat.mod_lt _ (by norm_num)
        interval_cases hm : d % 6
        · exfalso; exact hd3 (by omega)
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
        · exfalso; exact hd3 (by omega)
        · exact Or.inr (Or.inr (Or.inl rfl))
        · exact Or.inr (Or.inr (Or.inr rfl))
      rcases hmod with hm | hm | hm | hm
      · refine Or.inl (Int.modEq_iff_dvd.mpr ?_)
        have hm' : (d : ℤ) % 6 = 1 := by exact_mod_cast hm
        omega
      · refine Or.inr (Or.inr (Or.inl (Int.modEq_iff_dvd.mpr ?_)))
        have hm' : (d : ℤ) % 6 = 2 := by exact_mod_cast hm
        omega
      · refine Or.inr (Or.inr (Or.inr (Int.modEq_iff_dvd.mpr ?_)))
        have hm' : (d : ℤ) % 6 = 4 := by exact_mod_cast hm
        omega
      · refine Or.inr (Or.inl (Int.modEq_iff_dvd.mpr ?_))
        have hm' : (d : ℤ) % 6 = 5 := by exact_mod_cast hm
        omega
    -- the `±2`-guards are exactly the even ones; `even_le_three` caps at 2.
    set E := G.filter fun d => 2 ∣ d with hE
    have hEcard : E.card ≤ 2 := by
      have hsub : D.filter (fun d => 2 ∣ d) = insert v₁ E := by
        rw [hE, hG]
        ext d
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_erase]
        constructor
        · intro ⟨hdD, h2⟩
          by_cases hdv : d = v₁
          · exact Or.inl hdv
          · exact Or.inr ⟨⟨hdv, hdD⟩, h2⟩
        · intro h
          rcases h with rfl | ⟨⟨hdv, hdD⟩, h2⟩
          · exact ⟨hv₁D, dvd_trans (by norm_num : (2 : ℕ) ∣ 6) hv₁6⟩
          · exact ⟨hdD, h2⟩
      have hv₁E : v₁ ∉ E := by
        intro h
        have hvG : v₁ ∈ G := (Finset.mem_filter.mp h).1
        rw [hG] at hvG
        exact (Finset.mem_erase.mp hvG).1 rfl
      have := even_le_three hpos (le_of_eq hcard) hgcd hf
      rw [hsub, Finset.card_insert_of_notMem hv₁E] at this
      omega
    -- seed: the four guards get `1/5`-safety from `lrc5_int`; the anchor `v₁`
    -- gets `off`-control from `hfail`.
    have hGpos : ∀ d ∈ G, 0 < d := fun d hd => hpos d (Finset.mem_erase.mp hd).2
    have hseed : ∃ τ : ℝ, ∀ d ∈ G, (1 / 5 : ℝ) ≤ circ (τ * d) := by
      obtain ⟨τ, _, hτ⟩ := lrc5_int G hGpos (le_of_eq hGcard)
      exact ⟨τ, hτ⟩
    have hns : ∀ t : ℝ, (∀ d ∈ G, Int.fract ((d : ℝ) * t) ∈
        Set.Icc (1 / 6) (5 / 6)) → |off v₁ t| < 1 / 6 := by
      intro t ht
      obtain ⟨d, hdD, hdu⟩ := hf t
      by_cases hdv : d = v₁
      · rw [hdv] at hdu
        rw [abs_off]
        exact lt_of_not_ge ((circ_ge_sixth_fract ((v₁ : ℝ) * t)).not.mpr hdu)
      · exact absurd (ht d (Finset.mem_erase.mpr ⟨hdv, hdD⟩)) hdu
    -- parity dispatch on the number of `±2`-guards
    interval_cases hE : E.card
    · -- zero even guards: all four are `±1` — Proposition 5.4.
      have hres : ∀ d ∈ G, (d : ℤ) ≡ 1 [ZMOD 6] ∨ (d : ℤ) ≡ -1 [ZMOD 6] := by
        intro d hd
        rcases hGres d hd with h | h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · have hdE : d ∈ E :=
            Finset.mem_filter.mpr ⟨hd, dvd_two_of_modeq (Or.inl rfl) h⟩
          rw [Finset.card_eq_zero.mp hE] at hdE
          exact absurd hdE (Finset.notMem_empty d)
        · have hdE : d ∈ E :=
            Finset.mem_filter.mpr ⟨hd, dvd_two_of_modeq (Or.inr rfl) h⟩
          rw [Finset.card_eq_zero.mp hE] at hdE
          exact absurd hdE (Finset.notMem_empty d)
      exact (prop5_4 hv₁6 hv₁pos hGcard hGpos hres hseed hns).elim
    · -- one even guard `u`: Proposition 6.6.
      obtain ⟨u, huE⟩ := Finset.card_eq_one.mp hE
      have huG : u ∈ G := by
        have : u ∈ E := by rw [huE]; exact Finset.mem_singleton_self u
        exact (Finset.mem_filter.mp this).1
      have hu2 : 2 ∣ u := by
        have : u ∈ E := by rw [huE]; exact Finset.mem_singleton_self u
        exact (Finset.mem_filter.mp this).2
      obtain ⟨eu, heu, huum⟩ : ∃ e : ℤ, (e = 2 ∨ e = -2) ∧ (u : ℤ) ≡ e [ZMOD 6] := by
        rcases hGres u huG with h | h | h | h
        · -- `u ≡ 1` contradicts `2 | u`
          exact absurd hu2 (not_dvd_two_of_modeq (Or.inl rfl) h)
        · exact absurd hu2 (not_dvd_two_of_modeq (Or.inr rfl) h)
        · exact ⟨2, Or.inl rfl, h⟩
        · exact ⟨-2, Or.inr rfl, h⟩
      have hres : ∀ d ∈ G, d ≠ u →
          ∃ e : ℤ, (e = 1 ∨ e = -1) ∧ (d : ℤ) ≡ e [ZMOD 6] := by
        intro d hd hdu
        rcases hGres d hd with h | h | h | h
        · exact ⟨1, Or.inl rfl, h⟩
        · exact ⟨-1, Or.inr rfl, h⟩
        · -- `d ≡ 2` ⇒ `2 | d` ⇒ `d ∈ E` ⇒ `d = u`
          exfalso
          have h2d : 2 ∣ d := dvd_two_of_modeq (Or.inl rfl) h
          have : d ∈ E := Finset.mem_filter.mpr ⟨hd, h2d⟩
          rw [huE] at this
          exact hdu (Finset.mem_singleton.mp this)
        · exfalso
          have h2d : 2 ∣ d := dvd_two_of_modeq (Or.inr rfl) h
          have : d ∈ E := Finset.mem_filter.mpr ⟨hd, h2d⟩
          rw [huE] at this
          exact hdu (Finset.mem_singleton.mp this)
      exact (prop6_6 hv₁6 hv₁pos hGcard hGpos huG ⟨eu, heu, huum⟩ hres hseed hns).elim
    · -- two even guards: Proposition 4.1 (the other two are `±1`).
      obtain ⟨v₂, v₃, hv23, hEeq⟩ := Finset.card_eq_two.mp hE
      have hv2E : v₂ ∈ E := by
        rw [hEeq]; exact Finset.mem_insert.mpr (Or.inl rfl)
      have hv3E : v₃ ∈ E := by
        rw [hEeq]
        exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self v₃))
      have hv2G : v₂ ∈ G := (Finset.mem_filter.mp hv2E).1
      have hv3G : v₃ ∈ G := (Finset.mem_filter.mp hv3E).1
      have hv2e : 2 ∣ v₂ := (Finset.mem_filter.mp hv2E).2
      have hv3e : 2 ∣ v₃ := (Finset.mem_filter.mp hv3E).2
      -- the two odd guards `v₄ v₅` are `G \ E`
      have hEG : E ⊆ G := Finset.filter_subset _ _
      have hOcard : (G \ E).card = 2 := by
        rw [Finset.card_sdiff_of_subset hEG, hGcard, hE]
      obtain ⟨v₄, v₅, hv45, hOeq⟩ := Finset.card_eq_two.mp hOcard
      have hv4mem : v₄ ∈ G \ E := by
        rw [hOeq]; exact Finset.mem_insert.mpr (Or.inl rfl)
      have hv5mem : v₅ ∈ G \ E := by
        rw [hOeq]
        exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self v₅))
      have hv4G : v₄ ∈ G := (Finset.mem_sdiff.mp hv4mem).1
      have hv5G : v₅ ∈ G := (Finset.mem_sdiff.mp hv5mem).1
      have hv4o : ¬ 2 ∣ v₄ := fun h2 =>
        (Finset.mem_sdiff.mp hv4mem).2 (Finset.mem_filter.mpr ⟨hv4G, h2⟩)
      have hv5o : ¬ 2 ∣ v₅ := fun h2 =>
        (Finset.mem_sdiff.mp hv5mem).2 (Finset.mem_filter.mpr ⟨hv5G, h2⟩)
      obtain ⟨e₂, he₂, hv₂m⟩ : ∃ e : ℤ, (e = 2 ∨ e = -2) ∧ (v₂ : ℤ) ≡ e [ZMOD 6] := by
        rcases hGres v₂ hv2G with h | h | h | h
        · exact absurd hv2e (not_dvd_two_of_modeq (Or.inl rfl) h)
        · exact absurd hv2e (not_dvd_two_of_modeq (Or.inr rfl) h)
        · exact ⟨2, Or.inl rfl, h⟩
        · exact ⟨-2, Or.inr rfl, h⟩
      obtain ⟨e₃, he₃, hv₃m⟩ : ∃ e : ℤ, (e = 2 ∨ e = -2) ∧ (v₃ : ℤ) ≡ e [ZMOD 6] := by
        rcases hGres v₃ hv3G with h | h | h | h
        · exact absurd hv3e (not_dvd_two_of_modeq (Or.inl rfl) h)
        · exact absurd hv3e (not_dvd_two_of_modeq (Or.inr rfl) h)
        · exact ⟨2, Or.inl rfl, h⟩
        · exact ⟨-2, Or.inr rfl, h⟩
      obtain ⟨e₄, he₄, hv₄m⟩ : ∃ e : ℤ, (e = 1 ∨ e = -1) ∧ (v₄ : ℤ) ≡ e [ZMOD 6] := by
        rcases hGres v₄ hv4G with h | h | h | h
        · exact ⟨1, Or.inl rfl, h⟩
        · exact ⟨-1, Or.inr rfl, h⟩
        · exact absurd (dvd_two_of_modeq (Or.inl rfl) h) hv4o
        · exact absurd (dvd_two_of_modeq (Or.inr rfl) h) hv4o
      obtain ⟨e₅, he₅, hv₅m⟩ : ∃ e : ℤ, (e = 1 ∨ e = -1) ∧ (v₅ : ℤ) ≡ e [ZMOD 6] := by
        rcases hGres v₅ hv5G with h | h | h | h
        · exact ⟨1, Or.inl rfl, h⟩
        · exact ⟨-1, Or.inr rfl, h⟩
        · exact absurd (dvd_two_of_modeq (Or.inl rfl) h) hv5o
        · exact absurd (dvd_two_of_modeq (Or.inr rfl) h) hv5o
      have hDeq : D = {v₁, v₂, v₃, v₄, v₅} := by
        rw [← Finset.insert_erase hv₁D]
        have hGeq : G = {v₂, v₃, v₄, v₅} := by
          rw [← Finset.union_sdiff_of_subset hEG, hOeq, hEeq]
          ext d
          simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
            or_assoc]
        rw [← hG, hGeq]
      exact prop4_1 (hpos v₁ hv₁D) (hpos v₂ (Finset.mem_erase.mp hv2G).2)
        (hpos v₃ (Finset.mem_erase.mp hv3G).2)
        (hpos v₄ (Finset.mem_erase.mp hv4G).2)
        (hpos v₅ (Finset.mem_erase.mp hv5G).2)
        (Int.modEq_zero_iff_dvd.mpr (by exact_mod_cast hv₁6 : (6 : ℤ) ∣ v₁))
        hv₂m hv₃m hv₄m hv₅m he₂ he₃ he₄ he₅ (hDeq ▸ hf)
  · -- two multiples of 3: Proposition 3.1.
    exact prop3_1 hpos hcard hScard hf
  · -- three multiples of 3: Lemma 2.3.
    exact lemma2_3 hpos (le_of_eq hcard) hf hScard

/-- The card-5 `hfail` contradiction with arbitrary gcd: scale `D` by its gcd
and apply `lrc6_case_gcd` to the image `D' = D.image (· / g)`. -/
theorem lrc6_case {D : Finset ℕ} (hpos : ∀ d ∈ D, 0 < d) (hcard : D.card = 5)
    (hf : hfail D) : False := by
  classical
  set g := D.gcd id with hg
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega : 0 < D.card)
  have hgpos : 0 < g := Nat.pos_of_dvd_of_pos (Finset.gcd_dvd (f := id) ha) (hpos a ha)
  set D' := D.image (fun d => d / g) with hD'
  have hgcd1 : D'.gcd id = 1 := by
    have hdiv : g * D'.gcd id ∣ g := by
      rw [hg]
      apply Finset.dvd_gcd
      intro d hd
      obtain ⟨k, hk⟩ := Finset.gcd_dvd (f := id) hd
      have hk' : d = g * k := hk
      have hd' : d / g ∈ D' := Finset.mem_image.mpr ⟨d, hd, rfl⟩
      obtain ⟨j, hj⟩ := Finset.gcd_dvd (f := id) hd'
      use j
      show d = (g * D'.gcd id) * j
      have e : d = g * (d / g) := (Nat.mul_div_cancel' ⟨k, hk'⟩).symm
      have hj' : d / g = D'.gcd id * j := hj
      rw [e, hj']
      ring
    have h1 : D'.gcd id ∣ 1 :=
      (Nat.mul_dvd_mul_iff_left hgpos).mp ((mul_one g).symm ▸ hdiv)
    exact Nat.dvd_one.mp h1
  have hD'card : D'.card = 5 := by
    have hinj : Set.InjOn (fun d => d / g) ↑D := by
      intro a ha b hb hab
      have ha' : g ∣ a := Finset.gcd_dvd (f := id) (Finset.mem_coe.mp ha)
      have hb' : g ∣ b := Finset.gcd_dvd (f := id) (Finset.mem_coe.mp hb)
      have hab' : a / g = b / g := hab
      have e : a = g * (a / g) := (Nat.mul_div_cancel' ha').symm
      rw [hab'] at e
      rw [Nat.mul_div_cancel' hb'] at e
      exact e
    rw [hD', Finset.card_image_of_injOn hinj, hcard]
  have hD'pos : ∀ d ∈ D', 0 < d := by
    intro d' hd'
    obtain ⟨d, hd, hdd'⟩ := Finset.mem_image.mp hd'
    rw [← hdd']
    exact Nat.div_pos (Nat.le_of_dvd (hpos d hd) (Finset.gcd_dvd (f := id) hd)) hgpos
  have hf' : hfail D' := by
    intro s
    obtain ⟨d, hd, hdu⟩ := hf (s / g)
    refine ⟨d / g, Finset.mem_image.mpr ⟨d, hd, rfl⟩, ?_⟩
    have hg0 : (g : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hgpos.ne'
    have e2 : ((d / g : ℕ) : ℝ) * s = (d : ℝ) * (s / g) := by
      have hdd : ((d / g : ℕ) : ℝ) = (d : ℝ) / g :=
        Nat.cast_div (Finset.gcd_dvd (f := id) hd) hg0
      rw [hdd]; field_simp
    rw [safe6, e2]
    exact hdu
  exact lrc6_case_gcd hD'pos hD'card hgcd1 hf'

/-- The integer Lonely Runner theorem for `n = 6`, `D.card ≤ 5`. -/
theorem lrc6_int (D : Finset ℕ) (hpos : ∀ d ∈ D, 0 < d) (hcard : D.card ≤ 5) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ D, (1 / 6 : ℝ) ≤ circ (t * d) := by
  classical
  rcases lt_or_eq_of_le hcard with hlt | h5
  · obtain ⟨t, ht, hτ⟩ := lrc5_int D hpos (by omega : D.card ≤ 4)
    exact ⟨t, ht, fun d hd => le_trans (by norm_num) (hτ d hd)⟩
  · by_contra hcon
    apply lrc6_case hpos h5
    intro t
    by_contra hc
    push Not at hc
    apply hcon
    set n := ⌈-t⌉ + 1 with hn
    have hn0 : (0 : ℝ) < t + (n : ℝ) := by
      have hcl := Int.le_ceil (-t)
      rw [hn]
      push_cast
      linarith
    refine ⟨t + (n : ℝ), hn0, fun d hd => ?_⟩
    have hs : safe6 d (t + (n : ℝ)) := by
      have e : (d : ℝ) * (t + (n : ℝ)) = (d : ℝ) * t + ((d : ℤ) * n : ℤ) := by
        push_cast; ring
      rw [safe6, e, Int.fract_add_intCast]
      exact hc d hd
    rw [safe6_iff] at hs
    rwa [mul_comm]

end
