/-
Copyright (c) 2026 Research07 contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Research07 contributors
-/
import Research07.LRC7.FiniteStage1
import Research07.LRC7.FiniteStage2

/-!
# §7 of Barajas–Serra: `|A| = 5`, `m = 1` — the finite enumeration

The last case of the seven-runner proof (EJC 15(1) 2008 #R48, §7): five
units `A` plus a top-level element `d6` with `ν₇ d6 = 1`.  The finite
machinery is split across three files:

* `FiniteBase` — definitions (`pairRep49`, `rep98`, `reps49`, `units21`,
  the explicit 63-set `badSets49`, `normBad49`, `lifts98`, `d6res`,
  `maskTable49`) plus the residue lemmas bridging `|λd|_N` to
  `|λ·rep|_N`.
* `FiniteStage1` (`ZMod 49`) — every 5-subset `Q` of the 24 pair-reps is
  either *good* (some `λ ∈ units21` with `|λa|_49 ≥ 7` on `Q`) or lies in
  `badSets49` (`stage1`).  The kernel certificate enumerates normalized
  tuples `{1,b,c,d,e}` in 23 slices; transport scales arbitrary `Q` to a
  normalized `Q'` via a unit inverse.
* `FiniteStage2` (`ZMod 98`) — for every bad `Q`, every `≤ 5`-subset `T`
  of `lifts98 Q` and every `r ∈ d6res` with an odd element in `T ∪ {r}`
  (the paper's `gcd(D) = 1` side condition — all-even configurations
  genuinely fail), some `λ ∈ {1,…,49}` pushes `T ∪ {r}` to distance
  `≥ 14 = 98/7` (`stage2`).  Certified by literal uncovered-lift tables
  `uTabQ<k>` plus `decide`-checked spec bridges.
* **Assembly (`lrc7_m1`, below).**  Halve `A ∪ {d6}` by `2^v` (`v` =
  minimum `ν₂`) making the minimizer odd; let `P₀` be the pair-class set
  of the halved `A`, extend to a 5-subset `Q`.  If `Q` is good take
  `M = 49` (`absModN_top_ge7` covers `d6`); if bad apply `stage2` to
  `T = rep98 '' (halved A) ⊆ lifts98 Q` and take `M = 98`.  In both cases
  `absModN_mul_scale` lifts `(λ, M)` to `(λ, 2^v · M)`.
-/

/-! ### Assembly -/

/-- The `m = 1` case of Barajas–Serra (paper §7): five units plus one
top-level element admit a multiplier with all distances `≥ M/7`. -/
theorem lrc7_m1 (A : Finset ℕ) (hA : A.card = 5)
    (hpos : ∀ d ∈ A, 0 < d) (hunit : ∀ d ∈ A, ¬ 7 ∣ d)
    (d6 : ℕ) (hd6 : padicValNat 7 d6 = 1) (hd6pos : 0 < d6) :
    ∃ lam M : ℕ, 0 < lam ∧ 0 < M ∧ 7 ∣ M ∧
      ∀ d ∈ A ∪ {d6}, M / 7 ≤ absModN (lam * d) M := by
  classical
  -- `v` = minimum `2`-adic valuation over `A ∪ {d6}`; all elements are
  -- divisible by `2^v`, and the minimizer's quotient is odd.
  have hSne : (A ∪ {d6}).Nonempty :=
    ⟨d6, Finset.mem_union_right _ (Finset.mem_singleton_self _)⟩
  obtain ⟨d0, hd0S, hd0min⟩ :=
    Finset.exists_min_image (A ∪ {d6}) (padicValNat 2) hSne
  have hd0pos : 0 < d0 := by
    rcases Finset.mem_union.mp hd0S with h | h
    · exact hpos d0 h
    · rw [Finset.mem_singleton] at h
      exact h ▸ hd6pos
  have hdvd : ∀ d ∈ A ∪ {d6}, 2 ^ padicValNat 2 d0 ∣ d := fun d hd =>
    (Nat.pow_dvd_iff_le_padicValNat (by norm_num)
      (Nat.ne_of_gt (by
        rcases Finset.mem_union.mp hd with h1 | h1
        · exact hpos d h1
        · rw [Finset.mem_singleton] at h1; exact h1 ▸ hd6pos))).mpr (hd0min d hd)
  have hd0odd : ¬ 2 ∣ d0 / 2 ^ padicValNat 2 d0 := by
    intro h2
    have hd0eq : d0 = 2 ^ padicValNat 2 d0 * (d0 / 2 ^ padicValNat 2 d0) :=
      (Nat.mul_div_cancel' (hdvd d0 hd0S)).symm
    have hdvd2 : 2 ^ (padicValNat 2 d0 + 1) ∣ d0 := by
      rw [pow_succ]
      conv_rhs => rw [hd0eq]
      exact Nat.mul_dvd_mul_left _ h2
    have hvle : padicValNat 2 d0 + 1 ≤ padicValNat 2 d0 :=
      (Nat.pow_dvd_iff_le_padicValNat (by norm_num)
        (Nat.ne_of_gt hd0pos)).mp hdvd2
    omega
  -- The halved configuration.
  have hBcard : (A.image (fun d => d / 2 ^ padicValNat 2 d0)).card = 5 := by
    rw [Finset.card_image_of_injOn]
    · exact hA
    · intro a ha b hb hab
      have ha2 := hdvd a (Finset.mem_union_left _ ha)
      have hb2 := hdvd b (Finset.mem_union_left _ hb)
      have hab' : a / 2 ^ padicValNat 2 d0 = b / 2 ^ padicValNat 2 d0 := hab
      rw [← Nat.mul_div_cancel' ha2, ← Nat.mul_div_cancel' hb2, hab']
  have hBpos : ∀ e ∈ A.image (fun d => d / 2 ^ padicValNat 2 d0), 0 < e := by
    intro e he
    obtain ⟨a, haA, rfl⟩ := Finset.mem_image.mp he
    exact Nat.div_pos
      (Nat.le_of_dvd (hpos a haA) (hdvd a (Finset.mem_union_left _ haA)))
      (Nat.pow_pos (by norm_num))
  have hBunit : ∀ e ∈ A.image (fun d => d / 2 ^ padicValNat 2 d0), ¬ 7 ∣ e := by
    intro e he h7e
    obtain ⟨a, haA, rfl⟩ := Finset.mem_image.mp he
    have ha2 := hdvd a (Finset.mem_union_left _ haA)
    apply hunit a haA
    rw [← Nat.mul_div_cancel' ha2]
    exact dvd_mul_of_dvd_right h7e _
  have hd6dvd : 2 ^ padicValNat 2 d0 ∣ d6 :=
    hdvd d6 (Finset.mem_union_right _ (Finset.mem_singleton_self _))
  have he6pos : 0 < d6 / 2 ^ padicValNat 2 d0 :=
    Nat.div_pos (Nat.le_of_dvd hd6pos hd6dvd) (Nat.pow_pos (by norm_num))
  have he6val : padicValNat 7 (d6 / 2 ^ padicValNat 2 d0) = 1 := by
    have hd6eq : d6 = 2 ^ padicValNat 2 d0 * (d6 / 2 ^ padicValNat 2 d0) :=
      (Nat.mul_div_cancel' hd6dvd).symm
    have hv7 : ¬ 7 ∣ 2 ^ padicValNat 2 d0 := fun h =>
      absurd ((Nat.Prime.dvd_of_dvd_pow Nat.prime_seven) h) (by norm_num)
    have h := padicValNat_mul_seven hv7 (Nat.ne_of_gt he6pos)
    rw [← hd6eq, hd6] at h
    exact h.symm
  -- An odd element after halving (the minimizer's quotient).
  obtain ⟨e0, he0mem, he0eq⟩ :
      ∃ e0 ∈ A.image (fun d => d / 2 ^ padicValNat 2 d0) ∪
        {d6 / 2 ^ padicValNat 2 d0}, e0 = d0 / 2 ^ padicValNat 2 d0 := by
    rcases Finset.mem_union.mp hd0S with hd0A | hd06
    · exact ⟨d0 / 2 ^ padicValNat 2 d0,
        Finset.mem_union_left _ (Finset.mem_image.mpr ⟨d0, hd0A, rfl⟩), rfl⟩
    · rw [Finset.mem_singleton] at hd06
      exact ⟨d0 / 2 ^ padicValNat 2 d0,
        Finset.mem_union_right _ (by
          rw [hd06]
          exact Finset.mem_singleton_self _), rfl⟩
  have he0odd : e0 % 2 = 1 := by
    rw [he0eq]
    omega
  -- The halved pair-class set and its 5-element superset `Q`.
  have hP0sub : (A.image (fun d => d / 2 ^ padicValNat 2 d0)).image pairRep49
      ⊆ reps49 := by
    intro x hx
    obtain ⟨e, heB, rfl⟩ := Finset.mem_image.mp hx
    exact pairRep49_mem_reps (hBunit e heB)
  have hP0card : ((A.image (fun d => d / 2 ^ padicValNat 2 d0)).image
      pairRep49).card ≤ 5 := by
    calc ((A.image (fun d => d / 2 ^ padicValNat 2 d0)).image pairRep49).card
        ≤ (A.image (fun d => d / 2 ^ padicValNat 2 d0)).card :=
          Finset.card_image_le
      _ = 5 := hBcard
  have hreps : reps49.card = 24 := by decide
  obtain ⟨Q, hPQ, hQr, hQcard⟩ :=
    Finset.exists_subsuperset_card_eq hP0sub hP0card (by omega)
  have hQmem : Q ∈ reps49.powersetCard 5 :=
    Finset.mem_powersetCard.mpr ⟨hQr, hQcard⟩
  -- The dichotomy, then the `2^v` lift.
  rcases stage1 hQmem with hgood | hQbad
  · -- Stage 1 good: `M = 49`, `d6` via `absModN_top_ge7`.
    obtain ⟨lam, hlamU, hlam⟩ := hgood
    have hlam1 : 1 ≤ lam :=
      (Finset.mem_Icc.mp (Finset.mem_filter.mp hlamU).1).1
    have hlam7 : ¬ 7 ∣ lam := fun hd =>
      (Finset.mem_filter.mp hlamU).2 (Nat.dvd_iff_mod_eq_zero.mp hd)
    refine ⟨lam, 2 ^ padicValNat 2 d0 * 49, hlam1,
      Nat.mul_pos (Nat.pow_pos (by norm_num)) (by norm_num),
      dvd_mul_of_dvd_right (by norm_num : 7 ∣ 49) _, ?_⟩
    intro d hdS
    set e := d / 2 ^ padicValNat 2 d0 with he
    have hd_eq : d = 2 ^ padicValNat 2 d0 * e :=
      (Nat.mul_div_cancel' (hdvd d hdS)).symm
    have he_mem : e ∈ A.image (fun d => d / 2 ^ padicValNat 2 d0) ∪
        {d6 / 2 ^ padicValNat 2 d0} := by
      rcases Finset.mem_union.mp hdS with hdA | hd6e
      · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨d, hdA, rfl⟩)
      · rw [Finset.mem_singleton] at hd6e
        apply Finset.mem_union_right
        rw [Finset.mem_singleton, he, hd6e]
    have h1 : 7 ≤ absModN (lam * e) 49 := by
      rcases Finset.mem_union.mp he_mem with heB | he6e
      · have hmem : pairRep49 e ∈ Q :=
          hPQ (Finset.mem_image.mpr ⟨e, heB, rfl⟩)
        rw [absModN_pairRep49]
        exact hlam _ hmem
      · rw [Finset.mem_singleton] at he6e
        rw [he6e]
        have h2 := absModN_top_ge7 (m := 1) he6val he6pos hlam7
        simpa using h2
    rw [hd_eq, show lam * (2 ^ padicValNat 2 d0 * e)
        = 2 ^ padicValNat 2 d0 * (lam * e) by ring]
    rw [absModN_mul_scale _ _ _ (Nat.pow_pos (by norm_num)) (by norm_num)]
    have hdiv : (2 ^ padicValNat 2 d0 * 49) / 7 = 2 ^ padicValNat 2 d0 * 7 := by
      rw [show 2 ^ padicValNat 2 d0 * 49 = 7 * (2 ^ padicValNat 2 d0 * 7) by ring]
      exact Nat.mul_div_cancel_left _ (by norm_num)
    rw [hdiv]
    exact Nat.mul_le_mul_left _ h1
  · -- Stage 1 bad: `Q ∈ badSets49`; apply stage 2 with `M = 98`.
    have hTsub : (A.image (fun d => d / 2 ^ padicValNat 2 d0)).image rep98
        ⊆ lifts98 Q := by
      intro x hx
      obtain ⟨e, heB, rfl⟩ := Finset.mem_image.mp hx
      exact rep98_mem_lifts (hPQ (Finset.mem_image.mpr ⟨e, heB, rfl⟩))
    have hTcard : ((A.image (fun d => d / 2 ^ padicValNat 2 d0)).image
        rep98).card ≤ 5 := by
      calc ((A.image (fun d => d / 2 ^ padicValNat 2 d0)).image rep98).card
          ≤ (A.image (fun d => d / 2 ^ padicValNat 2 d0)).card :=
            Finset.card_image_le
        _ = 5 := hBcard
    have hTmem : (A.image (fun d => d / 2 ^ padicValNat 2 d0)).image rep98 ∈
        (lifts98 Q).powerset.filter (fun T => T.card ≤ 5) :=
      Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hTsub, hTcard⟩
    have hr6 : rep98 (d6 / 2 ^ padicValNat 2 d0) ∈ d6res :=
      rep98_d6_mem he6val he6pos
    have hoddT : ∃ x ∈ insert (rep98 (d6 / 2 ^ padicValNat 2 d0))
        ((A.image (fun d => d / 2 ^ padicValNat 2 d0)).image rep98),
        x % 2 = 1 := by
      rcases Finset.mem_union.mp he0mem with he0B | he06
      · exact ⟨rep98 e0,
          Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨e0, he0B, rfl⟩),
          (rep98_parity e0).trans he0odd⟩
      · rw [Finset.mem_singleton] at he06
        exact ⟨rep98 e0, by
          rw [he06]
          exact Finset.mem_insert_self _ _, (rep98_parity e0).trans he0odd⟩
    obtain ⟨lam, hlamI, hlamT, hlamr⟩ :=
      stage2 Q hQbad _ hTmem _ hr6 hoddT
    have hlam1 : 0 < lam := (Finset.mem_Icc.mp hlamI).1
    refine ⟨lam, 2 ^ padicValNat 2 d0 * 98, hlam1,
      Nat.mul_pos (Nat.pow_pos (by norm_num)) (by norm_num),
      dvd_mul_of_dvd_right (by norm_num : 7 ∣ 98) _, ?_⟩
    intro d hdS
    set e := d / 2 ^ padicValNat 2 d0 with he
    have hd_eq : d = 2 ^ padicValNat 2 d0 * e :=
      (Nat.mul_div_cancel' (hdvd d hdS)).symm
    have he_mem : e ∈ A.image (fun d => d / 2 ^ padicValNat 2 d0) ∪
        {d6 / 2 ^ padicValNat 2 d0} := by
      rcases Finset.mem_union.mp hdS with hdA | hd6e
      · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨d, hdA, rfl⟩)
      · rw [Finset.mem_singleton] at hd6e
        apply Finset.mem_union_right
        rw [Finset.mem_singleton, he, hd6e]
    have h1 : 14 ≤ absModN (lam * e) 98 := by
      rcases Finset.mem_union.mp he_mem with heB | he6e
      · have hmem : rep98 e ∈ (A.image (fun d => d / 2 ^ padicValNat 2 d0)).image
            rep98 := Finset.mem_image.mpr ⟨e, heB, rfl⟩
        rw [absModN_rep98]
        exact hlamT _ hmem
      · rw [Finset.mem_singleton] at he6e
        rw [he6e, absModN_rep98]
        exact hlamr
    rw [hd_eq, show lam * (2 ^ padicValNat 2 d0 * e)
        = 2 ^ padicValNat 2 d0 * (lam * e) by ring]
    rw [absModN_mul_scale _ _ _ (Nat.pow_pos (by norm_num)) (by norm_num)]
    have hdiv : (2 ^ padicValNat 2 d0 * 98) / 7 = 2 ^ padicValNat 2 d0 * 14 := by
      rw [show 2 ^ padicValNat 2 d0 * 98 = 7 * (2 ^ padicValNat 2 d0 * 14) by ring]
      exact Nat.mul_div_cancel_left _ (by norm_num)
    rw [hdiv]
    exact Nat.mul_le_mul_left _ h1
