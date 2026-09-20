/-
Copyright (c) 2026 Research07 contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Research07 contributors
-/
import Research07.LRC7.FiniteBase

set_option maxRecDepth 1000000

/-!
# §7 stage 1: the `ZMod 49` enumeration, normalized

A pair-set `Q ⊆ reps49` is *good* when some `λ ∈ units21` has
`|λa|_49 ≥ 7` on all of `Q`; otherwise `Q` is one of the 63 literal
`badSets49`.  The naive check of all `C(24,5) = 42504` sets is too large
for a single kernel `decide`, so the enumeration is normalized and
sliced:

* every `Q` (card 5) contains a unit element `u` (only three non-unit
  pair-reps exist); scaling by `ν ≡ ±u⁻¹` (`units21_inv`) maps `Q` to
  `Q' = rep(ν·Q)` — still a 5-subset of `reps49` — with `1 ∈ Q'`;
* hence only 4-tuples `2 ≤ a < b < c < d ≤ 24` need checking
  (`C(23,4) = 8855`, plus the `a`-slicing below): each is either
  covered (`goodN`, via the `maskTable49` bit table) or one of the 15
  normalized bad tuples (`badTuple`);
* a good `Q'` transports back along `λ ↦ rep(μ·ν)` using
  `absModN_mul_rep49`/`absModN_rep49_mul`; a bad `Q'` lands in
  `normBad49`, whose `units21`-orbit is exactly `badSets49`
  (`normBad49_orbit` — a literal 315-case check).

The 23 slices `stage1_sN` below keep each `decide` under ~1 GB of kernel
reduction garbage; the only public conclusion is `stage1` itself.
-/

/-- Bitmask cover predicate for the normalized tuple `{1,a,b,c,d}`:
some `maskTable49` entry covers all five elements.  `abbrev` so
`Decidable` synthesis sees through it. -/
abbrev goodN (a b c d : ℕ) : Prop :=
  ∃ p ∈ maskTable49, Nat.testBit p.2 1 ∧ Nat.testBit p.2 a ∧
    Nat.testBit p.2 b ∧ Nat.testBit p.2 c ∧ Nat.testBit p.2 d

/-- The 15 normalized bad tuples (sorted tails `Q ∖ {1}` of `normBad49`). -/
abbrev badTuple (a b c d : ℕ) : Prop := (a, b, c, d) ∈ normBadTails

/-- Slice `a = 2` of the normalized enumeration. -/
private theorem stage1_s2 : ∀ b ∈ Finset.Icc 2 24,
    ∀ c ∈ Finset.Icc 2 24, ∀ d ∈ Finset.Icc 2 24,
    2 < b → b < c → c < d → goodN 2 b c d ∨ badTuple 2 b c d := by
  decide +kernel

/-- Slice `a = 3` of the normalized enumeration. -/
private theorem stage1_s3 : ∀ b ∈ Finset.Icc 2 24,
    ∀ c ∈ Finset.Icc 2 24, ∀ d ∈ Finset.Icc 2 24,
    3 < b → b < c → c < d → goodN 3 b c d ∨ badTuple 3 b c d := by
  decide +kernel

/-- Slice `a = 4` of the normalized enumeration. -/
private theorem stage1_s4 : ∀ b ∈ Finset.Icc 2 24,
    ∀ c ∈ Finset.Icc 2 24, ∀ d ∈ Finset.Icc 2 24,
    4 < b → b < c → c < d → goodN 4 b c d ∨ badTuple 4 b c d := by
  decide +kernel

/-- Slice `a = 5` of the normalized enumeration. -/
private theorem stage1_s5 : ∀ b ∈ Finset.Icc 2 24,
    ∀ c ∈ Finset.Icc 2 24, ∀ d ∈ Finset.Icc 2 24,
    5 < b → b < c → c < d → goodN 5 b c d ∨ badTuple 5 b c d := by
  decide +kernel

/-- Slice `a = 6` of the normalized enumeration. -/
private theorem stage1_s6 : ∀ b ∈ Finset.Icc 2 24,
    ∀ c ∈ Finset.Icc 2 24, ∀ d ∈ Finset.Icc 2 24,
    6 < b → b < c → c < d → goodN 6 b c d ∨ badTuple 6 b c d := by
  decide +kernel

/-- Slice `a = 7` of the normalized enumeration. -/
private theorem stage1_s7 : ∀ b ∈ Finset.Icc 2 24,
    ∀ c ∈ Finset.Icc 2 24, ∀ d ∈ Finset.Icc 2 24,
    7 < b → b < c → c < d → goodN 7 b c d ∨ badTuple 7 b c d := by
  decide +kernel

/-- Slice `a = 8` of the normalized enumeration. -/
private theorem stage1_s8 : ∀ b ∈ Finset.Icc 2 24,
    ∀ c ∈ Finset.Icc 2 24, ∀ d ∈ Finset.Icc 2 24,
    8 < b → b < c → c < d → goodN 8 b c d ∨ badTuple 8 b c d := by
  decide +kernel

/-- Slice `a = 9` of the normalized enumeration. -/
private theorem stage1_s9 : ∀ b ∈ Finset.Icc 2 24,
    ∀ c ∈ Finset.Icc 2 24, ∀ d ∈ Finset.Icc 2 24,
    9 < b → b < c → c < d → goodN 9 b c d ∨ badTuple 9 b c d := by
  decide +kernel

/-- Slice `a = 10` of the normalized enumeration. -/
private theorem stage1_s10 : ∀ b ∈ Finset.Icc 2 24,
    ∀ c ∈ Finset.Icc 2 24, ∀ d ∈ Finset.Icc 2 24,
    10 < b → b < c → c < d → goodN 10 b c d ∨ badTuple 10 b c d := by
  decide +kernel

/-- Slice `a = 11` of the normalized enumeration. -/
private theorem stage1_s11 : ∀ b ∈ Finset.Icc 2 24,
    ∀ c ∈ Finset.Icc 2 24, ∀ d ∈ Finset.Icc 2 24,
    11 < b → b < c → c < d → goodN 11 b c d ∨ badTuple 11 b c d := by
  decide +kernel

/-- Slice `a = 12` of the normalized enumeration. -/
private theorem stage1_s12 : ∀ b ∈ Finset.Icc 2 24,
    ∀ c ∈ Finset.Icc 2 24, ∀ d ∈ Finset.Icc 2 24,
    12 < b → b < c → c < d → goodN 12 b c d ∨ badTuple 12 b c d := by
  decide +kernel

/-- Slice `a = 13` of the normalized enumeration. -/
private theorem stage1_s13 : ∀ b ∈ Finset.Icc 2 24,
    ∀ c ∈ Finset.Icc 2 24, ∀ d ∈ Finset.Icc 2 24,
    13 < b → b < c → c < d → goodN 13 b c d ∨ badTuple 13 b c d := by
  decide +kernel

/-- Slice `a = 14` of the normalized enumeration. -/
private theorem stage1_s14 : ∀ b ∈ Finset.Icc 2 24,
    ∀ c ∈ Finset.Icc 2 24, ∀ d ∈ Finset.Icc 2 24,
    14 < b → b < c → c < d → goodN 14 b c d ∨ badTuple 14 b c d := by
  decide +kernel

/-- Slice `a = 15` of the normalized enumeration. -/
private theorem stage1_s15 : ∀ b ∈ Finset.Icc 2 24,
    ∀ c ∈ Finset.Icc 2 24, ∀ d ∈ Finset.Icc 2 24,
    15 < b → b < c → c < d → goodN 15 b c d ∨ badTuple 15 b c d := by
  decide +kernel

/-- Slice `a = 16` of the normalized enumeration. -/
private theorem stage1_s16 : ∀ b ∈ Finset.Icc 2 24,
    ∀ c ∈ Finset.Icc 2 24, ∀ d ∈ Finset.Icc 2 24,
    16 < b → b < c → c < d → goodN 16 b c d ∨ badTuple 16 b c d := by
  decide +kernel

/-- Slice `a = 17` of the normalized enumeration. -/
private theorem stage1_s17 : ∀ b ∈ Finset.Icc 2 24,
    ∀ c ∈ Finset.Icc 2 24, ∀ d ∈ Finset.Icc 2 24,
    17 < b → b < c → c < d → goodN 17 b c d ∨ badTuple 17 b c d := by
  decide +kernel

/-- Slice `a = 18` of the normalized enumeration. -/
private theorem stage1_s18 : ∀ b ∈ Finset.Icc 2 24,
    ∀ c ∈ Finset.Icc 2 24, ∀ d ∈ Finset.Icc 2 24,
    18 < b → b < c → c < d → goodN 18 b c d ∨ badTuple 18 b c d := by
  decide +kernel

/-- Slice `a = 19` of the normalized enumeration. -/
private theorem stage1_s19 : ∀ b ∈ Finset.Icc 2 24,
    ∀ c ∈ Finset.Icc 2 24, ∀ d ∈ Finset.Icc 2 24,
    19 < b → b < c → c < d → goodN 19 b c d ∨ badTuple 19 b c d := by
  decide +kernel

/-- Slice `a = 20` of the normalized enumeration. -/
private theorem stage1_s20 : ∀ b ∈ Finset.Icc 2 24,
    ∀ c ∈ Finset.Icc 2 24, ∀ d ∈ Finset.Icc 2 24,
    20 < b → b < c → c < d → goodN 20 b c d ∨ badTuple 20 b c d := by
  decide +kernel

/-- Slice `a = 21` of the normalized enumeration. -/
private theorem stage1_s21 : ∀ b ∈ Finset.Icc 2 24,
    ∀ c ∈ Finset.Icc 2 24, ∀ d ∈ Finset.Icc 2 24,
    21 < b → b < c → c < d → goodN 21 b c d ∨ badTuple 21 b c d := by
  decide +kernel

/-- Slice `a = 22` of the normalized enumeration. -/
private theorem stage1_s22 : ∀ b ∈ Finset.Icc 2 24,
    ∀ c ∈ Finset.Icc 2 24, ∀ d ∈ Finset.Icc 2 24,
    22 < b → b < c → c < d → goodN 22 b c d ∨ badTuple 22 b c d := by
  decide +kernel

/-- Slice `a = 23` of the normalized enumeration. -/
private theorem stage1_s23 : ∀ b ∈ Finset.Icc 2 24,
    ∀ c ∈ Finset.Icc 2 24, ∀ d ∈ Finset.Icc 2 24,
    23 < b → b < c → c < d → goodN 23 b c d ∨ badTuple 23 b c d := by
  decide +kernel

/-- Slice `a = 24` of the normalized enumeration. -/
private theorem stage1_s24 : ∀ b ∈ Finset.Icc 2 24,
    ∀ c ∈ Finset.Icc 2 24, ∀ d ∈ Finset.Icc 2 24,
    24 < b → b < c → c < d → goodN 24 b c d ∨ badTuple 24 b c d := by
  decide +kernel

/-- Normalized enumeration: every sorted `{1,a,b,c,d}` with
`2 ≤ a < b < c < d ≤ 24` is covered or normalized-bad. -/
theorem stage1_norm : ∀ a ∈ Finset.Icc 2 24, ∀ b ∈ Finset.Icc 2 24,
    ∀ c ∈ Finset.Icc 2 24, ∀ d ∈ Finset.Icc 2 24,
    a < b → b < c → c < d → goodN a b c d ∨ badTuple a b c d := by
  intro a ha b hb c hc d hd h1 h2 h3
  obtain ⟨ha2, ha24⟩ := Finset.mem_Icc.mp ha
  interval_cases a
  · exact stage1_s2 b hb c hc d hd h1 h2 h3
  · exact stage1_s3 b hb c hc d hd h1 h2 h3
  · exact stage1_s4 b hb c hc d hd h1 h2 h3
  · exact stage1_s5 b hb c hc d hd h1 h2 h3
  · exact stage1_s6 b hb c hc d hd h1 h2 h3
  · exact stage1_s7 b hb c hc d hd h1 h2 h3
  · exact stage1_s8 b hb c hc d hd h1 h2 h3
  · exact stage1_s9 b hb c hc d hd h1 h2 h3
  · exact stage1_s10 b hb c hc d hd h1 h2 h3
  · exact stage1_s11 b hb c hc d hd h1 h2 h3
  · exact stage1_s12 b hb c hc d hd h1 h2 h3
  · exact stage1_s13 b hb c hc d hd h1 h2 h3
  · exact stage1_s14 b hb c hc d hd h1 h2 h3
  · exact stage1_s15 b hb c hc d hd h1 h2 h3
  · exact stage1_s16 b hb c hc d hd h1 h2 h3
  · exact stage1_s17 b hb c hc d hd h1 h2 h3
  · exact stage1_s18 b hb c hc d hd h1 h2 h3
  · exact stage1_s19 b hb c hc d hd h1 h2 h3
  · exact stage1_s20 b hb c hc d hd h1 h2 h3
  · exact stage1_s21 b hb c hc d hd h1 h2 h3
  · exact stage1_s22 b hb c hc d hd h1 h2 h3
  · exact stage1_s23 b hb c hc d hd h1 h2 h3
  · exact stage1_s24 b hb c hc d hd h1 h2 h3

/-- Every `maskTable49` entry is a `units21` multiplier. -/
theorem maskTable49_fst : ∀ p ∈ maskTable49, p.1 ∈ units21 := by decide

/-- Bit semantics of `maskTable49`: bit `a` is set iff `7 ≤ |p.1·a|_49`. -/
theorem maskTable49_spec : ∀ p ∈ maskTable49, ∀ a < 50,
    Nat.testBit p.2 a ↔ 7 ≤ absModN (p.1 * a) 49 := by decide

/-- The tail tuples correspond to the `normBad49` members. -/
theorem normBadTails_spec : ∀ t ∈ normBadTails,
    insert 1 {t.1, t.2.1, t.2.2.1, t.2.2.2} ∈ normBad49 := by decide

/-- Orbit closure: scaling a normalized bad set by a unit rep stays inside
`badSets49` — the three `U_49/{±1}` orbits are exactly the 63 bad sets. -/
theorem normBad49_orbit : ∀ Q' ∈ normBad49, ∀ u ∈ units21,
    (Q'.image fun t => pairRep49 (u * t)) ∈ badSets49 := by decide +kernel

/-! ### Transport: from normalized tuples back to arbitrary pair-sets -/

/-- A unit residue is coprime to 49. -/
theorem coprime49_of_mod7 {μ : ℕ} (hμ : μ % 7 ≠ 0) : Nat.Coprime μ 49 := by
  have h7 : Nat.Coprime μ 7 :=
    ((Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 7)).mpr
      (fun h => hμ (Nat.dvd_iff_mod_eq_zero.mp h))).symm
  rwa [show (49 : ℕ) = 7 ^ 2 by norm_num,
    Nat.coprime_pow_right_iff (show 0 < 2 by norm_num)]

/-- `rep(ν·u) = 1` means `u ≡ ±ν⁻¹`: scaling back recovers the rep. -/
theorem pairRep49_inv_mul {ν u a : ℕ} (h : pairRep49 (ν * u) = 1) :
    pairRep49 (u * (ν * a)) = pairRep49 a := by
  have hx : (ν * u) % 49 = 1 ∨ (ν * u) % 49 = 48 := by
    unfold pairRep49 at h
    have hxl : (ν * u) % 49 < 49 := Nat.mod_lt _ (by norm_num)
    rcases le_or_gt ((ν * u) % 49) (49 - (ν * u) % 49) with hc | hc
    · rw [min_eq_left hc] at h; exact Or.inl h
    · rw [min_eq_right hc.le] at h; right; omega
  have hmod : u * (ν * a) % 49 = ((ν * u) % 49 * a) % 49 := by
    have h2 : u * (ν * a) = (ν * u) * a := by ring
    rw [h2]
    exact ((Nat.mod_modEq (ν * u) 49).mul_right a).symm
  rcases hx with h1 | h1
  · apply pairRep49_congr
    rw [hmod, h1, Nat.one_mul]
  · rcases eq_or_ne (a % 49) 0 with h0 | h0
    · have hx0 : (u * (ν * a)) % 49 = 0 := by
        have h49 : 49 ∣ u * (ν * a) :=
          Nat.mul_assoc u ν a ▸ Dvd.dvd.mul_left (Nat.dvd_of_mod_eq_zero h0) (u * ν)
        exact Nat.mod_eq_zero_of_dvd h49
      unfold pairRep49
      rw [hx0, h0]
    · apply pairRep49_neg
      rw [hmod, h1]
      have hz : ((48 * a : ℕ) : ZMod 49) = -((a : ℕ) : ZMod 49) := by
        push_cast
        have h48 : (48 : ZMod 49) = -1 := by decide
        rw [h48, neg_one_mul]
      exact mod_add_eq_49_of_zmod_neg hz h0

/-- The stage-1 dichotomy: every 5-subset of the 24 pair-classes is either
covered by a unit multiplier mod 49 or is one of the 63 bad sets. -/
theorem stage1 {Q : Finset ℕ} (hQ : Q ∈ reps49.powersetCard 5) :
    (∃ lam ∈ units21, ∀ a ∈ Q, 7 ≤ absModN (lam * a) 49) ∨
      Q ∈ badSets49 := by
  obtain ⟨u, huQ, hu7⟩ : ∃ u ∈ Q, u % 7 ≠ 0 := by
    obtain ⟨hQr0, hQc0⟩ := Finset.mem_powersetCard.mp hQ
    by_contra hcon
    push Not at hcon
    have hsub : Q ⊆ ({7, 14, 21} : Finset ℕ) := by
      intro x hx
      obtain ⟨hx1, hx24⟩ := Finset.mem_Icc.mp (hQr0 hx)
      have hx7 := hcon x hx
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    have hc3 : ({7, 14, 21} : Finset ℕ).card = 3 := by decide
    have hle := Finset.card_le_card hsub
    omega
  obtain ⟨hQr, hQc⟩ := Finset.mem_powersetCard.mp hQ
  have huU : u ∈ units21 := Finset.mem_filter.mpr ⟨hQr huQ, hu7⟩
  obtain ⟨ν, hνU, hνu⟩ := units21_inv u huU
  have hν7 : ν % 7 ≠ 0 := (Finset.mem_filter.mp hνU).2
  have hνb : ν ∈ reps49 := (Finset.mem_filter.mp hνU).1
  set Q' := Q.image (fun a => pairRep49 (ν * a)) with hQ'def
  have hQ'card : Q'.card = 5 := by
    rw [hQ'def, Finset.card_image_of_injOn
      ((pairRep49_mul_injOn hν7).mono (Finset.coe_subset.mpr hQr)), hQc]
  have hQ'sub : Q' ⊆ reps49 := by
    intro x hx
    obtain ⟨a, haQ, rfl⟩ := Finset.mem_image.mp (hQ'def ▸ hx)
    exact pairRep49_mul_mem_reps hν7 (hQr haQ)
  have h1mem : 1 ∈ Q' := by
    rw [hQ'def]
    exact Finset.mem_image.mpr ⟨u, huQ, hνu⟩
  have hR : (Q'.erase 1).card = 4 := by
    rw [Finset.card_erase_of_mem h1mem, hQ'card]
  have hlen : (Finset.sort (Q'.erase 1)).length = 4 := by
    rw [Finset.length_sort, hR]
  obtain ⟨b, c, d, e, hsort⟩ := List.length_eq_four.mp hlen
  have hmem : ∀ x ∈ ([b, c, d, e] : List ℕ), x ∈ Q'.erase 1 := by
    intro x hx
    rw [← Finset.mem_sort (r := fun a b => a ≤ b), hsort]
    exact hx
  have hbnd : ∀ x ∈ ([b, c, d, e] : List ℕ), x ∈ Finset.Icc 2 24 := by
    intro x hx
    obtain ⟨hx1, hxQ⟩ := Finset.mem_erase.mp (hmem x hx)
    have hxr := Finset.mem_Icc.mp (hQ'sub hxQ)
    exact Finset.mem_Icc.mpr ⟨by omega, hxr.2⟩
  have hbI := hbnd b (by simp)
  have hcI := hbnd c (by simp)
  have hdI := hbnd d (by simp)
  have heI := hbnd e (by simp)
  have hsorted : ([b, c, d, e] : List ℕ).SortedLT := by
    have := Finset.sortedLT_sort (Q'.erase 1)
    rwa [hsort] at this
  rw [List.sortedLT_iff_pairwise] at hsorted
  rw [List.pairwise_cons] at hsorted
  obtain ⟨hb_rest, hsorted⟩ := hsorted
  rw [List.pairwise_cons] at hsorted
  obtain ⟨hc_rest, hsorted⟩ := hsorted
  rw [List.pairwise_cons] at hsorted
  obtain ⟨hd_rest, _⟩ := hsorted
  have hbc : b < c := hb_rest c (by simp)
  have hcd : c < d := hc_rest d (by simp)
  have hde : d < e := hd_rest e (by simp)
  have hQ'eq : Q' = insert 1 {b, c, d, e} := by
    rw [← Finset.insert_erase h1mem]
    congr 1
    apply Finset.ext
    intro x
    rw [← Finset.mem_sort (r := fun a b => a ≤ b), hsort]
    simp only [Finset.mem_insert, Finset.mem_singleton, List.mem_cons,
      List.mem_singleton, List.not_mem_nil, or_false]
  rcases stage1_norm b hbI c hcI d hdI e heI hbc hcd hde with hg | hbt
  · -- good: transport `μ` back along `rep(μ·ν)`
    obtain ⟨p, hpm, t1, tb, tc, td, te⟩ := hg
    have hμU := maskTable49_fst p hpm
    have hμ7 : p.1 % 7 ≠ 0 := (Finset.mem_filter.mp hμU).2
    have hcov : ∀ t ∈ Q', 7 ≤ absModN (p.1 * t) 49 := by
      intro t ht
      have ht50 : t < 50 := by
        have := Finset.mem_Icc.mp (hQ'sub ht); omega
      apply (maskTable49_spec p hpm t ht50).mp
      rw [hQ'eq] at ht
      rcases Finset.mem_insert.mp ht with h | ht
      · subst t; exact t1
      · rcases Finset.mem_insert.mp ht with h | ht
        · subst t; exact tb
        · rcases Finset.mem_insert.mp ht with h | ht
          · subst t; exact tc
          · rcases Finset.mem_insert.mp ht with h | ht
            · subst t; exact td
            · rw [Finset.mem_singleton] at ht; subst t; exact te
    refine Or.inl ⟨pairRep49 (p.1 * ν), ?_, ?_⟩
    · apply pairRep49_mem_units21
      · intro hd7
        have hdvd : 7 ∣ p.1 * ν := Nat.dvd_iff_mod_eq_zero.mpr hd7
        rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 7)).mp hdvd with
          h | h
        · exact hμ7 (Nat.dvd_iff_mod_eq_zero.mp h)
        · exact hν7 (Nat.dvd_iff_mod_eq_zero.mp h)
      · intro hd49
        have hdvd : 49 ∣ ν :=
          (coprime49_of_mod7 hμ7).symm.dvd_of_dvd_mul_left
            (Nat.dvd_of_mod_eq_zero hd49)
        have hν49 : ν % 49 = ν := Nat.mod_eq_of_lt (by
          have := Finset.mem_Icc.mp hνb; omega)
        have h0 : ν = 0 := by
          have := Nat.mod_eq_zero_of_dvd hdvd
          omega
        have := Finset.mem_Icc.mp hνb
        omega
    · intro a haQ
      have hta : pairRep49 (ν * a) ∈ Q' := by
        rw [hQ'def]
        exact Finset.mem_image.mpr ⟨a, haQ, rfl⟩
      have hta' : pairRep49 (ν * a) ∈ reps49 := hQ'sub hta
      have hrep : pairRep49 (ν * a) < 50 := by
        have := Finset.mem_Icc.mp hta'; omega
      calc 7 ≤ absModN (p.1 * pairRep49 (ν * a)) 49 := hcov _ hta
        _ = absModN (p.1 * (ν * a)) 49 := absModN_mul_rep49 p.1 ν a
        _ = absModN ((p.1 * ν) * a) 49 := by
          apply absModN_congr_res
          rw [Nat.mul_assoc]
        _ = absModN (pairRep49 (p.1 * ν) * a) 49 :=
          (absModN_rep49_mul (p.1 * ν) a).symm
  · -- bad: `Q'` is a normBad literal; orbit back by `u`
    right
    have hQ'norm : Q' ∈ normBad49 := by
      rw [hQ'eq]
      exact normBadTails_spec (b, c, d, e) hbt
    have hQeq : Q = Q'.image (fun t => pairRep49 (u * t)) := by
      apply Finset.ext
      intro a
      constructor
      · intro haQ
        apply Finset.mem_image.mpr
        refine ⟨pairRep49 (ν * a), ?_, ?_⟩
        · rw [hQ'def]
          exact Finset.mem_image.mpr ⟨a, haQ, rfl⟩
        · rw [pairRep49_mul_rep, pairRep49_inv_mul hνu]
          exact pairRep49_self (hQr haQ)
      · intro hx
        obtain ⟨t, htQ', ht⟩ := Finset.mem_image.mp hx
        obtain ⟨a', ha'Q, rfl⟩ := Finset.mem_image.mp (hQ'def ▸ htQ')
        rw [pairRep49_mul_rep, pairRep49_inv_mul hνu,
          pairRep49_self (hQr ha'Q)] at ht
        rwa [← ht]
    rw [hQeq]
    exact normBad49_orbit Q' hQ'norm u huU
