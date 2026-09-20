/-
Copyright (c) 2026 Research07 contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Research07 contributors
-/
import Research07.LRC7.Discrete

/-!
# Prime Filtering at `p = 7` (Barajas–Serra Lemma 2)

Generalization of `Research07/LRC5/Filtering.lean`: instead of a uniform
`{0, p−1}` forbidden digit set, each element `d` carries its own forbidden
set `F d ⊆ ZMod 7`.  This is the form the `n = 7` proof actually uses —
the Corollary-3 `{0,6}`-avoidance case is the specialization `F d = {0,6}`.

Mechanism (paper §2): process levels `i₀−1, i₀−2, …, 0` downwards.  At
level `j`, the multiplier `1 + k·7^{m−j}` shifts the leading digit of every
level-`j` element by `k·runit(d)` — a bijection of `ZMod 7` — while
residues at levels `> j` are preserved verbatim.  A level is filtered when
`Σ_{d ∈ level j} |F_d| ≤ 6 < 7` so a single `k` is good for the whole level.

The top-level `Λ_m` scalar step of paper Lemma 2 is kept separate
(`exists_top_scalar`): callers needing level-`m` normalization compose it
with `filtered7` (scalars first, then descending filtering; `Λ_{j<m}`
multipliers preserve level-`m` residues verbatim).
-/

private instance : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩

/-- `qdig7` depends only on the residue of `x` modulo `7^{m+1}`. -/
theorem qdig7_congr {m a b : ℕ} (h : a % 7 ^ (m + 1) = b % 7 ^ (m + 1)) :
    qdig7 m a = qdig7 m b := by
  unfold qdig7
  rw [h]

/-- Multiplying by a non-multiple of `7` preserves the `7`-adic valuation. -/
theorem padicValNat_mul_seven {lam d : ℕ} (hlam : ¬ 7 ∣ lam) (hd : d ≠ 0) :
    padicValNat 7 (lam * d) = padicValNat 7 d := by
  have hlam0 : lam ≠ 0 := by rintro rfl; exact hlam (dvd_zero 7)
  rw [padicValNat.mul hlam0 hd, padicValNat.eq_zero_of_not_dvd hlam, zero_add]

/-- Filter cardinality under a bijection: the number of `k : ZMod 7` with
`f k ∈ T` equals `|T|` when `k ↦ f k` is a bijection. -/
private theorem card_filter_bij {T : Finset (ZMod 7)} {f : ZMod 7 → ZMod 7}
    (hf : Function.Bijective f) :
    (Finset.univ.filter fun k : ZMod 7 => f k ∈ T).card = T.card := by
  rw [Finset.card_filter]
  calc (∑ k : ZMod 7, if f k ∈ T then (1 : ℕ) else 0)
      = ∑ v : ZMod 7, if v ∈ T then (1 : ℕ) else 0 :=
        Function.Bijective.sum_comp hf (fun v : ZMod 7 => if v ∈ T then (1 : ℕ) else 0)
    _ = T.card := by
        rw [← Finset.card_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]

/-- Per-level choice: for each `d` at level `j`, `k ↦ qdig7 m d + k·runit7 d`
is a bijection of `ZMod 7`, so exactly `|F d|` of the seven shifts are bad.
When `Σ |F| ≤ 6 < 7` one `k` is good for the whole level simultaneously. -/
theorem exists_k_all_good7 {m j : ℕ} (hjm : j < m) (S : Finset ℕ)
    (hS : ∀ d ∈ S, padicValNat 7 d = j) (hSpos : ∀ d ∈ S, 0 < d)
    (F : ℕ → Finset (ZMod 7))
    (hcard : (S.sum fun d => (F d).card) ≤ 6) :
    ∃ k : ℕ, k < 7 ∧ ∀ d ∈ S,
      qdig7 m ((1 + k * 7 ^ (m - j)) * d) ∉ F d := by
  classical
  have hbij : ∀ d ∈ S,
      Function.Bijective (fun k : ZMod 7 => qdig7 m d + k * runit7 d) := by
    intro d hd
    have hb : runit7 d ≠ 0 := runit7_ne_zero (hSpos d hd)
    rw [← Finite.injective_iff_bijective]
    intro a b hab
    exact mul_right_cancel₀ hb (add_left_cancel hab)
  -- Consequently exactly `|F d|` of the seven shifts are bad for `d`.
  have hbadcard : ∀ d ∈ S,
      (Finset.univ.filter (fun k : ZMod 7 =>
        qdig7 m d + k * runit7 d ∈ F d)).card = (F d).card :=
    fun d hd => card_filter_bij (hbij d hd)
  -- The union over `d ∈ S` of the bad-shift sets has size `≤ Σ|F| ≤ 6 < 7`.
  have hU : (S.biUnion (fun d => Finset.univ.filter (fun k : ZMod 7 =>
      qdig7 m d + k * runit7 d ∈ F d))).card ≤ 6 := by
    refine le_trans Finset.card_biUnion_le ?_
    calc ∑ d ∈ S, (Finset.univ.filter (fun k : ZMod 7 =>
            qdig7 m d + k * runit7 d ∈ F d)).card
        = ∑ d ∈ S, (F d).card :=
          Finset.sum_congr rfl fun d hd => hbadcard d hd
      _ ≤ 6 := hcard
  -- So some `K : ZMod 7` is good for every `d ∈ S` simultaneously.
  have hnon : ((Finset.univ : Finset (ZMod 7)) \ S.biUnion (fun d =>
      Finset.univ.filter (fun k : ZMod 7 =>
        qdig7 m d + k * runit7 d ∈ F d))).Nonempty := by
    rw [← Finset.card_pos, Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    have hcu : (Finset.univ : Finset (ZMod 7)).card = 7 := by
      rw [Finset.card_univ, ZMod.card]
    omega
  obtain ⟨K, hK⟩ := hnon
  rw [Finset.mem_sdiff] at hK
  obtain ⟨hKu, hKB⟩ := hK
  have hgoodK : ∀ d ∈ S, qdig7 m d + K * runit7 d ∉ F d := by
    intro d hd
    have hKd : K ∉ Finset.univ.filter (fun k : ZMod 7 =>
        qdig7 m d + k * runit7 d ∈ F d) :=
      fun hmem => hKB (Finset.mem_biUnion.mpr ⟨d, hd, hmem⟩)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hKd
    exact hKd
  -- Take the natural lift `k = K.val < 7` of `K`.
  refine ⟨K.val, ZMod.val_lt K, fun d hd => ?_⟩
  have hq := qdig7_multLow (k := K.val) hjm (hS d hd)
  rw [hq, ZMod.natCast_zmod_val K]
  exact hgoodK d hd

/-- **Prime Filtering** (Lemma 2, levels `< i₀`): if every level below `i₀`
has forbidden-set budget `Σ|F| ≤ 6`, some unit `λ` (a product of
`Λ_j`-multipliers, hence `7 ∤ λ`) puts every sub-`i₀` element's leading
digit outside its forbidden set and preserves residues at levels `≥ i₀`
verbatim. -/
theorem filtered7 (D : Finset ℕ) (hpos : ∀ d ∈ D, 0 < d) {m i₀ : ℕ}
    (_hm : ∀ d ∈ D, padicValNat 7 d ≤ m) (hi₀ : i₀ ≤ m)
    (F : ℕ → Finset (ZMod 7))
    (hlow : ∀ j, j < i₀ → ((level7 D j).sum fun d => (F d).card) ≤ 6) :
    ∃ lam : ℕ, ¬ 7 ∣ lam ∧
      (∀ d ∈ D, i₀ ≤ padicValNat 7 d →
        (lam * d) % 7 ^ (m + 1) = d % 7 ^ (m + 1)) ∧
      ∀ d ∈ D, padicValNat 7 d < i₀ →
        qdig7 m (lam * d) ∉ F d := by
  classical
  -- Induction on `t`: after handling levels `i₀−1 … i₀−t`, the partial
  -- multiplier `Lam` is good on levels `≥ i₀ − t` and verbatim on `≥ i₀`.
  have key : ∀ t : ℕ, t ≤ i₀ → ∃ lam : ℕ, ¬ 7 ∣ lam ∧
      (∀ d ∈ D, i₀ ≤ padicValNat 7 d →
        (lam * d) % 7 ^ (m + 1) = d % 7 ^ (m + 1)) ∧
      ∀ d ∈ D, i₀ - t ≤ padicValNat 7 d → padicValNat 7 d < i₀ →
        qdig7 m (lam * d) ∉ F d := by
    intro t
    induction t with
    | zero =>
      intro _
      refine ⟨1, by decide, ?_, ?_⟩
      · intro d _ _; rw [one_mul]
      · intro d _ h1 h2; simp at h1; omega
    | succ t ih =>
      intro ht
      obtain ⟨Lam, hLam7, hver, hgd⟩ := ih (Nat.le_of_succ_le ht)
      have hLam0 : Lam ≠ 0 := by rintro rfl; exact hLam7 (dvd_zero 7)
      -- Process level `j = i₀ − (t+1)` via `exists_k_all_good7` applied to
      -- the shifted level set `(Lam * ·) '' level7 D j`.
      set j := i₀ - (t + 1) with hj
      have hji : j < i₀ := by omega
      have hjm : j < m := by omega
      have hSval : ∀ x ∈ (level7 D j).image (fun d => Lam * d),
          padicValNat 7 x = j := by
        intro x hx
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
        obtain ⟨haD, haν⟩ := Finset.mem_filter.mp ha
        rw [padicValNat_mul_seven hLam7 (ne_of_gt (hpos a haD)), haν]
      have hSpos : ∀ x ∈ (level7 D j).image (fun d => Lam * d), 0 < x := by
        intro x hx
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
        obtain ⟨haD, -⟩ := Finset.mem_filter.mp ha
        exact Nat.mul_pos (Nat.pos_of_ne_zero hLam0) (hpos a haD)
      -- The shifted element `Lam·d` keeps `d`'s forbidden set.
      set F' : ℕ → Finset (ZMod 7) := fun x => F (x / Lam) with hF'def
      have hF'd : ∀ d : ℕ, F' (Lam * d) = F d := by
        intro d
        simp only [hF'def]
        rw [Nat.mul_div_right d (Nat.pos_of_ne_zero hLam0)]
      have hScard : ((level7 D j).image (fun d => Lam * d)).sum
          (fun x => (F' x).card) ≤ 6 := by
        rw [Finset.sum_image]
        · simp only [hF'd]
          exact hlow j hji
        · intro a _ b _ hab
          exact Nat.mul_left_cancel (Nat.pos_of_ne_zero hLam0) hab
      obtain ⟨k, hk7, hkg⟩ := exists_k_all_good7 hjm
        ((level7 D j).image (fun d => Lam * d)) hSval hSpos F' hScard
      -- The level-`j` multiplier `μ = 1 + k·7^{m−j}` is a unit mod 7.
      have h7pow : (7 : ℕ) ∣ 7 ^ (m - j) := by
        obtain ⟨e, he⟩ : ∃ e, m - j = e + 1 := ⟨m - j - 1, by omega⟩
        rw [he, pow_succ']
        exact dvd_mul_right 7 _
      have h7k : 7 ∣ k * 7 ^ (m - j) := dvd_mul_of_dvd_right h7pow k
      have hμ7 : ¬ 7 ∣ 1 + k * 7 ^ (m - j) := by
        intro h
        have h1 : 7 ∣ (1 + k * 7 ^ (m - j)) - k * 7 ^ (m - j) := Nat.dvd_sub h h7k
        rw [Nat.add_sub_cancel] at h1
        exact absurd (Nat.dvd_one.mp h1) (by decide)
      have hLam'7 : ¬ 7 ∣ (1 + k * 7 ^ (m - j)) * Lam :=
        Nat.Prime.not_dvd_mul Nat.prime_seven hμ7 hLam7
      refine ⟨(1 + k * 7 ^ (m - j)) * Lam, hLam'7, ?_, ?_⟩
      · -- Levels `≥ i₀`: `μ` preserves the residue verbatim
        -- (`residN_multLow7`, since `ν₇ (Lam·d) = ν₇ d ≥ i₀ > j`).
        intro d hd hν
        have hd0 : d ≠ 0 := ne_of_gt (hpos d hd)
        have hx : padicValNat 7 (Lam * d) = padicValNat 7 d :=
          padicValNat_mul_seven hLam7 hd0
        have hjx : j < padicValNat 7 (Lam * d) := by rw [hx]; omega
        have h1 := residN_multLow7 (k := k) hjm hjx
        rw [mul_assoc, h1, hver d hd hν]
      · -- Levels `j ≤ ν₇ d < i₀`: new level via `hkg`, old levels preserved.
        intro d hd hνj hνi
        have hd0 : d ≠ 0 := ne_of_gt (hpos d hd)
        rcases eq_or_lt_of_le hνj with hEq | hLt
        · -- `ν₇ d = j`: `d` lies at the level just processed.
          have hdl : d ∈ level7 D j := Finset.mem_filter.mpr ⟨hd, hEq.symm⟩
          have hxS : Lam * d ∈ (level7 D j).image (fun d => Lam * d) :=
            Finset.mem_image.mpr ⟨d, hdl, rfl⟩
          have hg := hkg (Lam * d) hxS
          rw [hF'd] at hg
          rwa [mul_assoc]
        · -- `ν₇ d > j`: `μ` preserves `Lam·d`'s residue, hence its digit.
          have hx : padicValNat 7 (Lam * d) = padicValNat 7 d :=
            padicValNat_mul_seven hLam7 hd0
          have hjx : j < padicValNat 7 (Lam * d) := by rw [hx]; exact hLt
          have h1 := residN_multLow7 (k := k) hjm hjx
          have hqd : qdig7 m (((1 + k * 7 ^ (m - j)) * Lam) * d)
              = qdig7 m (Lam * d) := by
            apply qdig7_congr
            rw [mul_assoc]; exact h1
          rw [hqd]
          exact hgd d hd (by omega) hνi
  -- `t = i₀` covers all levels `< i₀`; levels `≥ i₀` are verbatim.
  obtain ⟨lam, hlam7, hver, hgd⟩ := key i₀ le_rfl
  exact ⟨lam, hlam7, hver, fun d hd hlt => hgd d hd (by omega) hlt⟩

/-- **Corollary 3 form**: uniform `{0,6}` forbidden digits — every element
below `i₀` lands on a good digit `{1,…,5}` (equivalently `|λd|_N ≥ 7^m`
via `absModN_ge_iff_qdig7`). -/
theorem filtered7_good (D : Finset ℕ) (hpos : ∀ d ∈ D, 0 < d) {m i₀ : ℕ}
    (_hm : ∀ d ∈ D, padicValNat 7 d ≤ m) (hi₀ : i₀ ≤ m)
    (hlow : ∀ j, j < i₀ → 2 * (level7 D j).card ≤ 6) :
    ∃ lam : ℕ, ¬ 7 ∣ lam ∧
      (∀ d ∈ D, i₀ ≤ padicValNat 7 d →
        (lam * d) % 7 ^ (m + 1) = d % 7 ^ (m + 1)) ∧
      ∀ d ∈ D, padicValNat 7 d < i₀ →
        1 ≤ (qdig7 m (lam * d)).val ∧ (qdig7 m (lam * d)).val ≤ 5 := by
  classical
  have hF : ∀ j, j < i₀ →
      ((level7 D j).sum fun _ => ({0, 6} : Finset (ZMod 7)).card) ≤ 6 := by
    intro j hj
    have hc : ({0, 6} : Finset (ZMod 7)).card = 2 := by decide
    rw [Finset.sum_const, hc, smul_eq_mul]
    have h := hlow j hj
    omega
  obtain ⟨lam, hlam, hver, hgd⟩ := filtered7 D hpos _hm hi₀
    (fun _ => {0, 6}) hF
  refine ⟨lam, hlam, hver, fun d hd hlt => ?_⟩
  have hg := hgd d hd hlt
  have h0 : qdig7 m (lam * d) ≠ 0 := by
    intro h
    apply hg
    rw [h]
    exact Finset.mem_insert_self _ _
  have h6 : qdig7 m (lam * d) ≠ 6 := by
    intro h
    apply hg
    rw [h]
    exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self _))
  have hv : (qdig7 m (lam * d)).val < 7 := ZMod.val_lt _
  have hv0 : (qdig7 m (lam * d)).val ≠ 0 := by
    rw [Ne, ZMod.val_eq_zero]
    exact h0
  have hv6 : (qdig7 m (lam * d)).val ≠ 6 := by
    intro h
    apply h6
    rw [← ZMod.natCast_zmod_val (qdig7 m (lam * d))]
    rw [h]
    decide
  constructor <;> omega

/-- **Top-level scalar step** (paper Lemma 2, first paragraph): for level-`m`
elements, `q(c·d) = c·runit(d)` is a bijection over `c ∈ ZMod 7`, so
`Σ|F| ≤ 5` guarantees a nonzero scalar good for all of them simultaneously. -/
theorem exists_top_scalar {m : ℕ} (S : Finset ℕ)
    (hS : ∀ d ∈ S, padicValNat 7 d = m) (hSpos : ∀ d ∈ S, 0 < d)
    (F : ℕ → Finset (ZMod 7))
    (hcard : (S.sum fun d => (F d).card) ≤ 5) :
    ∃ c : ℕ, 0 < c ∧ c < 7 ∧ ∀ d ∈ S,
      qdig7 m (c * d) ∉ F d := by
  classical
  have hbij : ∀ d ∈ S,
      Function.Bijective (fun c : ZMod 7 => c * runit7 d) := by
    intro d hd
    have hb : runit7 d ≠ 0 := runit7_ne_zero (hSpos d hd)
    rw [← Finite.injective_iff_bijective]
    intro a b hab
    exact mul_right_cancel₀ hb hab
  -- Bad nonzero scalars per `d` ⊆ all scalars with `c·runit(d) ∈ F d`,
  -- which number exactly `|F d|` by the bijection.
  have hbad : ∀ d ∈ S,
      ((Finset.univ.filter fun c : ZMod 7 =>
        c ≠ 0 ∧ c * runit7 d ∈ F d)).card ≤ (F d).card := by
    intro d hd
    have hsub : (Finset.univ.filter fun c : ZMod 7 =>
        c ≠ 0 ∧ c * runit7 d ∈ F d)
        ⊆ Finset.univ.filter fun c : ZMod 7 => c * runit7 d ∈ F d := by
      intro c hc
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
      exact hc.2
    calc (Finset.univ.filter fun c : ZMod 7 =>
            c ≠ 0 ∧ c * runit7 d ∈ F d).card
        ≤ (Finset.univ.filter fun c : ZMod 7 => c * runit7 d ∈ F d).card :=
          Finset.card_le_card hsub
      _ = (F d).card := card_filter_bij (hbij d hd)
  have hU : (S.biUnion (fun d => Finset.univ.filter (fun c : ZMod 7 =>
      c ≠ 0 ∧ c * runit7 d ∈ F d))).card ≤ 5 := by
    refine le_trans Finset.card_biUnion_le ?_
    calc ∑ d ∈ S, (Finset.univ.filter (fun c : ZMod 7 =>
            c ≠ 0 ∧ c * runit7 d ∈ F d)).card
        ≤ ∑ d ∈ S, (F d).card :=
          Finset.sum_le_sum fun d hd => hbad d hd
      _ ≤ 5 := hcard
  -- The six nonzero scalars minus the bad union is nonempty.
  have hsub2 : S.biUnion (fun d => Finset.univ.filter (fun c : ZMod 7 =>
      c ≠ 0 ∧ c * runit7 d ∈ F d))
      ⊆ Finset.univ.filter (fun c : ZMod 7 => c ≠ 0) := by
    intro c hc
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ,
      true_and] at hc ⊢
    obtain ⟨d, hd, hc'⟩ := hc
    exact hc'.1
  have hnon : ((Finset.univ.filter fun c : ZMod 7 => c ≠ 0) \
      S.biUnion (fun d => Finset.univ.filter (fun c : ZMod 7 =>
        c ≠ 0 ∧ c * runit7 d ∈ F d))).Nonempty := by
    rw [← Finset.card_pos, Finset.card_sdiff_of_subset hsub2]
    have hcu : (Finset.univ.filter fun c : ZMod 7 => c ≠ 0).card = 6 := by
      rw [Finset.card_filter]
      have : (∑ c : ZMod 7, if c ≠ 0 then (1 : ℕ) else 0) = 6 := by decide
      exact this
    omega
  obtain ⟨C, hC⟩ := hnon
  rw [Finset.mem_sdiff] at hC
  obtain ⟨hCnz, hCB⟩ := hC
  rw [Finset.mem_filter] at hCnz
  have hgoodC : ∀ d ∈ S, C * runit7 d ∉ F d := by
    intro d hd
    have hCd : C ∉ Finset.univ.filter (fun c : ZMod 7 =>
        c ≠ 0 ∧ c * runit7 d ∈ F d) :=
      fun hmem => hCB (Finset.mem_biUnion.mpr ⟨d, hd, hmem⟩)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and] at hCd
    exact hCd hCnz.2
  refine ⟨C.val, ?_, ZMod.val_lt C, fun d hd => ?_⟩
  · have : C.val ≠ 0 := by
      intro h0
      rw [ZMod.val_eq_zero] at h0
      exact hCnz.2 h0
    omega
  have hq := qdig7_multTop (m := m) (l := C.val) (hS d hd)
  rw [hq, ZMod.natCast_zmod_val C]
  exact hgoodC d hd
