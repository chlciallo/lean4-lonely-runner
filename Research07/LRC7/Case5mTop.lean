import Research07.LRC7.Case4Int
import Research07.LRC7.NormU
import Research07.LRC7.Case5mBase
import Research07.LRC7.Case5mCases

/-!
# §6 top-level assembly helpers — `Case5mTop`

Verified pieces staged from `_dev/scratch` (all compiled under the 12 GB
memwatch cap with axiom whitelist `[propext, Classical.choice, Quot.sound]`):

* `lrc7_case3u_top` — the `|A'| ≤ 3` collapse branch of `normU7`
  normalization (counting argument, no subset-enumeration `decide`).
* `qdig7_add_top_resid` — exact leading-digit shift by a pure top-level
  residue `k·7^m` (§6.1 Case B engine).
* `case61_dichot'` — the §6.1 `×3` dichotomy under the `{0,1,6}` boundary
  pair envelope of `lemma9_i'` (mirrored `f`-order constraint).
* `lrc7_hc6_of` — the `hc6` leaf adapter: `normU7` normalization +
  cardinality dispatch (`≤3`/`4`/parameterized `5`).
-/


/-! Scratch: `lrc7_case3u_top` — ≤3 normalized units + one top-level element.
Finite argument (no subset-enumeration `decide`): each of the ≤3 shifted
points `p + c·t` forbids at most two shifts `t = (v−p)·c⁻¹` (`v ∈ {0,6}`),
so at most 6 of the 7 shifts in `ZMod 7` are bad — one always survives. -/

/-- The two shifts that send `p + c·t` into `{0,6}`. -/
private def badShift (c p : ZMod 7) : Finset (ZMod 7) :=
  {(0 - p) * c⁻¹, (6 - p) * c⁻¹}

private theorem badShift_card_le (c p : ZMod 7) : (badShift c p).card ≤ 2 := by
  show ({(0 - p) * c⁻¹, (6 - p) * c⁻¹} : Finset (ZMod 7)).card ≤ 2
  calc ({(0 - p) * c⁻¹, (6 - p) * c⁻¹} : Finset (ZMod 7)).card
      ≤ ({(6 - p) * c⁻¹} : Finset (ZMod 7)).card + 1 := Finset.card_insert_le _ _
    _ = 2 := by rw [Finset.card_singleton]

private theorem mem_badShift {c : ZMod 7} (hc : c ≠ 0) (p t : ZMod 7) :
    t ∈ badShift c p ↔ p + c * t ∈ bad06 := by
  show t ∈ ({(0 - p) * c⁻¹, (6 - p) * c⁻¹} : Finset (ZMod 7)) ↔ _
  rw [Finset.mem_insert, Finset.mem_singleton, bad06, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro (rfl | rfl)
    · left
      have hmul : c * ((0 - p) * c⁻¹) = 0 - p := by
        calc c * ((0 - p) * c⁻¹) = (0 - p) * (c⁻¹ * c) := by ring
          _ = 0 - p := by rw [inv_mul_cancel₀ hc, mul_one]
      rw [hmul]
      ring
    · right
      have hmul : c * ((6 - p) * c⁻¹) = 6 - p := by
        calc c * ((6 - p) * c⁻¹) = (6 - p) * (c⁻¹ * c) := by ring
          _ = 6 - p := by rw [inv_mul_cancel₀ hc, mul_one]
      rw [hmul]
      ring
  · rintro (h | h)
    · left
      have hsub : c * t = 0 - p := by rw [← h]; ring
      calc t = c⁻¹ * (c * t) := (inv_mul_cancel_left₀ hc t).symm
        _ = c⁻¹ * (0 - p) := by rw [hsub]
        _ = (0 - p) * c⁻¹ := mul_comm _ _
    · right
      have hsub : c * t = 6 - p := by rw [← h]; ring
      calc t = c⁻¹ * (c * t) := (inv_mul_cancel_left₀ hc t).symm
        _ = c⁻¹ * (6 - p) := by rw [hsub]
        _ = (6 - p) * c⁻¹ := mul_comm _ _

/-- Three class-point sets of total size ≤ 3 admit a `t` whose shifted union
avoids `{0,6}`. -/
private theorem case3u_finite (X₁ X₂ X₄ : Finset (ZMod 7))
    (hsum : X₁.card + X₂.card + X₄.card ≤ 3) :
    ∃ t : ZMod 7, avoids06
      ((X₁.image (· + t)) ∪ (X₂.image (· + 2 * t)) ∪ (X₄.image (· + 4 * t))) := by
  classical
  have hb1 : (X₁.biUnion (badShift 1)).card ≤ 2 * X₁.card := by
    calc (X₁.biUnion (badShift 1)).card
        ≤ ∑ x ∈ X₁, (badShift 1 x).card := Finset.card_biUnion_le
      _ ≤ ∑ _x ∈ X₁, 2 := Finset.sum_le_sum fun x _ => badShift_card_le 1 x
      _ = 2 * X₁.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have hb2 : (X₂.biUnion (badShift 2)).card ≤ 2 * X₂.card := by
    calc (X₂.biUnion (badShift 2)).card
        ≤ ∑ x ∈ X₂, (badShift 2 x).card := Finset.card_biUnion_le
      _ ≤ ∑ _x ∈ X₂, 2 := Finset.sum_le_sum fun x _ => badShift_card_le 2 x
      _ = 2 * X₂.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have hb4 : (X₄.biUnion (badShift 4)).card ≤ 2 * X₄.card := by
    calc (X₄.biUnion (badShift 4)).card
        ≤ ∑ x ∈ X₄, (badShift 4 x).card := Finset.card_biUnion_le
      _ ≤ ∑ _x ∈ X₄, 2 := Finset.sum_le_sum fun x _ => badShift_card_le 4 x
      _ = 2 * X₄.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  set T := X₁.biUnion (badShift 1) ∪ X₂.biUnion (badShift 2) ∪
    X₄.biUnion (badShift 4) with hT
  have hT6 : T.card ≤ 6 := by
    calc T.card
        ≤ (X₁.biUnion (badShift 1) ∪ X₂.biUnion (badShift 2)).card
          + (X₄.biUnion (badShift 4)).card := Finset.card_union_le _ _
      _ ≤ (X₁.biUnion (badShift 1)).card + (X₂.biUnion (badShift 2)).card
          + (X₄.biUnion (badShift 4)).card :=
        add_le_add (Finset.card_union_le _ _) le_rfl
      _ ≤ 2 * X₁.card + 2 * X₂.card + 2 * X₄.card :=
        add_le_add (add_le_add hb1 hb2) hb4
      _ ≤ 6 := by omega
  obtain ⟨t, htT⟩ : ∃ t : ZMod 7, t ∉ T := by
    by_contra h
    have hTu : T = Finset.univ := Finset.eq_univ_iff_forall.mpr fun t => by
      by_contra ht
      exact h ⟨t, ht⟩
    have hcard : T.card = 7 := by rw [hTu, Finset.card_univ, ZMod.card]
    omega
  refine ⟨t, fun y hy => ?_⟩
  rw [Finset.mem_union, Finset.mem_union] at hy
  rcases hy with (hy | hy) | hy
  · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hy
    intro hyb
    exact htT (Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_biUnion.mpr ⟨p, hp,
        (mem_badShift (by decide : (1 : ZMod 7) ≠ 0) p t).mpr
          (by simpa using hyb)⟩)))
  · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hy
    intro hyb
    exact htT (Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_biUnion.mpr ⟨p, hp,
        (mem_badShift (by decide : (2 : ZMod 7) ≠ 0) p t).mpr hyb⟩)))
  · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hy
    intro hyb
    exact htT (Finset.mem_union_right _
      (Finset.mem_biUnion.mpr ⟨p, hp,
        (mem_badShift (by decide : (4 : ZMod 7) ≠ 0) p t).mpr hyb⟩))

/-- `q ∉ {0,6}` gives `1 ≤ q.val ≤ 5` (for `absModN_ge_iff_qdig7`). -/
private theorem val_bounds_of_not_bad06 {q : ZMod 7}
    (h : q ∉ bad06) : 1 ≤ q.val ∧ q.val ≤ 5 := by
  rw [bad06, Finset.mem_insert, Finset.mem_singleton, not_or] at h
  have hlt : q.val < 7 := ZMod.val_lt q
  have hv0 : q.val ≠ 0 := fun hv => h.1 (by
    rw [← ZMod.natCast_zmod_val q, hv]; decide)
  have hv6 : q.val ≠ 6 := fun hv => h.2 (by
    rw [← ZMod.natCast_zmod_val q, hv]; decide)
  interval_cases q.val <;> omega

/-- ≤3 normalized units (classes `{1,2,4}`) plus a top-level element `d6` at
level `m`: some `λ ∈ Λ₀` (in particular `0 < λ` and `7 ∤ λ`) puts every scaled
residue at distance `≥ 7^m`. This is the `|A'| = 3` collapse branch of the
`normU7` normalization in the §6 assembly. -/
theorem lrc7_case3u_top {m : ℕ} (hm : 0 < m) {A : Finset ℕ}
    (hcard : A.card ≤ 3) (hpos : ∀ d ∈ A, 0 < d)
    (hunit : ∀ d ∈ A, padicValNat 7 d = 0)
    (hcls : ∀ d ∈ A, runit7 d ∈ ({1, 2, 4} : Finset (ZMod 7)))
    {d6 : ℕ} (hd6 : padicValNat 7 d6 = m) (hd6pos : 0 < d6) :
    ∃ lam : ℕ, 0 < lam ∧ ¬ 7 ∣ lam ∧
      ∀ d ∈ A ∪ {d6}, 7 ^ m ≤ absModN (lam * d) (7 ^ (m + 1)) := by
  classical
  set F1 := A.filter fun d => runit7 d = (1 : ZMod 7) with hF1
  set F2 := A.filter fun d => runit7 d = (2 : ZMod 7) with hF2
  set F4 := A.filter fun d => runit7 d = (4 : ZMod 7) with hF4
  have hdis12 : Disjoint F1 F2 := Finset.disjoint_left.mpr fun x hx1 hx2 => by
    rw [hF1, Finset.mem_filter] at hx1
    rw [hF2, Finset.mem_filter] at hx2
    have : (1 : ZMod 7) = 2 := hx1.2.symm.trans hx2.2
    exact absurd this (by decide)
  have hdis124 : Disjoint (F1 ∪ F2) F4 :=
    Finset.disjoint_left.mpr fun x hx hx4 => by
      rw [Finset.mem_union] at hx
      rw [hF1, Finset.mem_filter, hF2, Finset.mem_filter] at hx
      rw [hF4, Finset.mem_filter] at hx4
      rcases hx with hx | hx
      · have : (1 : ZMod 7) = 4 := hx.2.symm.trans hx4.2
        exact absurd this (by decide)
      · have : (2 : ZMod 7) = 4 := hx.2.symm.trans hx4.2
        exact absurd this (by decide)
  have hcard3 : (F1 ∪ F2 ∪ F4).card = F1.card + F2.card + F4.card := by
    rw [Finset.card_union_of_disjoint hdis124,
      Finset.card_union_of_disjoint hdis12]
  have hsub : F1 ∪ F2 ∪ F4 ⊆ A := by
    intro x hx
    rw [Finset.mem_union, Finset.mem_union] at hx
    rcases hx with (hx | hx) | hx
    · exact Finset.filter_subset _ _ hx
    · exact Finset.filter_subset _ _ hx
    · exact Finset.filter_subset _ _ hx
  have hsum : (F1.image (qdig7 m)).card + (F2.image (qdig7 m)).card
      + (F4.image (qdig7 m)).card ≤ 3 := by
    calc (F1.image (qdig7 m)).card + (F2.image (qdig7 m)).card
          + (F4.image (qdig7 m)).card
        ≤ F1.card + F2.card + F4.card :=
        add_le_add (add_le_add Finset.card_image_le Finset.card_image_le)
          Finset.card_image_le
      _ = (F1 ∪ F2 ∪ F4).card := hcard3.symm
      _ ≤ A.card := Finset.card_le_card hsub
      _ ≤ 3 := hcard
  obtain ⟨t, ht⟩ := case3u_finite _ _ _ hsum
  have hcls' : ∀ d ∈ A, runit7 d ∈
      ({1, 2 * 1, 4 * 1} : Finset (ZMod 7)) := by
    simpa only [mul_one] using hcls
  have ht' : avoids06
      (((A.filter fun d => runit7 d = 1).image (qdig7 m)).image (· + t)
        ∪ ((A.filter fun d => runit7 d = 2 * 1).image (qdig7 m)).image (· + 2 * t)
        ∪ ((A.filter fun d => runit7 d = 4 * 1).image (qdig7 m)).image
          (· + 4 * t)) := by
    simpa only [mul_one] using ht
  obtain ⟨lam, hlam_mem, hgood⟩ := exists_lambda0_of_shift hm
    (s := 1) one_ne_zero hunit hcls' t ht'
  have hlamnd : ¬ 7 ∣ lam := not_dvd_of_mem_multLow7_zero hm hlam_mem
  have hlampos : 0 < lam := by
    obtain ⟨k, -, hk⟩ := eq_one_add_of_mem_multLow7 hlam_mem
    omega
  refine ⟨lam, hlampos, hlamnd, fun d hd => ?_⟩
  rw [Finset.mem_union, Finset.mem_singleton] at hd
  rcases hd with hd | rfl
  · rw [absModN_ge_iff_qdig7 (by rw [hunit d hd]; exact hm) (hpos d hd) hlamnd]
    exact val_bounds_of_not_bad06 (hgood d hd)
  · exact absModN_top_ge7 hd6 hd6pos hlamnd


/-! ### The `hc6` adapter: `normU7` normalization + cardinality dispatch -/

/-- **`hc6` leaf adapter**: normalize the five units via `normU7` into the
quadratic-residue classes `{1,2,4}`; the normalized image `A'` may collapse
(`|A'| ∈ {1,…,5}` — each rep's fiber is the two residue classes `{r,−r}`).
Dispatch: `|A'| ≤ 3` → `lrc7_case3u_top`; `|A'| = 4` → `lrc7_case4` on
`A' ∪ {d6}`; `|A'| = 5` → the `hcase5` parameter (the real §6 dispatch,
pending `case61`–`case66`). -/
theorem lrc7_hc6_of {m : ℕ} (hm : 1 < m)
    (hcase5 : ∀ {A : Finset ℕ}, A.card = 5 →
      (∀ d ∈ A, 0 < d) → (∀ d ∈ A, padicValNat 7 d = 0) →
      (∀ d ∈ A, runit7 d ∈ ({1, 2, 4} : Finset (ZMod 7))) →
      ∀ d6 : ℕ, padicValNat 7 d6 = m → 0 < d6 →
      ∃ lam : ℕ, 0 < lam ∧ ¬ 7 ∣ lam ∧
        ∀ d ∈ A ∪ {d6}, 7 ^ m ≤ absModN (lam * d) (7 ^ (m + 1)))
    (A : Finset ℕ) (hA : A.card = 5)
    (_hpos : ∀ d ∈ A, 0 < d) (hnd : ∀ d ∈ A, ¬ 7 ∣ d)
    (d6 : ℕ) (hd6 : padicValNat 7 d6 = m) (hd6pos : 0 < d6) :
    ∃ lam : ℕ, 0 < lam ∧ ¬ 7 ∣ lam ∧
      ∀ d ∈ A ∪ {d6}, 7 ^ m ≤ absModN (lam * d) (7 ^ (m + 1)) := by
  classical
  set N := 7 ^ (m + 1) with hN
  have hNpos : 0 < N := Nat.pow_pos (by norm_num)
  have h7N : 7 ∣ N := dvd_pow_self 7 (by omega)
  set A' := A.image (normU7 N) with hA'
  have hdN : ∀ d ∈ A, d % N ≠ 0 := fun d hd h0 =>
    hnd d hd (dvd_trans h7N (Nat.dvd_of_mod_eq_zero h0))
  have hpos' : ∀ d' ∈ A', 0 < d' := by
    intro d' hd'
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hd'
    exact normU7_pos hNpos (hdN d hd)
  have hunit' : ∀ d' ∈ A', padicValNat 7 d' = 0 := by
    intro d' hd'
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hd'
    exact normU7_padic hNpos h7N (hnd d hd)
  have hcls' : ∀ d' ∈ A', runit7 d' ∈ ({1, 2, 4} : Finset (ZMod 7)) := by
    intro d' hd'
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hd'
    exact normU7_runit hNpos h7N (hnd d hd)
  have hcardA' : A'.card ≤ 5 := le_trans Finset.card_image_le (le_of_eq hA)
  -- bound transfer: rep bounds cover the raw elements (`absModN` is
  -- flip-invariant, `normU7_absModN`).
  have htr : ∀ lam : ℕ,
      (∀ d' ∈ A' ∪ {d6}, 7 ^ m ≤ absModN (lam * d') N) →
      ∀ d ∈ A ∪ {d6}, 7 ^ m ≤ absModN (lam * d) N := by
    intro lam hb d hd
    rw [Finset.mem_union, Finset.mem_singleton] at hd
    rcases hd with hd | rfl
    · have hmem : normU7 N d ∈ A' := Finset.mem_image.mpr ⟨d, hd, rfl⟩
      have h := hb _ (Finset.mem_union_left _ hmem)
      rwa [normU7_absModN hNpos] at h
    · exact hb _ (Finset.mem_union_right _
        (Finset.mem_singleton_self _))
  rcases lt_or_ge A'.card 4 with hlt | hge
  · obtain ⟨lam, hlp, hlnd, hb⟩ := lrc7_case3u_top (m := m) (A := A')
      (by omega) (by omega) hpos' hunit' hcls' hd6 hd6pos
    exact ⟨lam, hlp, hlnd, htr lam hb⟩
  · rcases eq_or_lt_of_le hge with h4 | h5
    · -- `|A'| = 4`: `A' ∪ {d6}` is exactly the `lrc7_case4` shape.
      set D := A' ∪ {d6} with hD
      have hDpos : ∀ d ∈ D, 0 < d := by
        intro d hd
        rw [hD, Finset.mem_union, Finset.mem_singleton] at hd
        rcases hd with hd | rfl
        · exact hpos' d hd
        · exact hd6pos
      have hDle : ∀ d ∈ D, padicValNat 7 d ≤ m := by
        intro d hd
        rw [hD, Finset.mem_union, Finset.mem_singleton] at hd
        rcases hd with hd | rfl
        · rw [hunit' d hd]; omega
        · rw [hd6]
      have hDmax : ∃ d ∈ D, padicValNat 7 d = m :=
        ⟨d6, Finset.mem_union_right _ (Finset.mem_singleton_self _), hd6⟩
      have hlvl : level7 D 0 = A' := by
        ext d
        simp only [level7, Finset.mem_filter, hD, Finset.mem_union,
          Finset.mem_singleton]
        constructor
        · rintro ⟨(hd' | rfl), hν⟩
          · exact hd'
          · rw [hd6] at hν; omega
        · intro hd'
          exact ⟨Or.inl hd', hunit' d hd'⟩
      have hc : (level7 D 0).card = 4 := by rw [hlvl]; exact h4.symm
      have hDcard : D.card ≤ 6 := by
        calc D.card ≤ A'.card + 1 := by
              rw [hD]; exact Finset.card_union_le _ _
          _ ≤ 6 := by omega
      obtain ⟨lam, hlp, hlnd, hb⟩ :=
        lrc7_case4 (m := m) D hDpos hDle (by omega) hDmax hc hDcard
      exact ⟨lam, hlp, hlnd, htr lam hb⟩
    · -- `|A'| = 5`: the real §6 dispatch.
      have hA5 : A'.card = 5 := by omega
      obtain ⟨lam, hlp, hlnd, hb⟩ :=
        hcase5 hA5 hpos' hunit' hcls' d6 hd6 hd6pos
      exact ⟨lam, hlp, hlnd, htr lam hb⟩


/-! ### §6.1 Case B: exact digit shift by a pure top-level residue -/

/-- `(a·7^m + b) / 7^m = a` when `b < 7^m` (local clone). -/
private theorem mul_pow_add_div {a b m : ℕ} (hb : b < 7 ^ m) :
    (a * 7 ^ m + b) / 7 ^ m = a := by
  have hP : 0 < 7 ^ m := Nat.pow_pos (by norm_num)
  rw [add_comm (a * 7 ^ m) b, mul_comm a (7 ^ m),
    Nat.add_mul_div_left _ _ hP, Nat.div_eq_of_lt hb, zero_add]

/-- Decompose `x % 7^{m+1}` as `q·7^m + f` (local clone). -/
private theorem residue_decomp {m x : ℕ} :
    ∃ q f : ℕ, x % 7 ^ (m + 1) = q * 7 ^ m + f ∧ q < 7 ∧ f < 7 ^ m := by
  refine ⟨(x % 7 ^ (m + 1)) / 7 ^ m, (x % 7 ^ (m + 1)) % 7 ^ m, ?_, ?_,
    Nat.mod_lt _ (Nat.pow_pos (by norm_num))⟩
  · rw [mul_comm, Nat.div_add_mod]
  · rw [Nat.div_lt_iff_lt_mul (Nat.pow_pos (by norm_num)), ← pow_succ']
    exact Nat.mod_lt _ (Nat.pow_pos (by norm_num))

/-- `qdig7` of a truncated residue equals the unwrapped digit cast (local
clone). -/
private theorem qdig7_eMod_of (m a : ℕ) :
    qdig7 m (a % 7 ^ (m + 1)) = ((a / 7 ^ m : ℕ) : ZMod 7) := by
  rw [qdig7_eq_cast_div]
  have hcast : (((a % 7 ^ (m + 1)) / 7 ^ m : ℕ) : ZMod 7)
      = ((a / 7 ^ m : ℕ) : ZMod 7) := by
    rw [pow_succ', Nat.mod_mul_left_div_self,
      ZMod.natCast_eq_natCast_iff', Nat.mod_mod]
  exact hcast

/-- **Exact digit shift by a pure-top residue**: adding `k·7^m` to a residue
shifts the leading digit by exactly `k` (no borrow — the low part is
untouched). This is what makes the `ν(E) = {m}` case clean: `q(A₁)` is a
*translate* of the top-residue digits. -/
theorem qdig7_add_top_resid {m x y k : ℕ}
    (h : x % 7 ^ (m + 1) = (y % 7 ^ (m + 1) + k * 7 ^ m) % 7 ^ (m + 1)) :
    qdig7 m x = qdig7 m y + (k : ZMod 7) := by
  obtain ⟨b, f, hb, hb7, hf⟩ := residue_decomp (m := m) (x := y)
  have hqy : qdig7 m y = (b : ZMod 7) := by
    unfold qdig7
    rw [hb, mul_pow_add_div hf]
  rw [hqy]
  unfold qdig7
  rw [h]
  have hsum : y % 7 ^ (m + 1) + k * 7 ^ m = (b + k) * 7 ^ m + f := by
    rw [hb]; ring
  rw [hsum]
  have hlt : ((b + k) % 7) * 7 ^ m + f < 7 ^ (m + 1) := by
    have h1 : (b + k) % 7 ≤ 6 := by
      have := Nat.mod_lt (b + k) (by norm_num : 0 < 7)
      omega
    calc ((b + k) % 7) * 7 ^ m + f
        ≤ 6 * 7 ^ m + f :=
        add_le_add (Nat.mul_le_mul h1 (le_refl _)) le_rfl
      _ < 7 ^ (m + 1) := by rw [pow_succ']; omega
  have hdecomp : (b + k) * 7 ^ m
      = (7 * ((b + k) / 7) + (b + k) % 7) * 7 ^ m := by
    rw [Nat.div_add_mod]
  have hmod : ((b + k) * 7 ^ m + f) % 7 ^ (m + 1)
      = ((b + k) % 7) * 7 ^ m + f := by
    conv_lhs => rw [hdecomp]
    conv_lhs => rw [show (7 * ((b + k) / 7) + (b + k) % 7) * 7 ^ m + f
        = 7 ^ (m + 1) * ((b + k) / 7) + (((b + k) % 7) * 7 ^ m + f) by
          rw [pow_succ']; ring]
    rw [Nat.mul_add_mod]
    exact Nat.mod_eq_of_lt hlt
  rw [hmod, mul_pow_add_div hf]
  have hcast : (((b + k) % 7 : ℕ) : ZMod 7) = (b : ZMod 7) + k := by
    have h1 : (((b + k) % 7 : ℕ) : ZMod 7) = ((b + k : ℕ) : ZMod 7) :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mpr (Nat.mod_modEq _ _)
    rw [h1, Nat.cast_add]
  rw [hcast]


/-! ### §6.1 Case A boundary: `×3` dichotomy under `{0,1,6}` -/


/-- `(6,0)`-pair constraint under `{0,1,6}`: `6 − c ∈ {0,1,6}` forces
`c = 0`, i.e. `f₀ ≤ f₆`. -/
private theorem case61_flt'_dec :
    ∀ f₆ f₀ : ZMod 7,
      (6 : ZMod 7) - 0 - (if f₆.val < f₀.val then (1 : ZMod 7) else 0)
        ∈ ({0, 1, 6} : Finset (ZMod 7)) →
      f₀.val ≤ f₆.val := by
  decide

/-- First alternative helper (unchanged): `q = 6 → f ≥ 3` scales into
`{0,1,2,5,6}`. -/
private theorem case61_mem_t1'_dec :
    ∀ q f : ZMod 7, q ∈ ({0, 6} : Finset (ZMod 7)) →
      (q = 6 → 3 ≤ f.val) →
      3 * q + ((3 * f.val / 7 : ℕ) : ZMod 7)
        ∈ ({0, 1, 2, 5, 6} : Finset (ZMod 7)) := by
  decide

/-- Second alternative helper (non-strict bound): a `0`-digit with
`f ≤ f₆ < 3` has zero carry. -/
private theorem case61_mem_t2'_dec :
    ∀ q f f₆ : ZMod 7, q ∈ ({0, 6} : Finset (ZMod 7)) →
      f₆.val < 3 → (q = 0 → f.val ≤ f₆.val) →
      3 * q + ((3 * f.val / 7 : ℕ) : ZMod 7)
        ∈ ({0, 1, 4, 5, 6} : Finset (ZMod 7)) := by
  decide

/-- §6.1 `×3` dichotomy, boundary version: same conclusion as
`case61_dichot` but pair-difference digits may range over `{0,1,6}`
(the `lemma9_i'` envelope). -/
theorem case61_dichot' {q₁ q₂ q₃ f₁ f₂ f₃ : ZMod 7}
    (hq₁ : q₁ ∈ ({0, 6} : Finset (ZMod 7)))
    (hq₂ : q₂ ∈ ({0, 6} : Finset (ZMod 7)))
    (hq₃ : q₃ ∈ ({0, 6} : Finset (ZMod 7)))
    (h₁₂ : q₁ - q₂ - (if f₁.val < f₂.val then (1 : ZMod 7) else 0)
      ∈ ({0, 1, 6} : Finset (ZMod 7)))
    (h₁₃ : q₁ - q₃ - (if f₁.val < f₃.val then (1 : ZMod 7) else 0)
      ∈ ({0, 1, 6} : Finset (ZMod 7)))
    (h₂₁ : q₂ - q₁ - (if f₂.val < f₁.val then (1 : ZMod 7) else 0)
      ∈ ({0, 1, 6} : Finset (ZMod 7)))
    (h₂₃ : q₂ - q₃ - (if f₂.val < f₃.val then (1 : ZMod 7) else 0)
      ∈ ({0, 1, 6} : Finset (ZMod 7)))
    (h₃₁ : q₃ - q₁ - (if f₃.val < f₁.val then (1 : ZMod 7) else 0)
      ∈ ({0, 1, 6} : Finset (ZMod 7)))
    (h₃₂ : q₃ - q₂ - (if f₃.val < f₂.val then (1 : ZMod 7) else 0)
      ∈ ({0, 1, 6} : Finset (ZMod 7))) :
    ({3 * q₁ + ((3 * f₁.val / 7 : ℕ) : ZMod 7),
      3 * q₂ + ((3 * f₂.val / 7 : ℕ) : ZMod 7),
      3 * q₃ + ((3 * f₃.val / 7 : ℕ) : ZMod 7)} : Finset (ZMod 7))
      ⊆ ({0, 1, 2, 5, 6} : Finset (ZMod 7)) ∨
    ({3 * q₁ + ((3 * f₁.val / 7 : ℕ) : ZMod 7),
      3 * q₂ + ((3 * f₂.val / 7 : ℕ) : ZMod 7),
      3 * q₃ + ((3 * f₃.val / 7 : ℕ) : ZMod 7)} : Finset (ZMod 7))
      ⊆ ({0, 1, 4, 5, 6} : Finset (ZMod 7)) := by
  have key : ∀ qi qj fi fj : ZMod 7,
      qi - qj - (if fi.val < fj.val then (1 : ZMod 7) else 0)
        ∈ ({0, 1, 6} : Finset (ZMod 7)) →
      qi = 6 → qj = 0 → fj.val ≤ fi.val := by
    intro qi qj fi fj h hqi hqj
    rw [hqi, hqj] at h
    exact case61_flt'_dec fi fj h
  by_cases h1 : q₁ = 6 → 3 ≤ f₁.val
  · by_cases h2 : q₂ = 6 → 3 ≤ f₂.val
    · by_cases h3 : q₃ = 6 → 3 ≤ f₃.val
      · left
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl
        · exact case61_mem_t1'_dec q₁ f₁ hq₁ h1
        · exact case61_mem_t1'_dec q₂ f₂ hq₂ h2
        · exact case61_mem_t1'_dec q₃ f₃ hq₃ h3
      · obtain ⟨h3, hf3⟩ := not_imp.mp h3
        have hf3 : f₃.val < 3 := not_le.mp hf3
        right
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl
        · exact case61_mem_t2'_dec q₁ f₁ f₃ hq₁ hf3
            (fun h0 => key q₃ q₁ f₃ f₁ h₃₁ h3 h0)
        · exact case61_mem_t2'_dec q₂ f₂ f₃ hq₂ hf3
            (fun h0 => key q₃ q₂ f₃ f₂ h₃₂ h3 h0)
        · exact case61_mem_t2'_dec q₃ f₃ f₃ hq₃ hf3
            (fun h0 => absurd (h0.symm.trans h3) (by decide))
    · obtain ⟨h2, hf2⟩ := not_imp.mp h2
      have hf2 : f₂.val < 3 := not_le.mp hf2
      right
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact case61_mem_t2'_dec q₁ f₁ f₂ hq₁ hf2
          (fun h0 => key q₂ q₁ f₂ f₁ h₂₁ h2 h0)
      · exact case61_mem_t2'_dec q₂ f₂ f₂ hq₂ hf2
          (fun h0 => absurd (h0.symm.trans h2) (by decide))
      · exact case61_mem_t2'_dec q₃ f₃ f₂ hq₃ hf2
          (fun h0 => key q₂ q₃ f₂ f₃ h₂₃ h2 h0)
  · obtain ⟨h1, hf1⟩ := not_imp.mp h1
    have hf1 : f₁.val < 3 := not_le.mp hf1
    right
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact case61_mem_t2'_dec q₁ f₁ f₁ hq₁ hf1
        (fun h0 => absurd (h0.symm.trans h1) (by decide))
    · exact case61_mem_t2'_dec q₂ f₂ f₁ hq₂ hf1
        (fun h0 => key q₁ q₂ f₁ f₂ h₁₂ h1 h0)
    · exact case61_mem_t2'_dec q₃ f₃ f₁ hq₃ hf1
        (fun h0 => key q₁ q₃ f₁ f₃ h₁₃ h1 h0)

/-- §6.1 Case B finite fact (corrected form): `q(A₁) = a + ({0} ∪ K)` needs
the *including-0* set dilated into a 5-interval — the two misses of
`{0} ∪ c·K` must be consecutive.  The `c` achieving this need not coincide
with the `c` for `K` alone, so the decide runs on this exact form
(verified over all `K ⊆ {1,…,6}` with `|K| ≤ 4` — collisions can shrink
`K` below 4). -/
theorem case61_dilate4_zero (K : Finset (ZMod 7))
    (hK : K ⊆ ({1, 2, 3, 4, 5, 6} : Finset (ZMod 7))) (hcard : K.card ≤ 4) :
    ∃ c : ZMod 7, c ≠ 0 ∧
      apLen (({0} : Finset (ZMod 7)) ∪ K.image (· * c)) ≤ 5 := by
  revert hK hcard K
  decide

#print axioms case61_dilate4_zero

private theorem mem_nonzero_seven {q : ZMod 7} (hq : q ≠ 0) :
    q ∈ ({1, 2, 3, 4, 5, 6} : Finset (ZMod 7)) := by
  have hU : ({1, 2, 3, 4, 5, 6} : Finset (ZMod 7)) =
      Finset.univ.erase 0 := by decide
  rw [hU, Finset.mem_erase]
  exact ⟨hq, Finset.mem_univ _⟩

private theorem apLen_mono' {X Y : Finset (ZMod 7)} (hXY : X ⊆ Y) :
    apLen X ≤ apLen Y := by
  obtain ⟨i, hi⟩ := (apLen_le_iff Y (apLen Y) (apLen_le_seven _)).mp le_rfl
  exact (apLen_le_iff X (apLen Y) (apLen_le_seven _)).mpr
    ⟨i, fun x hx => hi (hXY hx)⟩

/-- `ZMod`-cast of `eMod7` (local copy — the helper is `private` in
`Case5mCases`/`Case5mBase`). -/
private theorem eMod7_zmod_cast' (m x y : ℕ) :
    ((eMod7 m x y : ℕ) : ZMod (7 ^ (m + 1))) =
      if runit7 y = 2 * runit7 x then 2 * (x : ZMod _) - (y : ZMod _)
      else if runit7 x = 2 * runit7 y then 2 * (y : ZMod _) - (x : ZMod _)
      else (x : ZMod _) - (y : ZMod _) := by
  have hcast : ∀ a : ℕ,
      ((a % 7 ^ (m + 1) : ℕ) : ZMod (7 ^ (m + 1))) = (a : ZMod _) := by
    intro a
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr (Nat.mod_mod a _)
  have hN : ((7 ^ (m + 1) : ℕ) : ZMod (7 ^ (m + 1))) = 0 := ZMod.natCast_self _
  unfold eMod7
  split_ifs with h1 h2
  · rw [hcast, Nat.cast_sub (by
      have : y % 7 ^ (m + 1) < 7 ^ (m + 1) :=
        Nat.mod_lt _ (Nat.pow_pos (by norm_num))
      omega : y % 7 ^ (m + 1) ≤ 2 * (x % 7 ^ (m + 1)) + 7 ^ (m + 1))]
    rw [Nat.cast_add, Nat.cast_mul, hcast x, hcast y, hN, Nat.cast_ofNat]
    ring
  · rw [hcast, Nat.cast_sub (by
      have : x % 7 ^ (m + 1) < 7 ^ (m + 1) :=
        Nat.mod_lt _ (Nat.pow_pos (by norm_num))
      omega : x % 7 ^ (m + 1) ≤ 2 * (y % 7 ^ (m + 1)) + 7 ^ (m + 1))]
    rw [Nat.cast_add, Nat.cast_mul, hcast y, hcast x, hN, Nat.cast_ofNat]
    ring
  · rw [hcast, Nat.cast_sub (by
      have : y % 7 ^ (m + 1) < 7 ^ (m + 1) :=
        Nat.mod_lt _ (Nat.pow_pos (by norm_num))
      omega : y % 7 ^ (m + 1) ≤ x % 7 ^ (m + 1) + 7 ^ (m + 1))]
    rw [Nat.cast_add, hcast x, hcast y, hN]
    ring

/-- §6.1 Case B: all same-class differences sit at level `m`.
Then `q(A) ⊆ a + ({0} ∪ c·K)` for the `K` of nonzero difference digits
(`|K| ≤ 4`, `K ⊆ {1,…,6}`); `case61_dilate4_zero` gives `c` placing it in
a 5-interval, and a `Λ₀` shift makes `λ = λ₀·c` good on all of `A`. -/
theorem case61_caseB {m : ℕ} (hm : 0 < m) {A : Finset ℕ} (hcard : A.card ≤ 5)
    (hpos : ∀ d ∈ A, 0 < d)
    (hunit : ∀ d ∈ A, padicValNat 7 d = 0)
    {s : ZMod 7} (hs : s ≠ 0)
    (hcls : ∀ d ∈ A, runit7 d = s)
    (htop : ∀ x ∈ A, ∀ y ∈ A, x ≠ y →
      eMod7 m x y = 0 ∨ padicValNat 7 (eMod7 m x y) = m) :
    ∃ lam : ℕ, ¬ 7 ∣ lam ∧ good7 m lam A := by
  classical
  rcases A.eq_empty_or_nonempty with hAe | hAne
  · exact ⟨1, by norm_num, hAe ▸ good7_empty m 1⟩
  obtain ⟨b, hb⟩ := hAne
  set K := ((A.erase b).filter (fun d => eMod7 m d b ≠ 0)).image
    (fun d => qdig7 m (eMod7 m d b)) with hK
  have hKsub : K ⊆ ({1, 2, 3, 4, 5, 6} : Finset (ZMod 7)) := by
    intro q hq
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hq
    rw [Finset.mem_filter] at hd
    have htopd := (htop d (Finset.mem_of_mem_erase hd.1) b hb
      (Finset.ne_of_mem_erase hd.1)).resolve_left hd.2
    rw [qdig7_eq_runit7_of_top htopd]
    exact mem_nonzero_seven (runit7_ne_zero (Nat.pos_of_ne_zero hd.2))
  have hKcard : K.card ≤ 4 := by
    calc K.card ≤ ((A.erase b).filter _).card := Finset.card_image_le
      _ ≤ (A.erase b).card := Finset.card_filter_le _ _
      _ = A.card - 1 := Finset.card_erase_of_mem hb
      _ ≤ 4 := by omega
  obtain ⟨c, hc0, hcap⟩ := case61_dilate4_zero K hKsub hKcard
  have hcpos : 0 < c.val :=
    Nat.pos_of_ne_zero (by rwa [Ne, ZMod.val_eq_zero])
  have hc7 : ¬ 7 ∣ c.val := fun hdvd =>
    hc0 ((ZMod.val_eq_zero c).mp
      (Nat.eq_zero_of_dvd_of_lt hdvd (ZMod.val_lt c)))
  set a := qdig7 m (c.val * b) with ha
  have hsame_rel : ∀ d ∈ A, runit7 b ≠ 2 * runit7 d ∧
      runit7 d ≠ 2 * runit7 b := by
    intro d hd
    rw [hcls d hd, hcls b hb]
    exact ⟨fun h => hs (neg_eq_zero.mp (by linear_combination h)),
      fun h => hs (neg_eq_zero.mp (by linear_combination h))⟩
  have hmem : ∀ d ∈ A, qdig7 m (c.val * d) ∈
      (({0} : Finset (ZMod 7)) ∪ K.image (· * c)).image (· + a) := by
    intro d hd
    by_cases hdb : d = b
    · subst hdb
      refine Finset.mem_image.mpr ⟨0,
        Finset.mem_union_left _ (Finset.mem_singleton_self 0), ?_⟩
      show (0 : ZMod 7) + a = qdig7 m (c.val * d)
      rw [zero_add]
    by_cases he0 : eMod7 m d b = 0
    · have hdm : d % 7 ^ (m + 1) = b % 7 ^ (m + 1) := by
        have heq : eMod7 m d b =
            (d % 7 ^ (m + 1) + 7 ^ (m + 1) - b % 7 ^ (m + 1)) %
              7 ^ (m + 1) := by
          unfold eMod7
          obtain ⟨h1, h2⟩ := hsame_rel d hd
          rw [if_neg h1, if_neg h2]
        have hsub : d % 7 ^ (m + 1) + 7 ^ (m + 1) - b % 7 ^ (m + 1) =
            7 ^ (m + 1) := by
          have hbN : b % 7 ^ (m + 1) < 7 ^ (m + 1) :=
            Nat.mod_lt _ (Nat.pow_pos (by norm_num))
          have hdN : d % 7 ^ (m + 1) < 7 ^ (m + 1) :=
            Nat.mod_lt _ (Nat.pow_pos (by norm_num))
          have hdvd : 7 ^ (m + 1) ∣
              d % 7 ^ (m + 1) + 7 ^ (m + 1) - b % 7 ^ (m + 1) :=
            Nat.dvd_of_mod_eq_zero (heq ▸ he0)
          obtain ⟨k, hk⟩ := hdvd
          have hk1 : k = 1 := by
            have h1 : 0 < d % 7 ^ (m + 1) + 7 ^ (m + 1) -
                b % 7 ^ (m + 1) := by omega
            have h2 : d % 7 ^ (m + 1) + 7 ^ (m + 1) - b % 7 ^ (m + 1) <
                2 * 7 ^ (m + 1) := by omega
            rw [hk] at h1 h2
            rcases k with _ | _ | k
            · simp at h1
            · rfl
            · have : 7 ^ (m + 1) * (k + 1 + 1) ≥ 7 ^ (m + 1) * 2 := by
                apply Nat.mul_le_mul_left; omega
              omega
          rw [hk1, mul_one] at hk
          exact hk
        have hbN : b % 7 ^ (m + 1) < 7 ^ (m + 1) :=
          Nat.mod_lt _ (Nat.pow_pos (by norm_num))
        omega
      have hcd : (c.val * d) % 7 ^ (m + 1) = (c.val * b) % 7 ^ (m + 1) :=
        (Nat.ModEq.refl c.val).mul hdm
      refine Finset.mem_image.mpr ⟨0,
        Finset.mem_union_left _ (Finset.mem_singleton_self 0), ?_⟩
      show (0 : ZMod 7) + a = qdig7 m (c.val * d)
      rw [zero_add, ha]
      unfold qdig7
      rw [hcd]
    · have htopd := (htop d hd b hb hdb).resolve_left he0
      set kd := qdig7 m (eMod7 m d b) with hkd
      have hkdK : kd ∈ K :=
        Finset.mem_image.mpr ⟨d, Finset.mem_filter.mpr
          ⟨Finset.mem_erase.mpr ⟨hdb, hd⟩, he0⟩, hkd⟩
      have heeq : eMod7 m d b = kd.val * 7 ^ m := by
        have hlt : eMod7 m d b < 7 ^ (m + 1) := by
          unfold eMod7
          split_ifs <;> exact Nat.mod_lt _ (Nat.pow_pos (by norm_num))
        have := residN_top htopd
        rwa [Nat.mod_eq_of_lt hlt, ← hkd] at this
      have hcong : (c.val * d) % 7 ^ (m + 1) =
          (c.val * b % 7 ^ (m + 1) +
            (c.val * kd.val % 7) * 7 ^ m) % 7 ^ (m + 1) := by
        have hcastN : ∀ x : ℕ, ((x % 7 ^ (m + 1) : ℕ) :
            ZMod (7 ^ (m + 1))) = (x : ZMod _) :=
          fun x => (ZMod.natCast_eq_natCast_iff _ _ _).mpr
            (Nat.mod_mod x _)
        have heZ : ((eMod7 m d b : ℕ) : ZMod (7 ^ (m + 1))) =
            (d : ZMod _) - (b : ZMod _) := by
          rw [eMod7_zmod_cast']
          obtain ⟨h1, h2⟩ := hsame_rel d hd
          rw [if_neg h1, if_neg h2]
        have heZ2 : ((eMod7 m d b : ℕ) : ZMod (7 ^ (m + 1))) =
            ((kd.val * 7 ^ m : ℕ) : ZMod _) := by rw [heeq]
        have hsub : (d : ZMod (7 ^ (m + 1))) - (b : ZMod _) =
            ((kd.val * 7 ^ m : ℕ) : ZMod _) := heZ.symm.trans heZ2
        rw [sub_eq_iff_eq_add] at hsub
        have hck : ((c.val * kd.val * 7 ^ m : ℕ) : ZMod (7 ^ (m + 1))) =
            (((c.val * kd.val % 7) * 7 ^ m : ℕ) : ZMod _) := by
          have hsplit : 7 * (c.val * kd.val / 7) * 7 ^ m =
              7 ^ (m + 1) * (c.val * kd.val / 7) := by
            rw [pow_succ]; ring
          have h2 : (c.val * kd.val * 7 ^ m) % 7 ^ (m + 1) =
              (c.val * kd.val % 7 * 7 ^ m) % 7 ^ (m + 1) := by
            conv_lhs => rw [← Nat.mod_add_div (c.val * kd.val) 7]
            rw [add_mul, hsplit, Nat.add_mul_mod_self_left]
          exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr h2
        push_cast at hsub hck
        apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
        push_cast
        try rw [hcastN]
        push_cast
        linear_combination (c.val : ZMod (7 ^ (m + 1))) * hsub + hck
      have hqd := qdig7_add_top_resid hcong
      rw [← ha] at hqd
      have hcastk : (((c.val * kd.val % 7) : ℕ) : ZMod 7) = c * kd := by
        rw [ZMod.natCast_mod, Nat.cast_mul, ZMod.natCast_zmod_val,
          ZMod.natCast_zmod_val]
      rw [hcastk] at hqd
      refine Finset.mem_image.mpr ⟨c * kd,
        Finset.mem_union_right _ (Finset.mem_image.mpr
          ⟨kd, hkdK, mul_comm kd c⟩),
        ?_⟩
      show c * kd + a = qdig7 m (c.val * d)
      rw [hqd, add_comm]
  set A' := A.image (c.val * ·) with hA'
  have hA'q : A'.image (qdig7 m) ⊆
      (({0} : Finset (ZMod 7)) ∪ K.image (· * c)).image (· + a) := by
    intro q hq
    obtain ⟨d', hd', rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hd'
    exact hmem d hd
  have hap : apLen (A'.image (qdig7 m)) ≤ 5 :=
    le_trans (apLen_mono' hA'q) (by rw [apLen_image_add]; exact hcap)
  have hA'unit : ∀ d' ∈ A', padicValNat 7 d' = 0 := by
    intro d' hd'
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hd'
    rw [padicValNat_mul_unit7 (Nat.ne_of_gt hcpos)
      (Nat.ne_of_gt (hpos d hd)) hc7]
    exact hunit d hd
  have hcv0 : padicValNat 7 c.val = 0 := by
    by_contra h
    have h1 : (7 : ℕ) ^ 1 ∣ c.val := (Nat.pow_dvd_iff_le_padicValNat
      (by norm_num) (Nat.ne_of_gt hcpos)).mpr (Nat.pos_of_ne_zero h)
    rw [pow_one] at h1
    exact hc7 h1
  have hrun_c : runit7 c.val = c := by
    unfold runit7
    rw [hcv0, pow_zero, Nat.div_one, ZMod.natCast_zmod_val]
  have hA'cls : ∀ d' ∈ A', runit7 d' = c * s := by
    intro d' hd'
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hd'
    rw [runit7_mul, hrun_c, hcls d hd]
  have hcs : c * s ≠ 0 := mul_ne_zero hc0 hs
  obtain ⟨lam0, hlam0, hgood⟩ :=
    exists_lambda0_avoid hm hcs hA'unit hA'cls hap
  refine ⟨lam0 * c.val, ?_, ?_⟩
  · intro hdvd
    rcases (Nat.prime_seven.dvd_mul).mp hdvd with h | h
    · exact not_dvd_of_mem_multLow7_zero hm hlam0 h
    · exact hc7 h
  · intro d hd
    have := hgood (c.val * d) (Finset.mem_image.mpr ⟨d, hd, rfl⟩)
    rwa [← mul_assoc] at this


/-! ### §6 dispatcher: class decomposition + argmax + rotation -/

/-- Filters by distinct residue labels are disjoint. -/
theorem case5m_disj {A : Finset ℕ} {r1 r2 : ZMod 7} (h : r1 ≠ r2) :
    Disjoint (A.filter (fun d => runit7 d = r1))
      (A.filter (fun d => runit7 d = r2)) := by
  rw [Finset.disjoint_left]
  intro d hd hd2
  rw [Finset.mem_filter] at hd hd2
  exact h (hd.2 ▸ hd2.2)

/-- For `s ∈ {1,2,4}`, `2s` and `4s` lie in `{1,2,4}` and `s,2s,4s` are
pairwise distinct. -/
theorem case5m_labels {s : ZMod 7}
    (hs : s ∈ ({1, 2, 4} : Finset (ZMod 7))) :
    2 * s ∈ ({1, 2, 4} : Finset (ZMod 7)) ∧
      4 * s ∈ ({1, 2, 4} : Finset (ZMod 7)) ∧
      s ≠ 2 * s ∧ s ≠ 4 * s ∧ 2 * s ≠ 4 * s := by
  fin_cases hs <;> refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- The rotated partition covers `A` (left-associated union). -/
theorem case5m_classes_rot {A : Finset ℕ} {s : ZMod 7}
    (hs : s ∈ ({1, 2, 4} : Finset (ZMod 7)))
    (hcls : ∀ d ∈ A, runit7 d ∈ ({1, 2, 4} : Finset (ZMod 7))) :
    A.filter (fun d => runit7 d = s) ∪
        A.filter (fun d => runit7 d = 2 * s) ∪
          A.filter (fun d => runit7 d = 4 * s) = A := by
  ext d
  simp only [Finset.mem_union, Finset.mem_filter]
  constructor
  · rintro ((⟨hd, _⟩ | ⟨hd, _⟩) | ⟨hd, _⟩) <;> exact hd
  · intro hd
    have h := hcls d hd
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with h' | h' | h' <;>
      fin_cases hs <;>
        first
          | (exact Or.inl (Or.inl ⟨hd, h'.trans (by decide)⟩))
          | (exact Or.inl (Or.inr ⟨hd, h'.trans (by decide)⟩))
          | (exact Or.inr ⟨hd, h'.trans (by decide)⟩)

/-- Cardinality sum under the `s`-labeling. -/
theorem case5m_card_sum_rot {A : Finset ℕ} {s : ZMod 7}
    (hs : s ∈ ({1, 2, 4} : Finset (ZMod 7)))
    (hcls : ∀ d ∈ A, runit7 d ∈ ({1, 2, 4} : Finset (ZMod 7))) :
    (A.filter (fun d => runit7 d = s)).card +
      ((A.filter (fun d => runit7 d = 2 * s)).card +
        (A.filter (fun d => runit7 d = 4 * s)).card) = A.card := by
  obtain ⟨-, -, h1, h2, h3⟩ := case5m_labels hs
  have hdj' : Disjoint (A.filter (fun d => runit7 d = s) ∪
      A.filter (fun d => runit7 d = 2 * s))
      (A.filter (fun d => runit7 d = 4 * s)) :=
    Finset.disjoint_union_left.mpr ⟨case5m_disj h2, case5m_disj h3⟩
  rw [← Nat.add_assoc,
    ← Finset.card_union_of_disjoint (case5m_disj h1),
    ← Finset.card_union_of_disjoint hdj',
    case5m_classes_rot hs hcls]

set_option maxHeartbeats 800000 in
/-- **`lrc7_case5m` dispatcher**: most-popular class + rotation +
`case61`–`case66` (supplied as hypotheses). -/
theorem case5m_dispatch {m : ℕ} (_hm : 2 ≤ m) {A : Finset ℕ}
    (hcard : A.card = 5)
    (hpos : ∀ d ∈ A, 0 < d) (hunit : ∀ d ∈ A, padicValNat 7 d = 0)
    (hcls : ∀ d ∈ A, runit7 d ∈ ({1, 2, 4} : Finset (ZMod 7)))
    (hc61 : ∀ {X : Finset ℕ}, X.card = 5 → (∀ d ∈ X, 0 < d) →
      (∀ d ∈ X, padicValNat 7 d = 0) →
      ∀ {s : ZMod 7}, s ∈ ({1, 2, 4} : Finset (ZMod 7)) →
      (∀ d ∈ X, runit7 d = s) →
      ∃ lam : ℕ, ¬ 7 ∣ lam ∧ good7 m lam X)
    (hc62 : ∀ {A1 Ar : Finset ℕ}, A1.card = 4 → Ar.card = 1 →
      (∀ d ∈ A1 ∪ Ar, 0 < d) →
      (∀ d ∈ A1 ∪ Ar, padicValNat 7 d = 0) →
      ∀ {s : ZMod 7}, s ∈ ({1, 2, 4} : Finset (ZMod 7)) →
      (∀ d ∈ A1, runit7 d = s) →
      (∀ d ∈ Ar, runit7 d ∈ ({2 * s, 4 * s} : Finset (ZMod 7))) →
      ∃ lam : ℕ, ¬ 7 ∣ lam ∧ good7 m lam (A1 ∪ Ar))
    (hc63 : ∀ {A1 A2 A4 : Finset ℕ}, A1.card = 3 → A2.card = 1 →
      A4.card = 1 → (∀ d ∈ A1 ∪ A2 ∪ A4, 0 < d) →
      (∀ d ∈ A1 ∪ A2 ∪ A4, padicValNat 7 d = 0) →
      ∀ {s : ZMod 7}, s ∈ ({1, 2, 4} : Finset (ZMod 7)) →
      (∀ d ∈ A1, runit7 d = s) → (∀ d ∈ A2, runit7 d = 2 * s) →
      (∀ d ∈ A4, runit7 d = 4 * s) →
      ∃ lam : ℕ, ¬ 7 ∣ lam ∧ good7 m lam (A1 ∪ A2 ∪ A4))
    (hc64 : ∀ {A1 A2 : Finset ℕ}, A1.card = 3 → A2.card = 2 →
      (∀ d ∈ A1 ∪ A2, 0 < d) →
      (∀ d ∈ A1 ∪ A2, padicValNat 7 d = 0) →
      ∀ {s : ZMod 7}, s ∈ ({1, 2, 4} : Finset (ZMod 7)) →
      (∀ d ∈ A1, runit7 d = s) → (∀ d ∈ A2, runit7 d = 2 * s) →
      ∃ lam : ℕ, ¬ 7 ∣ lam ∧ good7 m lam (A1 ∪ A2))
    (hc65 : ∀ {A1 A4 : Finset ℕ}, A1.card = 3 → A4.card = 2 →
      (∀ d ∈ A1 ∪ A4, 0 < d) →
      (∀ d ∈ A1 ∪ A4, padicValNat 7 d = 0) →
      ∀ {s : ZMod 7}, s ∈ ({1, 2, 4} : Finset (ZMod 7)) →
      (∀ d ∈ A1, runit7 d = s) → (∀ d ∈ A4, runit7 d = 4 * s) →
      ∃ lam : ℕ, ¬ 7 ∣ lam ∧ good7 m lam (A1 ∪ A4))
    (hc66 : ∀ {A1 A2 A4 : Finset ℕ}, A1.card = 2 → A2.card = 2 →
      A4.card = 1 → (∀ d ∈ A1 ∪ A2 ∪ A4, 0 < d) →
      (∀ d ∈ A1 ∪ A2 ∪ A4, padicValNat 7 d = 0) →
      ∀ {s : ZMod 7}, s ∈ ({1, 2, 4} : Finset (ZMod 7)) →
      (∀ d ∈ A1, runit7 d = s) → (∀ d ∈ A2, runit7 d = 2 * s) →
      (∀ d ∈ A4, runit7 d = 4 * s) →
      ∃ lam : ℕ, ¬ 7 ∣ lam ∧ good7 m lam (A1 ∪ A2 ∪ A4)) :
    ∃ lam : ℕ, ¬ 7 ∣ lam ∧ good7 m lam A := by
  classical
  obtain ⟨s, hs, hmax⟩ : ∃ s ∈ ({1, 2, 4} : Finset (ZMod 7)),
      ∀ t ∈ ({1, 2, 4} : Finset (ZMod 7)),
        (A.filter (fun d => runit7 d = t)).card ≤
          (A.filter (fun d => runit7 d = s)).card := by
    by_cases h1 : (A.filter (fun d => runit7 d = 2)).card ≤
        (A.filter (fun d => runit7 d = 1)).card ∧
        (A.filter (fun d => runit7 d = 4)).card ≤
          (A.filter (fun d => runit7 d = 1)).card
    · exact ⟨1, by decide, fun t ht => by
          fin_cases ht <;> first | exact h1.1 | exact h1.2 | exact le_rfl⟩
    · by_cases h2 : (A.filter (fun d => runit7 d = 4)).card ≤
          (A.filter (fun d => runit7 d = 2)).card ∧
          (A.filter (fun d => runit7 d = 1)).card ≤
            (A.filter (fun d => runit7 d = 2)).card
      · exact ⟨2, by decide, fun t ht => by
          fin_cases ht <;> first | exact h2.2 | exact h2.1 | exact le_rfl⟩
      · push Not at h1 h2
        refine ⟨4, by decide, ?_⟩
        intro t ht
        fin_cases ht <;> omega
  obtain ⟨h2s, h4s, h12, h14, h24⟩ := case5m_labels hs
  set A1 := A.filter (fun d => runit7 d = s) with hA1
  set A2 := A.filter (fun d => runit7 d = 2 * s) with hA2
  set A4 := A.filter (fun d => runit7 d = 4 * s) with hA4
  have hsum : A1.card + (A2.card + A4.card) = 5 := by
    have := case5m_card_sum_rot hs hcls
    rwa [hcard] at this
  have hA1max2 : A2.card ≤ A1.card := hmax _ h2s
  have hA1max4 : A4.card ≤ A1.card := hmax _ h4s
  have hA1ge : 2 ≤ A1.card := by
    by_contra hlt
    push Not at hlt
    interval_cases h : A1.card <;> omega
  have hmem1 : ∀ d ∈ A1, runit7 d = s :=
    fun d hd => (Finset.mem_filter.mp hd).2
  have hmem2 : ∀ d ∈ A2, runit7 d = 2 * s :=
    fun d hd => (Finset.mem_filter.mp hd).2
  have hmem4 : ∀ d ∈ A4, runit7 d = 4 * s :=
    fun d hd => (Finset.mem_filter.mp hd).2
  have hunion : A1 ∪ A2 ∪ A4 = A := case5m_classes_rot hs hcls
  have hposU : ∀ d ∈ A1 ∪ A2 ∪ A4, 0 < d := fun d hd =>
    hpos d (hunion ▸ hd)
  have hunitU : ∀ d ∈ A1 ∪ A2 ∪ A4, padicValNat 7 d = 0 := fun d hd =>
    hunit d (hunion ▸ hd)
  have hA1le : A1.card ≤ 5 := by omega
  interval_cases hcA1 : A1.card
  · -- |A₁| = 2: residuals (2,1)→66 or (1,2)→66 via s ↦ 4s rotation
    by_cases hcA2 : A2.card = 2
    · have hcA4 : A4.card = 1 := by omega
      obtain ⟨lam, hlam, hgood⟩ :=
        hc66 hcA1 hcA2 hcA4 hposU hunitU hs hmem1 hmem2 hmem4
      exact ⟨lam, hlam, hunion ▸ hgood⟩
    · have hcA2 : A2.card = 1 := by omega
      have hcA4 : A4.card = 2 := by omega
      have h8 : (2 : ZMod 7) * (4 * s) = s := by
        have h8' : (8 : ZMod 7) = 1 := by decide
        calc (2 : ZMod 7) * (4 * s) = 8 * s := by ring
          _ = 1 * s := by rw [h8']
          _ = s := one_mul s
      have h16 : (4 : ZMod 7) * (4 * s) = 2 * s := by
        have h16' : (16 : ZMod 7) = 2 := by decide
        calc (4 : ZMod 7) * (4 * s) = 16 * s := by ring
          _ = 2 * s := by rw [h16']
      have hunion' : A4 ∪ A1 ∪ A2 = A := by
        ext d; simp only [Finset.mem_union]
        rw [← hunion]; simp only [Finset.mem_union]; tauto
      obtain ⟨lam, hlam, hgood⟩ := hc66 hcA4 hcA1 hcA2
        (fun d hd => hpos d (hunion' ▸ hd))
        (fun d hd => hunit d (hunion' ▸ hd))
        h4s hmem4
        (fun d hd => by rw [h8]; exact hmem1 d hd)
        (fun d hd => by rw [h16]; exact hmem2 d hd)
      exact ⟨lam, hlam, hunion' ▸ hgood⟩
  · -- |A₁| = 3: (1,1)→63, (2,0)→64, (0,2)→65
    by_cases hcA2 : A2.card = 1
    · have hcA4 : A4.card = 1 := by omega
      obtain ⟨lam, hlam, hgood⟩ :=
        hc63 hcA1 hcA2 hcA4 hposU hunitU hs hmem1 hmem2 hmem4
      exact ⟨lam, hlam, hunion ▸ hgood⟩
    · by_cases hcA4 : A4.card = 2
      · have hcA2 : A2.card = 0 := by omega
        have hA2e : A2 = ∅ := Finset.card_eq_zero.mp hcA2
        have hunion' : A1 ∪ A4 = A := by
          rw [← hunion, hA2e, Finset.union_empty]
        obtain ⟨lam, hlam, hgood⟩ := hc65 hcA1 hcA4
          (fun d hd => hpos d (hunion' ▸ hd))
          (fun d hd => hunit d (hunion' ▸ hd))
          hs hmem1 hmem4
        exact ⟨lam, hlam, hunion' ▸ hgood⟩
      · have hcA2 : A2.card = 2 := by omega
        have hcA4' : A4.card = 0 := by omega
        have hA4e : A4 = ∅ := Finset.card_eq_zero.mp hcA4'
        have hunion' : A1 ∪ A2 = A := by
          rw [← hunion, hA4e, Finset.union_empty]
        obtain ⟨lam, hlam, hgood⟩ := hc64 hcA1 hcA2
          (fun d hd => hpos d (hunion' ▸ hd))
          (fun d hd => hunit d (hunion' ▸ hd))
          hs hmem1 hmem2
        exact ⟨lam, hlam, hunion' ▸ hgood⟩
  · -- |A₁| = 4: case62 with Ar = A2 ∪ A4 (total card 1)
    have hdj24 : Disjoint A2 A4 := case5m_disj h24
    have hAr : (A2 ∪ A4).card = 1 := by
      rw [Finset.card_union_of_disjoint hdj24]
      omega
    have hArmem : ∀ d ∈ A2 ∪ A4,
        runit7 d ∈ ({2 * s, 4 * s} : Finset (ZMod 7)) := by
      intro d hd
      rw [Finset.mem_union] at hd
      rcases hd with h | h
      · exact Finset.mem_insert.mpr (Or.inl (hmem2 d h))
      · exact Finset.mem_insert.mpr
          (Or.inr (Finset.mem_singleton.mpr (hmem4 d h)))
    have hunion' : A1 ∪ (A2 ∪ A4) = A := by
      rw [← hunion, Finset.union_assoc]
    obtain ⟨lam, hlam, hgood⟩ := hc62 hcA1 hAr
      (fun d hd => hpos d (hunion' ▸ hd))
      (fun d hd => hunit d (hunion' ▸ hd))
      hs hmem1 hArmem
    exact ⟨lam, hlam, hunion' ▸ hgood⟩
  · -- |A₁| = 5: case61 (A1 = A)
    have hA1eq : A1 = A :=
      Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
        (le_of_eq (hcard.trans hcA1.symm))
    obtain ⟨lam, hlam, hgood⟩ := hc61 hcA1
      (fun d hd => hpos d (hA1eq ▸ hd))
      (fun d hd => hunit d (hA1eq ▸ hd))
      hs hmem1
    exact ⟨lam, hlam, hA1eq ▸ hgood⟩
/-- **`lrc7_case5m`** (parameterized on the six case theorems): the
`good7` conclusion of the dispatch converts to `absModN ≥ 7^m` on
`A ∪ {d6}`, `M = 7^{m+1}`. -/
theorem lrc7_case5m_of_cases {m : ℕ} (hm : 2 ≤ m) {A : Finset ℕ}
    (hcard : A.card = 5)
    (hpos : ∀ d ∈ A, 0 < d) (hunit : ∀ d ∈ A, padicValNat 7 d = 0)
    (hcls : ∀ d ∈ A, runit7 d ∈ ({1, 2, 4} : Finset (ZMod 7)))
    (hc61 : ∀ {X : Finset ℕ}, X.card = 5 → (∀ d ∈ X, 0 < d) →
      (∀ d ∈ X, padicValNat 7 d = 0) →
      ∀ {s : ZMod 7}, s ∈ ({1, 2, 4} : Finset (ZMod 7)) →
      (∀ d ∈ X, runit7 d = s) →
      ∃ lam : ℕ, ¬ 7 ∣ lam ∧ good7 m lam X)
    (hc62 : ∀ {A1 Ar : Finset ℕ}, A1.card = 4 → Ar.card = 1 →
      (∀ d ∈ A1 ∪ Ar, 0 < d) →
      (∀ d ∈ A1 ∪ Ar, padicValNat 7 d = 0) →
      ∀ {s : ZMod 7}, s ∈ ({1, 2, 4} : Finset (ZMod 7)) →
      (∀ d ∈ A1, runit7 d = s) →
      (∀ d ∈ Ar, runit7 d ∈ ({2 * s, 4 * s} : Finset (ZMod 7))) →
      ∃ lam : ℕ, ¬ 7 ∣ lam ∧ good7 m lam (A1 ∪ Ar))
    (hc63 : ∀ {A1 A2 A4 : Finset ℕ}, A1.card = 3 → A2.card = 1 →
      A4.card = 1 → (∀ d ∈ A1 ∪ A2 ∪ A4, 0 < d) →
      (∀ d ∈ A1 ∪ A2 ∪ A4, padicValNat 7 d = 0) →
      ∀ {s : ZMod 7}, s ∈ ({1, 2, 4} : Finset (ZMod 7)) →
      (∀ d ∈ A1, runit7 d = s) → (∀ d ∈ A2, runit7 d = 2 * s) →
      (∀ d ∈ A4, runit7 d = 4 * s) →
      ∃ lam : ℕ, ¬ 7 ∣ lam ∧ good7 m lam (A1 ∪ A2 ∪ A4))
    (hc64 : ∀ {A1 A2 : Finset ℕ}, A1.card = 3 → A2.card = 2 →
      (∀ d ∈ A1 ∪ A2, 0 < d) →
      (∀ d ∈ A1 ∪ A2, padicValNat 7 d = 0) →
      ∀ {s : ZMod 7}, s ∈ ({1, 2, 4} : Finset (ZMod 7)) →
      (∀ d ∈ A1, runit7 d = s) → (∀ d ∈ A2, runit7 d = 2 * s) →
      ∃ lam : ℕ, ¬ 7 ∣ lam ∧ good7 m lam (A1 ∪ A2))
    (hc65 : ∀ {A1 A4 : Finset ℕ}, A1.card = 3 → A4.card = 2 →
      (∀ d ∈ A1 ∪ A4, 0 < d) →
      (∀ d ∈ A1 ∪ A4, padicValNat 7 d = 0) →
      ∀ {s : ZMod 7}, s ∈ ({1, 2, 4} : Finset (ZMod 7)) →
      (∀ d ∈ A1, runit7 d = s) → (∀ d ∈ A4, runit7 d = 4 * s) →
      ∃ lam : ℕ, ¬ 7 ∣ lam ∧ good7 m lam (A1 ∪ A4))
    (hc66 : ∀ {A1 A2 A4 : Finset ℕ}, A1.card = 2 → A2.card = 2 →
      A4.card = 1 → (∀ d ∈ A1 ∪ A2 ∪ A4, 0 < d) →
      (∀ d ∈ A1 ∪ A2 ∪ A4, padicValNat 7 d = 0) →
      ∀ {s : ZMod 7}, s ∈ ({1, 2, 4} : Finset (ZMod 7)) →
      (∀ d ∈ A1, runit7 d = s) → (∀ d ∈ A2, runit7 d = 2 * s) →
      (∀ d ∈ A4, runit7 d = 4 * s) →
      ∃ lam : ℕ, ¬ 7 ∣ lam ∧ good7 m lam (A1 ∪ A2 ∪ A4))
    (d6 : ℕ) (hd6 : padicValNat 7 d6 = m) (hd6pos : 0 < d6) :
    ∃ lam : ℕ, 0 < lam ∧ ¬ 7 ∣ lam ∧
      ∀ d ∈ A ∪ {d6}, 7 ^ m ≤ absModN (lam * d) (7 ^ (m + 1)) := by
  obtain ⟨lam, hlamnd, hgood⟩ :=
    case5m_dispatch hm hcard hpos hunit hcls hc61 hc62 hc63 hc64 hc65 hc66
  have hlampos : 0 < lam := Nat.pos_of_ne_zero (fun h => hlamnd (h ▸ dvd_zero 7))
  refine ⟨lam, hlampos, hlamnd, fun d hd => ?_⟩
  rw [Finset.mem_union, Finset.mem_singleton] at hd
  rcases hd with hd | rfl
  · rw [absModN_ge_iff_qdig7 (by rw [hunit d hd]; omega) (hpos d hd) hlamnd]
    exact val_bounds_of_not_bad06 (hgood d hd)
  · exact absModN_top_ge7 hd6 hd6pos hlamnd


/-- **`hc6` adapter** parameterized on the six case theorems: feeds
`lrc7_case5m_of_cases` into `lrc7_hc6_of`, dropping the `¬ 7 ∣ lam`
conjunct to match the `IntCase` `hc6` signature. -/
theorem lrc7_hc6_aux {m : ℕ}
    (hc61 : ∀ {X : Finset ℕ}, X.card = 5 → (∀ d ∈ X, 0 < d) →
      (∀ d ∈ X, padicValNat 7 d = 0) →
      ∀ {s : ZMod 7}, s ∈ ({1, 2, 4} : Finset (ZMod 7)) →
      (∀ d ∈ X, runit7 d = s) →
      ∃ lam : ℕ, ¬ 7 ∣ lam ∧ good7 m lam X)
    (hc62 : ∀ {A1 Ar : Finset ℕ}, A1.card = 4 → Ar.card = 1 →
      (∀ d ∈ A1 ∪ Ar, 0 < d) →
      (∀ d ∈ A1 ∪ Ar, padicValNat 7 d = 0) →
      ∀ {s : ZMod 7}, s ∈ ({1, 2, 4} : Finset (ZMod 7)) →
      (∀ d ∈ A1, runit7 d = s) →
      (∀ d ∈ Ar, runit7 d ∈ ({2 * s, 4 * s} : Finset (ZMod 7))) →
      ∃ lam : ℕ, ¬ 7 ∣ lam ∧ good7 m lam (A1 ∪ Ar))
    (hc63 : ∀ {A1 A2 A4 : Finset ℕ}, A1.card = 3 → A2.card = 1 →
      A4.card = 1 → (∀ d ∈ A1 ∪ A2 ∪ A4, 0 < d) →
      (∀ d ∈ A1 ∪ A2 ∪ A4, padicValNat 7 d = 0) →
      ∀ {s : ZMod 7}, s ∈ ({1, 2, 4} : Finset (ZMod 7)) →
      (∀ d ∈ A1, runit7 d = s) → (∀ d ∈ A2, runit7 d = 2 * s) →
      (∀ d ∈ A4, runit7 d = 4 * s) →
      ∃ lam : ℕ, ¬ 7 ∣ lam ∧ good7 m lam (A1 ∪ A2 ∪ A4))
    (hc64 : ∀ {A1 A2 : Finset ℕ}, A1.card = 3 → A2.card = 2 →
      (∀ d ∈ A1 ∪ A2, 0 < d) →
      (∀ d ∈ A1 ∪ A2, padicValNat 7 d = 0) →
      ∀ {s : ZMod 7}, s ∈ ({1, 2, 4} : Finset (ZMod 7)) →
      (∀ d ∈ A1, runit7 d = s) → (∀ d ∈ A2, runit7 d = 2 * s) →
      ∃ lam : ℕ, ¬ 7 ∣ lam ∧ good7 m lam (A1 ∪ A2))
    (hc65 : ∀ {A1 A4 : Finset ℕ}, A1.card = 3 → A4.card = 2 →
      (∀ d ∈ A1 ∪ A4, 0 < d) →
      (∀ d ∈ A1 ∪ A4, padicValNat 7 d = 0) →
      ∀ {s : ZMod 7}, s ∈ ({1, 2, 4} : Finset (ZMod 7)) →
      (∀ d ∈ A1, runit7 d = s) → (∀ d ∈ A4, runit7 d = 4 * s) →
      ∃ lam : ℕ, ¬ 7 ∣ lam ∧ good7 m lam (A1 ∪ A4))
    (hc66 : ∀ {A1 A2 A4 : Finset ℕ}, A1.card = 2 → A2.card = 2 →
      A4.card = 1 → (∀ d ∈ A1 ∪ A2 ∪ A4, 0 < d) →
      (∀ d ∈ A1 ∪ A2 ∪ A4, padicValNat 7 d = 0) →
      ∀ {s : ZMod 7}, s ∈ ({1, 2, 4} : Finset (ZMod 7)) →
      (∀ d ∈ A1, runit7 d = s) → (∀ d ∈ A2, runit7 d = 2 * s) →
      (∀ d ∈ A4, runit7 d = 4 * s) →
      ∃ lam : ℕ, ¬ 7 ∣ lam ∧ good7 m lam (A1 ∪ A2 ∪ A4))
    (A : Finset ℕ) (hA : A.card = 5)
    (hpos : ∀ d ∈ A, 0 < d) (hnd : ∀ d ∈ A, ¬ 7 ∣ d)
    (d6 : ℕ) (hd6 : padicValNat 7 d6 = m) (hd6pos : 0 < d6)
    (hm : 1 < m) :
    ∃ lam : ℕ, 0 < lam ∧
      ∀ d ∈ A ∪ {d6}, 7 ^ m ≤ absModN (lam * d) (7 ^ (m + 1)) := by
  obtain ⟨lam, hlp, _hlnd, hb⟩ := lrc7_hc6_of hm
    (fun {X} hX hXp hXu hXc dd6 hd6' hd6pos' =>
      lrc7_case5m_of_cases hm hX hXp hXu hXc
        hc61 hc62 hc63 hc64 hc65 hc66 dd6 hd6' hd6pos')
    A hA hpos hnd d6 hd6 hd6pos
  exact ⟨lam, hlp, hb⟩


/-- **Reusable finisher**: if a unit-scaled copy `λ'·A` of a single-class
set has `apLen ≤ 5`, a `Λ₀`-shift `λ₀` puts it off `{0,6}` — so
`λ = λ₀·λ'` is a `good7` multiplier for `A`.  Used by `case61`–`case65`
endgames (each scales, bounds `apLen`, then finishes here). -/
theorem good7_of_smul_apLen {m : ℕ} (hm : 0 < m) {A : Finset ℕ}
    (hpos : ∀ d ∈ A, 0 < d) (hunit : ∀ d ∈ A, padicValNat 7 d = 0)
    {s : ZMod 7} (hs : s ≠ 0) (hsame : ∀ d ∈ A, runit7 d = s)
    {lam' : ℕ} (hlam' : ¬ 7 ∣ lam')
    (h : apLen ((A.image (fun d => lam' * d)).image (qdig7 m)) ≤ 5) :
    ∃ lam : ℕ, ¬ 7 ∣ lam ∧ good7 m lam A := by
  classical
  set B := A.image (fun d => lam' * d) with hB
  have hlam'0 : lam' ≠ 0 := fun hh => hlam' (hh ▸ dvd_zero 7)
  set s' := runit7 lam' * s with hs'def
  have hs'0 : s' ≠ 0 := by
    rw [hs'def]
    exact mul_ne_zero (runit7_ne_zero (Nat.pos_of_ne_zero hlam'0)) hs
  have hunitB : ∀ d' ∈ B, padicValNat 7 d' = 0 := by
    intro d' hd'
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hd'
    rw [padicValNat_mul_unit7 hlam'0 (Nat.ne_of_gt (hpos d hd)) hlam',
      hunit d hd]
  have hsameB : ∀ d' ∈ B, runit7 d' = s' := by
    intro d' hd'
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hd'
    rw [hs'def, runit7_mul, hsame d hd]
  obtain ⟨lam0, hlam0mem, hgoodB⟩ :=
    exists_lambda0_avoid hm hs'0 hunitB hsameB h
  have hlam0nd : ¬ 7 ∣ lam0 := not_dvd_of_mem_multLow7_zero hm hlam0mem
  refine ⟨lam0 * lam',
    Nat.Prime.not_dvd_mul Nat.prime_seven hlam0nd hlam', ?_⟩
  intro d hd
  have hdB : lam' * d ∈ B := Finset.mem_image.mpr ⟨d, hd, rfl⟩
  have hgood := hgoodB _ hdB
  rwa [mul_assoc]

/-- §6 shared: a `≤2`-AP digit set on a single-class unit set can be
Λ₀-shifted to land inside `{0,6}` (paper's "by (7) we may assume
q(B) ⊂ {0,6}").  Pair-difference digits are unaffected by Λ₀ (their
`eMod7` has level ≥ 1, so `λ_k·e ≡ e`), hence preserved — the caller
supplies whatever pair conditions it needs separately. -/
theorem exists_lambda0_qdig_06 {m : ℕ} {B : Finset ℕ}
    (hunit : ∀ d ∈ B, padicValNat 7 d = 0) {s : ZMod 7} (hs : s ≠ 0)
    (hcls : ∀ d ∈ B, runit7 d = s)
    (hap : apLen (B.image (qdig7 m)) ≤ 2) :
    ∃ lam ∈ multLow7 m 0,
      ∀ d ∈ B, qdig7 m (lam * d) ∈ ({0, 6} : Finset (ZMod 7)) := by
  classical
  set X := B.image (qdig7 m)
  obtain ⟨i, hi⟩ := (apLen_le_iff X 2 (by norm_num)).mp hap
  set t : ZMod 7 := 6 - i with ht
  set K : ZMod 7 := t * s⁻¹ with hK
  have hKs : K * s = t := by
    rw [hK, mul_assoc, inv_mul_cancel₀ hs, mul_one]
  refine ⟨1 + K.val * 7 ^ m, mem_multLow7_zero (ZMod.val_lt K), ?_⟩
  intro d hd
  have hqd : qdig7 m d ∈ X := Finset.mem_image.mpr ⟨d, hd, rfl⟩
  have hmem := hi hqd
  simp only [cycIv, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
  -- hmem : (qdig7 m d - i).val < 2  →  qdig7 m d - i ∈ {0,1}
  have hdi : qdig7 m d - i = 0 ∨ qdig7 m d - i = 1 := by
    have hcv : ((qdig7 m d - i).val : ZMod 7) = qdig7 m d - i :=
      ZMod.natCast_zmod_val _
    have hv2 : (qdig7 m d - i).val = 0 ∨ (qdig7 m d - i).val = 1 := by omega
    rcases hv2 with h0 | h1
    · left; rw [← hcv, h0]; exact Nat.cast_zero
    · right; rw [← hcv, h1]; exact Nat.cast_one
  have hsh : qdig7 m d + t ∈ ({0, 6} : Finset (ZMod 7)) := by
    rcases hdi with h0 | h0
    · have h1 : qdig7 m d = i := sub_eq_zero.mp h0
      have ht6 : i + (6 - i) = (6 : ZMod 7) := by ring
      rw [h1, ht]; exact Finset.mem_insert.mpr (Or.inr
        (Finset.mem_singleton.mpr ht6))
    · have h1 : qdig7 m d = i + 1 := by
        rw [sub_eq_iff_eq_add] at h0; rw [h0, add_comm]
      have ht0 : i + 1 + (6 - i) = (0 : ZMod 7) := by
        calc i + 1 + (6 - i) = (7 : ZMod 7) := by ring
          _ = 0 := by decide
      rw [h1, ht]; exact Finset.mem_insert.mpr (Or.inl ht0)
  have hsh' : qdig7 m ((1 + K.val * 7 ^ m) * d) = qdig7 m d + t := by
    rw [qdig7_lambda0 (m := m) (d := d) (k := K.val) (hunit d hd),
      ZMod.natCast_zmod_val K, hcls d hd, hKs]
  rwa [hsh']

/-- §6 shared finite fact: `{0,6,p,q}` has `apLen ≤ 5` unless
`{p,q} = {2,4}` (the unique bad configuration, where it is `6`). -/
theorem apLen_06_pair {p q : ZMod 7}
    (h : ({p, q} : Finset (ZMod 7)) ≠ {2, 4}) :
    apLen ({0, 6, p, q} : Finset (ZMod 7)) ≤ 5 := by
  revert h p q
  decide
