# lrc7_case4 — |A_s| = 3 block (verified, memwatch c4s3_4.csv exit=0)

File: `_dev/scratch/Case4MainS3.lean` lines 168–402 (bullet 2 of `interval_cases hSc : S.card`, i.e. `S.card = 3`).
Plus helper lemmas `s3_*` at lines 5–25 (added above the theorem).

```lean
    · -- <<S3-TARGET>> |A_s| = 3: S.card = 3, one extra in U \ S (classes 2/4).
      by_cases h4 : ∃ j ∈ Finset.Icc 1 5, ∃ i : ZMod 7, X j ⊆ cycIv i 4
      · -- eq. (11) holds: both shifts `t ∈ {1−i, 2−i}` keep `X j` off `{0,6}`,
        -- and `pair_point_avoid` picks one rescuing the extra unit `e`.
        obtain ⟨j, hj, i, hi⟩ := h4
        rw [Finset.mem_Icc] at hj
        have hSU : S ⊆ U := Finset.filter_subset _ _
        have hcard1 : (U \ S).card = 1 := by
          rw [Finset.card_sdiff_of_subset hSU, hUcard, hSc]
        obtain ⟨e, he⟩ := Finset.card_eq_one.mp hcard1
        have hemem : e ∈ U \ S := by
          rw [he]; exact Finset.mem_singleton_self e
        have heU : e ∈ U := (Finset.mem_sdiff.mp hemem).1
        have heS : e ∉ S := (Finset.mem_sdiff.mp hemem).2
        obtain ⟨c, hc124, hce⟩ := class_decomp (hr124 e heU) hs124
        have hc24 : c ∈ ({2, 4} : Finset (ZMod 7)) := by
          have hc1 : c ≠ 1 := by
            intro h1
            apply heS
            rw [hS]
            exact Finset.mem_filter.mpr ⟨heU, by rw [hce, h1, one_mul]⟩
          rcases Finset.mem_insert.mp hc124 with h | h
          · exact absurd h hc1
          rcases Finset.mem_insert.mp h with h | h
          · rw [h]; decide
          · rw [Finset.mem_singleton.mp h]; decide
        obtain ⟨t, ht, htgood⟩ := pair_point_avoid
          (z := qdig7 m (lamP m i₀ j u' * normU7 (7 ^ (m + 1)) e))
          (c := c) (i := i) hc24
        apply case4_finish hm him hj hu'nd hs0 t D hpos hle
        · intro d hdD hdν
          have hdU : d ∈ U := by
            have hdL : d ∈ level7 D 0 := Finset.mem_filter.mpr ⟨hdD, hdν⟩
            rwa [hU] at hdL
          by_cases hdS : d ∈ S
          · have hrd : runit7 (normU7 (7 ^ (m + 1)) d) = s := by
              rw [hS] at hdS
              exact (Finset.mem_filter.mp hdS).2
            rw [hrd, mul_assoc, inv_mul_cancel₀ hs0, mul_one]
            have hqd : qdig7 m (lamP m i₀ j u' * normU7 N d) ∈ X j := by
              rw [hXj j]
              exact Finset.mem_image.mpr ⟨d, hdS, rfl⟩
            have hshift : qdig7 m (lamP m i₀ j u' * normU7 N d) + t ∈
                cycIv (i + t) 4 := (mem_cycIv_add (a := t)).mp (hi hqd)
            have hi2 : i + t ∈ ({1, 2} : Finset (ZMod 7)) := by
              rcases Finset.mem_insert.mp ht with h | h
              · rw [h]
                have h1i : i + (1 - i) = (1 : ZMod 7) := by ring
                rw [h1i]
                exact Finset.mem_insert_self _ _
              · rw [Finset.mem_singleton.mp h]
                have h2i : i + (2 - i) = (2 : ZMod 7) := by ring
                rw [h2i]
                exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
            simpa [bad06] using avoids06_cycIv_4 hi2 _ hshift
          · have hde : d = e := by
              have hd' : d ∈ U \ S := Finset.mem_sdiff.mpr ⟨hdU, hdS⟩
              rw [he] at hd'
              exact Finset.mem_singleton.mp hd'
            rw [hde]
            have hre : runit7 (normU7 (7 ^ (m + 1)) e) = c * s := hce
            rw [hre, shift_of_class hs0]
            exact htgood
        · intro d hd h0' hlt
          exact hd5bound d hd h0' hlt j hj
      · -- eq. (11) fails for all `j`: the carry chain forces a 4-interval.
        push Not at h4
        obtain ⟨a, b, c, -, -, -, hSeq⟩ := Finset.card_eq_three.mp hSc
        have hX1 : X 1 = ({qdig7 m (lamP m i₀ 1 u' * normU7 N a),
            qdig7 m (lamP m i₀ 1 u' * normU7 N b),
            qdig7 m (lamP m i₀ 1 u' * normU7 N c)} : Finset (ZMod 7)) := by
          rw [hXj 1, hSeq, Finset.image_insert, Finset.image_insert,
            Finset.image_singleton]
        have hns1 : ∀ i : ZMod 7, ¬ ({qdig7 m (lamP m i₀ 1 u' * normU7 N a),
            qdig7 m (lamP m i₀ 1 u' * normU7 N b),
            qdig7 m (lamP m i₀ 1 u' * normU7 N c)} : Finset (ZMod 7)) ⊆
            cycIv i 4 := by
          intro i hsub
          rw [← hX1] at hsub
          exact h4 1 (by decide) i hsub
        rcases shape3 hns1 with ⟨x, hsh⟩ | ⟨x, hsh⟩
        · -- `X 1 = {x, x+1, x+4}`: the `j = 2` digits already fit a 4-interval.
          have hex : ∀ w : ZMod 7, ∃ d : ℕ,
              w ∈ ({x, x + 1, x + 4} : Finset (ZMod 7)) →
              d ∈ S ∧ qdig7 m (lamP m i₀ 1 u' * normU7 N d) = w := by
            intro w
            by_cases hw : w ∈ ({x, x + 1, x + 4} : Finset (ZMod 7))
            · have hwX : w ∈ X 1 := by rwa [hX1, hsh]
              obtain ⟨d, hd, hdq⟩ := Finset.mem_image.mp hwX
              exact ⟨d, fun _ => ⟨hd, hdq⟩⟩
            · exact ⟨0, fun h => absurd h hw⟩
          choose e he using hex
          have e0 := he x (Finset.mem_insert_self _ _)
          have e1 := he (x + 1)
            (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
          have e4 := he (x + 4)
            (Finset.mem_insert_of_mem
              (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
          have hne01 : e x ≠ e (x + 1) := by
            intro h
            have hq := e0.2
            rw [h, e1.2] at hq
            exact absurd hq (add_one_ne_self x)
          have hne04 : e x ≠ e (x + 4) := by
            intro h
            have hq := e0.2
            rw [h, e4.2] at hq
            exact absurd hq (s3_ne_add (a := 4) (by decide))
          have hne14 : e (x + 1) ≠ e (x + 4) := by
            intro h
            have hq := e1.2
            rw [h, e4.2] at hq
            exact absurd hq (s3_ne_add_add (a := 4) (b := 1) (by decide))
          have hcard3 : ({e x, e (x + 1), e (x + 4)} : Finset ℕ).card = 3 :=
            Finset.card_eq_three.mpr ⟨e x, e (x + 1), e (x + 4),
              hne01, hne04, hne14, rfl⟩
          have hES : ({e x, e (x + 1), e (x + 4)} : Finset ℕ) = S := by
            apply Finset.eq_of_subset_of_card_le
            · intro w hw
              simp only [Finset.mem_insert, Finset.mem_singleton] at hw
              rcases hw with rfl | rfl | rfl
              exacts [e0.1, e1.1, e4.1]
            · exact le_of_eq (hSc.trans hcard3.symm)
          have hXeq : ∀ j : ℕ, ({qdig7 m (lamP m i₀ j u' * normU7 N (e x)),
              qdig7 m (lamP m i₀ j u' * normU7 N (e (x + 1))),
              qdig7 m (lamP m i₀ j u' * normU7 N (e (x + 4)))} :
              Finset (ZMod 7)) = X j := by
            intro j
            rw [hXj j, ← hES, Finset.image_insert, Finset.image_insert,
              Finset.image_singleton]
          have hb0 := qdig7_two_sub (m := m) (i₀ := i₀) (u' := u')
            (x := normU7 N (e x))
          have hb1 := qdig7_two_sub (m := m) (i₀ := i₀) (u' := u')
            (x := normU7 N (e (x + 1)))
          have hb2 := qdig7_two_sub (m := m) (i₀ := i₀) (u' := u')
            (x := normU7 N (e (x + 4)))
          rw [e0.2] at hb0
          rw [e1.2] at hb1
          rw [e4.2] at hb2
          obtain ⟨i2, hi2⟩ := prop3ax _ _ _ hb0 hb1 hb2
          rw [hXeq 2] at hi2
          exact absurd hi2 (h4 2 (by decide) i2)
        · -- `X 1 = {x, x+2, x+4}`: `j = 3` hits `{2,3,4}`/`{3,4,5}` force the
          -- endpoints `b0 = 2`, `b2 = 5`; `j = 4` then fits a 4-interval.
          have hex : ∀ w : ZMod 7, ∃ d : ℕ,
              w ∈ ({x, x + 2, x + 4} : Finset (ZMod 7)) →
              d ∈ S ∧ qdig7 m (lamP m i₀ 1 u' * normU7 N d) = w := by
            intro w
            by_cases hw : w ∈ ({x, x + 2, x + 4} : Finset (ZMod 7))
            · have hwX : w ∈ X 1 := by rwa [hX1, hsh]
              obtain ⟨d, hd, hdq⟩ := Finset.mem_image.mp hwX
              exact ⟨d, fun _ => ⟨hd, hdq⟩⟩
            · exact ⟨0, fun h => absurd h hw⟩
          choose e he using hex
          have e0 := he x (Finset.mem_insert_self _ _)
          have e2 := he (x + 2)
            (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
          have e4 := he (x + 4)
            (Finset.mem_insert_of_mem
              (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
          have hne02 : e x ≠ e (x + 2) := by
            intro h
            have hq := e0.2
            rw [h, e2.2] at hq
            exact absurd hq (s3_ne_add (a := 2) (by decide))
          have hne04 : e x ≠ e (x + 4) := by
            intro h
            have hq := e0.2
            rw [h, e4.2] at hq
            exact absurd hq (s3_ne_add (a := 4) (by decide))
          have hne24 : e (x + 2) ≠ e (x + 4) := by
            intro h
            have hq := e2.2
            rw [h, e4.2] at hq
            exact absurd hq (s3_ne_add_add (a := 4) (b := 2) (by decide))
          have hcard3 : ({e x, e (x + 2), e (x + 4)} : Finset ℕ).card = 3 :=
            Finset.card_eq_three.mpr ⟨e x, e (x + 2), e (x + 4),
              hne02, hne04, hne24, rfl⟩
          have hES : ({e x, e (x + 2), e (x + 4)} : Finset ℕ) = S := by
            apply Finset.eq_of_subset_of_card_le
            · intro w hw
              simp only [Finset.mem_insert, Finset.mem_singleton] at hw
              rcases hw with rfl | rfl | rfl
              exacts [e0.1, e2.1, e4.1]
            · exact le_of_eq (hSc.trans hcard3.symm)
          have hXeq : ∀ j : ℕ, ({qdig7 m (lamP m i₀ j u' * normU7 N (e x)),
              qdig7 m (lamP m i₀ j u' * normU7 N (e (x + 2))),
              qdig7 m (lamP m i₀ j u' * normU7 N (e (x + 4)))} :
              Finset (ZMod 7)) = X j := by
            intro j
            rw [hXj j, ← hES, Finset.image_insert, Finset.image_insert,
              Finset.image_singleton]
          have hX3 := hXeq 3
          have hX4 := hXeq 4
          have hb0 := qdig7_three_sub (m := m) (i₀ := i₀) (u' := u')
            (x := normU7 N (e x))
          have hb1 := qdig7_three_sub (m := m) (i₀ := i₀) (u' := u')
            (x := normU7 N (e (x + 2)))
          have hb2 := qdig7_three_sub (m := m) (i₀ := i₀) (u' := u')
            (x := normU7 N (e (x + 4)))
          rw [e0.2] at hb0
          rw [e2.2] at hb1
          rw [e4.2] at hb2
          have hh1 : ∃ b ∈ ({qdig7 m (lamP m i₀ 3 u' * normU7 N (e x)),
              qdig7 m (lamP m i₀ 3 u' * normU7 N (e (x + 2))),
              qdig7 m (lamP m i₀ 3 u' * normU7 N (e (x + 4)))} :
              Finset (ZMod 7)), b - 3 * x ∈ ({2, 3, 4} : Finset (ZMod 7)) := by
            obtain ⟨b', hb'⟩ := hit3_of_not_subset4
              (fun i' => h4 3 (by decide) i') (3 * x + 2)
            obtain ⟨hb'X, hb'mem⟩ := Finset.mem_inter.mp hb'
            rw [← hX3] at hb'X
            exact ⟨b', hb'X, s3_cycIv_sub_234 hb'mem⟩
          have hh2 : ∃ b ∈ ({qdig7 m (lamP m i₀ 3 u' * normU7 N (e x)),
              qdig7 m (lamP m i₀ 3 u' * normU7 N (e (x + 2))),
              qdig7 m (lamP m i₀ 3 u' * normU7 N (e (x + 4)))} :
              Finset (ZMod 7)), b - 3 * x ∈ ({3, 4, 5} : Finset (ZMod 7)) := by
            obtain ⟨b', hb'⟩ := hit3_of_not_subset4
              (fun i' => h4 3 (by decide) i') (3 * x + 3)
            obtain ⟨hb'X, hb'mem⟩ := Finset.mem_inter.mp hb'
            rw [← hX3] at hb'X
            exact ⟨b', hb'X, s3_cycIv_sub_345 hb'mem⟩
          have hc0 := qdig7_succ_sub (m := m) (i₀ := i₀) (j := 3) (u' := u')
            (x := normU7 N (e x)) ⟨by norm_num, by norm_num⟩
          have hc1 := qdig7_succ_sub (m := m) (i₀ := i₀) (j := 3) (u' := u')
            (x := normU7 N (e (x + 2))) ⟨by norm_num, by norm_num⟩
          have hc2 := qdig7_succ_sub (m := m) (i₀ := i₀) (j := 3) (u' := u')
            (x := normU7 N (e (x + 4))) ⟨by norm_num, by norm_num⟩
          rw [e0.2] at hc0
          rw [e2.2] at hc1
          rw [e4.2] at hc2
          rw [show (3 : ℕ) + 1 = 4 from rfl] at hc0 hc1 hc2
          obtain ⟨i4, hi4⟩ := prop3bx _ _ _ hb0 hb1 hb2 hh1 hh2 _ _ _
            hc0 hc1 hc2
          rw [hX4] at hi4
          exact absurd hi4 (h4 4 (by decide) i4)
```

### Helpers (lines 5–25)

```lean
/-! ### Auxiliary `ZMod 7` checks for the `|Aₛ| = 3` block

`y ∈ cycIv (v + k) 3` transports to `y − v ∈ {k, k+1, k+2}`; used for the
translated `{2,3,4}`/`{3,4,5}` hits in `prop3bx`. -/

theorem s3_cycIv_sub_234 {y v : ZMod 7} (h : y ∈ cycIv (v + 2) 3) :
    y - v ∈ ({2, 3, 4} : Finset (ZMod 7)) := by
  revert y v h; decide

/-- `y ∈ cycIv (v + 3) 3` gives `y − v ∈ {3,4,5}` (translated `{3,4,5}`-hit). -/
theorem s3_cycIv_sub_345 {y v : ZMod 7} (h : y ∈ cycIv (v + 3) 3) :
    y - v ∈ ({3, 4, 5} : Finset (ZMod 7)) := by
  revert y v h; decide

/-- `x + a ≠ x` for `a ≠ 0` in `ZMod 7` (offset distinctness). -/
theorem s3_ne_add {x a : ZMod 7} (ha : a ≠ 0) : x + a ≠ x := by
  revert x a ha; decide

/-- `x + a ≠ x + b` for `a ≠ b` in `ZMod 7` (offset distinctness). -/
theorem s3_ne_add_add {x a b : ZMod 7} (h : a ≠ b) : x + a ≠ x + b := by
  revert x a b h; decide
```
