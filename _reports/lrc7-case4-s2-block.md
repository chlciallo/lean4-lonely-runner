# lrc7_case4 — |A_s|=2 block (Case4MainS2.lean)

Verified sorry-free block, verbatim from `_dev/scratch/Case4MainS2.lean` lines 141–470.
Build: `lake env lean _dev/scratch/Case4MainS2.lean` — zero errors (only pre-existing sorry warnings in sibling bullets).

```lean
    · -- <<S2-TARGET: fill this |A_s|=2 case — interval_cases orders low→high: THIS bullet has hSc : S.card = 2>>
      -- |A_s| = 2 (paper §5, Case 3). WLOG the two leftover classes are not both
      -- `4s`: the (4,4) configuration fails for the 4-consecutive-shift argument,
      -- so re-select the principal class `s' := 4s` when needed — the old extras
      -- become principal and the old S becomes class-`2s'` extras.
      obtain ⟨s', hs'124, hS'2, hnot44⟩ : ∃ s' ∈ ({1, 2, 4} : Finset (ZMod 7)),
          (U.filter (fun d => r d = s')).card = 2 ∧
          ¬ (∀ e ∈ U, r e ≠ s' → r e = 4 * s') := by
        by_cases h44 : ∀ e ∈ U, r e ≠ s → r e = 4 * s
        · have h4s124 : (4 : ZMod 7) * s ∈ ({1, 2, 4} : Finset (ZMod 7)) := by
            have h := hs124
            rcases Finset.mem_insert.mp h with rfl | h
            · decide
            rcases Finset.mem_insert.mp h with rfl | h
            · decide
            rw [Finset.mem_singleton] at h; rw [h]; decide
          have h4ne : (4 : ZMod 7) * s ≠ s := by
            have h := hs124
            rcases Finset.mem_insert.mp h with rfl | h
            · decide
            rcases Finset.mem_insert.mp h with rfl | h
            · decide
            rw [Finset.mem_singleton] at h; rw [h]; decide
          have hfilter : U.filter (fun d => r d = 4 * s) =
              U.filter (fun d => r d ≠ s) := by
            apply Finset.filter_congr
            intro x hx
            constructor
            · intro hx4
              rw [hx4]
              exact h4ne
            · intro hxne
              exact h44 x hx hxne
          have hcard4 : (U.filter (fun d => r d = 4 * s)).card = 2 := by
            have heq : U.filter (fun d => r d ≠ s) = U \ S := by
              ext x
              simp only [Finset.mem_filter, Finset.mem_sdiff, hS]
              constructor
              · rintro ⟨hxU, hxne⟩
                exact ⟨hxU, fun hxs => hxne hxs.2⟩
              · rintro ⟨hxU, hxnS⟩
                exact ⟨hxU, fun hxs => hxnS ⟨hxU, hxs⟩⟩
            have hsubU : S ⊆ U := Finset.filter_subset (fun d => r d = s) U
            rw [hfilter, heq, Finset.card_sdiff_of_subset hsubU, hUcard, hSc]
          have hnot : ¬ (∀ e ∈ U, r e ≠ 4 * s → r e = 4 * (4 * s)) := by
            intro hall
            have hne2 : (4 : ZMod 7) * (4 * s) ≠ s := by
              have h := hs124
              rcases Finset.mem_insert.mp h with rfl | h
              · decide
              rcases Finset.mem_insert.mp h with rfl | h
              · decide
              rw [Finset.mem_singleton] at h; rw [h]; decide
            obtain ⟨e, heS⟩ : S.Nonempty := Finset.card_pos.mp (by omega)
            rw [hS] at heS
            obtain ⟨heU, hes⟩ := Finset.mem_filter.mp heS
            have hne4 : r e ≠ 4 * s := by rw [hes]; exact Ne.symm h4ne
            have heq4 := hall e heU hne4
            rw [hes] at heq4
            exact hne2 heq4.symm
          exact ⟨4 * s, h4s124, hcard4, hnot⟩
        · exact ⟨s, hs124, by rw [← hS]; exact hSc, h44⟩
      have hs'0 : s' ≠ 0 := by
        have h := hs'124
        rcases Finset.mem_insert.mp h with rfl | h
        · decide
        rcases Finset.mem_insert.mp h with rfl | h
        · decide
        rw [Finset.mem_singleton] at h; rw [h]; decide
      set S' : Finset ℕ := U.filter (fun d => r d = s') with hS'def
      have hS'card : S'.card = 2 := by rw [hS'def]; exact hS'2
      set X' : ℕ → Finset (ZMod 7) := fun j =>
        S'.image (fun d => qdig7 m (lamP m i₀ j u' * normU7 N d)) with hX'
      by_cases h2 : ∃ j ∈ Finset.Icc 1 5, ∃ i : ZMod 7, X' j ⊆ cycIv i 2
      · -- ℓ ≤ 2 somewhere: 4 consecutive shifts rescue both extras.
        obtain ⟨j, hj, i, hi⟩ := h2
        rw [Finset.mem_Icc] at hj
        have hExtraCard : (U \ S').card = 2 := by
          have hsub : S' ⊆ U := Finset.filter_subset (fun d => r d = s') U
          rw [Finset.card_sdiff_of_subset hsub, hUcard, hS'card]
        obtain ⟨e1, e2, he12, hExtraEq⟩ := Finset.card_eq_two.mp hExtraCard
        have he1mem : e1 ∈ U \ S' := by
          rw [hExtraEq]; exact Finset.mem_insert_self _ _
        have he2mem : e2 ∈ U \ S' := by
          rw [hExtraEq]
          exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self _))
        have he1U : e1 ∈ U := (Finset.mem_sdiff.mp he1mem).1
        have he2U : e2 ∈ U := (Finset.mem_sdiff.mp he2mem).1
        have he1nS : e1 ∉ S' := (Finset.mem_sdiff.mp he1mem).2
        have he2nS : e2 ∉ S' := (Finset.mem_sdiff.mp he2mem).2
        have he1r : r e1 ≠ s' := fun h => he1nS (by
          rw [hS'def]; exact Finset.mem_filter.mpr ⟨he1U, h⟩)
        have he2r : r e2 ≠ s' := fun h => he2nS (by
          rw [hS'def]; exact Finset.mem_filter.mpr ⟨he2U, h⟩)
        obtain ⟨c1, hc1_124, he1c⟩ := class_decomp (hr124 e1 he1U) hs'124
        obtain ⟨c2, hc2_124, he2c⟩ := class_decomp (hr124 e2 he2U) hs'124
        have hc1 : c1 ∈ ({2, 4} : Finset (ZMod 7)) := by
          rcases Finset.mem_insert.mp hc1_124 with h1 | h24
          · exfalso
            rw [h1, one_mul] at he1c
            exact he1r he1c
          rcases Finset.mem_insert.mp h24 with h2v | h4v
          · rw [h2v]; decide
          · rw [Finset.mem_singleton] at h4v; rw [h4v]; decide
        have hc2 : c2 ∈ ({2, 4} : Finset (ZMod 7)) := by
          rcases Finset.mem_insert.mp hc2_124 with h1 | h24
          · exfalso
            rw [h1, one_mul] at he2c
            exact he2r he2c
          rcases Finset.mem_insert.mp h24 with h2v | h4v
          · rw [h2v]; decide
          · rw [Finset.mem_singleton] at h4v; rw [h4v]; decide
        have hne : ¬ (c1 = 4 ∧ c2 = 4) := by
          rintro ⟨h1, h2v⟩
          apply hnot44
          intro e heU hens
          have heS : e ∈ U \ S' := by
            rw [Finset.mem_sdiff]
            refine ⟨heU, ?_⟩
            intro hmemS
            have h := hmemS
            rw [hS'def] at h
            exact hens (Finset.mem_filter.mp h).2
          rw [hExtraEq] at heS
          rcases Finset.mem_insert.mp heS with rfl | hmem
          · rw [he1c, h1]
          · rw [Finset.mem_singleton] at hmem
            rw [hmem, he2c, h2v]
        obtain ⟨t, ht4, hz1, hz2⟩ := quad_point_avoid
          (z₁ := qdig7 m (lamP m i₀ j u' * normU7 N e1))
          (z₂ := qdig7 m (lamP m i₀ j u' * normU7 N e2))
          (c₁ := c1) (c₂ := c2) (i := i) hc1 hc2 hne
        have hit : i + t ∈ ({1, 2, 3, 4} : Finset (ZMod 7)) := by
          have htv : i + t = 1 ∨ i + t = 2 ∨ i + t = 3 ∨ i + t = 4 := by
            rcases Finset.mem_insert.mp ht4 with h | h
            · exact Or.inl (by rw [h]; ring)
            rcases Finset.mem_insert.mp h with h | h
            · exact Or.inr (Or.inl (by rw [h]; ring))
            rcases Finset.mem_insert.mp h with h | h
            · exact Or.inr (Or.inr (Or.inl (by rw [h]; ring)))
            · exact Or.inr (Or.inr (Or.inr (by rw [Finset.mem_singleton.mp h]; ring)))
          rcases htv with h | h | h | h <;> rw [h] <;> decide
        have hshS : t * s'⁻¹ * s' = t := by
          have h := shift_of_class (s := s') (c := 1) (t := t) hs'0
          simpa using h
        apply case4_finish hm him hj hu'nd hs'0 t D hpos hle
        · intro d hdD hdν
          have hdU : d ∈ U := by
            have hdL : d ∈ level7 D 0 := Finset.mem_filter.mpr ⟨hdD, hdν⟩
            rwa [hU] at hdL
          by_cases hdS : d ∈ S'
          · have hdr : r d = s' := by
              have h := hdS
              rw [hS'def] at h
              exact (Finset.mem_filter.mp h).2
            have hqd : qdig7 m (lamP m i₀ j u' * normU7 N d) ∈ X' j :=
              Finset.mem_image.mpr ⟨d, hdS, rfl⟩
            have hdrd : runit7 (normU7 (7 ^ (m + 1)) d) = s' := hdr
            rw [hdrd, hshS]
            have hshift : qdig7 m (lamP m i₀ j u' * normU7 N d) + t ∈
                cycIv (i + t) 2 := by
              have hmem := hi hqd
              have himg : qdig7 m (lamP m i₀ j u' * normU7 N d) + t ∈
                  (cycIv i 2).image (· + t) :=
                Finset.mem_image.mpr ⟨_, hmem, rfl⟩
              rwa [cycIv_image_add] at himg
            exact avoids06_cycIv_2 hit _ hshift
          · have hdExtra : d ∈ U \ S' := Finset.mem_sdiff.mpr ⟨hdU, hdS⟩
            rw [hExtraEq] at hdExtra
            rcases Finset.mem_insert.mp hdExtra with hde1 | hdE2
            · rw [hde1]
              have hrd1 : runit7 (normU7 (7 ^ (m + 1)) e1) = c1 * s' := he1c
              rw [hrd1, shift_of_class hs'0]
              exact hz1
            · rw [Finset.mem_singleton] at hdE2
              rw [hdE2]
              have hrd2 : runit7 (normU7 (7 ^ (m + 1)) e2) = c2 * s' := he2c
              rw [hrd2, shift_of_class hs'0]
              exact hz2
        · intro d hd h0' hlt
          exact hd5bound d hd h0' hlt j hj
      · -- No 2-interval fits any X' j: the propagation lemmas force a
        -- contradiction, so this branch is vacuous (paper's repeated use of (9)).
        push Not at h2
        obtain ⟨dA, dB, hdAB, hS'eq⟩ := Finset.card_eq_two.mp hS'card
        have hX'eq : ∀ j : ℕ, X' j = ({qdig7 m (lamP m i₀ j u' * normU7 N dA),
            qdig7 m (lamP m i₀ j u' * normU7 N dB)} : Finset (ZMod 7)) := by
          intro j
          have hX'j : X' j = S'.image
              (fun d => qdig7 m (lamP m i₀ j u' * normU7 N d)) := rfl
          rw [hX'j, hS'eq]
          ext w
          simp only [Finset.mem_image, Finset.mem_insert, Finset.mem_singleton]
          constructor
          · rintro ⟨d, hd, rfl⟩
            rcases hd with rfl | rfl
            · exact Or.inl rfl
            · exact Or.inr rfl
          · intro hw
            rcases hw with rfl | rfl
            · exact ⟨dA, Or.inl rfl, rfl⟩
            · exact ⟨dB, Or.inr rfl, rfl⟩
        have hdist : ∀ j ∈ Finset.Icc 1 5,
            qdig7 m (lamP m i₀ j u' * normU7 N dB) -
              qdig7 m (lamP m i₀ j u' * normU7 N dA) ∉
              ({0, 1, 6} : Finset (ZMod 7)) := by
          intro j hj hmem
          obtain ⟨i, hi⟩ := pair_subset2_iff.mpr hmem
          rw [← hX'eq j] at hi
          exact h2 j hj i hi
        have hcomp : ∀ z : ZMod 7, z ∉ ({0, 1, 6} : Finset (ZMod 7)) →
            z ∈ ({2, 3, 4, 5} : Finset (ZMod 7)) := by
          decide
        have hnegSymm : ∀ z : ZMod 7, z ∉ ({0, 1, 6} : Finset (ZMod 7)) →
            -z ∉ ({0, 1, 6} : Finset (ZMod 7)) := by
          decide
        have hswapDist : ∀ j ∈ Finset.Icc 1 5,
            qdig7 m (lamP m i₀ j u' * normU7 N dA) -
              qdig7 m (lamP m i₀ j u' * normU7 N dB) ∉
              ({0, 1, 6} : Finset (ZMod 7)) := by
          intro j hj
          have h := hnegSymm _ (hdist j hj)
          rwa [neg_sub] at h
        have hmem1 : qdig7 m (lamP m i₀ 1 u' * normU7 N dB) -
            qdig7 m (lamP m i₀ 1 u' * normU7 N dA) ∈
            ({2, 3, 4, 5} : Finset (ZMod 7)) :=
          hcomp _ (hdist 1 (Finset.mem_Icc.mpr ⟨by decide, by decide⟩))
        obtain ⟨a0, a1, hD01, hΔ, hdistO⟩ : ∃ a0 a1 : ℕ,
            S' = ({a0, a1} : Finset ℕ) ∧
            (qdig7 m (lamP m i₀ 1 u' * normU7 N a1) -
              qdig7 m (lamP m i₀ 1 u' * normU7 N a0) = 2 ∨
             qdig7 m (lamP m i₀ 1 u' * normU7 N a1) -
              qdig7 m (lamP m i₀ 1 u' * normU7 N a0) = 3) ∧
            (∀ j ∈ Finset.Icc 1 5, qdig7 m (lamP m i₀ j u' * normU7 N a1) -
              qdig7 m (lamP m i₀ j u' * normU7 N a0) ∉
              ({0, 1, 6} : Finset (ZMod 7))) := by
          rcases Finset.mem_insert.mp hmem1 with h2v | h345
          · exact ⟨dA, dB, hS'eq, Or.inl h2v, hdist⟩
          rcases Finset.mem_insert.mp h345 with h3v | h45
          · exact ⟨dA, dB, hS'eq, Or.inr h3v, hdist⟩
          rcases Finset.mem_insert.mp h45 with h4v | h5v
          · have hswap : qdig7 m (lamP m i₀ 1 u' * normU7 N dA) -
                qdig7 m (lamP m i₀ 1 u' * normU7 N dB) = 3 := by
              rw [← neg_sub, h4v]
              decide
            exact ⟨dB, dA, hS'eq.trans (Finset.pair_comm dA dB), Or.inr hswap,
              hswapDist⟩
          · rw [Finset.mem_singleton] at h5v
            have hswap : qdig7 m (lamP m i₀ 1 u' * normU7 N dA) -
                qdig7 m (lamP m i₀ 1 u' * normU7 N dB) = 2 := by
              rw [← neg_sub, h5v]
              decide
            exact ⟨dB, dA, hS'eq.trans (Finset.pair_comm dA dB), Or.inl hswap,
              hswapDist⟩
        rcases hΔ with hΔ2 | hΔ3
        · -- `{x, x+2}` shape: `prop2ix` (j=3 via `qdig7_three_sub`,
          -- j=4 and j=5 via `qdig7_succ_sub`).
          have hq1d1 : qdig7 m (lamP m i₀ 1 u' * normU7 N a1) =
              qdig7 m (lamP m i₀ 1 u' * normU7 N a0) + 2 :=
            (sub_eq_iff_eq_add.mp hΔ2).trans (add_comm _ _)
          have hb0 := qdig7_three_sub (m := m) (i₀ := i₀) (u' := u')
            (x := normU7 N a0)
          have hb1 := qdig7_three_sub (m := m) (i₀ := i₀) (u' := u')
            (x := normU7 N a1)
          rw [hq1d1] at hb1
          have hc0 : qdig7 m (lamP m i₀ 4 u' * normU7 N a0) -
              qdig7 m (lamP m i₀ 3 u' * normU7 N a0) -
              qdig7 m (lamP m i₀ 1 u' * normU7 N a0) ∈
              ({0, 1} : Finset (ZMod 7)) :=
            qdig7_succ_sub (m := m) (i₀ := i₀) (j := 3) (u' := u')
              (x := normU7 N a0) ⟨by decide, by decide⟩
          have hc1 : qdig7 m (lamP m i₀ 4 u' * normU7 N a1) -
              qdig7 m (lamP m i₀ 3 u' * normU7 N a1) -
              qdig7 m (lamP m i₀ 1 u' * normU7 N a1) ∈
              ({0, 1} : Finset (ZMod 7)) :=
            qdig7_succ_sub (m := m) (i₀ := i₀) (j := 3) (u' := u')
              (x := normU7 N a1) ⟨by decide, by decide⟩
          rw [hq1d1] at hc1
          have he0 : qdig7 m (lamP m i₀ 5 u' * normU7 N a0) -
              qdig7 m (lamP m i₀ 4 u' * normU7 N a0) -
              qdig7 m (lamP m i₀ 1 u' * normU7 N a0) ∈
              ({0, 1} : Finset (ZMod 7)) :=
            qdig7_succ_sub (m := m) (i₀ := i₀) (j := 4) (u' := u')
              (x := normU7 N a0) ⟨by decide, by decide⟩
          have he1 : qdig7 m (lamP m i₀ 5 u' * normU7 N a1) -
              qdig7 m (lamP m i₀ 4 u' * normU7 N a1) -
              qdig7 m (lamP m i₀ 1 u' * normU7 N a1) ∈
              ({0, 1} : Finset (ZMod 7)) :=
            qdig7_succ_sub (m := m) (i₀ := i₀) (j := 4) (u' := u')
              (x := normU7 N a1) ⟨by decide, by decide⟩
          rw [hq1d1] at he1
          have hfit := prop2ix _ _ hb0 hb1
            (hdistO 3 (Finset.mem_Icc.mpr ⟨by decide, by decide⟩))
            _ _ hc0 hc1
            (hdistO 4 (Finset.mem_Icc.mpr ⟨by decide, by decide⟩))
            _ _ he0 he1
          exact (hdistO 5 (Finset.mem_Icc.mpr ⟨by decide, by decide⟩) hfit).elim
        · -- `{x, x+3}` shape: `prop2iix` (j=2 via `qdig7_two_sub`,
          -- j=3 via `qdig7_succ_sub`, j=5 via `qdig7_five_sub23`).
          have hq1d1 : qdig7 m (lamP m i₀ 1 u' * normU7 N a1) =
              qdig7 m (lamP m i₀ 1 u' * normU7 N a0) + 3 :=
            (sub_eq_iff_eq_add.mp hΔ3).trans (add_comm _ _)
          have hb0 := qdig7_two_sub (m := m) (i₀ := i₀) (u' := u')
            (x := normU7 N a0)
          have hb1 := qdig7_two_sub (m := m) (i₀ := i₀) (u' := u')
            (x := normU7 N a1)
          rw [hq1d1] at hb1
          have hc0 : qdig7 m (lamP m i₀ 3 u' * normU7 N a0) -
              qdig7 m (lamP m i₀ 2 u' * normU7 N a0) -
              qdig7 m (lamP m i₀ 1 u' * normU7 N a0) ∈
              ({0, 1} : Finset (ZMod 7)) :=
            qdig7_succ_sub (m := m) (i₀ := i₀) (j := 2) (u' := u')
              (x := normU7 N a0) ⟨by decide, by decide⟩
          have hc1 : qdig7 m (lamP m i₀ 3 u' * normU7 N a1) -
              qdig7 m (lamP m i₀ 2 u' * normU7 N a1) -
              qdig7 m (lamP m i₀ 1 u' * normU7 N a1) ∈
              ({0, 1} : Finset (ZMod 7)) :=
            qdig7_succ_sub (m := m) (i₀ := i₀) (j := 2) (u' := u')
              (x := normU7 N a1) ⟨by decide, by decide⟩
          rw [hq1d1] at hc1
          have he0 := qdig7_five_sub23 (m := m) (i₀ := i₀) (u' := u')
            (x := normU7 N a0)
          have he1 := qdig7_five_sub23 (m := m) (i₀ := i₀) (u' := u')
            (x := normU7 N a1)
          have hfit := prop2iix _ _ hb0 hb1
            (hdistO 2 (Finset.mem_Icc.mpr ⟨by decide, by decide⟩))
            _ _ hc0 hc1
            (hdistO 3 (Finset.mem_Icc.mpr ⟨by decide, by decide⟩))
            _ _ he0 he1
          exact (hdistO 5 (Finset.mem_Icc.mpr ⟨by decide, by decide⟩) hfit).elim
```
