# W9 — BHK Lemma-8 (`Research07/M3/BHK.lean`) work log

Agent: W9 subagent. Started 2026-09-17 (fresh; previous attempt died before writing code).

## Task
Fill 4 sorries in `Research07/M3/BHK.lean`: `bhk_w_mem_kerSpanRat`, `bhk_w_eq_neg`,
`bhk_w_ne_zero`, `lrc5_real_of_irrational_ratio`. Frozen statements; no sorry/admit.

## Key findings so far

1. **Frozen `bhk_w_ne_zero` is VACUOUS (contradictory hypotheses)** — `hi : ∀ k, s k/r k ≤ s i/r i`
   (i = argmax) + `hj : ∀ k, s j/r j ≤ s k/r k` (j = argmin) + `hij : s i/r i < s j/r j` cannot
   all hold: `hj i` gives `s j/r j ≤ s i/r i`, contradicting `hij`. So the lemma is provable by
   `absurd (hj i) (not_le.mpr hij)` — but it is UNUSABLE in the assembly (can't satisfy its hyps
   with a real extremal choice). The real nonzeroness argument must be inlined in
   `lrc5_real_of_irrational_ratio`. Statement is *true* (vacuously) → not a countermodel case;
   proceeding per rules.

2. **Correct extremal choice is "adjacent values", NOT argmin/argmax.** Paper `bhk.txt` ~line 690:
   (18) is `s_i/r_i < s_j/r_j` AND `s_k/r_k ∉ (s_i/r_i, s_j/r_j)` (OCR-garbled; the mediant argument
   `w_k=0 ⟺ s_k/r_k = (s_i+s_j)/(r_i+r_j)` lands strictly inside the open interval, so needs the
   open-interval exclusion, which argmin/argmax do NOT give). Construction: j := argmax of ratio;
   i := argmax of ratio among `filter (· ratio < ratio j)` (nonempty since s ∦ r). Then
   `∀ k, s k/r k ≤ s i/r i ∨ s j/r j ≤ s k/r k`.

3. **Dependencies still sorry'd** (W6 `Relations.lean`: `exists_pos_rat_kerSpan`,
   `exists_kerSpanRat_not_parallel`, `kerSpan_eq_span_rat`, `kernel_coords_linearIndependent`;
   W8 `OrbitClosure.lean`: `orbit_dense_annihilator`; W5 `LRC4/Main.lean`: `lrc4_rat_finset`).
   I build against the frozen signatures only; `#print axioms` will show `sorryAx` until those
   WPs land — outside my file's control.

4. **API confirmations (Mathlib v4.34.0)**:
   - `Finset.exists_max_image (s)(f)(h : s.Nonempty) : ∃ x ∈ s, ∀ x' ∈ s, f x' ≤ f x` (Data/Finset/Max.lean:387)
   - `AddCircle.coe_zsmul : ↑(n • x) = n • ↑x` (rfl), `coe_add`, `coe_zero` (AddCircle/Defs.lean:198-214)
   - `UnitAddCircle = AddCircle (1:ℝ)`; `circ x := ‖(x : UnitAddCircle)‖` (defeq)
   - `map_sum (QuotientAddGroup.mk' (zmultiples 1))` + `QuotientAddGroup.mk'_apply : mk' N x = ↑x` for ∑↑x_i = ↑∑x_i
   - `mem_closure_iff : x ∈ closure s ↔ ∀ o, IsOpen o → x ∈ o → (o ∩ s).Nonempty` (Topology/Closure.lean:352)
   - `isOpen_iInter_of_finite [Finite ι]` (Topology/Basic.lean:106); `isOpen_lt` (OrderClosed.lean:588)
   - `continuous_apply i`, `Continuous.norm'` (primed!), `continuous_const`
   - `div_lt_div_iff₀ (hb : 0<b)(hd : 0<d) : a/b < c/d ↔ a*d < c*b` (GroupWithZero/Basic.lean:1457)
   - `div_eq_div_iff (hb)(hd) : a/b = c/d ↔ a*d = c*b` (Units/Basic.lean:468)
   - `div_mul_cancel₀ (a)(h : b≠0) : a/b*b = a`; `Submodule.smul_mem (r)(h)`, `Submodule.sub_mem`
   - `Rat.cast_abs : (↑|q|:K)=|↑q|`; `Finset.card_erase_of_mem`, `Finset.mem_erase (a ≠ b ∧ a ∈ s)`
   - `zsmul_eq_mul (a)(n:ℤ) : n•a = ↑n*a`; `Finset.mul_sum (s)(f)(a)`

## Plan
- `bhk_w_mem_kerSpanRat`: `(kerSpanRat u).sub_mem (smul_mem … hs) (smul_mem … hr)`.
- `bhk_w_eq_neg`: `simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring`.
- `bhk_w_ne_zero`: `absurd (hj i) (not_le.mpr hij)` (vacuous).
- `lrc5_real_of_irrational_ratio`: assembly as in the contract: r>0 ∈ kerSpanRat; s nonparallel;
  adjacent-ratio i,j; w; |w|-image Finset card ≤ 3 via w_i = −w_j; hlrc4; δ = 9/40;
  y := i ↦ ↑(t·w_i) ∈ annihilator via k•↑x = ↑(k•x) + map_sum + hwmem; open U = ⋂ {δ < ‖y i‖};
  `orbit_dense_annihilator` + `mem_closure_iff` → t'; answer `|t'|` via `circ_abs`/`abs_mul`.
