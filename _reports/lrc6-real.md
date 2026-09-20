# LRC n=6 real-speeds extension — incremental work log

**Scope.** Extend `lrc6_rel_rat`/`lonely_runner_six_rat` (rational speeds) to real
speeds: `lrc6_rel_real` + `lonely_runner_six (v : Fin 6 → ℝ)`, via the BHK
Lemma 8 induction step (bhk.txt §4, line 619: "the irrational case of
Conjecture 1 for n = 6 follows from the rational case of the conjecture for
n = 5"). Port of `M3/Main.lean` + `M3/BHK.lean` at Fin 5/Fin 6.

**Anchor citation.** `_external/bhk.txt` §4 Lemma 8 is n-generic:
`(n−2)` positive rationals `{vᵢt} ∈ (δ,1−δ)` ⇒ `(n−1)` positive reals with an
irrational ratio pair admit `{uᵢt} ∈ (δ,1−δ)`. Slack: δ ∈ (1/6, 1/5) = e.g. 11/60.
Hypothesis shape: BHK "∃ irrational ratio pair" ⟺ repo "¬∃c, all uᵢ = c·qᵢ"
(contrapositives).

**Plan.**

1. `lrc5_rat_finset` in `LRC5/Main.lean` — clone of `lrc4_rat_finset`
   (Finset ℚ, pos, card ≤ 4 ⇒ ∃t>0, 1/5 ≤ circ(t·q)), via `lrc5_int`.
2. `LRC6/RealCase.lean`: `lrc6_real_of_irrational_ratio` — port of
   `lrc5_real_of_irrational_ratio`: Fin 5, hlrc5 (card ≤ 4, ≥1/5), δ = 11/60.
   Reuses generic {n} infra: kerSpan/kerSpanRat/annihilator/
   orbit_dense_annihilator/exists_pos_rat_kerSpan/
   exists_kerSpanRat_not_parallel/bhk_w_*.
3. `LRC6/Main.lean`: `lrc6_rel_real` (by_cases commensurability:
   rational → scale `lrc6_rel_rat`; irrational → step 2) +
   `lonely_runner_six` (Fin 6, succAbove, dist_unitAddCircle_eq_circ).
4. Audit.lean `#print axioms`; STATEMENT.md section; failures.md.

---

## Log

### Setup
- Baseline `lake build` kicked off (user had touched `LRC6/IntCase.lean`,
  `Prop41.lean` docstring after the audit — re-verify cleanliness).
- Path note: lakefile.toml is at repo ROOT (`07/`), sources in `Research07/`;
  build must run from root, not `Research07/`.

### Code written (pre-build)
- `LRC5/Main.lean`: `lrc5_rat_finset` added between `lrc5_rel_rat` and
  `lonely_runner_five_rat` — verbatim port of `lrc4_rat_finset`
  (`Finset ℚ`, pos, `card ≤ 4` ⇒ `∃t>0, ∀q∈S, 1/5 ≤ circ(t·q)`), via `lrc5_int`.
  Denominator product `B = ∏ q∈S, q.den`, `n q = q.num.natAbs * (B/q.den)`,
  `D = S.image n`, `t = t₀·B`.
- `LRC6/RealCase.lean` (new, ~200 lines): `lrc6_real_of_irrational_ratio` —
  Fin-5 port of `lrc5_real_of_irrational_ratio`. Changes: `Fin 4→Fin 5`,
  `hlrc4→hlrc5` (`card ≤ 4`, `≥1/5`), `δ = 9/40 → 11/60` (∈ (1/6, 1/5)),
  erase-card `3→4`, conclusion `>1/5→>1/6`. Imports `Research07.M3.BHK`
  (reuses generic `{n}` `bhk_w_mem_kerSpanRat`/`bhk_w_eq_neg` + all
  Relations/OrbitClosure infra). The vacuous `bhk_w_ne_zero` helper was NOT
  ported — nonvanishing is proved inline as in the original.
- `LRC6/Main.lean`: `import Research07.LRC6.RealCase`; appended
  `lrc6_rel_real` (commensurability dichotomy: `lrc6_rel_rat` scale vs
  `lrc6_real_of_irrational_ratio lrc5_rat_finset`) and `lonely_runner_six`
  (`Fin 6 → ℝ` injective, succAbove→Fin 5 relatives, `circ_neg` bridge).
  Module docstring updated to cover real speeds.
- `Audit.lean`: added `#print axioms` for `lrc6_rel_real`,
  `lonely_runner_six`, `lrc5_rat_finset`, `lrc6_real_of_irrational_ratio`;
  coverage docstring updated.

### Build
- `lake build` attempts 1–3 hit transient `failed to read file
  <mathlib>.olean(.private)` errors on random modules (files verified intact;
  no stray lean/lake processes; 16.7 GB RAM free) — known failure mode
  (`transient-oleen-read + lock-contention` in failures.md).
- Attempt 4: **green, 8960 jobs**. User-modified `LRC6/IntCase.lean` +
  `Prop41.lean` compile fine. `LRC6.Main`/`RealCase`/`LRC5.Main` elaborated
  with zero errors — the Fin-5 port needed no proof fixes.
- Audit section of build log: `lrc6_rel_real`, `lonely_runner_six`,
  `lrc5_rat_finset`, `lrc6_real_of_irrational_ratio` all report
  `[propext, Classical.choice, Quot.sound]`. ✓

### Gates
- Banned-construct scan on new/modified files: only doc-comment prose
  "admit(s)" (identical wording to `M3/BHK.lean`, previously accepted). ✓
- `RealCase.lean` inside import tree via `LRC6.Main` ← `Research07.lean`;
  no scratch touched. ✓
- `STATEMENT.md`: n=6 real-speeds section added; ℚ-only "known gap" marked
  closed. `failures.md`: transient-olean line appended.

## Final summary

| Theorem | Statement | Status |
|---|---|---|
| `lrc5_rat_finset` | Finset ℚ, pos, card ≤ 4 ⇒ ∃t>0, ∀q∈S, `1/5 ≤ circ(t·q)` | ✓ built |
| `lrc6_real_of_irrational_ratio` | Fin 5 positive reals, ¬commensurate ⇒ ∃t>0, ∀i, `1/6 < circ(t·uᵢ)` | ✓ built |
| `lrc6_rel_real` | Fin 5 nonzero reals ⇒ ∃t>0, ∀i, `1/6 ≤ circ(t·wᵢ)` | ✓ built |
| `lonely_runner_six` | Fin 6 injective reals ⇒ ∀i ∃t≥0, ∀j≠i, `1/6 ≤ dist` | ✓ built |

All axioms `[propext, Classical.choice, Quot.sound]`; zero sorry/admit/
native_decide/unsafe. The real-speeds n=6 extension is complete and matches
the formal-conjectures LRC shape at n = 6 with no domain restriction.
