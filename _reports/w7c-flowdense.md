# W7c — Flow Kronecker density (`flow_orbit_dense`)

Owner: subagent W7c. File owned: `Research07/M3/FlowDense.lean`.
Frozen statement:

```lean
theorem flow_orbit_dense {d : ℕ} {c : Fin d → ℝ} (hc : LinearIndependent ℚ c) :
    Dense (Set.range fun t : ℝ => fun i => ((t * c i : ℝ) : UnitAddCircle))
```

## Progress log

### Session start (fresh agent, previous died pre-code)
- Read `FlowDense.lean` (single sorry), `Dirichlet.lean` (W7b — COMPLETE, no sorry,
  `exists_forall_norm_zsmul_lt[_inv]` proven), `Relations.lean` (W6, has sorries — fine),
  `OrbitClosure.lean` (W8 consumer), `PLAN_M3.md`.
- Math analysis: flow density on T^d ⟺ (via section x_d = 0, return map = rotation by
  `α_ℓ = c_ℓ/c_d` on T^{d-1}) discrete inhomogeneous Kronecker for `{1, α}` ℚ-indep.
  All elementary routes reduce to: **inhomogeneous multidim discrete Kronecker**.
  Next: check `_external/bhk.txt` Kronecker–Perron usage, five-distance-sharp repo for
  Kronecker lemmas, and mathlib API (`AddCircle` density, `exists_norm_nsmul_le`,
  Fourier `mFourier`, OfMinimal).

### Session 2 (agent 3) — API recon complete, route B confirmed feasible

**Decision: route B (Fourier + ergodicity) for the discrete Kronecker kernel.**

Confirmed API (mathlib v4.34):
- `UnitAddTorus d := d → UnitAddCircle` (abbrev, `Topology/Instances/AddCircle/Real.lean:52`).
- `mFourier`, `mFourierLp`, `orthonormal_mFourier`, `mFourierBasis : HilbertBasis (d→ℤ) ℂ L²`,
  `mFourierBasis_repr : repr f i = mFourierCoeff f i`,
  `hasSum_mFourier_series_L2` — all in `Analysis/Fourier/AddCircleMulti.lean`.
- `fourier_apply : fourier n x = toCircle (n • x)`; `toCircle_add`, `toCircle_zero`,
  `AddCircle.injective_toCircle (hT : T ≠ 0)`, `AddCircle.toCircle_addChar : AddChar (AddCircle T) Circle`
  (bundled hom for `map_prod`).
- `AddCircle.coe_zsmul / coe_sub / coe_add / coe_zero / coe_eq_zero_iff : (↑x : AddCircle p)=0 ↔ ∃ n:ℤ, n•p=x`.
- `ergodic_add_left_iff_denseRange_zsmul (μ) [IsFiniteMeasure μ] [μ.InnerRegular]
   [μ.IsAddLeftInvariant] [NeZero μ] : Ergodic (g + ·) μ ↔ DenseRange (· • g : ℤ → G)`
  (to_additive of `ergodic_mul_left_iff_denseRange_zpow`, OfMinimal.lean:215).
- `volume` on `UnitAddTorus ι` (ι Fintype): `IsAddHaarMeasure` via `pi.isAddHaarMeasure`
  (Constructions/Pi.lean:649, to_additive'd); `InnerRegular` via
  `instInnerRegularOfIsHaarMeasureOfCompactSpace` (Haar/Unique.lean:683, compact group);
  finite ⟹ `IsFiniteMeasure`, `NeZero` via probability.
- `measurePreserving_add_left μ g : MeasurePreserving (g + ·) μ μ` (Group/Measure.lean:86);
  `integral_add_left_eq_self (f) (g) : ∫ x, f (g+x) = ∫ f` (Group/Integral.lean:92, additive).
- `indicatorConstLp p hs hμs c : Lp`, `indicatorConstLp_coeFn`;
  `Filter.EventuallyEmptyOrUniv.of_indicator_const (EventuallyConst (s.indicator fun _ ↦ c)) (hc : c ≠ 0)`
  (Order/Filter/EventuallyConst.lean).
- `hasSum_single`/`hasSum_ite_eq` for collapsing the Fourier series to the k=0 term.

**Plan**:
- `FlowDenseAux.lean` (new, mine): `mFourier_apply_add` (char property);
  `mFourier k a = toCircle (∑ kᵢ•aᵢ)`; nonvanishing `mFourier k a ≠ 1` for `k≠0` from
  "no integer relation among {1,α}"; `Ergodic (a+·) volume` (MP by Haar invariance,
  PreErgodic via indicator Fourier coeffs ⇒ a.e. const); then
  `denseRange_zsmul_unitAddTorus` = discrete Kronecker for `{1,α}` ℚ-indep.
- `FlowDense.lean` glue: pick `j` (any; `c j ≠ 0` from LI), section `x_j = 0`,
  `α : {i // i ≠ j} → ℝ := c i / c j`; return times `t₀ + m/c_j`; int-relation
  lemma `∑ ℓ_i c_i = 0 → ℓ = 0` from `LinearIndependent ℚ c`; finish with
  `pi_norm_lt_iff`.

## 2026-09-17 15:51 — W7c COMPLETE: `flow_orbit_dense` proved, builds clean, axioms clean

### Status: DONE

- `lake build Research07.M3.FlowDense` — **zero errors, zero sorries in owned files**.
- `lake build Research07` (full umbrella, 8944 jobs) — **succeeds**; downstream
  `OrbitClosure`/`BHK`/`Main` all build against the new `flow_orbit_dense`.
- Axiom check (`lake env lean` on a scratch file, since deleted):
  - `flow_orbit_dense` : `[propext, Classical.choice, Quot.sound]` — CLEAN, no `sorryAx`.
  - `FlowKronecker.denseRange_zsmul`, `FlowKronecker.ergodic_add_left_torus` — same clean set.
- `grep sorry|admit|native_decide|unsafe` on `FlowDense.lean`/`FlowDenseAux.lean` — empty.

### Files

- `Research07/M3/FlowDenseAux.lean` (~210 lines, NEW, mine): namespace `FlowKronecker`.
  - `mFourier_apply_add` (character is multiplicative),
  - `mFourier_apply_eq_toCircle` (`mFourier k a = toCircle (∑ kᵢ • aᵢ)`),
  - `mFourier_ne_one` (no-relation ⟹ no nontrivial character fixes `a`),
  - `ergodic_add_left_torus` (rotation ergodic: invariant set's L² indicator has
    `f̂ k = mFourier(-k) a · f̂ k`, so `f̂` supported on `{0}`, series collapses to the
    constant `mFourierLp 0`, `s` a.e. empty/full via `EventuallyEmptyOrUniv.of_indicator_const`),
  - `denseRange_zsmul` (discrete Kronecker via `ergodic_add_left_iff_denseRange_zsmul`).
- `Research07/M3/FlowDense.lean` (~125 lines, mine): `flow_orbit_dense` filled.
  Case `d=0`: range = univ (subsingleton). Case `d≥1`: `j := ⟨0,hd⟩`, `c j ≠ 0` by
  `hc.ne_zero`; `dense_iff_inter_open` + `Metric.isOpen_iff`; lift `x j = ↑r`
  (`QuotientAddGroup.mk'_surjective`+`mk'_apply`); LI transport to
  `{i // i ≠ j}` via `g : Fin d → ℚ` (dite with `g j = -n`), `Finset.sum_subtype`,
  `Finset.sum_erase_add`, `Fintype.linearIndependent_iff`; `m` from
  `denseRange_zsmul.exists_dist_lt` on the subtype torus; `t = r/c_j + m/c_j`;
  per-coordinate bound via `dist_pi_lt_iff` (`i=j` exact, `i≠j` via `dist_eq_norm`+`abel`).

### Key gotchas hit (for future agents)

- **`mFourier` API uses a *local* `MeasureSpace UnitAddCircle` instance**
  (`⟨AddCircle.haarAddCircle⟩`, mass 1) that differs from the global
  `AddCircle.measureSpace` (mass `T`). Outside `AddCircleMulti.lean` you must
  re-declare the three local instances or `hasSum_mFourier_series_L2`/`mFourierLp`
  will not unify with ambient `volume` (this was the last blocker).
- `Lp.coeFn_smul c f : ⇑(c • f) =ᵐ c • ⇑f`; use `rw [← hg_eq] at h` rather than `▸`
  when a coefficient mentions `⇑g` (the `▸` motive rewrote all `g`s wrongly).
- `Finset.sum_subtype` needs `(p := ...)` named or the predicate metavariable
  doesn't get inferred; `dif_neg` is deprecated → `dite_eq_right i.prop`.
- `AddCircle.coe_eq_zero_iff` takes the period `p` **explicitly** — use it with
  `rw`, or `(AddCircle.coe_eq_zero_iff (1:ℝ)).mpr`.
- `Dense.exists_dist_lt`/`DenseRange.exists_dist_lt` produce `dist x (f b)` order
  (target first) — needed a `dist_comm`.
- `QuotientAddGroup.mk'_surjective` gives `mk' N r = x`; `mk'_apply` rewrites it
  to `↑r = x`.
- `zmultiples` lives in `AddSubgroup` namespace.

### Verification gates recap

- `lake build Research07.M3.FlowDense` clean ✓; `lake build Research07` clean ✓
  (pre-existing linter warnings + LRC4 sorries belong to other agents' files).
- `#print axioms` = `[propext, Classical.choice, Quot.sound]` only ✓.
- Frozen statement unchanged; no countermodel needed — statement proved as-is.
