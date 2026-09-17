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
