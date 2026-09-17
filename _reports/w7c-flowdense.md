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
