# W7b — Simultaneous Dirichlet approximation on the torus

Owner: subagent W7b. File owned: `Research07/M3/Dirichlet.lean`.
Frozen statements: `exists_forall_norm_zsmul_lt`, `exists_forall_norm_zsmul_lt_inv` on `Fin d → UnitAddCircle`.

## Progress log

### 2026-XX session start
- Project confirmed: Lean toolchain `leanprover/lean4:v4.34.0`, mathlib rev `v4.34.0`.
- `_external/five-distance-sharp` present — Route A source available.
- Next: inspect `SimultaneousDirichlet.lean` + `SimultaneousApprox.lean` deps; inspect LRC5 wiring; check `UnitAddCircle` API in this mathlib.

### API recon (done)
- Route A chosen. Deps confirmed in mathlib v4.34:
  - `Finset.exists_ne_map_eq_of_card_lt_of_maps_to (hc : #t < #s) (hf : Set.MapsTo f s t)` — Mathlib/Data/Finset/Card.lean:470.
  - `Int.abs_sub_lt_one_of_floor_eq_floor` (Floor/Ring.lean:239), `Int.fract_nonneg`/`fract_lt_one` (386/393), `Int.floor_nonneg` (Floor/Defs.lean:306), `round_le` (Algebra/Order/Round.lean:158), `exists_nat_gt` (Archimedean/Defs.lean:76).
  - `UnitAddCircle.norm_eq : ‖(x : UnitAddCircle)‖ = |x - round x|` — Normed/Group/AddCircle.lean:223. Already wrapped as `circ` in `Research07/LRC3/Circ.lean`.
  - `AddCircle.coe_zsmul : (↑(n • x) : AddCircle p) = n • ↑x` (rfl) — Topology/Instances/AddCircle/Defs.lean:201.
  - `AddCircle.coe_image_Ico_eq` (simp) at Defs.lean:461 — p,a implicit after `variable {p a}` (Defs.lean:323).
  - `QuotientAddGroup.mk'_surjective : Surjective (mk' N)` — QuotientGroup/Defs.lean:100; `mk' N x = ↑x` is rfl (`mk'_apply`).
- Plan: port `rem`/`delta`/`bddBelow_rem`/`delta_le`/`delta_nonneg` + `box`/`exists_delta_lt_inv` (adding `q ≤ Q^d` output)/`exists_delta_lt` into `namespace SimDirichlet`; bridge lemma `norm_zsmul_le_delta` via `le_ciInf` + `round_le` + `norm_le_pi_norm`; frozen theorems top-level.
- `import Mathlib` per project convention (Circ.lean). Mathlib oleans already built.
