# W7a report — Subtorus.lean sorries

Agent: W7a. File owned: `Research07/M3/Subtorus.lean`.
Task: fill `subtorusMap_continuous` + `subtorusMap_range_eq_annihilator`. Zero sorry/admit/native_decide/unsafe.

## 2026-09-17 — Plan

Math design for `subtorusMap_range_eq_annihilator`:

- (⊆) Pure algebra: `∑ i, k i • Φ(x) i = ∑ ℓ, (∑ i k i * ρ ℓ i) • x ℓ = 0` since
  `ρ ℓ ∈ kerSpanInt u` kills every `k ∈ relLattice u`.
- (⊇) For `y ∈ annihilator u`: lift to `ỹ : Fin n → ℝ` coordinatewise
  (`UnitAddCircle = ℝ ⧸ zmultiples 1`). For `k ∈ relLattice`, `∑ k i • y i = 0`
  gives `∃ z : ℤ, ∑ (k i:ℝ) * ỹ i = z` via `AddCircle.coe_eq_zero_iff`.
- Quotient `Q := ℤⁿ ⧸ kerSpanInt u`: torsion-free (kerSpanInt saturated — the
  `ℕ`-scalar versions of its defining equations persist) + finite ⟹ free
  (`Module.free_of_finite_type_torsion_free'`). Take `bq : Basis ιQ ℤ Q`,
  lifts `γ j` with `mkQ (γ j) = bq j`, functionals `f j := (bq.repr ∘ₗ mkQ) j`,
  coefficient vectors `c j i := f j (Pi.single i 1)`.
- `c j ∈ relLattice u`: `c j` kills `kerSpanInt` (mkQ = 0 there); need
  `kerSpan u = span_ℝ (range ρ̃)` (via W6 `kerSpan_eq_span_rat` + clearing
  denominators into `kerSpanInt ⊆ span_ℤ ρ` via `hspan`), and `u ∈ kerSpan`
  (`mem_kerSpan_self`).
- `w j := ` integer value of `F j ỹ = ∑ ỹ i * c j i`. `z₀ := ∑ j, w j • γ j ∈ ℤⁿ`,
  `v := ỹ - ↑z₀`. Then `F j v = 0` ∀j.
- Projection `P x := x - ∑ j, F j x • γ̃ j` (ℝ-linear): `P v = v`; each
  `P e_i = ↑(e_i - ∑ c j i • γ j)` and that integer vector ∈ kerSpanInt
  (mkQ kills it by `bq.sum_repr`) ⊆ `span_ℤ ρ`, so `v = ∑ v i • P e_i ∈ span_ℝ ρ̃`.
- `∃ x̃ : Fin d → ℝ, v = ∑ x̃ ℓ • ρ̃ ℓ` (`Submodule.mem_span_range_iff_exists_fun`);
  `x := fun ℓ => (x̃ ℓ : UnitAddCircle)`; `Φ(x) i = ↑(v i) = ↑ỹ i - ↑↑z₀ i = y i`
  since integers are 0 mod 1.

NO `LinearIndependent ℝ ρ̃`, NO rank counting needed. Key avoided pitfalls:
double-annihilator (not needed — W6's `kerSpan_eq_span_rat` gives kerSpan =
span of rational points directly); extend_scalars (avoided via projection P
with integer-valued images of basis vectors).

Continuity: `continuous_pi` + `continuous_finset_sum` + `(continuous_apply ℓ).zsmul`
or `continuous_zsmul`. To verify exact names in mathlib v4.34.

## API names to verify (checklist)

- [ ] `UnitAddCircle` def/coe, `AddCircle.coe_eq_zero_iff`, zsmul-on-coe lemma
- [ ] `continuous_pi`, `continuous_finset_sum`, `continuous_apply`, `continuous_zsmul`
- [ ] `Finset.sum_zsmul` / `smul_sum`, `mul_zsmul`
- [ ] `Module.free_of_finite_type_torsion_free'`, `NoZeroSMulDivisors` ctor
- [ ] `Module.Free.chooseBasis`, Fintype on `ChooseBasisIndex`
- [ ] `Submodule.ker_mkQ`, `Submodule.mkQ_surjective`, `Submodule.Quotient.mk_eq_zero`
- [ ] `Submodule.mem_span_range_iff_exists_fun`
- [ ] Rat common-denominator API (`Rat.num_div_den`, `Rat.den` dvd)

---

## FINAL REPORT — W7a complete (2026-09-17 ~15:30)

### Status: BOTH sorries filled, file compiles with ZERO errors.

`lake env lean Research07/M3/Subtorus.lean` → 0 errors. Only style
warnings remain (haveI-on-Prop linter at :101,:102; unused-variable
linter on the frozen `hinj` hypothesis — `hinj` is part of the frozen
statement and is genuinely not needed: the result holds under the given
hypotheses; linear independence is required only to identify `d` with
the lattice rank, not for the set equality).

### Verification caveat — CONCURRENT AGENTS
`lake build` currently fails on `Research07/M3/Relations.lean`
(lines ~471–607): another agent (W6) is mid-edit on that file; its
in-progress proof attempts do not compile. NOT my file, NOT touched.
Workaround used for verification: compiled the git-HEAD (skeleton,
sorry-bearing) Relations.lean to
`.lake/build/lib/lean/Research07/M3/Relations.olean` via direct `lean`
call, then `lake env lean` on Subtorus.lean → clean.
The orchestrator must re-run `lake build Research07.M3.Subtorus` after
W6's Relations.lean compiles again.

### Axiom audit (Scratch file, since removed)
- `subtorusMap_continuous` depends on axioms:
  [propext, Classical.choice, Quot.sound] — CLEAN.
- `subtorusMap_range_eq_annihilator` depends on:
  [propext, sorryAx, Classical.choice, Quot.sound].
  The `sorryAx` enters ONLY via `kerSpan_eq_span_rat` (still `sorry` in
  the skeleton Relations.lean it was audited against). Subtorus.lean
  itself contains no sorry/admit/native_decide/unsafe/axiom.
  Re-audit once Relations is finished — expected to drop to the
  standard three axioms.

### Proof architecture of subtorusMap_range_eq_annihilator (⊇ direction)
1. `K := kerSpanInt u` is *saturated*: `m • v ∈ K`, `m ≠ 0` → `v ∈ K`
   (a ℤ-relation kills `m•v` iff it kills `v`). Hence
   `Q := (Fin n → ℤ) ⧸ K` is `Module.IsTorsionFree ℤ` — proved manually
   via `Submodule.ker_mkQ` + `LinearMap.map_smul` + `mul_eq_zero`.
2. `Q` finite + torsion-free ⇒ `Module.Free ℤ Q`
   (`Module.free_of_finite_type_torsion_free'`); take
   `bq := Module.Free.chooseBasis ℤ Q`, lifts `γ j` with
   `K.mkQ (γ j) = bq j`, functionals
   `f j := Finsupp.lapply j ∘ₗ bq.repr.toLinearMap ∘ₗ K.mkQ` —
   integer-valued with `f j (γ j') = δ_{j'j}` (`bq.repr_self_apply`).
3. Rows `c j i := f j (eᵢ)` satisfy `f j v = ∑ c j i * v i`
   (`pi_eq_sum_univ'` + linearity) and `f j (ρ ℓ) = 0` since `ρ ℓ ∈ K`.
4. `hker_eq : kerSpan u = span_ℝ (range ρR)`: ⊆ via
   `kerSpan_eq_span_rat` + common denominator `N = ∏ den(xᵢ)`
   (`hdenom`, `Nat.cast_div`, `Rat.num_div_den`) + `hspan`;
   ⊇ from `hmem` by casting `∑ kᵢ(ρℓ)ᵢ = 0` to ℝ.
5. `c j ∈ relLattice u`: `F j` (ℝ-linear extension of `f j`) kills
   `span ρR = kerSpan ∋ u`, so `∑ cⱼᵢ uᵢ = 0`.
6. For `y ∈ annihilator`: lift `yR : Fin n → ℝ`; `∑ cⱼᵢ • yᵢ = 0` +
   `AddCircle.coe_eq_zero_iff` ⇒ `F j yR = w j ∈ ℤ`. Subtract
   `z₀ = ∑ wⱼ•γⱼ` (has `f j z₀ = w j`) ⇒ `v = yR − z̃₀` has `F j v = 0`.
7. Corrected vectors `g i := eᵢ − ∑ c j i • γ j ∈ K` (their `mkQ`
   vanishes: `∑ fⱼeᵢ•bqⱼ = ∑ cⱼᵢ•bqⱼ`), so `g i ∈ span ρ` (`hspan`);
   decomposition `v = ∑ vᵢ • g̃ᵢ` (the `F`-part vanishes) puts
   `v ∈ span_ℝ ρR` ⇒ coefficients `xR : Fin d → ℝ`,
   preimage `x ℓ := ↑xR ℓ`. Pointwise equality uses
   `AddCircle.coe_zsmul`, `map_sum` on `QuotientAddGroup.mk'`, and
   `↑z̃₀ᵢ = 0` on the circle (`coe_eq_zero_iff`, `z • 1 = ↑z`).

### API names confirmed working (v4.34)
- `continuous_finsetSum` (not `continuous_finset_sum`),
  `continuous_zsmul`, `continuous_pi`, `continuous_apply`.
- `QuotientAddGroup.mk'`, `QuotientAddGroup.mk'_apply`,
  `QuotientAddGroup.mk'_surjective` — all on `AddSubgroup.zmultiples 1`.
- `Module.isTorsionFree_iff_smul_eq_zero`, `Submodule.ker_mkQ`,
  `mkQ_surjective`, `bq.repr_self_apply j' j`
  (arg order: basis index FIRST, output index second),
  `Finsupp.lapply`, `Finsupp.single_eq_*`,
  `pi_eq_sum_univ'`, `Nat.cast_div hdvd hden0` (2 explicit proofs),
  `Int.cast_natCast`, `Finset.dvd_prod_of_mem`, `mul_zsmul`,
  `Finset.smul_sum`, `Finset.sum_smul`, `Finset.sum_ite_eq'`.

### Lean-4 pitfalls hit (for future agents)
- `ρ̃`, `ỹ`, `x̃` are INVALID identifiers (combining diacritics) →
  parse errors far away from the actual line. Use `ρR`, `yR`, `xR`.
- `Pi.single i 1` needs the codomain known; annotate
  `(Pi.single i (1:ℤ) : Fin n → ℤ)` when not inferable.
- `rw [Finset.sum_apply]` only rewrites the FIRST matching `(∑) i`
  instance — call twice for two-sided goals.
- `simp` eagerly rewrites `a • b` to `a * b` (smul_eq_mul is simp),
  breaking later `map_smul` rewrites — prefer `rw`+`simp only` chains.
- `(x : ℚ)`-style ascriptions propagate the expected type INTO
  arithmetic operands (no `↑(_*_)` pattern remains for `Int.cast_mul`).
- `← Rat.num_div_den` rewrites `x` inside `x.num`/`x.den` too — use
  `conv_rhs` to target.

### Files changed
- `Research07/M3/Subtorus.lean` — both sorries proved (~390 lines).
- `.lake/build/lib/lean/Research07/M3/Subtorus.olean` + skeleton
  `Relations.olean` — build artifacts only (lake will rebuild
  Relations when its source is fixed; no source file of another
  package was modified).
