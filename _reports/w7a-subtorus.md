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
