# W6 — Relations.lean progress report

## 2026-XX-XX — kickoff

Owned file: `Research07/M3/Relations.lean` (imports `Mathlib`, `Research07.LRC3.Circ`).
4 frozen theorems to prove:

- `kerSpan_eq_span_rat` : `kerSpan u = span ℝ (cast '' kerSpanRat u)`
- `exists_pos_rat_kerSpan` : positive `u` ⇒ ∃ positive rational point of `kerSpanRat u`
- `exists_kerSpanRat_not_parallel` : `u ∉ ℝ·r` ⇒ ∃ `s ∈ kerSpanRat u`, `s ∉ ℚ·r`
- `kernel_coords_linearIndependent` : coordinates of `u` in a ℚ-spanning set of `kerSpanRat u` are ℚ-linearly independent

Definitions already in file: `relLattice` (ℤ-kernel of `Fintype.linearCombination ℤ u`),
`kerSpan` (real annihilator of relLattice), `kerSpanRat` (rational version),
`kerSpanInt`, `annihilator`, `mem_kerSpan_self` (proved).

Plan of attack (math):
- `kerSpan_eq_span_rat`: kerSpan is kernel of the real relation matrix whose rows are a
  finite generating set of relLattice (fg since ℤⁿ is noetherian). A rational matrix has
  the same kernel over ℚ vs ℝ up to base change; so kerSpan = ℝ-span of ℚ-kernel.
  Route: relLattice u is a f.g. ℤ-module (submodule of ℤⁿ, noetherian). Pick a ℚ-basis
  of `Submodule.span ℚ (relLattice-cast)` or work directly with orthogonal complement:
  kerSpan u = (span ℝ of relLattice-cast)ᗮ in ℝⁿ, and kerSpanRat u = (span ℚ of
  relLattice-cast)ᗮ in ℚⁿ. Then use: for a ℚ-subspace W ⊆ ℚⁿ,
  (Wᗮ base-changed) = (W base-changed)ᗮ — dimension counting via rank-nullity.
  Simpler concrete route: kerSpan is cut out by finitely many rational linear equations;
  ker A over ℝ = ℝ ⊗ ker A over ℚ. Mathlib likely has `LinearMap.ker` base-change API or
  we do it via Basis: take ℚ-basis b of kerSpanRat u (exists since f.d.), show the cast
  family is ℝ-linearly independent and spans kerSpan.
- `exists_pos_rat_kerSpan`: u ∈ kerSpan ⇒ u ∈ span of cast basis ⇒ u = Σ c_ℓ ρ_ℓ with
  real coeffs; approximate each c_ℓ by rationals q_ℓ with |q_ℓ − c_ℓ| small; since all
  uᵢ > 0 and there are finitely many coords/terms, small perturbation keeps positivity;
  Σ q_ℓ ρ_ℓ ∈ kerSpanRat.
- `exists_kerSpanRat_not_parallel`: contrapositive — if every s ∈ kerSpanRat is a
  rational multiple of r, then kerSpanRat ⊆ ℚ·r, so kerSpan = span ℝ ⊆ ℝ·r, so u ∈ ℝ·r.
- `kernel_coords_linearIndependent`: if Σ b_ℓ c_ℓ = 0 with b ≠ 0 (b₀ ≠ 0), then
  u ∈ ℝ-span of {ρ_ℓ : ℓ ≠ ℓ₀} cast =: W'. Every k ∈ relLattice vanishes on all of
  kerSpanRat ⊇ W', so the ℚ-annihilator of W' (in ℚⁿ) viewed in ℝⁿ... wait, more
  precisely: u ∈ ℝ-span of cast(W') where W' ⊊ kerSpanRat. Then the annihilator
  (in ℚⁿ*, i.e. ℚⁿ acting by dot product) of W' strictly contains annihilator of
  kerSpanRat = span of relLattice. Pick k' ∈ ℚⁿ, k' ⊥ W', k' not ⊥ kerSpanRat
  (exists since W' ≠ kerSpanRat and f.d.). Scale k' to integers ⇒ integer relation
  vanishing on... hmm actually we need: k' ⊥ {ρ_ℓ:ℓ≠ℓ₀} but k' not orthogonal to all
  of kerSpanRat. Then k' ∉ span_ℚ(relLattice) (else it would ⊥ kerSpanRat), in
  particular scaled-integer k'' ∉ relLattice, but k'' ⊥ ρ_ℓ for ℓ≠ℓ₀ hence k''·u = 0
  since u ∈ span of those ρ_ℓ over ℝ... wait no: k''·u = Σ_ℓ c_ℓ (k''·ρ_ℓ) = 0. So
  k'' IS a relation of u — contradiction. Good.

Status: starting exploration of mathlib API.

## Analysis session 1 — API found, thm4 SUSPECTED FALSE

### Key mathlib API (all confirmed present in v4.34)
- `linearIndependent_algebraMap_comp_iff` (LinearAlgebra/LinearIndependent/BaseChange.lean:46):
  `LinearIndependent S (fun i ↦ algebraMap R S ∘ v i) ↔ LinearIndependent R v` for
  `v : ι → ι' → R`, R comm ring, S domain+algebra+faithful — gives ℚ-lin-indep of rational
  vectors ⟹ ℝ-lin-indep of casts. THE (★) lemma.
- `Module.Basis.extend (hs : LinearIndepOn K id s) : Basis (hs.extend (subset_univ s)) K V`
  + `Basis.extend_apply_self`, `coe_extend`, `LinearIndepOn.subset_extend` (s ⊆ extend).
- `LinearIndependent.linearIndepOn_id : LI R v → LinearIndepOn R id (range v)`.
- `Module.Free.chooseBasis`, `Module.Finite.finite_basis : Finite ι`.
- `Submodule.exists_le_ker_of_notMem` (Basis/VectorSpace.lean:306):
  `v ∉ p → ∃ f : V →ₗ[K] K, f v ≠ 0 ∧ p ≤ ker f` — functional existence, both for the
  φ : ℝ →ₗ[ℚ] ℚ trick AND thm4 construction.
- `LinearMap.exists_extend`, `exists_extend_of_notMem`.
- `Finsupp.mem_span_image_iff_linearCombination`, `Submodule.mem_span_set`.
- `exists_rat_btwn`, `Rat.denseRange_cast` for thm2 perturbation.
- `LinearMap.pi`, `LinearMap.proj`, `Finsupp.lapply`, `Basis.repr_self`.

### kernel_coords_linearIndependent is FALSE as stated (countermodel found)
Hypotheses only require `kerSpanRat u ≤ span ℚ (range ρ)` — ρ need NOT lie in kerSpanRat
and need NOT be independent, so the representation `u = Σ c ρ` is non-unique and c can be
chosen rationally dependent.

Countermodel A (n=3, d=2, ρ even independent):
- u = ![1,1,0]; relLattice = {(m,−m,p)}; kerSpanRat = {x : x₀=x₁, x₂=0} = span{(1,1,0)}.
- ρ = ![![0,0,1], ![1,1,1]] (linearly independent); span ρ ∋ (1,1,0) ✓ hρspan.
- c = ![−1,1]; hc : u = −ρ₀ + ρ₁ = (1,1,0) ✓.
- ¬LI ℚ c : relation b = ![1,1] gives −1+1 = 0.

Countermodel B (n=2, d=2, span ρ = kerSpanRat exactly, ρ dependent):
- u = ![1,1]; kerSpanRat = span{(1,1)}; ρ = ![![1,1],![2,2]]; c = ![1/2,1/4].
- hc : u = (1/2)(1,1)+(1/4)(2,2) = (1,1) ✓. ¬LI : b = ![1,−2].

Minimal fix needed: add `hρmem : ∀ ℓ, ρ ℓ ∈ kerSpanRat u` AND `hρind : LinearIndependent ℚ ρ`
(then ρ is a genuine basis of kerSpanRat; proof goes through via
`u ∈ span_ℝ σ(W')`, `W' = span{ρ'ℓ} ⊊ kerSpanRat` since ρ₀∉W',
`exists_le_ker_of_notMem` gives functional f ⊥ W' with f(ρ₀)≠0, dot-kills u
contradicting ρ₀ ∈ kerSpanRat — clears denominators to integer relation).
Will build the countermodel in Lean to confirm, then flag for orchestrator.

### Proof plan for the 3 true theorems
thm1 `kerSpan_eq_span_rat`: ⊇ trivial. ⊆ : basis e of kerSpanRat, `Basis.extend` to basis B
of ℚⁿ; σ∘B spans ℝⁿ (δᵢ = σ(Σ B.repr δᵢ) trick) so `x = Σ c_i • σ(B_i)`; for `c_i ≠ 0` with
`B_i ∉ range e`, apply φ : ℝ →ₗ[ℚ] ℚ with φ(c_i)=1 (scale exists_le_ker_of_notMem);
`x_φ := coordwise φ` lands in kerSpanRat = span(range e), but `x_φ = Σ φ(c_j) • B_j` has
B-coordinate φ(c_i)=1 at index i — contradiction via B.repr support ⊆ B⁻¹'(range e).
thm2: u ∈ span σ(kerSpanRat) ⇒ u = Σ c_s σ(s) finite; r = Σ q_s s for rational q_s ≈ c_s;
r ∈ kerSpanRat (submodule closed); positivity open ⇒ preserved for |q_s−c_s| small.
thm3: contrapositive — if kerSpanRat ⊆ ℚ∙r then u ∈ ℝ∙σr contradicting h.
