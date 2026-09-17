# PLAN_M3 — Full real-speeds LRC(5) + tier-up roadmap

Status: **planning complete, ready to start**. Recon: 3 background agents + direct reading of
BHK (EJC 2001 #R3, downloaded to `_external/bhk.pdf`/`bhk.txt`) + cloned
`ElVec1o/five-distance-sharp` (v4.30, sorry-free) to `_external/`.

## 0. Prior-art verdict (final)

- LRC n=6, n=7: **zero formalizations in any proof assistant** (Lean/Isabelle/Coq/HOL/Mizar).
  Either would be a world-first. `formal-conjectures` still only has sorry'd statements.
- Multidim Kronecker / flow-orbit density / subtorus classification: **missing from mathlib**
  and no open PRs. Only an axiom'd Weyl statement in an unrelated repo exists.
- Simultaneous Dirichlet: **not in mathlib**, but two sorry-free Lean artifacts exist —
  `five-distance-sharp/ThreeGap/SimultaneousDirichlet.lean` (~120 lines self-contained
  pigeonhole, cloned) and mathlib's own `NormedAddCommGroup.exists_norm_nsmul_le`
  (WellApproximable.lean:322) which gives it on `UnitAddTorus (Fin d)` in ~100-200 lines.
- Computational line (Rosenfeld/Trakulthongchai k=7..13): all unverified C++; nothing
  kernel-checkable anywhere. Our work does not duplicate theirs.

## 1. The BHK Lemma 8 mechanism (verified against the paper)

Statement (instantiated to our case): fix δ ∈ (1/5, 1/4). If every 3 positive rationals admit
t>0 with `{t·vᵢ} ∈ (δ,1−δ)`, then for any 4 positive reals u₁..u₄ with some irrational ratio
uᵢ/uⱼ, ∃t>0 with `{t·uᵢ} ∈ (δ,1−δ) ⊆ (1/5,4/5)` — the slack eats the boundary problem that
killed the naive Dirichlet+compactness attempt.

Proof skeleton (BHK §4, reconstructed from `bhk.txt` lines 617–710):

1. `M(u) = {y ∈ ℝ⁴ : ∃t, y ≡ t·u mod ℤ⁴}`; goal ⇔ `M̄(u) ∩ (δ,1−δ)⁴ ≠ ∅`.
2. Kronecker–Perron: `M̄(u) = Ker(A) + ℤ⁴`, A = maximal rational relation matrix
   (rows = ℚ-basis of `{k ∈ ℚ⁴ : Σkᵢuᵢ = 0}`). If A = 0 (independent case) → M̄ = ℝ⁴, done.
3. u ∈ Ker(A) positive + A rational ⇒ ∃ r ∈ Ker(A)∩ℚ⁴ positive (perturb rational coeffs of u).
4. u not ∝ rational vector ⇒ dim Ker(A) ≥ 2 ⇒ ∃ s ∈ Ker(A)∩ℚ⁴, s ∦ r.
5. i := argmin sₖ/rₖ, j := argmax; then `w := (rᵢ+rⱼ)·s − (sᵢ+sⱼ)·r` satisfies
   wᵢ = −wⱼ and **wₖ ≠ 0 for all k** (wₖ=0 ⟺ sₖ/rₖ strictly between the extremal ratios — ⊥).
   (Note: the PDF's (19) renders `≠` as `=`; the argument forces all-nonzero.)
6. Distinct values of {|wₖ|} number ≤ 3 (wᵢ = −wⱼ collapses one); pad to exactly 3 positive
   rationals; apply the n−1 hypothesis ⇒ ∃t with `{t·wₖ} ∈ (δ,1−δ)` ∀k
   ({−x} = 1−{x} handles the sign).
7. `t·w ∈ Ker(A)` ⇒ `frac(t·w) ∈ M̄(u) ∩ (δ,1−δ)⁴`. ∎

**Consequence for the DAG**: the n−1 hypothesis is only ever fed *rational* 3-tuples ⇒ we need
`lrc4_int` (3 distinct positive integers, threshold 1/4) — NOT the full real n=4 theorem.

## 2. Phase M3 work packages (target: `lonely_runner_five`, real speeds)

### W5: `lrc4_int` — NEW hidden prerequisite (~300–500 lines, easy-medium)
Renault's appendix s=3 proof (mod-4 finite residue enumeration, same character as our
`digit_chase`): at `t = m/4`, runner unsafe iff `4 | m·vᵢ`; residues mod 4 force a short case
list; secondary time kills survivors. Plus rational bridge (`lrc4_rat`) cloned from
`lrc5_rel_rat` structure. Can also try deriving via B-S |D|=2 warmup-style direct argument —
whatever is shortest. **Agent-confirmed detail pending** (literature agent still verifying
Renault's exact case list; fallback = prove directly, it's small).

### W6: Relation-lattice API (~300–500 lines, low-medium)
- `relLattice (u : ι → ℝ) := LinearMap.ker (Fintype.linearCombination ℚ u)` as ℚ-submodule.
- Freeness/finiteness of the ℤ-kernel (`Submodule.module_free` PID chain), rank bookkeeping.
- `minRatSpan u := ker`-annihilator subspace = smallest ℚ-subspace containing u; the
  ℚ-basis {r_ℓ} of `minRatSpan`; u = Σ c_ℓ r_ℓ with c_ℓ ℝ-coefficients.
- **Minimality lemma**: {c_ℓ} ℚ-independent (else u lies in a proper ℚ-subspace ⇒ bigger
  relation lattice, contradicting maximality of A).
- Positive rational kernel vector from positive u (rational perturbation of coefficients).

### W7: Flow Kronecker — the analytic crux (~800–1500 lines, hard)
`{c_ℓ : Fin d → ℝ}` ℚ-independent ⇒ `{t·c mod ℤ^d : t ∈ ℝ}` dense in `UnitAddTorus (Fin d)`.
- d=1: trivial (nonzero slope hits everything).
- Candidate routes: (a) multidim pigeonhole on a long segment (Hardy–Wright-style);
  (b) ℤ-orbit density on the *subtorus* after basis change — careful: ℤ-orbit has extra
  integer-sum relations, so must parametrize the subtorus first (W6 gives the basis) and
  then need ℤ-Kronecker in the internal coords where {c_ℓ} indep gives density via
  `ergodic_add_left_iff_denseRange_zsmul` + Fourier on `UnitAddTorus`
  (`mFourierBasis`, `orthonormal_mFourier` — all in mathlib).
  Route (b) is likely cheapest given `ergodic_add_left_iff_denseRange_zsmul` exists.

### W8: Orbit-closure density, ⊇ direction (~400–800 lines, medium)
`closure {t·u mod ℤ⁴} ⊇ {y : ∀k, Σkᵢuᵢ = 0 → Σkᵢyᵢ = 0}` — parametrize the annihilator
subtorus by the W6 basis {r_ℓ}, pull back to flow Kronecker on T^{dim}. (⊆ direction is
trivial continuity; only ⊇ is needed.)

### W9: BHK Lemma 8 assembly for n=5 (~400–600 lines, medium bookkeeping)
Steps 3–7 of §1 in Lean: extremal-ratio indices over `Fin 4`, the w construction,
distinct-magnitude bound `({|wₖ|}).card ≤ 3`, pad to 3 rationals, apply `lrc4_rat` at δ,
`frac(t·w) ∈ M̄` via W8, extract the orbit-approximating real time via density+openness.

### W10: Final assembly + audit (~300–500 lines, easy)
`lonely_runner_five (v : Fin 5 → ℝ) (hv : Injective v)`:
Galilean → 4 relative speeds wⱼ = vⱼ − vᵢ (Fin.succAbove, reuse LRC5/Main pattern);
case split: all ratios rational → clear denominators → `lrc5_int`; else W9.
Update `Audit.lean`, `#print axioms`, zero-sorry gate, JOURNAL/STATEMENT sync.

**M3 total estimate: ~2.5–4k lines, 6 work packages.** W5 ∥ W6 ∥ W7 parallelizable
(W7 depends only on mathlib); W8 needs W6+W7; W9 needs W5+W6+W8; W10 last.

## 3. Phase T — tier-up after M3 (ordered by ROI)

| Order | Item | Est. | Why |
|---|---|---|---|
| T1 | **κ(V) finite-check formula** `κ(V) = max_{N=v+v'} κ_N(V)/N` | ~0.8–1.5k | Cheapest; standalone metatheorem ⇒ per-instance decidability certificate; "most mathlib-shaped" deliverable; Haralambis/Czerwiński–Grytczuk, unformalized |
| T2 | **p-general refactor** of Discrete/Filtering (`(p:ℕ)[Fact p.Prime]`, per-element forbidden sets F_d, top-level Λ_m stage) | ~0.7–1.3k | Required by T4 anyway; also the upstreamable PFL artifact |
| T3 | **n=6 via Renault** (Discrete Math 287, 9pp; mod-6 residue classes + interval bookkeeping) | ~2–3.5k | World-first; produces `lrc6_int` which T4 needs as an internal lemma (B-S §4 reduction invokes |D′|≤5 case) |
| T4 | **n=7 via Barajas–Serra main theorem** (§§4–6, ~9 dense pp; ℤ₇ case analysis + compression via PFL-on-differences) | ~5.5–8k | World-first; formalizes an actual 2008 research paper — the JFR-grade item |
| ✗ | n=6 via BHK torus method | ~12–20k | Not worth it; Renault route strictly better |

Not blocked by M3: T1, T2 can start immediately in parallel with M3.
T3/T4 each deliver integer+rational versions; their real-speeds versions ride on W7–W10
infrastructure (BHK Lemma 8 generalizes: n=6 real needs n=5 rational — we have it; n=7 real
needs n=6 rational — T3 delivers it).

## 4. Publication shape (after M3 + T1..T3 minimum)

- Workshop/JFR paper: "first kernel-verified LRC n≥4; BHK real→integer reduction formalized;
  reusable Kronecker-on-subtori + prime-filtering library; multi-agent blueprint pipeline".
- Mathlib PR candidates: simultaneous Dirichlet on UnitAddTorus, flow-Kronecker/subtorus
  density, p-general prime filtering lemma, κ(V) decidability.
- formal-conjectures: link our theorem to their sorry'd statement.

## 5. Risks

- W7 flow-Kronecker is the only deep analytic piece; if Fourier route stalls, elementary
  Hardy–Wright pigeonhole route is the fallback (more lines, fewer dependencies).
- W9's density→open-set argument needs `IsOpen` of the cube + `Dense` def unfold — standard
  but fiddly real-analysis bookkeeping.
- Statement fidelity hazard: BHK's M(u) lives in ℝ⁴ (covering space) not T⁴ — keep both
  pictures straight; the `frac`/`Int.fract` API is the bridge.
- Renault s=3 case list unverified (paywall) — W5 budget has slack; direct proof acceptable.
