# Verified Lonely Runner Conjecture — n = 3, 4, 5, 6, 7

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.22851977.svg)](https://doi.org/10.5281/zenodo.22851977)
[![SWH](https://archive.softwareheritage.org/badge/swh:1:snp:8e220024403049ac000bde7c29a3f23151054eb2/)](https://archive.softwareheritage.org/swh:1:snp:8e220024403049ac000bde7c29a3f23151054eb2)

Kernel-checked Lean 4 + Mathlib formalization of the Lonely Runner
Conjecture (LRC) for up to seven runners — including, to our knowledge,
the largest verified instance of a full LRC case over **arbitrary real
speeds**.

*Toolchain:* `leanprover/lean4:v4.34.0` · *License:* Apache 2.0

## Main results

| Theorem | Statement |
|---|---|
| `lonely_runner_three` | LRC for 3 runners, arbitrary real speeds |
| `lrc4_int` | LRC for ≤ 3 distinct integer speeds + 1 stationary runner (n = 4) |
| `lrc4_rat_finset` | n = 4, rational speeds |
| `lrc5_int` | LRC for ≤ 4 distinct integer speeds + 1 stationary runner (n = 5) |
| `lonely_runner_five` | **n = 5, arbitrary real speeds** |
| `lrc6_int` | LRC for ≤ 5 distinct integer speeds + 1 stationary runner (n = 6) |
| `lonely_runner_six` | **n = 6, arbitrary real speeds** |
| `lrc7_int` | LRC for ≤ 6 distinct integer speeds + 1 stationary runner (n = 7) |
| `lonely_runner_seven` | **n = 7, arbitrary real speeds** |

Each level also ships its relational and rational wrappers
(`lrc*_rel_rat`, `lrc*_rat_finset`, `lonely_runner_*_rat`; for
n = 5, 6, 7 additionally `lrc*_rel_real`). All statements use circular
distance on `ℝ/ℤ` (`UnitAddCircle`) and match the statement family of
the DeepMind *formal-conjectures* repository, whose LRC entries remain
unproved (`sorry`).

## Proof architecture

- **Real speeds (n = 5, 6, 7)** := BHK Lemma 8 (Bohman–Holzman–Kleitman,
  *Duke Math. J.* 2004), instantiated once per dimension
  (`LRC{5,6,7}/…/RealCase.lean`): either the relative speeds share a
  common ratio (reduce to the rational case) or an equal-coordinates
  kernel vector plus a Kronecker-type density argument pushes a runner
  to loneliness directly.
- **n = 7 integer** := Barajas–Serra (2008, EJC 15(1) R48): 7-adic
  valuation decomposition; the `|A₀| ≤ 3` finite case (§7), the
  four-unit case (§5), and the five-units-plus-one-element case (§6)
  split into six digit-pattern cases `case61`–`case66`, discharged by
  explicit finite certificates.
- **n = 6 integer** := Renault's (2004) parity/residue case split.
- **n = 5 integer** := the prime-filtering argument of Barajas–Serra,
  tracking base-5 digits.
- **n = 4 integer** := the appendix argument of Renault: push a safe
  time to a finite boundary set, take the extremizer, and re-enter at a
  half-integer shift.
- **n = 3 real** := covering argument à la Wills (1967).

### Reusable infrastructure

- `SimDirichlet.*` — simultaneous Dirichlet approximation on `ℝᵈ` via
  pigeonhole (self-contained, ~190 lines).
- `flow_orbit_dense` — flow-version Kronecker: ℚ-independence of speeds
  implies density of the one-parameter orbit in `ℝᵈ/ℤᵈ`, proved through
  ergodicity and a Fourier (`mFourier`) L² argument.
- `subtorusMap_range_eq_annihilator` — subtorus/annihilator
  characterization `M̄(u) = Ker(A) + ℤᵈ` via saturated ℤ-submodules and
  dual functionals.
- `orbit_dense_annihilator` — Kronecker–Perron orbit-closure statement.

## Verifying it yourself

```bash
# requires elan (https://elan.lean-lang.org)
lake build
```

The umbrella import `Research07.lean` includes `Research07/Audit.lean`,
which runs `#print axioms` over every exported theorem. All results
depend only on the standard axioms
`[propext, Classical.choice, Quot.sound]` — no `sorry`, `native_decide`,
`unsafe`, or custom axioms.

`STATEMENT.md` audits the *statements* themselves (the part the kernel
cannot check): a symbol-by-symbol comparison against the informal
proposition, including cases where countermodel checking caught
incorrect initial statements before they could ship.

## Repository map

```
Research07/
  Audit.lean      axiom gate over all exported theorems
  LRC3/           n = 3 (real speeds)
  LRC4/           n = 4 (integer + rational)
  LRC5/           n = 5 (integer + rational + real)
  LRC6/           n = 6 (integer + rational + real)
  LRC7/           n = 7 (integer + rational + real)
  M3/             BHK reduction machinery:
                  relations lattice, subtorus, Dirichlet,
                  flow Kronecker, orbit closure
STATEMENT.md      statement-fidelity audit vs the literature
```

## Provenance

Developed by Honglu Chen (Nanjing University) with an AI-agent-assisted
pipeline: frozen statements, parallel subagents, countermodel-driven
statement review, and a comprehensive axiom gate. Statement fidelity was
verified against the primary literature (Wills 1967; Renault 2004;
Bohman–Holzman–Kleitman 2004; Barajas–Serra 2008).

## Citing

Archived on Zenodo: <https://doi.org/10.5281/zenodo.22851977>
(concept DOI resolves to the latest release). If you use this work,
please cite the DOI and note the Lean toolchain version
(`leanprover/lean4:v4.34.0`) for reproducibility; see `CITATION.cff`
for full metadata.
