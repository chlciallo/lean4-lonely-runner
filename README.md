# Verified Lonely Runner Conjecture — n = 3, 4, 5

Kernel-checked Lean 4 + Mathlib formalization of the Lonely Runner
Conjecture (LRC) for up to five runners, including — to our knowledge —
the first verified instance of a full LRC case over **arbitrary real
speeds**.

*Toolchain:* `leanprover/lean4:v4.34.0` · *License:* Apache 2.0

## Main results

| Theorem | Statement |
|---|---|
| `lonely_runner_three` | LRC for 3 runners, arbitrary real speeds |
| `lrc4_int` | LRC for ≤ 3 distinct integer speeds + 1 stationary runner (n = 4) |
| `lrc4_rat_finset` | n = 4, rational speeds |
| `lrc5_int` | LRC for ≤ 4 distinct integer speeds + 1 stationary runner (n = 5) |
| `lonely_runner_five_rat` | n = 5, rational speeds |
| **`lonely_runner_five`** | **n = 5, arbitrary real speeds** — via the BHK reduction |

All statements use circular distance on `ℝ/ℤ` (`UnitAddCircle`) and match
the statement family of the DeepMind *formal-conjectures* repository,
whose LRC entries remain unproved (`sorry`).

## Proof architecture

- **n = 5 real** := BHK Lemma 8 (Bohman–Holzman–Kleitman, *Duke Math. J.*
  2004): either the relative speeds share a common ratio (reduce to the
  rational case) or a Kronecker-type density argument pushes a runner to
  loneliness directly.
- **n = 5 integer** := the prime-filtering argument of Barajas–Serra
  (2008), tracking base-5 digits.
- **n = 4 integer** := the appendix argument of Renault (2004): push a
  safe time to a finite boundary set, take the extremizer, and re-enter
  at a half-integer shift.
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
proposition, including two cases where countermodel checking caught
incorrect initial statements before they could ship.

## Repository map

```
Research07/
  Audit.lean      axiom gate over all exported theorems
  Basic.lean      shared utilities
  LRC3/           n = 3 (real speeds)
  LRC4/           n = 4 (integer + rational)
  LRC5/           n = 5 (integer + rational + real assembly)
  M3/             BHK reduction machinery:
                  relations lattice, subtorus, Dirichlet,
                  flow Kronecker, orbit closure
_reports/         incremental work logs (statement-fidelity records)
```

## Provenance

Developed by Honglu Chen (Nanjing University) with an AI-agent-assisted
pipeline: frozen statements, parallel subagents, countermodel-driven
statement review, and a comprehensive axiom gate. Statement fidelity was
verified against the primary literature (Wills 1967; Renault 2004;
Bohman–Holzman–Kleitman 2004; Barajas–Serra 2008).

## Citing

If you use this work, please cite the repository and note the Lean
toolchain version (`leanprover/lean4:v4.34.0`) for reproducibility.
