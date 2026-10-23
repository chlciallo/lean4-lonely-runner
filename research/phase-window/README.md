# Phase-window descent: research checkpoint

Status: first proved checkpoint, 2026-10-24. The general local theorem, its optimality and the deletion corollary are kernel-checked. This is not a proof of the general Lonely Runner Conjecture and not yet a submission-ready paper.

The goal is a genuine decrease in the number of speeds, with enough phase information retained to lift a witness. Exact preservation of a single core phase is already false: for speeds `(3,5,8)`, none of the times `(2j+1)/16` makes all three distances at least `1/4`, although the retained speed `8` is maximally safe. The time `1/11` works when the phase is allowed to move.

We therefore retain a **window with a quantified margin**. The current candidate is the sharp, phase-uniform local escape radius for two periodic families of forbidden intervals with unequal thresholds. A local two-speed theorem transfers to deletion of two speeds from an arbitrary core.

## Priority boundary

The equal-threshold bound at `delta = 1/6` is already contained in Bohman–Holzman–Kleitman, *Six Lonely Runners* (2001), Lemma 4. Its extension to smaller equal thresholds is elementary. We do **not** claim that bound as new. Fan–Sun's *Amending the Lonely Runner Spectrum Conjecture* (2026), Lemma 15 in the journal version / Lemma 3.4 on arXiv, gives a related two-fast-runner transfer. Jensen's *Mixed thresholds in the Lonely Runner Conjecture* (2026) studies unequal thresholds for same-origin global existence. The proposed exact local, arbitrary-phase envelope must be distinguished from these results and checked further for priority.

## Proved results

For positive thresholds `α+β≤1/2`, the exact uniform local radius for ordered speeds `0<a≤b` and arbitrary phases is

`max(α+β, α(1+2β)/(1−2β)) / a`.

The upper bound and both necessary inequalities are proved for general real parameters in Lean. At equal thresholds `δ≤1/6`, the radius is `2δ/a`.

This yields a true `k → k−2` deletion theorem: for `k≥5`, if the retained speeds have absolute value at most `M`, have a witness at radius `1/(k−1)`, and the deleted speeds satisfy `0<a≤b`, `a≥(k−1)M`, then the full instance has a witness at radius `1/(k+1)`.

**Short-relation refinement:** if a retained speed is `b−a` and its phase at the same core witness has distance at least `2δ+|b−a|δ/a`, the escape radius is only `δ/a`. At `δ=1/(k+1)`, this gives a verified `k → k−2` reduction under `a≥(k−1)M/2` plus that explicit relative-phase guard. The core `(1,2,3)` and deleted pair `(6,8)` are an exact example where this criterion applies and the uniform criterion does not.

- [Full mathematical note and priority discussion](NOTE.md)
- [中文阶段报告](STATUS.zh-CN.md)
- [General optimality theorem](PhaseWindow/Sharpness.lean)
- [Actual dimension-decreasing theorem](PhaseWindow/Descent.lean)
- [Short-relation descent](PhaseWindow/Relation.lean)
- [Countermodels, including all real times in the frozen fibre](PhaseWindow/Counterexamples.lean)

Publication strength and novelty remain open research questions; no journal acceptance or quartile is guaranteed.

## Reproduce

This is an independent Lake package inside the repository. From this directory, with elan installed:

```sh
lake exe cache get
python verify.py
```

Lean is pinned to 4.34.0. The committed Lake manifest pins Mathlib to `5ed2965256430c3649e86755f9576b54eca72435` and fixes transitive dependencies. On a fresh checkout Lake fetches the dependencies. The verification script builds this package, audits eleven exported theorems, rejects proof holes and nonstandard proof declarations, and runs the exact rational experiment suite.

The checked package contains 27 theorem declarations across six proof modules. The axiom audit of the eleven main outputs only reports the standard foundational axioms. The window experiments cover 45,144 rational parameter choices; a separate scan checks all 25,812 guard-admissible cases among 80,784 phase/ratio choices; they are cross-checks, not substitutes for the parameterized Lean proofs.

Only this package is built. The upstream fixed-person-count proof tree is unchanged.
