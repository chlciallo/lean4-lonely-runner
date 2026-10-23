# Sharp local two-speed avoidance and certified descent

Research note, 2026-10-24. General theorems below are kernel-checked in Lean 4.34.0. Priority and publication assessment remain provisional.

## 1. Statement and scope

Write `||x|| = min_{m in Z} |x-m|`. For positive thresholds α, β with α+β ≤ 1/2, define

\[
C(\alpha,\beta)=\max\left\{\alpha+\beta,
\frac{\alpha(1+2\beta)}{1-2\beta}\right\}.
\]

**Theorem 1 (sharp local radius).** For every pair of real speeds `0<a≤b`, phases `x,y`, and reference time `t₀`, there is a time t such that

\[
|t-t_0|\le \frac{C(\alpha,\beta)}{a},\qquad
\|at+x\|\ge\alpha,\qquad \|bt+y\|\ge\beta.
\]

The constant C is optimal **uniformly over all real ratios b/a≥1 and all phases**. This is a local waiting-radius statement. It is not a statement that the same constant is optimal for a specified integer speed pair, for equal initial phases, or for a specified lower-dimensional core.

Lean: `two_speed_escape_explicit` proves existence for actual speeds; `uniform_radius_iff_explicit` proves the exact optimal normalized constant, including necessity.

The first expression dominates precisely when `2α+β≤1/2`. In particular,

\[
C(\delta,\delta)=2\delta\quad(0<\delta\le1/6),
\]

whereas for `1/6<δ≤1/4` the second expression dominates. The transition is a change in the topology of a possible bad component, not an artefact of numerical optimization.

## 2. Proof of the upper bound

Scale time so that the slower speed is 1; write ρ=b/a≥1. A slow bad interval is

\[
A_n=(n-\alpha-x,n+\alpha-x).
\]

The fast bad intervals have length `2β/ρ`, and their intervening gaps have length `(1−2β)/ρ`. A fast interval cannot bridge the entire gap between two slow bad intervals: its length is at most `2β≤1−2α`. Strictly bad intervals are open, so a mere endpoint contact does not join components.

Enclose a slow interval `(L,R)` by points l≤L and r≥R safe for the fast runner: if an endpoint is already safe, retain it; otherwise move outward to the nearest boundary of its fast bad interval. Each extension is at most `2β/ρ`. These enclosing points also remain safe for the slow runner, because `2β/ρ≤1−2α`.

If at most one endpoint extends, the enclosure has length at most

\[
2\alpha+2\beta/\rho\le2(\alpha+\beta).
\]

If both extensions belong to the same fast interval, the same bound suffices. Otherwise let the two fast interval indices differ by an integer m≥1. Their separation and their overlap with the slow interval give

\[
m-2\beta<2\alpha\rho,\qquad
\rho(r-l)=m+2\beta.
\]

Since m≥1 and β>0,

\[
(1-2\beta)(m+2\beta)
\le(1+2\beta)(m-2\beta).
\]

Consequently

\[
r-l<\frac{2\alpha(1+2\beta)}{1-2\beta}.
\]

Every bad point lies either in one of these enclosures or in a single fast interval with both endpoints slow-safe. To see this without an appeal to an infinite interval graph, take the fast bad interval containing the point. If one of its endpoints is slow-unsafe, use the enclosure of that slow interval; a safe enclosure endpoint cannot lie strictly inside the fast interval. Otherwise its own endpoints are safe for both runners.

We have therefore enclosed every bad point between jointly safe endpoints at distance at most 2C from one another. One endpoint lies within C of the point. Scaling back gives Theorem 1. These are the cases in `enclose_slow_block` and `two_speed_escape_normalized`; the proof in Lean constructs enclosing endpoints directly.

## 3. Optimality

Both mechanisms are necessary.

**Adjacent-interval obstruction.** Suppose K<α+β. Choose R with K<R<α+β, and take ρ=1. Choose phases so the two bad intervals are

\[
(-R,2\alpha-R),\qquad(R-2\beta,R).
\]

They overlap and cover `[-K,K]`, so radius K cannot work uniformly. Formally, `uniform_radius_sum_lower` proves K≥α+β.

**Bridging obstruction.** Any uniform radius must already satisfy K≥α+β>0. Suppose

\[
(1-2\beta)K<\alpha(1+2\beta).
\]

Choose

\[
\frac{1-2\beta}{2\alpha}<\rho<\frac{1/2+\beta}{K}.
\]

The interval is nonempty, and its left endpoint is at least 1 by α+β≤1/2. Take phases x=0, y=1/2. The slow bad interval `(-α,α)` overlaps the two adjacent fast bad intervals centred at `±1/(2ρ)`. Their union covers `[-K,K]`, because

\[
\rho\alpha>1/2-\beta,\qquad \rho K<1/2+\beta.
\]

This is `bridge_obstruction` and `uniform_radius_bridge_lower`. Thus the two inequalities characterizing K are both necessary and sufficient, establishing the maximum formula exactly.

## 4. A genuine decrease in the number of speeds

**Theorem 2 (two-speed deletion).** Let k≥5. Retain k−2 speeds uᵢ, with `|uᵢ|≤M`, and let the two deleted speeds satisfy

\[
0<a\le b,\qquad a\ge(k-1)M.
\]

Suppose the retained speeds have a time t₀ with

\[
\|u_i t_0+\phi_i\|\ge\frac1{k-1}\quad\text{for every retained }i.
\]

Then, for arbitrary phases of the deleted speeds, the full k-speed instance has a time with all distances at least `1/(k+1)`.

**Proof.** Put δ=1/(k+1)≤1/6. Theorem 1 finds a time within `R=2δ/a` of t₀ making the deleted pair safe. Each retained phase moves by at most MR. Distance to the nearest integer is 1-Lipschitz, and

\[
\frac1{k-1}-\frac{2M}{(k+1)a}\ge\frac1{k+1}
\]

under the stated separation. This proves the result. Lean declaration: `delete_two`.

There is no assumption of the full k-speed conjecture in this theorem. The premise concerns only k−2 speeds, at their natural LRC threshold. The formal statement allows arbitrary phases **conditional on that explicit core witness**; it does not assume that every shifted core possesses such a witness.

The more general `transfer_core` retains individual speeds and initial phases, and requires a margin `M R`. It is suitable for an interval certificate rather than just an existential isolated witness.

For example, `(1,2,3,12,13)` has the short relation `13−12=1`. Its retained core `(1,2,3)` is safe at radius 1/4 at t₀=1/4; M=3 and a=12 meet the deletion threshold. The time `19/72` gives full distances

\[
(19/72,17/36,5/24,1/6,31/72).
\]

The theorem applies for every k≥5 when the separation hypothesis holds. Iterating it decreases the number of speeds by two each time. It does not cover arbitrary short relations among comparable speeds.

### 4.1. A relation-aware improvement

There is a stronger statement when a retained short relation controls the relative phase.

**Theorem 3 (relative-phase window).** Let `0<δ≤1/2`, `0<a≤b`. If, at t₀,

\[
\|(b-a)t_0+y-x\|\ge 2\delta+|b-a|\frac{\delta}{a},
\]

then a time t exists within **δ/a** of t₀ such that both deleted speeds are δ-safe. This halves the phase-uniform small-threshold radius. The hypothesis is explicit and may fail; the theorem does not assert it for every short relation.

**Proof.** If both speeds are already safe, stop. Otherwise move an excluded runner to the nearest boundary of its forbidden interval. This costs at most δ/a, because both speeds are at least a. During that motion the relative phase changes by at most `|b−a|δ/a`, so its distance from the integers remains at least 2δ. At the chosen boundary the moved runner has distance exactly δ. The other runner must have distance at least δ: otherwise the triangle inequality would put their relative phase at distance strictly below 2δ. All phases are evaluated on the same time trajectory throughout. Lean: `relation_escape`.

**Corollary 4 (short-relation descent).** Let k≥4 and δ=1/(k+1). Suppose the retained k−2 speeds are bounded in absolute value by M and include a speed `uⱼ=b−a`, with its phase equal to `y−x`. If

\[
a\ge\frac{k-1}{2}M
\]

and **the same core witness t₀** satisfies both

\[
\|u_i t_0+\phi_i\|\ge\frac1{k-1}\quad\forall i,
\qquad
\|u_j t_0+\phi_j\|\ge 2\delta+|u_j|\frac{\delta}{a},
\]

then the full k-speed instance has a δ-safe time. The stronger requirement on coordinate j is essential. The theorem is `relation_delete_two`; its more general margin interface is `relation_delete`.

This is a **genuine k→k−2 reduction using the short relation** `b−a−uⱼ=0`, with half the uniform speed-separation threshold. It does not claim that the extra core guard follows from LRC(k−2).

Example: core `(1,2,3)`, deleted pair `(6,8)`, t₀=1/4, δ=1/6. The retained difference speed is 2 and its phase is 1/2, exceeding the required 7/18. The half-threshold condition holds with equality, while the phase-uniform bound `a≥12` fails. A lifted witness is `11/48`.

## 5. Countermodels that fix the statement

1. **A fixed core phase cannot always be lifted.** For speeds `(3,5,8)`, at every real time satisfying `8t=z+1/2`, z∈Z, at least one of the first two distances is below 1/4. The statement quantifying over all such real times is proved in `frozen_phase_counterexample`. The unrestricted time 1/11 works. A short relation alone therefore does not justify preservation of an isolated maximally safe phase.
2. **The 2δ radius stops at δ=1/6.** At a=3, b=5, δ=1/5, phases x=0,y=1/2, a bad component is `(-7/50,7/50)`. Its half-length exceeds `2δ/a=2/15`. The equivalent normalized obstruction is proved in `one_fifth_obstruction`.
3. **An attempted rotation-gap inequality fails.** The guess `rG≥1+||rC||` for the largest gap of `{0,C,…,(r−1)C}` fails for r=6,C=2/5. Here G=1/5, whereas `||6C||=2/5`. This rejected approach is not used in any theorem.
4. **The relative-phase drift term cannot be dropped.** At a=2, b=5, t₀=1/2 and δ=1/6, the relative phase has distance 1/2, so it exceeds 2δ. Nevertheless there is no jointly safe time within δ/a=1/12 of t₀. The slow runner is safe in that window only at its endpoints; the fast runner is unsafe at both. This is proved for all real times in `drift_allowance_needed`.

## 6. Prior art and novelty boundary

- Bohman–Holzman–Kleitman, [*Six Lonely Runners* (2001), Lemma 4](https://www.combinatorics.org/ojs/index.php/eljc/article/view/v8i2r3), already bound the bad components of two runners at threshold 1/6. The two-block geometry above follows that approach. The equal-threshold small-radius result is **not claimed as new**; extending that estimate to smaller δ is elementary.
- Fan–Sun, [*Amending the Lonely Runner Spectrum Conjecture*](https://arxiv.org/html/2306.10417v2#S3.SS1), Lemma 3.4 on arXiv / Lemma 15 in the journal, use a local displacement bound of 3δ/a to transfer a core witness to two fast runners. Theorem 2 gives a stronger sufficient condition than that particular displacement estimate at δ≤1/6, but this numerical comparison does not establish priority over all earlier literature.
- Jensen, [*Mixed thresholds in the Lonely Runner Conjecture*](https://arxiv.org/abs/2605.27941), studies the same-origin, global existence region for unequal thresholds and gives two-function integral formulas. Our exact statement instead quantifies over arbitrary phases and every starting time, and controls local distance in time.
- Beck–Everett, [*Lonely Runner Relations*](https://arxiv.org/abs/2609.06259), motivates retaining relation information. Their short-relation theorem does not supply the scale separation required here. We have not bridged that gap.

The candidate contribution is the **sharp mixed-threshold local envelope, its formal optimality proof, and the verified relation-aware transfer interface**. A targeted public search has not identified this exact formula, but the derivation is elementary and close to established interval methods. The phase-aware refinement is also elementary; formal verification alone does not establish new mathematics. Novelty and significance need further scrutiny. This checkpoint is not represented as a guaranteed Q2 paper or as a solution of the general conjecture.

## 7. Evidence

The updated standalone package passes `lake build` (1013 jobs including dependency tasks). Fifteen exported results have axiom reports containing only `propext`, `Classical.choice`, and `Quot.sound`. No proof holes, added axioms, native decision shortcuts, or unsafe declarations are used.

`probe_windows.py` checks 45,144 exact rational parameter choices, including unequal thresholds and near-degenerate configurations. The largest observed ratio of a bad-component length to the proved bound is 80/81. These experiments helped reject false extensions; the general conclusions and optimality rely on the Lean proofs, not on finite sampling.

`probe_relation.py` scans 80,784 rational phase/ratio/threshold choices. Exactly 25,812 meet the stated relative-phase guard; all have an exact local witness. The script also checks the drift counterexample and the `(1,2,3,6,8)` descent example. The other choices are outside the sufficient hypothesis, not alleged counterexamples to LRC.

Only the new standalone research package was built. The upstream fixed-person-count proof tree was not modified or rebuilt for this checkpoint.

## 8. Second checkpoint: closing the guard by deleting a sum triple

The earlier guarded pair theorem remains valid but its extra core condition is not automatic. The new [sum-triple theorem](TRIPLE_NOTE.md) instead removes the retained difference speed together with its pair. It gives the exact compatible-phase radius `max(5δ/2,δ(1+2δ)/(1−4δ))/d` for speeds `d,a,a+d`, and a guard-free `k→k−3` corollary for k≥7 under `d≥5(k−2)M/6`. Upper bound, both sharpness mechanisms, the actual deletion theorem, and a counterexample to independent phases are now proved in Lean. See the separate note for complete proofs and current literature checks.
