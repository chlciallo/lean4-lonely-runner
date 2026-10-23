# Sharp local escape for a compatible sum triple

Research checkpoint, 2026-10-24. All theorem statements below concerning the local radius and three-speed deletion are proved in Lean. Priority is provisional. This is not a proof of the general Lonely Runner Conjecture (LRC).

We write `||x|| = dist(x,Z)`. The parameter k counts nonzero relative speeds, hence the LRC target is `1/(k+1)`.

## 1. Main theorem

Let `0<δ≤1/6`, `0<d≤a`, and let x,y,t₀ be arbitrary real numbers. There is a real t such that

\[
|t-t_0|\le \frac{C_3(\delta)}d,\qquad
\|dt+x\|,\ \|at+y\|,\ \|(a+d)t+x+y\|\ge\delta,
\]

where

\[
C_3(\delta)=\max\left\{\frac{5\delta}{2},
\frac{\delta(1+2\delta)}{1-4\delta}\right\}.
\]

This is the **exact smallest uniform constant** when quantified over all real ratios a/d≥1, all compatible phases x,y,x+y, and every reference time. This quantifier includes a=d; we do not assert that every distinct integer triple, or every common-origin instance, attains the worst case. Compatibility modulo integers also suffices, by integer translation invariance of distance.

Lean: `triple_escape`, `uniform_triple_radius_iff`. The transition is at δ=1/8:

| Threshold range | C₃(δ) |
|---|---|
| 0<δ≤1/8 | 5δ/2 |
| 1/8≤δ≤1/6 | δ(1+2δ)/(1−4δ) |

In particular C₃(1/6)=2/3, C₃(1/7)=3/7, and C₃(1/8)=5/16.

## 2. Endpoint construction

Normalize d=1 and put ρ=a/d≥1. After centering one slow forbidden interval at zero and removing integer shifts, the three phases become

\[
u,\quad \rho u+Y,\quad (\rho+1)u+Y.
\]

Set η=(ρ+2)δ and let j be the largest integer strictly below Y+η, so `j<Y+η≤j+1`. Define

\[
r=\max\left\{\delta,\frac{j-Y+\delta}{\rho}\right\}.
\]

Then δ≤r≤4δ, and r is safe for all three phases:

- If r=δ, the inequality `j+δ≤ρδ+Y`, together with `Y+(ρ+2)δ≤j+1`, places both fast phases in `[j+δ,j+1−δ]`.
- Otherwise `ρr+Y=j+δ`. The third phase is `j+δ+r`, which is in the same safe cell because r≤4δ and 6δ≤1. Also δ≤r≤4δ≤1−δ makes the slow phase safe.

Reflecting this construction gives a safe left endpoint l≤−δ with l≥−4δ. If either endpoint is exactly ±δ, their separation is at most 5δ.

Otherwise both endpoints are fast boundaries. Writing their integer separation as m, we have

\[
\rho(r-l)=m+2\delta,\qquad m-4\delta<2\rho\delta.
\]

If m≤0, the width is at most 2δ. If m≥1, the elementary identity

\[
(1+2\delta)(m-4\delta)-(1-4\delta)(m+2\delta)
=6\delta(m-1)\ge0
\]

gives

\[
r-l<\frac{2\delta(1+2\delta)}{1-4\delta}.
\]

Thus every slow forbidden interval is enclosed by jointly safe endpoints at distance at most 2C₃(δ) from each other. Lean: `triple_right`, `enclose_triple`.

## 3. From one forbidden interval to every reference time

The existing two-speed theorem gives a point s within `2δ/ρ≤C₃(δ)` of t₀ where the two fast phases are safe. If the slow phase is also safe, stop. Otherwise s lies in a slow forbidden interval. Apply the preceding enclosure to obtain jointly safe endpoints l≤s≤r with `r−l≤2C₃(δ)`.

One of these endpoints is within C₃(δ) of t₀. If t₀ lies inside [l,r], use the width bound; if it lies outside, the nearer endpoint is between t₀ and s and hence no farther than s. This completes the upper bound. All translations use the same time variable, preserving the sum relation. Lean: `endpoint_choice_near`, `triple_escape_normalized`.

## 4. Sharpness

Two obstruction families force the two terms independently.

**Three adjacent intervals.** Take ρ=1, slow phase 0, and both other phases −D, with D<3δ approaching 3δ. The forbidden intervals centered at 0, D/2, D have radii δ, δ/2, δ and overlap. They cover `(-δ,D+δ)`, whose half-length approaches 5δ/2. Lean: `triple_radius_linear_lower`.

**A symmetric five-interval chain.** Take slow phase 0 and both fast phases 1/2. For

\[
\rho>\frac{1-4\delta}{2\delta}\ge1,
\]

the forbidden intervals form a chain in the order B,C,A,C,B covering

\[
\left(-\frac{1/2+\delta}{\rho},\frac{1/2+\delta}{\rho}\right).
\]

Letting ρ decrease to the displayed threshold forces the second term of C₃. One direct way to check the positive half is: safety of A would imply t≥δ; safety of B inside the proposed interval would imply ρt≤1/2−δ; safety of C would imply `(ρ+1)t≥1/2+δ`. Hence t≥2δ, contradicting the bound on ρ. The negative half follows by reflection. Lean: `triple_bridge_obstruction`, `triple_radius_bridge_lower`.

## 5. Actual k→k−3 reduction

Let k≥7. Retain k−3 speeds uᵢ with `|uᵢ|≤M`, and suppose their phases have a common witness t₀ at the smaller problem's natural threshold `1/(k−2)`. Delete the triple d,a,a+d, with compatible phases, satisfying

\[
0<d\le a,\qquad d\ge\frac{5(k-2)}6 M.
\]

Then the full k-speed instance has a witness at threshold `1/(k+1)`.

Indeed, δ=1/(k+1)≤1/8, so the triple escape radius is `R=5δ/(2d)`. Every retained phase moves by at most MR, while

\[
\frac1{k-2}-\delta=\frac{3\delta}{k-2}\ge MR.
\]

The 1-Lipschitz property of distance to the nearest integer preserves all retained constraints. Lean: `delete_sum_triple`.

Unlike the previous guarded pair reduction, **there is no additional marked-core-phase hypothesis**. The difference speed d is removed together with the two others. The price is a specific sum triple and scale separation. Core phases may be arbitrary conditional on the stated witness; we never assume a general shifted LRC.

Example: core `(1,2,3,4)`, M=4, t₀=1/5. Delete `(17,18,35)`. Since 17≥50/3, the new reduction applies. The exact lifted witness `11/56` makes all seven distances at least 1/8. The previous uniform pair condition would require `18≥6·17`, and the guarded pair separation would require `18≥3·17`; both fail.

This comparison is to the two earlier sufficient criteria in this package, not a claim that no existing LRC theorem handles the example.

## 6. An unbounded recursive family

Starting from `(1,2,3,4)`, let m be the current number of speeds and M their maximum. Append

\[
d=\left\lceil\frac{5(m+1)M}{6}\right\rceil,\quad a=d+1,\quad b=2d+1.
\]

The new size is k=m+3, and the separation inequality holds by construction. Since m≥4, these are three new, distinct, larger positive integers. Induction using `delete_sum_triple` therefore gives the LRC conclusion for every depth of this construction, not just the first few sizes. This recursive-family induction is described mathematically here; the standalone quantified deletion theorem is the Lean-checked component.

`probe_descent.py` constructs the first 20 layers (ending with 64 nonzero speeds), finds exact rational lifts, and independently checks every speed at every layer. The small example is followed by `(234,235,469)` and `(4300,4301,8601)`. Each layer fails the separation part of both previous pair criteria. The experiment is an application certificate, not evidence that arbitrary 64-speed sets satisfy LRC.

For a sorted positive instance satisfying this separation, the removed triple must be the three largest speeds. Thus recognizing successive admissible deletions needs only a linear number of relation/separation checks after sorting. This statement counts arithmetic comparisons; it is not a bit-complexity claim for arbitrary LRC. The dimension decreases by three at each accepted step. General configurations need not admit any step.

## 7. Why the phase hypothesis is mathematical content

If the three initial phases are independent, the bound fails. At δ=1/9, speeds `(1,9/8,17/8)` and phases `(0,1/12,7/12)` have a forbidden component

\[
(94/153,182/153).
\]

Its half-width is 44/153, strictly larger than C₃(1/9)=5/18. At reference time 46/51 there is no safe point within 5/18. The all-real-times obstruction is proved by `incompatible_triple_counterexample`; it is not just a numerical grid observation.

## 8. Priority and current research boundary

- BHK's [*Six Lonely Runners* (2001)](https://www.combinatorics.org/ojs/index.php/eljc/article/view/v8i2r3), Lemma 4, supplies the classical two-block method. We use its parameterized two-speed analogue as an input. The equal-threshold two-speed estimate is not new.
- The exact mixed-threshold two-speed formula and Fan–Sun/Jensen comparisons are recorded in [NOTE.md](NOTE.md). The present triple proof uses the sum-compatible phases essentially, as the countermodel demonstrates. A targeted search has not located this exact triple formula, but that is not a priority certificate.
- Blanco–Criado–Santos, [*Coloopless zonotopes and counterexamples to the Shifted Lonely Runner Conjecture*](https://arxiv.org/html/2603.24784v2), explicitly disprove the unrestricted shifted conjecture starting with five nonzero speeds. This reinforces the need to preserve compatible phases and to state the core witness as a hypothesis. Their geometric results do not automatically give the local time-radius statement proved here.
- Hu–Jing's 16 October 2026 preprint [*Near optimal gap in the Lonely Runner Conjecture*](https://arxiv.org/abs/2610.23790) claims a uniform improvement `(1+c)/(2n)` over the union-bound scale. It includes a detailed AI-assistance statement. That is a different general-n objective from exact local lifting; this checkpoint must not be marketed as the first AI-assisted arbitrary-n advance. We have not independently audited their entire proof.

The remaining publication question is whether the sharp local classification plus its structural applications is sufficiently new and substantial. The elementary separated tower is an illustration, not by itself a strong new class theorem. A broad reduction for comparable speeds, a classification of more general short relations, or a significant optimality extension would strengthen the case. No Q2 acceptance guarantee is warranted.

## 9. Reproducibility

`python verify.py` builds the standalone package and checks the exported axiom reports, then runs exact rational interval experiments. The new triple grid contains 21,888 parameter choices, plus 15 near-sharp family samples. All interval unions use **strict overlap**, because touching open forbidden intervals leave a safe boundary. Independent phases deliberately produce the countermodel above. The universal statements and optimality are proved in Lean; finite searches are cross-checks.

`probe_core.py` preserves an optional exploratory mixed-core search. Its guard target omits the positive drift allowance and uses the full problem's threshold for the other coordinates; its output must not be confused with a proof of the earlier guarded-core premise. The sum-triple theorem bypasses that search rather than assuming it succeeds.
