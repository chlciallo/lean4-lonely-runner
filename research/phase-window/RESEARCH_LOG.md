# Research ledger

2026-10-24 checkpoint. General theorem statements are in NOTE.md and the Lean source. This file records decisions and rejected candidates so they are not rediscovered as apparent progress.

| Candidate or task | Result | Consequence |
|---|---|---|
| Preserve a single maximally safe core phase under a short relation | False: `(3,5,8)` with `8t in Z+1/2` | Prove window-based lifting instead; full real-time countermodel in Lean |
| Rotation gap `rG≥1+||rC||` | False at `r=6,C=2/5` | Do not use this candidate |
| Equal-threshold local radius `2δ/a` for δ≤1/6 | Proved; BHK (2001), Lemma 4 already contains the endpoint case | Credit prior art; not a new-theorem claim |
| Extend `2δ/a` to δ=1/5 | False for speeds 3,5 with phases 0,1/2 | Preserve the threshold transition |
| Mixed-threshold radius `max(α+β,α(1+2β)/(1−2β))/a` | Existence and optimality proved generally in Lean | Candidate exact formula; priority assessment remains provisional |
| Core-to-pair transfer with quantified margin | Proved generally in Lean | Actual `k→k−2` theorem with explicit separation |
| Short relation `b−a=uⱼ` plus a protected relative phase | Proved generally in Lean | Half-radius lift and half the uniform separation threshold |
| Remove the relative-phase drift allowance | False at a=2,b=5,t₀=1/2,δ=1/6 | Drift term retained; full interval countermodel in Lean |
| Novelty check | Compared BHK, Fan–Sun, Jensen, Beck–Everett; searched local two-speed/interval terminology | No claim of guaranteed priority or publication strength |

Formalization rework consisted of implicit phase-argument inference, an unnecessary tactic after goal closure, a negation simplification loop, deferred subgoal order, and a Windows output-encoding issue. None required weakening a proved mathematical statement. The source keyword gate also matched the English word “unsafe” in a comment; that comment was rephrased. The final successful logs contain the audited theorem set.

## Remaining objective

The user's publication-level objective is still active. This checkpoint does not meet a promise of a Q2 paper. The immediate research issue is **existence of a core witness satisfying the stronger relative-phase guard**, without assuming the desired full-instance conclusion. General LRC(k−2) alone supplies only a weaker uniform margin. A useful next theorem must produce the guard for a substantial structured family, relax the separation using phase constraints, or establish a genuinely new classification. Merely parameterizing another finite-person proof, relabeling BHK, or increasing an experiment range would not resolve that issue.

No subagents were used. No messages were sent to researchers or maintainers. The checkpoint is published on an isolated research branch of the user's repository.
