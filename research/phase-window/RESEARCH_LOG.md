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

## Second checkpoint, 2026-10-24: compatible sum triples

The guard-existence issue above is bypassed for a separated sum triple, not solved for all cores. New theorem: the exact local constant for `(1,ρ,ρ+1)` with phases `(x,y,x+y)` is `max(5δ/2,δ(1+2δ)/(1−4δ))` for `0<δ≤1/6`. Both directions are proved in Lean. The proof constructs jointly safe endpoints using a ceiling integer and a shared fast phase; no interval-component finiteness or numerical enumeration is assumed.

The new `delete_sum_triple` removes three speeds for every k≥7 under `d≥5(k−2)M/6`, using only the ordinary lower-dimensional core witness. The exact independent-phase counterexample is formalized too. See TRIPLE_NOTE.md for full hypotheses and proof.

| Task | Result |
|---|---|
| Optional marked-core search | Preserved in probe_core.py; it searches a relaxed mixed-threshold question, not the full guarded premise |
| First coarse sum-triple bound | 4δ/d follows from a two-step guard construction; replaced by the sharp envelope |
| Sharp compatible sum-triple envelope | Upper bound and both lower mechanisms kernel-checked |
| Drop phase compatibility | False at δ=1/9, ratios 1,9/8,17/8, phases 0,1/12,7/12; all-real window countermodel proved |
| Exact cross-check | 21,888 grid choices passed; 15 near-sharp samples; independent-phase failure recovered |
| Recursive application | 20 certified lifts from 4 to 64 speeds, each outside the separation criteria of the two prior pair lemmas |
| Prior art | Rechecked BHK interval argument; found and recorded 2026 shifted counterexamples and Hu–Jing's AI-assisted general-n lower-bound preprint |

Formal rework: missing real FloorRing import; one redundant tactic after field_simp closed its goal. No mathematical weakening was needed. The second checkpoint passes the complete verification script with 15 principal axiom reports and 40 theorem declarations across eight modules.

The publication objective is still active. The next substantive question is whether the sharp compatible-window classification extends to other short relations or yields a broad application beyond separated towers. The unbounded tower is deliberately not presented as a new unrestricted-n theorem. No communication with researchers or journal submission has been performed.

## Priority audit, 2026-10-24

The user requested priority checking before further theorem expansion. Nine primary sources were compared at selected original statements and relevant proof sections; see PRIORITY_AUDIT.zh-CN.md and priority-sources.json. This is a bounded audit, not an exhaustive novelty certificate.

Confirmed: BHK contains both the two-block estimate and explicit treatment of sum relations; Kravitz Proposition 8.1 already implements local margin transfer; Fan–Sun uses two-fast-runner transfer and relative-speed reductions. These methods must not be claimed as original.

New adverse finding: the recursive example family satisfies `vᵢ₊₃≥4vᵢ`. An analytic argument shows that every such instance with n≥494 meets the condition of Dubickas (2011), Theorem 1.1. The earlier recursive family therefore supplies no new asymptotic global-existence class. Exact premise checks for 200 layers are in prior-art-checks.json. The primary source uses floor((n+1)/(12e)), which must not be replaced by a ceiling from a secondary paraphrase.

No exact duplicate of C₃'s full compatible-phase local radius was identified in the inspected results. Its originality remains unconfirmed, and the elementary deletion corollary is not counted as an independent main contribution. No Lean source changed in this audit; its mathematical validation is the existing clean build. The new exact prior-art premise checker was run separately. No researchers were contacted.
