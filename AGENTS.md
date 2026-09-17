# Project rules — Research07 (Lean 4 LRC formalization)

## Subagent reporting protocol (STANDING RULE, user-mandated 2026-09-17)

Every subagent (explore or general) MUST maintain an incremental report file on disk:

- Path: `_reports/<task-slug>.md` (create `_reports/` if missing; one file per agent).
- Append findings **as you go** — after every major find, every ~10 tool calls minimum.
  Structure: timestamped sections, each self-contained (paths, URLs, decl names, verdicts).
- The file is the agent's durable memory: if the agent dies/is interrupted, the report
  must already contain everything found so far. Never hold results only in context.
- Final section = structured summary for the orchestrator.

Orchestrator side: when dispatching agents, put this requirement verbatim in the contract.
Never dispatch more than one heavy literature-reconstruction per agent — split into
small single-source digs so a killed agent loses little.

**Profile requirement:** `subagent_explore` is READ-ONLY (no file writes) — any agent
with reporting duties MUST be `subagent_general`. If an explore agent is used anyway
(pure search), the orchestrator must persist its final-message findings to
`_reports/` on receipt. (Rule added after 24e5010e/39d7801e were dispatched with a
report contract they physically could not fulfill.)

## Verification gates (apply to every Lean change)

- `lake build` clean; zero `sorry`/`admit`/`native_decide`/`unsafe`.
- `#print axioms` may only show `[propext, Classical.choice, Quot.sound]`.
- Frozen statements may only be changed via a demonstrated countermodel + orchestrator
  approval (precedent: `exists_k_all_good` positivity fix).
- Scratch files must live outside the import tree (`Research07/Scratch.lean`,
  `LRC5/DiscreteWork.lean` are dev-only).

## Project state cheat-sheet (2026-09-17)

- DONE + audited: `lonely_runner_three` (real speeds), `lrc5_int`,
  `lrc5_rel_rat`, `lonely_runner_five_rat` (integer/rational n=5). See `Audit.lean`.
- NEXT: Phase M3 = full real-speeds `lonely_runner_five` via BHK Lemma 8 —
  blueprint in `PLAN_M3.md`. Tier-up roadmap (κ(V) formula, p-generalization,
  n=6 Renault, n=7 Barajas–Serra) in §3 of same file.
- `_external/` holds reference clones (five-distance-sharp, bhk.pdf/bhk.txt) —
  reference only, not part of the package.
