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

## Failure ledger (STANDING RULE)

On every build failure, false/oversized statement, dead subagent, or
notable rework, append ONE line to `_dev/failures.md` (gitignored, local):
`date | component | what failed | root-cause tag | fix`.
Reuse existing tags when possible; invent new ones sparingly.
When asked, summarize the ledger as a frequency table by tag.

## Verification gates (apply to every Lean change)

- `lake build` clean; zero `sorry`/`admit`/`native_decide`/`unsafe`.
- `#print axioms` may only show `[propext, Classical.choice, Quot.sound]`.
- Frozen statements may only be changed via a demonstrated countermodel + orchestrator
  approval (precedent: `exists_k_all_good` positivity fix).
- Scratch files must live outside the import tree (`Research07/Scratch.lean`,
  `LRC5/DiscreteWork.lean` are dev-only).

## Project state cheat-sheet (2026-09-17, final)

- ALL DONE + audited: `lonely_runner_three`, `lrc4_int`/`lrc4_rat_finset`,
  `lrc5_int`, `lonely_runner_five_rat`, and **`lonely_runner_five`**
  (full real-speeds n=5 via BHK Lemma 8). Zero sorry; axiom gate
  `[propext, Classical.choice, Quot.sound]` enforced by `Audit.lean`
  (imported from the umbrella `Research07.lean`).
- Full build: `lake build` = 8945 jobs clean.
- Planning docs and roadmap live in `_dev/docs/` (local only, gitignored).
- `_external/` holds reference clones (five-distance-sharp, bhk.pdf/bhk.txt) —
  reference only, not part of the package.
- `_dev/` holds scratch/dev files (gitignored): `scratch/`, `W8overlay/`.
- `_reports/` = agent work logs; `STATEMENT.md` = statement-fidelity audit
  including the countermodel correction table.
