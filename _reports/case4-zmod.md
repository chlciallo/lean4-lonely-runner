# case4-zmod.md — Case4.lean `interval_cases` → `fin_cases` repair log

Task: make `Research07/LRC7/Case4.lean` compile. Blocker: `interval_cases` does not
support `ZMod 7` (needs `LocallyFiniteOrder`). Strategy: `fin_cases` (Fintype enum)
+ `decide`-based closers.

## 2026-10-02 — segment 1: recon

### File inventory
- `Research07/LRC7/Case4.lean` (191 lines), imports `Research07.LRC7.Filtering`
  (→ `Discrete` → `LRC5.Discrete` → `LRC3.Circ` → `import Mathlib`; all tactics
  available transitively, incl. `fin_cases`, `interval_cases`, `decide`).
- `cycIv i L` def at `Research07/LRC7/Discrete.lean:360`:
  `Finset.univ.filter fun x : ZMod 7 => (x - i).val < L`. Plain decidable Finset —
  membership/subset/Nonempty/∃ all `Decidable` → `decide` can evaluate.

### `interval_cases` sites (12 total, all on `ZMod 7` vars)
- L44 `not_mem_bad_of_mem_cycIv`: `interval_cases x <;> simp at h ⊢ <;> omega`
- L50 `pair_avoid`: `rcases hr with rfl|rfl <;> interval_cases z <;> simp`
- L57,65 `quad_avoid_22/24`: `interval_cases z3 <;> interval_cases z4 <;> refine ⟨?_,?_,?_,?_⟩ <;> decide`
  — NOTE: `refine` leaves witness `?i : ZMod 7` metavariable; `decide` cannot fill
  a non-Prop mvar → this closer is broken even with interval_cases; replace with
  plain `decide` (kernel enumerates the bounded ∃).
- L72-73 `shape4`: 4×interval_cases + `simp_all <;> tauto` — ∃-conclusion, simp/tauto
  can't synthesize witnesses → needs decide/ absurd-prune.
- L81-82 `shape3`: same issue.
- L88 `pair_dist`: same.
- L106-109 `prop4`: 4+4 vars, ∀-hyp `hhit` not enumerable by simp → needs decide-prune.
- L118 `prop3a`, L133-135 `prop3b`, L152-154 `prop2i`, L170-172 `prop2ii`: same.
- L177 `mem_pair_iff_val`: `interval_cases z <;> simp` → `fin_cases z <;> decide`.

### Prior art in repo
- `LRC3/Main.lean:45-66`: `fin_cases i`/`fin_cases j` on `Fin 3` — works, produces
  `⟨k, _⟩` Fin.mk literal subgoals (ZMod 7 is defeq `Fin 7`, same machinery).
- `LRC7/FiniteBase.lean:284`: `interval_cases k <;> first | exact absurd rfl hk7 | decide`
  — established `first | absurd | decide` idiom.
- Ledger (`_dev/failures.md`): kernel `decide` on big enums (>12GB) caused the
  31GB crash; small sliced decides are safe (200-600MB). Our per-goal decides are
  ≤2401-element scans — trivial.

### Design (per-lemma, all decide-based, no reliance on simp literal-eval)
- Membership hyps pruned via `first | exact absurd hX (by decide) | skip`
  (evaluates `¬(x ∈ S)` concretely after casing; `skip` keeps valid combos).
- Final goals (`∃ i`, `x ∉ S`, iff) closed by `decide`.
- `not_mem_bad_of_mem_cycIv` has free `L` → can't decide whole; use
  `rintro (rfl|rfl)` on `x ∈ {0,6}` + `decide`-computed `(lit-1).val` + `omega`.

## 2026-10-02 — segment 2: edits applied (pre-build)

All 12 `interval_cases` sites rewritten. Summary of new proofs:
- `not_mem_bad_of_mem_cycIv` (L40-48): `simp only [cycIv,...] at h`;
  `simp only [mem_insert, mem_singleton]`; `rintro (rfl|rfl)` substs x;
  `decide`-computed `(lit-1).val` + `omega`. No casing needed.
- `pair_avoid` (L54): `rcases hr with rfl|rfl <;> fin_cases z <;> decide`.
- `quad_avoid_22/24` (L61,68): `fin_cases z3 <;> fin_cases z4 <;> decide`
  (dropped broken `refine ⟨?_,?_,?_,?_⟩` — decide can't fill a non-Prop mvar).
- `shape4/shape3/pair_dist` (L74-91): `fin_cases` all vars,
  `first | exact absurd h (by decide) | decide` — absurd kills combos where the
  ∀-hyp is false (decide evaluates `¬∀`), decide proves the ∃/∉ conclusion.
- `prop4` (L109-117), `prop3a` (L126-128), `prop3b` (L143-150),
  `prop2i` (L167-174), `prop2ii` (L190-197): interleaved
  `fin_cases vX <;> (first | exact absurd hX (by decide) | skip)` pruning after
  each variable (keeps fan-out small: each membership hyp kills ~5/7 branches);
  final `decide` on the ∃/∈ conclusion. Checkable ∀/Nonempty hyps get their own
  `absurd` alternative at the stage where all their vars are concrete.
- `mem_pair_iff_val` (L202): `fin_cases z <;> decide` (Iff decidable).
- `mem_cycIv_add`, `cycIv_zero_add`: untouched (no casing).

Risks to watch: `fin_cases` on `ZMod 7` Fintype elems; `(first | tac | skip)`
inside `<;>` parse; `by decide` on `¬(∀ i, Nonempty ...)` reduction.

## 2026-10-02 — segment 3: build 1 (case4_1) FAILED + root-cause probes

### Build 1 result (`_dev/memlog/case4_1.csv`, cap 12288)
- `Case4.lean:54`: `failed to synthesize Decidable ((fun i ↦ i) ⟨0, ⋯⟩ ∉ {0,6} ∨ ...)`
  at `pair_avoid`'s `fin_cases z <;> decide`. Stack overflow at exit, peak 11.5GB,
  not watchdog-killed.

### Probe results (`_dev/scratch/case4_probe.lean`, logs case4_probe1/2)
Root cause isolated: **`fin_cases` substitutes `Fin 7`-typed `⟨k,⋯⟩` literals**
(pp shows `(fun i ↦ i) ⟨k, ⋯⟩` = `ZMod.finEquiv.symm`/ofFin applied). Then:

- `decide` FAILS whenever a `Finset.decidableMem ?a ?s` must unify `?a` with a
  bare `⟨k,⋯⟩` elem: direct mem `⟨k⟩ ∈ s` / `⟨k⟩ ∉ s` (probes A2, A3 — even with
  `(⟨k,⋯⟩ : ZMod 7)` ascription), Iff/∨/∧ props containing bare-elem mems
  (probe 11, probe B residual `0 ∉ {0,6} ∨ ¬0+2=0 ∧ ¬0+2=6`).
- `decide` WORKS when the mem-subject is: a bound `∀`/`∃` var (probe 2, ∀-decide;
  A1/A4 controls), an `OfNat` literal `(0 : ZMod 7)`, or an arith expr
  `⟨k⟩ - ⟨j⟩` / `⟨k⟩ + i*2` — `HSub`/`HAdd` result is `ZMod 7`-typed via ZMod's
  own instances so `?a`'s type is consistent (probe D confirmed on
  `c0 - b0 ∈ {0,1}`; probes 6/8/9 on ∃-decide and ∀-absurd).
- `simp at h` DOES evaluate `⟨k⟩ ∈ {literals}` fully (probe C/F): False cases
  close the goal, True cases drop the hyp. → correct pruning tactic for
  direct-elem mem hyps.
- `absurd h (by decide)` works for: arith-typed mems (`c0 - b0 ∈ s`, `hd`,
  `he*`, `hdc`), `∀`-props (`hhit`, `shape4.h`), `Nonempty` props (`hh1/hh2`) —
  the prop-head instances don't route through a bare-elem `decidableMem`.
- `beta_reduce` alone does NOT fix bare-elem decide (probe earlier round);
  `simp` on the GOAL also leaves undecidable residuals (probe B).

### Revised edits applied to Case4.lean
- `pair_avoid` (L54): `rcases hr <;> revert z <;> decide` — ∀-form, bound-var
  mem subject → decide evaluates 7 cases.
- `quad_avoid_22/24`: `fin_cases z3 <;> fin_cases z4 <;> beta_reduce <;> decide`
  (∃-decide; mem subjects `z3+i*2` are HAdd-typed → clean).
- `prop4`: `fin_cases bX <;> simp at hbX` interleaved (simp prunes direct-elem
  mem hyps), `absurd hhit/hcX (by decide)` for ∀-hyp + arith mems, final decide.
- `prop3a/prop3b/prop2i/prop2ii`: same restructure — `simp at hb*` for direct
  elems, `absurd (by decide)` for arith mems/Nonempty/∀, final `decide`.
- `shape4/shape3/pair_dist`: kept `first | exact absurd h (by decide) | decide`
  (h is ∀-prop → absurd-decide OK; conclusions are ∃-eq/⊆/arith-mem → decide OK).
- `mem_pair_iff_val`: `revert z; decide` (Iff over bound var → decidable).

### Build 2 result (`_dev/memlog/case4_2.csv`, cap 12288) — FAILED on memory
- No Lean errors at all: `std::bad_alloc` at peak_tree_priv=12288MB (job cap
  itself caused alloc failure, `killed=False`). ~3.3GB above the ~9GB import
  baseline → some construct's peak consumption is too high.
- Prime suspects: `shape4`'s `fin_cases x0..x3` = 2401 simultaneous goals in
  tactic state (each carrying full ctx); prop4/prop3b/prop2i/prop2ii cascades.
- Next: bisect — build truncated variants / measure per-construct peak in
  scratch; candidate fix: `revert`-to-∀ + kernel `decide` for shape-style lemmas
  (turns goal-state cost into sequential kernel eval), or earlier pruning.

## 2026-10-02 — segment 4: bisect + final design + GREEN

### Bisect probes (all under memwatch cap 12288)

- `case4_p1` (small lemmas + shape-style): t1 not_mem_bad, t2 pair_avoid,
  t3 quad_avoid, t4 shape4 (2401 goals!), t5 shape3, t6 pair_dist —
  **all passed except t3**: `beta_reduce <;> decide` whnf-loops (200k
  heartbeats). Peak 10.8GB — fin_cases goal-state was NOT the OOM driver.
- `case4_q`: `fin_cases z3 <;> fin_cases z4 <;> decide` (no beta_reduce) —
  quad_avoid_22/24 pass clean, 26s, 8.8GB. **`beta_reduce` was the trigger.**
- `case4_p2` (5 cascades + mem_pair): `INTERNAL PANIC: out of memory` at
  12.16GB, 269s — cascades were the hog.
- `case4_u1` (prop4-cascade alone): whnf-timeout at 360s, 10.8GB — the
  `fin_cases <;> simp at <;> first|absurd|skip` chain spends its life in
  per-goal simp/decide across ~100s of live goals.
- `case4_s1`: **`suffices`-∀ + `decide` for prop4-shape PASSED** (~few sec);
  v4/v5 (prop2i/ii-shape) failed `Decidable` synth — traced via
  `case4_dec/dec2/dec3` to **`synthInstance.maxSize`** (deep ∀+imp nesting;
  `set_option synthInstance.maxSize 4096` fixes; shallow fragments synth fine).

### Final mechanism (empirical rules)

`fin_cases` substitutes `Fin 7`-typed `⟨k,⋯⟩` literals; `Finset.decidableMem`
TC-synth fails on bare-elem `?a` (type `Fin 7 vs ZMod 7` mismatch at `inst`
transparency). `decide` works iff every mem-subject is a bound var, `OfNat`
literal, or `HSub`/`HAdd` expr (ZMod-typed). `suffices`+∀-prop puts ALL
mem-subjects on bound vars → `Decidable` synthesized once, kernel-evaluated on
literals; `decidableImp`/`decidableForall` short-circuit = hyp pruning, so
prop4's 7^8 naive space shrinks to ~10-20k evals.

### Final proofs in Case4.lean (all green)

- `pair_avoid` L59: `rcases hr <;> revert z <;> decide`.
- `quad_avoid_22/24` L66/73: `fin_cases z3 <;> fin_cases z4 <;> decide`
  (beta_reduce removed — it whnf-loops).
- `shape4` L78-86, `shape3` L90-98, `pair_dist` L102-108,
  `prop4` L113-126, `prop3a` L134-141, `prop3b` L154-165,
  `prop2i` L181-192, `prop2ii` L207-220: `suffices H : ∀-interleaved-prop by
  exact H args; decide`.
- `mem_pair_iff_val` L219-221: `revert z; decide`.
- `not_mem_bad_of_mem_cycIv` L45-53: `simp only` + `rintro (rfl|rfl)` +
  `decide`-val + `omega` (unchanged, passed as-is).
- `mem_cycIv_add` L38-42: unchanged.
- `cycIv_zero_add` L226-235: `sub_zero` added to simp set (`(a-0).val` vs
  `a.val` were distinct omega atoms); `ZMod.val_add_of_lt hsum` replaced a
  broken `rw`-chain (`ZMod.val_natCast` leaves `%`-literals that don't match
  `exact Nat.mod_eq_of_lt`).
- File-level `set_option synthInstance.maxSize 4096` (L33) for prop2i/ii's
  deep ∀+imp `Decidable` props. Plain `--` comment — `/--` docstring before
  `set_option` is a parse error.

### Final build — GREEN

- `python _dev/memwatch.py 12288 _dev/memlog/case4_4.csv -- lake build
  Research07.LRC7.Case4` → **built in 32s, peak_tree_priv=10383MB,
  killed=False, zero errors** (8928 jobs).
- `#print axioms` on all 15 theorems: `[propext, Classical.choice,
  Quot.sound]` — whitelist clean (`_dev/memlog/case4_ax.csv`).
- No `sorry`/`admit`/`native_decide`/`unsafe`/`interval_cases` in file.
- No theorem statements changed. Only `Case4.lean`, this report, and
  `_dev/failures.md` modified. Scratch probes live in `_dev/scratch/`
  (gitignored): `case4_probe.lean`, `case4_p1.lean`, `case4_p2.lean`,
  `case4_q.lean`, `case4_u1.lean`, `case4_s1.lean`, `case4_dec.lean`,
  `case4_dec2.lean`, `case4_dec3.lean`, `case4_ax.lean`.

### Orchestrator summary

- **Status: DONE.** `lake build Research07.LRC7.Case4` green under 12GB
  watchdog (peak 10.4GB, 32s).
- Reusable rules: on `ZMod 7`, `interval_cases` unsupported; `fin_cases`
  yields `Fin`-typed `⟨k,⋯⟩` literals that break `decide` on bare-elem mems —
  prefer `suffices`-∀ + `decide` (bound-var subjects + imp short-circuit
  pruning) for multi-var/hyp lemmas; never `beta_reduce` before `decide`
  (whnf loop); deep ∀+imp `Decidable` props need `synthInstance.maxSize`;
  omega needs `sub_zero` to unify `(x-0).val`/`x.val` atoms;
  `ZMod.val_add_of_lt` is the direct `(a+b).val = a.val+b.val` lemma.
