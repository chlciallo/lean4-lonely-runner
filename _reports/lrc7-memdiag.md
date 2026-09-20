# LRC7 memory diagnosis — BSOD root cause + verified fix (2026-09-18)

## Symptoms (from _dev/failures.md)

lean.exe ballooned to ~31GB commit; system = 32GB RAM + 16GB pagefile =
47.7GB commit limit → 99.5% → BSOD 0xEF / hangs / powercycles ×3.
`.olean.private "failed to read"` errors on random mathlib modules.

## Tool delivered

`_dev/memwatch.py <cap_mb> <log.csv> -- <cmd>`:
- Windows Job Object `JOB_OBJECT_LIMIT_JOB_MEMORY` — caps the whole
  process tree; allocations fail past the cap (OS-enforced kill).
- Poll watchdog (0.5s) as backup; CSV log per poll: tree private/WS MB,
  peak, system commit used/limit, all lean.exe (pid:MB:.lean file),
  top-5 other processes.
- Verified: 300MB cap kills an allocating process at cap; system safe.

Logs in `_dev/memlog/`.

## Experiments (all under caps — no crashes)

| Probe | Content | Result |
|---|---|---|
| finprobe5 | `import Filtering` only | **~7.5GB @11s** — import baseline |
| finprobe2b | `powersetCard 5 |>.card` decide | **+2.3GB** on top of import; exit 0 @10.9GB peak |
| finprobe1b | `badSets49.card=63` (filter+λcheck) | **>16GB**, killed still climbing ~250MB/s |
| decprobe4 | 20^4 nested-∀ bitmask goodN | **>12GB** killed |
| decprobe5 | 3 slices × ~8k-iter decides | **exit 0, peak 9.56GB** — slices cost 170–600MB, freed between |

## Diagnosis

1. **Import baseline ≈ 8.5GB per lean.exe** — every file transitively
   `import Mathlib` (LRC3/Circ, Basic, LRC6 files).  Always-present cost.
2. **Big-enumeration `decide +kernel` is the bomb** — kernel reduction
   garbage grows ~linearly with total unit work:
   - `powersetCard` materialization itself is cheap (+2.3GB for 42504).
   - Per-element *predicate evaluation* is the hog (each absModN/Finset op
     leaves reduction garbage).
3. `.olean.private` errors = **allocation-failure symptoms**, not disk
   corruption (files verified present; module paths random).
4. Fixes that work: **(a) shrink enumeration** (normalize by λ=a⁻¹ → only
   sets containing 1: C(20,4)=4845 vs 42504), **(b) cheapen per-element
   work** (bitmask cover table → ~30 kernel steps vs ~500),
   **(c) slice the decide** (~8k iterations per `decide` call, private
   lemmas + dispatch — memory freed between subgoals).
5. `Decidable` synthesis does **not** unfold plain `def`s — helpers fed
   to `decide` must be `abbrev` (or unfolded in the statement).

## Fix plan for Finite.lean (validated)

- `badSets49` := **explicit 63-set Finset** (3 orbits of 21 under
  `units21` scaling — paper's three exceptional sets, verbatim).
- `stage1_norm`: `∀ a b c d ∈ reps21', a<b<c<d → goodN ∨ {1,a,b,c,d} ∈
  normBad` — decided **per outer element `a`** (~20 private slices,
  each ≤ ~8000 lazy iterations ≈ ≤600MB), assembled by interval_cases
  dispatch.  Top statement unchanged (paper-faithful).
- `normBad` = the 15 normalized bad sets (computed, matches orbit reps).
- `stage1` (all Q): pick `a∈Q`, scale by `a⁻¹`, apply `stage1_norm`,
  map back — no enumeration.
- `stage2`: slice the 63 `Q`s into ~7 chunks of ≤10; inner
  `T ⊆ lifts (≤10 elems → 2^10 materialize = cheap) × 6 r`.
- `badSets49_card = 63` — trivial decide on a literal set.

Expected peak ≈ 9.5–11GB (baseline + slice increments) vs ~30GB before.

## Open

- stage-2 inner iteration count per chunk — verify under cap before
  committing.
- User-side: enlarge pagefile (system-managed or ≥32GB) as backstop.

## 2026-10-02 update — resolution implemented

### Stage-1 Decidable-synthesis blocker (solved)

- Symptom: `decide +kernel` on
  `∀ b c d ∈ Finset.Icc 2 24, goodN a b c d ∨ badTuple a b c d` failed
  `Decidable` synthesis even though `badTuple` (15-way tuple-equality
  disjunction) synthesized standalone and `∨ True` passed under `∀∈`.
- Bisect (`_dev/scratch/SynProbe*.lean`): `Finset.decidableDforallFinset`
  needs `∀ a h, Decidable (p a h)` — the ~119-node Or-of-And instance
  tree exceeds synthesis limits when produced *inside* the dependent
  quantifier (single `∧` and small `∨` pass).
- Fix: `badTuple a b c d := (a,b,c,d) ∈ normBadTails` — literal
  15-element `Finset (ℕ×ℕ×ℕ×ℕ)`; `decidableMem` synthesizes trivially
  and kernel cost is ~15 tuple `decEq` per iteration (cheaper than the
  Or tree). `normBadTails_spec` (decide) bridges tuples back to
  `normBad49` membership.
- Result: `FiniteStage1` GREEN, 68 s, peak tree-private 10.1 GB
  (≈ 8.5 GB baseline + 1.6 GB for all 23 slices — per-slice release
  confirmed).

### Stage-2 architecture (generated, building)

- `_dev/gen_stage2.py` emits `FiniteStage2.lean` (3727 lines): per bad
  set `Q_k`, `uTabQ<k>` literal `(λ, U_λ)` table per residue
  r ∈ {7,…,42}; `stage2_Q<k>` = `∀ T ∈ powersetCard 5, ∀ r ∈ d6res,
  odd → ∃ p ∈ uTab, ∀ t ∈ T, t ∉ p.2` by `decide +kernel`
  (252 T-subsets each, ~1 GB); `uTabQ<k>_spec` (decide) = honest-coverage
  bridge `U = {t : |λt|_98 < 14}` ∧ `14 ≤ |λr|_98` ∧ `λ ∈ Icc 1 49`;
  `stage2_lift_<k>` extends `card ≤ 5` via
  `Finset.exists_subsuperset_card_eq`.
- Public `stage2` keeps the exact `lrc7_m1` interface; dispatch unfolds
  `badSets49` to a 63-way `Q = q_k` disjunction (`simp only` + mem
  lemmas) then `rcases … rfl` per literal.
- Audit surface unchanged: `badSets49` is the explicit 63-set list; each
  `uTabQ<k>` is auditable data + a proved spec bridge.
