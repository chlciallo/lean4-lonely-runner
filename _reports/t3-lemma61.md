# T3 — Lemma61 (Renault Lemma 6.1) proof log

Task: prove `lemma6_1` in `Research07/LRC6/Lemma61.lean` (Lean4+Mathlib v4.34.0, Windows).
Verify: `export PATH="$HOME/.elan/bin:$PATH"`, `lake env lean Research07/LRC6/Lemma61.lean`.
Baseline: file compiles in ~21 s with the sorry.

## Statement recap
`x₂ x₄ x₅ ∈ Ico 0 1` ⇒ either
(1) `∃ lam al : ℕ, 2≤lam≤5, 1≤al≤5` with `fract(lam·x₄+al/6)`, `fract(lam·x₅+al/6)`, `fract(lam·x₂+2al/6)` ∈ `Icc(1/6,5/6)`, or
(2) `∃ al ∈ {1,2,3,4}` with `fract(x₄+al/6)`, `fract(x₅+al/6)`, `fract(x₂+2al/6)` ∈ `Ioo(1/6,5/6)`.
Symmetric in x₄,x₅ (can exploit role-swap).

## Paper proof (renault.txt L184–197) — decoded
Assume ¬(1),¬(2). Notation: `pᵢ^λ = ⟨λxᵢ⟩`, `q = ⟨λx₂⟩`.

KEY DECODING (interval forms). For `u ∈ [0,1)` and shift `s = α/6`, `α∈{1..5}`:
- `fract(u + α/6) ∉ Icc(1/6,5/6)` ⟺ `u ∈ J_α := Ioo((5-α)/6, (7-α)/6)` (open interval, NO wrap since `α≤5 ⇒ (7-α)/6 ≤ 1`):
  J₁=(4/6,6/6), J₂=(3/6,5/6), J₃=(2/6,4/6), J₄=(1/6,3/6), J₅=(0/6,2/6). Every point ∈(0,1) lies in ≤2 CONSECUTIVE J's (chain overlaps); p=0 lies in none.
- For runner 2 (shift `2α/6`): `fract(q + 2α/6) ∉ Icc` ⟺ `q ∈ K_α`:
  K₁=K₄=(3/6,5/6), K₂=K₅=(1/6,3/6), K₃ = `q ∉ Icc(1/6,5/6)` (i.e. `[0,1/6)∪(5/6,1)`; shift is 1 so fract(q+1)=q).
  ⇒ x₂-bad set B ⊆ {1..5} is one of ∅, {3}, {1,4}, {2,5} — ≤2 elements, never 2 consecutive.

STEP 1 (per λ∈{2,3,4,5}): `|p₄-p₅| ∈ (1/6,5/6)`. Proof by contradiction on `d≤1/6` i.e. `|p₄-p₅|≤1/6 ∨ ≥5/6`, case on q:
- q∈(3/6,5/6): K₁,K₄ hold ⇒ J₂,J₃,J₅ covered by {p₄,p₅}. J₅-point <1/3; J₃∩J₂=(3/6,4/6) needs other point ⇒ |diff|∈(1/6,2/3). Contradiction.
- q∈(1/6,3/6): K₂,K₅ ⇒ J₁,J₃,J₄ covered. J₁-point >2/3; other ∈J₃∩J₄=(2/6,3/6) ⇒ |diff|∈(1/6,2/3). Contradiction.
- q∈wrap (K₃ only): J₁,J₂,J₄,J₅ covered ⇒ forced split {J₅∩J₄=(1/6,2/6)}|{J₂∩J₁=(4/6,5/6)} ⇒ |diff|∈(1/3,2/3). Contradiction.
- q∈{1/6,1/2,5/6}: all 5 J's needed; J₅(<1/3), J₁(>2/3) distinct points, J₃ uncovered. Contradiction.

Then `⟨λ(x₄-x₅)⟩ = ⟨p₄-p₅⟩ ∈ (1/6,5/6)` ∀λ∈{2,3,4,5} (since |p₄-p₅|∈(1/6,5/6) and fract(p₄-p₅)= |diff| or 1-|diff|).

CLAIM 2.4 (contrapositive): `u ∈ Ioo(1/6,5/6) ⇒ ∃λ∈{2,3,4,5}, fract(λu) ∉ Ioo(1/6,5/6)`.
VERIFIED by hand: safe-preimage intersection is empty. λ-safe (open band) preimages:
  λ=2: (1/12,5/12)∪(7/12,11/12); λ=3: (1/18,5/18)∪(7/18,11/18)∪(13/18,17/18);
  λ=4: (1,5,7,11,13,17,19,23)/24 pieces; λ=5: (7,11,13,17,19,23,25,29)/30 pieces.
  ∩(1/6,5/6): after λ2: (1/6,5/12)∪(7/12,5/6); ∩λ3: (1/6,5/18)∪(7/18,5/12)∪(7/12,11/18)∪(13/18,5/6);
  ∩λ4: (1/6,5/24)∪(7/18,5/12)∪(7/12,11/18)∪(19/24,5/6); ∩λ5 = ∅. ✓
Plan: `fract(z)∈Ioo(1/6,5/6) ↔ ∃k:ℤ, z∈Ioo(k+1/6,k+5/6)`; bound k per λ (k₂∈{0,1},k₃∈{0,1,2},k₄∈{0,1,2,3},k₅∈{1,2,3}), rcases 2·3·4·3=72 leaves, all closed by linarith.

With δ = fract(x₄-x₅): `⟨λδ⟩ = ⟨λ(x₄-x₅)⟩ ∈ (1/6,5/6)` ∀λ ⇒ claim24 ⇒ δ ∉(1/6,5/6) ⇒ δ∈[0,1/6]∪[5/6,1). λ=2 ⇒ δ∈(1/12,1/6]∪[5/6,11/12); λ=5 kills δ=1/6 (⟨5/6⟩∉open) and δ=5/6 (⟨25/6⟩=1/6∉open). So δ∈(1/12,1/6)∪(5/6,11/12). Since |x₄-x₅| = δ or 1-δ: `|x₄-x₅| ∈ (1/12,1/6)∪(5/6,11/12)` and circ-dist ∈(1/12,1/6).

STEP 2 (λ=2): `|p₄²-p₅²| ∈ (1/6,1/3)∪(2/3,5/6)` (from ⟨2δ⟩∈(1/6,1/3)∪(2/3,5/6) and |p₄-p₅|∈{⟨2δ⟩,1-⟨2δ⟩}).
Case on q=⟨2x₂⟩ (only 2 survivable cases — cleaner than paper's |A| counting):
- q∈(3/6,5/6): h₂,h₃,h₅ p-side ⇒ one pt ∈J₅=(0,2/6), other ∈J₃∩J₂=(3/6,4/6). If J₅-pt ≤1/6 ⇒ |diff|∈(1/3,2/3) contradicts ⇒ J₅-pt ∈(1/6,2/6). CASE B: q∈(3/6,5/6), {p₄,p₅} = one ∈(3/6,4/6), other ∈(1/6,2/6).
- q∈(1/6,3/6): h₁,h₃,h₄ p-side ⇒ one pt ∈J₁=(4/6,6/6), other ∈J₃∩J₄=(2/6,3/6). If J₁-pt ≥5/6 ⇒ |diff|∈(1/3,2/3) contradicts ⇒ J₁-pt ∈(4/6,5/6). CASE A: q∈(1/6,3/6), {p₄,p₅} = one ∈(4/6,5/6), other ∈(2/6,3/6).
- q wrap or boundary: impossible (same arguments as step1 — the |diff|∈(1/3,2/3) resp. J₃-uncovered contradictions are independent of the stronger bound).

CASE A tail (say p₄∈(4/6,5/6), p₅∈(2/6,3/6), q∈(1/6,3/6)):
x₄∈(2/6,5/12)∪(5/6,11/12) [preimage ⟨2·⟩], x₅∈(1/6,1/4)∪(4/6,3/4), x₂∈(1/12,1/4)∪(7/12,3/4).
- x₅∈(4/6,3/4): dist<1/6 ⇒ x₄∈(5/6,11/12). (2)-witness: x₂∈(1/12,1/4)⇒α=4; x₂∈(7/12,3/4)⇒α=3. ✓ (verified: α=4 gives x₄+4/6→(3/6,7/12), x₅+4/6→(2/6,5/12), x₂+8/6→(5/12,7/12); α=3 gives x₂+1=x₂∈(7/12,3/4)⊂band.)
- x₅∈(1/6,1/4): dist ⇒ x₄∈(2/6,5/12). (2): x₂∈(1/12,1/4)⇒α=1; x₂∈(7/12,3/4)∪(1/12,1/6)⇒α=2 — union covers all x₂. ✓ (α=1: x₄+1/6→(3/6,7/12),x₅+1/6→(2/6,5/12),x₂+2/6→(5/12,7/12). α=2: x₄+2/6→(4/6,3/4),x₅+2/6→(3/6,7/12),x₂+4/6→(3/4,5/6) needs x₂<1/6 OR x₂∈(7/12,3/4)⇒fract(x₂+4/6)=x₂-1/3∈(1/4,5/12).)

CASE B tail (say p₄∈(3/6,4/6), p₅∈(1/6,2/6), q∈(3/6,5/6)):
x₄∈(1/4,2/6)∪(3/4,5/6), x₅∈(1/12,1/6)∪(7/12,4/6), x₂∈(1/4,5/12)∪(3/4,11/12).
- x₄∈(1/4,2/6): dist ⇒ x₅∈(1/12,1/6). (2): x₂∈(3/4,11/12)⇒α=2; x₂∈(1/4,5/12)⇒α=3. covers all. ✓
- x₄∈(3/4,5/6): dist ⇒ x₅∈(7/12,4/6). ¬(2) at α=4: x₄+4/6→(5/12,3/6)∈Ioo, x₅+4/6→(1/4,2/6)∈Ioo ⇒ x₂+8/6∉Ioo. fract(x₂+4/3)=x₂-2/3∈(1/12,1/4) for x₂∈(3/4,11/12); ∉Ioo ⇒ x₂≤5/6 ⇒ x₂∈(3/4,5/6]. Then (1) λ=4,α=1: ⟨4x₄+1/6⟩=4x₄+1/6-3∈(1/6,3/6)⊆Icc; ⟨4x₅+1/6⟩=4x₅+1/6-2∈(3/6,5/6)⊆Icc; ⟨4x₂+2/6⟩=4x₂+2/6-3∈(2/6,4/6]⊆Icc. ∎

## Helper lemmas planned (private, above theorem)
- `fract_eq_sub_intCast`/`fract_eq_of_floor`: `k ≤ z < k+1 ⇒ fract z = z - k` via `Int.fract_eq_iff`.
- `bad_Icc_iff`: `u∈[0,1), s∈[1/6,5/6] ⇒ (fract(u+s) ∉ Icc(1/6,5/6) ↔ u ∈ Ioo(5/6-s,7/6-s))`.
- `mem_Ioo_fract_iff`: `fract z ∈ Ioo(1/6,5/6) ↔ ∃k:ℤ, z∈Ioo(k+1/6,k+5/6)`.
- `claim24` as above.
- `step1`/`step2`: the two case-bash lemmas with d₁..d₅ hypotheses (J/K disjunctions as above).
- `fract_mul_nat'`: `fract(k·fract y) = fract(k·y)` for k:ℕ.
- `fract_self_add` already in Setup: `fract(x+s) = fract(fract x + s)`.
- doubling preimage: `fract(2x) ∈ Ioo a b ⇒ x ∈ Ioo(a/2,b/2) ∨ Ioo((a+1)/2,(b+1)/2)` (via fract(2x)∈{2x,2x-1}).

## API to verify
`Int.fract_eq_iff`, `Int.fract_eq_self`, `Int.fract_add_intCast`, `Int.fract_sub_intCast`, `Int.self_sub_fract`, `Int.self_sub_floor`, `Int.fract_nonneg`, `Int.fract_lt_one`.

## Log
- [start] Read statement, Setup.lean, Reduction.lean, renault.txt L40–253. Full interval-arithmetic decoding done (above). Compile baseline OK (~21 s).

## Progress log 2
- Helpers DONE and compiling: `fract_eq_of_floor`, `fract_eq_sub_one`, `fract_mul_nat'`, `bad_Icc_iff`, `bad_Ioo_iff`, `mem_Ioo_fract_iff`, `fract_two_mul`, `claim24` (72-case rcases+linarith works).
- GOTCHA: `push_neg` on `¬(a∧b)` gives `a→¬b` implication, NOT a disjunction. Use `rw [Set.mem_Icc, not_and_or, not_le, not_le] at h` for disjunctive form, same on goal for producing.
- GOTCHA: `omega` does NOT consume `↑k2 < 3/2` real-cast bounds; derive integer bounds via `have : (k:ℝ) < 2 := by linarith; exact_mod_cast this` then omega.
- GOTCHA: `le_or_lt` unknown identifier in this Mathlib; use `lt_or_ge`.
- `fract_eq_sub_one` (specialization of fract_eq_of_floor to k=1) avoids `(↑(1:ℤ))` cast pain: proof via `Int.fract_eq_iff` + `push_cast; ring`.
- Next: `step1`, `step2` case-bash lemmas, then main theorem.

## Progress log 3 (agent 2)
- File state on arrival: helpers + step1 + step2 already fully written; only sorry at lemma6_1 (~line 691). Compile showed 14 linarith errors in step1/step2 case-bashes.
- FIXES APPLIED (all `.1`/`.2` swaps or wrong-fact fixes):
  - `linarith [h.1, h1.1]` → `[h.2, h1.1]` ×4 (lines ~359,372,614,627): `v/u ∈ Ioo(1/6,1/2)` vs `∈ Ioo(2/3,1)` needs upper bound `<1/2` vs `>2/3`.
  - `linarith [h.2, h5.2]` → `[h.1, h5.2]` ×4 (~362,377,617,632): `∈Ioo(1/2,5/6)` vs `∈Ioo 0 (1/3)` needs `>1/2` vs `<1/3`.
  - `linarith [h3.1, h1.1]` → `[h3.2, h1.1]` ×2 (~421,675); `[h3.2, h5.2]` → `[h3.1, h5.2]` ×2 (~422,676).
  - line 551 `[h1.2, hv4.1]` → `[h1.2, hv3.1]`; line 573 `[h1.2, hu4.1]` → `[h1.2, hu3.1]`. NOTE: step1's analogues (303,317) are CORRECT as written — step1 `hc` is non-strict (`5/6 ≤ |u−v|`), step2 `hd` is strict (`|u−v|<5/6` on same branch), so step2 needs `v>1/3` (hv3.1) to get `u−v < 2/3` against `hd1 : 2/3 < u−v`.
- GOTCHA: `linarith` does NOT destructure `h : x ∈ Set.Ioo a b` in context; must pass `h.1`/`h.2` explicitly. Equations and plain comparisons ARE used.
- NEXT: helpers + main theorem per plan below.
- PLAN (implemented below): `fract_abs_cases` (fract d ∈ {|d|,1−|d|}), `fract_mem_Ioo_of_abs`, `abs_mem_of_fract`, `fract_sub_fract` (fract(pᵢ−pⱼ)=fract(λ(xᵢ−xⱼ))), `fract_two_mul_Ioo` (halving preimage), `delta_range`, `abs_diff_range`, `fract_two_delta`, `mem_Ioo_fract'`/`mem_Icc_fract'` (band-membership via integer translate + linarith), `d_of_bad`/`d_of_bad_sub`/`d_of_bad_one` (bad-disjunct → J/K interval, handling doubled shifts 2α/6 incl. s=1 and s=1+s'), `dlist` (all five d's per λ), `step1_pre`, `caseA` (u-high/v-low + swapped calls), `caseB` (α=4 squeeze + λ=4,α=1 finish + swapped calls), then `lemma6_1` by_contra assembly.
- Cast strategy: keep `((k:ℕ):ℝ)` forms from `bad`; convert `↑(2:ℕ)`→`(2:ℝ)` via `simp only [Nat.cast_ofNat]`; `exact_mod_cast` for claim24's literal-2 facts.

## Progress log 4 (final — COMPLETE, compiles clean)
- Remaining blockers on arrival: 2 `linarith failed` at `hd2` construction (~1189–1190).
- ROOT CAUSE FOUND (via full error log `error(lean.synthInstanceFailed)`, not `error:`): the `hd2`/`hf2` statement types used `Int.fract ((2 : ℕ) : ℝ * x₄)` — Lean parses this as `(2:ℕ) : (ℝ * x₄)` (the `:` ascription swallows `ℝ * x₄` as a "type") → `HMul Type ℝ ?m` + `Int.fract (2:ℕ)` → `Ring ℕ`/`FloorRing ℕ`/`AddGroup ℕ` synthesis failures. Consequence: `abs_mem_of_fract`'s implicit `{d}` never unified → `?d` stayed `?m.2053` → `by linarith` bound-args ran on metavar goals → failed; the leftover `AddGroup ℕ` instance goal then swallowed `obtain`/`have res`/`rcases` → `Or.casesOn can only eliminate into Prop` (propRecLargeElim).
- FIXES:
  1. Parenthesize every casted literal factor: `(((2 : ℕ) : ℝ) * x₄)` (and `x₅`) — applied throughout `hf2`, `hd2`, and the linarith hints. (Done in file; `dlist`/`caseB` already used `(((k:ℕ):ℝ)/6)` forms.)
  2. `hd2` built via tactic block `refine abs_mem_of_fract ?_ ?_ hf2` then two `· linarith [Int.fract_nonneg .., Int.fract_lt_one ..]` bullets — `refine` pins `?d` from `hf2` BEFORE the bound goals are created, so the goals are concrete `-1 < d` / `d < 1`.
- `push_neg` → `push Not` migration completed file-wide (deprecation warnings gone).
- VERIFICATION (2026-09-18, project root `07/`):
  - `lake env lean Research07/LRC6/Lemma61.lean` → exit 0, **zero output** (no errors, no warnings).
  - `lake env lean -o .lake/build/lib/lean/Research07/LRC6/Lemma61.olean Research07/LRC6/Lemma61.lean` → exit 0, olean 3.46 MB emitted.
  - `grep -nE "sorry|admit|native_decide|unsafe" Lemma61.lean` → empty.
  - `#print axioms lemma6_1` → `[propext, Classical.choice, Quot.sound]` — exactly the allowed set.
  - Statement frozen verbatim (checked lines 1099–1112): `∃ lam al:ℕ, 2≤lam≤5, 1≤al≤5` closed band `∨ ∃ al∈{1,2,3,4}` open band; doubled shift `2 * ↑al / 6` preserved on runner 2.

## FINAL ORCHESTRATOR SUMMARY
- **Status: DONE.** `Research07/LRC6/Lemma61.lean` (1229 lines) compiles clean under `import Mathlib` + `import Research07.LRC6.Setup` only; no sorry/admit/native_decide/unsafe; axioms = allowed set.
- **Proof shape** (by_contra assembly, lines ~1099–1229):
  1. `wit`/`wic` turn the two failed alternatives into per-witness contradictions; `bad lam al` = three-way ∉Icc disjunction for every `2≤λ≤5`, `1≤α≤5`.
  2. `dlist lam bad` produces the five J/K interval-covering disjunctions; `step1_pre` + `step1` give `|⟨λx₄⟩−⟨λx₅⟩| ∈ (1/6,5/6)` for all λ∈{2,3,4,5}.
  3. `δ := fract (x₄−x₅)`; `fract_sub_fract`+`fract_mul_nat'`+`fract_mem_Ioo_of_abs` turn step1 into `fract(λδ) ∈ (1/6,5/6)`; `claim24` contrapositive gives `δ ∉ (1/6,5/6)`; `delta_range` narrows to `δ ∈ (1/12,1/6)∪(5/6,11/12)`; `abs_diff_range` lifts to `|x₄−x₅|`.
  4. `fract_two_delta`+`abs_mem_of_fract` give `|⟨2x₄⟩−⟨2x₅⟩| ∈ (1/6,1/3)∪(2/3,5/6)`; `step2` (λ=2 case-bash) leaves exactly four configs (A: high/low ± mirror; B: mid-high/mid-low ± mirror).
  5. `caseA` discharges via open-band witnesses `wit`; `caseB` via α=4 open-band squeeze plus the λ=4,α=1 closed-band witness `wic`. All contradict hc1/hc2.
- **Key Lean gotchas logged for reuse**: (a) `linarith` needs explicit `.1`/`.2` Ioo components and `push_cast` before cast equations; (b) `omega` needs `exact_mod_cast` bridge for real-cast integer bounds; (c) `:`-ascription has low precedence — `((k:ℕ):ℝ) * x` MUST be written `(((k:ℕ):ℝ) * x)` or the ascription eats `ℝ * x` as a bogus type (`HMul Type ℝ`, `Ring/FloorRing/AddGroup ℕ` synth failures); (d) implicit args of lemmas only unify when a later explicit arg pins them — use `refine f ?_ ?_ h` (not `(by tac)` term args) when `by`-tactic goals must see the concrete implicit; (e) `error(lean.synthInstanceFailed)` lines don't match `grep "error:"` — use `grep -nE "error"` or check exit code.
- Failure ledger updated (`_dev/failures.md`, tag `ascription-precedence + implicit-mvar`).
- No remaining caveats. The lemma is ready for downstream use (Reduction.lean chain for lonely_runner_six / two-even case).
