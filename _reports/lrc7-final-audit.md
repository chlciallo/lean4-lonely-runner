# LRC7 Final Adversarial Audit — Statement Fidelity & Anti-Drift

**Scope.** Independent audit of the `n = 7` (Barajas–Serra 2008) layer of the Lean 4
Lonely Runner formalization at `D:\creation\Research_Projects\07`. Read-only: no source
files were modified. Independent evidence was produced with `lake env lean --stdin`
(`#check` / `#print axioms` / `#print`) against the already-built oleans — no files
written.

**Bottom line.** No drift found. All seven checklist items PASS. The `n = 7` layer
proves the real theorems with the real hypotheses; the axiom cone is exactly
`[propext, Classical.choice, Quot.sound]`; the case decomposition matches the paper.

---

## §1. Frozen headline statements — byte-level fidelity

`Research07/LRC7/Main.lean` was read in full (103 lines). Kernel-elaborated types were
independently confirmed via `#check` through `lake env lean --stdin`:

```
lrc7_int : ∀ (D : Finset ℕ), (∀ d ∈ D, 0 < d) → D.card ≤ 6 →
             ∃ t, 0 < t ∧ ∀ d ∈ D, 1/7 ≤ circ (t * ↑d)
lrc7_rel_rat : ∀ (w : Fin 6 → ℚ), (∀ i, w i ≠ 0) →
             ∃ t, 0 < t ∧ ∀ i, 1/7 ≤ circ (t * ↑(w i))
lonely_runner_seven_rat : ∀ (v : Fin 7 → ℚ), Function.Injective v →
             ∀ i, ∃ t, 0 ≤ t ∧ ∀ j ≠ i, 1/7 ≤ dist ↑(t*↑(v i)) ↑(t*↑(v j))
```

- `lrc7_int` — `Main.lean:29–34`. Matches the frozen text exactly (`(1 / 7 : ℝ)` vs
  the checklist's `(1/7 : ℝ)` is whitespace-only; same elaborated term). `circ (t * d)`
  elaborates to `circ (t * ↑d)` — the natural cast, as required.
- `lrc7_rel_rat` — `Main.lean:38–40`. Exact match.
- `lonely_runner_seven_rat` — `Main.lean:86–90`. Exact match; `dist` is on
  `UnitAddCircle`-coerced points (identical convention to the six-runner theorem).
  Proof (`Main.lean:91–103`): `Fin.succAbove` relative speeds → `lrc7_rel_rat` →
  `dist_unitAddCircle_eq_circ` + `circ_neg`. Sound.

**Comparison vs `lonely_runner_six_rat`** (`Research07/LRC6/Main.lean:118–134`): the two
statements are literal n-analogs — `Fin 6→Fin 7`, `Fin 5→Fin 6` (succAbove index),
`1/6→1/7`, `lrc6_rel_rat→lrc7_rel_rat`. Proof bodies are line-for-line identical
modulo these indices. Same for `lrc7_rel_rat` vs `lrc6_rel_rat` (`LRC6/Main.lean:30–72`)
— same denominator-clearing construction, `≤ 6` vs `≤ 5` card bound only.

**Verdict: PASS.**

---

## §2. Definition integrity — uniqueness & shared location

Repo-wide grep for `def`/`abbrev` of each audited name; exactly one definition each,
in the expected shared file, no parallel shadow copies under `Research07/LRC7/`:

| Name | Location | Body |
|---|---|---|
| `circ` | `LRC3/Circ.lean:17` | `noncomputable def circ x := ‖(x : UnitAddCircle)‖` (shared LRC3 layer; `#print circ` confirmed) |
| `good7` | `LRC7/Case5mBase.lean:130–131` | `∀ d ∈ A, qdig7 m (lam * d) ∉ ({0,6} : Finset (ZMod 7))` |
| `qdig7` | `LRC7/Discrete.lean:38` | `(↑((x % 7^(m+1)) / 7^m) : ZMod 7)` — leading base-7 digit |
| `runit7` | `LRC7/Discrete.lean:41` | `(↑(x / 7^(padicValNat 7 x)) : ZMod 7)` — unit part |
| `eMod7` | `LRC7/Differences.lean:55–61` | if-chain: `2x−y` / `2y−x` / `x−y` mod `7^{m+1}` |
| `residueRelOf` | `LRC7/Differences.lean:48–51` | same branch conditions as `eMod7` |
| `apLen` | `LRC7/Discrete.lean:383–384` | min covering `cycIv` length in `ZMod 7` |

`eMod7`/`residueRelOf` share identical guards (`runit7 y = 2*runit7 x` → `twoX` →
`2x−y`; `runit7 x = 2*runit7 y` → `twoY` → `2y−x`; else `same` → `x−y`), matching the
paper's `e(x,y)` case definition. The `same` fallback is disjoint from the `2·` guards
for `{1,2,4}`-valued units (if both held, `3r ≡ 0`, impossible mod 7), so no
misclassification. `absModN` itself is the genuine `min (x%N) (N−x%N)`
(`LRC5/Discrete.lean:33`, reused — documented at `Discrete.lean:29`).

Benign near-duplicates (not shadows of audited names): private utility lemmas with
identical names appear in `Differences.lean` and `Case5mBase.lean`/`Case5mTop.lean`
(e.g. `mul_pow_add_div`, `residue_decomp`) — private, same statements, documented as
local copies. `case61_dichot'` (Case5mTop.lean:420) vs `case61_dichot`
(Case5mBase.lean:1154) are distinct named theorems. `lemma9_i'`/`lemma9_ii3` are
primed variants, not redefinitions.

**Verdict: PASS.**

---

## §3. Case interfaces vs dispatcher

`case5m_dispatch` (`Case5mTop.lean:813–855`), `lrc7_case5m_of_cases` (988–1032) and
`lrc7_hc6_aux` (1047–1097) all carry **identical** `hc61`–`hc66` parameter shapes —
verified by reading all three signatures in full. The public case theorems match:

- `case61` (`Case5mC61.lean:1203`): `A.card = 5`, all `runit7 = s`, `s ∈ {1,2,4}` →
  `∃ lam, ¬7∣lam ∧ good7 m lam A`. Extra parameters `h10`/`h9ii` are **exactly**
  `lemma10`/`lemma9_ii` signatures (`Case5mL10.lean:1192`, `1764`) — verified
  side-by-side (bound-name `∃ h` vs `∃ ℓ` only; `(j : ZMod 7)` vs `((j:ℕ):ZMod 7)`
  defeq).
- `case62` (`Case5mC62.lean:3992`): `A1.card = 4`, `Ar.card = 1`,
  `∀ d ∈ Ar, runit7 d ∈ {2*s, 4*s}` — matches hc62.
- `case63` (`Case5mC63.lean:4903`): cards `3,1,1`, classes `s, 2s, 4s`.
- `case64` (`Case5mC64.lean:960`): cards `3,2`, classes `s, 2s`.
- `case65` (`Case5mC65.lean:5863`): cards `3,2`, classes `s, 4s`.
- `case66` (`Case66.lean:1387–1414`): cards `2,2,1`, classes `s, 2s, 4s`, plus the
  `hc66top` hypothesis — verbatim identical to `case66_top`'s type
  (`Case66.lean:3209–3226`), which supplies it (`Case5m.lean:47–48`).

`Case5m.lean:31–48` wires all six into `lrc7_hc6_aux` correctly, including the
`h10`/`h9ii` instantiation at line 36.

**Dispatch completeness** (`Case5mTop.lean:856–984`): `s` = argmax class; `A1, A2, A4`
are the runit filters; `interval_cases` on `A1.card ∈ {2,3,4,5}` (≤1 impossible since
sum=5 forces max ≥ 2 — `hA1ge` at 886–889). Branches: 5→hc61; 4→hc62 with
`Ar = A2∪A4`; 3→(1,1)=hc63 / (2,0)=hc64 / (0,2)=hc65; 2→(2,1)=hc66 directly,
(1,2)=hc66 under the `s ↦ 4s` rotation — arithmetic checked at lines 911–920
(`2·4s = s`, `4·4s = 2s` mod 7). All `(a2,a4)` with `a2,a4 ≤ a1`, `a2+a4 = 5−a1` are
covered.

`lrc7_hc6_aux` (1047–1097): identical hc6-signature inputs, `A.card = 5`,
`∀ d ∈ A, ¬7∣d`, `padicValNat 7 d6 = m`, `1 < m` → `∃ lam, 0 < lam ∧ ∀ d ∈ A∪{d6},
7^m ≤ absModN (lam*d) (7^{m+1})`. `lrc7_hc6` (`Case5m.lean:25–30`) is the public leaf;
`#check` confirmed it exactly matches the `hc6` parameter type in
`exists_mult_aux`/`lrc7_int_of_leaves` (`IntCase.lean:150–154`, `577–581`).

`lrc7_hc6_of` (`Case5mTop.lean:223–296`): `normU7` normalization
(`NormU.lean:45` — sign-flip into `{1,2,4}` classes, `normU7_absModN` flip-invariance
at 48) then dispatch on `|A'|`: ≤3→`lrc7_case3u_top` (145–152), =4→`lrc7_case4`
shaped set `A'∪{d6}`, =5→`hcase5`. Total coverage: `card_image_le` gives `|A'| ≤ 5`;
all sub-5 cases handled. This correctly models the paper's `x ∼ −x` pair-class
collapse.

`lrc7_int_of_leaves` (`IntCase.lean:570–584`) consumes `lrc7_case4`
(`Case4Int.lean:739–745`, exact hc4 shape) and `lrc7_hc6`; `Main.lean:34` instantiates
them. The `m₀ = 1` branch routes to `lrc7_m1` (`IntCase.lean:268–273`;
`Finite.lean:43` — the §7 finite case); `m₀ ≥ 2` routes to `hc6`. Branch-A filtering
(`filtered7_good`, `Filtering.lean:225`) handles `∀ j < m₀, |level j| ≤ 3`; the
`j₀ > 0` sub-branch scales by `7^{-j₀}` into the hc4 shape (`IntCase.lean:293–412`).

**Verdict: PASS.**

---

## §4. No vacuous or scope-shrinking assumptions

- **`good7` is the real bound.** `good7 m lam A` = every `qdig7 m (lam·d) ∉ {0,6}`
  (Case5mBase.lean:130–131). `absModN_ge_iff_qdig7` (`Discrete.lean:163–166`) proves
  `7^m ≤ absModN (lam*d) (7^{m+1}) ↔ 1 ≤ (qdig7 m (lam*d)).val ≤ 5` under
  `padicValNat 7 d < m`, `0 < d`, `¬7∣lam`. `qdig7 ∉ {0,6}` ⟺ `val ∈ [1,5]` —
  genuinely equivalent to the distance bound, not weakened. `lrc7_case5m_of_cases`
  applies this bridge at `Case5mTop.lean:1039` plus `absModN_top_ge7` for `d6`.
- **Unit hypotheses are exactly `padicValNat 7 d = 0`** (case theorems) or the
  equivalent `¬ 7 ∣ d` (hc6 interface, `IntCase.lean:151`; `lrc7_hc6_of` converts via
  `normU7_padic`). No strengthening (e.g. no `d < N`, no extra coprimality, no
  restricted residue sets beyond the `{1,2,4}` normalization that `normU7`
  *produces*, not assumes).
- **`s ∈ {1,2,4}`** is the paper's sign-class normalization, discharged by
  `normU7_runit` — not an extra hypothesis on the original `A`.
- **`case63`/`case65` take `hm : 1 < m`; `case61`/`case62`/`case64`/`case66` take
  `2 ≤ m`.** On `ℕ` these are the same proposition (`1 < m` ≡ `2 ≤ m` definitionally);
  `lrc7_hc6` supplies `hm : 1 < m` (`Case5m.lean:28`) and the dispatcher's
  `_hm : 2 ≤ m` (`Case5mTop.lean:813`) is compatible both directions. No narrowing.
- **Conclusions are not weakened**: every case produces `∃ lam, ¬7∣lam ∧ good7 …`;
  `lrc7_hc6_aux` produces `0 < lam` plus the `absModN` bound on `A ∪ {d6}`
  (the `¬7∣lam` conjunct is dropped only at the `hc6` boundary, where
  `exists_mult_aux` doesn't need it — `IntCase.lean:153`). `lrc7_int_of`
  (`IntCase.lean:558–566`) yields `t = lam/M > 0` — strict positivity as required.
- **`lrc7_int` admits `D.card ≤ 6`** — the correct general statement (duplicates
  collapse; the empty/small cases are handled, e.g. `IntCase.lean:508–510`).

**Verdict: PASS.**

---

## §5. Construct hygiene

Greps across `Research07/LRC7/*.lean` + `Research07/Audit.lean`:

- `axiom`, `@[implemented_by]`, `native_decide`, `unsafe`, `sorry`, `admit`,
  `decide!`, `Lean.ofReduceBool`, `addDecide`, `opaque`, `@[extern]`, `partial def`,
  `macro` — **zero hits in code** (all matches were inside docstrings/comments).
- `set_option` keys used: `maxHeartbeats`, `maxRecDepth`, `synthInstance.maxSize`
  only. None of the flagged keys (`debug.`, `trace.`, `unification.`,
  `synthInstance.maxHeartbeats`, `relaxedAutoImplicit`, `autoImplicit true`) appear.
- `decide +kernel` certificates: `FiniteStage1.lean:46–103+`, `FiniteStage2` per-Q
  tables, plus `decide` on finite `ZMod 7`/`Finset` propositions throughout — all
  kernel-reduction paths, permitted by the checklist. Independently confirmed: the
  axiom audit of `stage1`/`stage2` shows no `Lean.ofReduceBool` (§7 below).
- `classical` tactics appear (local `open Classical`/proof-level classicality) — these
  contribute only `Classical.choice`, which is whitelisted.

**Verdict: PASS.**

---

## §6. Paper fidelity vs `_external/bs7-ejc.txt`

Section markers located directly in the reference text:

| Paper | Text line | Statement | Code |
|---|---|---|---|
| §6.1 | bs7:582 | `\|A1\| = 5` | `case61` (Case5mC61.lean:1203, card 5, single class) |
| §6.2 | bs7:620–621 | `\|A1\| = 4`, `r(d5) ∈ {2s,4s}` | `case62` (hc62: `runit7 d ∈ {2*s,4*s}` on the 1-set) |
| §6.3 | bs7:625 | `\|A1\|=3, \|A2\|=1, \|A4\|=1` | `case63` |
| §6.4 | bs7:711 | `\|A1\|=3, \|A2\|=2` | `case64` (class-`2s` block) |
| §6.5 | bs7:740 | `\|A1\|=3, \|A4\|=2` | `case65` (class-`4s` block) |
| §6.6 | bs7:764–770 | `\|A1\|=2`; `r(e12),r(e34) ∈ {1,2,4}`; split on `ν(e12)=ν(e34)` and at `=m`: (a) `r(e12)=2r(e34)`, (b) `r(e12)=4r(e34)` | `case66` + `hc66top` (`ν(e12)=ν(e34)=m` exactly); `case66_top_core` (Case66.lean:3130–3143) splits via `zmod7_ratio124` into ratio 1/2/4 — consistent since `4 = 2⁻¹` mod 7 |

Supporting lemmas mapped: Lemma 9(i/ii) → `lemma9_i` (Case5mL9.lean:281),
`lemma9_ii`/`lemma9_i'`/`lemma9_ii3` (Case5mL10.lean:1764, 2537; Case5mL9b.lean:603);
Lemma 10 → `lemma10` (Case5mL10.lean:1192); Lemma 11 → `lemma11`
(Case5mL10.lean:934); Lemma 5 → `lemma5` (Compress.lean:279, `apLen ≤ 5` + `(3,1,1)`
exceptional branch); Lemma 6 → `lemma6` (Compress.lean:387); Lemma 12 → `lemma12`
(Compress.lean:516, `A₂.card ≤ 2` + exceptional condition). §5 (`|A| = 4`) →
`lrc7_case4` (Case4Int.lean:739); §7 (`m = 1`) → `lrc7_m1` (Finite.lean:43) via
`stage1`/`stage2`.

**§7 fidelity detail** (bs7:802–810): the paper's three exceptional sets
`{1,3,4,5,18}`, `{1,4,6,10,11}`, `{1,4,6,10,22}` (up to dilation) and the `Z₉₈`
verification with `gcd(D) = 1`. Code: `badSets49` (FiniteBase.lean:54–64) lists 63
literal sets = the three `U₄₉/{±1}` orbits (the three paper representatives appear at
positions 1, 3, 4); `stage2` (FiniteStage2.lean:3647–3653) checks each `T ⊆ lifts98 Q`
(`|T| ≤ 5`), `r ∈ {7,…,42}`, **with the odd-element side condition**
`(∃ x ∈ insert r T, x % 2 = 1)` — the faithful `gcd(D)=1` model (comment at
3641–3645 explicitly notes all-even configs genuinely fail); `lrc7_m1` discharges it
via `2^ν₂`-halving (`hd0odd`, Finite.lean:67–82). `stage1` (FiniteStage1.lean:274–276)
proves every non-bad `Q` has a unit multiplier in `units21`.

**Verdict: PASS.**

---

## §7. Axiom-audit coverage

`Research07/Audit.lean:43–45` prints axioms for `lrc7_int`, `lrc7_rel_rat`,
`lonely_runner_seven_rat` — confirmed verbatim.

**Independent verification** (not relying on Audit.lean or prior claims): ran
`lake env lean --stdin` with `#print axioms` over 24 declarations — every one
returned exactly `[propext, Classical.choice, Quot.sound]`:

`lrc7_int`, `lrc7_rel_rat`, `lonely_runner_seven_rat`, `lrc7_hc6`, `lrc7_m1`,
`lrc7_case4`, `case61`, `case62`, `case63`, `case64`, `case65`,
`LRC7Case66.case66`, `LRC7Case66.case66_top`, `stage1`, `stage2`, `lemma10`,
`lemma11`, `lemma9_ii`, `lemma5`, `lemma6`, `lemma12`, `filtered7`,
`lrc7_case3u_top`, `good7`.

Crucially, `lrc7_int` is the **root of the entire LRC7 dependency cone**
(`lrc7_int_of_leaves lrc7_case4 lrc7_hc6`, with `lrc7_m1`/`stage1`/`stage2` inside the
`exists_mult_aux` tree and `case61`–`case66` inside `lrc7_hc6`). Its clean axiom set
transitively certifies every dependency: any `sorryAx`/`ofReduceBool`/custom axiom
anywhere in the tree would surface in that print. None did.

**Verdict: PASS.**

---

## Anomalies / observations (non-blocking)

1. `Research07/LRC7/_reports/lrc7-sec6-case66-top5.md` — an agent report file lives
   *inside* the source tree (`LRC7/`). It is a `.md`, not imported; harmless but
   misplaced (should live in the top-level `_reports/`). Housekeeping only.
2. `exists_mult_aux`'s `hc6` hypothesis uses `¬ 7 ∣ d` while case theorems use
   `padicValNat 7 d = 0` — equivalent for positive `d`; converted by `normU7_padic`.
   Consistent, not a mismatch.
3. `badSets49`'s 63-set literal list is asserted to be the three `U₄₉/{±1}` orbits —
   the comment says "independently verified"; the three paper representatives are
   present in the list. A skeptic could re-derive the orbit closure externally, but
   `stage1`/`stage2` are `decide`-checked regardless of how the list was produced
   (the list only *names* which sets need stage-2 treatment; `stage1` proves all
   *other* reps49 5-subsets good, so completeness is machine-checked, not assumed).
4. Audit.lean also `#print`s axioms for `prop3_1`/`prop4_1`/`prop5_4`/`prop6_6`
   (lines 46–49) — these are LRC6 declarations, correctly labeled as supporting
   theorems, not LRC7 leakage.
5. Whitespace: frozen text `(1/7 : ℝ)` vs source `(1 / 7 : ℝ)` — identical term.

## Final checklist

| # | Item | Verdict |
|---|---|---|
| 1 | Frozen headline statements (byte-level + elaborated `#check`) | **PASS** |
| 2 | Definition integrity (single defs, expected files, no shadows) | **PASS** |
| 3 | Six case interfaces vs dispatcher + `case66_top` wiring + coverage | **PASS** |
| 4 | No vacuous shortcuts (`good7`↔`7^m ≤ absModN`, `hunit`, `hm` compat) | **PASS** |
| 5 | Construct hygiene (no axiom/native_decide/sorry/unsafe/decide!; clean options) | **PASS** |
| 6 | Paper fidelity §6.1–§6.6 + §7 finite layer | **PASS** |
| 7 | Audit coverage + independent axiom run (24 decls, whitelist only) | **PASS** |

**Overall: PASS — no statement weakening, definition swaps, or vacuous-hypothesis
shortcuts detected in the `n = 7` layer.**

## Structured summary for the orchestrator

- Files read (audit evidence): `LRC7/Main.lean` (full), `LRC6/Main.lean` (full),
  `LRC7/Case5mTop.lean` (69–160, 215–296, 810–1190), `LRC7/Case5m.lean` (full),
  `LRC7/Case5mBase.lean` (110–160), `LRC7/Case5mC61.lean` (1196–1260),
  `LRC7/Case5mL10.lean` (1192–1230, 1764–1800), `LRC7/Case66.lean` (1387–1440,
  3107–3226), `LRC7/Discrete.lean` (30–89, 155–204, 375–414),
  `LRC7/Differences.lean` (30–89), `LRC7/IntCase.lean` (140–293, 293–412, 490–584),
  `LRC7/Case4Int.lean` (739–780), `LRC7/Finite.lean` (30–90),
  `LRC7/FiniteBase.lean` (36–115), `LRC7/FiniteStage1.lean` (sigs),
  `LRC7/FiniteStage2.lean` (sigs + 3640–3680), `LRC7/NormU.lean` (sigs),
  `LRC3/Circ.lean:17`, `LRC5/Discrete.lean:33`, `Research07.lean`, `Audit.lean`
  (full), `_external/bs7-ejc.txt` (§5–§8, lines 342–833).
- Commands run: repo greps (defs, hygiene, signatures), `lake env lean --help`,
  two `lake env lean --stdin` sessions (24× `#print axioms`; 6× `#check` + 2×
  `#print`), `git status` (no source modifications by this agent).
- Files written: `_reports/lrc7-final-audit.md` (this file only).
- Independent verification performed (not trusting prior claims): elaborated types
  of all three headline theorems; axiom sets of 24 LRC7 declarations; paper section
  text comparison; dispatcher coverage arithmetic.
- No source edits, no scratch files, no build artifacts touched.
