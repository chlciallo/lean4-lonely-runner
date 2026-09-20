# lrc7-compress.md — §6 compression + finite-check toolkit (Compress.lean)

Agent: U3 `Compress.lean` (slug lrc7-compress). Build:
`cd D:\creation\Research_Projects\07 && lake build Research07.LRC7.Compress`

## Status log

### 2026-09-18 — Paper statements extracted + finite facts pre-verified

Sources: `_external/bs7-ejc.txt` lines 481–525 (Lemma 5/6), 559 (Remark 8),
714–730 (Lemma 12); cross-checked `_external/bs7.txt` lines 602–746 (arXiv HTML,
better symbol rendering — Lemma 6 ẽ-conditions are **negative** `∉`, stripped
in the EJC pdftotext).

**Exact paper statements (EJC):**
- **Remark 8.** X⊂Z. (i) q(X−X)⊂{0,6} ⇒ ℓ(k·X)≤k+1, 1≤k≤6.
  (ii) q(X−X)⊂{0,1,5,6} ⇒ ℓ(X)≤3.
- **Lemma 5.** ℓ(A1)+ℓ(A2)+ℓ(A4)≤5 ⇒ ∃λ∈Λ₀: q(λA)∩{0,6}=∅,
  unless (ℓ)=(3,1,1) and ẽ(d,d′)∈{2,4} ∀d∈A2,d′∈A4.
  λ_k = 1+7^m·k·s⁻¹ gives q-shift **+jk** on class-j element (j∈{1,2,4}).
- **Lemma 6.** q(A1)⊂{1,…,ℓ(A1)}, d∈A1 with q(d)=1 ⇒ ∃λ∈Λ₀ covering if:
  (i) (5,0,1)+ẽ(d,d′)∉{4,6}∀d′∈A4, or (5,1,0)+ẽ(d,d′)∉{2,3}∀d′∈A2;
  (ii) (4,0,2), or (4,2,0)+ẽ(d,d′)≠4 (d′∈A2∩q⁻¹(i), q(A2)={i,i+1});
  (iii) (3,3,0) or (3,0,3).
- **Lemma 12.** |A1|=3,|A2|=2, d∈A1 anchor of covering interval, d′∈A2:
  (i) ℓ(A1)≤3 ⇒ ∃k∈{0,1,2} covering; (ii) ℓ(A1)=4 ∧ ẽ(d,d′)∈{0,1,6} ⇒ covering.
- **ẽ formulas (class ratios s:2s:4s, uniform in s):**
  ẽ(d₁∈A1, d′∈A4) = 2q(d′)−q(d₁) [r(d₁)=2r(d′)];
  ẽ(d₁∈A1, d′∈A2) = 2q(d₁)−q(d′) [r(d′)=2r(d₁)];
  ẽ(d₂∈A2, d′∈A4) = 2q(d₂)−q(d′) [r(d′)=2r(d₂)].

**Python pre-verification (`_dev/compress_check.py`, exhaustive over Z₇):**
- lemma5 core: interval-level disjunction TRUE **only with** the ordering
  constraint `apLen A2 ≤ apLen A1 ∧ apLen A4 ≤ apLen A1` (paper's "A1 = a class
  with *larger* length" convention). Counterexamples without it: exactly the
  (1,1,3),(1,3,1) shapes at 4 (j2,j4) pairs. ⇒ added as hypothesis `hord`.
- (3,1,1) exceptional: no-shift-works ⇒ 2i2−i4∈{2,4} confirmed exactly.
- lemma6 all six triples verified (i2,i4 over all Z₇).
- lemma12 (i),(ii) verified over all A2 (card≤2, 29 subsets) × l1.
- remark8 (i),(ii) verified over all 128 subsets.
- exists_shift_avoid (L≤5) verified.

**Shift parameterization decision:** public statements use the *pure shift*
`∃ t : ZMod 7` / `∃ k ∈ {0,1,2}` on A1 (A2 gets `2t`, A4 `4t`) — this is the
paper's `q(λ_k d) = q(d) + jk` with λ_k = 1+7^m·k·s⁻¹; equivalently the
unnormalized family λ'_k = 1+7^m·k gives shift `k·s` (k·s ranges over all Z₇
for s≠0). The `s ∈ {1,2,4}` hypothesis is kept as the class marker (caller
needs it for the integer-side multiplier construction); Z₇ combinatorics do
not depend on it.

### 2026-09-18 — Infrastructure + Remark 8 green

`Compress.lean` first milestone builds clean (~22s): `bad06`, `avoids06`,
cycIv helpers (`mem_cycIv`, `cycIv_zero/one/two/seven`, `cycIv_image_add`),
`avoids06_of_subset_shift` (subset transport through `+t` shift),
apLen helpers (`apLen_le_seven`, `apLen_empty`, `nonempty_of_apLen_pos`,
`eq_singleton_of_apLen_one`, `card_le_one_imp_apLen_le_one`,
`one_lt_card_of_apLen_ge_two`), `exists_shift_avoid`, `remark8_i`,
`remark8_ii` (via private `decide` certificates — need
`set_option maxRecDepth 16384` for `decide` over `Finset (ZMod 7)`).
`#print axioms` on both: `[propext, Classical.choice, Quot.sound]` ✓.

Notes: mathlib v4.34 has NO `ZMod.val_eq_zero` (renamed/removed) — use
`ZMod.natCast_zmod_val` round-trip instead (`eq_zero_of_val_eq_zero` helper).
`Finset.image_subset_image` exists.

### 2026-10-02 — Lemmas 5/6/12 landed; module green

`lake build Research07.LRC7.Compress` succeeds (23s, 8927 jobs). All six
`#print axioms` report `[propext, Classical.choice, Quot.sound]` — zero
`sorry`/`admit`/`native_decide`/`unsafe` (grep-verified).

Key engineering notes for callers:
- **Fin.val whnf-timeout (important):** `apLen X` unfolds to
  `(apScores X).min' ⋯` and is whnf-opaque; unifying
  `(⟨apLen A₁,_⟩ : Fin n).val =?= apLen A₁` blows the 200k-heartbeat budget
  (reproduced `_dev/scratch/probe2.lean`). All private cores therefore
  quantify `∀ m ∈ Finset.range n` (decidable bounded-forall) instead of
  `l : Fin n`; applications pass `apLen A₁` with
  `Finset.mem_range.mpr (by omega)` so no `.val` reduction is ever needed.
- Private `decide` cores need `set_option maxRecDepth 16384` (lemma5_core
  uses 32768); lemma6 cores are small enough for plain `decide`.
- `avoids06` needs a local `Decidable` instance
  (`inferInstanceAs (Decidable (∀ x ∈ X, x ∉ bad06))`) for the decide cores.

## Interface section — final API (Research07/LRC7/Compress.lean)

Module: `import Research07.LRC7.Compress` (imports `Research07.LRC7.Discrete`).

**Definitions**
- `bad06 : Finset (ZMod 7) := {0, 6}` (line 43)
- `avoids06 (X : Finset (ZMod 7)) : Prop := ∀ x ∈ X, x ∉ bad06` (line 47)
  + `instance : Decidable (avoids06 X)` (line 49)

**cycIv / apLen helpers** (public): `mem_cycIv` (73),
`cycIv_zero` (76), `cycIv_one` (87), `cycIv_two` (99),
`cycIv_image_add` (119), `avoids06_of_subset_shift` (134),
`cycIv_seven` (140), `apLen_le_seven` (145), `apLen_empty` (149),
`nonempty_of_apLen_pos` (154), `eq_singleton_of_apLen_one` (160),
`card_le_one_imp_apLen_le_one` (169), `one_lt_card_of_apLen_ge_two` (178),
`add_one_ne_self` (185), `avoids06_mono` (52), `avoids06_union` (55),
`avoids06_union3` (69), `avoids06_empty` (66).

**exists_shift_avoid** (line 205):
```lean
theorem exists_shift_avoid {X : Finset (ZMod 7)} {i : ZMod 7} {L : ℕ}
    (hL : L ≤ 5) (hX : X ⊆ cycIv i L) :
    ∃ t : ZMod 7, avoids06 (X.image (· + t))
```

**remark8_i** (line 228):
```lean
theorem remark8_i {B : Finset (ZMod 7)}
    (hB : ∀ x ∈ B, ∀ y ∈ B, (x - y : ZMod 7) ∈ ({0, 1, 6} : Finset (ZMod 7)))
    {k : ZMod 7} (hk : k ≠ 0) :
    apLen (B.image (· * k)) ≤ k.val + 1
```

**remark8_ii** (line 242):
```lean
theorem remark8_ii {B : Finset (ZMod 7)}
    (hB : ∀ x ∈ B, ∀ y ∈ B, (x - y : ZMod 7) ∈ ({0, 1, 5, 6} : Finset (ZMod 7))) :
    apLen B ≤ 3
```

**lemma5** (line 279) — conclusion is the shift-or-exception disjunction;
`_hs`/`s` kept as the congruence-class marker (unused in Z₇ proof):
```lean
theorem lemma5 {A₁ A₂ A₄ : Finset (ZMod 7)} (s : ZMod 7)
    (_hs : s ∈ ({1, 2, 4} : Finset (ZMod 7)))
    (hord : apLen A₂ ≤ apLen A₁ ∧ apLen A₄ ≤ apLen A₁)
    (h : apLen A₁ + apLen A₂ + apLen A₄ ≤ 5) :
    (∃ t : ZMod 7, avoids06
        ((A₁.image (· + t)) ∪ (A₂.image (· + 2 * t)) ∪ (A₄.image (· + 4 * t)))) ∨
    (apLen A₁ = 3 ∧ apLen A₂ = 1 ∧ apLen A₄ = 1 ∧
      ∀ d ∈ A₂, ∀ d' ∈ A₄, (2 * d - d' : ZMod 7) ∈ ({2, 4} : Finset (ZMod 7)))
```

**lemma6** (line 387) — six-way disjunction with `ẽ` side-conditions folded in;
`hA1` is the normalized covering `A₁ ⊆ cycIv 1 (apLen A₁)`, `_hd` the anchor
`1 ∈ A₁` (used by callers to justify the normalization; unused in Zₗ proof):
```lean
theorem lemma6 {A₁ A₂ A₄ : Finset (ZMod 7)} (s : ZMod 7)
    (_hs : s ∈ ({1, 2, 4} : Finset (ZMod 7)))
    (_hd : (1 : ZMod 7) ∈ A₁)
    (hA1 : A₁ ⊆ cycIv 1 (apLen A₁))
    (h : (apLen A₁ = 5 ∧ apLen A₂ = 0 ∧ apLen A₄ = 1 ∧
            ∀ d' ∈ A₄, (2 * d' - 1 : ZMod 7) ∉ ({4, 6} : Finset (ZMod 7)))
       ∨ (apLen A₁ = 5 ∧ apLen A₂ = 1 ∧ apLen A₄ = 0 ∧
            ∀ d' ∈ A₂, (2 - d' : ZMod 7) ∉ ({2, 3} : Finset (ZMod 7)))
       ∨ (apLen A₁ = 4 ∧ apLen A₂ = 0 ∧ apLen A₄ = 2)
       ∨ (apLen A₁ = 4 ∧ apLen A₂ = 2 ∧ apLen A₄ = 0 ∧
            ∀ d' ∈ A₂, (d' + 1 : ZMod 7) ∈ A₂ → (2 - d' : ZMod 7) ≠ 4)
       ∨ (apLen A₁ = 3 ∧ apLen A₂ = 3 ∧ apLen A₄ = 0)
       ∨ (apLen A₁ = 3 ∧ apLen A₂ = 0 ∧ apLen A₄ = 3)) :
    ∃ t : ZMod 7, avoids06
      ((A₁.image (· + t)) ∪ (A₂.image (· + 2 * t)) ∪ (A₄.image (· + 4 * t)))
```
`ẽ` mapping (normalized anchor `q(d)=1`): `d' ∈ A₄ → ẽ = 2q(d')−1`;
`d' ∈ A₂ → ẽ = 2−q(d')`. The (4,2,0) side-condition is stated for the lower
element `d'` of `A₂ = {i₂, i₂+1}` via `d'+1 ∈ A₂` (singleton-lower-element
form of the paper's `ẽ(d,d') ≠ 4` for `d' ∈ A₂ ∩ q⁻¹(i)`).

**lemma12** (line 516):
```lean
theorem lemma12 {A₁ A₂ : Finset (ZMod 7)} (s : ZMod 7)
    (_hs : s ∈ ({1, 2, 4} : Finset (ZMod 7)))
    (_hd : (1 : ZMod 7) ∈ A₁)
    (hA2 : A₂.card ≤ 2)
    (hA1 : A₁ ⊆ cycIv 1 (apLen A₁))
    (h : apLen A₁ ≤ 3 ∨ (apLen A₁ = 4 ∧
        ∃ d' ∈ A₂, (2 - d' : ZMod 7) ∈ ({0, 1, 6} : Finset (ZMod 7)))) :
    ∃ k ∈ ({0, 1, 2} : Finset (ZMod 7)),
      avoids06 ((A₁.image (· + k)) ∪ (A₂.image (· + 2 * k)))
```

**Audit lines kept in source** (info-only, allowed):
`#print axioms remark8_i/remark8_ii` (246–247),
`#print axioms lemma5/lemma6` (485–486),
`#print axioms lemma12/exists_shift_avoid` (538–539).

## Orchestrator summary

- **Status:** DONE. `lake build Research07.LRC7.Compress` green, all axioms
  `[propext, Classical.choice, Quot.sound]`, no forbidden tokens.
- **Deliverable:** `Research07/LRC7/Compress.lean` (~540 lines), finite
  ZMod-7 forms of Remark 8, Lemmas 5/6/12 + cycIv/apLen/shift helpers.
- **Caller-facing conventions:**
  - Shifts: `∃ t : ZMod 7`, A₂ shifted by `2t`, A₄ by `4t` (= λ_k's `+jk`);
    lemma12 shifts by `k ∈ {0,1,2}` / `2k`.
  - `s : ZMod 7, s ∈ {1,2,4}` is a marker hypothesis (unused in Z₇).
  - `avoids06`/`bad06` are the q(λA)∩{0,6}=∅ model.
  - lemma5 needs `hord` (A₁ longest) — required, verified by exhaustive check.
  - lemma6/lemma12 take the normalized covering `A₁ ⊆ cycIv 1 (apLen A₁)`
    and anchor `1 ∈ A₁`; `ẽ` conditions inlined in the disjunctions.
  - apLen-side inputs remain arbitrary Finsets; wrappers use
    `apLen_le_iff` + `avoids06_of_subset_shift`.
- **Watch-item for downstream:** never unify `(⟨apLen X,_⟩ : Fin n).val`
  against `apLen X` — whnf-timeout; the range-bounded core signatures avoid
  it. If integer bridge needs `Fin`, convert via `Fin.ofNat'`/explicit casts,
  not `.val` round-trips on `apLen` terms.
- **Verification artifacts:** `_dev/compress_check.py` (exhaustive checker),
  `_dev/scratch/probe2.lean` (whnf-timeout repro).
