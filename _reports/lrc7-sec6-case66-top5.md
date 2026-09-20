# lrc7-sec6-case66-top5 — finish `case66_top` in Case66.lean

Agent #5 on this task (4 predecessors died on connection interrupts, NOT design
failures). Report is durable memory: appended every ~10 tool calls.

## 2026-09-19 20:20 — Boot / state audit

- Working dir: `D:\creation\Research_Projects\07\Research07\LRC7`
- File: `Case66.lean`, 2158 lines, compiles 0 errors (orchestrator-verified).
- `_reports/lrc7-sec6-case66.md` (the referenced design doc) DOES NOT EXIST —
  predecessors apparently never persisted it. Reconstructing design from the
  task contract + the file itself.
- Created `_reports/`, `_dev/` dirs. Datestamp: Sat Sep 19 20:20 2026.

## Task contract (verbatim essentials)

1. `case66b_finish` — mirror of `case66a_finish`: normalized `e12 = 7^m`,
   `e34 = 2*7^m`, anchor d4, digits `{k, k+2, 4*x+4*k, 4*x+4*k+1, 2*k-y}`.
2. `case66a`/`case66b` — ratio dispatchers: unit `λ₀` normalizes to (2,1)/(1,2)
   model; `(x,y)∈bad66a` → ε-corner via `case66a_eps` +
   `exists_multLow_one_set_seven'` + `sigma_eps_magic`; else `case66*_finish`.
3. `case66_top` — signature frozen (see contract). Pure-top `e = r*7^m`; swaps
   normalize `r12,r34∈{1,2,4}`; ratio1→scalar→both top digits 6→lemma5 ending;
   ratio2→case66a; ratio4→case66b.
- Insert before `end LRC7Case66`. NO sorry/admit/native_decide/unsafe.
- Compile ONLY `lake env lean Research07/LRC7/Case66.lean`.

## Plan

1. Read §4/§5 of Case66.lean (lines 1620-2158) to learn `case66a_finish`
   shape + all helpers.
2. Read `Case5mBase.lean` tables ~1281-1328 (`bad66a`, `case66a_bad`,
   `case66a_eps`, `case66b_good`, `case66b_sig*_dec`).
3. Write `case66b_finish` mirroring `case66a_finish`.
4. Write `case66a`/`case66b` dispatchers.
5. Write `case66_top`.

## 2026-09-19 20:25 — Recon complete (design reconstructed, baseline green)

Baseline: `lake env lean Research07/LRC7/Case66.lean` → 0 errors (~4min compile).

### Paper text recovered (`_external/bs7-ejc.txt` §6.6, line 764-799)

- Ratio-1 (r12=r34): scalar `c` w/ `c·r=6` makes both `q(λe)∈{0,6}` →
  `case66_finish` (lemma5 ending). [contract says "scalar makes both top
  digits 6"]
- Case (a) `r12=2r34`: normalize e12=2N/7,e34=N/7 via scalar `c=r34⁻¹`.
  `λk∈Λ₀`, `q(λk d2)=k∈{1,2,3}`; model `{k,k+2,2k−x,2k−x+1,4y+4k}`,
  `x=ẽ(d2,d4)`, `y=ẽ(d2,d5)`. Bad set `bad66a={(4,2),(4,4),(5,4),(6,4),(6,6)}`.
  Escapes: ν(e24)<m→Lemma7(i) puts x∉{4,5,6}; ν(e24)=m,ν(e25)<m→Lemma7(i)
  on (d5,d2) puts y∉{2,4} (r24∈{4,5}) or y∉{4,6} (r24∈{0,6});
  both pure-top→ε-corner: `(x,y)=(q(e24)−ε₁,q(e25)−ε₂)` realized by
  `q(λ·7d5)=4ε₂+2ε₁` (Λ₁-shift, σ-magic on shared d2-low-block).
- Case (b) `r34=2r12`: normalize e12=N/7,e34=2N/7 via `c=r12⁻¹`. Anchor
  `q(λk d4)=k`; model `{k,k+2,4x+4k,4x+4k+1,2k−y}` (`x=ẽ(d2,d4)`,
  `y=ẽ(d4,d5)`). Lemma 7 forces `x∉{2,4}` then `case66b_good` ∀b.

### Key derivation (verified against file machinery)

- `e ≡ 0 mod 7^m` + `e<7^{m+1}` ⟺ `e = Q·7^m`, `Q=e/7^m<7`.
  `etd7_twoX_of_low`/`etd7_twoY_of_low` give `ẽ = Q − σ`,
  `σ = 2·(lo%7^m)/7^m ∈ {0,1}` → `ẽ ∈ {Q−1,Q}`.
- Λ₁-shift `λ=1+k·7^{m−1}`: `(λd)%7^m = d%7^{m−1}+A·7^{m−1}`,
  `A=digit7(m−1)(λd)=q(λ·7d)` settable via `exists_multLow_one_set_seven'`
  (need `c63_lo1`-style clone for Case66).
- twoX σ after shift: `σ'=(2A+β)/7`, `β=2·(d%7^{m−1})/7^{m−1}`.
- Chained (twoY (d2,d5) link forces `(λd2)%7^m=(2(λd5)%7^m)%7^m` =
  `((β5+2A5)%7)·7^{m−1}+r5`): `σ₁'=(2·((2A5+β5)%7)+c2)/7`,
  `c2=2·((2(d5%7^{m−1}))%7^{m−1})/7^{m−1}`. `sigma_eps_magic` with
  `A5=4ε₂+2ε₁` gives σ₂'=ε₂, σ₁'=ε₁.
- `case66b` σ-force: `sigma_single`: A₂=4a → σ'=a; `case66b_sig1_dec`
  (Q∈{2,4}→σ=1→x=Q−1∈{1,3}), `sig0_dec` (Q∈{3,5}→σ=0→x=Q),
  `auto_dec` (Q∈{0,1,6}→{Q−1,Q}∩{2,4}=∅).
- `exists_multLow_etd7_avoid` needs `0<ν`; ν=0 (e≢0 mod 7, e≠0) needs a
  variant — proof identical since `hν` only used for `e≠0`. Will add
  `exists_multLow_etd7_avoid'` taking `he0` + `hνm:ν<m` (j<m incl 0 works:
  `lambda_low_top_resid` covers j=0 too).
- Scaled-element bookkeeping: `eMod7_smul` (runit7 c≠0),
  `padicValNat_mul_seven`, `runit7_mul`, `good7` conversion via mul_assoc.

### Implementation plan (bottom-up)

1. `multLow1_lo` (lo-block clone) + `exists_multLow_etd7_avoid'` +
   `good7_of_scalar_mul` helpers.
2. `case66b_finish` (mirror of `case66a_finish`, anchor d4).
3. `case66a_go`/`case66b_go` — normalized dispatches (incl ε-corner).
4. `case66a`/`case66b` — scalar-normalizing wrappers.
5. `case66_top` — swap-normalize via `neg_mem124`+`eMod7_same_swap`+
   `neg_resid`, ratio split {1,2,4}²→9 cases→{eq,caseA,caseB}.

## 2026-09-19 20:52 — case66b_finish COMPILED (0 errors)

`case66b_finish` added at ~line 2162: mirror of `case66a_finish`, anchor d4,
model `{k,k+2,4x+4k,4x+4k+1,2k−y}`, x=ẽ(d2,d4), y=ẽ(d4,d5), ha : x∉{2,4}.

KEY TOOLING FINDING: `ring`/`linear_combination` on `ZMod 7` do NOT reduce
coefficients mod 7 (`8*a=a` fails). Any "divide by 2" step
(K*(2s)=-q4 ⟹ K*s=-4q4) must inject `(4:ZMod7)*2=1` via `decide` then
`←mul_assoc`/`one_mul` plumbing. Verified in _dev/scratch/TestZ7.lean.
