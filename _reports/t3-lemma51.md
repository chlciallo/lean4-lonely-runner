# T3 — Lemma 5.1 (`lemma5_1`) — work log

## Task
Prove `lemma5_1` in `Research07/LRC6/Lemma51.lean` (FROZEN statement, no changes):
three positions `x₃, x₄, x₅ ∈ [0,1)`, either `∃(λ,α)∈{2..5}×{1..5}` with all
`fract(λxᵢ+α/6) ∈ Icc(1/6,5/6)`, OR `∃α∈{1,2,4}` with all
`fract(xᵢ+α/6) ∈ Ioo(1/6,5/6)`. Renault Lemma 5.1 (combinatorial core, unique-even
n=6 case). No sorry/admit/native_decide/unsafe.

## Status: IN PROGRESS — helper lemmas done & compiling, main case tree next

---
## 2026-09-18 — Session 1

### Verified API (via #check, all confirmed)
- `Int.fract_eq_iff : fract a = b ↔ 0≤b ∧ b<1 ∧ ∃z:ℤ, a-b=↑z`  ← key for `fract y = y-k`.
- `Int.fract_add_intCast`, `Int.fract_sub_intCast`, `Int.fract_eq_self` (iff),
  `Int.fract_nonneg`, `Int.fract_lt_one`, `Int.self_sub_floor`, `Int.floor_le`,
  `Int.lt_floor_add_one`, `Int.floor_nonneg : 0≤⌊a⌋↔0≤a`.
- `div_lt_iff₀ : 0<c → (b/c < a ↔ b < a*c)`, `lt_div_iff₀ : 0<c → (a<b/c ↔ a*c<b)`.
- `fract_self_add : fract(x+s)=fract(fract x + s)` (from Setup.lean).
- `mul_lt_mul_of_pos_left`, `mul_nonneg`, `Set.mem_Icc/Ioo/Ico`.

### Helper lemmas — ALL COMPILING (above lemma5_1, `private`)
- `fract_eq_sub_of_mem`: `k≤y<k+1 → fract y = y-k`. Core primitive.
- `bad_iff`: for `u∈[0,1)`, `al∈{1..5}`:
  `fract(u+al/6) ∉ Icc(1/6,5/6) ↔ u ∈ Ioo ((5-al)/6, (7-al)/6)`.
  Proof via `fract y ∈ Icc ↔ y∈[1/6,5/6]∪[7/6,11/6]` (since y=u+al/6∈[1/6,11/6)).
  This is the `⟨λx+α/6⟩∈(5/6,1/6) ⇔ ⟨λx⟩∈((5-α)/6,(7-α)/6)` shift.
- `mul_preimage`: `fract(lam·x)∈Ioo p q → ∃n:ℤ, 0≤n∧n<lam ∧ x∈Ioo((n+p)/lam,(n+q)/lam)`.
- `preimage2` (lam=2): `fract(2x)∈Ioo p q → x∈Ioo(p/2,q/2) ∨ x∈Ioo((1+p)/2,(1+q)/2)`.
- `fract_mul_Ioo`: `x∈Ioo a b`, `n≤lam·a`, `lam·b≤n+1` → `fract(lam·x)∈Ioo(lam·a-n, lam·b-n)`.
- `fract_add6_Ioo`: `x∈Ioo a b`, `n+1/6 < a+al/6`, `b+al/6 < n+5/6` →
  `fract(x+al/6)∈Ioo(1/6,5/6)` (for exhibiting property (2)).
- `one_per_third`: from `a,b,c ∈Ico 0 1` + three third-cover disjunctions
  (`hT1:∈Ioo(0,1/3)`, `hT2:∈Ioo(1/3,2/3)`, `hT3:∈Ioo(2/3,1)`), conclude the
  6-permutation disjunction (exactly one value per open third = bijection runner↔third).
  Proved by 27-way `rcases` + `first | exact disj | exfalso;linarith`.

### Key design decisions
- Proof is `by_contra`/`push_neg`: `h1` = failure of disj1 (∀(λ,α) some runner bad),
  `h2` = failure of disj2 (∀α∈{1,2,4} some runner not in Ioo).
- `bad`/`badU`: convert `h1` (per λ, per α) into "runner's `fract(λx) ∈ B_α`" via
  `fract_self_add` + `bad_iff`. `B_α = ((5-α)/6,(7-α)/6)`; `B₅=T1`, `B₃=T2`, `B₁=T3`.
- `one_per_third` gives the runner↔third bijection per λ.
- Role-parameterized case lemmas (proved once, applied per permutation):
  `lam2_caseA{yA yB yC}` = λ=2 case (a); `lam2_caseB` = case (b); case (c) direct.

### Interval arithmetic verified (matches renault.txt lines 130–144)
- λ=2 case(a): `fract(2yA)∈(0,1/6)`, `fract(2yB)∈(1/3,1/2)`, `fract(2yC)∈(2/3,5/6)`
  → yA∈(0,1/12)∪(1/2,7/12), yB∈(1/6,1/4)∪(2/3,3/4), yC∈(1/3,5/12)∪(5/6,11/12)
  → fract(3·) ranges; 3 subcases (which runner is λ=3's T1) → α=2,4,1 resp.
- λ=2 case(b): symmetric; hard subcase (x₅ is λ=3-T3) → λ=4 case-(a) then λ=5
  no-runner-in-T2 contradiction. Verified all interval computations.
- λ=2 case(c): `fract(2yA)∈[1/6,1/3)`, `fract(2yC)∈(2/3,5/6]` → `fract(4yA)∈[1/3,2/3)`,
  `fract(4yC)∈(1/3,2/3]` → two runners in T2 for λ=4 → contradicts one_per_third.

### Gotchas / fixes applied
- `set`-bound `k` cannot be `subst`'d → use `rcases ... with hkk` + `rw [hkk] at hfl`.
- `norm_num at h` unfolds `∈Set.Ioo` to raw `∧` — avoid inside lemmas that need Ioo form;
  ∧-form is still defeq so `exact` works at call sites.
- `first |` (not `first [...]`) is the correct Lean4 alternatives syntax.
- `push_neg` deprecated → use `rw [not_lt]`, `not_or`, `push Not` where possible.
- `linarith` can't multiply → supply `mul_lt_mul_of_pos_left` facts explicitly.
- `simpa`→ prefer `norm_num at h; exact h` to dodge style warning.

### TODO
- `badU` extraction (h1 → per-(λ,α) bad-runner disjunctions) inside lemma5_1.
- `lam2_caseA`, `lam2_caseB`, `lam2_caseC` role-parameterized lemmas.
- λ=2 top-level dispatch over the 6 perms × (a)/(b)/(c).
- Assemble `lemma5_1`, clean warnings, compile exit 0.

---
## 2026-09-18 — Session 2 (subagent continuation)

### Fixes applied to prior helpers (file did NOT compile clean before)
- `bad_iff` line ~74: `norm_num at h0` reduced `Int.fract_sub_intCast y 1` to `True`
  (it's `@[simp]` — norm_num applies it). Fixed via `Int.cast_one` rewrite + exact.
- `fract_add6_Ioo`: hypotheses `n+1/6 < a+al/6`, `b+al/6 < n+5/6` were TOO STRICT —
  boundary cases need `≤` (e.g. w∈(5/6,11/12), α=2, n=1: `5/6+2/6 = 7/6 = n+1/6`).
  Changed both to `≤`; conclusion still strict Ioo since x∈(a,b) is strict.
- After fixes: file compiles, only `sorry` warning at lemma5_1.

### New verified API (scratch-tested in _dev/scratch/l51test.lean)
- `↑(2:ℕ)` and `(2:ℝ)` are DEFEQ: `exact h` works across `Int.fract (↑2*x)` vs `Int.fract (2*x)`.
- `norm_num at h` on `f ∈ Set.Ioo ((5-↑5)/6)((7-↑5)/6)` → `0 < f ∧ f < 1/3`
  (normalizes Nat.cast→numeral, evaluates endpoints, unfolds mem_Ioo to ∧).
- `norm_num at h` on disjunction of such → disjunction of ∧-forms.
- `Set.Ioo_subset_Ioo : a₂ ≤ a₁ → b₁ ≤ b₂ → Ioo a₁ b₁ ⊆ Ioo a₂ b₂`.
- `fract_nat_mul d k t : fract(↑d*(↑k*t)) = fract(↑k*fract(↑d*t))`.
- `not_and_or : ¬(a∧b) ↔ ¬a∨¬b`; `Int.self_sub_fract : a - fract a = ↑⌊a⌋`.
- `Int.fract_add_intCast : fract(a+↑m)=fract a` (@[simp]).

### Architecture decided (supersedes "TODO" in Session 1)
- `Thirds a b c` = abbrev for the 6-perm disjunction (one_per_third's conclusion type).
- `lam2_analysis {u v w}` (private): ONE role-parameterized lemma for the whole λ=2
  trichotomy. u=T1-role, v=T2-role, w=T3-role at λ=2. Internally by_cases:
  `f_u2∈(0,1/6)`→lam2_caseA; else `f_w2∈(5/6,1)`→lam2_caseB; else case (c) inline.
- `lam2_caseA`/`lam2_caseB` take: `hu hv hw : ·∈Ico 0 1`, `hbad` (role-ordered
  ∀ lam al bad-arc 3-way), `hgood` (role-ordered ∀ al∈{1,2,4} conjunction→False),
  and λ=2 memberships. They build `Thirds` at λ=3 internally from hbad via
  one_per_third + b1of..b5of conversions — NO Perm6 reordering needed anywhere.
- lemma5_1: `bad`, `good`, `hthird` haves; `hthird 2` → 6 perms; per perm ONE
  `lam2_analysis` call with 3-line match-reorder of `bad`/`good` + role-ordered
  Ico hyps + the perm's hT1/hT2/hT3 (already in role order: disjunct is
  `runner∈T1 ∧ runner∈T2 ∧ runner∈T3`).
- New helpers: `fract_add_int_right` (fract(a+y)=fract(a+fract y)),
  `fract4_eq` (fract(4x)=fract(x+fract(3x))), `fract5_eq'` (=fract(x+fract(4x))),
  `fract5_eq` (=fract(fract3x+fract2x)), `fract_add_Ioo`, `fract_wrap`,
  `branch_pick` (select preimage branch by fract image disjointness),
  `thirds_T1`/`thirds_T3`/`thirds_T2_unique` (Thirds eliminators).

### Verified interval arithmetic for case (b) hard subcase
- KEY SLICK STEP: in caseB subcase-w, `f_w3≤5/6` isn't needed as trichotomy —
  `hbad 3 2` (B_2=(1/2,5/6)) directly forces w: f_u3,f_v3∈(1/4,1/2) are
  STRICTLY <1/2 hence ∉(1/2,5/6) → f_w3∈(1/2,5/6)∩(3/4,1)=(3/4,5/6) STRICT.
  Gives f_w4∈(1/3,1/2) strict — no Ioc bookkeeping needed.
- Subsub-i (v is λ3-T1): f_v3∈(1/4,1/3), f_u3∈(1/3,1/2); f_u4=fract(u+f_u3)∈(3/4,1),
  f_v4∈(0,1/6), f_w4∈(1/3,1/2); `hbad 4 2` → f_u4∈(3/4,5/6); then
  f_u5∈(1/6,1/3), f_v5∈(3/4,1), f_w5∈wrap(11/12,7/6)→≤1/6∨>11/12. No T2-runner.
- Subsub-ii (u is λ3-T1): f_u3∈(1/4,1/3), f_v3∈(1/3,1/2); f_u5=fract(f_u3+f_u2)∈(1/12,1/3),
  f_v5∈wrap(5/6,7/6)→≤1/6∨>5/6, f_w5∈wrap(11/12,7/6)→≤1/6∨>11/12. No T2-runner.

---
## 2026-09-19 — Session 3 (subagent continuation, repair + finish)

### State found on arrival
- File 772 lines. Helpers (21–336) + `lam2_caseA` (342–482) + `lam2_caseB` (486–754)
  written; `lemma5_1` still `sorry` (line 770). `lam2_caseC`/`lam2_analysis`/main body
  NEVER written (died mid-write on connection error).
- BROKEN: 6 `branch_pick` call sites pass `⟨Int.fract_nonneg _, h·⟩` as the
  `fract(3·) ∈ Ioo p q` arg — `Int.fract_nonneg` gives `0 ≤ f` but Ioo needs `0 < f`.
  Sites: lines 589, 592 (subcase u-T3), 600, 606 (subcase v-T3), 615, 618 (subcase w-T3).

### Fix plan (verified against branch_pick signature + interval arithmetic)
- Add `low_branch {f} (hlt : f < 2/3) : f ∈ Ioo(3/4)1 ∨ f ∈ Ioo(1/4)(1/2) → f ∈ Ioo(1/4)(1/2)`.
- Each broken `hf` becomes `low_branch h·lt f·3(.symm)` giving `fract(3·)∈Ioo(1/4)(1/2)`,
  i.e. p=1/4,q=1/2. Disjointness `q=1/2 ≤ 3·c−n` holds in all 6 sites (rhs=3/4).
- fv3 has order `Ioo(3/4,1)∨Ioo(1/4,1/2)` → use directly; fu3/fw3 reversed → `.symm`.
- Pass explicit `(p := 1/4) (q := 1/2)` so `hd`'s `by norm_num` sees concrete goal.

### Verified: existing (non-broken) branch_pick calls
- sub1 huI: pu.symm(a=11/12,b=1,c=5/12,d=1/2,n=1), hd Or.inl `1/2≤2/3` ✓
- sub2 hvI: pv(a=1/4,b=1/3,c=3/4,d=5/6,n=2), hd Or.inl `1/2≤2/3` ✓
- sub3 hwI: pw.symm(a=7/12,b=2/3,c=1/12,d=1/6,n=0), hd Or.inl `1/2≤2/3` ✓
- caseB refinements hv2/hw2 via `hbad 2 2`/`hbad 2 4`: B_2=(1/2,5/6) kills u(>5/6),
  w(<1/3) → v∈(1/2,2/3); B_4=(1/6,1/2) kills u, v(via hv2) → w∈(1/6,1/3) ✓

### Remaining construction
- `lam2_caseC` (role u=T1,v=T2,w=T3): hu2∈Ico[1/6,1/3), hw2∈Ioc(2/3,5/6] →
  fract(4u)=fract(2·fract 2u)∈[1/3,2/3)⊆Icc, fract(4w)∈(1/3,2/3]⊆Icc →
  Thirds@4 (hbad 4·5/3/1) → `thirds_T2_unique hT h4u h4w` : False. NO hgood needed.
- `fract(4x)=fract(2·fract(2x))` via `4x=2x+2x` + `fract_self_add` + `fract_add_int_right`.
- `lam2_analysis` (u=T1,v=T2,w=T3): by_cases f2u<1/6 → caseA(u,v,w);
  else by_cases 5/6<f2w → caseB(w,v,u) (reversed roles!); else caseC(u,v,w).
- lemma5_1: by_contra+not_or → hbad (per (λ,α): ¬all-good → some runner's
  fract(λx)∈B_α via fract_self_add+bad_iff contrapos), hgood (h2 instantiator),
  hthird λ (hbad λ·5/3/1→one_per_third). hthird 2 → rcases 6 perms → per perm:
  lam2_analysis with role-ordered Ico + first-trick Or-reorder lambda + hgood perm-map.
- hgood perm maps (args i_r1 i_r2 i_r3 → x₃,x₄,x₅ order):
  p1(a,b,c); p2(a,c,b); p3(b,a,c); p4(c,a,b); p5(b,c,a); p6(c,b,a).
- `fract_self_add (x s) : fract(x+s)=fract(fract x+s)` — VERIFIED in Setup.lean:88.

---
## 2026-09-19 — Session 3, part 2: DONE — compiles exit 0, all gates pass

### What was broken vs. what was added
- REPAIRED (mid-write debris): 6 `branch_pick` sites passed
  `⟨Int.fract_nonneg _, h·⟩` where Ioo needs `0 < f` (strict). Added `low_branch`
  helper (line 340): `f < 2/3 → f ∈ Ioo(3/4)1 ∨ Ioo(1/4)(1/2) → f ∈ Ioo(1/4)(1/2)`.
  Sites now pass `low_branch h·lt f·3(.symm)` (p=1/4,q=1/2; `hd`'s norm_num
  discharges `1/2 ≤ 3·c−n = 3/4`). fv3 order matches directly; fu3/fw3 need `.symm`.
- REPAIRED: 3 `fract_wrap` calls in caseB hard subcase — implicit `s` stayed a
  metavariable (only constraint came from `by linarith` args → circular, linarith
  fails on `?m` goals). Fixed by explicit `(s := ·)`: `fract(3v)+fract(2v)` (line 679),
  `fract(3w)+fract(2w)` (line 687), `w + fract(4w)` (line 747).
- ADDED `lam2_caseC` (line 775): role order u=T1,v=T2,w=T3; takes
  `hu2 : fract(2u) ∈ Ico[1/6,1/3)`, `hw2 : fract(2w) ∈ Ioc(2/3,5/6]` (NO hgood —
  pure counting). `fract(4x)=fract(2·fract(2x))` via `4x=2x+2x` + `fract_self_add`
  + `fract_add_int_right` + `congr 1; ring`. Then `fract(4u)∈[1/3,2/3)` (fract_eq_self,
  2y∈[1/3,2/3)⊆[0,1)), `fract(4w)∈(1/3,2/3]` (fract_eq_sub_of_mem k=1,
  2y∈(4/3,5/3]→2y−1), both ⊆ Icc(1/3,2/3); Thirds@4 via hbad 4·(5,3,1)+one_per_third;
  kill via `thirds_T2_unique hT h4u h4w`.
- ADDED `lam2_analysis` (line 833): by_cases `fract(2u)<1/6` → caseA(u,v,w);
  else by_cases `5/6<fract(2w)` → caseB(w,v,u) REVERSED roles (caseB's u=T3-runner);
  else caseC(u,v,w) with `⟨not_lt.mp ha, h1T.2⟩` / `⟨h3T.1, not_lt.mp hb⟩`.
  caseB's role-reversed hbad via `rcases hbad … <;> first | Or.inl|Or.inl∘Or.inr|Or.inr∘Or.inr`
  and hgood via `fun al hm iw iv iu => hgood al hm iu iv iw`.
- WROTE `lemma5_1` body (line 870+): `by_contra`+`not_or` → `hbad` (per (λ,α):
  `by_contra`+`not_or`² → `apply h1` + 3×`rw [fract_self_add]; by_contra hmem;
  exact nb· ((bad_iff (fract_nonneg _)(fract_lt_one _) ha1 ha5).mp hmem)`),
  `hgood` (`fun al hm i3 i4 i5 => h2 ⟨al, hm, i3, i4, i5⟩`), `hthird λ`
  (hbad λ·5/3/1 → norm_num → one_per_third), `hT := hthird 2` ascribed to
  literal-2 Thirds (defeq ↑2↔2 held). rcases 6 perms → per perm ONE
  lam2_analysis call: Ico args (h3,h4,h5 permuted), hbad role-reorder lambda
  (first-trick, uniform), hgood perm map: p1(a,b,c) p2(a,c,b) p3(b,a,c)
  p4(c,a,b) p5(b,c,a) p6(c,b,a).

### Verified compile facts (from real errors)
- `⟨Int.fract_nonneg _, ·⟩` NEVER works as an Ioo-membership proof (≤ vs <).
- Implicit args whose only constraints come from `by tac` args stay metavars —
  linarith can't run on `?m` goals. Pass `fract_wrap (s := ·)` explicitly.
- `Int.fract (↑(2:ℕ) * x)` defeq `Int.fract (2 * x)` CONFIRMED again: hT ascribed
  literal-2 type from hthird's `↑lam` form works; all lam2_* boundary hyps
  (h1T/h2T/h3T literal-2 Ioo) exact-match.
- `rw [Set.mem_Ioc] at hw2` gives `2/3 < f ∧ f ≤ 5/6` (pair works with linarith).
- `_hu/_hv/_hw` prefix kills unusedVariable linter in lam2_caseC (Ico args are
  genuinely unused — one_per_third gets `⟨fract_nonneg _, fract_lt_one _⟩`).

### FINAL STATE (verified 2026-09-19)
- `lake env lean Research07/LRC6/Lemma51.lean` → **exit 0, ZERO warnings/errors**.
- grep `sorry|admit|native_decide|unsafe` → clean. 974 lines.
- `#print axioms lemma5_1` → `[propext, Classical.choice, Quot.sound]` ✓ gate.
- olean emitted: `.lake/build/lib/lean/Research07/LRC6/Lemma51.olean`.
- lemma5_1 statement FROZEN-untouched; all helpers `private` above it.

### Structured summary for orchestrator
- STATUS: **lemma5_1 PROVED AND VERIFIED**. File at
  `Research07/LRC6/Lemma51.lean` (974 lines), compiles clean under
  `lake env lean` (exit 0, no warnings), zero forbidden tactics, axiom gate clean.
- Proof follows renault.txt L5.1 exactly: by_contra → bad-arc disjunctions →
  one_per_third per λ → λ=2 trichotomy (a)/(b)/(c) via role-parameterized
  lam2_caseA/B/C + lam2_analysis dispatch over the 6 Thirds-permutations.
- New decls: `low_branch` (L340), `lam2_caseC` (L775), `lam2_analysis` (L833),
  `lemma5_1` body (L870–972). All case lemmas private; statement unchanged.
- Caveats for downstream: `hbad`-style role-ordered disjunctions reorder via the
  `rcases … <;> first | exact Or.inl h | …` pattern (uniform, no per-perm maps
  needed for Or-chains; hgood still needs explicit perm maps — listed above).
- Scratch file `_dev/scratch/l51_axioms.lean` (axiom check) — dev-only, outside
  import tree; safe to delete.
