# T3 — Lemma 6.4 formalization log (Lemma64.lean)

Task: replace `sorry` in `lemma6_4` (Research07/LRC6/Lemma64.lean) with full proof.
Frozen statement; helpers allowed above it. No sorry/admit/native_decide/unsafe.

## Math verification (from _external/renault.txt lines ~224-228)

Contradiction proof. ¬(1) ⇒ some xᵢ ∈ [5/12,7/12] (fract(2x)∉(1/6,5/6) for
x∈[1/6,5/6] ⟺ x∈[5/12,7/12]: 2x∈[1/3,5/3], fract=2x or 2x−1; unsafe iff
2x≥5/6 or 2x−1≤1/6). ¬(2) at α=1 ⇒ some xᵢ≥2/3 (fract(x+1/6)∉(1/6,5/6);
x+1/6∈[1/3,1], unsafe iff x+1/6≥5/6 or x=5/6 exactly). ¬(2) at α=5 ⇒ some
xᵢ≤1/3 (fract(x+5/6)=x−1/6∈[0,2/3], unsafe iff x−1/6≤1/6).
Three witnesses distinct (disjoint intervals) ⇒ permutation of {x₃,x₄,x₅}:
mid a∈[5/12,7/12], low b∈[1/6,1/3], high c∈[2/3,5/6].

Core: u=⟨3a⟩=3a−1∈[1/4,3/4]; v=⟨3b⟩∈[1/2,1)∪{0} (3b∈[1/2,1]);
w=⟨3c⟩=3c−2∈[0,1/2]. F(k)=failure of (3,α) for α=k∈{0..5} after
fract_self_add; G(k)=same for λ=5.
F(0): u always safe ⇒ v unsafe (v∈(5/6,1)∪{0}=Case A) or w unsafe
(w<1/6=Case B).
- Case A: F(2)⇒u>1/2; F(4)⇒w>1/6; F(5)⇒w<1/3; F(3)⇒u<2/3;
  F(1)⇒v≠0⇒v>5/6. Hence a∈(1/2,5/9), b∈(5/18,1/3), c∈(13/18,7/9).
  G(5): ⟨5a⟩+5/6, ⟨5b⟩+5/6, ⟨5c⟩+5/6 all safe ⇒ contradiction.
- Case B: F(4)⇒u<1/2; F(2)⇒v∈(1/2,5/6); F(1)⇒v>2/3; F(3)⇒u>1/3;
  F(5)⇒w>0. Hence a∈(4/9,1/2), b∈(2/9,5/18), c∈(2/3,13/18).
  G(1): all safe ⇒ contradiction.
Verified all endpoint arithmetic by hand.

## Plan
Helpers: `fract_sub_of_le` (fract z = z−n for z∈[n,n+1));
`safe6`/`unsafe6` (fract(y+k/6)∈[1/6,5/6] iff y+k/6∈[1/6,5/6]∪[7/6,11/6],
y∈[0,1), k≤5); `not_fst/snd/thd`; `key_mid/key_hi/key_lo` (witness
extraction); `lemma6_4_core` (a,b,c permuted roles + failure hyp ⇒ False).
Main: by_contra, extract 3 witnesses, 27-way rcases, 6 viable branches.

## 2026-09-18 — Compile-error fix session (subagent t3-fix)

Baseline `lake env lean Research07/LRC6/Lemma64.lean` errors (full log captured):
- Cast mismatches `↑(1:ℤ)` vs `(1:ℝ)` at lines 47, 84, 106, 127, 133 (fract_eq_sub call sites).
- Line 141: `rw [h] at h1` rewrites `Int.fract_lt_one` result to `3*b<1` but goal needs `fract(3b)<1` — broken regardless of casts.
- `↑k/6` vs `k/6` literal mismatches at 215,217,219,220,254,259,263,267,269 (safe6/unsafe6 call sites).
- Heartbeat timeouts at 302:60 (simp inside linarith) and 310:4 — Lean aborted elaboration there; lines 311-460 never checked.
- Warning: unused `push_cast` at line 28.

Verified: `Int.fract_eq_iff : fract a = b ↔ 0 ≤ b ∧ b < 1 ∧ ∃ z : ℤ, a-b=↑z` (Floor/Ring.lean:430); `fract_self_add` in LRC6/Setup.lean:88.

Plan (per orchestrator): retype fract_eq_sub n:ℤ→ℝ with `∃ k:ℤ, n=k`; retype safe6/unsafe6 k:ℕ→ℝ with `hk : 0≤k∧k≤5`; fix hvb rw bug; add `.1` projections in 6 dispatch args (simp [Set.mem_Icc] turns hx4 into And, `⟨hx4,l4⟩` would mismatch); local maxHeartbeats on lemma6_4_core + lemma6_4.

## 2026-09-18 — RESOLVED: file compiles clean, olean emitted

### Root causes found (beyond orchestrator diagnosis)
1. **fract_eq_sub/safe6/unsafe6 casts** — as diagnosed; retyped `n:ℤ→ℝ` with
   `(hn : ∃ k : ℤ, n = k)`; `k:ℕ→ℝ` with `hk : 0 ≤ k ∧ k ≤ 5`. Call-site arity
   preserved for safe6/unsafe6; fract_eq_sub sites gained `⟨N, by norm_num⟩`.
2. **F/G inner quantifiers also ℕ-typed** (NOT in diagnosis): `F : ∀ k : ℕ` made
   `F 1` produce `↑(1:ℕ)/6` while safe6 call sites now produce literal `1/6` —
   mismatches at lines 219, 223, 269, 337, 341, 372. Fix: same pattern —
   `∀ k : ℝ, (∃ n : ℕ, k = n) → k ≤ 5 → ...`, body does `obtain ⟨n,rfl⟩`,
   `exact_mod_cast` for `n ≤ 5`. All 13 call sites gained `⟨N, by norm_num⟩`.
3. **hvb proof bug** (line ~139): `rw [h] at h1` rewrote `Int.fract_lt_one`'s
   result `fract(3b)<1` into `3*b<1`, then used it where `fract(3b)<1` was
   needed. Fixed: `⟨by linarith, Int.fract_lt_one (3*b)⟩`.
4. **set_option placement**: `set_option ... in` between doc comment and decl
   fails parse ("unexpected token 'set_option'; expected 'lemma'"). Must go
   BEFORE the `/-- -/` doc comment.
5. **Heartbeat timeouts** at old lines 302/310: both inside lemma6_4_core;
   400000 heartbeats on lemma6_4_core + lemma6_4 suffices (2× default).

### False leads
- `⟨hx4.1, l4⟩` projection idea: WRONG — hx4 is already `1/6 ≤ x₄` (from
  `obtain` at line ~404), not an And. Reverted; original `⟨hx4, l4⟩` correct.

### Final state
- `lake env lean Research07/LRC6/Lemma64.lean` → exit 0, ZERO errors, ZERO warnings.
- `lake env lean -o .lake/build/lib/lean/Research07/LRC6/Lemma64.olean` → emitted (2.77 MB).
- No sorry/admit/native_decide/unsafe (grep: only `unsafe6` ident + comment words).
- `theorem lemma6_4` statement UNCHANGED (frozen). Helpers changed:
  - `fract_eq_sub (z:ℝ)(n:ℝ)(hn:∃k:ℤ,n=k)(h0:n≤z)(h1:z<n+1) : fract z = z-n`
  - `safe6/unsafe6` `(k:ℝ)(hk:0≤k∧k≤5)`; `F/G` `(k:ℝ)(∃n:ℕ,k=n)→k≤5`.
  - `set_option maxHeartbeats 400000 in` on lemma6_4_core + lemma6_4 only.
- `_dev/failures.md` line appended.
