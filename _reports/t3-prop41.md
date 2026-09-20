# T3 — Prop 4.1 (three even speeds) work log

Task: create `Research07/LRC6/Prop41.lean` proving `prop4_1` (frozen signature).
Build: `export PATH="$HOME/.elan/bin:$PATH"`, `lake env lean Research07/LRC6/Prop41.lean`.

## 2026-09-19 — recon

Read `_external/renault.txt` §4 (lines 102–112), `Reduction.lean`, `Setup.lean`,
`Driver.lean`, `Prop54.lean`.

Paper structure (line refs):
- PARA1 (l.108): x₁ safe, x₂ ∈ [5/6,1/6] CLOSED arc, x₄=0 → ∃l∈{1,2,4,5} all-safe.
  B₅ ≤1 or 2 consecutive; B₃ ≤1 or distance-3 pair.
- PARA2 (l.109): x₁ safe, x₅ ∈ [5/6,1/6], x₄=0 → ∃l∈{1..5} all-safe.
  B₅ ⊆ {1,5}; B₂,B₃ ≤1 or distance-3.
- Combine (l.110): x₄=0 ∧ x₁∈Icc ⇒ x₂,x₃,x₅ ∈ (1/6,5/6) open, x₅ ∈ (1/3,2/3)
  (else t+1/2 works).
- Divisibility (l.111): ¬(v₄|v₁) → s with x₄(s)=0, x₁(s)∈[1/12,1/6]∪{1/5};
  x₅(2s),x₅(4s)∈(1/3,2/3) but x₅(4s)=⟨2x₅(2s)⟩ impossible → v₄|v₁.
- 6v₄|v₁, 6v₅|v₁ (l.112): e₁=0,|e₄|=1 ⇒ v₁≥6v₄, v₁≥6v₅.
- Finish (l.112): t̃=1/(6v₁); at λt̃ (λ∈{1..5}) x₁ safe, x₄,x₅<1/6 unsafe →
  arg3 contrapositive ⇒ x₂,x₃ ∈ (1/6,5/6) → Claim 2.4 contradiction.
- Argument 3 (l.95): x₁ safe + ≥3 of {2..5} in [5/6,1/6] ⇒ ∃l∈{0,1,2} t+l/3 ∈D.

Key notation: [5/6,1/6] = closed unsafe arc = ∉Ioo(1/6,5/6) (boundary counts);
(5/6,1/6) = open arc = ¬safe6 (∉Icc). B-sets use open arc.

## Design (lean decl plan)

- `fract_int_mul`: `fract(n·fract x) = fract(n·x)` for n:ℤ (int `fract_nat_mul`).
- `unsafe_add_shift_Icc`: u∈[0,1), u∉Ioo(1/6,5/6), fract s∈{1/3,1/2,2/3}
  ⇒ fract(u+s)∈Icc. (closed-arc input; output may hit boundary)
- `unsafe_add_shift_Ioo`: u∈[0,1), u∉Icc, fract s∈{1/3,1/2,2/3}
  ⇒ fract(u+s)∈Ioo. (strict; for pairwise exclusions)
- `unsafe_pair_sixth`: d≡e mod6, fract(e(b-a)/6)∈{1/3,1/2,2/3} ⇒
  safe6 d (t+a/6) ∨ safe6 d (t+b/6). (bad_third_le_one analogue for sixths)
- mirror: for e=±2, pos(t+4/6)=pos(t+1/6), pos(t+5/6)=pos(t+2/6) (e·3/6=±1 int).
- `arg_zero_pm2` (PARA1, generic roles a,z,y,b,c): x_a∈Icc, x_b∉Ioo, x_z=0
  ⇒ ∃l∈{1,2,4,5} all five safe.
- `arg_zero_pm1` (PARA2): x_a∈Icc, x_y∉Ioo, x_z=0 ⇒ ∃l∈{1..5} all safe.
- `combine_zero`: x_z=0 ∧ safe6 a ⇒ x_b,x_c∈Ioo(1/6,5/6) ∧ x_y∈Ioo(1/3,2/3)
  (t+1/2 argument: b,c,a even → unchanged; z odd → 1/2; y odd → u+1/2).
- `arg3`: safe6 a t + 3 runners ∉Ioo + 4th ⇒ ∃l∈{1,2} all-safe → contra.
- `exists_int_mul_Ioo_band`: u∈(0,1/6)∪(5/6,1) ⇒ ∃λ:ℤ, fract(λu)∈[1/12,1/6].
- `fract_two_Ioo`: u∈Ioo(1/3,2/3) ⇒ fract(2u)∉Ioo(1/3,2/3).
- residue facts: e∈{±1,±2}⇒¬3|d; e=±1⇒d odd∧¬3|d (gcd(d,6)=1); e∈{0,±2}⇒2|d.
- `dvd_of_odd_runner` (z|a): full divisibility chain via combine_zero.
- finish: t̃=1/(6a), arg3 contrapositive + claim2_4 on x_{b}(t̃).

Signature check: `hv1 : (v₁:ℤ) ≡ 0 [ZMOD 6]` → 6|v₁ via Int.modEq_zero_iff_dvd.

## 2026-09-30 — COMPLETE: prop4_1 verified, all gates pass

`lake env lean Research07/LRC6/Prop41.lean` → **exit 0** (zero warnings).
`lake build` (full) → Prop41.olean emitted, `prop4_1` available to `IntCase`.

### Tail fixes applied by orchestrator
1. Set-equality rewrites (`insert_comm` chains) replaced — `{v₄}` is `singleton`,
   not `insert v₄ ∅`; `ext+simp+tauto`/`aesop`/`fin_cases` all timed out or failed
   on opaque-var literals → solved by unfolding `hfail` + `rcases rfl <;> simp`
   (no set equality needed at all).
2. `claim2_4`/`hI2` bound mismatch: `2 ≤ lam` → `1 ≤ lam` via `omega` bridge.
3. `prop4_1` signature (frozen) unchanged; call in `IntCase.lean` resolves.

Axioms (via Audit.lean on the umbrella): `[propext, Classical.choice, Quot.sound]`.
