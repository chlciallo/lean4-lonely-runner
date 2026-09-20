# lrc7-sec6-case66-top6 — finish `case66_top` in Case66.lean

Agent #6 on this task (5 predecessors died on connection interrupts / context
exhaustion — NOT design failures). Report is durable memory: appended every
~10 tool calls. WRITE TO DISK EARLY AND OFTEN.

## 2026-09-19 21:36 — Boot / state audit

- Working dir: `D:\creation\Research_Projects\07\Research07\LRC7`
- File: `Case66.lean`, **2565 lines**, reportedly **4 errors** remaining, all at
  ONE pattern (lines ~2501, ~2546): `have hll := lambda_low_top_resid hjm
  (show (1:ℕ) < 7 by norm_num)` — implicit `k` uninferable in a `have` without
  type annotation. FIX: annotate `hll` with full expected type, or restructure.
- Done & compiling (once the 4 errors fixed): `case66a_finish`,
  `case66b_finish`, `case66a_red` (2470), `case66b_red` (2519) — red theorems
  handle normalized pair `(e12 = 2*7^m, e34 = 7^m)` (case a) / `(=7^m, =2*7^m)`
  (case b) incl ε-corner via `case66a_eps`/`case66b_good`.
- Spec reports read: `_reports/lrc7-sec6-case66.md` (root) +
  `Research07/LRC7/_reports/lrc7-sec6-case66-top5.md` (nested, predecessor).

## Remaining work (from contract)

1. Fix the 4 `lambda_low_top_resid` errors in `case66a_red`/`case66b_red`.
2. `case66a`/`case66b` — scalar-normalizing wrappers (unit λ₀ via
   `exists_top_scalar_set`/`runit7` → normalize to red model → `case66*_red`).
3. `case66_top` — EXACT signature in contract; produces
   `∃ lam, ¬7∣lam ∧ good7 m lam {d1,…,d5}`.

## Hard rules

- NO sorry/admit/native_decide/unsafe. 0 errors required.
- Compile ONLY `lake env lean Research07/LRC7/Case66.lean` (from repo root
  `D:/creation/Research_Projects/07` — verify path).
- Insert before `end LRC7Case66`; do NOT touch `case66` (~1387) or §1-§3.
- Log failure+fix one-liners to `_dev/failures.md`.

## 2026-09-19 21:50 — STEP 1 DONE: file GREEN (0 errors, 2564 lines)

Fixed the 4 `lambda_low_top_resid` errors (2 sites) by replacing
`have hll := lambda_low_top_resid hjm (show (1:ℕ)<7 …); rwa [one_mul] at hll`
with `rw [eMod7_mul hlam'r, heXX, hlam', ← one_mul (7 ^ m)]` + `exact
lambda_low_top_resid hjm (show (1:ℕ) < 7 …)`. The `← one_mul` rewrites both
`7^m` occurrences (LHS factor + RHS) to `1 * 7^m`, matching the lemma's `t*7^m`
shape with `t := 1`, `k := k` inferred from the goal.
- Sites: `case66a_red` he34' (~2499), `case66b_red` he12' (~2544).
- `lake env lean` → exit 0, zero `error` lines. Logged to failures.md.

## Interfaces confirmed

- `case66a_red (hm) (hp*) (hu*) (hs0) (h1..h5 runit7) (he12 : e12 = 2*7^m)
  (he34 : e34 = 7^m) {k j} (hjm : j<m) (hnb : (etd7 m (lam'*d2) (lam'*d4),
  etd7 m (lam'*d2) (lam'*d5)) ∉ bad66a)` where `lam' = 1+k*7^(m-j)` — reduces
  a Λ_j-shifted not-bad config to `case66a_finish`.
- `case66b_red`: same but `(he12 = 7^m) (he34 = 2*7^m)` and
  `ha : etd7 m (lam'*d2) (lam'*d4) ∉ {2,4}`.
- `case66a_finish`: normalized `e12=2*7^m, e34=7^m`, `(x,y)∉bad66a` with
  `x = etd7 m d2 d4`, `y = etd7 m d2 d5`.
- `case66b_finish`: normalized `e12=7^m, e34=2*7^m`, `x∉{2,4}` with
  `x = etd7 m d2 d4`, `y = etd7 m d4 d5`.
- `exists_multLow_etd7_avoid'` (2411): twoX pair `runit7 d' = 2*runit7 d`,
  `e≠0`, `ν(e)<m` → `∃ k<7, etd7 m (Λ_ν d) (Λ_ν d') ∉ X` (apLen X ≤4).
- `exists_multLow_etd7_avoid` (1942): same + `0<ν(e)` explicit.
- dec-tables: `case66a_auto_dec` r∈{1,2,3}, `case66a_safeA_dec` r∈{4,5} y∉{2,4},
  `case66a_safeB_dec` r∈{0,6} y∉{4,6}, `case66a_notbad_x_dec` x∉{4,5,6};
  `case66b_auto_dec` r∈{0,1,6}, `case66b_sig1_dec` r∈{2,4} σ=1,
  `case66b_sig0_dec` r∈{3,5} σ=0; `case66b_eps_dec` ∀p ∃ε p−ε∉{2,4}.
- σ-linkage: `etd7_same_of_low`, `etd7_twoX_of_low`, `etd7_twoY_of_low`,
  `low_link_twoY`, `two_mul_low_div`, `multLow1_mod_low`, `multLow1_lo`,
  `multLow1_mid_eq`, `sigma_eps_magic`, `sigma_single`.
- `neg_mem124` (1885): r≠0 → r∈{1,2,4} ∨ −r∈{1,2,4}.
- `padic_lt_of_mod_ne` (2399): e≠0, e<7^{m+1}, e%7^m≠0 → ν(e)<m.

## TODO next

case66a/case66b wrappers (scalar-normalize via unit c to red model — actually
since case66a_red consumes Λ_j-shifts, the wrappers must run the full subcase
tree producing SOME lam; the scalar-normalization must be applied FIRST to get
e12'=2*7^m etc, then the subcase tree operates on scaled elements c*di).

Wait — re-check: does the subcase tree happen BEFORE or AFTER scaling? The
e24/e25 residues scale by c too (eMod7_smul: runit7 c ≠ 0 needed). etd7 values
transform... hmm need to check how etd7 transforms under scalar. Actually
simplest: apply scalar c first (new elements c*di), then the ν-tree on the
SCALED elements — the normalized model applies to them directly. ν(e(ci,cj))
= ν(e(di,dj)) since c unit; residues scale by c mod N. So the wrapper:
1. pick c with runit7 c = r34⁻¹ (case a) — need `∃ c, runit7 c = u` for unit u:
   exists via c = u.val? runit7 u.val = u for u∈{1..6}: check
   `runit7_of_padic_zero`/`runit7_eq_one_of_mod7`/`runit7_mul_of_mod7`.
   Simpler: c := t.val for t∈{1..6}, `runit7 t.val = t`? Need a lemma —
   `runit7` is `x % 7`-ish cast. Check Discrete.lean runit7 def.
2. prove scaled hyps: eMod7_smul gives e(c*d1,c*d2) = (c*e12)%N = c*r12*7^m%N
   = (c*r12)*7^m %N = 2*7^m when c*r12=2.
3. subcase tree on ν(e(c*d2,c*d4)) = ν(e(d2,d4))·(padicValNat_mul_seven needs
   c≡0 mod7? e(c*d2,c*d4) = (c*e24)%N — ν of that = ν(e24) when c unit:
   padicValNat_mul? c not div by 7 → ν(c*e)=ν(e). Check padicValNat.mul.
   Then e%7^m = 0 iff e24%7^m = 0 (c unit). Equivalent route: work with
   e24' = eMod7 m (c*d2) (c*d4) directly.
4. produce lam = (Λ-shift or Λ₁-corner or plain) ∘ c; good7 via good7_mul.

Actually case66a_red/b_red ALREADY produce `∃ lam, ¬7∣lam ∧ good7 ... {d1..d5}`
for the unscaled elements given the Λ_j-shifted hnb. So the WRAPPER for case a:
given e12 = r12*7^m, e34 = r34*7^m, r12=2*r34 — scale by c=r34⁻¹ → apply
subcase tree to scaled elements → case66a_red on scaled elements gives lam with
good7 on {c*d1,…} image = lam' where good7_mul pulls back: final lam_total =
lam*c... wait good7_mul: good7 m lam (A.image (c*·)) → good7 m (lam*c) A?
Check signature.

## 2026-09-19 22:00 — Design finalized for remaining theorems

Interfaces decided (all insert before `end LRC7Case66`):

1. dec-tables (all `by decide`): `zmod7_split_a` ∀r: r∈{1,2,3}∨r∈{0,4,5,6};
   `zmod7_split_b` ∀r: r∈{0,1,6}∨r∈{2,4}∨r∈{3,5};
   `zmod7_split_c` ∀r: r∈{0,4,5,6}→r∈{4,5}∨r∈{0,6};
   `zmod7_ratio124` ∀a b∈{1,2,4}: a=b∨a=2b∨b=2a.
2. `exists_multLow1_set_digit` (hm:1≤m)(hd:νd=0)(hd0:0<d)(hw:w<7):
   ∃k<7, ((d/7^{m-1})%7 + k*(d%7))%7 = w — nat-level W-setter via
   exists_multLow_one_set_seven' + qdig7_seven + multLow1_lo/mid_eq.
3. `sigma_multLow1` (hm:1≤m): 2*(Λ₁x%7^m)/7^m = (2*W+2*(x%7^{m-1})/7^{m-1})/7
   via multLow1_lo + two_mul_low_div.
4. `etd7_multLow_top_mem` (hrel:r y=2r x)(he:e%7^m=0)(hjm:j<m):
   etd7(Λ_jx,Λ_jy) ∈ {q(e)−1, q(e)} — via etd7_twoX_of_low+lambda_low_top_resid.
5. `case66_sigma_force` (case-b): ∃k<7, etd7(Λ₁d2,Λ₁d4) = q(e24)−ε
   (ε∈{0,1}, w=4ε via sigma_single).
6. `case66a_corner` (case-a joint ε-corner): given e24%7^m=e25%7^m=0, ε₁,ε₂
   ZMod with val<2 and (q24−ε₁,q25−ε₂)∉bad66a → ∃k<7 with shifted pair ∉
   bad66a. σ-chain: u5=d5%7^{m-1}, a5=d5/7^{m-1}%7, cm5=2u5/P, u2'=(2u5)%P,
   dig2=(2a5+cm5)%7 (via low_link_twoY), W5=w=4ε₂v+2ε₁v, W2=(2w+cm5)%7
   (ZMod-linear_combination congruence), sigma_eps_magic → σ24'=ε₁v,σ25'=ε₂v.
7. `case66a_go`/`case66b_go` — normalized dispatchers on he12=2*7^m,he34=7^m
   (a) / =7^m,=2*7^m (b); subcase tree per spec §6.6; j=0,k=0 for auto,
   j=ν(E25) for lemma7_i', j=1 for σ-force/corner.
8. `case66a`/`case66b` — scalar wrappers: exists_top_scalar_set t=1 on the
   *subordinate* residue (e34 for a, e12 for b) → c with runit7 c = r⁻¹ →
   scaled e's are (2,1)/(1,2)-normalized via residN_top; good7_mul unwraps.
9. `case66_swap_top` — swap facts (e(y,x)≠0, ν=m, r=−r).
10. `case66_top_core` — hr12,hr34 ∈{1,2,4} given → ratio split → eq: scalar
    t=6 + case66_finish (Finset-level A1={d1,d2} etc.); a→case66a; b→case66b.
11. `case66_top` — neg_mem124 on each residue → 4 orientation cases → core
    + Finset ext-tauto for swapped sets.

Key APIs verified: exists_top_scalar_set (CSmB:546), eMod7_smul (C66:94,
runit7 c≠0), eMod7_mul (CSmB:646, runit7=1), residN_top (CSmB:524),
mod_pow_succ_of_padic (C66:189), neg_resid (C66:307), eMod7_same_swap
(C66:372), low_link_twoY (C66:1824), two_mul_low_div (C66:1800),
multLow1_lo (C66:2307), multLow1_mid_eq (C66:2374), sigma_eps_magic
(C66:1871), sigma_single (C66:1879), case66a_eps (CSmB:1307),
exists_multLow_etd7_avoid' (C66:2411), eMod7_comm_of_two (C66:153),
etd7_twoY_eq (C66:2298), padic_lt_of_mod_ne (C66:2399),
qdig7_eq_runit7_of_ne (C66:183), qdig7_eq_cast_div (Disc:280),
qdig7_of_resid (C66:47), good7_mul (CSmB:137).
