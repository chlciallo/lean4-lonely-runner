# lrc7-finite.md — LRC7 Finite.lean (§7, m=1 enumeration) agent log

Task: `Research07/LRC7/Finite.lean` proving `lrc7_m1` (frozen statement, see
`_reports/lrc7-interfaces.md` U1). Two-stage Z_49/Z_98 enumeration, `decide`-based.

## 2026-09-18 — session start, context read

Read: `_reports/lrc7-interfaces.md` (frozen contract), `_reports/bs7-structure.md`
(§7 verified externally: 63 bad pair-sets = 3 orbits reps {1,3,4,5,18},
{1,4,6,10,11}, {1,4,6,10,22}; stage-2 λ may be non-unit e.g. λ=7).

Available infra (compiled green):
- `absModN x N = min (x%N) (N−x%N)`, `absModN_neg` (LRC5.Discrete)
- `absModN_top_ge7 : ν₇d=m → 0<d → ¬7∣λ → 7^m ≤ |λd|_{7^{m+1}}` (LRC7.Discrete)
- `padicValNat_mul_seven`, `qdig7`, `runit7`, `level7` (LRC7.*)

## Design (derived, to be implemented)

- `pairRep49 d = min (d%49) (49−d%49)` ∈ {1..24} for units; reps49 = Icc 1 24.
- `rep98 d = min (d%98) (98−d%98)` ∈ {a, 49−a} where a = pairRep49 d (sign-class
  rep of the mod-98 lift); for d6 (ν=1): rep98 d6 ∈ {7,14,21,28,35,42}.
- `badSets49 := (reps49.powersetCard 5).filter (fun P => !good49b P)` where
  `good49b P = units49.any (λ => P.all (a => 7 ≤ absModN (λ*a) 49))`.
  Stage-1 trichotomy is then definitional (good ∨ ¬good), NO decide needed.
- Stage 2 (the only heavy decide): ∀ Q ∈ badSets49, ∀ T ⊆ lifts(Q) with |T|≤5,
  ∀ r ∈ {7,…,42}: ∃ λ ∈ Icc 1 49 (∀a∈T: 14≤|λa|_98) ∧ 14≤|λr|_98.
  λ∈{1..49} suffices since |λx|_98 = |(98−λ)x|_98 for all x simultaneously.
- Bridge lemmas: |λd|_49 = |λ·pairRep49 d|_49; |λd|_98 = |λ·rep98 d|_98;
  rep98 d ∈ {pairRep49 d, 49−pairRep49 d} (holds for ALL d).
- Assembly: P0 = A.image pairRep49 ⊆ reps49, |P0|≤5; extend to Q 5-set
  (Finset.exists_smaller_set on reps49\P0). Good → M=49 (+ absModN_top_ge7 for
  d6); bad → stage2 → M=98.

## Open: decide feasibility for the filter over C(24,5)=42504 pair-sets × ≤42λ
## (kernel eval ~10^7-10^8 steps). Fallbacks: Bool checker + chunked lemmas.

## 2026-09-18 — CRITICAL FINDING: gcd(D)=1 restriction

Python sanity check of my encoding (`reps49={1..24}`, `units49={1..48}\7Z`,
`badSets49` = filter not-good over powersetCard 5):
- bad count = **63** ✓ (matches paper: {1,3,4,5,18},{1,4,6,10,11},{1,4,6,10,22} orbits)
- BUT naive stage-2 (all T ⊆ lifts(Q), |T|≤5, r∈{7..42}, ∃λ∈{1..49}):
  **189 FAILURES**, all with T all-even + r∈{14,28,42} (even).
  Example: A'={4,18,44,46,48} (classes {1,3,4,5,18}), d6-rep=14 → best |λ·|_98=12.
- Paper text (`_external/bs7-ejc.txt` line ~804): "every set D ... **verifying
  gcd(D)=1** admits a multiplier in Z98". The enumeration EXCLUDES gcd>1 configs.
- Since 98 is even, `rep98 d` odd ↔ `d` odd; all-even residues ⟺ all actual
  elements even ⟺ gcd≥2. Verified: restricting to configs with some odd element
  → **235,116 configs, 0 fails**; 6,048 all-even configs skipped.
- Consequence for `lrc7_m1` (no gcd hypothesis): handle all-even inputs by
  dividing out `2^v` (v = min ν₂ over A∪{d6}); the halved config keeps
  card/units/ν(d6)=1, gains an odd element (the minimizer); lift λ,M to λ,2^v·M
  via `absModN_mul_scale : |c·x|_{cM} = c|x|_M` and `(2^v M)/7 = 2^v(M/7)` (7|M).
- Uniform assembly (no case split): always halve by 2^v, then stage-1 trichotomy
  on halved pair-set; stage-2 odd-witness always exists (minimizer quotient odd).

## Lemma names confirmed in mathlib v4.34.0
- `Finset.exists_subsuperset_card_eq (s⊆t) (#s≤n) (n≤#t) : ∃u, s⊆u∧u⊆t∧#u=n`
- `Finset.exists_min_image` (to_dual of exists_max_image), `card_image_of_injOn`
- `ZMod.natCast_eq_natCast_iff' : (↑a:ZMod c)=↑b ↔ a%c=b%c`; `ZMod.natCast_self`,
  `ZMod.natCast_mod`, `ZMod.natCast_eq_zero_iff`
- `Nat.pow_dvd_iff_le_padicValNat (hp:p≠1)(hn:n≠0)`, `padicValNat.prime_pow`,
  `Nat.Prime.dvd_of_dvd_pow`, `Nat.odd_iff : Odd n ↔ n%2=1`, `Nat.even_iff`
- `Finset.decidableDforallFinset`/`decidableDexistsFinset` (bounded ∀∃ decidable)

## Plan (v2)
- `units21 := (Icc 1 24).filter (·%7≠0)` — 21 λ's suffice mod sign for stage-1
  filter (halves kernel work); `badSets49` uses it (same 63 sets).
- `stage2`: ∀Q∈badSets49, ∀T⊆lifts(Q) |T|≤5, ∀r∈{7..42},
  (∃x∈insert r T, x%2=1) → ∃λ∈Icc 1 49: (14≤|λt|_98 ∀t) ∧ 14≤|λr|_98. `decide`.
- `badSets49_card : badSets49.card = 63 := by decide` (audit).
- `lrc7_m1`: halving + dichotomy + `absModN_mul_scale` lift.
