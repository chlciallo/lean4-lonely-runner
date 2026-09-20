/-
Copyright (c) 2026 Research07 contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Research07 contributors
-/
import Research07.LRC7.Case4
import Research07.LRC7.NormU
import Research07.LRC7.Compress
-- import Research07.LRC7.Carry  -- pending repair (qdig7_add_mem)

/-!
# §5 integer assembly — `lrc7_case4`

Barajas–Serra §5: `D` has exactly `4` level-`0` units `A = {d1,d2,d3,d4}`,
at most one element `d5` at an intermediate level `i₀ ∈ (0, m]` (the count
`4+2+1` or `4+1+1+1` exceeds `|D| ≤ 6`), and top-level elements at level `m`
(auto-good by `absModN_top_ge7`).

Multiplier families (paper):

* `λ'_j = j·u'·(1 + 7^{m−i₀})`, `1 ≤ j ≤ 5`, with `u·u' ≡ 1 (mod 7^{m+1−i₀})`
  — eq. (8): `|λ'_j·d5|_N ≥ 7^m` (`eq8_absModN`);
* `λ_k = 1 + k·7^m ∈ Λ₀` — preserves `d5`'s residue (`residN_multLow7`) and
  shifts `qdig` by `k·runit7` (`qdig7_multLow`, eq. (10)).

The digit dynamics is eq. (9): `q(λ'_{j+1}·d) ∈ q(λ'_j·d) + q(λ'_1·d) + {0,1}`
(`qdig7_add_mem` applied to `λ'_{j+1} = λ'_j + λ'_1`).

Units are sign-normalized by `normU7` so `runit7 ∈ {1,2,4}` (certificates
transfer via `normU7_absModN`).  The three sub-cases `|A_s| = 4,3,2` dispatch
to the `ZMod 7` lemmas of `Case4.lean` via the translation-shifted wrappers
`prop4x`/`prop3ax`/`prop3bx`/`prop2ix`/`prop2iix` below (the paper's "WLOG"
normalizations are just cyclic translations).
-/

private instance : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩

/-! ## The `Λ'` family and eq. (8) -/

/-- The `Λ'` multiplier `λ'_j = j·u'·(1 + 7^{m−i₀})`. -/
def lamP (m i₀ j u' : ℕ) : ℕ := j * u' * (1 + 7 ^ (m - i₀))

/-- `λ'_j` is a unit modulo `7` whenever `j ∈ {1,…,5}`, `7 ∤ u'` and `i₀ ≤ m`
(the factor `1 + 7^{m−i₀}` is `1` or `2` mod `7`). -/
theorem lamP_not_dvd {m i₀ j u' : ℕ} (him : i₀ ≤ m) (hj : 1 ≤ j ∧ j ≤ 5)
    (hu' : ¬ 7 ∣ u') : ¬ 7 ∣ lamP m i₀ j u' := by
  intro h
  rcases hj with ⟨hj1, hj5⟩
  have hf : ¬ 7 ∣ (1 + 7 ^ (m - i₀)) := by
    rcases Nat.lt_or_eq_of_le him with h | h
    · have h7 : 7 ∣ 7 ^ (m - i₀) := dvd_pow_self 7 (by omega)
      omega
    · rw [h, Nat.sub_self, pow_zero]
      omega
  have hj' : ¬ 7 ∣ j := fun h => by interval_cases j <;> omega
  rcases (Nat.Prime.dvd_mul Nat.prime_seven).mp h with h | h
  · rcases (Nat.Prime.dvd_mul Nat.prime_seven).mp h with h | h
    · exact hj' h
    · exact hu' h
  · exact hf h

/-- eq. (8): `λ'_j·d5 ≡ j·(7^{i₀} + 7^m) (mod 7^{m+1})`, and that residue has
`absModN ≥ 7^m`.  `d5 = u·7^{i₀}` with `u·u' ≡ 1 (mod 7^{m+1−i₀})`. -/
theorem eq8_absModN {m i₀ j u u' : ℕ} (hi0 : 0 < i₀) (him : i₀ ≤ m)
    (hj : 1 ≤ j ∧ j ≤ 5) (huu' : u * u' ≡ 1 [MOD 7 ^ (m + 1 - i₀)]) :
    7 ^ m ≤ absModN (lamP m i₀ j u' * (u * 7 ^ i₀)) (7 ^ (m + 1)) := by
  rcases hj with ⟨hj1, hj5⟩
  have hm : 0 < m := by omega
  have hN : 7 ^ (m + 1) = 49 * 7 ^ (m - 1) := by
    rw [show m + 1 = m - 1 + 2 by omega, pow_add]; ring
  have h7m : 7 ^ m = 7 * 7 ^ (m - 1) := by
    conv_lhs => rw [show m = m - 1 + 1 by omega]
    exact pow_succ' 7 (m - 1)
  -- The congruence `λ'_j·d5 ≡ j·(7^{i₀} + 7^m) (mod N)`.
  have hcong : lamP m i₀ j u' * (u * 7 ^ i₀) ≡ j * (7 ^ i₀ + 7 ^ m)
      [MOD 7 ^ (m + 1)] := by
    have hA : u * u' * 7 ^ i₀ ≡ 1 * 7 ^ i₀ [MOD 7 ^ (m + 1)] := by
      have h2 := Nat.ModEq.mul_right' (7 ^ i₀) huu'
      rwa [show 7 ^ (m + 1 - i₀) * 7 ^ i₀ = 7 ^ (m + 1) from by
        rw [← pow_add]; congr 1; omega] at h2
    have hB : u * u' * 7 ^ m ≡ 1 * 7 ^ m [MOD 7 ^ (m + 1)] := by
      have hd7 : 7 ∣ 7 ^ (m + 1 - i₀) := dvd_pow_self 7 (by omega)
      have h7 : u * u' ≡ 1 [MOD 7] := by
        rw [Nat.ModEq] at huu' ⊢
        rw [← Nat.mod_mod_of_dvd (u * u') hd7, huu',
          Nat.mod_mod_of_dvd _ hd7]
      have h2 := Nat.ModEq.mul_right' (7 ^ m) h7
      rwa [show 7 * 7 ^ m = 7 ^ (m + 1) from (pow_succ' 7 m).symm] at h2
    have hC : u * u' * (7 ^ i₀ + 7 ^ m) ≡ 7 ^ i₀ + 7 ^ m
        [MOD 7 ^ (m + 1)] := by
      have h := Nat.ModEq.add hA hB
      rw [mul_add]
      simpa using h
    have hD : lamP m i₀ j u' * (u * 7 ^ i₀) =
        j * (u * u' * (7 ^ i₀ + 7 ^ m)) := by
      unfold lamP
      have h7m' : 7 ^ i₀ * 7 ^ (m - i₀) = 7 ^ m := by
        rw [← pow_add]; congr 1; omega
      calc j * u' * (1 + 7 ^ (m - i₀)) * (u * 7 ^ i₀)
          = j * (u * u') * (7 ^ i₀ + 7 ^ i₀ * 7 ^ (m - i₀)) := by ring
        _ = j * (u * u' * (7 ^ i₀ + 7 ^ m)) := by rw [h7m']; ring
    rw [hD]
    exact Nat.ModEq.mul (Nat.ModEq.refl j) hC
  -- `absModN` only sees the residue, so replace by `j·(7^{i₀}+7^m)`.
  have hres : absModN (lamP m i₀ j u' * (u * 7 ^ i₀)) (7 ^ (m + 1)) =
      absModN (j * (7 ^ i₀ + 7 ^ m)) (7 ^ (m + 1)) := by
    unfold absModN
    rw [show (lamP m i₀ j u' * (u * 7 ^ i₀)) % 7 ^ (m + 1) =
        (j * (7 ^ i₀ + 7 ^ m)) % 7 ^ (m + 1) from hcong]
  rw [hres]
  rcases Nat.lt_or_eq_of_le him with hlt | heq
  · -- `i₀ < m`: the residue is verbatim `j·7^{i₀} + j·7^m`.
    have hle1 : 7 ^ i₀ ≤ 7 ^ (m - 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpos : 0 < 7 ^ (m - 1) := Nat.pow_pos (by norm_num)
    have hjle1 : j * 7 ^ i₀ ≤ 5 * 7 ^ (m - 1) :=
      Nat.mul_le_mul hj5 hle1
    have hjle2 : j * 7 ^ m ≤ 35 * 7 ^ (m - 1) := by
      have h := Nat.mul_le_mul hj5 (le_refl (7 ^ m))
      rw [h7m] at h ⊢
      calc j * (7 * 7 ^ (m - 1)) = 7 * (j * 7 ^ (m - 1)) := by ring
        _ ≤ 7 * (5 * 7 ^ (m - 1)) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul hj5 (le_refl _))
        _ = 35 * 7 ^ (m - 1) := by ring
    have hval : j * (7 ^ i₀ + 7 ^ m) < 7 ^ (m + 1) := by
      have hE : j * (7 ^ i₀ + 7 ^ m) = j * 7 ^ i₀ + j * 7 ^ m := by ring
      omega
    rw [show absModN (j * (7 ^ i₀ + 7 ^ m)) (7 ^ (m + 1)) =
        min (j * (7 ^ i₀ + 7 ^ m)) (7 ^ (m + 1) - j * (7 ^ i₀ + 7 ^ m)) from by
        unfold absModN
        rw [Nat.mod_eq_of_lt hval]]
    apply le_min
    · have hE : j * (7 ^ i₀ + 7 ^ m) = j * 7 ^ i₀ + j * 7 ^ m := by ring
      have h1 : 7 ^ m ≤ j * 7 ^ m :=
        Nat.le_mul_of_pos_left _ (by omega)
      omega
    · have hE : j * (7 ^ i₀ + 7 ^ m) = j * 7 ^ i₀ + j * 7 ^ m := by ring
      omega
  · -- `i₀ = m`: residue `(2j % 7)·7^m`.
    rw [heq]
    have hval : j * (7 ^ m + 7 ^ m) = (2 * j) * 7 ^ m := by ring
    rw [hval, show absModN ((2 * j) * 7 ^ m) (7 ^ (m + 1)) =
        min ((2 * j % 7) * 7 ^ m) ((7 - 2 * j % 7) * 7 ^ m) from by
        unfold absModN
        rw [pow_succ', Nat.mul_mod_mul_right]
        congr 2
        rw [Nat.sub_mul]]
    apply le_min
    · have h1 : 1 ≤ 2 * j % 7 := by
        have h2 : 2 * j % 7 ≠ 0 := by
          intro h0
          have hd : 7 ∣ 2 * j := Nat.dvd_iff_mod_eq_zero.mpr h0
          rcases (Nat.Prime.dvd_mul Nat.prime_seven).mp hd with h | h
          · omega
          · interval_cases j <;> omega
        omega
      calc 7 ^ m = 1 * 7 ^ m := (one_mul _).symm
        _ ≤ (2 * j % 7) * 7 ^ m :=
          Nat.mul_le_mul_right _ (by omega)
    · have h1 : 1 ≤ 7 - 2 * j % 7 := by
        have h2 : 2 * j % 7 < 7 := Nat.mod_lt _ (by norm_num)
        omega
      calc 7 ^ m = 1 * 7 ^ m := (one_mul _).symm
        _ ≤ (7 - 2 * j % 7) * 7 ^ m :=
          Nat.mul_le_mul_right _ (by omega)

/-! ## Complement and translation helpers -/

/-- Complement of a 5-interval is a 2-interval. -/
theorem mem_of_not_mem_cycIv5 {x i : ZMod 7} (h : x ∉ cycIv i 5) :
    x ∈ cycIv (i + 5) 2 := by
  revert x i h; decide

/-- Complement of a 4-interval is a 3-interval. -/
theorem mem_of_not_mem_cycIv4 {x i : ZMod 7} (h : x ∉ cycIv i 4) :
    x ∈ cycIv (i + 4) 3 := by
  revert x i h; decide

/-- Complement of a 2-interval is a 5-interval. -/
theorem mem_of_not_mem_cycIv2 {x i : ZMod 7} (h : x ∉ cycIv i 2) :
    x ∈ cycIv (i + 2) 5 := by
  revert x i h; decide

/-! ## Translation-shifted propagation lemmas

The `ZMod 7` lemmas of `Case4.lean` are stated in the normalized frame (the
`j = 1` digits start at `0`).  The actual digit sets are cyclic translates
`{x, x+2, x+4, x+6}` etc.; since translation `z ↦ z − t` is a `ZMod 7`
automorphism preserving the window structure, each shifted statement is
still a finite check — here with `∀ x` folded into the `decide`. -/

/-- Shifted `prop4` (`|Aₛ| = 4`): `j = 1` digits `{x, x+2, x+4, x+6}`. -/
theorem prop4x {x : ZMod 7} (b0 b1 b2 b3 : ZMod 7)
    (hb0 : b0 - 3 * x ∈ ({0, 1, 2} : Finset (ZMod 7)))
    (hb1 : b1 - 3 * (x + 2) ∈ ({0, 1, 2} : Finset (ZMod 7)))
    (hb2 : b2 - 3 * (x + 4) ∈ ({0, 1, 2} : Finset (ZMod 7)))
    (hb3 : b3 - 3 * (x + 6) ∈ ({0, 1, 2} : Finset (ZMod 7)))
    (hhit : ∀ i : ZMod 7, (({b0, b1, b2, b3} : Finset (ZMod 7)) ∩
      cycIv i 2).Nonempty)
    (c0 c1 c2 c3 : ZMod 7)
    (hc0 : c0 - b0 - x ∈ ({0, 1} : Finset (ZMod 7)))
    (hc1 : c1 - b1 - (x + 2) ∈ ({0, 1} : Finset (ZMod 7)))
    (hc2 : c2 - b2 - (x + 4) ∈ ({0, 1} : Finset (ZMod 7)))
    (hc3 : c3 - b3 - (x + 6) ∈ ({0, 1} : Finset (ZMod 7))) :
    ∃ i : ZMod 7, ({c0, c1, c2, c3} : Finset (ZMod 7)) ⊆ cycIv i 5 := by
  suffices H : ∀ x : ZMod 7, ∀ b0 : ZMod 7,
      b0 - 3 * x ∈ ({0, 1, 2} : Finset (ZMod 7)) →
      ∀ b1 : ZMod 7, b1 - 3 * (x + 2) ∈ ({0, 1, 2} : Finset (ZMod 7)) →
      ∀ b2 : ZMod 7, b2 - 3 * (x + 4) ∈ ({0, 1, 2} : Finset (ZMod 7)) →
      ∀ b3 : ZMod 7, b3 - 3 * (x + 6) ∈ ({0, 1, 2} : Finset (ZMod 7)) →
      (∀ i : ZMod 7, (({b0, b1, b2, b3} : Finset (ZMod 7)) ∩
        cycIv i 2).Nonempty) →
      ∀ c0 : ZMod 7, c0 - b0 - x ∈ ({0, 1} : Finset (ZMod 7)) →
      ∀ c1 : ZMod 7, c1 - b1 - (x + 2) ∈ ({0, 1} : Finset (ZMod 7)) →
      ∀ c2 : ZMod 7, c2 - b2 - (x + 4) ∈ ({0, 1} : Finset (ZMod 7)) →
      ∀ c3 : ZMod 7, c3 - b3 - (x + 6) ∈ ({0, 1} : Finset (ZMod 7)) →
      ∃ i : ZMod 7, ({c0, c1, c2, c3} : Finset (ZMod 7)) ⊆ cycIv i 5 by
    exact H x b0 hb0 b1 hb1 b2 hb2 b3 hb3 hhit c0 hc0 c1 hc1 c2 hc2 c3 hc3
  set_option synthInstance.maxSize 16384 in
  set_option maxRecDepth 524288 in
  decide

/-- Shifted `prop3a` (`|Aₛ| = 3`, pattern `{x, x+1, x+4}`): the `j = 2`
digits already sit in a 4-interval. -/
theorem prop3ax {x : ZMod 7} (b0 b1 b2 : ZMod 7)
    (hb0 : b0 - 2 * x ∈ ({0, 1} : Finset (ZMod 7)))
    (hb1 : b1 - 2 * (x + 1) ∈ ({0, 1} : Finset (ZMod 7)))
    (hb2 : b2 - 2 * (x + 4) ∈ ({0, 1} : Finset (ZMod 7))) :
    ∃ i : ZMod 7, ({b0, b1, b2} : Finset (ZMod 7)) ⊆ cycIv i 4 := by
  suffices H : ∀ x : ZMod 7, ∀ b0 : ZMod 7,
      b0 - 2 * x ∈ ({0, 1} : Finset (ZMod 7)) →
      ∀ b1 : ZMod 7, b1 - 2 * (x + 1) ∈ ({0, 1} : Finset (ZMod 7)) →
      ∀ b2 : ZMod 7, b2 - 2 * (x + 4) ∈ ({0, 1} : Finset (ZMod 7)) →
      ∃ i : ZMod 7, ({b0, b1, b2} : Finset (ZMod 7)) ⊆ cycIv i 4 by
    exact H x b0 hb0 b1 hb1 b2 hb2
  set_option synthInstance.maxSize 16384 in
  set_option maxRecDepth 524288 in
  decide

/-- Shifted `prop3b` (`|Aₛ| = 3`, pattern `{x, x+2, x+4}`): if the `j = 3`
digits hit `{2,3,4}` and `{3,4,5}` (translated), the `j = 4` digits sit in a
4-interval. -/
theorem prop3bx {x : ZMod 7} (b0 b1 b2 : ZMod 7)
    (hb0 : b0 - 3 * x ∈ ({0, 1, 2} : Finset (ZMod 7)))
    (hb1 : b1 - 3 * (x + 2) ∈ ({0, 1, 2} : Finset (ZMod 7)))
    (hb2 : b2 - 3 * (x + 4) ∈ ({0, 1, 2} : Finset (ZMod 7)))
    (hh1 : ∃ b ∈ ({b0, b1, b2} : Finset (ZMod 7)),
      b - 3 * x ∈ ({2, 3, 4} : Finset (ZMod 7)))
    (hh2 : ∃ b ∈ ({b0, b1, b2} : Finset (ZMod 7)),
      b - 3 * x ∈ ({3, 4, 5} : Finset (ZMod 7)))
    (c0 c1 c2 : ZMod 7)
    (hc0 : c0 - b0 - x ∈ ({0, 1} : Finset (ZMod 7)))
    (hc1 : c1 - b1 - (x + 2) ∈ ({0, 1} : Finset (ZMod 7)))
    (hc2 : c2 - b2 - (x + 4) ∈ ({0, 1} : Finset (ZMod 7))) :
    ∃ i : ZMod 7, ({c0, c1, c2} : Finset (ZMod 7)) ⊆ cycIv i 4 := by
  suffices H : ∀ x : ZMod 7, ∀ b0 : ZMod 7,
      b0 - 3 * x ∈ ({0, 1, 2} : Finset (ZMod 7)) →
      ∀ b1 : ZMod 7, b1 - 3 * (x + 2) ∈ ({0, 1, 2} : Finset (ZMod 7)) →
      ∀ b2 : ZMod 7, b2 - 3 * (x + 4) ∈ ({0, 1, 2} : Finset (ZMod 7)) →
      (∃ b ∈ ({b0, b1, b2} : Finset (ZMod 7)),
        b - 3 * x ∈ ({2, 3, 4} : Finset (ZMod 7))) →
      (∃ b ∈ ({b0, b1, b2} : Finset (ZMod 7)),
        b - 3 * x ∈ ({3, 4, 5} : Finset (ZMod 7))) →
      ∀ c0 : ZMod 7, c0 - b0 - x ∈ ({0, 1} : Finset (ZMod 7)) →
      ∀ c1 : ZMod 7, c1 - b1 - (x + 2) ∈ ({0, 1} : Finset (ZMod 7)) →
      ∀ c2 : ZMod 7, c2 - b2 - (x + 4) ∈ ({0, 1} : Finset (ZMod 7)) →
      ∃ i : ZMod 7, ({c0, c1, c2} : Finset (ZMod 7)) ⊆ cycIv i 4 by
    exact H x b0 hb0 b1 hb1 b2 hb2 hh1 hh2 c0 hc0 c1 hc1 c2 hc2
  set_option synthInstance.maxSize 16384 in
  set_option maxRecDepth 524288 in
  decide

/-- Shifted `prop2i` (`|Aₛ| = 2`, pattern `{x, x+2}`): the `j = 3, 4, 5`
chain forces the pair distance into `{0,1,6}`. -/
theorem prop2ix {x : ZMod 7} (b0 b1 : ZMod 7)
    (hb0 : b0 - 3 * x ∈ ({0, 1, 2} : Finset (ZMod 7)))
    (hb1 : b1 - 3 * (x + 2) ∈ ({0, 1, 2} : Finset (ZMod 7)))
    (hd : b1 - b0 ∉ ({0, 1, 6} : Finset (ZMod 7)))
    (c0 c1 : ZMod 7)
    (hc0 : c0 - b0 - x ∈ ({0, 1} : Finset (ZMod 7)))
    (hc1 : c1 - b1 - (x + 2) ∈ ({0, 1} : Finset (ZMod 7)))
    (hdc : c1 - c0 ∉ ({0, 1, 6} : Finset (ZMod 7)))
    (e0 e1 : ZMod 7)
    (he0 : e0 - c0 - x ∈ ({0, 1} : Finset (ZMod 7)))
    (he1 : e1 - c1 - (x + 2) ∈ ({0, 1} : Finset (ZMod 7))) :
    e1 - e0 ∈ ({0, 1, 6} : Finset (ZMod 7)) := by
  suffices H : ∀ x : ZMod 7, ∀ b0 : ZMod 7,
      b0 - 3 * x ∈ ({0, 1, 2} : Finset (ZMod 7)) →
      ∀ b1 : ZMod 7, b1 - 3 * (x + 2) ∈ ({0, 1, 2} : Finset (ZMod 7)) →
      b1 - b0 ∉ ({0, 1, 6} : Finset (ZMod 7)) →
      ∀ c0 : ZMod 7, c0 - b0 - x ∈ ({0, 1} : Finset (ZMod 7)) →
      ∀ c1 : ZMod 7, c1 - b1 - (x + 2) ∈ ({0, 1} : Finset (ZMod 7)) →
      c1 - c0 ∉ ({0, 1, 6} : Finset (ZMod 7)) →
      ∀ e0 : ZMod 7, e0 - c0 - x ∈ ({0, 1} : Finset (ZMod 7)) →
      ∀ e1 : ZMod 7, e1 - c1 - (x + 2) ∈ ({0, 1} : Finset (ZMod 7)) →
      e1 - e0 ∈ ({0, 1, 6} : Finset (ZMod 7)) by
    exact H x b0 hb0 b1 hb1 hd c0 hc0 c1 hc1 hdc e0 he0 e1 he1
  set_option synthInstance.maxSize 16384 in
  set_option maxRecDepth 524288 in
  decide

/-- Shifted `prop2ii` (`|Aₛ| = 2`, pattern `{x, x+3}`): the `j = 2, 3` chain
and the `j = 5 = 2 + 3` decomposition force the distance into `{0,1,6}`. -/
theorem prop2iix {x : ZMod 7} (b0 b1 : ZMod 7)
    (hb0 : b0 - 2 * x ∈ ({0, 1} : Finset (ZMod 7)))
    (hb1 : b1 - 2 * (x + 3) ∈ ({0, 1} : Finset (ZMod 7)))
    (hd : b1 - b0 ∉ ({0, 1, 6} : Finset (ZMod 7)))
    (c0 c1 : ZMod 7)
    (hc0 : c0 - b0 - x ∈ ({0, 1} : Finset (ZMod 7)))
    (hc1 : c1 - b1 - (x + 3) ∈ ({0, 1} : Finset (ZMod 7)))
    (hdc : c1 - c0 ∉ ({0, 1, 6} : Finset (ZMod 7)))
    (e0 e1 : ZMod 7)
    (he0 : e0 - b0 - c0 ∈ ({0, 1} : Finset (ZMod 7)))
    (he1 : e1 - b1 - c1 ∈ ({0, 1} : Finset (ZMod 7))) :
    e1 - e0 ∈ ({0, 1, 6} : Finset (ZMod 7)) := by
  suffices H : ∀ x : ZMod 7, ∀ b0 : ZMod 7,
      b0 - 2 * x ∈ ({0, 1} : Finset (ZMod 7)) →
      ∀ b1 : ZMod 7, b1 - 2 * (x + 3) ∈ ({0, 1} : Finset (ZMod 7)) →
      b1 - b0 ∉ ({0, 1, 6} : Finset (ZMod 7)) →
      ∀ c0 : ZMod 7, c0 - b0 - x ∈ ({0, 1} : Finset (ZMod 7)) →
      ∀ c1 : ZMod 7, c1 - b1 - (x + 3) ∈ ({0, 1} : Finset (ZMod 7)) →
      c1 - c0 ∉ ({0, 1, 6} : Finset (ZMod 7)) →
      ∀ e0 : ZMod 7, e0 - b0 - c0 ∈ ({0, 1} : Finset (ZMod 7)) →
      ∀ e1 : ZMod 7, e1 - b1 - c1 ∈ ({0, 1} : Finset (ZMod 7)) →
      e1 - e0 ∈ ({0, 1, 6} : Finset (ZMod 7)) by
    exact H x b0 hb0 b1 hb1 hd c0 hc0 c1 hc1 hdc e0 he0 e1 he1
  set_option synthInstance.maxSize 16384 in
  set_option maxRecDepth 524288 in
  decide

/-- `qdig7 m x` is the `m`-th base-7 digit of `x` (local copy). -/
private theorem qdig7_eq_digit7' (m x : ℕ) : qdig7 m x = digit7 m x := by
  unfold qdig7 digit7
  rw [pow_succ, Nat.mod_mul_right_div_self]

/-- The `m`-th digit of a sum: digits add, with a carry
`c = (a % 7^m + b % 7^m) / 7^m ∈ {0,1}` (local copy). -/
private theorem digit7_add' (m a b : ℕ) :
    digit7 m (a + b) = digit7 m a + digit7 m b +
      (((a % 7 ^ m + b % 7 ^ m) / 7 ^ m : ℕ) : ZMod 7) := by
  unfold digit7
  have hpos : (0:ℕ) < 7 ^ m := Nat.pow_pos (by norm_num)
  have hdiv : (a + b) / 7 ^ m =
      a / 7 ^ m + b / 7 ^ m + (a % 7 ^ m + b % 7 ^ m) / 7 ^ m := by
    conv_lhs => rw [← Nat.div_add_mod a (7 ^ m), ← Nat.div_add_mod b (7 ^ m)]
    rw [show 7 ^ m * (a / 7 ^ m) + a % 7 ^ m + (7 ^ m * (b / 7 ^ m) + b % 7 ^ m)
        = (a % 7 ^ m + b % 7 ^ m) + 7 ^ m * (a / 7 ^ m + b / 7 ^ m) from by ring]
    rw [Nat.add_mul_div_left _ _ hpos]
    ring
  rw [hdiv]
  simp only [ZMod.natCast_mod, Nat.cast_add]

/-- The `m`-th digit of a sum lies in `digit + digit + {0,1}` (local copy). -/
private theorem digit7_add_mem' (m a b : ℕ) :
    digit7 m (a + b) ∈
      ({digit7 m a + digit7 m b, digit7 m a + digit7 m b + 1} :
        Finset (ZMod 7)) := by
  rw [digit7_add']
  have hc : (a % 7 ^ m + b % 7 ^ m) / 7 ^ m = 0 ∨
      (a % 7 ^ m + b % 7 ^ m) / 7 ^ m = 1 := by
    have hlt : (a % 7 ^ m + b % 7 ^ m) / 7 ^ m < 2 := by
      rw [Nat.div_lt_iff_lt_mul (Nat.pow_pos (by norm_num))]
      have h1 : a % 7 ^ m < 7 ^ m := Nat.mod_lt _ (Nat.pow_pos (by norm_num))
      have h2 : b % 7 ^ m < 7 ^ m := Nat.mod_lt _ (Nat.pow_pos (by norm_num))
      omega
    interval_cases ((a % 7 ^ m + b % 7 ^ m) / 7 ^ m) <;> simp
  rcases hc with h0 | h1
  · rw [h0, Nat.cast_zero, add_zero]; exact Finset.mem_insert_self _ _
  · rw [h1, Nat.cast_one]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)

/-- `qdig7` form of `digit7_add_mem` (local copy). -/
private theorem qdig7_add_mem' (m a b : ℕ) :
    qdig7 m (a + b) ∈
      ({qdig7 m a + qdig7 m b, qdig7 m a + qdig7 m b + 1} :
        Finset (ZMod 7)) := by
  rw [qdig7_eq_digit7', qdig7_eq_digit7', qdig7_eq_digit7']
  exact digit7_add_mem' m a b

/-! ## The `eq. (9)` carry chain on `λ'_j` -/

/-- `λ'_{a+b} = λ'_a + λ'_b` as naturals. -/
theorem lamP_add (m i₀ a b u' : ℕ) :
    lamP m i₀ (a + b) u' = lamP m i₀ a u' + lamP m i₀ b u' := by
  unfold lamP; ring

/-- eq. (9): `q(λ'_{a+b}·x) ∈ q(λ'_a·x) + q(λ'_b·x) + {0,1}`. -/
theorem qdig7_lamP_add (m i₀ a b u' x : ℕ) :
    qdig7 m (lamP m i₀ (a + b) u' * x) ∈
      ({qdig7 m (lamP m i₀ a u' * x) + qdig7 m (lamP m i₀ b u' * x),
        qdig7 m (lamP m i₀ a u' * x) + qdig7 m (lamP m i₀ b u' * x) + 1} :
        Finset (ZMod 7)) := by
  rw [lamP_add, add_mul]
  exact qdig7_add_mem' m _ _

/-- `{0,1} + {0,1} ⊆ {0,1,2}` in `ZMod 7`. -/
theorem add_mem_01_012 {a b : ZMod 7} (ha : a ∈ ({0, 1} : Finset (ZMod 7)))
    (hb : b ∈ ({0, 1} : Finset (ZMod 7))) :
    a + b ∈ ({0, 1, 2} : Finset (ZMod 7)) := by
  revert a b ha hb; decide

/-- `q(λ'_₂·x) − 2·q(λ'_₁·x) ∈ {0,1}`. -/
theorem qdig7_two_sub {m i₀ u' x : ℕ} :
    qdig7 m (lamP m i₀ 2 u' * x) - 2 * qdig7 m (lamP m i₀ 1 u' * x) ∈
      ({0, 1} : Finset (ZMod 7)) := by
  have h := qdig7_lamP_add m i₀ 1 1 u' x
  rw [show (1 : ℕ) + 1 = 2 from rfl] at h
  rcases Finset.mem_insert.mp h with h | h
  · rw [h]; ring_nf; simp
  · rw [Finset.mem_singleton] at h
    rw [h]; ring_nf; simp

/-- `q(λ'_₃·x) − 3·q(λ'_₁·x) ∈ {0,1,2}` (two carry steps). -/
theorem qdig7_three_sub {m i₀ u' x : ℕ} :
    qdig7 m (lamP m i₀ 3 u' * x) - 3 * qdig7 m (lamP m i₀ 1 u' * x) ∈
      ({0, 1, 2} : Finset (ZMod 7)) := by
  have h32 : qdig7 m (lamP m i₀ 3 u' * x) -
      qdig7 m (lamP m i₀ 2 u' * x) - qdig7 m (lamP m i₀ 1 u' * x) ∈
      ({0, 1} : Finset (ZMod 7)) := by
    have h := qdig7_lamP_add m i₀ 2 1 u' x
    rw [show (2 : ℕ) + 1 = 3 from rfl] at h
    rcases Finset.mem_insert.mp h with h | h
    · rw [h]; ring_nf; simp
    · rw [Finset.mem_singleton] at h
      rw [h]; ring_nf; simp
  have h21 := qdig7_two_sub (m := m) (i₀ := i₀) (u' := u') (x := x)
  have hsum := add_mem_01_012 h32 h21
  have heq : qdig7 m (lamP m i₀ 3 u' * x) - 3 * qdig7 m (lamP m i₀ 1 u' * x) =
      (qdig7 m (lamP m i₀ 3 u' * x) - qdig7 m (lamP m i₀ 2 u' * x) -
        qdig7 m (lamP m i₀ 1 u' * x)) +
      (qdig7 m (lamP m i₀ 2 u' * x) - 2 * qdig7 m (lamP m i₀ 1 u' * x)) := by
    ring
  rwa [heq]

/-- `q(λ'_{j+1}·x) − q(λ'_j·x) − q(λ'_₁·x) ∈ {0,1}` for `1 ≤ j ≤ 4`. -/
theorem qdig7_succ_sub {m i₀ j u' x : ℕ} (_hj : 1 ≤ j ∧ j ≤ 4) :
    qdig7 m (lamP m i₀ (j + 1) u' * x) - qdig7 m (lamP m i₀ j u' * x) -
      qdig7 m (lamP m i₀ 1 u' * x) ∈ ({0, 1} : Finset (ZMod 7)) := by
  have h := qdig7_lamP_add m i₀ j 1 u' x
  rcases Finset.mem_insert.mp h with h | h
  · rw [h]; ring_nf; simp
  · rw [Finset.mem_singleton] at h
    rw [h]; ring_nf; simp

/-- `q(λ'_₅·x) − q(λ'_₂·x) − q(λ'_₃·x) ∈ {0,1}` (`λ'_5 = λ'_2 + λ'_3`). -/
theorem qdig7_five_sub23 {m i₀ u' x : ℕ} :
    qdig7 m (lamP m i₀ 5 u' * x) - qdig7 m (lamP m i₀ 2 u' * x) -
      qdig7 m (lamP m i₀ 3 u' * x) ∈ ({0, 1} : Finset (ZMod 7)) := by
  have h := qdig7_lamP_add m i₀ 2 3 u' x
  rw [show (2 : ℕ) + 3 = 5 from rfl] at h
  rcases Finset.mem_insert.mp h with h | h
  · rw [h]; ring_nf; simp
  · rw [Finset.mem_singleton] at h
    rw [h]; ring_nf; simp

/-- `z ∉ {0,6}` iff `1 ≤ z.val ≤ 5`. -/
theorem not_mem_bad06_iff_val {z : ZMod 7} :
    z ∉ ({0, 6} : Finset (ZMod 7)) ↔ 1 ≤ z.val ∧ z.val ≤ 5 := by
  revert z; decide

/-- `z ∉ bad06` iff `1 ≤ z.val ≤ 5` (the `bad06`-named variant). -/
theorem not_mem_bad06_iff_val' {z : ZMod 7} :
    z ∉ bad06 ↔ 1 ≤ z.val ∧ z.val ≤ 5 := by
  revert z; decide

/-- `1 + k·7^m` is never divisible by `7` for `m ≥ 1`. -/
theorem not_dvd_one_add {k m : ℕ} (hm : 0 < m) : ¬ 7 ∣ (1 + k * 7 ^ m) := by
  intro h
  have h7 : 7 ∣ k * 7 ^ m :=
    dvd_mul_of_dvd_right (dvd_pow_self 7 (Nat.ne_of_gt hm)) k
  have h1 : (1 + k * 7 ^ m) % 7 = 1 := by
    rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd h7]
  have h0 : (1 + k * 7 ^ m) % 7 = 0 := Nat.mod_eq_zero_of_dvd h
  omega

/-! ## The `Λ₀`-finish packaging -/

/-- `runit7` of a level-0 element is just its `ZMod 7` cast (local copy). -/
theorem runit7_of_padic_zero' {x : ℕ} (hx : padicValNat 7 x = 0) :
    runit7 x = (x : ZMod 7) := by
  unfold runit7
  rw [hx, pow_zero, Nat.div_one]

/-- `runit7` of `lamP·d̃` is `↑lamP · runit7 d̃` when both are units. -/
theorem runit7_lamP {m i₀ j u' d : ℕ} (hd0 : padicValNat 7 d = 0)
    (hdpos : 0 < d) (hl : ¬ 7 ∣ lamP m i₀ j u') :
    runit7 (lamP m i₀ j u' * d) = (lamP m i₀ j u' : ZMod 7) * runit7 d := by
  have hl0 : lamP m i₀ j u' ≠ 0 := fun h => hl (h ▸ dvd_zero 7)
  have hd0' : d ≠ 0 := Nat.ne_of_gt hdpos
  have hν : padicValNat 7 (lamP m i₀ j u' * d) = 0 := by
    rw [padicValNat_mul_unit7 hl0 hd0' hl, hd0]
  rw [runit7_of_padic_zero' hν, Nat.cast_mul, runit7_of_padic_zero' hd0]

/-- A level-0 unit's digit under the `Λ₀` multiplier: eq. (10) at `j = 0`.
(Local name `qdig7_lambda0'` — `Case5mBase` exports the general version.) -/
theorem qdig7_lambda0' {m k x : ℕ} (hm : 0 < m) (hx : padicValNat 7 x = 0) :
    qdig7 m ((1 + k * 7 ^ m) * x) =
      qdig7 m x + (k : ZMod 7) * runit7 x := by
  exact qdig7_multLow hm hx


/-- `lamP` is positive under the §5 constraints. -/
theorem lamP_pos {m i₀ j u' : ℕ} (hj : 1 ≤ j ∧ j ≤ 5) (hu' : ¬ 7 ∣ u') :
    0 < lamP m i₀ j u' := by
  unfold lamP
  have hu'0 : 0 < u' := Nat.pos_of_ne_zero (fun h => hu' (h ▸ dvd_zero 7))
  exact Nat.mul_pos (Nat.mul_pos (by omega) hu'0) (by positivity)

/-- Per-element certificate: a `{0,6}`-avoiding shifted digit yields the
`absModN` bound for `d` (via `normU7`). -/
theorem case4_elem_bound {m i₀ j u' k d : ℕ} (hm : 0 < m)
    (hd0 : padicValNat 7 d = 0) (hdpos : 0 < d)
    (hj : 1 ≤ j ∧ j ≤ 5) (him : i₀ ≤ m) (hu' : ¬ 7 ∣ u')
    (hdig : qdig7 m ((1 + k * 7 ^ m) * (lamP m i₀ j u' *
        normU7 (7 ^ (m + 1)) d)) ∉ ({0, 6} : Finset (ZMod 7))) :
    7 ^ m ≤ absModN ((1 + k * 7 ^ m) * lamP m i₀ j u' * d) (7 ^ (m + 1)) := by
  set N := 7 ^ (m + 1) with hN
  have hNpos : 0 < N := Nat.pow_pos (by norm_num)
  have h7N : 7 ∣ N := dvd_pow_self 7 (by omega)
  have hdnd : ¬ 7 ∣ d := by
    have hd0' : d ≠ 0 := Nat.ne_of_gt hdpos
    exact (padic7_eq_zero_iff hd0').mp hd0
  have hdmod : d % N ≠ 0 := fun h0 =>
    hdnd (dvd_trans h7N (Nat.dvd_of_mod_eq_zero h0))
  have hdν : padicValNat 7 (normU7 N d) = 0 :=
    normU7_padic hNpos h7N hdnd
  have hl : ¬ 7 ∣ lamP m i₀ j u' := lamP_not_dvd him hj hu'
  have hl0 : lamP m i₀ j u' ≠ 0 := fun h => hl (h ▸ dvd_zero 7)
  have hd0'' : normU7 N d ≠ 0 := Nat.ne_of_gt (normU7_pos hNpos hdmod)
  have hν : padicValNat 7 (lamP m i₀ j u' * normU7 N d) = 0 := by
    rw [padicValNat_mul_unit7 hl0 hd0'' hl, hdν]
  have hlam : ¬ 7 ∣ (1 + k * 7 ^ m) := not_dvd_one_add hm
  have hv : 1 ≤ (qdig7 m ((1 + k * 7 ^ m) *
        (lamP m i₀ j u' * normU7 N d))).val ∧
      (qdig7 m ((1 + k * 7 ^ m) *
        (lamP m i₀ j u' * normU7 N d))).val ≤ 5 :=
    (not_mem_bad06_iff_val).mp hdig
  have hbound := (absModN_ge_iff_qdig7 (m := m)
      (d := lamP m i₀ j u' * normU7 N d) (lam := 1 + k * 7 ^ m)
      (by rw [hν]; exact hm) (Nat.mul_pos (lamP_pos hj hu') (normU7_pos hNpos hdmod))
      hlam).mpr hv
  rwa [← mul_assoc, normU7_absModN hNpos] at hbound

/-! ## The unified `Λ₀` finish -/

/-- `cycIv c 2` avoids `{0,6}` for `c ∈ {1,2,3,4}`. -/
theorem avoids06_cycIv_2 {c : ZMod 7} (hc : c ∈ ({1, 2, 3, 4} : Finset (ZMod 7))) :
    avoids06 (cycIv c 2) := by
  revert c hc; decide

/-- `cycIv c 4` avoids `{0,6}` for `c ∈ {1,2}`. -/
theorem avoids06_cycIv_4 {c : ZMod 7} (hc : c ∈ ({1, 2} : Finset (ZMod 7))) :
    avoids06 (cycIv c 4) := by
  revert c hc; decide

/-- Two consecutive shifts rescue one leftover element of class `c ∈ {2,4}`:
for every `z, i`, at least one `t ∈ {1−i, 2−i}` keeps `z + c·t` out of `{0,6}`. -/
theorem pair_point_avoid {z c i : ZMod 7} (hc : c ∈ ({2, 4} : Finset (ZMod 7))) :
    ∃ t ∈ ({1 - i, 2 - i} : Finset (ZMod 7)), z + c * t ∉ ({0, 6} : Finset (ZMod 7)) := by
  suffices H : ∀ z c i : ZMod 7, c ∈ ({2, 4} : Finset (ZMod 7)) →
      ∃ t ∈ ({1 - i, 2 - i} : Finset (ZMod 7)),
        z + c * t ∉ ({0, 6} : Finset (ZMod 7)) by
    exact H z c i hc
  set_option synthInstance.maxSize 16384 in
  set_option maxRecDepth 524288 in
  decide

/-- Four consecutive shifts rescue two leftover elements whose classes lie in
`{(2,2),(2,4),(4,2)}` — the `(4,4)` case is genuinely impossible (paper's
WLOG choice of `s`). -/
theorem quad_point_avoid {z₁ z₂ c₁ c₂ i : ZMod 7}
    (hc1 : c₁ ∈ ({2, 4} : Finset (ZMod 7)))
    (hc2 : c₂ ∈ ({2, 4} : Finset (ZMod 7)))
    (hne : ¬ (c₁ = 4 ∧ c₂ = 4)) :
    ∃ t ∈ ({1 - i, 2 - i, 3 - i, 4 - i} : Finset (ZMod 7)),
      z₁ + c₁ * t ∉ ({0, 6} : Finset (ZMod 7)) ∧
      z₂ + c₂ * t ∉ ({0, 6} : Finset (ZMod 7)) := by
  suffices H : ∀ z₁ z₂ c₁ c₂ i : ZMod 7,
      c₁ ∈ ({2, 4} : Finset (ZMod 7)) → c₂ ∈ ({2, 4} : Finset (ZMod 7)) →
      ¬ (c₁ = 4 ∧ c₂ = 4) →
      ∃ t ∈ ({1 - i, 2 - i, 3 - i, 4 - i} : Finset (ZMod 7)),
        z₁ + c₁ * t ∉ ({0, 6} : Finset (ZMod 7)) ∧
        z₂ + c₂ * t ∉ ({0, 6} : Finset (ZMod 7)) by
    exact H z₁ z₂ c₁ c₂ i hc1 hc2 hne
  set_option synthInstance.maxSize 16384 in
  set_option maxRecDepth 524288 in
  decide

/-- The unified §5 finish. Given `j ∈ {1,…,5}` and a shift `t`, set
`k = (t·(λ'_j·s)⁻¹).val` and `lam = (1+k·7^m)·λ'_j`. Class-`cs` units then
shift by `c·t`; intermediate elements keep their `λ'_j` residue (eq. (2));
top-level elements are handled by `absModN_top_ge7`. -/
theorem case4_finish {m i₀ j u' : ℕ} (hm : 0 < m) (him : i₀ ≤ m)
    (hj : 1 ≤ j ∧ j ≤ 5) (hu' : ¬ 7 ∣ u') {s : ZMod 7} (_hs : s ≠ 0)
    (t : ZMod 7) (D : Finset ℕ)
    (hpos : ∀ d ∈ D, 0 < d)
    (hle : ∀ d ∈ D, padicValNat 7 d ≤ m)
    (hgood : ∀ d ∈ D, padicValNat 7 d = 0 →
      (qdig7 m (lamP m i₀ j u' * normU7 (7 ^ (m + 1)) d) +
        t * s⁻¹ * runit7 (normU7 (7 ^ (m + 1)) d)) ∉ ({0, 6} : Finset (ZMod 7)))
    (hd5 : ∀ d ∈ D, 0 < padicValNat 7 d → padicValNat 7 d < m →
      7 ^ m ≤ absModN (lamP m i₀ j u' * d) (7 ^ (m + 1))) :
    ∃ lam : ℕ, 0 < lam ∧ ¬ 7 ∣ lam ∧
      ∀ d ∈ D, 7 ^ m ≤ absModN (lam * d) (7 ^ (m + 1)) := by
  set N := 7 ^ (m + 1) with hN
  have hNpos : 0 < N := Nat.pow_pos (by norm_num)
  have hLp : ¬ 7 ∣ lamP m i₀ j u' := lamP_not_dvd him hj hu'
  have hL7 : (lamP m i₀ j u' : ZMod 7) ≠ 0 := by
    rwa [Ne, ZMod.natCast_eq_zero_iff]
  set k := (t * s⁻¹ * (lamP m i₀ j u' : ZMod 7)⁻¹).val with hk
  have hkcast : (k : ZMod 7) = t * s⁻¹ * (lamP m i₀ j u' : ZMod 7)⁻¹ := by
    rw [hk]; exact ZMod.natCast_zmod_val (t * s⁻¹ * (lamP m i₀ j u' : ZMod 7)⁻¹)
  have hlam : ¬ 7 ∣ (1 + k * 7 ^ m) * lamP m i₀ j u' := by
    intro hdvd
    rcases (Nat.Prime.dvd_mul Nat.prime_seven).mp hdvd with h | h
    · exact not_dvd_one_add hm h
    · exact hLp h
  refine ⟨_, Nat.mul_pos (by positivity) (lamP_pos hj hu'), hlam, ?_⟩
  intro d hd
  have hdpos := hpos d hd
  have hdle := hle d hd
  rcases eq_or_lt_of_le (Nat.zero_le (padicValNat 7 d)) with h0 | h0'
  · -- Level-0 unit: the shifted digit avoids `{0,6}`.
    have hdig : qdig7 m ((1 + k * 7 ^ m) *
        (lamP m i₀ j u' * normU7 N d)) ∉ ({0, 6} : Finset (ZMod 7)) := by
      have hdnd : ¬ 7 ∣ d := (padic7_eq_zero_iff (Nat.ne_of_gt hdpos)).mp h0.symm
      have hdmod : d % N ≠ 0 := fun hh =>
        hdnd (dvd_trans (dvd_pow_self 7 (by omega)) (Nat.dvd_of_mod_eq_zero hh))
      have hdν : padicValNat 7 (normU7 N d) = 0 :=
        normU7_padic hNpos (dvd_pow_self 7 (by omega)) hdnd
      have hd0'' : normU7 N d ≠ 0 := Nat.ne_of_gt (normU7_pos hNpos hdmod)
      have hl0 : lamP m i₀ j u' ≠ 0 := fun h => hLp (h ▸ dvd_zero 7)
      have hνx : padicValNat 7 (lamP m i₀ j u' * normU7 N d) = 0 := by
        rw [padicValNat_mul_unit7 hl0 hd0'' hLp, hdν]
      have hsh : (k : ZMod 7) * runit7 (lamP m i₀ j u' * normU7 N d) =
          t * s⁻¹ * runit7 (normU7 N d) := by
        rw [runit7_lamP hdν (normU7_pos hNpos hdmod) hLp, hkcast]
        have hc : (t * s⁻¹ * (lamP m i₀ j u' : ZMod 7)⁻¹) *
            (lamP m i₀ j u' : ZMod 7) = t * s⁻¹ := by
          rw [mul_assoc, inv_mul_cancel₀ hL7, mul_one]
        rw [← mul_assoc, hc]
      rw [qdig7_lambda0' hm hνx, hsh]
      exact hgood d hd h0.symm
    exact case4_elem_bound hm h0.symm hdpos hj him hu' hdig
  · rcases lt_or_eq_of_le hdle with hlt | heq
    · -- Intermediate level: eq. (8) bound + residue preservation (eq. (2)).
      have hb := hd5 d hd h0' hlt
      have hl0 : lamP m i₀ j u' ≠ 0 := fun h => hLp (h ▸ dvd_zero 7)
      have hνx : 0 < padicValNat 7 (lamP m i₀ j u' * d) := by
        rw [padicValNat_mul_unit7 hl0 (Nat.ne_of_gt hdpos) hLp]; omega
      have hres : absModN ((1 + k * 7 ^ m) * lamP m i₀ j u' * d) N =
          absModN (lamP m i₀ j u' * d) N := by
        unfold absModN
        rw [show ((1 + k * 7 ^ m) * lamP m i₀ j u' * d) % N =
            (lamP m i₀ j u' * d) % N from by
          rw [mul_assoc]
          exact residN_multLow7 hm hνx]
      rwa [hres]
    · -- Top level.
      exact absModN_top_ge7 heq hdpos hlam

/-! ## Hit/shape bridges for the case analysis -/

/-- If `X` fits no 5-interval, it hits every 2-interval. -/
theorem hit2_of_not_subset5 {X : Finset (ZMod 7)}
    (h : ∀ i : ZMod 7, ¬ X ⊆ cycIv i 5) (i : ZMod 7) :
    (X ∩ cycIv i 2).Nonempty := by
  obtain ⟨x, hxX, hxni⟩ := Finset.not_subset.mp (h (i + 2))
  have hx := mem_of_not_mem_cycIv5 hxni
  rw [show i + 2 + 5 = i from by
    have h7 : (2 + 5 : ZMod 7) = 0 := by decide
    rw [add_assoc, h7, add_zero]] at hx
  exact ⟨x, Finset.mem_inter.mpr ⟨hxX, hx⟩⟩

/-- If `X` fits no 4-interval, it hits every 3-interval. -/
theorem hit3_of_not_subset4 {X : Finset (ZMod 7)}
    (h : ∀ i : ZMod 7, ¬ X ⊆ cycIv i 4) (i : ZMod 7) :
    (X ∩ cycIv i 3).Nonempty := by
  obtain ⟨x, hxX, hxni⟩ := Finset.not_subset.mp (h (i + 3))
  have hx := mem_of_not_mem_cycIv4 hxni
  rw [show i + 3 + 4 = i from by
    have h7 : (3 + 4 : ZMod 7) = 0 := by decide
    rw [add_assoc, h7, add_zero]] at hx
  exact ⟨x, Finset.mem_inter.mpr ⟨hxX, hx⟩⟩

/-- A pair `{a,b}` fits a 2-interval iff `b − a ∈ {0,1,6}`. -/
theorem pair_subset2_iff {a b : ZMod 7} :
    (∃ i : ZMod 7, ({a, b} : Finset (ZMod 7)) ⊆ cycIv i 2) ↔
      b - a ∈ ({0, 1, 6} : Finset (ZMod 7)) := by
  revert a b; decide

/-- For `s ∈ {1,2,4}` nonzero, `{s, 2s, 4s} = {1,2,4}`. -/
theorem class_cover {s : ZMod 7} (hs : s ∈ ({1, 2, 4} : Finset (ZMod 7))) :
    ({s, 2 * s, 4 * s} : Finset (ZMod 7)) = {1, 2, 4} := by
  revert s hs; decide

/-- `s⁻¹·(c·s) = c` for `s ≠ 0`. -/
theorem inv_mul_cancel_left' {s c : ZMod 7} (hs : s ≠ 0) :
    s⁻¹ * (c * s) = c := by
  rw [← mul_assoc, mul_comm s⁻¹ c, mul_assoc, inv_mul_cancel₀ hs, mul_one]

/-- The shift on a class-`cs` element is `c·t`. -/
theorem shift_of_class {s c t : ZMod 7} (hs : s ≠ 0) :
    t * s⁻¹ * (c * s) = c * t := by
  calc t * s⁻¹ * (c * s) = t * (s⁻¹ * (c * s)) := by ring
    _ = t * c := by rw [inv_mul_cancel_left' hs]
    _ = c * t := mul_comm _ _

/-- `r ∈ {1,2,4}` decomposes as `r = c·s` with `c ∈ {1,2,4}` relative to any
`s ∈ {1,2,4}`. -/
theorem class_decomp {r s : ZMod 7} (hr : r ∈ ({1, 2, 4} : Finset (ZMod 7)))
    (hs : s ∈ ({1, 2, 4} : Finset (ZMod 7))) :
    ∃ c ∈ ({1, 2, 4} : Finset (ZMod 7)), r = c * s := by
  revert r s hr hs; decide

/-! ### Auxiliary `ZMod 7` checks for the `|Aₛ| = 3` block

`y ∈ cycIv (v + k) 3` transports to `y − v ∈ {k, k+1, k+2}`; used for the
translated `{2,3,4}`/`{3,4,5}` hits in `prop3bx`. -/

theorem s3_cycIv_sub_234 {y v : ZMod 7} (h : y ∈ cycIv (v + 2) 3) :
    y - v ∈ ({2, 3, 4} : Finset (ZMod 7)) := by
  revert y v h; decide

/-- `y ∈ cycIv (v + 3) 3` gives `y − v ∈ {3,4,5}` (translated `{3,4,5}`-hit). -/
theorem s3_cycIv_sub_345 {y v : ZMod 7} (h : y ∈ cycIv (v + 3) 3) :
    y - v ∈ ({3, 4, 5} : Finset (ZMod 7)) := by
  revert y v h; decide

/-- `x + a ≠ x` for `a ≠ 0` in `ZMod 7` (offset distinctness). -/
theorem s3_ne_add {x a : ZMod 7} (ha : a ≠ 0) : x + a ≠ x := by
  revert x a ha; decide

/-- `x + a ≠ x + b` for `a ≠ b` in `ZMod 7` (offset distinctness). -/
theorem s3_ne_add_add {x a b : ZMod 7} (h : a ≠ b) : x + a ≠ x + b := by
  revert x a b h; decide

/-- The integer-level `|D₇(0)| = 4` case (paper §5). -/
theorem lrc7_case4 {m : ℕ} (D : Finset ℕ)
    (hpos : ∀ d ∈ D, 0 < d)
    (hle : ∀ d ∈ D, padicValNat 7 d ≤ m) (hm : 0 < m)
    (hmax : ∃ d ∈ D, padicValNat 7 d = m)
    (hc : (level7 D 0).card = 4) (hcard : D.card ≤ 6) :
    ∃ lam : ℕ, 0 < lam ∧ ¬ 7 ∣ lam ∧
      ∀ d ∈ D, 7 ^ m ≤ absModN (lam * d) (7 ^ (m + 1)) := by
  classical
  set N := 7 ^ (m + 1) with hN
  have hNpos : 0 < N := Nat.pow_pos (by norm_num)
  have h7N : 7 ∣ N := dvd_pow_self 7 (Nat.ne_of_gt (by omega))
  obtain ⟨d1, d2, d3, d4, hd12, hd13, hd14, hd23, hd24, hd34, hU⟩ :=
    Finset.card_eq_four.mp hc
  set U : Finset ℕ := {d1, d2, d3, d4} with hUdef
  have hUmem : ∀ x ∈ U, x ∈ D ∧ padicValNat 7 x = 0 := by
    intro x hx
    have hx' : x ∈ level7 D 0 := by rwa [hU]
    exact Finset.mem_filter.mp hx'
  have hUcard : U.card = 4 := by rw [← hU]; exact hc
  set r : ℕ → ZMod 7 := fun d => runit7 (normU7 N d) with hr
  have hr124 : ∀ d ∈ U, r d ∈ ({1, 2, 4} : Finset (ZMod 7)) := by
    intro d hd
    obtain ⟨hdD, hdν⟩ := hUmem d hd
    have hdnd : ¬ 7 ∣ d :=
      (padic7_eq_zero_iff (Nat.ne_of_gt (hpos d hdD))).mp hdν
    exact normU7_runit hNpos h7N hdnd
  set inter := D.filter (fun d => 0 < padicValNat 7 d ∧ padicValNat 7 d < m)
    with hinter
  obtain ⟨dm, hdm, hνm⟩ := hmax
  have hinter_card : inter.card ≤ 1 := by
    have hdis : Disjoint (level7 D 0) (level7 D m) := by
      rw [Finset.disjoint_left]
      intro x hx0 hxm
      have hx0' := Finset.mem_filter.mp hx0
      have hxm' := Finset.mem_filter.mp hxm
      have := hx0'.2.symm.trans hxm'.2
      omega
    have hsub : level7 D 0 ∪ level7 D m ⊆ D := by
      intro x hx
      rcases Finset.mem_union.mp hx with h | h
      · exact (Finset.mem_filter.mp h).1
      · exact (Finset.mem_filter.mp h).1
    have hml : 1 ≤ (level7 D m).card :=
      Finset.card_pos.mpr ⟨dm, Finset.mem_filter.mpr ⟨hdm, hνm⟩⟩
    have hcardU : (level7 D 0 ∪ level7 D m).card =
        (level7 D 0).card + (level7 D m).card :=
      Finset.card_union_of_disjoint hdis
    have hinter_sub : inter ⊆ D \ (level7 D 0 ∪ level7 D m) := by
      intro x hx
      have hxf := Finset.mem_filter.mp hx
      rw [Finset.mem_sdiff]
      refine ⟨hxf.1, ?_⟩
      intro hxU
      rcases Finset.mem_union.mp hxU with h0 | hm'
      · have h0' := Finset.mem_filter.mp h0
        have := hxf.2
        omega
      · have hm'' := Finset.mem_filter.mp hm'
        have := hxf.2
        omega
    have hle' := Finset.card_le_card hinter_sub
    rw [Finset.card_sdiff_of_subset hsub, hcardU, hc] at hle'
    omega
  have main : ∀ (i₀ u' : ℕ), 0 < i₀ → i₀ ≤ m → ¬ 7 ∣ u' →
      (∀ d ∈ D, 0 < padicValNat 7 d → padicValNat 7 d < m →
        ∀ j : ℕ, 1 ≤ j ∧ j ≤ 5 →
          7 ^ m ≤ absModN (lamP m i₀ j u' * d) N) →
      ∃ lam : ℕ, 0 < lam ∧ ¬ 7 ∣ lam ∧
        ∀ d ∈ D, 7 ^ m ≤ absModN (lam * d) N := by
    intro i₀ u' hi0 him hu'nd hd5bound
    set cnt : ZMod 7 → ℕ := fun c => (U.filter (fun d => r d = c)).card with hcnt
    have hcntsum : cnt 1 + cnt 2 + cnt 4 = 4 := by
      have hpart : U.filter (fun d => r d = 1) ∪ U.filter (fun d => r d = 2) ∪
          U.filter (fun d => r d = 4) = U := by
        ext x
        constructor
        · intro h
          rcases Finset.mem_union.mp h with h | h
          · rcases Finset.mem_union.mp h with h | h
            · exact (Finset.mem_filter.mp h).1
            · exact (Finset.mem_filter.mp h).1
          · exact (Finset.mem_filter.mp h).1
        · intro hx
          have hrx := hr124 x hx
          rcases Finset.mem_insert.mp hrx with h | h
          · exact Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hx, h⟩))
          rcases Finset.mem_insert.mp h with h | h
          · exact Finset.mem_union_left _
              (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hx, h⟩))
          · exact Finset.mem_union_right _
              (Finset.mem_filter.mpr ⟨hx, Finset.mem_singleton.mp h⟩)
      have hd1 : Disjoint (U.filter (fun d => r d = 1))
          (U.filter (fun d => r d = 2)) := by
        rw [Finset.disjoint_left]
        intro x h1 h2
        rw [Finset.mem_filter] at h1 h2
        rw [h1.2] at h2
        exact absurd h2.2 (by decide)
      have hd124 : Disjoint (U.filter (fun d => r d = 1) ∪
          U.filter (fun d => r d = 2)) (U.filter (fun d => r d = 4)) := by
        rw [Finset.disjoint_left]
        intro x h12 h4
        rw [Finset.mem_filter] at h4
        rcases Finset.mem_union.mp h12 with h1 | h2
        · rw [Finset.mem_filter] at h1
          rw [h1.2] at h4
          exact absurd h4.2 (by decide)
        · rw [Finset.mem_filter] at h2
          rw [h2.2] at h4
          exact absurd h4.2 (by decide)
      rw [← hUcard, ← hpart,
        Finset.card_union_of_disjoint hd124,
        Finset.card_union_of_disjoint hd1]
    obtain ⟨s, hs124, hsmax⟩ := Finset.exists_max_image
        ({1, 2, 4} : Finset (ZMod 7)) cnt (by decide)
    have hs0 : s ≠ 0 := by
      have := hs124
      rcases Finset.mem_insert.mp this with h | h
      · rw [h]; decide
      rcases Finset.mem_insert.mp h with h | h
      · rw [h]; decide
      · rw [Finset.mem_singleton.mp h]; decide
    set S := U.filter (fun d => r d = s) with hS
    have hScard : S.card = cnt s := by rw [hS, hcnt]
    have hSge : 2 ≤ S.card := by
      have h1 := hsmax 1 (by decide)
      have h2 := hsmax 2 (by decide)
      have h4 := hsmax 4 (by decide)
      rw [hScard]
      omega
    have hSle : S.card ≤ 4 := by
      have := Finset.card_filter_le U (fun d => r d = s)
      rwa [hUcard] at this
    set X : ℕ → Finset (ZMod 7) := fun j =>
      S.image (fun d => qdig7 m (lamP m i₀ j u' * normU7 N d)) with hX
    have hXj : ∀ j, X j = S.image
        (fun d => qdig7 m (lamP m i₀ j u' * normU7 N d)) := fun _ => rfl
    interval_cases hSc : S.card
    · -- <<S2-TARGET: fill this |A_s|=2 case — interval_cases orders low→high: THIS bullet has hSc : S.card = 2>>
      -- |A_s| = 2 (paper §5, Case 3). WLOG the two leftover classes are not both
      -- `4s`: the (4,4) configuration fails for the 4-consecutive-shift argument,
      -- so re-select the principal class `s' := 4s` when needed — the old extras
      -- become principal and the old S becomes class-`2s'` extras.
      obtain ⟨s', hs'124, hS'2, hnot44⟩ : ∃ s' ∈ ({1, 2, 4} : Finset (ZMod 7)),
          (U.filter (fun d => r d = s')).card = 2 ∧
          ¬ (∀ e ∈ U, r e ≠ s' → r e = 4 * s') := by
        by_cases h44 : ∀ e ∈ U, r e ≠ s → r e = 4 * s
        · have h4s124 : (4 : ZMod 7) * s ∈ ({1, 2, 4} : Finset (ZMod 7)) := by
            have h := hs124
            rcases Finset.mem_insert.mp h with rfl | h
            · decide
            rcases Finset.mem_insert.mp h with rfl | h
            · decide
            rw [Finset.mem_singleton] at h; rw [h]; decide
          have h4ne : (4 : ZMod 7) * s ≠ s := by
            have h := hs124
            rcases Finset.mem_insert.mp h with rfl | h
            · decide
            rcases Finset.mem_insert.mp h with rfl | h
            · decide
            rw [Finset.mem_singleton] at h; rw [h]; decide
          have hfilter : U.filter (fun d => r d = 4 * s) =
              U.filter (fun d => r d ≠ s) := by
            apply Finset.filter_congr
            intro x hx
            constructor
            · intro hx4
              rw [hx4]
              exact h4ne
            · intro hxne
              exact h44 x hx hxne
          have hcard4 : (U.filter (fun d => r d = 4 * s)).card = 2 := by
            have heq : U.filter (fun d => r d ≠ s) = U \ S := by
              ext x
              simp only [Finset.mem_filter, Finset.mem_sdiff, hS]
              constructor
              · rintro ⟨hxU, hxne⟩
                exact ⟨hxU, fun hxs => hxne hxs.2⟩
              · rintro ⟨hxU, hxnS⟩
                exact ⟨hxU, fun hxs => hxnS ⟨hxU, hxs⟩⟩
            have hsubU : S ⊆ U := Finset.filter_subset (fun d => r d = s) U
            rw [hfilter, heq, Finset.card_sdiff_of_subset hsubU, hUcard, hSc]
          have hnot : ¬ (∀ e ∈ U, r e ≠ 4 * s → r e = 4 * (4 * s)) := by
            intro hall
            have hne2 : (4 : ZMod 7) * (4 * s) ≠ s := by
              have h := hs124
              rcases Finset.mem_insert.mp h with rfl | h
              · decide
              rcases Finset.mem_insert.mp h with rfl | h
              · decide
              rw [Finset.mem_singleton] at h; rw [h]; decide
            obtain ⟨e, heS⟩ : S.Nonempty := Finset.card_pos.mp (by omega)
            rw [hS] at heS
            obtain ⟨heU, hes⟩ := Finset.mem_filter.mp heS
            have hne4 : r e ≠ 4 * s := by rw [hes]; exact Ne.symm h4ne
            have heq4 := hall e heU hne4
            rw [hes] at heq4
            exact hne2 heq4.symm
          exact ⟨4 * s, h4s124, hcard4, hnot⟩
        · exact ⟨s, hs124, by rw [← hS]; exact hSc, h44⟩
      have hs'0 : s' ≠ 0 := by
        have h := hs'124
        rcases Finset.mem_insert.mp h with rfl | h
        · decide
        rcases Finset.mem_insert.mp h with rfl | h
        · decide
        rw [Finset.mem_singleton] at h; rw [h]; decide
      set S' : Finset ℕ := U.filter (fun d => r d = s') with hS'def
      have hS'card : S'.card = 2 := by rw [hS'def]; exact hS'2
      set X' : ℕ → Finset (ZMod 7) := fun j =>
        S'.image (fun d => qdig7 m (lamP m i₀ j u' * normU7 N d)) with hX'
      by_cases h2 : ∃ j ∈ Finset.Icc 1 5, ∃ i : ZMod 7, X' j ⊆ cycIv i 2
      · -- ℓ ≤ 2 somewhere: 4 consecutive shifts rescue both extras.
        obtain ⟨j, hj, i, hi⟩ := h2
        rw [Finset.mem_Icc] at hj
        have hExtraCard : (U \ S').card = 2 := by
          have hsub : S' ⊆ U := Finset.filter_subset (fun d => r d = s') U
          rw [Finset.card_sdiff_of_subset hsub, hUcard, hS'card]
        obtain ⟨e1, e2, he12, hExtraEq⟩ := Finset.card_eq_two.mp hExtraCard
        have he1mem : e1 ∈ U \ S' := by
          rw [hExtraEq]; exact Finset.mem_insert_self _ _
        have he2mem : e2 ∈ U \ S' := by
          rw [hExtraEq]
          exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self _))
        have he1U : e1 ∈ U := (Finset.mem_sdiff.mp he1mem).1
        have he2U : e2 ∈ U := (Finset.mem_sdiff.mp he2mem).1
        have he1nS : e1 ∉ S' := (Finset.mem_sdiff.mp he1mem).2
        have he2nS : e2 ∉ S' := (Finset.mem_sdiff.mp he2mem).2
        have he1r : r e1 ≠ s' := fun h => he1nS (by
          rw [hS'def]; exact Finset.mem_filter.mpr ⟨he1U, h⟩)
        have he2r : r e2 ≠ s' := fun h => he2nS (by
          rw [hS'def]; exact Finset.mem_filter.mpr ⟨he2U, h⟩)
        obtain ⟨c1, hc1_124, he1c⟩ := class_decomp (hr124 e1 he1U) hs'124
        obtain ⟨c2, hc2_124, he2c⟩ := class_decomp (hr124 e2 he2U) hs'124
        have hc1 : c1 ∈ ({2, 4} : Finset (ZMod 7)) := by
          rcases Finset.mem_insert.mp hc1_124 with h1 | h24
          · exfalso
            rw [h1, one_mul] at he1c
            exact he1r he1c
          rcases Finset.mem_insert.mp h24 with h2v | h4v
          · rw [h2v]; decide
          · rw [Finset.mem_singleton] at h4v; rw [h4v]; decide
        have hc2 : c2 ∈ ({2, 4} : Finset (ZMod 7)) := by
          rcases Finset.mem_insert.mp hc2_124 with h1 | h24
          · exfalso
            rw [h1, one_mul] at he2c
            exact he2r he2c
          rcases Finset.mem_insert.mp h24 with h2v | h4v
          · rw [h2v]; decide
          · rw [Finset.mem_singleton] at h4v; rw [h4v]; decide
        have hne : ¬ (c1 = 4 ∧ c2 = 4) := by
          rintro ⟨h1, h2v⟩
          apply hnot44
          intro e heU hens
          have heS : e ∈ U \ S' := by
            rw [Finset.mem_sdiff]
            refine ⟨heU, ?_⟩
            intro hmemS
            have h := hmemS
            rw [hS'def] at h
            exact hens (Finset.mem_filter.mp h).2
          rw [hExtraEq] at heS
          rcases Finset.mem_insert.mp heS with rfl | hmem
          · rw [he1c, h1]
          · rw [Finset.mem_singleton] at hmem
            rw [hmem, he2c, h2v]
        obtain ⟨t, ht4, hz1, hz2⟩ := quad_point_avoid
          (z₁ := qdig7 m (lamP m i₀ j u' * normU7 N e1))
          (z₂ := qdig7 m (lamP m i₀ j u' * normU7 N e2))
          (c₁ := c1) (c₂ := c2) (i := i) hc1 hc2 hne
        have hit : i + t ∈ ({1, 2, 3, 4} : Finset (ZMod 7)) := by
          have htv : i + t = 1 ∨ i + t = 2 ∨ i + t = 3 ∨ i + t = 4 := by
            rcases Finset.mem_insert.mp ht4 with h | h
            · exact Or.inl (by rw [h]; ring)
            rcases Finset.mem_insert.mp h with h | h
            · exact Or.inr (Or.inl (by rw [h]; ring))
            rcases Finset.mem_insert.mp h with h | h
            · exact Or.inr (Or.inr (Or.inl (by rw [h]; ring)))
            · exact Or.inr (Or.inr (Or.inr (by rw [Finset.mem_singleton.mp h]; ring)))
          rcases htv with h | h | h | h <;> rw [h] <;> decide
        have hshS : t * s'⁻¹ * s' = t := by
          have h := shift_of_class (s := s') (c := 1) (t := t) hs'0
          simpa using h
        apply case4_finish hm him hj hu'nd hs'0 t D hpos hle
        · intro d hdD hdν
          have hdU : d ∈ U := by
            have hdL : d ∈ level7 D 0 := Finset.mem_filter.mpr ⟨hdD, hdν⟩
            rwa [hU] at hdL
          by_cases hdS : d ∈ S'
          · have hdr : r d = s' := by
              have h := hdS
              rw [hS'def] at h
              exact (Finset.mem_filter.mp h).2
            have hqd : qdig7 m (lamP m i₀ j u' * normU7 N d) ∈ X' j :=
              Finset.mem_image.mpr ⟨d, hdS, rfl⟩
            have hdrd : runit7 (normU7 (7 ^ (m + 1)) d) = s' := hdr
            rw [hdrd, hshS]
            have hshift : qdig7 m (lamP m i₀ j u' * normU7 N d) + t ∈
                cycIv (i + t) 2 := by
              have hmem := hi hqd
              have himg : qdig7 m (lamP m i₀ j u' * normU7 N d) + t ∈
                  (cycIv i 2).image (· + t) :=
                Finset.mem_image.mpr ⟨_, hmem, rfl⟩
              rwa [cycIv_image_add] at himg
            exact avoids06_cycIv_2 hit _ hshift
          · have hdExtra : d ∈ U \ S' := Finset.mem_sdiff.mpr ⟨hdU, hdS⟩
            rw [hExtraEq] at hdExtra
            rcases Finset.mem_insert.mp hdExtra with hde1 | hdE2
            · rw [hde1]
              have hrd1 : runit7 (normU7 (7 ^ (m + 1)) e1) = c1 * s' := he1c
              rw [hrd1, shift_of_class hs'0]
              exact hz1
            · rw [Finset.mem_singleton] at hdE2
              rw [hdE2]
              have hrd2 : runit7 (normU7 (7 ^ (m + 1)) e2) = c2 * s' := he2c
              rw [hrd2, shift_of_class hs'0]
              exact hz2
        · intro d hd h0' hlt
          exact hd5bound d hd h0' hlt j hj
      · -- No 2-interval fits any X' j: the propagation lemmas force a
        -- contradiction, so this branch is vacuous (paper's repeated use of (9)).
        push Not at h2
        obtain ⟨dA, dB, hdAB, hS'eq⟩ := Finset.card_eq_two.mp hS'card
        have hX'eq : ∀ j : ℕ, X' j = ({qdig7 m (lamP m i₀ j u' * normU7 N dA),
            qdig7 m (lamP m i₀ j u' * normU7 N dB)} : Finset (ZMod 7)) := by
          intro j
          have hX'j : X' j = S'.image
              (fun d => qdig7 m (lamP m i₀ j u' * normU7 N d)) := rfl
          rw [hX'j, hS'eq]
          ext w
          simp only [Finset.mem_image, Finset.mem_insert, Finset.mem_singleton]
          constructor
          · rintro ⟨d, hd, rfl⟩
            rcases hd with rfl | rfl
            · exact Or.inl rfl
            · exact Or.inr rfl
          · intro hw
            rcases hw with rfl | rfl
            · exact ⟨dA, Or.inl rfl, rfl⟩
            · exact ⟨dB, Or.inr rfl, rfl⟩
        have hdist : ∀ j ∈ Finset.Icc 1 5,
            qdig7 m (lamP m i₀ j u' * normU7 N dB) -
              qdig7 m (lamP m i₀ j u' * normU7 N dA) ∉
              ({0, 1, 6} : Finset (ZMod 7)) := by
          intro j hj hmem
          obtain ⟨i, hi⟩ := pair_subset2_iff.mpr hmem
          rw [← hX'eq j] at hi
          exact h2 j hj i hi
        have hcomp : ∀ z : ZMod 7, z ∉ ({0, 1, 6} : Finset (ZMod 7)) →
            z ∈ ({2, 3, 4, 5} : Finset (ZMod 7)) := by
          decide
        have hnegSymm : ∀ z : ZMod 7, z ∉ ({0, 1, 6} : Finset (ZMod 7)) →
            -z ∉ ({0, 1, 6} : Finset (ZMod 7)) := by
          decide
        have hswapDist : ∀ j ∈ Finset.Icc 1 5,
            qdig7 m (lamP m i₀ j u' * normU7 N dA) -
              qdig7 m (lamP m i₀ j u' * normU7 N dB) ∉
              ({0, 1, 6} : Finset (ZMod 7)) := by
          intro j hj
          have h := hnegSymm _ (hdist j hj)
          rwa [neg_sub] at h
        have hmem1 : qdig7 m (lamP m i₀ 1 u' * normU7 N dB) -
            qdig7 m (lamP m i₀ 1 u' * normU7 N dA) ∈
            ({2, 3, 4, 5} : Finset (ZMod 7)) :=
          hcomp _ (hdist 1 (Finset.mem_Icc.mpr ⟨by decide, by decide⟩))
        obtain ⟨a0, a1, hD01, hΔ, hdistO⟩ : ∃ a0 a1 : ℕ,
            S' = ({a0, a1} : Finset ℕ) ∧
            (qdig7 m (lamP m i₀ 1 u' * normU7 N a1) -
              qdig7 m (lamP m i₀ 1 u' * normU7 N a0) = 2 ∨
             qdig7 m (lamP m i₀ 1 u' * normU7 N a1) -
              qdig7 m (lamP m i₀ 1 u' * normU7 N a0) = 3) ∧
            (∀ j ∈ Finset.Icc 1 5, qdig7 m (lamP m i₀ j u' * normU7 N a1) -
              qdig7 m (lamP m i₀ j u' * normU7 N a0) ∉
              ({0, 1, 6} : Finset (ZMod 7))) := by
          rcases Finset.mem_insert.mp hmem1 with h2v | h345
          · exact ⟨dA, dB, hS'eq, Or.inl h2v, hdist⟩
          rcases Finset.mem_insert.mp h345 with h3v | h45
          · exact ⟨dA, dB, hS'eq, Or.inr h3v, hdist⟩
          rcases Finset.mem_insert.mp h45 with h4v | h5v
          · have hswap : qdig7 m (lamP m i₀ 1 u' * normU7 N dA) -
                qdig7 m (lamP m i₀ 1 u' * normU7 N dB) = 3 := by
              rw [← neg_sub, h4v]
              decide
            exact ⟨dB, dA, hS'eq.trans (Finset.pair_comm dA dB), Or.inr hswap,
              hswapDist⟩
          · rw [Finset.mem_singleton] at h5v
            have hswap : qdig7 m (lamP m i₀ 1 u' * normU7 N dA) -
                qdig7 m (lamP m i₀ 1 u' * normU7 N dB) = 2 := by
              rw [← neg_sub, h5v]
              decide
            exact ⟨dB, dA, hS'eq.trans (Finset.pair_comm dA dB), Or.inl hswap,
              hswapDist⟩
        rcases hΔ with hΔ2 | hΔ3
        · -- `{x, x+2}` shape: `prop2ix` (j=3 via `qdig7_three_sub`,
          -- j=4 and j=5 via `qdig7_succ_sub`).
          have hq1d1 : qdig7 m (lamP m i₀ 1 u' * normU7 N a1) =
              qdig7 m (lamP m i₀ 1 u' * normU7 N a0) + 2 :=
            (sub_eq_iff_eq_add.mp hΔ2).trans (add_comm _ _)
          have hb0 := qdig7_three_sub (m := m) (i₀ := i₀) (u' := u')
            (x := normU7 N a0)
          have hb1 := qdig7_three_sub (m := m) (i₀ := i₀) (u' := u')
            (x := normU7 N a1)
          rw [hq1d1] at hb1
          have hc0 : qdig7 m (lamP m i₀ 4 u' * normU7 N a0) -
              qdig7 m (lamP m i₀ 3 u' * normU7 N a0) -
              qdig7 m (lamP m i₀ 1 u' * normU7 N a0) ∈
              ({0, 1} : Finset (ZMod 7)) :=
            qdig7_succ_sub (m := m) (i₀ := i₀) (j := 3) (u' := u')
              (x := normU7 N a0) ⟨by decide, by decide⟩
          have hc1 : qdig7 m (lamP m i₀ 4 u' * normU7 N a1) -
              qdig7 m (lamP m i₀ 3 u' * normU7 N a1) -
              qdig7 m (lamP m i₀ 1 u' * normU7 N a1) ∈
              ({0, 1} : Finset (ZMod 7)) :=
            qdig7_succ_sub (m := m) (i₀ := i₀) (j := 3) (u' := u')
              (x := normU7 N a1) ⟨by decide, by decide⟩
          rw [hq1d1] at hc1
          have he0 : qdig7 m (lamP m i₀ 5 u' * normU7 N a0) -
              qdig7 m (lamP m i₀ 4 u' * normU7 N a0) -
              qdig7 m (lamP m i₀ 1 u' * normU7 N a0) ∈
              ({0, 1} : Finset (ZMod 7)) :=
            qdig7_succ_sub (m := m) (i₀ := i₀) (j := 4) (u' := u')
              (x := normU7 N a0) ⟨by decide, by decide⟩
          have he1 : qdig7 m (lamP m i₀ 5 u' * normU7 N a1) -
              qdig7 m (lamP m i₀ 4 u' * normU7 N a1) -
              qdig7 m (lamP m i₀ 1 u' * normU7 N a1) ∈
              ({0, 1} : Finset (ZMod 7)) :=
            qdig7_succ_sub (m := m) (i₀ := i₀) (j := 4) (u' := u')
              (x := normU7 N a1) ⟨by decide, by decide⟩
          rw [hq1d1] at he1
          have hfit := prop2ix _ _ hb0 hb1
            (hdistO 3 (Finset.mem_Icc.mpr ⟨by decide, by decide⟩))
            _ _ hc0 hc1
            (hdistO 4 (Finset.mem_Icc.mpr ⟨by decide, by decide⟩))
            _ _ he0 he1
          exact (hdistO 5 (Finset.mem_Icc.mpr ⟨by decide, by decide⟩) hfit).elim
        · -- `{x, x+3}` shape: `prop2iix` (j=2 via `qdig7_two_sub`,
          -- j=3 via `qdig7_succ_sub`, j=5 via `qdig7_five_sub23`).
          have hq1d1 : qdig7 m (lamP m i₀ 1 u' * normU7 N a1) =
              qdig7 m (lamP m i₀ 1 u' * normU7 N a0) + 3 :=
            (sub_eq_iff_eq_add.mp hΔ3).trans (add_comm _ _)
          have hb0 := qdig7_two_sub (m := m) (i₀ := i₀) (u' := u')
            (x := normU7 N a0)
          have hb1 := qdig7_two_sub (m := m) (i₀ := i₀) (u' := u')
            (x := normU7 N a1)
          rw [hq1d1] at hb1
          have hc0 : qdig7 m (lamP m i₀ 3 u' * normU7 N a0) -
              qdig7 m (lamP m i₀ 2 u' * normU7 N a0) -
              qdig7 m (lamP m i₀ 1 u' * normU7 N a0) ∈
              ({0, 1} : Finset (ZMod 7)) :=
            qdig7_succ_sub (m := m) (i₀ := i₀) (j := 2) (u' := u')
              (x := normU7 N a0) ⟨by decide, by decide⟩
          have hc1 : qdig7 m (lamP m i₀ 3 u' * normU7 N a1) -
              qdig7 m (lamP m i₀ 2 u' * normU7 N a1) -
              qdig7 m (lamP m i₀ 1 u' * normU7 N a1) ∈
              ({0, 1} : Finset (ZMod 7)) :=
            qdig7_succ_sub (m := m) (i₀ := i₀) (j := 2) (u' := u')
              (x := normU7 N a1) ⟨by decide, by decide⟩
          rw [hq1d1] at hc1
          have he0 := qdig7_five_sub23 (m := m) (i₀ := i₀) (u' := u')
            (x := normU7 N a0)
          have he1 := qdig7_five_sub23 (m := m) (i₀ := i₀) (u' := u')
            (x := normU7 N a1)
          have hfit := prop2iix _ _ hb0 hb1
            (hdistO 2 (Finset.mem_Icc.mpr ⟨by decide, by decide⟩))
            _ _ hc0 hc1
            (hdistO 3 (Finset.mem_Icc.mpr ⟨by decide, by decide⟩))
            _ _ he0 he1
          exact (hdistO 5 (Finset.mem_Icc.mpr ⟨by decide, by decide⟩) hfit).elim
    · -- <<S3-TARGET>> |A_s| = 3: S.card = 3, one extra in U \ S (classes 2/4).
      by_cases h4 : ∃ j ∈ Finset.Icc 1 5, ∃ i : ZMod 7, X j ⊆ cycIv i 4
      · -- eq. (11) holds: both shifts `t ∈ {1−i, 2−i}` keep `X j` off `{0,6}`,
        -- and `pair_point_avoid` picks one rescuing the extra unit `e`.
        obtain ⟨j, hj, i, hi⟩ := h4
        rw [Finset.mem_Icc] at hj
        have hSU : S ⊆ U := Finset.filter_subset _ _
        have hcard1 : (U \ S).card = 1 := by
          rw [Finset.card_sdiff_of_subset hSU, hUcard, hSc]
        obtain ⟨e, he⟩ := Finset.card_eq_one.mp hcard1
        have hemem : e ∈ U \ S := by
          rw [he]; exact Finset.mem_singleton_self e
        have heU : e ∈ U := (Finset.mem_sdiff.mp hemem).1
        have heS : e ∉ S := (Finset.mem_sdiff.mp hemem).2
        obtain ⟨c, hc124, hce⟩ := class_decomp (hr124 e heU) hs124
        have hc24 : c ∈ ({2, 4} : Finset (ZMod 7)) := by
          have hc1 : c ≠ 1 := by
            intro h1
            apply heS
            rw [hS]
            exact Finset.mem_filter.mpr ⟨heU, by rw [hce, h1, one_mul]⟩
          rcases Finset.mem_insert.mp hc124 with h | h
          · exact absurd h hc1
          rcases Finset.mem_insert.mp h with h | h
          · rw [h]; decide
          · rw [Finset.mem_singleton.mp h]; decide
        obtain ⟨t, ht, htgood⟩ := pair_point_avoid
          (z := qdig7 m (lamP m i₀ j u' * normU7 (7 ^ (m + 1)) e))
          (c := c) (i := i) hc24
        apply case4_finish hm him hj hu'nd hs0 t D hpos hle
        · intro d hdD hdν
          have hdU : d ∈ U := by
            have hdL : d ∈ level7 D 0 := Finset.mem_filter.mpr ⟨hdD, hdν⟩
            rwa [hU] at hdL
          by_cases hdS : d ∈ S
          · have hrd : runit7 (normU7 (7 ^ (m + 1)) d) = s := by
              rw [hS] at hdS
              exact (Finset.mem_filter.mp hdS).2
            rw [hrd, mul_assoc, inv_mul_cancel₀ hs0, mul_one]
            have hqd : qdig7 m (lamP m i₀ j u' * normU7 N d) ∈ X j := by
              rw [hXj j]
              exact Finset.mem_image.mpr ⟨d, hdS, rfl⟩
            have hshift : qdig7 m (lamP m i₀ j u' * normU7 N d) + t ∈
                cycIv (i + t) 4 := (mem_cycIv_add (a := t)).mp (hi hqd)
            have hi2 : i + t ∈ ({1, 2} : Finset (ZMod 7)) := by
              rcases Finset.mem_insert.mp ht with h | h
              · rw [h]
                have h1i : i + (1 - i) = (1 : ZMod 7) := by ring
                rw [h1i]
                exact Finset.mem_insert_self _ _
              · rw [Finset.mem_singleton.mp h]
                have h2i : i + (2 - i) = (2 : ZMod 7) := by ring
                rw [h2i]
                exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
            simpa [bad06] using avoids06_cycIv_4 hi2 _ hshift
          · have hde : d = e := by
              have hd' : d ∈ U \ S := Finset.mem_sdiff.mpr ⟨hdU, hdS⟩
              rw [he] at hd'
              exact Finset.mem_singleton.mp hd'
            rw [hde]
            have hre : runit7 (normU7 (7 ^ (m + 1)) e) = c * s := hce
            rw [hre, shift_of_class hs0]
            exact htgood
        · intro d hd h0' hlt
          exact hd5bound d hd h0' hlt j hj
      · -- eq. (11) fails for all `j`: the carry chain forces a 4-interval.
        push Not at h4
        obtain ⟨a, b, c, -, -, -, hSeq⟩ := Finset.card_eq_three.mp hSc
        have hX1 : X 1 = ({qdig7 m (lamP m i₀ 1 u' * normU7 N a),
            qdig7 m (lamP m i₀ 1 u' * normU7 N b),
            qdig7 m (lamP m i₀ 1 u' * normU7 N c)} : Finset (ZMod 7)) := by
          rw [hXj 1, hSeq, Finset.image_insert, Finset.image_insert,
            Finset.image_singleton]
        have hns1 : ∀ i : ZMod 7, ¬ ({qdig7 m (lamP m i₀ 1 u' * normU7 N a),
            qdig7 m (lamP m i₀ 1 u' * normU7 N b),
            qdig7 m (lamP m i₀ 1 u' * normU7 N c)} : Finset (ZMod 7)) ⊆
            cycIv i 4 := by
          intro i hsub
          rw [← hX1] at hsub
          exact h4 1 (by decide) i hsub
        rcases shape3 hns1 with ⟨x, hsh⟩ | ⟨x, hsh⟩
        · -- `X 1 = {x, x+1, x+4}`: the `j = 2` digits already fit a 4-interval.
          have hex : ∀ w : ZMod 7, ∃ d : ℕ,
              w ∈ ({x, x + 1, x + 4} : Finset (ZMod 7)) →
              d ∈ S ∧ qdig7 m (lamP m i₀ 1 u' * normU7 N d) = w := by
            intro w
            by_cases hw : w ∈ ({x, x + 1, x + 4} : Finset (ZMod 7))
            · have hwX : w ∈ X 1 := by rwa [hX1, hsh]
              obtain ⟨d, hd, hdq⟩ := Finset.mem_image.mp hwX
              exact ⟨d, fun _ => ⟨hd, hdq⟩⟩
            · exact ⟨0, fun h => absurd h hw⟩
          choose e he using hex
          have e0 := he x (Finset.mem_insert_self _ _)
          have e1 := he (x + 1)
            (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
          have e4 := he (x + 4)
            (Finset.mem_insert_of_mem
              (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
          have hne01 : e x ≠ e (x + 1) := by
            intro h
            have hq := e0.2
            rw [h, e1.2] at hq
            exact absurd hq (add_one_ne_self x)
          have hne04 : e x ≠ e (x + 4) := by
            intro h
            have hq := e0.2
            rw [h, e4.2] at hq
            exact absurd hq (s3_ne_add (a := 4) (by decide))
          have hne14 : e (x + 1) ≠ e (x + 4) := by
            intro h
            have hq := e1.2
            rw [h, e4.2] at hq
            exact absurd hq (s3_ne_add_add (a := 4) (b := 1) (by decide))
          have hcard3 : ({e x, e (x + 1), e (x + 4)} : Finset ℕ).card = 3 :=
            Finset.card_eq_three.mpr ⟨e x, e (x + 1), e (x + 4),
              hne01, hne04, hne14, rfl⟩
          have hES : ({e x, e (x + 1), e (x + 4)} : Finset ℕ) = S := by
            apply Finset.eq_of_subset_of_card_le
            · intro w hw
              simp only [Finset.mem_insert, Finset.mem_singleton] at hw
              rcases hw with rfl | rfl | rfl
              exacts [e0.1, e1.1, e4.1]
            · exact le_of_eq (hSc.trans hcard3.symm)
          have hXeq : ∀ j : ℕ, ({qdig7 m (lamP m i₀ j u' * normU7 N (e x)),
              qdig7 m (lamP m i₀ j u' * normU7 N (e (x + 1))),
              qdig7 m (lamP m i₀ j u' * normU7 N (e (x + 4)))} :
              Finset (ZMod 7)) = X j := by
            intro j
            rw [hXj j, ← hES, Finset.image_insert, Finset.image_insert,
              Finset.image_singleton]
          have hb0 := qdig7_two_sub (m := m) (i₀ := i₀) (u' := u')
            (x := normU7 N (e x))
          have hb1 := qdig7_two_sub (m := m) (i₀ := i₀) (u' := u')
            (x := normU7 N (e (x + 1)))
          have hb2 := qdig7_two_sub (m := m) (i₀ := i₀) (u' := u')
            (x := normU7 N (e (x + 4)))
          rw [e0.2] at hb0
          rw [e1.2] at hb1
          rw [e4.2] at hb2
          obtain ⟨i2, hi2⟩ := prop3ax _ _ _ hb0 hb1 hb2
          rw [hXeq 2] at hi2
          exact absurd hi2 (h4 2 (by decide) i2)
        · -- `X 1 = {x, x+2, x+4}`: `j = 3` hits `{2,3,4}`/`{3,4,5}` force the
          -- endpoints `b0 = 2`, `b2 = 5`; `j = 4` then fits a 4-interval.
          have hex : ∀ w : ZMod 7, ∃ d : ℕ,
              w ∈ ({x, x + 2, x + 4} : Finset (ZMod 7)) →
              d ∈ S ∧ qdig7 m (lamP m i₀ 1 u' * normU7 N d) = w := by
            intro w
            by_cases hw : w ∈ ({x, x + 2, x + 4} : Finset (ZMod 7))
            · have hwX : w ∈ X 1 := by rwa [hX1, hsh]
              obtain ⟨d, hd, hdq⟩ := Finset.mem_image.mp hwX
              exact ⟨d, fun _ => ⟨hd, hdq⟩⟩
            · exact ⟨0, fun h => absurd h hw⟩
          choose e he using hex
          have e0 := he x (Finset.mem_insert_self _ _)
          have e2 := he (x + 2)
            (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
          have e4 := he (x + 4)
            (Finset.mem_insert_of_mem
              (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
          have hne02 : e x ≠ e (x + 2) := by
            intro h
            have hq := e0.2
            rw [h, e2.2] at hq
            exact absurd hq (s3_ne_add (a := 2) (by decide))
          have hne04 : e x ≠ e (x + 4) := by
            intro h
            have hq := e0.2
            rw [h, e4.2] at hq
            exact absurd hq (s3_ne_add (a := 4) (by decide))
          have hne24 : e (x + 2) ≠ e (x + 4) := by
            intro h
            have hq := e2.2
            rw [h, e4.2] at hq
            exact absurd hq (s3_ne_add_add (a := 4) (b := 2) (by decide))
          have hcard3 : ({e x, e (x + 2), e (x + 4)} : Finset ℕ).card = 3 :=
            Finset.card_eq_three.mpr ⟨e x, e (x + 2), e (x + 4),
              hne02, hne04, hne24, rfl⟩
          have hES : ({e x, e (x + 2), e (x + 4)} : Finset ℕ) = S := by
            apply Finset.eq_of_subset_of_card_le
            · intro w hw
              simp only [Finset.mem_insert, Finset.mem_singleton] at hw
              rcases hw with rfl | rfl | rfl
              exacts [e0.1, e2.1, e4.1]
            · exact le_of_eq (hSc.trans hcard3.symm)
          have hXeq : ∀ j : ℕ, ({qdig7 m (lamP m i₀ j u' * normU7 N (e x)),
              qdig7 m (lamP m i₀ j u' * normU7 N (e (x + 2))),
              qdig7 m (lamP m i₀ j u' * normU7 N (e (x + 4)))} :
              Finset (ZMod 7)) = X j := by
            intro j
            rw [hXj j, ← hES, Finset.image_insert, Finset.image_insert,
              Finset.image_singleton]
          have hX3 := hXeq 3
          have hX4 := hXeq 4
          have hb0 := qdig7_three_sub (m := m) (i₀ := i₀) (u' := u')
            (x := normU7 N (e x))
          have hb1 := qdig7_three_sub (m := m) (i₀ := i₀) (u' := u')
            (x := normU7 N (e (x + 2)))
          have hb2 := qdig7_three_sub (m := m) (i₀ := i₀) (u' := u')
            (x := normU7 N (e (x + 4)))
          rw [e0.2] at hb0
          rw [e2.2] at hb1
          rw [e4.2] at hb2
          have hh1 : ∃ b ∈ ({qdig7 m (lamP m i₀ 3 u' * normU7 N (e x)),
              qdig7 m (lamP m i₀ 3 u' * normU7 N (e (x + 2))),
              qdig7 m (lamP m i₀ 3 u' * normU7 N (e (x + 4)))} :
              Finset (ZMod 7)), b - 3 * x ∈ ({2, 3, 4} : Finset (ZMod 7)) := by
            obtain ⟨b', hb'⟩ := hit3_of_not_subset4
              (fun i' => h4 3 (by decide) i') (3 * x + 2)
            obtain ⟨hb'X, hb'mem⟩ := Finset.mem_inter.mp hb'
            rw [← hX3] at hb'X
            exact ⟨b', hb'X, s3_cycIv_sub_234 hb'mem⟩
          have hh2 : ∃ b ∈ ({qdig7 m (lamP m i₀ 3 u' * normU7 N (e x)),
              qdig7 m (lamP m i₀ 3 u' * normU7 N (e (x + 2))),
              qdig7 m (lamP m i₀ 3 u' * normU7 N (e (x + 4)))} :
              Finset (ZMod 7)), b - 3 * x ∈ ({3, 4, 5} : Finset (ZMod 7)) := by
            obtain ⟨b', hb'⟩ := hit3_of_not_subset4
              (fun i' => h4 3 (by decide) i') (3 * x + 3)
            obtain ⟨hb'X, hb'mem⟩ := Finset.mem_inter.mp hb'
            rw [← hX3] at hb'X
            exact ⟨b', hb'X, s3_cycIv_sub_345 hb'mem⟩
          have hc0 := qdig7_succ_sub (m := m) (i₀ := i₀) (j := 3) (u' := u')
            (x := normU7 N (e x)) ⟨by norm_num, by norm_num⟩
          have hc1 := qdig7_succ_sub (m := m) (i₀ := i₀) (j := 3) (u' := u')
            (x := normU7 N (e (x + 2))) ⟨by norm_num, by norm_num⟩
          have hc2 := qdig7_succ_sub (m := m) (i₀ := i₀) (j := 3) (u' := u')
            (x := normU7 N (e (x + 4))) ⟨by norm_num, by norm_num⟩
          rw [e0.2] at hc0
          rw [e2.2] at hc1
          rw [e4.2] at hc2
          rw [show (3 : ℕ) + 1 = 4 from rfl] at hc0 hc1 hc2
          obtain ⟨i4, hi4⟩ := prop3bx _ _ _ hb0 hb1 hb2 hh1 hh2 _ _ _
            hc0 hc1 hc2
          rw [hX4] at hi4
          exact absurd hi4 (h4 4 (by decide) i4)
    · -- |A_s| = 4: all units have residue `s`.
      have hS4 : S = U := by
        apply Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
        rw [hSc, hUcard]
      have hrs : ∀ d ∈ U, r d = s := by
        intro d hd
        have hdS : d ∈ S := by rw [hS4]; exact hd
        exact (Finset.mem_filter.mp hdS).2
      by_cases h5 : ∃ j ∈ Finset.Icc 1 5, ∃ i : ZMod 7, X j ⊆ cycIv i 5
      · obtain ⟨j, hj, i, hi⟩ := h5
        rw [Finset.mem_Icc] at hj
        obtain ⟨t, ht⟩ := exists_shift_avoid (le_refl 5) hi
        apply case4_finish hm him hj hu'nd hs0 t D hpos hle
        · intro d hdD hdν
          have hdU : d ∈ U := by
            have hdL : d ∈ level7 D 0 := Finset.mem_filter.mpr ⟨hdD, hdν⟩
            rwa [hU, hUdef] at hdL
          have hrs' : runit7 (normU7 (7 ^ (m + 1)) d) = s := hrs d hdU
          rw [hrs', mul_assoc, inv_mul_cancel₀ hs0, mul_one]
          have hqd : qdig7 m (lamP m i₀ j u' * normU7 N d) ∈ X j := by
            rw [hXj j]
            exact Finset.mem_image.mpr ⟨d, by rw [hS4]; exact hdU, rfl⟩
          have := ht (qdig7 m (lamP m i₀ j u' * normU7 N d) + t)
            (Finset.mem_image.mpr ⟨_, hqd, rfl⟩)
          simpa [bad06] using this
        · intro d hd h0' hlt
          exact hd5bound d hd h0' hlt j hj
      · push Not at h5
        have hhit1 : ∀ i : ZMod 7, (X 1 ∩ cycIv i 2).Nonempty :=
          fun i => hit2_of_not_subset5 (fun i' => h5 1 (by decide) i') i
        have hX1eq : X 1 = ({qdig7 m (lamP m i₀ 1 u' * normU7 N d1),
            qdig7 m (lamP m i₀ 1 u' * normU7 N d2),
            qdig7 m (lamP m i₀ 1 u' * normU7 N d3),
            qdig7 m (lamP m i₀ 1 u' * normU7 N d4)} : Finset (ZMod 7)) := by
          rw [hXj 1, hS4, hUdef]
          ext w
          simp only [Finset.mem_image, Finset.mem_insert, Finset.mem_singleton]
          constructor
          · rintro ⟨d, hd, rfl⟩
            rcases hd with rfl | rfl | rfl | rfl
            · exact Or.inl rfl
            · exact Or.inr (Or.inl rfl)
            · exact Or.inr (Or.inr (Or.inl rfl))
            · exact Or.inr (Or.inr (Or.inr rfl))
          · intro hw
            rcases hw with rfl | rfl | rfl | rfl
            · exact ⟨d1, Or.inl rfl, rfl⟩
            · exact ⟨d2, Or.inr (Or.inl rfl), rfl⟩
            · exact ⟨d3, Or.inr (Or.inr (Or.inl rfl)), rfl⟩
            · exact ⟨d4, Or.inr (Or.inr (Or.inr rfl)), rfl⟩
        obtain ⟨x, hx⟩ := shape4 (x0 := qdig7 m (lamP m i₀ 1 u' * normU7 N d1))
          (x1 := qdig7 m (lamP m i₀ 1 u' * normU7 N d2))
          (x2 := qdig7 m (lamP m i₀ 1 u' * normU7 N d3))
          (x3 := qdig7 m (lamP m i₀ 1 u' * normU7 N d4)) (by rwa [← hX1eq])
        have hex : ∀ w : ZMod 7, ∃ d : ℕ,
            w ∈ ({x, x + 2, x + 4, x + 6} : Finset (ZMod 7)) →
            d ∈ U ∧ qdig7 m (lamP m i₀ 1 u' * normU7 N d) = w := by
          intro w
          by_cases hw : w ∈ ({x, x + 2, x + 4, x + 6} : Finset (ZMod 7))
          · have hwX : w ∈ X 1 := by rwa [hX1eq, hx]
            obtain ⟨d, hd, hdq⟩ := Finset.mem_image.mp hwX
            exact ⟨d, fun _ => ⟨by rw [hS4] at hd; exact hd, hdq⟩⟩
          · exact ⟨0, fun h => absurd h hw⟩
        choose e he using hex
        have e0 := he x (Finset.mem_insert_self _ _)
        have e2 := he (x + 2) (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
        have e4 := he (x + 4) (Finset.mem_insert_of_mem
          (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))
        have e6 := he (x + 6) (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))))
        have hEU : ({e x, e (x + 2), e (x + 4), e (x + 6)} : Finset ℕ) = U := by
          apply Finset.eq_of_subset_of_card_le
          · intro w hw
            simp only [Finset.mem_insert, Finset.mem_singleton] at hw
            rcases hw with rfl | rfl | rfl | rfl
            exacts [e0.1, e2.1, e4.1, e6.1]
          · rw [hUcard]
            have himg : ({e x, e (x + 2), e (x + 4), e (x + 6)} : Finset ℕ).image
                (fun d => qdig7 m (lamP m i₀ 1 u' * normU7 N d)) =
                ({x, x + 2, x + 4, x + 6} : Finset (ZMod 7)) := by
              ext w
              simp only [Finset.mem_image, Finset.mem_insert, Finset.mem_singleton]
              constructor
              · rintro ⟨d, hd, rfl⟩
                rcases hd with rfl | rfl | rfl | rfl
                · rw [e0.2]; exact Or.inl rfl
                · rw [e2.2]; exact Or.inr (Or.inl rfl)
                · rw [e4.2]; exact Or.inr (Or.inr (Or.inl rfl))
                · rw [e6.2]; exact Or.inr (Or.inr (Or.inr rfl))
              · intro hw
                rcases hw with h | h | h | h
                · rw [h]; exact ⟨e x, Or.inl rfl, e0.2⟩
                · rw [h]; exact ⟨e (x + 2), Or.inr (Or.inl rfl), e2.2⟩
                · rw [h]; exact ⟨e (x + 4), Or.inr (Or.inr (Or.inl rfl)), e4.2⟩
                · rw [h]; exact ⟨e (x + 6), Or.inr (Or.inr (Or.inr rfl)), e6.2⟩
            have hinj : Function.Injective (· + x) := fun a b h => by
              simpa using congrArg (· + -x) h
            have himg2 : ({x, x + 2, x + 4, x + 6} : Finset (ZMod 7)) =
                Finset.image (· + x) ({0, 2, 4, 6} : Finset (ZMod 7)) := by
              ext w
              simp only [Finset.mem_insert, Finset.mem_singleton,
                Finset.mem_image]
              constructor
              · rintro (h | h | h | h)
                · rw [h]; exact ⟨0, by decide, zero_add x⟩
                · rw [h]; exact ⟨2, by decide, add_comm 2 x⟩
                · rw [h]; exact ⟨4, by decide, add_comm 4 x⟩
                · rw [h]; exact ⟨6, by decide, add_comm 6 x⟩
              · rintro ⟨c, hc, rfl⟩
                rcases hc with rfl | rfl | rfl | rfl <;> simp [add_comm]
            have hc4 : ({x, x + 2, x + 4, x + 6} : Finset (ZMod 7)).card = 4 := by
              rw [himg2, Finset.card_image_of_injective _ hinj]
              decide
            rw [← himg] at hc4
            have hle := Finset.card_image_le
              (s := {e x, e (x + 2), e (x + 4), e (x + 6)})
              (f := fun d => qdig7 m (lamP m i₀ 1 u' * normU7 N d))
            omega
        have hX3' : ({qdig7 m (lamP m i₀ 3 u' * normU7 N (e x)),
            qdig7 m (lamP m i₀ 3 u' * normU7 N (e (x + 2))),
            qdig7 m (lamP m i₀ 3 u' * normU7 N (e (x + 4))),
            qdig7 m (lamP m i₀ 3 u' * normU7 N (e (x + 6)))} : Finset (ZMod 7)) =
            ({e x, e (x + 2), e (x + 4), e (x + 6)} : Finset ℕ).image
              (fun d => qdig7 m (lamP m i₀ 3 u' * normU7 N d)) := by
          ext w
          simp only [Finset.mem_image, Finset.mem_insert, Finset.mem_singleton]
          constructor
          · rintro (rfl | rfl | rfl | rfl)
            · exact ⟨e x, Or.inl rfl, rfl⟩
            · exact ⟨e (x + 2), Or.inr (Or.inl rfl), rfl⟩
            · exact ⟨e (x + 4), Or.inr (Or.inr (Or.inl rfl)), rfl⟩
            · exact ⟨e (x + 6), Or.inr (Or.inr (Or.inr rfl)), rfl⟩
          · rintro ⟨d, hd, rfl⟩
            rcases hd with rfl | rfl | rfl | rfl
            · exact Or.inl rfl
            · exact Or.inr (Or.inl rfl)
            · exact Or.inr (Or.inr (Or.inl rfl))
            · exact Or.inr (Or.inr (Or.inr rfl))
        have hX3 : ({qdig7 m (lamP m i₀ 3 u' * normU7 N (e x)),
            qdig7 m (lamP m i₀ 3 u' * normU7 N (e (x + 2))),
            qdig7 m (lamP m i₀ 3 u' * normU7 N (e (x + 4))),
            qdig7 m (lamP m i₀ 3 u' * normU7 N (e (x + 6)))} : Finset (ZMod 7)) =
            X 3 := by
          rw [hX3', hEU, ← hS4, hXj 3]
        have hb0 := qdig7_three_sub (m := m) (i₀ := i₀) (u' := u')
          (x := normU7 N (e x))
        have hb1 := qdig7_three_sub (m := m) (i₀ := i₀) (u' := u')
          (x := normU7 N (e (x + 2)))
        have hb2 := qdig7_three_sub (m := m) (i₀ := i₀) (u' := u')
          (x := normU7 N (e (x + 4)))
        have hb3 := qdig7_three_sub (m := m) (i₀ := i₀) (u' := u')
          (x := normU7 N (e (x + 6)))
        rw [e0.2] at hb0
        rw [e2.2] at hb1
        rw [e4.2] at hb2
        rw [e6.2] at hb3
        have hhit : ∀ i : ZMod 7, (({qdig7 m (lamP m i₀ 3 u' * normU7 N (e x)),
            qdig7 m (lamP m i₀ 3 u' * normU7 N (e (x + 2))),
            qdig7 m (lamP m i₀ 3 u' * normU7 N (e (x + 4))),
            qdig7 m (lamP m i₀ 3 u' * normU7 N (e (x + 6)))} : Finset (ZMod 7)) ∩
            cycIv i 2).Nonempty := by
          rw [hX3]
          intro i
          exact hit2_of_not_subset5 (fun i' => h5 3 (by decide) i') i
        have hc0 := qdig7_succ_sub (m := m) (i₀ := i₀) (u' := u')
          (x := normU7 N (e x)) (j := 3) ⟨by norm_num, by norm_num⟩
        have hc1 := qdig7_succ_sub (m := m) (i₀ := i₀) (u' := u')
          (x := normU7 N (e (x + 2))) (j := 3) ⟨by norm_num, by norm_num⟩
        have hc2 := qdig7_succ_sub (m := m) (i₀ := i₀) (u' := u')
          (x := normU7 N (e (x + 4))) (j := 3) ⟨by norm_num, by norm_num⟩
        have hc3 := qdig7_succ_sub (m := m) (i₀ := i₀) (u' := u')
          (x := normU7 N (e (x + 6))) (j := 3) ⟨by norm_num, by norm_num⟩
        rw [e0.2] at hc0
        rw [e2.2] at hc1
        rw [e4.2] at hc2
        rw [e6.2] at hc3
        rw [show (3 : ℕ) + 1 = 4 from rfl] at hc0 hc1 hc2 hc3
        obtain ⟨i4, hi4⟩ := prop4x _ _ _ _ hb0 hb1 hb2 hb3 hhit _ _ _ _
          hc0 hc1 hc2 hc3
        have hX4' : ({qdig7 m (lamP m i₀ 4 u' * normU7 N (e x)),
            qdig7 m (lamP m i₀ 4 u' * normU7 N (e (x + 2))),
            qdig7 m (lamP m i₀ 4 u' * normU7 N (e (x + 4))),
            qdig7 m (lamP m i₀ 4 u' * normU7 N (e (x + 6)))} : Finset (ZMod 7)) =
            ({e x, e (x + 2), e (x + 4), e (x + 6)} : Finset ℕ).image
              (fun d => qdig7 m (lamP m i₀ 4 u' * normU7 N d)) := by
          ext w
          simp only [Finset.mem_image, Finset.mem_insert, Finset.mem_singleton]
          constructor
          · rintro (rfl | rfl | rfl | rfl)
            · exact ⟨e x, Or.inl rfl, rfl⟩
            · exact ⟨e (x + 2), Or.inr (Or.inl rfl), rfl⟩
            · exact ⟨e (x + 4), Or.inr (Or.inr (Or.inl rfl)), rfl⟩
            · exact ⟨e (x + 6), Or.inr (Or.inr (Or.inr rfl)), rfl⟩
          · rintro ⟨d, hd, rfl⟩
            rcases hd with rfl | rfl | rfl | rfl
            · exact Or.inl rfl
            · exact Or.inr (Or.inl rfl)
            · exact Or.inr (Or.inr (Or.inl rfl))
            · exact Or.inr (Or.inr (Or.inr rfl))
        have hX4 : ({qdig7 m (lamP m i₀ 4 u' * normU7 N (e x)),
            qdig7 m (lamP m i₀ 4 u' * normU7 N (e (x + 2))),
            qdig7 m (lamP m i₀ 4 u' * normU7 N (e (x + 4))),
            qdig7 m (lamP m i₀ 4 u' * normU7 N (e (x + 6)))} : Finset (ZMod 7)) =
            X 4 := by
          rw [hX4', hEU, ← hS4, hXj 4]
        rw [hX4] at hi4
        obtain ⟨t, ht⟩ := exists_shift_avoid (le_refl 5) hi4
        refine case4_finish (j := 4) hm him ⟨by norm_num, by norm_num⟩
          hu'nd hs0 t D hpos hle ?_ ?_
        · intro d hdD hdν
          have hdU : d ∈ U := by
            have hdL : d ∈ level7 D 0 := Finset.mem_filter.mpr ⟨hdD, hdν⟩
            rwa [hU, hUdef] at hdL
          have hrs' : runit7 (normU7 (7 ^ (m + 1)) d) = s := hrs d hdU
          rw [hrs', mul_assoc, inv_mul_cancel₀ hs0, mul_one]
          have hqd : qdig7 m (lamP m i₀ 4 u' * normU7 N d) ∈ X 4 := by
            rw [hXj 4]
            exact Finset.mem_image.mpr ⟨d, by rw [hS4]; exact hdU, rfl⟩
          have := ht (qdig7 m (lamP m i₀ 4 u' * normU7 N d) + t)
            (Finset.mem_image.mpr ⟨_, hqd, rfl⟩)
          simpa [bad06] using this
        · intro d hd h0' hlt
          exact hd5bound d hd h0' hlt 4 ⟨by norm_num, by norm_num⟩
  by_cases hempty : inter = ∅
  · refine main m 1 hm le_rfl (by norm_num) ?_
    intro d hd h0' hlt j hj
    exfalso
    have hdI : d ∈ inter := Finset.mem_filter.mpr ⟨hd, h0', hlt⟩
    rw [hempty] at hdI
    exact Finset.notMem_empty d hdI
  · have hcard1 : inter.card = 1 := by
      rcases Nat.eq_zero_or_pos inter.card with h | h
      · exact absurd (Finset.card_eq_zero.mp h) hempty
      · omega
    obtain ⟨d5, hd5eq⟩ := Finset.card_eq_one.mp hcard1
    have hd5mem : d5 ∈ D ∧ 0 < padicValNat 7 d5 ∧ padicValNat 7 d5 < m := by
      have hdI : d5 ∈ inter := by
        rw [hd5eq]; exact Finset.mem_singleton_self _
      obtain ⟨h1, h2, h3⟩ := Finset.mem_filter.mp hdI
      exact ⟨h1, h2, h3⟩
    set i₀ := padicValNat 7 d5 with hi₀
    set u := Nat.divMaxPow d5 7 with hu
    set nn := 7 ^ (m + 1 - i₀) with hnn
    set u' := ((u : ZMod nn)⁻¹).val with hu'
    have hd5dec : d5 = u * 7 ^ i₀ :=
      (Nat.divMaxPow_mul_pow_padicValNat 7 d5).symm
    have hund : ¬ 7 ∣ u :=
      Nat.not_dvd_divMaxPow (by norm_num) (Nat.ne_of_gt (hpos d5 hd5mem.1))
    have hcop : Nat.Coprime u nn := by
      rw [hnn]
      exact (Nat.coprime_pow_right_iff (by omega) u 7).mpr
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_seven).mpr hund).symm
    have huu' : u * u' ≡ 1 [MOD nn] := by
      rw [hu']
      have h := ZMod.mul_val_inv hcop
      rw [← Nat.cast_mul, ← Nat.cast_one] at h
      exact (ZMod.natCast_eq_natCast_iff _ _ _).mp h
    have hu'nd : ¬ 7 ∣ u' := by
      intro h7u'
      have hmod7 : u * u' ≡ 1 [MOD 7] := by
        have hd7 : 7 ∣ nn := by
          rw [hnn]
          exact dvd_pow_self 7 (by omega)
        exact Nat.ModEq.of_dvd hd7 huu'
      rw [Nat.ModEq] at hmod7
      have h0 : (u * u') % 7 = 0 :=
        Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_right h7u' u)
      omega
    have hi0 : 0 < i₀ := by rw [hi₀]; exact hd5mem.2.1
    have him : i₀ ≤ m := by rw [hi₀]; exact le_of_lt hd5mem.2.2
    refine main i₀ u' hi0 him hu'nd ?_
    intro d hd h0' hlt j hj
    have hdd5 : d = d5 := by
      have hdI : d ∈ inter := Finset.mem_filter.mpr ⟨hd, h0', hlt⟩
      rw [hd5eq] at hdI
      exact Finset.mem_singleton.mp hdI
    rw [hdd5, hd5dec]
    exact eq8_absModN hi0 him hj huu'
