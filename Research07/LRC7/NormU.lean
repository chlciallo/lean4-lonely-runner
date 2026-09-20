import Research07.LRC7.Discrete

/-!
# Sign-normalized representatives `normU7`

The paper normalizes residues to `{1, 2, 4}` by replacing an element `d`
by `N - d % N` when `d % 7 ∈ {3, 5, 6}` (Barajas–Serra's "we may assume
the residues are in `{1,2,4}`").  This file provides the normalization
function and its invariants: `absModN` under any multiplier is unchanged,
positivity/`ν = 0` is preserved for units, and the unit residue lands in
`{1, 2, 4}`.

Mirrors `LRC5/IntCase.lean`'s `normU5`/`absModN_mul_flip`.
-/

/-- `absModN` agrees with `valMinAbs`. -/
theorem absModN_eq_natAbs {x N : ℕ} (hN : 0 < N) :
    absModN x N = ((x : ZMod N).valMinAbs).natAbs := by
  haveI : NeZero N := ⟨hN.ne'⟩
  unfold absModN
  rw [ZMod.valMinAbs_natAbs_eq_min, ZMod.val_natCast]

/-- `absModN` is invariant under negating the residue. -/
theorem absModN_mul_flip {lam d N : ℕ} (hN : 0 < N) :
    absModN (lam * (N - d % N)) N = absModN (lam * d) N := by
  rw [absModN_eq_natAbs hN, absModN_eq_natAbs hN]
  have hcast : ((lam * (N - d % N) : ℕ) : ZMod N) =
      -((lam * d : ℕ) : ZMod N) := by
    have hle : d % N ≤ N := (Nat.mod_lt d hN).le
    rw [Nat.cast_mul, Nat.cast_sub hle, ZMod.natCast_self, zero_sub,
      ZMod.natCast_mod, mul_neg, ← Nat.cast_mul]
  rw [hcast, ZMod.natAbs_valMinAbs_neg]

/-- For `d ≠ 0`, `ν(d) = 0` iff `7 ∤ d`. -/
theorem padic7_eq_zero_iff {d : ℕ} (hd : d ≠ 0) :
    padicValNat 7 d = 0 ↔ ¬ 7 ∣ d := by
  have h : (7 : ℕ) ∣ d ↔ 1 ≤ padicValNat 7 d := by
    have h' := Nat.pow_dvd_iff_le_padicValNat (p := 7) (n := d) (k := 1)
      (by norm_num) hd
    simpa using h'
  omega

/-- Sign-normalized representative of `d` modulo `N`: keeps `d` when its
mod-7 residue is in `{1,2,4}`, else takes the complement `N - d % N`. -/
def normU7 (N d : ℕ) : ℕ := if d % 7 ∈ ({1, 2, 4} : Finset ℕ) then d else N - d % N

/-- `normU7` preserves `absModN` under any multiplier. -/
theorem normU7_absModN {lam d N : ℕ} (hN : 0 < N) :
    absModN (lam * normU7 N d) N = absModN (lam * d) N := by
  unfold normU7
  split_ifs with _
  · rfl
  · exact absModN_mul_flip hN

/-- The normalized representative is positive when `d % N ≠ 0`. -/
theorem normU7_pos {d N : ℕ} (hN : 0 < N) (hd : d % N ≠ 0) :
    0 < normU7 N d := by
  unfold normU7
  split_ifs with _
  · exact Nat.pos_of_ne_zero (fun h => hd (by simp [h]))
  · exact Nat.sub_pos_of_lt (Nat.mod_lt d hN)

/-- For a unit `d` (`7 ∤ d`), the normalized representative is still a unit. -/
theorem normU7_not_dvd {d N : ℕ} (hN : 0 < N) (h7 : 7 ∣ N) (hd : ¬ 7 ∣ d) :
    ¬ 7 ∣ normU7 N d := by
  unfold normU7
  split_ifs with hmem
  · exact hd
  · intro hcon
    have hle : d % N ≤ N := (Nat.mod_lt d hN).le
    have h1 : 7 ∣ d % N := by
      have h2 := Nat.dvd_sub h7 hcon
      rwa [Nat.sub_sub_self hle] at h2
    have hme : d % N ≡ d [MOD 7] := Nat.ModEq.of_dvd h7 (Nat.mod_modEq d N)
    exact hd (Nat.dvd_of_mod_eq_zero (hme ▸ Nat.mod_eq_zero_of_dvd h1))

/-- For a unit `d`, the normalized representative has `padicValNat 0`. -/
theorem normU7_padic {d N : ℕ} (hN : 0 < N) (h7 : 7 ∣ N) (hd : ¬ 7 ∣ d) :
    padicValNat 7 (normU7 N d) = 0 := by
  have hnd : ¬ 7 ∣ normU7 N d := normU7_not_dvd hN h7 hd
  have hn0 : normU7 N d ≠ 0 := fun h => hnd (h.symm ▸ dvd_zero 7)
  exact (padic7_eq_zero_iff hn0).mpr hnd

/-- For a unit `d`, the normalized representative's `runit7` lies in
`{1, 2, 4}` (when `7 ∣ N`). -/
theorem normU7_runit {d N : ℕ} (hN : 0 < N) (h7 : 7 ∣ N) (hd : ¬ 7 ∣ d) :
    runit7 (normU7 N d) ∈ ({1, 2, 4} : Finset (ZMod 7)) := by
  have hd0 : d % 7 ≠ 0 := fun h0 => hd (Nat.dvd_of_mod_eq_zero h0)
  have hdlt : d % 7 < 7 := Nat.mod_lt d (by norm_num)
  have hcast_d : ((d : ℕ) : ZMod 7) = ((d % 7 : ℕ) : ZMod 7) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mpr (Nat.mod_modEq d 7).symm
  have hd0' : d ≠ 0 := fun h => hd (h.symm ▸ dvd_zero 7)
  unfold normU7
  split_ifs with hmem
  · have hν : padicValNat 7 d = 0 := (padic7_eq_zero_iff hd0').mpr hd
    unfold runit7
    rw [hν, pow_zero, Nat.div_one, hcast_d]
    interval_cases (d % 7) <;> first | decide | simp_all
  · have hnd : ¬ 7 ∣ (N - d % N) := by
      have h' := normU7_not_dvd hN h7 hd
      unfold normU7 at h'
      rwa [if_neg hmem] at h' 
    have hν : padicValNat 7 (N - d % N) = 0 := by
      have hn0 : N - d % N ≠ 0 := fun h => hnd (h.symm ▸ dvd_zero 7)
      exact (padic7_eq_zero_iff hn0).mpr hnd
    unfold runit7
    rw [hν, pow_zero, Nat.div_one]
    have hN0 : ((N : ℕ) : ZMod 7) = 0 := (ZMod.natCast_eq_zero_iff N 7).mpr h7
    have hdN : ((d % N : ℕ) : ZMod 7) = ((d : ℕ) : ZMod 7) :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mpr
        (Nat.ModEq.of_dvd h7 (Nat.mod_modEq d N))
    have hle : d % N ≤ N := (Nat.mod_lt d hN).le
    rw [Nat.cast_sub hle, hN0, hdN, hcast_d, zero_sub]
    interval_cases (d % 7) <;> first | decide | simp_all

