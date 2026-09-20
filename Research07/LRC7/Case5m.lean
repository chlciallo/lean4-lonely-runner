import Research07.LRC7.Case5mC61
import Research07.LRC7.Case5mC62
import Research07.LRC7.Case5mC63
import Research07.LRC7.Case5mC64
import Research07.LRC7.Case5mC65
import Research07.LRC7.Case66
import Research07.LRC7.Case5mTop
import Research07.LRC7.Case5mL10

/-!
# §6 aggregation — the `hc6` leaf for `lrc7_int`

`lrc7_hc6` instantiates `lrc7_hc6_aux` (Case5mTop) with the six case
theorems `case61 … case66` (paper §6.1–§6.6, one file each), producing the
`IntCase`-consumable leaf:

  `|A| = 5` units + one top-level element `d6` (level `m > 1`)
  ⇒ `∃ lam > 0, ∀ d ∈ A ∪ {d6}, 7^m ≤ |lam·d|_{7^{m+1}}`.
-/

/-- The `|D₇(0)| = 5`, `m > 1` leaf: five units plus one level-`m`
element admit a positive multiplier pushing every element's `7^{m+1}`-mod
distance to at least `7^m`.  Assembled from the six §6 case theorems via
`lrc7_hc6_aux` (Case5mTop). -/
theorem lrc7_hc6 {m : ℕ} (A : Finset ℕ) (hA : A.card = 5)
    (hpos : ∀ d ∈ A, 0 < d) (hnd : ∀ d ∈ A, ¬ 7 ∣ d)
    (d6 : ℕ) (hd6 : padicValNat 7 d6 = m) (hd6pos : 0 < d6)
    (hm : 1 < m) :
    ∃ lam : ℕ, 0 < lam ∧
      ∀ d ∈ A ∪ {d6}, 7 ^ m ≤ absModN (lam * d) (7 ^ (m + 1)) := by
  refine lrc7_hc6_aux ?_ ?_ ?_ ?_ ?_ ?_ A hA hpos hnd d6 hd6 hd6pos hm
  · exact fun {X : Finset ℕ} (hX : X.card = 5) (hXp : ∀ d ∈ X, 0 < d)
        (hXu : ∀ d ∈ X, padicValNat 7 d = 0) {s : ZMod 7}
        (hs : s ∈ ({1, 2, 4} : Finset (ZMod 7)))
        (hXc : ∀ d ∈ X, runit7 d = s) =>
      case61 hm hX hXp hXu hs hXc lemma10 lemma9_ii
  · exact case62 hm
  · exact case63 hm
  · exact case64 hm
  · exact case65 hm
  · exact fun {A1 A2 A4 : Finset ℕ} (hA1 : A1.card = 2) (hA2 : A2.card = 2)
        (hA4 : A4.card = 1) (hpos' : ∀ d ∈ A1 ∪ A2 ∪ A4, 0 < d)
        (hunit' : ∀ d ∈ A1 ∪ A2 ∪ A4, padicValNat 7 d = 0)
        {s : ZMod 7} (hs : s ∈ ({1, 2, 4} : Finset (ZMod 7)))
        (h1 : ∀ d ∈ A1, runit7 d = s) (h2 : ∀ d ∈ A2, runit7 d = 2 * s)
        (h4 : ∀ d ∈ A4, runit7 d = 4 * s) =>
      LRC7Case66.case66 hm hA1 hA2 hA4 hpos' hunit' hs h1 h2 h4
        (LRC7Case66.case66_top hm)
