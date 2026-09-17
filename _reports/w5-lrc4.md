# W5 — LRC4: Lonely Runner integer case (≤3 speeds, threshold 1/4) + rational corollary

Agent: W5 subagent. Started: (session start). Status: **in progress**.

## Task
- `Research07/LRC4/IntCase.lean`: `theorem lrc4_int (D : Finset ℕ) (hpos : ∀ d ∈ D, 0 < d) (hcard : D.card ≤ 3) : ∃ t : ℝ, 0 < t ∧ ∀ d ∈ D, (1/4 : ℝ) ≤ circ (t * d)`
- `Research07/LRC4/Main.lean`: `theorem lrc4_rel_rat (w : Fin 3 → ℚ) (hw : ∀ i, w i ≠ 0) : ∃ t : ℝ, 0 < t ∧ ∀ i, (1/4 : ℝ) ≤ circ (t * w i)`
- `circ` defined in `Research07/LRC3/Circ.lean`.
- Rules: no sorry/admit/native_decide/unsafe/new axioms.

## Progress log

### [T0] Setup
- Created this report. `_reports/` did not exist; created.
- Next: read `LRC3/Circ.lean`, `LRC5/IntCase.lean` (pad-to-card + gcd bridge), `LRC5/Main.lean` (clear denominators), `Research07.lean`/`Basic.lean` import wiring.
