/-
Copyright (c) 2026 Research07 contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Research07 contributors
-/
import Research07.M3.Main
import Research07.LRC4.Main
import Research07.LRC6.Main

/-!
# Audit

Machine-level acceptance check for the formalization: every exported theorem
must depend only on Lean's three standard axioms
`[propext, Classical.choice, Quot.sound]`. Anything else (`sorryAx` from a
leftover `sorry`, `Lean.ofReduceBool` from `native_decide`, custom axioms)
shows up here.

Coverage: LRC n=3 (real), LRC n=4 (integer + rational wrappers),
LRC n=5 (integer + rational + **full real speeds** via BHK),
LRC n=6 (integer + rational wrappers via Renault's case split), and every
load-bearing M3 intermediate theorem.
-/

-- ============ headline theorems ============
#print axioms lonely_runner_three
#print axioms lrc4_int
#print axioms lrc4_rel_rat
#print axioms lrc4_rat_finset
#print axioms lrc5_int
#print axioms lrc5_rel_rat
#print axioms lonely_runner_five_rat
#print axioms lrc5_rel_real
#print axioms lonely_runner_five
#print axioms lrc6_int
#print axioms lrc6_rel_rat
#print axioms lonely_runner_six_rat
#print axioms prop3_1
#print axioms prop4_1
#print axioms prop5_4
#print axioms prop6_6

-- ============ M3 intermediate layer ============
#print axioms SimDirichlet.exists_delta_lt_inv
#print axioms SimDirichlet.exists_delta_lt
#print axioms kerSpan_eq_span_rat
#print axioms exists_pos_rat_kerSpan
#print axioms exists_kerSpanRat_not_parallel
#print axioms kernel_coords_linearIndependent_of_basis
#print axioms subtorusMap_range_eq_annihilator
#print axioms flow_orbit_dense
#print axioms orbit_dense_annihilator
#print axioms lrc5_real_of_irrational_ratio

-- ============ supporting APIs used downstream ============
#print axioms circ_ge_quarter_fract
#print axioms circ_ge_quarter_iff
#print axioms two_moving
#print axioms dist_unitAddCircle_eq_circ
