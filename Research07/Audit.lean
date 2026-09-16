/-
Copyright (c) 2026 Research07 contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Research07 contributors
-/
import Research07.LRC3.Main

/-!
# Audit

Machine-level acceptance check for the formalization: the main theorem must
depend only on Lean's three standard axioms. Anything else (e.g. `sorryAx` from
a leftover `sorry`, or `Lean.ofReduceBool` from `native_decide`) shows up here.
-/

#print axioms lonely_runner_three
