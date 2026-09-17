import Mathlib

open UnitAddTorus MeasureTheory Measure

example : BorelSpace (UnitAddTorus (Fin 3)) := inferInstance
example : IsAddHaarMeasure (volume : Measure (UnitAddTorus (Fin 3))) := inferInstance
example : (volume : Measure (UnitAddTorus (Fin 3))).InnerRegular := inferInstance
example : IsFiniteMeasure (volume : Measure (UnitAddTorus (Fin 3))) := inferInstance
example : NeZero (volume : Measure (UnitAddTorus (Fin 3))) := inferInstance
example : SecondCountableTopology (UnitAddTorus (Fin 3)) := inferInstance

example {ι : Type*} [Fintype ι] (a : UnitAddTorus ι) :
    Ergodic (a + ·) (volume : Measure (UnitAddTorus ι)) ↔
      DenseRange (· • a : ℤ → UnitAddTorus ι) :=
  ergodic_add_left_iff_denseRange_zsmul volume
