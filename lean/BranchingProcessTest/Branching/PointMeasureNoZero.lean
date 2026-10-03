import Combinatorics.BranchingWalk.Step.PointMeasure

/-!
# Optional point measures need no zero mark

These examples pin down that the mark type itself needs no `Zero` value: an
absent optional slot contributes the zero *measure*.
-/

open MeasureTheory
open Combinatorics.Branching

example : Measurable (Measure.iOptionDiracSum :
    (Unit → Option Empty) → Measure Empty) :=
  Measure.iOptionDiracSum_measurable

example : Measurable (stepPointMeasure : Step Unit Empty → Measure Empty) :=
  stepPointMeasure_measurable
