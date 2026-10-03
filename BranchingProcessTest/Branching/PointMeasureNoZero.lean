import Probability.BranchingRandomWalk.Step.PointMeasure

/-!
# Optional point measures need no zero mark

These examples pin down that the mark type itself needs no `Zero` value: an
absent optional slot contributes the zero *measure*.
-/

open MeasureTheory
open Combinatorics.Branching
open ProbabilityTheory.BranchingRandomWalk

example : Measurable (Measure.iOptionDiracSum :
    (Unit → Option Empty) → Measure Empty) :=
  Measure.iOptionDiracSum_measurable

example : Measurable (stepPointMeasure : Step Unit Empty → Measure Empty) :=
  stepPointMeasure_measurable

example : Measurable (fun _ : Unit => (fun _ : Unit => none : Step Unit Empty)) :=
  measurable_const

example (S : Unit → Step Unit Empty) (hS : Measurable S) :
    Measurable (pointMeasureOf S) :=
  pointMeasureOf_measurable S hS

private def absentFalse : StepPresentation Unit Unit Bool where
  present := fun _ _ => false
  measurable_present := fun _ => measurable_const
  displace := fun _ _ => false
  measurable_displace := fun _ => measurable_const

private def absentTrue : StepPresentation Unit Unit Bool where
  present := fun _ _ => false
  measurable_present := fun _ => measurable_const
  displace := fun _ _ => true
  measurable_displace := fun _ => measurable_const

example : absentFalse.toFun = absentTrue.toFun := by
  funext ω i
  simp [absentFalse, absentTrue, StepPresentation.toFun]

example : absentFalse ≠ absentTrue := by
  intro h
  have hdisplace := congrArg
    (fun S : StepPresentation Unit Unit Bool => S.displace Unit.unit Unit.unit) h
  change false = true at hdisplace
  cases hdisplace
