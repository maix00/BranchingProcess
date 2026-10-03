import Probability.BranchingRandomWalk.Step.PointMeasure
import Probability.BranchingRandomWalk.Step.PointProcess

noncomputable section

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

example (f : Unit → Option Empty) :
    Measure.IsIntegerValued (Measure.iOptionDiracSum f) :=
  Measure.iOptionDiracSum_isIntegerValued f

example : (Measure.iOptionDiracSum (fun _ : Fin 2 => some true)) {true} = 2 := by
  rw [Measure.iOptionDiracSum_apply _ (measurableSet_singleton true)]
  simp

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

private def noChildren : StepPresentation Unit Empty Empty where
  present := fun i _ => nomatch i
  measurable_present := by intro i; nomatch i
  displace := fun i _ => nomatch i
  measurable_displace := by intro i; nomatch i

example : ProbabilityTheory.PointProcess Unit Empty ∅ :=
  noChildren.toPointProcess ∅ (by intro ω s hs; cases hs)
