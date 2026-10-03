import Probability.BranchingProcess.GaltonWatson.BranchingProperty
import Probability.BranchingProcess.Offspring.PointMeasure
import Probability.BranchingRandomWalk.Genealogy.GaltonWatson
import Combinatorics.BranchingWalk.StepField
import Mathlib.Probability.Independence.InfinitePi

noncomputable section

/-!
# Galton--Watson law interface checks

The general presampled law accepts an offspring configuration law directly,
allows an all-absent offspring configuration, and inherits the shared
generation-size observation.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

private def emptyConfiguration : Combinatorics.Branching.Step Unit PUnit.{1} :=
  fun _ => none

private noncomputable def emptyOffspringLaw :
    ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw Unit PUnit.{1} :=
  Measure.dirac emptyConfiguration |>.toProbabilityMeasure

example : ProbabilityMeasure (Combinatorics.Branching.Process Unit) :=
  ProbabilityTheory.BranchingProcess.GaltonWatson.law emptyOffspringLaw

example (μ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw Unit PUnit.{1}) :
    iIndepFun
      (fun u (field : Combinatorics.Branching.StepField Unit PUnit.{1}) => field u)
      (μ.fieldLaw : Measure (Combinatorics.Branching.StepField Unit PUnit.{1})) :=
  ProbabilityTheory.BranchingProcess.GaltonWatson.field_independent μ

example (μ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw Unit PUnit.{1}) :
    ((ProbabilityTheory.BranchingProcess.GaltonWatson.law μ :
      ProbabilityMeasure (Combinatorics.Branching.Process Unit)) :
      Measure (Combinatorics.Branching.Process Unit)).map
        (fun β => β.step PUnit.unit) =
      (μ.fieldLaw : Measure (Combinatorics.Branching.StepField Unit PUnit.{1})) :=
  ProbabilityTheory.BranchingProcess.GaltonWatson.law_stepField μ

example (β : Combinatorics.Branching.Process Unit) : β.generationSize 0 = 1 :=
  Combinatorics.Branching.RootIndexed.BranchingWalk.generationSize_zero β

example (β : Combinatorics.Branching.Process Unit) {n m : ℕ} (hnm : n ≤ m)
    (hzero : β.generationSize n = 0) : β.generationSize m = 0 :=
  Combinatorics.Branching.RootIndexed.BranchingWalk.generationSize_eq_zero_of_le
    β hnm hzero

example {ι Mark : Type*} [MeasurableSpace Mark]
    (μ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw ι Mark)
    (u : Combinatorics.UlamHarris.TreeNode ι) :
    (μ.fieldLaw : Measure (Combinatorics.Branching.StepField ι Mark)).map
        (fun field => field u) =
      (μ : Measure (Combinatorics.Branching.Step ι Mark)) :=
  ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw.fieldLaw_coordinate μ u

example {ι Mark : Type*} [Countable ι] [MeasurableSpace Mark]
    (μ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw ι Mark) :
    ProbabilityMeasure (Measure Mark) :=
  μ.pointMeasureLaw

example {ι Mark Mark' : Type*} [Countable ι]
    [MeasurableSpace Mark] [MeasurableSpace Mark']
    (μ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw ι Mark)
    (f : Mark → Mark') (hf : Measurable f) :
    (μ.mapMarks f hf).pointMeasureLaw =
      μ.pointMeasureLaw.map (Measure.map f) :=
  ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw.pointMeasureLaw_mapMarks
    μ f hf

example {ι Mark Mark' : Type*} [MeasurableSpace Mark] [MeasurableSpace Mark']
    (μ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw ι Mark)
    (f : Mark → Mark') (hf : Measurable f) :
    (μ.mapMarks f hf).fieldLaw =
      (μ.fieldLaw).map (Combinatorics.Branching.StepField.map f) :=
  ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw.fieldLaw_mapMarks
    μ f hf

example {ι Mark : Type*} [MeasurableSpace Mark]
    (ξ : Combinatorics.Branching.Step ι Mark) :
    Combinatorics.Branching.stepPointMeasure ξ Set.univ =
      (ξ.childCount : ℝ≥0∞) :=
  Combinatorics.Branching.stepPointMeasure_univ ξ
