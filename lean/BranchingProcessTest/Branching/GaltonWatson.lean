import Probability.BranchingProcess.GaltonWatson.BranchingProperty
import Probability.BranchingRandomWalk.Genealogy.GaltonWatson
import Mathlib.Probability.Independence.InfinitePi

noncomputable section

/-!
# Galton--Watson law interface checks

The general tree law accepts an offspring configuration law directly, allows
an all-absent offspring configuration, and inherits the shared generation
size observation.
-/

open MeasureTheory ProbabilityTheory

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
  ProbabilityTheory.BranchingProcess.GaltonWatson.generationSize_zero β

example (β : Combinatorics.Branching.Process Unit) {n m : ℕ} (hnm : n ≤ m)
    (hzero : β.generationSize n = 0) : β.generationSize m = 0 :=
  Combinatorics.Branching.RootIndexed.BranchingWalk.generationSize_eq_zero_of_le
    β hnm hzero
