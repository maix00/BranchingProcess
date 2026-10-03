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

private def emptyConfiguration : Combinatorics.Branching.Step Unit PUnit :=
  fun _ => none

private noncomputable def emptyOffspringLaw :
    ProbabilityTheory.BranchingProcess.OffspringLaw Unit :=
  Measure.dirac emptyConfiguration |>.toProbabilityMeasure

example : ProbabilityMeasure (Combinatorics.Branching.Process Unit) :=
  ProbabilityTheory.BranchingProcess.GaltonWatson.law emptyOffspringLaw

example (μ : ProbabilityTheory.BranchingProcess.OffspringLaw Unit) :
    iIndepFun
      (fun u (field : Combinatorics.Branching.StepField Unit PUnit) => field u)
      (μ.fieldLaw : Measure (Combinatorics.Branching.StepField Unit PUnit)) :=
  ProbabilityTheory.BranchingProcess.GaltonWatson.field_independent μ

example (μ : ProbabilityTheory.BranchingProcess.OffspringLaw Unit) :
    ((ProbabilityTheory.BranchingProcess.GaltonWatson.law μ :
      ProbabilityMeasure (Combinatorics.Branching.Process Unit)) :
      Measure (Combinatorics.Branching.Process Unit)).map
        (fun β => β.step PUnit.unit) =
      (μ.fieldLaw : Measure (Combinatorics.Branching.StepField Unit PUnit)) :=
  ProbabilityTheory.BranchingProcess.GaltonWatson.law_stepField μ

example (β : Combinatorics.Branching.Process Unit) : β.generationSize 0 = 1 :=
  ProbabilityTheory.BranchingProcess.GaltonWatson.generationSize_zero β

example (β : Combinatorics.Branching.Process Unit) {n m : ℕ} (hnm : n ≤ m)
    (hzero : β.generationSize n = 0) : β.generationSize m = 0 :=
  Combinatorics.Branching.RootIndexed.BranchingWalk.generationSize_eq_zero_of_le
    β hnm hzero
