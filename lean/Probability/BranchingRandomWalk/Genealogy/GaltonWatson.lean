module

public import Probability.BranchingProcess.GaltonWatson.Generation
public import Probability.BranchingRandomWalk.Step.Map

/-!
# Forgetting marks to obtain a Galton--Watson law

This is the marked-walk adapter only. The tree-valued law and generation
observations are defined in `Probability.BranchingProcess.GaltonWatson` from
an offspring configuration law.
-/

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk

open MeasureTheory

/-- Forget the spatial marks of a random step and use the resulting offspring
configuration law to construct its Galton--Watson genealogy. -/
noncomputable def StepPresentation.toGaltonWatsonLaw
    {Ω ι X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (S : StepPresentation Ω ι X) (P : Measure Ω) [IsProbabilityMeasure P] :
    ProbabilityMeasure (Combinatorics.Branching.Process ι) :=
  ProbabilityTheory.BranchingProcess.GaltonWatson.law
    ((S.unmarkedLaw P).toProbabilityMeasure)

end ProbabilityTheory.BranchingRandomWalk

end
