module

public import Probability.BranchingRandomWalk.Step.Presentation

@[expose] public section

/-!
# Constructors for random branching steps

This file supplies generic constructors from coordinate random variables.  It
does not impose a distribution on those coordinates.
-/

namespace ProbabilityTheory.BranchingRandomWalk

/-- Assemble an everywhere-present random step from an indexed family of
measurable displacement random variables. -/
def StepPresentation.full
    {Ω ι X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (D : ι → StepPresentationDisplace Ω X) (hD : ∀ i, Measurable (D i)) : StepPresentation Ω ι X where
  present _ _ := true
  measurable_present _ := measurable_const
  displace := D
  measurable_displace := hD

@[simp] theorem StepPresentation.full_present
    {Ω ι X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (D : ι → StepPresentationDisplace Ω X) (hD : ∀ i, Measurable (D i))
    (i : ι) (ω : Ω) :
    (StepPresentation.full D hD).present i ω = true := rfl

@[simp] theorem StepPresentation.full_displace
    {Ω ι X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (D : ι → StepPresentationDisplace Ω X) (hD : ∀ i, Measurable (D i))
    (i : ι) :
    (StepPresentation.full D hD).displace i = D i := rfl

@[simp] theorem StepPresentation.full_apply
    {Ω ι X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (D : ι → StepPresentationDisplace Ω X) (hD : ∀ i, Measurable (D i))
    (ω : Ω) (i : ι) :
    StepPresentation.full D hD ω i = some (D i ω) := by
  simp [StepPresentation.toFun]

end ProbabilityTheory.BranchingRandomWalk
