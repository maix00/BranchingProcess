import Probability.BranchingRandomWalk.Step.Basic

/-!
# Constructors for random branching steps

This file supplies generic constructors from coordinate random variables.  It
does not impose a distribution on those coordinates.
-/

namespace ProbabilityTheory.BranchingRandomWalk

/-- Assemble an everywhere-present random step from an indexed family of
measurable displacement random variables. -/
def Step.full
    {Ω ι X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (D : ι → StepDisplace Ω X) (hD : ∀ i, Measurable (D i)) : Step Ω ι X where
  present _ _ := true
  measurable_present _ := measurable_const
  displace := D
  measurable_displace := hD

@[simp] theorem Step.full_present
    {Ω ι X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (D : ι → StepDisplace Ω X) (hD : ∀ i, Measurable (D i))
    (i : ι) (ω : Ω) :
    (Step.full D hD).present i ω = true := rfl

@[simp] theorem Step.full_displace
    {Ω ι X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (D : ι → StepDisplace Ω X) (hD : ∀ i, Measurable (D i))
    (i : ι) :
    (Step.full D hD).displace i = D i := rfl

@[simp] theorem Step.full_apply
    {Ω ι X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (D : ι → StepDisplace Ω X) (hD : ∀ i, Measurable (D i))
    (ω : Ω) (i : ι) :
    Step.full D hD ω i = some (D i ω) := by
  simp [Step.toFun]

end ProbabilityTheory.BranchingRandomWalk
