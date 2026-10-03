module

public import Probability.BranchingRandomWalk.Step.Presentation
public import Probability.BranchingRandomWalk.Step.PointMeasure
public import Probability.PointProcess.Basic

@[expose] public section

/-!
# Point-process observations of a random step

A branching random walk starts from `S : Ω → Step ι X`. Its point process is
the deterministic Dirac sum of that step. This module is an adapter to the
generic `ProbabilityTheory.PointProcess` interface; it never reconstructs or
orders a step from a measure.
-/

open MeasureTheory

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.Branching

/-- Package the point-measure observation of `S` as an abstract point process
once its local finiteness has been verified samplewise. Its integer-valuedness
is inherited from the Dirac-sum representation. -/
noncomputable def StepPresentation.toPointProcess
    {Ω ι X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [Countable ι]
    (S : StepPresentation Ω ι X) (𝒜 : Set (Set X))
    (hfinite : ∀ ω, IsFiniteOnFamily (S.pointMeasure ω) 𝒜) :
    PointProcess Ω X 𝒜 where
  toMeasure := S.pointMeasure
  measurable_toMeasure := S.pointMeasure_measurable
  counting := fun ω => stepPointMeasure_isIntegerValued (S ω)
  finiteOn := hfinite

end ProbabilityTheory.BranchingRandomWalk
