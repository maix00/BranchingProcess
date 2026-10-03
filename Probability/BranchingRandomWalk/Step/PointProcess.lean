module

public import Probability.BranchingRandomWalk.Step.Basic
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
once counting and local finiteness have been verified samplewise. -/
noncomputable def Step.toPointProcess
    {Ω ι X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [Countable ι]
    (S : Step Ω ι X) (𝒜 : Set (Set X))
    (hcount : ∀ ω, IsCountingMeasure (S.pointMeasure ω))
    (hfinite : ∀ ω, IsFiniteOnFamily (S.pointMeasure ω) 𝒜) :
    PointProcess Ω X 𝒜 where
  toMeasure := S.pointMeasure
  measurable_toMeasure := S.pointMeasure_measurable
  counting := hcount
  finiteOn := hfinite

end ProbabilityTheory.BranchingRandomWalk
