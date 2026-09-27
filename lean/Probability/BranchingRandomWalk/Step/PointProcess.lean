import Probability.BranchingRandomWalk.Step.Basic
import Probability.PointProcess.Basic

/-!
# Point-process observations of a random step

A branching random walk starts from `Ξ : Ω → Step ι X`. Its point process is
the deterministic Dirac sum of that step. This module is an adapter to the
generic `ProbabilityTheory.PointProcess` interface; it never reconstructs or
orders a step from a measure.
-/

open MeasureTheory

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.Branching

/-- Package the point-measure observation of `Ξ` as an abstract point process
once counting and local finiteness have been verified samplewise. -/
noncomputable def Step.toPointProcess
    {Ω ι X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [Countable ι] [Zero X]
    (Ξ : Step Ω ι X) (𝒜 : Set (Set X))
    (hcount : ∀ ω, IsCountingMeasure (Ξ.pointMeasure ω))
    (hfinite : ∀ ω, IsFiniteOnFamily (Ξ.pointMeasure ω) 𝒜) :
    PointProcess Ω X 𝒜 where
  toMeasure := Ξ.pointMeasure
  measurable_toMeasure := Ξ.pointMeasure_measurable
  counting := hcount
  finiteOn := hfinite

end ProbabilityTheory.BranchingRandomWalk
