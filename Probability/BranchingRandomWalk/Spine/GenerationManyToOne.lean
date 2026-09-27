import Probability.BranchingRandomWalk.Spine.Generation
import Probability.BranchingRandomWalk.Spine.RandomWalk

/-!
# Actual-generation many-to-one identities

This file connects observables of the pre-sampled branching field to the spine
random walk.  The first-generation theorem is the base case for the general
subtree induction.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ProbabilityTheory.BranchingRandomWalk.Spine

open Combinatorics.Branching MeasureTheory

/-- Weighted many-to-one for the actual first generation of the pre-sampled
field. -/
theorem weightedGenerationOneManyToOne
    {ι Mark Position : Type*} [Countable ι]
    [MeasurableSpace Mark] [MeasurableSpace Position]
    (d : Mark → Position) (hd : Measurable d)
    (potential : Potential Position)
    (μ : Measure (Combinatorics.Branching.Step ι Mark))
    [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization (potential.comp d hd) μ)
    {f : ℝ → ENNReal} (hf : Measurable f) (x : ℝ) :
    (∫⁻ ω, weightedGenerationEndpoint (potential.comp d hd) 1 f x ω
        ∂stepFieldLaw μ) =
      ∫⁻ increment,
        f (x + (spineRandomWalk (potential.comp d hd) μ hboundary).positionAt
          id 1 increment)
        ∂(spineRandomWalk (potential.comp d hd) μ hboundary).incrementLaw := by
  calc
    (∫⁻ ω, weightedGenerationEndpoint (potential.comp d hd) 1 f x ω
        ∂stepFieldLaw μ) =
        weightedBranchingEndpointOperator (potential.comp d hd) μ f x :=
      lintegral_weightedGenerationEndpoint_one
        (potential.comp d hd) μ hf x
    _ = weightedBranchingEndpointIterate
        (potential.comp d hd) μ 1 f x := rfl
    _ = _ := weightedEndpointManyToOne_randomWalk
      d hd potential μ hboundary hf 1 x

/-- Unweighted many-to-one for the actual first generation of the pre-sampled
field. -/
theorem generationOneManyToOne
    {ι Mark Position : Type*} [Countable ι]
    [MeasurableSpace Mark] [MeasurableSpace Position]
    (d : Mark → Position) (hd : Measurable d)
    (potential : Potential Position)
    (μ : Measure (Combinatorics.Branching.Step ι Mark))
    [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization (potential.comp d hd) μ)
    {f : ℝ → ENNReal} (hf : Measurable f) (x : ℝ) :
    (∫⁻ ω, generationEndpoint (potential.comp d hd) 1 f x ω
        ∂stepFieldLaw μ) =
      ∫⁻ increment,
        ENNReal.ofReal (Real.exp
          ((spineRandomWalk (potential.comp d hd) μ hboundary).positionAt
            id 1 increment)) *
          f (x + (spineRandomWalk (potential.comp d hd) μ hboundary).positionAt
            id 1 increment)
        ∂(spineRandomWalk (potential.comp d hd) μ hboundary).incrementLaw := by
  calc
    (∫⁻ ω, generationEndpoint (potential.comp d hd) 1 f x ω
        ∂stepFieldLaw μ) =
        branchingEndpointOperator (potential.comp d hd) μ f x :=
      lintegral_generationEndpoint_one (potential.comp d hd) μ hf x
    _ = branchingEndpointIterate
        (potential.comp d hd) μ 1 f x := rfl
    _ = _ := endpointManyToOne_randomWalk
      d hd potential μ hboundary hf 1 x

end ProbabilityTheory.BranchingRandomWalk.Spine
