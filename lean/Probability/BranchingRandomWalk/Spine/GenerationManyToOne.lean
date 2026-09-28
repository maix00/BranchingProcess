import Probability.BranchingRandomWalk.Spine.GenerationBranching
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

/-- Weighted many-to-one for the actual generation of the pre-sampled
branching field, for every discrete generation. -/
theorem weightedGenerationManyToOne
    {ι Mark Position : Type*} [Countable ι]
    [MeasurableSpace Mark] [MeasurableSpace Position]
    (d : Mark → Position) (hd : Measurable d)
    (potential : Potential Position)
    (μ : Measure (Combinatorics.Branching.Step ι Mark))
    [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization (potential.comp d hd) μ)
    {f : ℝ → ENNReal} (hf : Measurable f) (n : ℕ) (x : ℝ) :
    (∫⁻ ω, weightedGenerationEndpoint (potential.comp d hd) n f x ω
        ∂stepFieldLaw μ) =
      ∫⁻ increment,
        f (x + RandomWalk.partialSum n increment)
        ∂tiltedIncrementFieldLaw (potential.comp d hd) μ := by
  calc
    (∫⁻ ω, weightedGenerationEndpoint (potential.comp d hd) n f x ω
        ∂stepFieldLaw μ) =
        weightedBranchingEndpointIterate
          (potential.comp d hd) μ n f x :=
      lintegral_weightedGenerationEndpoint_eq_iterate
        (potential.comp d hd) μ hf n x
    _ = _ := weightedEndpointManyToOne_randomWalk
      d hd potential μ hboundary hf n x

/-- Unweighted many-to-one for the actual generation of the pre-sampled
branching field, including the reciprocal exponential spine factor. -/
theorem generationManyToOne
    {ι Mark Position : Type*} [Countable ι]
    [MeasurableSpace Mark] [MeasurableSpace Position]
    (d : Mark → Position) (hd : Measurable d)
    (potential : Potential Position)
    (μ : Measure (Combinatorics.Branching.Step ι Mark))
    [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization (potential.comp d hd) μ)
    {f : ℝ → ENNReal} (hf : Measurable f) (n : ℕ) (x : ℝ) :
    (∫⁻ ω, generationEndpoint (potential.comp d hd) n f x ω
        ∂stepFieldLaw μ) =
      ∫⁻ increment,
        ENNReal.ofReal (Real.exp
          (RandomWalk.partialSum n increment)) *
          f (x + RandomWalk.partialSum n increment)
        ∂tiltedIncrementFieldLaw (potential.comp d hd) μ := by
  calc
    (∫⁻ ω, generationEndpoint (potential.comp d hd) n f x ω
        ∂stepFieldLaw μ) =
        branchingEndpointIterate (potential.comp d hd) μ n f x :=
      lintegral_generationEndpoint_eq_iterate
        (potential.comp d hd) μ hf n x
    _ = _ := endpointManyToOne_randomWalk
      d hd potential μ hboundary hf n x

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
        f (x + RandomWalk.partialSum 1 increment)
        ∂tiltedIncrementFieldLaw (potential.comp d hd) μ := by
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
          (RandomWalk.partialSum 1 increment)) *
          f (x + RandomWalk.partialSum 1 increment)
        ∂tiltedIncrementFieldLaw (potential.comp d hd) μ := by
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
