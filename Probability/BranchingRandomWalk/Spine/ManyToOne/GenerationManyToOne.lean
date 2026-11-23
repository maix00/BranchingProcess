/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Spine.Path.ManyToOne.Identity

/-!
# Actual-generation many-to-one identities

This file connects observables of the pre-sampled branching field to the spine
random walk. Each endpoint theorem specializes the canonical state-tree path
identity to the last coordinate; the one-generation forms specialize `n = 1`.

## Public declarations

- `weightedGenerationManyToOne` and `generationManyToOne`: identify the
  weighted and unweighted observable sums over the actual generation of the
  pre-sampled field with the corresponding spine-walk expectations.
- `weightedGenerationOneManyToOne` and `generationOneManyToOne`: their
  one-generation forms, obtained by setting `n = 1`.

For a measurable observable \(f:\mathbb R\to[0,\infty]\), generation
\(n\), and initial position \(x\), the weighted identity is
\[
  \int^-_\omega \operatorname{weightedGenerationEndpoint}
  (V\!\circ d,n,f,x,\omega)\,d\operatorname{offspringFieldLaw}(\mu)
  =\int^-_z f(x+S_n(z))\,
  d\operatorname{tiltedIncrementFieldLaw}(V\!\circ d,\mu),
\]
and the unweighted identity is
\[
  \int^-_\omega \operatorname{generationEndpoint}
  (V\!\circ d,n,f,x,\omega)\,d\operatorname{offspringFieldLaw}(\mu)
  =\int^-_z \operatorname{ofReal}(e^{S_n(z)})f(x+S_n(z))\,
  d\operatorname{tiltedIncrementFieldLaw}(V\!\circ d,\mu),
\]
where \(V\) is the potential and
\(S_n=\operatorname{AdditivePath.displacement}(n,\cdot)\).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ProbabilityTheory.BranchingRandomWalk.Spine

open ProbabilityTheory.BranchingProcess (offspringFieldLaw offspringFieldLaw_coordinate offspringFieldLaw_independent offspringFieldLaw_mapMarks)

open ProbabilityTheory.RandomWalk

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
        ∂offspringFieldLaw μ) =
      ∫⁻ increment,
        f (x + AdditivePath.displacement n increment)
        ∂tiltedIncrementFieldLaw (potential.comp d hd) μ := by
  have hi := weightedPathManyToOne d hd potential μ hboundary n
    (F := fun path => f (path ⟨n, Nat.lt_succ_self n⟩))
    (hf.comp (measurable_pi_apply _)) x
  simpa only [weightedPathGeneration_last, history_last, AdditivePath.fromIncrements] using hi

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
        ∂offspringFieldLaw μ) =
      ∫⁻ increment,
        ENNReal.ofReal (Real.exp
          (AdditivePath.displacement n increment)) *
          f (x + AdditivePath.displacement n increment)
        ∂tiltedIncrementFieldLaw (potential.comp d hd) μ := by
  have hi := pathManyToOne d hd potential μ hboundary n
    (F := fun path => f (path ⟨n, Nat.lt_succ_self n⟩))
    (hf.comp (measurable_pi_apply _)) x
  simpa only [pathGeneration_last, history_last, AdditivePath.fromIncrements] using hi

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
        ∂offspringFieldLaw μ) =
      ∫⁻ increment,
        f (x + AdditivePath.displacement 1 increment)
        ∂tiltedIncrementFieldLaw (potential.comp d hd) μ := by
  exact weightedGenerationManyToOne d hd potential μ hboundary hf 1 x

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
        ∂offspringFieldLaw μ) =
      ∫⁻ increment,
        ENNReal.ofReal (Real.exp
          (AdditivePath.displacement 1 increment)) *
          f (x + AdditivePath.displacement 1 increment)
        ∂tiltedIncrementFieldLaw (potential.comp d hd) μ := by
  exact generationManyToOne d hd potential μ hboundary hf 1 x

end ProbabilityTheory.BranchingRandomWalk.Spine
