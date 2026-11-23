/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Spine.ManyToOne.EndpointManyToOne
public import Probability.BranchingRandomWalk.Spine.RandomWalk.IncrementProcess
public import Probability.Process.RandomWalk.Kernel.Endpoint

/-!
# Branching-field endpoint realization

The endpoint recursions for a tilted branching field are obtained by combining
the independent-increment realization with the field's product law.

For `φ : Potential X`, a boundary-normalized step law `μ`, and measurable
`f : ℝ → [0,∞]`, the finite partial sum of the iid tilted increment field
realizes the endpoint iterate:

\[
\int^-_{\omega} f(x+S_n(\omega))\,
  \partial\operatorname{tiltedIncrementFieldLaw}(\varphi,\mu)
=\operatorname{endpointIterate}
  (\operatorname{tiltedPotentialLaw}(\varphi,-1,\mu),n,f)(x),
\]

where `S_n(ω) = AdditivePath.displacement n ω`.  The unweighted iterate has
the reciprocal exponential factor:

\[
\int^-_{\omega}\operatorname{ENNReal.ofReal}(e^{S_n(\omega)})
  f(x+S_n(\omega))\,
  \partial\operatorname{tiltedIncrementFieldLaw}(\varphi,\mu)
=\operatorname{exponentialEndpointIterate}
  (\operatorname{tiltedPotentialLaw}(\varphi,-1,\mu),n,f)(x).
\]

Composing these identities with the endpoint recursions identifies the
weighted and unweighted branching iterates with the same two increment
integrals.

The IID integral identities reuse the general random-walk endpoint module;
no BRW-specific copies of the partial-sum inductions are retained.

## Public declarations

- `weightedEndpointManyToOne_product` and
  `endpointManyToOne_product`: the corresponding many-to-one formulas for the
  auxiliary IID increment law. The raw measure `μ` need not be a probability
  measure. Actual branching-field endpoints are derived separately in
  `GenerationManyToOne.lean` from the general state-tree theorem.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.Spine

open ProbabilityTheory.RandomWalk

open Combinatorics.Branching MeasureTheory

/-- Weighted product-process identity with separate raw mark and position
spaces. -/
theorem weightedEndpointManyToOne_product
    {ι Mark Position : Type*} [Countable ι]
    [MeasurableSpace Mark] [MeasurableSpace Position]
    (d : Mark → Position) (hd : Measurable d)
    (potential : Potential Position)
    (μ : Measure (Combinatorics.Branching.Step ι Mark))
    (hboundary : HasBoundaryNormalization (potential.comp d hd) μ)
    {f : ℝ → ENNReal} (hf : Measurable f) (n : ℕ) (x : ℝ) :
    weightedBranchingEndpointIterate (potential.comp d hd) μ n f x =
      ∫⁻ increment, f (x + AdditivePath.displacement n increment)
        ∂tiltedIncrementFieldLaw (potential.comp d hd) μ := by
  rw [weightedEndpointManyToOne d hd potential μ hboundary hf n]
  let := tiltedPotentialLaw_isProbability (potential.comp d hd) μ hboundary
  exact (lintegral_iidPosition_eq_endpointIterate
    (tiltedPotentialLaw (potential.comp d hd) (-1) μ) hf n x).symm

/-- Unweighted product-process identity with separate raw mark and position
spaces. -/
theorem endpointManyToOne_product
    {ι Mark Position : Type*} [Countable ι]
    [MeasurableSpace Mark] [MeasurableSpace Position]
    (d : Mark → Position) (hd : Measurable d)
    (potential : Potential Position)
    (μ : Measure (Combinatorics.Branching.Step ι Mark))
    (hboundary : HasBoundaryNormalization (potential.comp d hd) μ)
    {f : ℝ → ENNReal} (hf : Measurable f) (n : ℕ) (x : ℝ) :
    branchingEndpointIterate (potential.comp d hd) μ n f x =
      ∫⁻ increment,
        ENNReal.ofReal (Real.exp (AdditivePath.displacement n increment)) *
          f (x + AdditivePath.displacement n increment)
        ∂tiltedIncrementFieldLaw (potential.comp d hd) μ := by
  rw [endpointManyToOne d hd potential μ hboundary hf n]
  let := tiltedPotentialLaw_isProbability (potential.comp d hd) μ hboundary
  exact (lintegral_iidPosition_expWeighted_eq_endpointIterate
    (tiltedPotentialLaw (potential.comp d hd) (-1) μ) hf n x).symm

end ProbabilityTheory.BranchingRandomWalk.Spine
