/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Spine.ManyToOne.EndpointManyToOne
public import Probability.BranchingRandomWalk.Spine.PointMeasure.Basic
public import Probability.Process.RandomWalk.Kernel.Endpoint
public import Probability.RandomMeasure.ExponentialTilt

/-!
# Enumeration-free endpoint many-to-one recursion

The offspring law in this file is a law on measures over an arbitrary
measurable mark space.  One branching transition is expressed by integration
against the sampled measure, so neither the mark space nor an auxiliary set
of child slots is assumed countable.

For measurable `φ : E → ℝ`, measurable `f : ℝ → [0,∞]`, and a law `Q` on
random measures, the weighted one-step operator satisfies the following
identity, where
`w_{φ,θ}(z) = RandomMeasure.exponentialWeight φ θ z`:

\[
\int^-_{\nu}\!\int^-_{z}
  w_{\varphi,\theta}(z)f(x+\varphi(z))\,d\nu(z)\,dQ(\nu)
=\operatorname{endpointOperator}
  (\operatorname{RandomMeasure.tiltedLaw}(\varphi,\theta,Q))f(x).
\]

The unweighted branching operator has the reciprocal-weight representation

\[
\int^-_{\nu}\!\int^-_{z}
  f(x+\varphi(z))\,d\nu(z)\,dQ(\nu)
=\operatorname{exponentialEndpointOperator}
  (\operatorname{RandomMeasure.tiltedLaw}(\varphi,-1,Q))f(x).
\]

When the relevant tilted law has total mass one, iteration gives the
corresponding endpoint identities at every generation: the weighted iterate
is `endpointIterate` under the `θ`-tilted law, while the unweighted iterate is
`exponentialEndpointIterate` under the `-1`-tilted law.

## Public declarations

- `pointMeasureWeightedEndpointOperator` and `pointMeasureEndpointOperator`:
  the one-step exponential and unweighted transitions obtained directly from
  a law on random measures.
- `pointMeasureWeightedEndpointOperator_eq_tilted` and
  `pointMeasureEndpointOperator_eq_untilted`: identify those transitions with
  the abstract tilted and untilted endpoint operators.
- `pointMeasureWeightedEndpointIterate`,
  `pointMeasureEndpointIterate`,
  `measurable_pointMeasureWeightedEndpointIterate`, and
  `measurable_pointMeasureEndpointIterate`: define and establish measurability
  of the iterated random-measure transitions.
- `pointMeasureWeightedEndpointManyToOne` and
  `pointMeasureEndpointManyToOne`: identify the iterated weighted and
  unweighted branching integrals with endpoint integrals under the
  enumeration-free tilted potential law.
- `pointMeasureWeightedEndpointOperator_map_stepPointMeasure`,
  `pointMeasureEndpointOperator_map_stepPointMeasure`,
  `pointMeasureWeightedEndpointIterate_map_stepPointMeasure`, and
  `pointMeasureEndpointIterate_map_stepPointMeasure`: transfer the operators
  and their iterates along the slot-to-point-measure pushforward.
-/

open MeasureTheory
open scoped ENNReal
open ProbabilityTheory.RandomWalk

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.Spine

open MeasureTheory

/-- One exponentially weighted branching transition obtained directly from
a law on random measures. -/
noncomputable def pointMeasureWeightedEndpointOperator
    {E : Type*} [MeasurableSpace E]
    (potential : E → ℝ) (θ : ℝ) (law : Measure (Measure E))
    (f : ℝ → ENNReal) (x : ℝ) : ENNReal :=
  ∫⁻ ν, ∫⁻ z, RandomMeasure.exponentialWeight potential θ z *
    f (x + potential z) ∂ν ∂law

/-- One unweighted branching transition obtained directly from a law on
random measures. -/
noncomputable def pointMeasureEndpointOperator
    {E : Type*} [MeasurableSpace E]
    (potential : E → ℝ) (law : Measure (Measure E))
    (f : ℝ → ENNReal) (x : ℝ) : ENNReal :=
  ∫⁻ ν, ∫⁻ z, f (x + potential z) ∂ν ∂law

theorem pointMeasureWeightedEndpointOperator_eq_tilted
    {E : Type*} [MeasurableSpace E]
    {potential : E → ℝ} (hpotential : Measurable potential)
    (θ : ℝ) (law : Measure (Measure E))
    {f : ℝ → ENNReal} (hf : Measurable f) :
    pointMeasureWeightedEndpointOperator potential θ law f =
      endpointOperator (RandomMeasure.tiltedLaw potential θ law) f := by
  funext x
  symm
  exact RandomMeasure.lintegral_tiltedLaw hpotential θ law
    (hf.comp (measurable_const.add measurable_id))

theorem pointMeasureEndpointOperator_eq_untilted
    {E : Type*} [MeasurableSpace E]
    {potential : E → ℝ} (hpotential : Measurable potential)
    (law : Measure (Measure E))
    {f : ℝ → ENNReal} (hf : Measurable f) :
    pointMeasureEndpointOperator potential law f =
      exponentialEndpointOperator
        (RandomMeasure.tiltedLaw potential (-1) law) f := by
  funext x
  symm
  simpa [exponentialEndpointOperator, pointMeasureEndpointOperator] using
    (RandomMeasure.lintegral_tiltedLaw_cancel hpotential (-1) law
      (f := fun y : ℝ => f (x + y))
      (hf.comp (measurable_const.add measurable_id)))

/-- Iterated weighted generation intensity, defined without a child
enumeration. -/
noncomputable def pointMeasureWeightedEndpointIterate
    {E : Type*} [MeasurableSpace E]
    (potential : E → ℝ) (θ : ℝ) (law : Measure (Measure E)) :
    ℕ → (ℝ → ENNReal) → ℝ → ENNReal
  | 0, f => f
  | n + 1, f => pointMeasureWeightedEndpointOperator potential θ law
      (pointMeasureWeightedEndpointIterate potential θ law n f)

/-- Iterated unweighted generation intensity, defined without a child
enumeration. -/
noncomputable def pointMeasureEndpointIterate
    {E : Type*} [MeasurableSpace E]
    (potential : E → ℝ) (law : Measure (Measure E)) :
    ℕ → (ℝ → ENNReal) → ℝ → ENNReal
  | 0, f => f
  | n + 1, f => pointMeasureEndpointOperator potential law
      (pointMeasureEndpointIterate potential law n f)

theorem measurable_pointMeasureWeightedEndpointIterate
    {E : Type*} [MeasurableSpace E]
    {potential : E → ℝ} (hpotential : Measurable potential)
    (θ : ℝ) (law : Measure (Measure E))
    (hnormalization : RandomMeasure.HasNormalization potential θ law)
    {f : ℝ → ENNReal} (hf : Measurable f) :
    ∀ n, Measurable
      (pointMeasureWeightedEndpointIterate potential θ law n f)
  | 0 => hf
  | n + 1 => by
      let _ : IsProbabilityMeasure
          (RandomMeasure.tiltedLaw potential θ law) :=
        RandomMeasure.tiltedLaw_isProbability hpotential θ law hnormalization
      rw [pointMeasureWeightedEndpointIterate,
        pointMeasureWeightedEndpointOperator_eq_tilted hpotential θ law
          (measurable_pointMeasureWeightedEndpointIterate hpotential θ law
            hnormalization hf n)]
      exact measurable_endpointOperator _
        (measurable_pointMeasureWeightedEndpointIterate hpotential θ law
          hnormalization hf n)

/-- Enumeration-free weighted many-to-one recursion. -/
theorem pointMeasureWeightedEndpointManyToOne
    {E : Type*} [MeasurableSpace E]
    {potential : E → ℝ} (hpotential : Measurable potential)
    (θ : ℝ) (law : Measure (Measure E))
    (hnormalization : RandomMeasure.HasNormalization potential θ law)
    {f : ℝ → ENNReal} (hf : Measurable f) :
    ∀ n, pointMeasureWeightedEndpointIterate potential θ law n f =
      endpointIterate
        (RandomMeasure.tiltedLaw potential θ law) n f
  | 0 => rfl
  | n + 1 => by
      let _ : IsProbabilityMeasure
          (RandomMeasure.tiltedLaw potential θ law) :=
        RandomMeasure.tiltedLaw_isProbability hpotential θ law hnormalization
      rw [pointMeasureWeightedEndpointIterate, endpointIterate,
        pointMeasureWeightedEndpointManyToOne hpotential θ law
          hnormalization hf n]
      exact pointMeasureWeightedEndpointOperator_eq_tilted hpotential θ law
        (measurable_endpointIterate _ hf n)

theorem measurable_pointMeasureEndpointIterate
    {E : Type*} [MeasurableSpace E]
    {potential : E → ℝ} (hpotential : Measurable potential)
    (law : Measure (Measure E))
    (hnormalization : RandomMeasure.HasNormalization potential (-1) law)
    {f : ℝ → ENNReal} (hf : Measurable f) :
    ∀ n, Measurable (pointMeasureEndpointIterate potential law n f)
  | 0 => hf
  | n + 1 => by
      let _ : IsProbabilityMeasure
          (RandomMeasure.tiltedLaw potential (-1) law) :=
        RandomMeasure.tiltedLaw_isProbability hpotential (-1) law hnormalization
      rw [pointMeasureEndpointIterate,
        pointMeasureEndpointOperator_eq_untilted hpotential law
          (measurable_pointMeasureEndpointIterate hpotential law
            hnormalization hf n)]
      exact measurable_exponentialEndpointOperator _
        (measurable_pointMeasureEndpointIterate hpotential law
          hnormalization hf n)

/-- Enumeration-free unweighted many-to-one recursion. -/
theorem pointMeasureEndpointManyToOne
    {E : Type*} [MeasurableSpace E]
    {potential : E → ℝ} (hpotential : Measurable potential)
    (law : Measure (Measure E))
    (hnormalization : RandomMeasure.HasNormalization potential (-1) law)
    {f : ℝ → ENNReal} (hf : Measurable f) :
    ∀ n, pointMeasureEndpointIterate potential law n f =
      exponentialEndpointIterate
        (RandomMeasure.tiltedLaw potential (-1) law) n f
  | 0 => rfl
  | n + 1 => by
      let _ : IsProbabilityMeasure
          (RandomMeasure.tiltedLaw potential (-1) law) :=
        RandomMeasure.tiltedLaw_isProbability hpotential (-1) law hnormalization
      rw [pointMeasureEndpointIterate, exponentialEndpointIterate,
        pointMeasureEndpointManyToOne hpotential law hnormalization hf n]
      exact pointMeasureEndpointOperator_eq_untilted hpotential law
        (measurable_exponentialEndpointIterate _ hf n)

/-- A labelled offspring step realizes the abstract weighted random-measure
transition through its counting measure. -/
theorem pointMeasureWeightedEndpointOperator_map_stepPointMeasure
    {ι E : Type*} [Countable ι] [MeasurableSpace E] [Zero E]
    (φ : Combinatorics.Branching.Potential E)
    (μ : Measure (Combinatorics.Branching.Step ι E))
    {f : ℝ → ENNReal} (hf : Measurable f) :
    pointMeasureWeightedEndpointOperator φ (-1)
        (μ.map (Combinatorics.Branching.stepPointMeasure
          (ι := ι) (X := E))) f =
      weightedBranchingEndpointOperator φ μ f := by
  rw [pointMeasureWeightedEndpointOperator_eq_tilted
      φ.measurable_toFun (-1)
        (μ.map (Combinatorics.Branching.stepPointMeasure
          (ι := ι) (X := E))) hf,
    weightedBranchingEndpointOperator_eq_tilted φ μ hf,
    pointMeasure_tiltedLaw_eq_tiltedPotentialLaw]

/-- A labelled offspring step realizes the abstract unweighted random-measure
transition through its counting measure. -/
theorem pointMeasureEndpointOperator_map_stepPointMeasure
    {ι E : Type*} [Countable ι] [MeasurableSpace E] [Zero E]
    (φ : Combinatorics.Branching.Potential E)
    (μ : Measure (Combinatorics.Branching.Step ι E))
    {f : ℝ → ENNReal} (hf : Measurable f) :
    pointMeasureEndpointOperator φ
        (μ.map (Combinatorics.Branching.stepPointMeasure
          (ι := ι) (X := E))) f =
      branchingEndpointOperator φ μ f := by
  rw [pointMeasureEndpointOperator_eq_untilted
      φ.measurable_toFun
        (μ.map (Combinatorics.Branching.stepPointMeasure
          (ι := ι) (X := E))) hf,
    branchingEndpointOperator_eq_untilted φ μ hf,
    pointMeasure_tiltedLaw_eq_tiltedPotentialLaw]

theorem pointMeasureWeightedEndpointIterate_map_stepPointMeasure
    {ι E : Type*} [Countable ι] [MeasurableSpace E] [Zero E]
    (φ : Combinatorics.Branching.Potential E)
    (μ : Measure (Combinatorics.Branching.Step ι E))
    (hboundary : HasBoundaryNormalization φ μ)
    {f : ℝ → ENNReal} (hf : Measurable f) :
    ∀ n, pointMeasureWeightedEndpointIterate φ (-1)
        (μ.map (Combinatorics.Branching.stepPointMeasure
          (ι := ι) (X := E))) n f =
      weightedBranchingEndpointIterate φ μ n f
  | 0 => rfl
  | n + 1 => by
      rw [pointMeasureWeightedEndpointIterate,
        weightedBranchingEndpointIterate,
        pointMeasureWeightedEndpointIterate_map_stepPointMeasure
          φ μ hboundary hf n]
      exact pointMeasureWeightedEndpointOperator_map_stepPointMeasure φ μ
        (by
          rw [← pointMeasureWeightedEndpointIterate_map_stepPointMeasure
            φ μ hboundary hf n]
          exact measurable_pointMeasureWeightedEndpointIterate
            φ.measurable_toFun (-1)
              (μ.map (Combinatorics.Branching.stepPointMeasure
                (ι := ι) (X := E)))
              (pointMeasure_hasNormalization φ μ hboundary) hf n)

theorem pointMeasureEndpointIterate_map_stepPointMeasure
    {ι E : Type*} [Countable ι] [MeasurableSpace E] [Zero E]
    (φ : Combinatorics.Branching.Potential E)
    (μ : Measure (Combinatorics.Branching.Step ι E))
    (hboundary : HasBoundaryNormalization φ μ)
    {f : ℝ → ENNReal} (hf : Measurable f) :
    ∀ n, pointMeasureEndpointIterate φ
        (μ.map (Combinatorics.Branching.stepPointMeasure
          (ι := ι) (X := E))) n f =
      branchingEndpointIterate φ μ n f
  | 0 => rfl
  | n + 1 => by
      rw [pointMeasureEndpointIterate, branchingEndpointIterate,
        pointMeasureEndpointIterate_map_stepPointMeasure
          φ μ hboundary hf n]
      exact pointMeasureEndpointOperator_map_stepPointMeasure φ μ
        (by
          rw [← pointMeasureEndpointIterate_map_stepPointMeasure
            φ μ hboundary hf n]
          exact measurable_pointMeasureEndpointIterate
            φ.measurable_toFun
              (μ.map (Combinatorics.Branching.stepPointMeasure
                (ι := ι) (X := E)))
              (pointMeasure_hasNormalization φ μ hboundary) hf n)

end ProbabilityTheory.BranchingRandomWalk.Spine
