/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Assumptions.Structural
public import Probability.BranchingRandomWalk.Spine.Tilted.Law
public import Combinatorics.BranchingWalk.Step.Ordering.OrderDual

/-!
# Order duality of tilted branching-step laws

For a countable offspring-slot type $\iota$, reversing real step marks
changes each potential from $x$ to $-x$. The corresponding dual $-1$ tilted
spine law is the image under negation of the original $+1$ tilted law.
Boundary normalization, integrals, and second moments transfer through this
identity.

## Public declarations

- `ProbabilityTheory.BranchingRandomWalk.Spine.HasBoundaryNormalization.map_orderDualPotential`:
  dual boundary normalization transfers to the mapped real-step law.
- `ProbabilityTheory.BranchingRandomWalk.Spine.tiltedPotentialLaw_real_stepMapOrderDualPotential`:
  mapping a dual step through the dual potential preserves its real $-1$ tilted law.
- `ProbabilityTheory.BranchingRandomWalk.Spine.tiltedPotentialLaw_orderDual_stepOrderDual`:
  for countable slots, the dual $-1$ tilted law is the image under $x\mapsto -x$
  of the original real $+1$ tilted law.
- `ProbabilityTheory.BranchingRandomWalk.Spine.tiltedPotentialLaw_orderDual_stepOrderDual_integral`:
  $\int f(x)\,d\nu^*(x)=\int f(-x)\,d\nu(x)$ for measurable $f$.
- `ProbabilityTheory.BranchingRandomWalk.Spine.tiltedPotentialLaw_orderDual_stepOrderDual_memLp_two`:
  $L^2$ integrability of the original $+1$ tilted law transfers to the dual law.
-/

open MeasureTheory
open scoped ENNReal

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.Spine

open Combinatorics.Branching

variable {ι : Type*}

theorem HasBoundaryNormalization.map_orderDualPotential
    [Countable ι] (μ : Measure (Step ι (OrderDual ℝ)))
    (h : HasBoundaryNormalization orderDualPotential μ) :
    HasBoundaryNormalization realPotential
      (Measure.map (Step.map orderDualPotential) μ) := by
  change (∫⁻ ξ, totalPotentialWeight realPotential (-1) ξ
      ∂Measure.map (Step.map orderDualPotential) μ) = 1
  rw [lintegral_map (totalPotentialWeight_measurable realPotential (-1))
    (Step.map_measurable orderDualPotential.measurable_toFun)]
  calc
    (∫⁻ ξ, totalPotentialWeight realPotential (-1)
        (ξ.map orderDualPotential) ∂μ) =
      ∫⁻ ξ, totalPotentialWeight orderDualPotential (-1) ξ ∂μ := by
        apply lintegral_congr
        intro ξ
        exact totalPotentialWeight_real_stepMapOrderDualPotential ξ
    _ = 1 := h

theorem tiltedPotentialLaw_real_stepMapOrderDualPotential
    [Countable ι] (μ : Measure (Step ι (OrderDual ℝ))) :
    tiltedPotentialLaw realPotential (-1)
        (Measure.map (Step.map orderDualPotential) μ) =
      tiltedPotentialLaw orderDualPotential (-1) μ := by
  classical
  ext s hs
  rw [tiltedPotentialLaw_apply realPotential (-1)
      (Measure.map (Step.map orderDualPotential) μ) s hs,
    tiltedPotentialLaw_apply orderDualPotential (-1) μ s hs]
  apply tsum_congr
  intro i
  have hrealSet : MeasurableSet
      ((fun ξ : Step ι ℝ =>
        ξ.potentialValue' realPotential i) ⁻¹' s) :=
    hs.preimage (Step.potentialValue'_measurable realPotential i)
  have hdualSet : MeasurableSet
      ((fun ξ : Step ι (OrderDual ℝ) =>
        ξ.potentialValue' orderDualPotential i) ⁻¹' s) :=
    hs.preimage (Step.potentialValue'_measurable orderDualPotential i)
  rw [← lintegral_indicator hrealSet,
    ← lintegral_indicator hdualSet]
  rw [lintegral_map
    ((realizedPotentialWeight_measurable realPotential (-1) i).indicator
      hrealSet) (Step.map_measurable orderDualPotential.measurable_toFun)]
  apply lintegral_congr
  intro ξ
  have hvalue := orderDualPotentialValue_stepMap ξ i
  simp only [Set.indicator_apply, Set.mem_preimage]
  rw [hvalue, realizedPotentialWeight_real_stepMapOrderDualPotential]

/-- The spine law observed through `OrderDual` is the image under negation of
the original right-tilted spine law. This transports right-side moment
conditions without assuming invariance of the offspring law. -/
theorem tiltedPotentialLaw_orderDual_stepOrderDual
    [Countable ι] (μ : Measure (Step ι ℝ)) :
    tiltedPotentialLaw orderDualPotential (-1)
        (Measure.map stepOrderDual μ) =
      Measure.map Neg.neg (tiltedPotentialLaw realPotential 1 μ) := by
  classical
  ext s hs
  rw [tiltedPotentialLaw_apply orderDualPotential (-1)
      (Measure.map stepOrderDual μ) s hs,
    Measure.map_apply measurable_neg hs,
    tiltedPotentialLaw_apply realPotential 1 μ (Neg.neg ⁻¹' s)
      (hs.preimage measurable_neg)]
  apply tsum_congr
  intro i
  have hdualSet : MeasurableSet
      ((fun ξ : Step ι (OrderDual ℝ) =>
        ξ.potentialValue' orderDualPotential i) ⁻¹' s) :=
    hs.preimage (Step.potentialValue'_measurable orderDualPotential i)
  have hrealSet : MeasurableSet
      ((fun ξ : Step ι ℝ => ξ.potentialValue' realPotential i) ⁻¹'
        (Neg.neg ⁻¹' s)) :=
    (hs.preimage measurable_neg).preimage
      (Step.potentialValue'_measurable realPotential i)
  rw [← lintegral_indicator hdualSet,
    ← lintegral_indicator hrealSet]
  rw [lintegral_map
    ((realizedPotentialWeight_measurable orderDualPotential (-1) i).indicator
      hdualSet) measurable_stepOrderDual]
  apply lintegral_congr
  intro ξ
  have hvalue := orderDualPotentialValue_stepOrderDual ξ i
  have hreal : Step.potentialValue' realPotential ξ i = value' ξ i := by
    simp [Step.potentialValue', Step.potentialAt?, realPotential, value']
  simp only [Set.indicator_apply, Set.mem_preimage]
  rw [hvalue, realizedPotentialWeight_orderDual_stepOrderDual]
  rw [hreal]

theorem tiltedPotentialLaw_orderDual_stepOrderDual_integral
    [Countable ι] (μ : Measure (Step ι ℝ))
    (f : ℝ → ℝ) (hf : Measurable f) :
    ∫ y, f y ∂tiltedPotentialLaw orderDualPotential (-1)
        (Measure.map stepOrderDual μ) =
      ∫ y, f (-y) ∂tiltedPotentialLaw realPotential 1 μ := by
  rw [tiltedPotentialLaw_orderDual_stepOrderDual]
  exact integral_map measurable_neg.aemeasurable hf.aestronglyMeasurable

theorem tiltedPotentialLaw_orderDual_stepOrderDual_memLp_two
    [Countable ι] (μ : Measure (Step ι ℝ))
    (h : MemLp id 2 (tiltedPotentialLaw realPotential 1 μ)) :
    MemLp id 2
      (tiltedPotentialLaw orderDualPotential (-1)
        (Measure.map stepOrderDual μ)) := by
  rw [tiltedPotentialLaw_orderDual_stepOrderDual,
    memLp_map_measure_iff stronglyMeasurable_id.aestronglyMeasurable
      measurable_neg.aemeasurable]
  change MemLp (-id) 2
    (tiltedPotentialLaw realPotential 1 μ)
  simpa using h.neg

end ProbabilityTheory.BranchingRandomWalk.Spine

end
