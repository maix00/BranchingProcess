/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingProcess.Offspring.Count
import Probability.BranchingProcess.Offspring.Map
import Probability.BranchingRandomWalk.Selection.NSelection.Speed.OrderDualEnvironment
import Probability.BranchingRandomWalk.Selection.NSelection.Tail.SelectedEndpointSublevel

/-!
# Endpoint sublevel under right-side assumptions

The event is defined on the `OrderDual` observation of the original
offspring law. Its endpoint is below a threshold in the dual order exactly
when the original endpoint is above that threshold. The proof maps this
observation through `orderDualPotential` only to reuse the real-valued
left-endpoint estimate.
-/

open Filter MeasureTheory
open scoped ENNReal Topology

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail

open Combinatorics.Branching
open Combinatorics.UlamHarris
open ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw
open ProbabilityTheory.BranchingRandomWalk.Spine
open ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed

/-- Map every step in a finite-root field from its dual observation to the
real potential used by the endpoint estimates. -/
def orderDualFieldToPotential {m : ℕ}
    (field : FiniteRootStepField m ℕ (OrderDual ℝ)) :
    FiniteRootStepField m ℕ ℝ :=
  fun r => (field r).map orderDualPotential

theorem measurable_orderDualFieldToPotential (m : ℕ) :
    Measurable (orderDualFieldToPotential (m := m)) := by
  rw [measurable_pi_iff]
  intro r
  exact (Combinatorics.Branching.StepField.map_measurable
    orderDualPotential.measurable_toFun).comp (measurable_pi_apply r)

/-- Some generation-`H` member of the first-`N` selected population has
endpoint below `threshold` in `OrderDual ℝ`. Under the original real order,
this is an endpoint above the same threshold. -/
def firstNSelectedEndpointBelowOrderDual (m N H : ℕ)
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (threshold : OrderDual ℝ) :
    Set (FiniteRootStepField m ℕ (OrderDual ℝ)) :=
  {field | orderDualFieldToPotential field ∈
    firstNSelectedEndpointBelow m N H (orderDualPotential threshold)}

theorem measurableSet_firstNSelectedEndpointBelowOrderDual (m N H : ℕ)
    [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)]
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (threshold : OrderDual ℝ) :
    MeasurableSet (firstNSelectedEndpointBelowOrderDual m N H threshold) := by
  change MeasurableSet
    (orderDualFieldToPotential (m := m) ⁻¹'
      firstNSelectedEndpointBelow m N H (orderDualPotential threshold))
  exact (measurableSet_firstNSelectedEndpointBelow m N H
    (orderDualPotential threshold)).preimage
      (measurable_orderDualFieldToPotential m)

private theorem finiteRootStepFieldLaw_orderDual_map_potential
    (μ : Measure (Step ℕ (OrderDual ℝ))) [IsProbabilityMeasure μ]
    (m : ℕ) :
    (finiteRootStepFieldLaw μ m).map
        (orderDualFieldToPotential (m := m)) =
      finiteRootStepFieldLaw
        (μ.map (Step.map orderDualPotential)) m := by
  convert (RootIndexed.stepFieldLaw_mapMarks (Root := Fin m) (α := ℕ)
    (μ := μ) (f := orderDualPotential)
    orderDualPotential.measurable_toFun) using 1 <;> rfl

private theorem tiltedPotentialLaw_orderDual_neg_mean
    (μ : Measure (Step ℕ ℝ))
    (hmean : (∫ y : ℝ, y ∂tiltedPotentialLaw realPotential 1 μ) = 0) :
    (∫ y : ℝ, y ∂tiltedPotentialLaw orderDualPotential (-1)
      (Measure.map stepOrderDual μ)) = 0 := by
  rw [tiltedPotentialLaw_orderDual_stepOrderDual]
  calc
    (∫ y : ℝ, y ∂Measure.map Neg.neg
        (tiltedPotentialLaw realPotential 1 μ)) =
      ∫ y : ℝ, -y ∂tiltedPotentialLaw realPotential 1 μ := by
        exact integral_map measurable_neg.aemeasurable
          stronglyMeasurable_id.aestronglyMeasurable
    _ = -(∫ y : ℝ, y ∂tiltedPotentialLaw realPotential 1 μ) := by
          rw [integral_neg]
    _ = 0 := by rw [hmean]; simp

private theorem tiltedPotentialLaw_orderDual_secondMoment
    (μ : Measure (Step ℕ ℝ)) :
    (∫ y : ℝ, y ^ 2 ∂tiltedPotentialLaw orderDualPotential (-1)
      (Measure.map stepOrderDual μ)) =
    ∫ y : ℝ, y ^ 2 ∂tiltedPotentialLaw realPotential 1 μ := by
  rw [tiltedPotentialLaw_orderDual_stepOrderDual]
  calc
    (∫ y : ℝ, y ^ 2 ∂Measure.map Neg.neg
        (tiltedPotentialLaw realPotential 1 μ)) =
      ∫ y : ℝ, (-y) ^ 2 ∂tiltedPotentialLaw realPotential 1 μ := by
        exact integral_map measurable_neg.aemeasurable
          ((measurable_id.pow_const 2).aestronglyMeasurable)
    _ = ∫ y : ℝ, y ^ 2 ∂tiltedPotentialLaw realPotential 1 μ := by
          congr 1
          funext y
          ring

/-- The polynomial upper-tail bound for the endpoint selected in the dual
order. All displayed hypotheses are conditions on the original offspring
law. The finite-root field law is its `OrderDual` observation. -/
theorem eventually_finiteRootStepFieldLaw_firstNSelectedEndpointBelowOrderDual_le_polynomial_of_logarithmic_scales
    {L : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw ℕ ℝ}
    (hboundary : HasRightBoundaryNormalization (L : Measure (Step ℕ ℝ)))
    (hsupercritical : L.IsSupercritical)
    (hspineMean : (∫ y : ℝ, y ∂tiltedPotentialLaw realPotential 1
      (L : Measure (Step ℕ ℝ))) = 0)
    (hspineFiniteVariance : MemLp id 2
      (tiltedPotentialLaw realPotential 1 (L : Measure (Step ℕ ℝ))))
    {horizon : ℕ → ℕ} {a t zeta : ℝ}
    (ha_zero : 0 ≤ a) (ha_one : a ≤ 1) (ht : 0 < t)
    (hhorizon : Tendsto
      (fun n : ℕ => (horizon n : ℝ) / Real.log (n : ℝ) ^ 3)
      atTop (𝓝 t))
    (habove : a - (Real.pi ^ 2 / 2) *
      (∫ y : ℝ, y ^ 2 ∂tiltedPotentialLaw realPotential 1
        (L : Measure (Step ℕ ℝ))) * t < zeta) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∀ᶠ n : ℕ in atTop,
      (finiteRootStepFieldLaw
        (L.mapMarks OrderDual.toDual measurable_id :
          Measure (Step ℕ (OrderDual ℝ)))
        (Nat.floor ((n : ℝ) ^ a)))
        (@firstNSelectedEndpointBelowOrderDual
          (Nat.floor ((n : ℝ) ^ a)) n (horizon n)
          (RootIndexed.addressLinearOrder
            (Fin (Nat.floor ((n : ℝ) ^ a))) ℕ)
          (OrderDual.toDual (zeta * Real.log (n : ℝ)))) ≤
        ENNReal.ofReal (Real.exp (-epsilon * Real.log (n : ℝ))) := by
  let μ : Measure (Step ℕ ℝ) := L
  let Ldual : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw
      ℕ (OrderDual ℝ) := L.mapMarks OrderDual.toDual measurable_id
  let μdual : Measure (Step ℕ (OrderDual ℝ)) := Ldual
  let Lpotential : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw
      ℕ ℝ := Ldual.mapMarks orderDualPotential orderDualPotential.measurable_toFun
  have hμdual : μdual = Measure.map stepOrderDual μ := by
    change (L.mapMarks OrderDual.toDual measurable_id :
      Measure (Step ℕ (OrderDual ℝ))) = Measure.map stepOrderDual μ
    rfl
  have hμpotential : (Lpotential : Measure (Step ℕ ℝ)) =
      μdual.map (Step.map orderDualPotential) := by
    change (Ldual.mapMarks orderDualPotential
      orderDualPotential.measurable_toFun : Measure (Step ℕ ℝ)) = _
    rw [ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw.mapMarks_toMeasure]
  have hboundaryDual : HasBoundaryNormalization orderDualPotential μdual := by
    rw [hμdual]
    exact HasRightBoundaryNormalization.orderDual (L : Measure (Step ℕ ℝ))
      hboundary
  have hboundaryPotential :
      HasBoundaryNormalization realPotential (Lpotential : Measure (Step ℕ ℝ)) := by
    have h := HasBoundaryNormalization.map_orderDualPotential μdual hboundaryDual
    simpa [Lpotential, μdual,
      ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw.mapMarks_toMeasure] using h
  have hsupercriticalPotential : Lpotential.IsSupercritical := by
    have hdualCount : Ldual.childCountLaw = L.childCountLaw := by
      simpa [Ldual] using
        (ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw.childCountLaw_mapMarks
          L OrderDual.toDual measurable_id)
    have hpotentialCount : Lpotential.childCountLaw = Ldual.childCountLaw := by
      simpa [Lpotential] using
        (ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw.childCountLaw_mapMarks
          Ldual orderDualPotential orderDualPotential.measurable_toFun)
    change 1 < ∫⁻ n : ℕ∞, (n : ℝ≥0∞) ∂Lpotential.childCountLaw
    rw [hpotentialCount, hdualCount]
    change 1 < L.expectedChildCount
    exact hsupercritical
  have hspineMeanPotential :
      (∫ y : ℝ, y ∂tiltedPotentialLaw realPotential (-1)
        (Lpotential : Measure (Step ℕ ℝ))) = 0 := by
    rw [show tiltedPotentialLaw realPotential (-1)
        (Lpotential : Measure (Step ℕ ℝ)) =
        tiltedPotentialLaw orderDualPotential (-1) μdual by
          rw [hμpotential]
          exact tiltedPotentialLaw_real_stepMapOrderDualPotential μdual]
    exact tiltedPotentialLaw_orderDual_neg_mean μ hspineMean
  have hspineFiniteVariancePotential : MemLp id 2
      (tiltedPotentialLaw realPotential (-1)
        (Lpotential : Measure (Step ℕ ℝ))) := by
    rw [show tiltedPotentialLaw realPotential (-1)
        (Lpotential : Measure (Step ℕ ℝ)) =
        tiltedPotentialLaw orderDualPotential (-1) μdual by
          rw [hμpotential]
          exact tiltedPotentialLaw_real_stepMapOrderDualPotential μdual]
    rw [hμdual]
    exact tiltedPotentialLaw_orderDual_stepOrderDual_memLp_two μ hspineFiniteVariance
  have hsecondMoment :
      (∫ y : ℝ, y ^ 2 ∂tiltedPotentialLaw realPotential (-1)
        (Lpotential : Measure (Step ℕ ℝ))) =
      ∫ y : ℝ, y ^ 2 ∂tiltedPotentialLaw realPotential 1 μ := by
    have hlaw : tiltedPotentialLaw realPotential (-1)
        (Lpotential : Measure (Step ℕ ℝ)) =
        tiltedPotentialLaw orderDualPotential (-1) μdual := by
      rw [hμpotential]
      exact tiltedPotentialLaw_real_stepMapOrderDualPotential μdual
    rw [hlaw, hμdual]
    exact tiltedPotentialLaw_orderDual_secondMoment μ
  have hbelow : -zeta < -a + (Real.pi ^ 2 / 2) *
      (∫ y : ℝ, y ^ 2 ∂tiltedPotentialLaw realPotential (-1)
        (Lpotential : Measure (Step ℕ ℝ))) * t := by
    rw [hsecondMoment]
    linarith
  obtain ⟨epsilon, hepsilon, hbound⟩ :=
    eventually_finiteRootStepFieldLaw_firstNSelectedEndpointBelow_le_polynomial_of_logarithmic_scales
      (L := Lpotential) hboundaryPotential hsupercriticalPotential
      hspineMeanPotential hspineFiniteVariancePotential
      (horizon := horizon) (a := a) (t := t) (zeta := -zeta)
      ha_zero ha_one ht hhorizon hbelow
  refine ⟨epsilon, hepsilon, ?_⟩
  filter_upwards [hbound] with n hboundn
  let m := Nat.floor ((n : ℝ) ^ a)
  letI : LinearOrder (RootIndexed.TreeNode (Fin m) ℕ) :=
    RootIndexed.addressLinearOrder (Fin m) ℕ
  have hmap :
      (finiteRootStepFieldLaw μdual m).map
          (orderDualFieldToPotential (m := m)) =
        finiteRootStepFieldLaw (Lpotential : Measure (Step ℕ ℝ)) m := by
    calc
      (finiteRootStepFieldLaw μdual m).map
          (orderDualFieldToPotential (m := m)) =
        finiteRootStepFieldLaw
          (μdual.map (Step.map orderDualPotential)) m :=
            finiteRootStepFieldLaw_orderDual_map_potential μdual m
      _ = finiteRootStepFieldLaw (Lpotential : Measure (Step ℕ ℝ)) m := by
            rw [hμpotential]
  have hmeas := measurableSet_firstNSelectedEndpointBelow m n (horizon n)
    ((-zeta) * Real.log (n : ℝ))
  have hthreshold : orderDualPotential
      (OrderDual.toDual (zeta * Real.log (n : ℝ))) =
        (-zeta) * Real.log (n : ℝ) := by
    simp [orderDualPotential]
  have hmeasure :
      (finiteRootStepFieldLaw μdual m)
        (firstNSelectedEndpointBelowOrderDual m n (horizon n)
          (OrderDual.toDual (zeta * Real.log (n : ℝ)))) =
      (finiteRootStepFieldLaw (Lpotential : Measure (Step ℕ ℝ)) m)
        (firstNSelectedEndpointBelow m n (horizon n)
          ((-zeta) * Real.log (n : ℝ))) := by
    change (finiteRootStepFieldLaw μdual m)
        (orderDualFieldToPotential (m := m) ⁻¹'
          firstNSelectedEndpointBelow m n (horizon n)
            (orderDualPotential (OrderDual.toDual
              (zeta * Real.log (n : ℝ))))) = _
    rw [hthreshold]
    calc
      _ = (finiteRootStepFieldLaw μdual m).map
          (orderDualFieldToPotential (m := m))
          (firstNSelectedEndpointBelow m n (horizon n)
            ((-zeta) * Real.log (n : ℝ))) := by
              exact (Measure.map_apply
                (measurable_orderDualFieldToPotential m) hmeas).symm
      _ = (finiteRootStepFieldLaw (Lpotential : Measure (Step ℕ ℝ)) m)
          (firstNSelectedEndpointBelow m n (horizon n)
            ((-zeta) * Real.log (n : ℝ))) := by
              rw [hmap]
  rw [show (L.mapMarks OrderDual.toDual measurable_id :
      Measure (Step ℕ (OrderDual ℝ))) = μdual by rfl,
    show (Nat.floor ((n : ℝ) ^ a) : ℕ) = m by rfl,
    hmeasure]
  simpa [m, logarithmicEndpointThreshold, logarithmOfSampleSize] using hboundn

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail
