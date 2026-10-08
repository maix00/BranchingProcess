/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.Process.SmallDeviation.Mogulskii.PathClass.Partition.LowerGeometry
import Probability.Process.SmallDeviation.Mogulskii.PathClass.Partition.LowerProduct

/-!
# Finite-partition lower bound from endpoint-return kernels

The deterministic core construction and independent cell kernels combine to
give a genuine probability lower bound for the scaled step corridor. The
almost-sure zero start is intersected into the event only for the pathwise
inclusion; it does not change its probability.
-/

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory.Process.SmallDeviation.Mogulskii

/-- The product of the independent endpoint-return kernels is a lower bound
for the probability that the scaled stable path stays in the step corridor.
The proof keeps the almost-sure pinned-start condition explicit, because the
deterministic concatenation uses the value at time zero. -/
theorem measure_scalePath_preimage_corridorSet_ge_coreReturnProduct
    {α scale : ℝ} {μ : Measure ℝ}
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hP : IsStableClockProcessLaw α μ unitIntervalClock P)
    (upper lower : StepBoundary)
    (center radius : Fin (StepBoundary.commonKnots upper lower).card → ℝ)
    (innerLower innerUpper :
      Fin ((StepBoundary.commonKnots upper lower).card - 1) → ℝ)
    (hcenter0 : center ⟨0, by
      have hcard := Finset.card_pos.mpr
        (StepBoundary.commonKnots_nonempty upper lower)
      omega⟩ = 0)
    (hradius0 : radius ⟨0, by
      have hcard := Finset.card_pos.mpr
        (StepBoundary.commonKnots_nonempty upper lower)
      omega⟩ = 0)
    (hscale : 0 < scale)
    (hcores : ∀ j : Fin (StepBoundary.commonKnots upper lower).card,
      center j - radius j ∈ selValues upper lower
        (StepBoundary.commonPartitionGrid upper lower j.val) ∧
      center j + radius j ∈ selValues upper lower
        (StepBoundary.commonPartitionGrid upper lower j.val))
    (hradiusStep : ∀ i : Fin ((StepBoundary.commonKnots upper lower).card - 1),
      radius (commonPartitionCellLeftKnotIndex upper lower i) <
        radius (commonPartitionCellRightKnotIndex upper lower i))
    (hgeometry : ∀ i : Fin ((StepBoundary.commonKnots upper lower).card - 1),
      lower.rightTrace (StepBoundary.commonPartitionGrid upper lower i.val) <
          innerLower i ∧
        innerLower i <
          center (commonPartitionCellLeftKnotIndex upper lower i) -
            radius (commonPartitionCellLeftKnotIndex upper lower i) ∧
        innerLower i <
          center (commonPartitionCellRightKnotIndex upper lower i) -
            radius (commonPartitionCellRightKnotIndex upper lower i) ∧
        center (commonPartitionCellLeftKnotIndex upper lower i) +
            radius (commonPartitionCellLeftKnotIndex upper lower i) <
          innerUpper i ∧
        center (commonPartitionCellRightKnotIndex upper lower i) +
            radius (commonPartitionCellRightKnotIndex upper lower i) <
          innerUpper i ∧
        innerUpper i <
          upper.rightTrace (StepBoundary.commonPartitionGrid upper lower i.val)) :
    (∏ i : Fin ((StepBoundary.commonKnots upper lower).card - 1),
      P (commonPartitionCellCoreReturnEvent (α := α) scale upper lower center radius
        innerLower innerUpper i)) ≤
      P ((Skorokhod.scalePath scale) ⁻¹' corridorSet upper lower) := by
  let events : Fin ((StepBoundary.commonKnots upper lower).card - 1) →
      Set (CadlagPath unitInterval ℝ) :=
    fun i => commonPartitionCellCoreReturnEvent (α := α) scale upper lower center radius
      innerLower innerUpper i
  have hfactor : P (⋂ i, events i) = ∏ i, P (events i) := by
    let cellScale : Fin ((StepBoundary.commonKnots upper lower).card - 1) → ℝ :=
      fun i => scale / commonPartitionCellSpatialScale α upper lower i
    let lo : Fin ((StepBoundary.commonKnots upper lower).card - 1) → ℝ :=
      fun i => innerLower i +
        radius (commonPartitionCellLeftKnotIndex upper lower i) -
        center (commonPartitionCellLeftKnotIndex upper lower i)
    let hi : Fin ((StepBoundary.commonKnots upper lower).card - 1) → ℝ :=
      fun i => innerUpper i -
        radius (commonPartitionCellLeftKnotIndex upper lower i) -
        center (commonPartitionCellLeftKnotIndex upper lower i)
    let coreLo : Fin ((StepBoundary.commonKnots upper lower).card - 1) → ℝ :=
      fun i => center (commonPartitionCellRightKnotIndex upper lower i) -
        center (commonPartitionCellLeftKnotIndex upper lower i) -
        (radius (commonPartitionCellRightKnotIndex upper lower i) -
          radius (commonPartitionCellLeftKnotIndex upper lower i)) / 2
    let coreHi : Fin ((StepBoundary.commonKnots upper lower).card - 1) → ℝ :=
      fun i => center (commonPartitionCellRightKnotIndex upper lower i) -
        center (commonPartitionCellLeftKnotIndex upper lower i) +
        (radius (commonPartitionCellRightKnotIndex upper lower i) -
          radius (commonPartitionCellLeftKnotIndex upper lower i)) / 2
    have h := measure_iInter_scaledNormalizedCellIocReturnEvent_eq_prod
      hP upper lower cellScale lo hi coreLo coreHi
    simpa [events, commonPartitionCellCoreReturnEvent, cellScale, lo, hi,
      coreLo, coreHi] using h
  let startZero : Set (CadlagPath unitInterval ℝ) := {f | f ⊥ = 0}
  have hstart : (⋂ i, events i) ∩ startZero ⊆
      (Skorokhod.scalePath scale) ⁻¹' corridorSet upper lower := by
    intro f hf
    have hevents : f ∈ ⋂ i, commonPartitionCellCoreReturnEvent (α := α)
        scale upper lower center radius innerLower innerUpper i := by
      simpa only [events] using hf.1
    exact inter_commonPartitionCellCoreReturnEvent_subset_corridorSet
      (α := α) (scale := scale) upper lower center radius innerLower innerUpper
      hcenter0 hradius0 hscale hcores hradiusStep hgeometry f hf.2 hevents
  have hstartMeasure : P ((⋂ i, events i) ∩ startZero) = P (⋂ i, events i) := by
    apply measure_congr
    filter_upwards [hP.ae_start_eq_zero] with f hf
    simp [startZero, hf]
  calc
    _ = P (⋂ i, events i) := hfactor.symm
    _ = P ((⋂ i, events i) ∩ startZero) := hstartMeasure.symm
    _ ≤ P ((Skorokhod.scalePath scale) ⁻¹' corridorSet upper lower) :=
      measure_mono hstart

end ProbabilityTheory.Process.SmallDeviation.Mogulskii
