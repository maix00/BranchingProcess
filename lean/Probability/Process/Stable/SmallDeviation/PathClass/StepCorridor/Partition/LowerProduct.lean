/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Stable.SmallDeviation.PathClass.StepCorridor.Partition.LowerKernel
public import Probability.Process.Path.PathClass.StepCorridor.Probability.Partition.Independence

/-!
# Product lower kernels on a finite boundary partition

The normalized translated paths on adjacent cells remain mutually
independent. Consequently, finite intersections of endpoint-return kernel
events factor exactly, including when each cell has its own scale and return
window.
-/

open MeasureTheory
open ProbabilityTheory.Process.Path.PathClass.StepCorridor.Probability
open scoped NNReal

@[expose] public section

namespace ProbabilityTheory

open Skorokhod.PathClass.StepCorridor

/-- Independent normalized cell paths, each multiplied by its own spatial
scale. This is the family of local paths used by the lower partition bound.
-/
theorem IsStableClockProcessLaw.iIndepFun_scaledNormalizedCommonPartitionCellPaths
    {α : ℝ} {μ : Measure ℝ}
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hP : IsStableClockProcessLaw α μ UnitInterval.clock P)
    (upper lower : StepBoundary)
    (scale : Fin ((StepBoundary.commonKnots upper lower).card - 1) → ℝ) :
    iIndepFun
      (fun (i : Fin ((StepBoundary.commonKnots upper lower).card - 1))
          (f : CadlagPath unitInterval ℝ) q =>
        scale i * normalizedCommonPartitionCellPath (α := α)
          upper lower i q f) P := by
  let hbase : HasStableClockIncrements α μ UnitInterval.clock
      cadlagPathProcess P := hP
  have hindepRaw := HasIndepIncrements.iIndepFun_commonStepBoundaryCells
    hbase.indepIncrements (fun t => hbase.aemeasurable_eval t) upper lower
  have hspatialMeas : ∀ i, Measurable (fun path :
      RationalCoordinate.UnitInterval → ℝ =>
        fun q => commonPartitionCellSpatialScale α upper lower i * path q) := by
    intro i
    rw [measurable_pi_iff]
    intro q
    fun_prop
  have hindepNormalized := hindepRaw.comp
    (fun i path => fun q => commonPartitionCellSpatialScale α upper lower i * path q)
    hspatialMeas
  have hscaleMeas : ∀ i, Measurable (fun path :
      RationalCoordinate.UnitInterval → ℝ => fun q => scale i * path q) := by
    intro i
    rw [measurable_pi_iff]
    intro q
    fun_prop
  have hindepScaled := hindepNormalized.comp
    (fun i path => fun q => scale i * path q) hscaleMeas
  convert hindepScaled using 1
  funext i f q
  simp [normalizedCommonPartitionCellPath, commonPartitionCellSpatialScale,
    commonPartitionCellLength, StepBoundary.commonPartitionCellTime,
    Function.comp_def]

/-- Endpoint-return events on the finitely many normalized partition cells
factor as a product under the stable clock path law. -/
theorem measure_iInter_scaledNormalizedCellIocReturnEvent_eq_prod
    {α : ℝ} {μ : Measure ℝ}
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hP : IsStableClockProcessLaw α μ UnitInterval.clock P)
    (upper lower : StepBoundary)
    (scale lo hi coreLo coreHi :
      Fin ((StepBoundary.commonKnots upper lower).card - 1) → ℝ) :
    P (⋂ i, scaledNormalizedCellIocReturnEvent (α := α)
        upper lower i (scale i) (lo i) (hi i) (coreLo i) (coreHi i)) =
      ∏ i, P (scaledNormalizedCellIocReturnEvent (α := α)
        upper lower i (scale i) (lo i) (hi i) (coreLo i) (coreHi i)) := by
  let cellPath := fun (i : Fin ((StepBoundary.commonKnots upper lower).card - 1))
      (f : CadlagPath unitInterval ℝ) (q : RationalCoordinate.UnitInterval) =>
        scale i * normalizedCommonPartitionCellPath (α := α) upper lower i q f
  have hindep :=
    ProbabilityTheory.IsStableClockProcessLaw.iIndepFun_scaledNormalizedCommonPartitionCellPaths
      hP upper lower scale
  have hfactor := hindep.measure_inter_preimage_eq_mul
    (Finset.univ : Finset (Fin ((StepBoundary.commonKnots upper lower).card - 1)))
    (sets := fun i => Skorokhod.rationalCoordinateCorridorIocReturnWithMargin
      (lo i) (hi i) (coreLo i) (coreHi i))
    (by
      intro i hiI
      exact Skorokhod.measurableSet_rationalCoordinateCorridorIocReturnWithMargin
        (lo i) (hi i) (coreLo i) (coreHi i))
  simpa [cellPath, scaledNormalizedCellIocReturnEvent] using hfactor

end ProbabilityTheory

end
