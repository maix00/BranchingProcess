/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Path.PathClass.StepCorridor.Probability.Partition.Independence
public import Probability.Process.Stable.SmallDeviation.PathClass.StepCorridor.Partition.Core.Stable

/-!
# Independence of normalized stable partition paths

Independent increments make the translated paths on disjoint cells
independent. Applying the cell-specific stable spatial scaling and any
additional positive scale preserves this independence.

## Public declarations

* `IsStableClockProcessLaw.iIndepFun_scaledNormalizedCommonPartitionCellPaths`
  states that the family `q ↦ scale i * normalizedCommonPartitionCellPath i q`
  is mutually independent under the stable clock path law.
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
    (hP : IsStableClockProcessLaw α μ unitInterval.clock P)
    (upper lower : StepBoundary)
    (scale : Fin ((StepBoundary.commonKnots upper lower).card - 1) → ℝ) :
    iIndepFun
      (fun (i : Fin ((StepBoundary.commonKnots upper lower).card - 1))
          (f : CadlagPath unitInterval ℝ) q =>
        scale i * normalizedCommonPartitionCellPath (α := α)
          upper lower i q f) P := by
  let hbase : HasStableClockIncrements α μ unitInterval.clock
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


end ProbabilityTheory

end
