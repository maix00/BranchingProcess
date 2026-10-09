/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Path.PathClass.StepCorridor.Probability.Partition.Independence
public import Probability.Process.Path.PathClass.StepCorridor.Probability.Partition.Range
public import Topology.Cadlag.Skorokhod.PathClass.StepCorridor.Partition.LowerCores
public import Probability.Process.Stable.FiniteDimensional
public import Probability.Process.Stable.PathLaw
public import Probability.Process.Stable.PathContinuity
public import Probability.Process.Stable.SmallDeviation.EscapeRate.PathLaw.Transfer
public import Probability.Process.Path.UnitInterval
public import Probability.Process.Path.Skorokhod.RationalTime
public import Probability.MeasureTheory.FiniteProduct

/-!
# Stable laws on nonuniform boundary cells

The cell process is translated to its left endpoint and rescaled by the
stable time-space factor. Its rational-coordinate law is the unit-time stable
process law, so a half-open closed range event can be bounded by a slightly
wider full stable tube using the fixed-time no-jump result.
-/

open Skorokhod.PathClass.StepCorridor
open ProbabilityTheory.Process.Path.PathClass.StepCorridor.Probability

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory


/-- Stable time-space normalization for one partition cell. -/
noncomputable def commonPartitionCellSpatialScale (α : ℝ)
    (upper lower : StepBoundary)
    (i : Fin ((StepBoundary.commonKnots upper lower).card - 1)) : ℝ :=
  commonPartitionCellLength upper lower i ^ (-(1 / α))

/-- The stable spatial normalization of a common partition cell is positive,
for every real stable index. -/
theorem commonPartitionCellSpatialScale_pos (α : ℝ)
    (upper lower : StepBoundary)
    (i : Fin ((StepBoundary.commonKnots upper lower).card - 1)) :
    0 < commonPartitionCellSpatialScale α upper lower i := by
  exact Real.rpow_pos_of_pos (commonPartitionCellLength_pos upper lower i) _

/-- A common boundary cell, translated to its left endpoint and normalized
to unit stable time. -/
noncomputable def normalizedCommonPartitionCellPath
    {α : ℝ} (upper lower : StepBoundary)
    (i : Fin ((StepBoundary.commonKnots upper lower).card - 1)) :
    RationalCoordinate.UnitInterval → CadlagPath unitInterval ℝ → ℝ := by
  let left := StepBoundary.commonPartitionGrid upper lower i.val
  let scale := commonPartitionCellSpatialScale α upper lower i
  let φ : RationalCoordinate.UnitInterval → unitInterval := fun q =>
    StepBoundary.commonPartitionCellTime upper lower i.val
      (RationalCoordinate.toUnitInterval q)
  exact fun q f => scale * (f (φ q) - f left)

/-- On each positive-length cell of the common finite partition, the
translated and normalized coordinate path has the unit stable clock. -/
theorem IsStableClockProcessLaw.hasStableClockIncrements_normalizedCommonPartitionCellPath
    {α : ℝ} {μ : Measure ℝ}
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hP : IsStableClockProcessLaw α μ UnitInterval.clock P)
    (upper lower : StepBoundary)
    (i : Fin ((StepBoundary.commonKnots upper lower).card - 1)) :
    HasStableClockIncrements α μ
      (fun q : RationalCoordinate.UnitInterval => (RationalCoordinate.toNNReal q : ℝ))
      (normalizedCommonPartitionCellPath (α := α) upper lower i) P := by
  let left := StepBoundary.commonPartitionGrid upper lower i.val
  let right := StepBoundary.commonPartitionGrid upper lower (i.val + 1)
  let length : ℝ := (right : ℝ) - (left : ℝ)
  let scale : ℝ := length ^ (-(1 / α))
  let φ : RationalCoordinate.UnitInterval → unitInterval := fun q =>
    StepBoundary.commonPartitionCellTime upper lower i.val
      (RationalCoordinate.toUnitInterval q)
  have hlength : 0 < length := by
    have hlt : (left : ℝ) < (right : ℝ) := by
      dsimp [left, right]
      exact_mod_cast StepBoundary.commonPartitionGrid_strictSucc upper lower i.val i.isLt
    exact sub_pos.mpr hlt
  have htoMono : Monotone RationalCoordinate.toUnitInterval := by
    intro q r hqr
    change ((q : ℚ) : ℝ) ≤ ((r : ℚ) : ℝ)
    exact_mod_cast hqr
  have hφmono : Monotone φ :=
    (StepBoundary.monotone_commonPartitionCellTime upper lower i.val).comp htoMono
  have hφbot : φ ⊥ = left := by
    have hqbot : RationalCoordinate.toUnitInterval ⊥ = (⊥ : unitInterval) := by
      apply Subtype.ext
      norm_num [RationalCoordinate.toUnitInterval]
    change StepBoundary.commonPartitionCellTime upper lower i.val
      (RationalCoordinate.toUnitInterval ⊥) = left
    rw [hqbot, StepBoundary.commonPartitionCellTime_bot]
  have hclockPoint (q : RationalCoordinate.UnitInterval) :
      UnitInterval.clock (φ q) = (left : ℝ) +
        (RationalCoordinate.toNNReal q : ℝ) * length := by
    change (StepBoundary.commonPartitionCellTime upper lower i.val
      (RationalCoordinate.toUnitInterval q) : ℝ) = _
    rw [StepBoundary.coe_commonPartitionCellTime]
    simp [left, right, length, RationalCoordinate.toNNReal_coe]
  have htranslated :=
    (show HasStableClockIncrements α μ UnitInterval.clock
      cadlagPathProcess P from hP).translate_comp_time φ hφmono
  let oldClock : RationalCoordinate.UnitInterval → ℝ := fun q =>
    UnitInterval.clock (φ q) - UnitInterval.clock (φ ⊥)
  let newClock : RationalCoordinate.UnitInterval → ℝ := fun q =>
    (RationalCoordinate.toNNReal q : ℝ)
  have hnewMono : Monotone newClock := by
    intro q r hqr
    change (RationalCoordinate.toNNReal q : ℝ) ≤ (RationalCoordinate.toNNReal r : ℝ)
    exact_mod_cast RationalCoordinate.monotone_toNNReal hqr
  have hnewBot : newClock ⊥ = 0 := by
    change (RationalCoordinate.toNNReal ⊥ : ℝ) = 0
    simp [RationalCoordinate.toNNReal_bot]
  have holdClock (q : RationalCoordinate.UnitInterval) :
      oldClock q = length * newClock q := by
    change UnitInterval.clock (φ q) - UnitInterval.clock (φ ⊥) =
      length * (RationalCoordinate.toNNReal q : ℝ)
    rw [hclockPoint q, hclockPoint ⊥]
    simp [RationalCoordinate.toNNReal_bot]
    ring
  have hcompat : ∀ s t, s ≤ t →
      (newClock t - newClock s) ^ (1 / α) =
        scale * (oldClock t - oldClock s) ^ (1 / α) := by
    intro s t hst
    have hnonneg : 0 ≤ newClock t - newClock s :=
      sub_nonneg.mpr (hnewMono hst)
    rw [holdClock t, holdClock s]
    have hfactor : length * newClock t - length * newClock s =
        length * (newClock t - newClock s) := by ring
    rw [hfactor, Real.mul_rpow hlength.le hnonneg]
    dsimp [scale]
    rw [Real.rpow_neg hlength.le]
    have hpos : 0 < length ^ (1 / α) :=
      Real.rpow_pos_of_pos hlength _
    field_simp
  have hscaled := htranslated.map_spaceScale scale newClock hnewMono hnewBot hcompat
  simpa [normalizedCommonPartitionCellPath, commonPartitionCellSpatialScale,
    commonPartitionCellLength, left, right, length, scale, φ,
    hφbot, newClock, oldClock, cadlagPathProcess] using hscaled

/-- The normalized path on any common partition cell has the same rational
coordinate law as a unit-time stable Lévy path. -/
theorem IsStableClockProcessLaw.identDistrib_normalizedCommonPartitionCellPath
    {α : ℝ} {μ : Measure ℝ}
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    {Ω : Type*} [MeasurableSpace Ω]
    {X : ℝ≥0 → Ω → ℝ} {Q : Measure Ω} [IsProbabilityMeasure Q]
    (hP : IsStableClockProcessLaw α μ UnitInterval.clock P)
    (hX : IsStableLevyProcess α μ X Q)
    (upper lower : StepBoundary)
    (i : Fin ((StepBoundary.commonKnots upper lower).card - 1)) :
    IdentDistrib
      (fun f q => normalizedCommonPartitionCellPath (α := α) upper lower i q f)
      (fun ω q => X (RationalCoordinate.toNNReal q) ω) P Q := by
  have hcell := IsStableClockProcessLaw.hasStableClockIncrements_normalizedCommonPartitionCellPath
    hP upper lower i
  have hXgrid0 := hX.increments.comp_time RationalCoordinate.toNNReal
    RationalCoordinate.monotone_toNNReal RationalCoordinate.toNNReal_bot
  have hXgrid : HasStableClockIncrements α μ
      (fun q => (RationalCoordinate.toNNReal q : ℝ))
      (fun q ω => X (RationalCoordinate.toNNReal q) ω) Q := by
    convert hXgrid0 using 1
  exact hcell.process_identDistrib_of_aemeasurable hXgrid
    (AEMeasurable.of_eval fun q => hcell.aemeasurable_eval q)
    (AEMeasurable.of_eval fun q => hXgrid.aemeasurable_eval q)

/-- A strict-corridor path event on a nonuniform cell is bounded by the
slightly wider unit-time stable range tube. The proof first removes the
random starting position by using pairwise range differences. At the right
endpoint, fixed-time continuity of the stable process extends the half-open
closed bound to the full range before it is enlarged to an open tube. -/
theorem measure_commonPartitionCellRangeEvent_le_rationalHorizonTube
    {α : ℝ} {μ : Measure ℝ}
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    {Ω : Type*} [MeasurableSpace Ω]
    {X : ℝ≥0 → Ω → ℝ} {Q : Measure Ω} [IsProbabilityMeasure Q]
    (hP : IsStableClockProcessLaw α μ UnitInterval.clock P)
    (hX : IsStableLevyProcess α μ X Q)
    (upper lower : StepBoundary)
    (i : Fin ((StepBoundary.commonKnots upper lower).card - 1))
    (width margin : ℝ) (hmargin : 0 < margin) :
    P (commonPartitionCellRangeEvent
        (X := fun t (f : CadlagPath unitInterval ℝ) => f t)
        upper lower i width) ≤
      Q (rationalHorizonTubeEvent X 1
        (commonPartitionCellSpatialScale α upper lower i * width + margin)) := by
  let scale := commonPartitionCellSpatialScale α upper lower i
  let observation : CadlagPath unitInterval ℝ → CellInteriorCoordinate → ℝ :=
    fun f q => normalizedCommonPartitionCellPath (α := α) upper lower i q.val f
  let reference : Ω → CellInteriorCoordinate → ℝ :=
    fun ω q => X (RationalCoordinate.toNNReal q.val) ω
  let fullReference : Ω → RationalCoordinate.UnitInterval → ℝ :=
    fun ω q => X (RationalCoordinate.toNNReal q) ω
  let restrict : (RationalCoordinate.UnitInterval → ℝ) →
      (CellInteriorCoordinate → ℝ) := fun g q => g q.val
  have hscalePos : 0 < scale := by
    exact commonPartitionCellSpatialScale_pos α upper lower i
  have hrestrict : Measurable restrict := by
    rw [measurable_pi_iff]
    intro q
    exact measurable_pi_apply q.val
  have hident := IsStableClockProcessLaw.identDistrib_normalizedCommonPartitionCellPath
    hP hX upper lower i
  have hidentInterior := hident.comp hrestrict
  have hprob :
      P (observation ⁻¹' commonPartitionCellRangeBound (scale * width)) =
        Q (reference ⁻¹' commonPartitionCellRangeBound (scale * width)) := by
    have hmeasure := hidentInterior.measure_mem_eq
      (measurableSet_commonPartitionCellRangeBound (scale * width))
    simpa [observation, reference, restrict, Function.comp_def] using hmeasure
  have hrawSubset :
      commonPartitionCellRangeEvent
        (X := fun t (f : CadlagPath unitInterval ℝ) => f t)
        upper lower i width ⊆
      observation ⁻¹' commonPartitionCellRangeBound (scale * width) := by
    intro f hf
    change ∀ s t : CellInteriorCoordinate,
      |commonPartitionCellPath
          (X := fun t (f : CadlagPath unitInterval ℝ) => f t)
          upper lower i f s - commonPartitionCellPath
          (X := fun t (f : CadlagPath unitInterval ℝ) => f t)
          upper lower i f t| ≤ width at hf
    change ∀ s t : CellInteriorCoordinate,
      |observation f s - observation f t| ≤ scale * width
    intro s t
    have hscaleAbs : |observation f s - observation f t| =
        scale * |commonPartitionCellPath
          (X := fun t (f : CadlagPath unitInterval ℝ) => f t)
          upper lower i f s - commonPartitionCellPath
          (X := fun t (f : CadlagPath unitInterval ℝ) => f t) upper lower i f t| := by
      change |scale * commonPartitionCellPath
          (X := fun t (f : CadlagPath unitInterval ℝ) => f t)
          upper lower i f s - scale * commonPartitionCellPath
          (X := fun t (f : CadlagPath unitInterval ℝ) => f t)
          upper lower i f t| = _
      rw [← mul_sub, abs_mul, abs_of_pos hscalePos]
    rw [hscaleAbs]
    exact mul_le_mul_of_nonneg_left (hf s t) hscalePos.le
  have hinteriorFull :
      Q (reference ⁻¹' commonPartitionCellRangeBound (scale * width)) ≤
        Q (fullReference ⁻¹' Skorokhod.rationalCoordinateOscillationLe
          (scale * width)) := by
    apply measure_mono_ae
    filter_upwards [hX.ae_rationalInteriorOscillationLe_implies_rationalCoordinateOscillationLe
      (scale * width)] with ω hendpoint
    intro hlocal
    change ∀ s t : RationalCoordinate.UnitInterval,
      |X (RationalCoordinate.toNNReal s) ω - X (RationalCoordinate.toNNReal t) ω| ≤ scale * width
    apply hendpoint
    intro s t hs ht
    exact hlocal ⟨s, hs⟩ ⟨t, ht⟩
  have hfullOpen :
      Q (fullReference ⁻¹' Skorokhod.rationalCoordinateOscillationLe
        (scale * width)) ≤
      Q (rationalHorizonTubeEvent X 1 (scale * width + margin)) := by
    apply measure_mono
    intro ω hω
    change (fun q => X (1 * RationalCoordinate.toNNReal q) ω) ∈
      Skorokhod.rationalCoordinateOscillationTube (scale * width + margin)
    simpa [one_mul, rationalHorizonTubeEvent, rationalHorizonProcess] using
      Skorokhod.rationalCoordinateOscillationLe_subset_tube
        (scale * width) margin hmargin hω
  calc
    P (commonPartitionCellRangeEvent
        (X := fun t (f : CadlagPath unitInterval ℝ) => f t)
        upper lower i width) ≤
      P (observation ⁻¹' commonPartitionCellRangeBound (scale * width)) :=
        measure_mono hrawSubset
    _ = Q (reference ⁻¹' commonPartitionCellRangeBound (scale * width)) := hprob
    _ ≤ Q (fullReference ⁻¹' Skorokhod.rationalCoordinateOscillationLe
        (scale * width)) := hinteriorFull
    _ ≤ Q (rationalHorizonTubeEvent X 1 (scale * width + margin)) := hfullOpen

/-- Any event forcing a closed range bound on each selected partition cell
is bounded by the product of the corresponding slightly enlarged stable
range tubes. Independent increments factor the half-open cells; translation,
stable scaling, and fixed-time no-jump transfer each factor to unit time. -/
theorem measure_set_le_stableProcessTubeProduct_of_rangeBounds
    {α : ℝ} {μ : Measure ℝ}
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    {Ω : Type*} [MeasurableSpace Ω]
    {X : ℝ≥0 → Ω → ℝ} {Q : Measure Ω} [IsProbabilityMeasure Q]
    (hP : IsStableClockProcessLaw α μ UnitInterval.clock P)
    (hX : IsStableLevyProcess α μ X Q)
    (upper lower : StepBoundary)
    (s : Finset (Fin ((StepBoundary.commonKnots upper lower).card - 1)))
    (G : Set (CadlagPath unitInterval ℝ))
    (width : Fin ((StepBoundary.commonKnots upper lower).card - 1) → ℝ)
    (hsubset : G ⊆ ⋂ i ∈ s, commonPartitionCellRangeEvent
      (X := fun t (f : CadlagPath unitInterval ℝ) => f t)
      upper lower i (width i))
    (margin : Fin ((StepBoundary.commonKnots upper lower).card - 1) → ℝ)
    (hmargin : ∀ i ∈ s, 0 < margin i) :
    P G ≤
      ∏ i ∈ s, P (stableProcessTube
        ((commonPartitionCellSpatialScale α upper lower i * width i + margin i) / 2)) := by
  let hbase : HasStableClockIncrements α μ UnitInterval.clock
      cadlagPathProcess P := hP
  have hindep := HasIndepIncrements.iIndepFun_commonStepBoundaryInteriorCells
    hbase.indepIncrements (fun t => hbase.aemeasurable_eval t) upper lower
  have hproduct := measure_biInter_commonPartitionCellRangeEvent_eq_prod
    hindep s width
  have hfactor : ∀ i ∈ s,
      P (commonPartitionCellRangeEvent
        (X := fun t (f : CadlagPath unitInterval ℝ) => f t)
        upper lower i (width i)) ≤
      P (stableProcessTube
        ((commonPartitionCellSpatialScale α upper lower i * width i +
          margin i) / 2)) := by
    intro i hiMem
    let tubeWidth := commonPartitionCellSpatialScale α upper lower i * width i
      + margin i
    have hlocal := measure_commonPartitionCellRangeEvent_le_rationalHorizonTube
      hP hX upper lower i (width i) (margin i) (hmargin i hiMem)
    have hbridge : P (stableProcessTube (tubeWidth / 2)) =
        Q (rationalHorizonTubeEvent X 1 tubeWidth) := by
      have hprob := hP.measure_stableProcessTube_eq_rationalRangeProbability
        hX (tubeWidth / 2)
      have hwidthEq : 2 * (tubeWidth / 2) = tubeWidth := by ring
      simpa [ProbabilityTheory.rationalRangeProbability, hwidthEq] using hprob
    exact hlocal.trans_eq hbridge.symm
  calc
    P G ≤ P (⋂ i ∈ s, commonPartitionCellRangeEvent
        (X := fun t (f : CadlagPath unitInterval ℝ) => f t)
        upper lower i (width i)) := measure_mono hsubset
    _ = ∏ i ∈ s, P (commonPartitionCellRangeEvent
        (X := fun t (f : CadlagPath unitInterval ℝ) => f t)
        upper lower i (width i)) := hproduct
    _ ≤ ∏ i ∈ s, P (stableProcessTube
        ((commonPartitionCellSpatialScale α upper lower i * width i +
          margin i) / 2)) := by
      apply Finset.prod_le_prod
      intro i hiMem
      exact hfactor i hiMem

/-- The strict step-corridor probability is bounded by the product of the
slightly enlarged stable-process range tubes associated to its finite-width
partition cells. Cells with an infinite boundary are omitted. -/
theorem measure_corridorSet_le_stableProcessTubeProduct
    {α : ℝ} {μ : Measure ℝ}
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    {Ω : Type*} [MeasurableSpace Ω]
    {X : ℝ≥0 → Ω → ℝ} {Q : Measure Ω} [IsProbabilityMeasure Q]
    (hP : IsStableClockProcessLaw α μ UnitInterval.clock P)
    (hX : IsStableLevyProcess α μ X Q)
    (upper lower : StepBoundary)
    (s : Finset (Fin ((StepBoundary.commonKnots upper lower).card - 1)))
    (lo hi : Fin ((StepBoundary.commonKnots upper lower).card - 1) → ℝ)
    (hlower : ∀ i ∈ s, lower.rightTrace
      (StepBoundary.commonPartitionGrid upper lower i.val) = (lo i : EReal))
    (hupper : ∀ i ∈ s, upper.rightTrace
      (StepBoundary.commonPartitionGrid upper lower i.val) = (hi i : EReal))
    (hwidth : ∀ i ∈ s, lo i < hi i)
    (margin : ℝ) (hmargin : 0 < margin) :
    P (corridorSet upper lower) ≤
      ∏ i ∈ s, P (stableProcessTube
        ((commonPartitionCellSpatialScale α upper lower i * (hi i - lo i) +
          margin) / 2)) := by
  simpa using measure_set_le_stableProcessTubeProduct_of_rangeBounds
    hP hX upper lower s (corridorSet upper lower) (fun i => hi i - lo i)
    (corridorSet_subset_biInter_commonPartitionCellRangeEvents
      upper lower s lo hi hlower hupper hwidth) (fun _ => margin)
    (by intro i hiMem; exact hmargin)

end ProbabilityTheory

end
