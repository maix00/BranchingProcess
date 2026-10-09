/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Topology.Cadlag.Skorokhod.PathClass.StepCorridor.Partition.LowerCores
public import Probability.Process.Stable.SmallDeviation.PathClass.StepCorridor.Partition.Stable
public import Probability.Process.Stable.SmallDeviation.EscapeRate.Endpoint

/-!
# Stable endpoint-return kernels on partition cells

This module transfers the source's left-open, right-closed endpoint-return
events from a normalized nonuniform cell to a reference stable Lévy process.
The resulting kernel has the same escape rate as a centered range tube.
-/

open Filter MeasureTheory
open Skorokhod.PathClass.StepCorridor
open scoped NNReal Topology

@[expose] public section

namespace ProbabilityTheory

open Skorokhod.PathClass.StepCorridor

/-- A normalized cell path, multiplied by a positive scale, belongs to a
fixed open corridor with a left-open, right-closed terminal window. -/
def scaledNormalizedCellIocReturnEvent
    {α : ℝ} (upper lower : StepBoundary)
    (i : Fin ((StepBoundary.commonKnots upper lower).card - 1))
    (scale lo hi coreLo coreHi : ℝ) : Set (CadlagPath unitInterval ℝ) :=
  (fun f q => scale *
    normalizedCommonPartitionCellPath (α := α) upper lower i q f) ⁻¹'
      Skorokhod.rationalCoordinateCorridorIocReturnWithMargin
        lo hi coreLo coreHi

/-- The scaled normalized-cell event has the corresponding unit-time
stable-process probability. The path-law comparison uses all rational
coordinates, including the right endpoint required by the return window. -/
theorem measure_scaledNormalizedCellIocReturnEvent_eq
    {α scale : ℝ} {μ : Measure ℝ}
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    {Ω : Type*} [MeasurableSpace Ω]
    {X : ℝ≥0 → Ω → ℝ} {Q : Measure Ω} [IsProbabilityMeasure Q]
    (hP : IsStableClockProcessLaw α μ UnitInterval.clock P)
    (hX : IsStableLevyProcess α μ X Q)
    (hscale : 0 < scale)
    (upper lower : StepBoundary)
    (i : Fin ((StepBoundary.commonKnots upper lower).card - 1))
    (lo hi coreLo coreHi : ℝ) :
    P (scaledNormalizedCellIocReturnEvent (α := α)
        upper lower i scale lo hi coreLo coreHi) =
      Q (fullSegmentCorridorIocReturnEvent X 0 1
        (lo / scale) (hi / scale) (coreLo / scale) (coreHi / scale)) := by
  let scaleMap : (RationalCoordinate.UnitInterval → ℝ) →
      (RationalCoordinate.UnitInterval → ℝ) := fun f q => scale * f q
  have hscaleMap : Measurable scaleMap := by
    rw [measurable_pi_iff]
    intro q
    fun_prop
  have hcell := IsStableClockProcessLaw.identDistrib_normalizedCommonPartitionCellPath
    hP hX upper lower i
  have hcellScale := hcell.comp hscaleMap
  have hprob := hcellScale.measure_mem_eq
    (Skorokhod.measurableSet_rationalCoordinateCorridorIocReturnWithMargin
      lo hi coreLo coreHi)
  have hleft :
      ((scaleMap ∘ fun f q =>
        normalizedCommonPartitionCellPath (α := α) upper lower i q f) ⁻¹'
          Skorokhod.rationalCoordinateCorridorIocReturnWithMargin
            lo hi coreLo coreHi) =
        (fun f q => scale *
          normalizedCommonPartitionCellPath (α := α) upper lower i q f) ⁻¹'
          Skorokhod.rationalCoordinateCorridorIocReturnWithMargin
            lo hi coreLo coreHi := by
    ext f
    rfl
  have hright :
      ((scaleMap ∘ fun ω q => X (RationalCoordinate.toNNReal q) ω) ⁻¹'
          Skorokhod.rationalCoordinateCorridorIocReturnWithMargin
            lo hi coreLo coreHi) =
        (fun ω q => scale * X (RationalCoordinate.toNNReal q) ω) ⁻¹'
          Skorokhod.rationalCoordinateCorridorIocReturnWithMargin
            lo hi coreLo coreHi := by
    ext ω
    rfl
  rw [hleft, hright] at hprob
  have hprob' :
      P (scaledNormalizedCellIocReturnEvent (α := α)
          upper lower i scale lo hi coreLo coreHi) =
        Q ((fun ω q => scale * X (RationalCoordinate.toNNReal q) ω) ⁻¹'
          Skorokhod.rationalCoordinateCorridorIocReturnWithMargin
            lo hi coreLo coreHi) := by
    simpa [scaledNormalizedCellIocReturnEvent] using hprob
  have hstart : ∀ᵐ ω ∂Q, X 0 ω = 0 := hX.increments.ae_start_eq_zero
  have hscaleStart :
      Q ((fun ω q => scale * X (RationalCoordinate.toNNReal q) ω) ⁻¹'
          Skorokhod.rationalCoordinateCorridorIocReturnWithMargin
            lo hi coreLo coreHi) =
        Q ((fun ω q => scale *
            (X (RationalCoordinate.toNNReal q) ω - X 0 ω)) ⁻¹'
          Skorokhod.rationalCoordinateCorridorIocReturnWithMargin
            lo hi coreLo coreHi) := by
    apply measure_congr
    filter_upwards [hstart] with ω hω
    have hfun : (fun q => scale * X (RationalCoordinate.toNNReal q) ω) =
        (fun q => scale * (X (RationalCoordinate.toNNReal q) ω - X 0 ω)) := by
      funext q
      simp [hω]
    change ((fun q => scale * X (RationalCoordinate.toNNReal q) ω) ∈
        Skorokhod.rationalCoordinateCorridorIocReturnWithMargin
          lo hi coreLo coreHi) =
      ((fun q => scale * (X (RationalCoordinate.toNNReal q) ω - X 0 ω)) ∈
        Skorokhod.rationalCoordinateCorridorIocReturnWithMargin
          lo hi coreLo coreHi)
    rw [hfun]
  have hdivide :
      Q ((fun ω q => scale *
          (X (RationalCoordinate.toNNReal q) ω - X 0 ω)) ⁻¹'
        Skorokhod.rationalCoordinateCorridorIocReturnWithMargin
          lo hi coreLo coreHi) =
      Q ((fun ω q => X (RationalCoordinate.toNNReal q) ω - X 0 ω) ⁻¹'
        Skorokhod.rationalCoordinateCorridorIocReturnWithMargin
          (lo / scale) (hi / scale) (coreLo / scale) (coreHi / scale)) := by
    have hset :
        (fun ω q => scale * (X (RationalCoordinate.toNNReal q) ω - X 0 ω)) ⁻¹'
            Skorokhod.rationalCoordinateCorridorIocReturnWithMargin
              lo hi coreLo coreHi =
          (fun ω q => X (RationalCoordinate.toNNReal q) ω - X 0 ω) ⁻¹'
            Skorokhod.rationalCoordinateCorridorIocReturnWithMargin
              (lo / scale) (hi / scale) (coreLo / scale) (coreHi / scale) := by
      ext ω
      change (fun q => scale *
          (X (RationalCoordinate.toNNReal q) ω - X 0 ω)) ∈
            Skorokhod.rationalCoordinateCorridorIocReturnWithMargin
              lo hi coreLo coreHi ↔
        (fun q => X (RationalCoordinate.toNNReal q) ω - X 0 ω) ∈
          Skorokhod.rationalCoordinateCorridorIocReturnWithMargin
            (lo / scale) (hi / scale) (coreLo / scale) (coreHi / scale)
      exact (Skorokhod.mem_rationalCoordinateCorridorIocReturnWithMargin_smul_iff
        scale hscale _ lo hi coreLo coreHi)
    rw [hset]
  have hfull := measure_fullSegmentCorridorIocReturnEvent_eq_rational
    Q X 0 1 (lo / scale) (hi / scale) (coreLo / scale) (coreHi / scale)
    hX.ae_cadlag
  calc
    _ = Q ((fun ω q => scale * X (RationalCoordinate.toNNReal q) ω) ⁻¹'
        Skorokhod.rationalCoordinateCorridorIocReturnWithMargin
          lo hi coreLo coreHi) := hprob'
    _ = Q ((fun ω q => scale *
        (X (RationalCoordinate.toNNReal q) ω - X 0 ω)) ⁻¹'
        Skorokhod.rationalCoordinateCorridorIocReturnWithMargin
          lo hi coreLo coreHi) := hscaleStart
    _ = Q ((fun ω q => X (RationalCoordinate.toNNReal q) ω - X 0 ω) ⁻¹'
        Skorokhod.rationalCoordinateCorridorIocReturnWithMargin
          (lo / scale) (hi / scale) (coreLo / scale) (coreHi / scale)) := hdivide
    _ = Q (fullSegmentCorridorIocReturnEvent X 0 1
        (lo / scale) (hi / scale) (coreLo / scale) (coreHi / scale)) := by
      simpa [zero_add, one_mul] using hfull

/-- A fixed endpoint-return kernel on a nonuniform partition cell has the
same logarithmic escape rate as the centered stable tube. -/
theorem HasStableProcessEscapeRate.tendsto_inv_rpow_mul_log_scaledNormalizedCellIocReturnEvent
    {α C : ℝ} {μ : Measure ℝ}
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hEscape : HasStableProcessEscapeRate α μ P C)
    {Ω : Type*} [MeasurableSpace Ω]
    {X : ℝ≥0 → Ω → ℝ} {Q : Measure Ω} [IsProbabilityMeasure Q]
    (hX : IsStableLevyProcess α μ X Q)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    (upper lower : StepBoundary)
    (i : Fin ((StepBoundary.commonKnots upper lower).card - 1))
    {radius d c b : ℝ}
    (hradius : 0 < radius)
    (hd : -1 < d ∧ d < 1) (hc : -1 < c) (hcb : c < b) (hb : b ≤ 1) :
    Tendsto
      (fun scale : ℝ => scale⁻¹ ^ α * Real.log
        ((P (scaledNormalizedCellIocReturnEvent (α := α) upper lower i scale
          (radius * (d - 1)) (radius * (d + 1))
          (radius * (d + c)) (radius * (d + b)))).toReal))
      atTop (𝓝 (C / radius ^ α)) := by
  have hbase := hEscape.tendsto_stableRangeLogRate_of_isStableLevyProcess hX
  have hrate := hX.tendsto_inv_rpow_mul_log_shiftedEndpointCorridorProbability
    hcdf hbase hd hc hcb hb hradius
  have heq : (fun scale : ℝ => scale⁻¹ ^ α * Real.log
      ((P (scaledNormalizedCellIocReturnEvent (α := α) upper lower i scale
        (radius * (d - 1)) (radius * (d + 1))
        (radius * (d + c)) (radius * (d + b)))).toReal)) =ᶠ[atTop]
      (fun scale : ℝ => scale⁻¹ ^ α * Real.log
        ((shiftedEndpointCorridorProbability Q X d c b
          (radius / scale)).toReal)) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with scale hscale
    have hprob := measure_scaledNormalizedCellIocReturnEvent_eq
      hEscape.isStableClockProcessLaw hX hscale upper lower i
      (radius * (d - 1)) (radius * (d + 1))
      (radius * (d + c)) (radius * (d + b))
    have hprob' :
      P (scaledNormalizedCellIocReturnEvent (α := α) upper lower i scale
          (radius * (d - 1)) (radius * (d + 1))
          (radius * (d + c)) (radius * (d + b))) =
          shiftedEndpointCorridorProbability Q X d c b (radius / scale) := by
      rw [hprob]
      unfold shiftedEndpointCorridorProbability
      congr 1
      all_goals congr 1 <;> field_simp
    rw [hprob']
  exact hrate.congr' heq.symm

/-- The endpoint-return kernel rate for arbitrary finite corridor bounds
containing the origin. Its value depends only on the corridor half-width; the
return window may be any left-open, right-closed subinterval of the corridor.
-/
theorem HasStableProcessEscapeRate.tendsto_inv_rpow_mul_log_scaledNormalizedCellIocReturnEvent_of_bounds
    {α C : ℝ} {μ : Measure ℝ}
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hEscape : HasStableProcessEscapeRate α μ P C)
    {Ω : Type*} [MeasurableSpace Ω]
    {X : ℝ≥0 → Ω → ℝ} {Q : Measure Ω} [IsProbabilityMeasure Q]
    (hX : IsStableLevyProcess α μ X Q)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    (upper lower : StepBoundary)
    (i : Fin ((StepBoundary.commonKnots upper lower).card - 1))
    {lo hi coreLo coreHi : ℝ}
    (hlo : lo < 0) (hhi : 0 < hi)
    (hcoreLo : lo < coreLo) (hcore : coreLo < coreHi)
    (hcoreHi : coreHi ≤ hi) :
    Tendsto
      (fun scale : ℝ => scale⁻¹ ^ α * Real.log
        ((P (scaledNormalizedCellIocReturnEvent (α := α) upper lower i scale
          lo hi coreLo coreHi)).toReal))
      atTop (𝓝 (C / (((hi - lo) / 2) ^ α))) := by
  let radius : ℝ := (hi - lo) / 2
  let d : ℝ := (hi + lo) / (hi - lo)
  let c : ℝ := coreLo / radius - d
  let b : ℝ := coreHi / radius - d
  have hwidth : 0 < hi - lo := by linarith
  have hradius : 0 < radius := by
    dsimp [radius]
    linarith
  have hd : -1 < d ∧ d < 1 := by
    constructor
    · dsimp [d]
      rw [lt_div_iff₀ hwidth]
      linarith
    · dsimp [d]
      rw [div_lt_iff₀ hwidth]
      linarith
  have hloEq : radius * (d - 1) = lo := by
    dsimp [radius, d]
    field_simp [ne_of_gt hwidth]
    ring
  have hhiEq : radius * (d + 1) = hi := by
    dsimp [radius, d]
    field_simp [ne_of_gt hwidth]
    ring
  have hcoreLoEq : radius * (d + c) = coreLo := by
    dsimp [c]
    calc
      radius * (d + (coreLo / radius - d)) = radius * (coreLo / radius) := by
        ring
      _ = coreLo := mul_div_cancel₀ coreLo hradius.ne'
  have hcoreHiEq : radius * (d + b) = coreHi := by
    dsimp [b]
    calc
      radius * (d + (coreHi / radius - d)) = radius * (coreHi / radius) := by
        ring
      _ = coreHi := mul_div_cancel₀ coreHi hradius.ne'
  have hc : -1 < c := by
    have hnumerator : (d - 1) * radius < coreLo := by
      calc
        (d - 1) * radius = radius * (d - 1) := by ring
        _ = lo := hloEq
        _ < coreLo := hcoreLo
    have hquot : d - 1 < coreLo / radius :=
      (lt_div_iff₀ hradius).2 hnumerator
    dsimp [c]
    linarith
  have hcb : c < b := by
    dsimp [c, b]
    have hdiv : coreLo / radius < coreHi / radius :=
      (div_lt_div_iff_of_pos_right hradius).2 hcore
    linarith
  have hb : b ≤ 1 := by
    have hnumerator : coreHi ≤ (d + 1) * radius := by
      calc
        coreHi ≤ hi := hcoreHi
        _ = radius * (d + 1) := hhiEq.symm
        _ = (d + 1) * radius := by ring
    have hquot : coreHi / radius ≤ d + 1 :=
      (div_le_iff₀ hradius).2 hnumerator
    dsimp [b]
    linarith
  have hrate :=
    ProbabilityTheory.HasStableProcessEscapeRate.tendsto_inv_rpow_mul_log_scaledNormalizedCellIocReturnEvent
      hEscape hX hcdf upper lower i hradius hd hc hcb hb
  have hevent : ∀ scale : ℝ,
      P (scaledNormalizedCellIocReturnEvent (α := α) upper lower i scale
        lo hi coreLo coreHi) =
      P (scaledNormalizedCellIocReturnEvent (α := α) upper lower i scale
        (radius * (d - 1)) (radius * (d + 1))
        (radius * (d + c)) (radius * (d + b))) := by
    intro scale
    rw [hloEq, hhiEq, hcoreLoEq, hcoreHiEq]
  have heq : (fun scale : ℝ => scale⁻¹ ^ α * Real.log
      ((P (scaledNormalizedCellIocReturnEvent (α := α) upper lower i scale
        lo hi coreLo coreHi)).toReal)) =ᶠ[atTop]
      (fun scale : ℝ => scale⁻¹ ^ α * Real.log
        ((P (scaledNormalizedCellIocReturnEvent (α := α) upper lower i scale
          (radius * (d - 1)) (radius * (d + 1))
          (radius * (d + c)) (radius * (d + b)))).toReal)) := by
    filter_upwards with scale
    rw [hevent]
  have hrate' := hrate.congr' heq.symm
  simpa [radius] using hrate'

/-- Reparametrize a unit-time endpoint kernel by the large scale of the
original, nonuniform partition cell. The resulting rate is multiplied by the
inverse `α`-power of the cell's spatial normalization. -/
theorem HasStableProcessEscapeRate.tendsto_inv_rpow_mul_log_scaledNormalizedCellIocReturnEvent_of_bounds_divScale
    {α C spatialScale : ℝ} {μ : Measure ℝ}
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hEscape : HasStableProcessEscapeRate α μ P C)
    {Ω : Type*} [MeasurableSpace Ω]
    {X : ℝ≥0 → Ω → ℝ} {Q : Measure Ω} [IsProbabilityMeasure Q]
    (hX : IsStableLevyProcess α μ X Q)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    (upper lower : StepBoundary)
    (i : Fin ((StepBoundary.commonKnots upper lower).card - 1))
    {lo hi coreLo coreHi : ℝ}
    (hlo : lo < 0) (hhi : 0 < hi)
    (hcoreLo : lo < coreLo) (hcore : coreLo < coreHi)
    (hcoreHi : coreHi ≤ hi)
    (hspatial : 0 < spatialScale) :
    Tendsto
      (fun scale : ℝ => scale⁻¹ ^ α * Real.log
        ((P (scaledNormalizedCellIocReturnEvent (α := α) upper lower i
          (scale / spatialScale) lo hi coreLo coreHi)).toReal))
      atTop (𝓝 (spatialScale ^ (-α) * (C / (((hi - lo) / 2) ^ α)))) := by
  have hrate :=
    ProbabilityTheory.HasStableProcessEscapeRate.tendsto_inv_rpow_mul_log_scaledNormalizedCellIocReturnEvent_of_bounds
      hEscape hX hcdf upper lower i hlo hhi hcoreLo hcore hcoreHi
  have hscale : Tendsto (fun scale : ℝ => scale / spatialScale) atTop atTop :=
    (tendsto_id : Tendsto (fun x : ℝ => x) atTop atTop).atTop_div_const hspatial
  have hcomp := hrate.comp hscale
  have heq : (fun scale : ℝ => scale⁻¹ ^ α * Real.log
      ((P (scaledNormalizedCellIocReturnEvent (α := α) upper lower i
        (scale / spatialScale) lo hi coreLo coreHi)).toReal)) =ᶠ[atTop]
      (fun scale : ℝ => spatialScale ^ (-α) *
        ((scale / spatialScale)⁻¹ ^ α * Real.log
          ((P (scaledNormalizedCellIocReturnEvent (α := α) upper lower i
            (scale / spatialScale) lo hi coreLo coreHi)).toReal))) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with scale hscale
    have hdivInv : (scale / spatialScale)⁻¹ = spatialScale / scale := by
      field_simp
    have hfactor : scale⁻¹ ^ α = spatialScale ^ (-α) *
        (spatialScale / scale) ^ α := by
      rw [Real.div_rpow hspatial.le hscale.le,
        Real.rpow_neg hspatial.le α,
        Real.inv_rpow hscale.le α]
      have hpos : 0 < spatialScale ^ α := Real.rpow_pos_of_pos hspatial α
      have hposScale : 0 < scale ^ α := Real.rpow_pos_of_pos hscale α
      field_simp
    rw [hdivInv, hfactor]
    ring
  have hscaled := (tendsto_const_nhds :
      Tendsto (fun _ : ℝ => spatialScale ^ (-α)) atTop
        (𝓝 (spatialScale ^ (-α)))).mul hcomp
  exact hscaled.congr' heq.symm

/-- The arbitrary-bound endpoint kernel on a common partition cell has the
source rate `C * cellLength / halfWidth^α` when the path is scaled in the
original time coordinate. -/
theorem HasStableProcessEscapeRate.tendsto_inv_rpow_mul_log_scaledNormalizedCellIocReturnEvent_of_cell
    {α C : ℝ} {μ : Measure ℝ}
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hEscape : HasStableProcessEscapeRate α μ P C)
    {Ω : Type*} [MeasurableSpace Ω]
    {X : ℝ≥0 → Ω → ℝ} {Q : Measure Ω} [IsProbabilityMeasure Q]
    (hX : IsStableLevyProcess α μ X Q)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    (upper lower : StepBoundary)
    (i : Fin ((StepBoundary.commonKnots upper lower).card - 1))
    {lo hi coreLo coreHi : ℝ}
    (hlo : lo < 0) (hhi : 0 < hi)
    (hcoreLo : lo < coreLo) (hcore : coreLo < coreHi)
    (hcoreHi : coreHi ≤ hi) (hα : 0 < α) :
    Tendsto
      (fun scale : ℝ => scale⁻¹ ^ α * Real.log
        ((P (scaledNormalizedCellIocReturnEvent (α := α) upper lower i
          (scale / commonPartitionCellSpatialScale α upper lower i)
          lo hi coreLo coreHi)).toReal))
      atTop (𝓝 (C * commonPartitionCellLength upper lower i /
        (((hi - lo) / 2) ^ α))) := by
  let length := commonPartitionCellLength upper lower i
  let spatialScale := commonPartitionCellSpatialScale α upper lower i
  let radius := (hi - lo) / 2
  have hlength : 0 < length := commonPartitionCellLength_pos upper lower i
  have hspatial : 0 < spatialScale :=
    commonPartitionCellSpatialScale_pos α upper lower i
  have hradius : 0 < radius := by
    dsimp [radius]
    linarith
  have hspatialPower : spatialScale ^ (-α) = length := by
    change (length ^ (-(1 / α))) ^ (-α) = length
    rw [← Real.rpow_mul hlength.le]
    have hexp : -(1 / α) * (-α) = 1 := by
      field_simp [ne_of_gt hα]
    rw [hexp, Real.rpow_one]
  have hrate :=
    ProbabilityTheory.HasStableProcessEscapeRate.tendsto_inv_rpow_mul_log_scaledNormalizedCellIocReturnEvent_of_bounds_divScale
      hEscape hX hcdf upper lower i hlo hhi hcoreLo hcore hcoreHi hspatial
  rw [hspatialPower] at hrate
  have hcoeff : length * (C / (radius ^ α)) = C * length / (radius ^ α) := by
    ring
  rw [hcoeff] at hrate
  simpa [length, radius, spatialScale] using hrate

end ProbabilityTheory

end
