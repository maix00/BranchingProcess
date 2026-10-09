/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Stable.SmallDeviation.Mogulskii.PathClass.Partition.Stable
public import Topology.Cadlag.Skorokhod.Scaling

/-!
# Scaled step corridors on common partition cells

Multiplying a path by a positive factor divides each corridor width seen by
the original path by that factor. This deterministic bridge lets the stable
cell estimate apply directly to the process small-deviation event.
-/

@[expose] public section

open Filter MeasureTheory
open scoped NNReal Topology

namespace ProbabilityTheory

open ProbabilityTheory.Process.SmallDeviation.Mogulskii

/-- Scaling a path into a finite step corridor forces each selected cell's
range diameter to be at most the corresponding corridor width divided by
the scale. -/
theorem scalePath_preimage_corridorSet_subset_commonPartitionCellRangeEvent
    {scale : ℝ} (hscale : 0 < scale)
    (upper lower : StepBoundary)
    (i : Fin ((StepBoundary.commonKnots upper lower).card - 1))
    {lo hi : ℝ}
    (hlower : lower.rightTrace
      (StepBoundary.commonPartitionGrid upper lower i.val) = (lo : EReal))
    (hupper : upper.rightTrace
      (StepBoundary.commonPartitionGrid upper lower i.val) = (hi : EReal))
    (hwidth : lo < hi) :
    (Skorokhod.scalePath scale) ⁻¹' corridorSet upper lower ⊆
      commonPartitionCellRangeEvent
        (X := fun t (f : CadlagPath unitInterval ℝ) => f t)
        upper lower i ((hi - lo) / scale) := by
  intro f hf
  have hrange := corridorSet_subset_commonPartitionCellRangeEvent_of_finiteBounds
    upper lower i hlower hupper hwidth hf
  change ∀ s t : CellInteriorCoordinate,
    |commonPartitionCellPath
        (X := fun t (f : CadlagPath unitInterval ℝ) => f t)
        upper lower i (Skorokhod.scalePath scale f) s -
      commonPartitionCellPath
        (X := fun t (f : CadlagPath unitInterval ℝ) => f t)
        upper lower i (Skorokhod.scalePath scale f) t| ≤ hi - lo at hrange
  change ∀ s t : CellInteriorCoordinate,
    |commonPartitionCellPath
        (X := fun t (f : CadlagPath unitInterval ℝ) => f t)
        upper lower i f s -
      commonPartitionCellPath
        (X := fun t (f : CadlagPath unitInterval ℝ) => f t) upper lower i f t| ≤
      (hi - lo) / scale
  let τ (q : CellInteriorCoordinate) :=
    StepBoundary.commonPartitionCellTime upper lower i.val
      (RationalCoordinate.toUnitInterval q.val)
  intro s t
  have hscaledDiff :
      commonPartitionCellPath
          (X := fun t (f : CadlagPath unitInterval ℝ) => f t)
          upper lower i (Skorokhod.scalePath scale f) s -
        commonPartitionCellPath
          (X := fun t (f : CadlagPath unitInterval ℝ) => f t)
          upper lower i (Skorokhod.scalePath scale f) t =
        scale * (f (τ s) - f (τ t)) := by
    simp [commonPartitionCellPath, Skorokhod.scalePath_apply, τ]
    ring
  have hrawDiff :
      commonPartitionCellPath
          (X := fun t (f : CadlagPath unitInterval ℝ) => f t)
          upper lower i f s -
        commonPartitionCellPath
          (X := fun t (f : CadlagPath unitInterval ℝ) => f t) upper lower i f t =
        f (τ s) - f (τ t) := by
    simp [commonPartitionCellPath, τ]
  have hmul : scale * |f (τ s) - f (τ t)| ≤ hi - lo := by
    have h := hrange s t
    rw [hscaledDiff, abs_mul, abs_of_pos hscale] at h
    exact h
  rw [hrawDiff]
  exact (le_div_iff₀ hscale).2 (by simpa [mul_comm] using hmul)

/-- The probability of a positively scaled step corridor is bounded by the
product of the stable tubes obtained from its finite cell widths. -/
theorem measure_scalePath_preimage_corridorSet_le_stableProcessTubeProduct
    {α scale : ℝ} {μ : Measure ℝ}
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    {Ω : Type*} [MeasurableSpace Ω]
    {X : ℝ≥0 → Ω → ℝ} {Q : Measure Ω} [IsProbabilityMeasure Q]
    (hP : IsStableClockProcessLaw α μ unitIntervalClock P)
    (hX : IsStableLevyProcess α μ X Q)
    (hscale : 0 < scale)
    (upper lower : StepBoundary)
    (s : Finset (Fin ((StepBoundary.commonKnots upper lower).card - 1)))
    (lo hi : Fin ((StepBoundary.commonKnots upper lower).card - 1) → ℝ)
    (hlower : ∀ i ∈ s, lower.rightTrace
      (StepBoundary.commonPartitionGrid upper lower i.val) = (lo i : EReal))
    (hupper : ∀ i ∈ s, upper.rightTrace
      (StepBoundary.commonPartitionGrid upper lower i.val) = (hi i : EReal))
    (hwidth : ∀ i ∈ s, lo i < hi i)
    (margin : Fin ((StepBoundary.commonKnots upper lower).card - 1) → ℝ)
    (hmargin : ∀ i ∈ s, 0 < margin i) :
    P ((Skorokhod.scalePath scale) ⁻¹' corridorSet upper lower) ≤
      ∏ i ∈ s, P (stableProcessTube
        ((commonPartitionCellSpatialScale α upper lower i *
          ((hi i - lo i) / scale) + margin i) / 2)) := by
  apply measure_set_le_stableProcessTubeProduct_of_rangeBounds
    hP hX upper lower s _ (fun i => (hi i - lo i) / scale) ?_ margin hmargin
  intro f hf
  simp only [Set.mem_iInter]
  intro i hiMem
  exact scalePath_preimage_corridorSet_subset_commonPartitionCellRangeEvent
    hscale upper lower i (hlower i hiMem) (hupper i hiMem) (hwidth i hiMem) hf

/-- A relative enlargement of each normalized cell range gives tube radii
`rᵢ / scale`, with `rᵢ` independent of the scaling parameter. This is the
form that can be sent directly through the stable escape-rate limit. -/
theorem measure_scalePath_preimage_corridorSet_le_stableProcessTubeProduct_of_relativeEnlargement
    {α scale ε : ℝ} {μ : Measure ℝ}
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    {Ω : Type*} [MeasurableSpace Ω]
    {X : ℝ≥0 → Ω → ℝ} {Q : Measure Ω} [IsProbabilityMeasure Q]
    (hP : IsStableClockProcessLaw α μ unitIntervalClock P)
    (hX : IsStableLevyProcess α μ X Q)
    (hscale : 0 < scale) (hε : 0 < ε)
    (upper lower : StepBoundary)
    (s : Finset (Fin ((StepBoundary.commonKnots upper lower).card - 1)))
    (lo hi : Fin ((StepBoundary.commonKnots upper lower).card - 1) → ℝ)
    (hlower : ∀ i ∈ s, lower.rightTrace
      (StepBoundary.commonPartitionGrid upper lower i.val) = (lo i : EReal))
    (hupper : ∀ i ∈ s, upper.rightTrace
      (StepBoundary.commonPartitionGrid upper lower i.val) = (hi i : EReal))
    (hwidth : ∀ i ∈ s, lo i < hi i) :
    P ((Skorokhod.scalePath scale) ⁻¹' corridorSet upper lower) ≤
      ∏ i ∈ s, P (stableProcessTube
        (((1 + ε) * commonPartitionCellSpatialScale α upper lower i *
          (hi i - lo i) / 2) / scale)) := by
  let cellScale (i : Fin ((StepBoundary.commonKnots upper lower).card - 1)) :=
    commonPartitionCellSpatialScale α upper lower i
  let margin (i : Fin ((StepBoundary.commonKnots upper lower).card - 1)) :=
    ε * cellScale i * ((hi i - lo i) / scale)
  have hcellScalePos (i : Fin ((StepBoundary.commonKnots upper lower).card - 1)) :
      0 < cellScale i := by
    exact commonPartitionCellSpatialScale_pos α upper lower i
  have hmargin : ∀ i ∈ s, 0 < margin i := by
    intro i hiMem
    dsimp [margin]
    exact mul_pos (mul_pos hε (hcellScalePos i))
      (div_pos (sub_pos.mpr (hwidth i hiMem)) hscale)
  have hbase := measure_scalePath_preimage_corridorSet_le_stableProcessTubeProduct
    hP hX hscale upper lower s lo hi hlower hupper hwidth margin hmargin
  have hradius (i : Fin ((StepBoundary.commonKnots upper lower).card - 1)) :
      (cellScale i * ((hi i - lo i) / scale) + margin i) / 2 =
        (((1 + ε) * cellScale i * (hi i - lo i) / 2) / scale) := by
    dsimp [margin]
    dsimp [cellScale]
    field_simp [ne_of_gt hscale]
  calc
    P ((Skorokhod.scalePath scale) ⁻¹' corridorSet upper lower) ≤
      ∏ i ∈ s, P (stableProcessTube
        ((cellScale i * ((hi i - lo i) / scale) + margin i) / 2)) := hbase
    _ = ∏ i ∈ s, P (stableProcessTube
        (((1 + ε) * commonPartitionCellSpatialScale α upper lower i *
          (hi i - lo i) / 2) / scale)) := by
      apply Finset.prod_congr rfl
      intro i hiMem
      rw [hradius]

/-- The limiting sum of relative cell escape rates is the source constant
`2^α C` times the finite partition energy, in the limit as the enlargement
vanishes. This equality records the normalization conversion explicitly. -/
theorem sum_relativeCommonPartitionTubeRate_eq
    {α C ε : ℝ} (hα : 0 < α) (hε : 0 < ε)
    (upper lower : StepBoundary)
    (s : Finset (Fin ((StepBoundary.commonKnots upper lower).card - 1)))
    (lo hi : Fin ((StepBoundary.commonKnots upper lower).card - 1) → ℝ)
    (hwidth : ∀ i ∈ s, lo i < hi i) :
    (∑ i ∈ s, C /
      (((1 + ε) * commonPartitionCellSpatialScale α upper lower i *
        (hi i - lo i) / 2) ^ α)) =
      C * (2 / (1 + ε)) ^ α *
        ∑ i ∈ s, commonPartitionCellLength upper lower i /
          (hi i - lo i) ^ α := by
  let A : ℝ := (1 + ε) / 2
  have hA : 0 < A := by
    dsimp [A]
    positivity
  have hAinvPow : (2 / (1 + ε)) ^ α * A ^ α = 1 := by
    rw [← Real.mul_rpow
      (div_nonneg (by norm_num : (0 : ℝ) ≤ 2) (by linarith : 0 ≤ 1 + ε)) hA.le]
    have hproduct : 2 / (1 + ε) * A = 1 := by
      dsimp [A]
      field_simp [ne_of_gt (by linarith : 0 < 1 + ε)]
    rw [hproduct, Real.one_rpow]
  have hterm : ∀ i ∈ s,
      C / (((1 + ε) * commonPartitionCellSpatialScale α upper lower i *
        (hi i - lo i) / 2) ^ α) =
      (C * (2 / (1 + ε)) ^ α) *
        (commonPartitionCellLength upper lower i / (hi i - lo i) ^ α) := by
    intro i hiMem
    let length := commonPartitionCellLength upper lower i
    let cellScale := commonPartitionCellSpatialScale α upper lower i
    let width := hi i - lo i
    have hlength : 0 < length := commonPartitionCellLength_pos upper lower i
    have hcellScale : 0 < cellScale := commonPartitionCellSpatialScale_pos α upper lower i
    have hwidth' : 0 < width := sub_pos.mpr (hwidth i hiMem)
    have hcellScalePow : cellScale ^ α = length⁻¹ := by
      change (commonPartitionCellLength upper lower i ^ (-(1 / α))) ^ α =
        (commonPartitionCellLength upper lower i)⁻¹
      rw [← Real.rpow_mul hlength.le]
      have hexp : -(1 / α) * α = -1 := by
        field_simp [ne_of_gt hα]
      rw [hexp, Real.rpow_neg hlength.le]
      simp
      rfl
    have hradiusEq :
        ((1 + ε) * commonPartitionCellSpatialScale α upper lower i *
          (hi i - lo i) / 2) = A * cellScale * width := by
      dsimp [A, cellScale, width]
      ring
    have hradiusPow :
        ((1 + ε) * commonPartitionCellSpatialScale α upper lower i *
          (hi i - lo i) / 2) ^ α = A ^ α * length⁻¹ * width ^ α := by
      rw [hradiusEq,
        Real.mul_rpow (mul_nonneg hA.le hcellScale.le) hwidth'.le,
        Real.mul_rpow hA.le hcellScale.le, hcellScalePow]
    have hAinv : (2 / (1 + ε)) ^ α = (A ^ α)⁻¹ := by
      calc
        (2 / (1 + ε)) ^ α = (2 / (1 + ε)) ^ α *
            ((A ^ α) * (A ^ α)⁻¹) := by
          rw [mul_inv_cancel₀ (Real.rpow_pos_of_pos hA α).ne']
          simp
        _ = ((2 / (1 + ε)) ^ α * A ^ α) * (A ^ α)⁻¹ := by ring
        _ = (A ^ α)⁻¹ := by rw [hAinvPow]; simp
    rw [hradiusPow, hAinv]
    dsimp [length, width]
    field_simp [ne_of_gt hA, (Real.rpow_pos_of_pos hA α).ne',
      (Real.rpow_pos_of_pos hwidth' α).ne', hlength.ne']
  calc
    _ = ∑ i ∈ s, (C * (2 / (1 + ε)) ^ α) *
        (commonPartitionCellLength upper lower i / (hi i - lo i) ^ α) := by
      apply Finset.sum_congr rfl
      intro i hiMem
      exact hterm i hiMem
    _ = C * (2 / (1 + ε)) ^ α *
        ∑ i ∈ s, commonPartitionCellLength upper lower i /
          (hi i - lo i) ^ α := by
      rw [Finset.mul_sum]

/-- The logarithmic rate of a positively rescaled step corridor is eventually
bounded above by the sum of the stable cell escape rates, provided the
corridor probability is eventually positive. The remaining step for the
source's process theorem is the endpoint-core lower bound, which supplies
this positivity and the matching lower rate. -/
theorem HasStableProcessEscapeRate.eventually_scalePath_corridor_logRate_le
    {α C : ℝ} {μ : Measure ℝ}
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hEscape : HasStableProcessEscapeRate α μ P C)
    {Ω : Type*} [MeasurableSpace Ω]
    {X : ℝ≥0 → Ω → ℝ} {Q : Measure Ω} [IsProbabilityMeasure Q]
    (hX : IsStableLevyProcess α μ X Q)
    (upper lower : StepBoundary)
    (s : Finset (Fin ((StepBoundary.commonKnots upper lower).card - 1)))
    (lo hi : Fin ((StepBoundary.commonKnots upper lower).card - 1) → ℝ)
    (hlower : ∀ i ∈ s, lower.rightTrace
      (StepBoundary.commonPartitionGrid upper lower i.val) = (lo i : EReal))
    (hupper : ∀ i ∈ s, upper.rightTrace
      (StepBoundary.commonPartitionGrid upper lower i.val) = (hi i : EReal))
    (hwidth : ∀ i ∈ s, lo i < hi i)
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η)
    (hpositive : ∀ᶠ scale : ℝ in atTop,
      0 < (P ((Skorokhod.scalePath scale) ⁻¹' corridorSet upper lower)).toReal) :
    ∀ᶠ scale : ℝ in atTop,
      scale⁻¹ ^ α * Real.log
        ((P ((Skorokhod.scalePath scale) ⁻¹' corridorSet upper lower)).toReal) ≤
        (C * (2 / (1 + ε)) ^ α *
          ∑ i ∈ s, commonPartitionCellLength upper lower i /
            (hi i - lo i) ^ α) + η := by
  let radius (i : Fin ((StepBoundary.commonKnots upper lower).card - 1)) :=
    (1 + ε) * commonPartitionCellSpatialScale α upper lower i *
      (hi i - lo i) / 2
  have hradius : ∀ i ∈ s, 0 < radius i := by
    intro i hiMem
    dsimp [radius]
    have hcell : 0 < commonPartitionCellSpatialScale α upper lower i :=
      commonPartitionCellSpatialScale_pos α upper lower i
    exact div_pos
      (mul_pos (mul_pos (by linarith : 0 < 1 + ε) hcell)
        (sub_pos.mpr (hwidth i hiMem))) (by norm_num)
  have hsum := hEscape.tendsto_invRpow_mul_sum_log_stableProcessTube
    s radius hradius
  have hsumUpper : ∀ᶠ scale : ℝ in atTop,
      scale⁻¹ ^ α *
        ∑ i ∈ s, Real.log ((P (stableProcessTube (radius i / scale))).toReal) <
        (∑ i ∈ s, C / radius i ^ α) + η := by
    have hevent := hsum.eventually
      (Iio_mem_nhds (lt_add_of_pos_right _ hη))
    simpa using hevent
  filter_upwards [hpositive, hsumUpper, eventually_gt_atTop (0 : ℝ)] with
    scale hpositiveScale hsumScale hscale
  have hproduct := measure_scalePath_preimage_corridorSet_le_stableProcessTubeProduct_of_relativeEnlargement
    hEscape.isStableClockProcessLaw hX hscale hε upper lower s lo hi
    hlower hupper hwidth
  have hproduct' :
      P ((Skorokhod.scalePath scale) ⁻¹' corridorSet upper lower) ≤
        ∏ i ∈ s, P (stableProcessTube (radius i / scale)) := by
    simpa [radius] using hproduct
  have hlog := ProbabilityTheory.measure_log_toReal_le_sum_log_toReal_of_le_finsetProduct
    P s ((Skorokhod.scalePath scale) ⁻¹' corridorSet upper lower)
    (fun i => stableProcessTube (radius i / scale)) hproduct' hpositiveScale
  have hscaledLog := mul_le_mul_of_nonneg_left hlog
    (Real.rpow_nonneg (inv_nonneg.mpr hscale.le) α)
  have hrate : scale⁻¹ ^ α *
      ∑ i ∈ s, Real.log ((P (stableProcessTube (radius i / scale))).toReal) <
        (∑ i ∈ s, C / radius i ^ α) + η := hsumScale
  have hα : 0 < α := hEscape.isStableClockProcessLaw.strictlyStable.1
  have henergyRate := sum_relativeCommonPartitionTubeRate_eq
    (C := C) hα hε upper lower s lo hi hwidth
  rw [henergyRate] at hrate
  simpa [radius] using le_trans hscaledLog hrate.le

end ProbabilityTheory

end
