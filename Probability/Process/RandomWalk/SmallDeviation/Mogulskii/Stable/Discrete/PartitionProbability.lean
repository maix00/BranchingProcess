/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Path.Corridor.Horizontal
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Discrete.PartitionCorridor
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Rate.Lower

/-!
# Lower probability inputs for partition cells

The source endpoint-return lower bound gives positivity and a logarithmic
lower bound for a centered tube at the full horizon. A fixed spatial rescaling
converts it to any positive cell width; horizon monotonicity then supplies the
same lower bound for each shorter half-open partition cell.
-/

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

open ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii

/-- The endpoint-return lower bound supplies eventual positivity and
logarithmic lower coboundedness for any fixed-width range event observed up to
a horizon no longer than `n`. The rate change under the spatial rescaling is
controlled by regular variation of the stable scale time. -/
theorem eventually_partialSumRangeOscillationLTProbability_pos_and_rateLog_cobounded
    {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {α C : ℝ} {normalization scale : ℕ → ℝ}
    (hscale : IsStableMogulskiiScale α ν normalization scale)
    (hα : 0 < α) (hα₂ : α ≤ 2)
    (hslow : Asymptotics.IsSlowlyVaryingAtTop (stableSlowVariation α ν))
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hEscape : HasStableProcessEscapeRate α μ P C)
    {Ω : Type*} [MeasurableSpace Ω]
    {X : ℝ≥0 → Ω → ℝ} {Q : Measure Ω} [IsProbabilityMeasure Q]
    (hX : IsStableLevyProcess α μ X Q)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization (fun _ => 0))
    (htightBase : IsTightMeasureSet
      (Set.range fun n => RandomWalk.normalizedStepPathLaw ν normalization n))
    {width : ℝ} (hwidth : 0 < width) {horizon : ℕ → ℕ}
    (hhorizon : ∀ᶠ n : ℕ in atTop, horizon n ≤ n) :
    (∀ᶠ n : ℕ in atTop,
      0 < partialSumRangeOscillationLTProbability (iidSequenceLaw ν)
        (width * scale n) (horizon n)) ∧
    Filter.IsCoboundedUnder (· ≤ ·) atTop
      (fun n => stableSmallDeviationRate α ν scale n * Real.log
        (partialSumRangeOscillationLTProbability (iidSequenceLaw ν)
          (width * scale n) (horizon n)).toReal) := by
  let cellScale : ℕ → ℝ := fun n => width * scale n
  let tubeProbability : ℕ → ENNReal := fun n =>
    openHorizontalTubeProbability (iidSequenceLaw ν) (1 / 2) (cellScale n) n
  let fullRangeProbability : ℕ → ENNReal := fun n =>
    partialSumRangeOscillationLTProbability (iidSequenceLaw ν) (cellScale n) n
  let cellRangeProbability : ℕ → ENNReal := fun n =>
    partialSumRangeOscillationLTProbability (iidSequenceLaw ν) (cellScale n) (horizon n)
  let cellRate : ℕ → ℝ := fun n => stableSmallDeviationRate α ν scale n
  let scaledRate : ℕ → ℝ := fun n => stableSmallDeviationRate α ν cellScale n
  let scaledTubeRate : ℕ → ℝ := fun n =>
    scaledRate n * Real.log (tubeProbability n).toReal
  let scaledCellRate : ℕ → ℝ := fun n =>
    scaledRate n * Real.log (cellRangeProbability n).toReal
  let cellProbabilityRate : ℕ → ℝ := fun n =>
    cellRate n * Real.log (cellRangeProbability n).toReal
  let rateRatio : ℕ → ℝ := fun n => cellRate n / scaledRate n
  have hcellScale : IsStableMogulskiiScale α ν normalization cellScale := by
    simpa [cellScale] using hscale.const_mul hwidth
  have hscaledRateZero : Tendsto scaledRate atTop (𝓝 0) := by
    simpa [scaledRate] using
      tendsto_stableSmallDeviationRate_zero_of_slowVariation
        hcellScale.stableNorming hcellScale.scale_tendsto_atTop
        hcellScale.scale_div_normalization_tendsto_zero hα hα₂ hslow
  have hreturn := Stable.stableEscapeRate_eventually_positive_and_log_cobounded
    hcellScale hα hα₂ hslow hscaledRateZero hEscape hX hcdf hDOA htightBase
  have hcellScalePos : ∀ᶠ n : ℕ in atTop, 0 < cellScale n :=
    hcellScale.eventually_scale_pos
  have htubeLeCell : ∀ᶠ n : ℕ in atTop,
      tubeProbability n ≤ cellRangeProbability n := by
    filter_upwards [hcellScalePos, hhorizon] with n hscaleN hhorizonN
    calc
      tubeProbability n ≤ fullRangeProbability n := by
        simpa [tubeProbability, fullRangeProbability] using
          RandomWalk.openHorizontalTubeProbability_le_partialSumRangeOscillationLTProbability
            ν (by norm_num : (0 : ℝ) < 1 / 2)
            (by norm_num : (1 / 2 : ℝ) < 1) hscaleN n
      _ ≤ cellRangeProbability n := by
        simpa [fullRangeProbability, cellRangeProbability] using
          RandomWalk.partialSumRangeOscillationLTProbability_antitone_horizon
            (iidSequenceLaw ν) (cellScale n) hhorizonN
  have hcellPositive : ∀ᶠ n : ℕ in atTop, 0 < cellRangeProbability n := by
    filter_upwards [hreturn.1, htubeLeCell] with n htube hle
    exact lt_of_lt_of_le (by simpa [tubeProbability, cellScale] using htube) hle
  have htubeOne (n : ℕ) : tubeProbability n ≤ 1 := by
    calc
      tubeProbability n ≤ iidSequenceLaw ν Set.univ :=
        measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  have hcellOne (n : ℕ) : cellRangeProbability n ≤ 1 := by
    calc
      cellRangeProbability n ≤ iidSequenceLaw ν Set.univ :=
        measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  have hslowScalePos : ∀ᶠ n : ℕ in atTop,
      0 < stableSlowVariation α ν (scale n) :=
    hscale.scale_tendsto_atTop.eventually hslow.eventually_pos
  have hslowCellPos : ∀ᶠ n : ℕ in atTop,
      0 < stableSlowVariation α ν (cellScale n) :=
    hcellScale.scale_tendsto_atTop.eventually hslow.eventually_pos
  have hcellRatePos : ∀ᶠ n : ℕ in atTop, 0 < cellRate n := by
    filter_upwards [eventually_gt_atTop (0 : ℕ), hscale.eventually_scale_pos,
      hslowScalePos] with n hn hs hL
    change 0 < stableSmallDeviationRate α ν scale n
    rw [stableSmallDeviationRate]
    have hnReal : 0 < (n : ℝ) := by exact_mod_cast hn
    positivity
  have hscaledRatePos : ∀ᶠ n : ℕ in atTop, 0 < scaledRate n := by
    filter_upwards [eventually_gt_atTop (0 : ℕ), hcellScale.eventually_scale_pos,
      hslowCellPos] with n hn hs hL
    change 0 < stableSmallDeviationRate α ν cellScale n
    rw [stableSmallDeviationRate]
    have hnReal : 0 < (n : ℝ) := by exact_mod_cast hn
    positivity
  have hlogTubeLeCell : ∀ᶠ n : ℕ in atTop,
      Real.log (tubeProbability n).toReal ≤ Real.log (cellRangeProbability n).toReal := by
    filter_upwards [hreturn.1, hcellPositive, htubeLeCell] with n htube hcell hprob
    have htubeTop : tubeProbability n ≠ ⊤ :=
      ne_of_lt (htubeOne n |>.trans_lt ENNReal.one_lt_top)
    have hcellTop : cellRangeProbability n ≠ ⊤ :=
      ne_of_lt (hcellOne n |>.trans_lt ENNReal.one_lt_top)
    have htubeRealPos : 0 < (tubeProbability n).toReal :=
      ENNReal.toReal_pos (ne_of_gt (by simpa [tubeProbability, cellScale] using htube))
        htubeTop
    have htoRealLe : (tubeProbability n).toReal ≤ (cellRangeProbability n).toReal :=
      (ENNReal.toReal_le_toReal htubeTop hcellTop).2 hprob
    exact Real.log_le_log htubeRealPos htoRealLe
  have hscaledCellRateNonpos : ∀ᶠ n : ℕ in atTop, scaledCellRate n ≤ 0 := by
    filter_upwards [hcellPositive, Filter.Eventually.of_forall hcellOne,
      hscaledRatePos] with n hpos hone hrate
    have hcellTop : cellRangeProbability n ≠ ⊤ :=
      ne_of_lt (hone.trans_lt ENNReal.one_lt_top)
    have hrealPos : 0 < (cellRangeProbability n).toReal :=
      ENNReal.toReal_pos (ne_of_gt hpos) hcellTop
    have hrealLe : (cellRangeProbability n).toReal ≤ 1 :=
      (ENNReal.toReal_le_toReal hcellTop ENNReal.one_ne_top).2 hone
    have hlog : Real.log (cellRangeProbability n).toReal ≤ 0 :=
      Real.log_nonpos hrealPos.le hrealLe
    exact mul_nonpos_of_nonneg_of_nonpos hrate.le hlog
  have hscaledTubeRateNonpos : ∀ᶠ n : ℕ in atTop, scaledTubeRate n ≤ 0 := by
    filter_upwards [hreturn.1, Filter.Eventually.of_forall htubeOne,
      hscaledRatePos] with n hpos hone hrate
    have htubeTop : tubeProbability n ≠ ⊤ :=
      ne_of_lt (hone.trans_lt ENNReal.one_lt_top)
    have hrealPos : 0 < (tubeProbability n).toReal :=
      ENNReal.toReal_pos (ne_of_gt (by simpa [tubeProbability, cellScale] using hpos))
        htubeTop
    have hrealLe : (tubeProbability n).toReal ≤ 1 :=
      (ENNReal.toReal_le_toReal htubeTop ENNReal.one_ne_top).2 hone
    have hlog : Real.log (tubeProbability n).toReal ≤ 0 :=
      Real.log_nonpos hrealPos.le hrealLe
    exact mul_nonpos_of_nonneg_of_nonpos hrate.le hlog
  have hrateRatio : Tendsto rateRatio atTop (𝓝 ((width ^ α)⁻¹)) := by
    have hratio := tendsto_stableSmallDeviationRate_const_mul_div hscale hslow hwidth
    have hinv := hratio.inv₀ (Real.rpow_pos_of_pos hwidth α).ne'
    simpa [rateRatio, cellRate, scaledRate, cellScale] using hinv
  let ratioBound : ℝ := (width ^ α)⁻¹ + 1
  have hratioBound : ∀ᶠ n : ℕ in atTop, rateRatio n < ratioBound := by
    have hlimit : (width ^ α)⁻¹ < ratioBound := by
      dsimp [ratioBound]
      linarith
    exact hrateRatio.eventually (isOpen_Iio.mem_nhds hlimit)
  obtain ⟨lowerBound, hlowerBound⟩ := hreturn.2.1.frequently_ge
  have hlowerBoundNonpos : lowerBound ≤ 0 := by
    obtain ⟨n, hfreq, hevent⟩ :=
      (hlowerBound.and_eventually hscaledTubeRateNonpos).exists
    exact hfreq.trans hevent
  have hrateFactorEq : ∀ᶠ n : ℕ in atTop,
      cellProbabilityRate n = rateRatio n * scaledCellRate n := by
    filter_upwards [hscaledRatePos] with n hrate
    change stableSmallDeviationRate α ν scale n *
        Real.log (cellRangeProbability n).toReal =
      (stableSmallDeviationRate α ν scale n /
        stableSmallDeviationRate α ν cellScale n) *
        (stableSmallDeviationRate α ν cellScale n *
          Real.log (cellRangeProbability n).toReal)
    calc
      _ = stableSmallDeviationRate α ν scale n *
          (((stableSmallDeviationRate α ν cellScale n)⁻¹ *
            stableSmallDeviationRate α ν cellScale n) *
              Real.log (cellRangeProbability n).toReal) := by
        rw [inv_mul_cancel₀ hrate.ne', one_mul]
      _ = _ := by rw [div_eq_mul_inv]; ring
  have hscaledTubeLeCell : ∀ᶠ n : ℕ in atTop,
      scaledTubeRate n ≤ scaledCellRate n := by
    filter_upwards [hlogTubeLeCell, hscaledRatePos] with n hlog hrate
    exact mul_le_mul_of_nonneg_left hlog hrate.le
  have hfinalFrequently : ∃ᶠ n : ℕ in atTop,
      ratioBound * lowerBound ≤ cellProbabilityRate n := by
    apply (hlowerBound.and_eventually
      (hscaledTubeRateNonpos.and <| hscaledCellRateNonpos.and <|
        hscaledTubeLeCell.and <| hratioBound.and hrateFactorEq)).mono
    intro n hn
    rcases hn with ⟨hbaseLower, hconditions⟩
    rcases hconditions with ⟨hTubeNonpos, hRest⟩
    rcases hRest with ⟨hCellNonpos, hRest⟩
    rcases hRest with ⟨hTubeLeCell, hRest⟩
    rcases hRest with ⟨hq, hfactor⟩
    have hratioBoundLe : rateRatio n ≤ ratioBound := hq.le
    calc
      ratioBound * lowerBound ≤ ratioBound * scaledTubeRate n :=
        mul_le_mul_of_nonneg_left hbaseLower (by
          dsimp [ratioBound]
          positivity)
      _ ≤ ratioBound * scaledCellRate n :=
        mul_le_mul_of_nonneg_left hTubeLeCell (by
          dsimp [ratioBound]
          positivity)
      _ ≤ rateRatio n * scaledCellRate n :=
        mul_le_mul_of_nonpos_right hratioBoundLe hCellNonpos
      _ = cellProbabilityRate n := hfactor.symm
  refine ⟨hcellPositive, ?_⟩
  exact IsCoboundedUnder.of_frequently_ge hfinalFrequently

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

end
