/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Corridor
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Partition
import Mathlib.Topology.Order.LiminfLimsup

/-!
# Stable Mogulskii upper rate from a fixed block parameter

This module converts the source's independent-block bound into the
small-deviation logarithmic normalization. The theorem keeps one fixed block
parameter and one strict one-block base; the source's slow diagonal is a later
step, after the fixed-parameter limits have been established.
-/

open Filter MeasureTheory
open scoped ENNReal Topology

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable

/-- Convert an eventual independent-block power bound into a normalized
logarithmic limsup. This analytic step is shared by centered corridor and
translation-invariant range events. -/
theorem limsup_stableSmallDeviationRate_mul_log_probability_le_of_blockPowerBound
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {α constant τ : ℝ} {normalization scale : ℕ → ℝ} {horizon : ℕ → ℕ}
    (hscale : IsStableMogulskiiScale α ν normalization scale)
    (hα : 0 < α) (hα₂ : α ≤ 2)
    (hslow : Asymptotics.IsSlowlyVaryingAtTop (stableSlowVariation α ν))
    (hconstant : 0 < constant)
    (hhorizon : Tendsto (fun n => (horizon n : ℝ) / (n : ℝ))
      atTop (𝓝 τ))
    {q : ℝ} (hq : 0 < q)
    (probability : ℕ → ENNReal)
    (hprobabilityOne : ∀ n, probability n ≤ 1)
    (hblockBound : ∀ᶠ n : ℕ in atTop,
      probability n ≤ ENNReal.ofReal q ^
        (horizon n / stableBlockLength α ν constant scale n))
    (hpositive : ∀ᶠ n : ℕ in atTop, 0 < probability n)
    (hlowerCobounded : Filter.IsCoboundedUnder (· ≤ ·) atTop
      (fun n => stableSmallDeviationRate α ν scale n *
        Real.log (probability n).toReal)) :
    atTop.limsup (fun n => stableSmallDeviationRate α ν scale n *
      Real.log (probability n).toReal) ≤ (τ / constant) * Real.log q := by
  let blockCount : ℕ → ℕ := fun n =>
    horizon n / stableBlockLength α ν constant scale n
  let coefficient : ℕ → ℝ := fun n =>
    stableSmallDeviationRate α ν scale n * (blockCount n : ℝ)
  have hscaleTop : Tendsto scale atTop atTop :=
    IsStableMogulskiiScale.scale_tendsto_atTop hscale
  have hscalePos : ∀ᶠ n : ℕ in atTop, 0 < scale n :=
    IsStableMogulskiiScale.eventually_scale_pos hscale
  have hslowPos : ∀ᶠ n : ℕ in atTop,
      0 < stableSlowVariation α ν (scale n) :=
    hscaleTop.eventually hslow.eventually_pos
  have hlogBound : ∀ᶠ n : ℕ in atTop,
      stableSmallDeviationRate α ν scale n * Real.log (probability n).toReal ≤
        coefficient n * Real.log q := by
    filter_upwards [hblockBound, hpositive, hscalePos, hslowPos] with n hprob hpos hs hL
    have hprobTop : probability n ≠ ⊤ := ne_of_lt ((hprobabilityOne n).trans_lt
      ENNReal.one_lt_top)
    have hpowTop : (ENNReal.ofReal q) ^ blockCount n ≠ ⊤ :=
      ENNReal.pow_ne_top ENNReal.ofReal_ne_top
    have hrealBound : (probability n).toReal ≤ q ^ blockCount n := by
      have hrealENN : (probability n).toReal ≤
          ((ENNReal.ofReal q) ^ blockCount n).toReal :=
        (ENNReal.toReal_le_toReal hprobTop hpowTop).2 (by simpa [blockCount] using hprob)
      simpa [ENNReal.toReal_pow, ENNReal.toReal_ofReal hq.le] using hrealENN
    have hrealPos : 0 < (probability n).toReal :=
      ENNReal.toReal_pos (ne_of_gt hpos) hprobTop
    have hlog := Real.log_le_log hrealPos hrealBound
    rw [Real.log_pow] at hlog
    have hrateNonneg : 0 ≤ stableSmallDeviationRate α ν scale n := by
      rw [stableSmallDeviationRate]
      positivity
    have hmul := mul_le_mul_of_nonneg_left hlog hrateNonneg
    calc
      stableSmallDeviationRate α ν scale n * Real.log (probability n).toReal ≤
          stableSmallDeviationRate α ν scale n *
            ((blockCount n : ℝ) * Real.log q) := hmul
      _ = coefficient n * Real.log q := by
        dsimp [coefficient]
        ring
  have hcoefficient : Tendsto coefficient atTop (𝓝 (τ / constant)) := by
    simpa [coefficient, blockCount] using
      tendsto_stableScaleTime_div_nat_mul_segmentBlockCount
        hα hα₂ hconstant hscale hslow hhorizon
  have hright : Tendsto (fun n => coefficient n * Real.log q) atTop
      (𝓝 ((τ / constant) * Real.log q)) := hcoefficient.mul_const _
  calc
    atTop.limsup (fun n => stableSmallDeviationRate α ν scale n *
        Real.log (probability n).toReal) ≤
      atTop.limsup (fun n => coefficient n * Real.log q) :=
        Filter.limsup_le_limsup hlogBound hlowerCobounded hright.isBoundedUnder_le
    _ = (τ / constant) * Real.log q := hright.limsup_eq

/-- A fixed stable block parameter bounds the normalized logarithmic rate on
any positive-width horizontal corridor and any macroscopic time segment. The
strict one-block base is supplied by the path-law limit and closed-set
Portmanteau estimate; positivity and lower coboundedness remain explicit
because this statement takes real logarithms and then forms a limsup. -/
theorem limsup_stableSmallDeviationRate_mul_log_openHorizontalTubeProbability_le_of_blockPathLimit
    {ν μ : Measure ℝ} [IsProbabilityMeasure ν]
    {α constant margin c width τ : ℝ}
    {normalization scale : ℕ → ℝ} {horizon : ℕ → ℕ}
    (hscale : IsStableMogulskiiScale α ν normalization scale)
    (hα : 0 < α) (hα₂ : α ≤ 2)
    (hslow : Asymptotics.IsSlowlyVaryingAtTop
      (stableSlowVariation α ν))
    (hconstant : 0 < constant)
    (hτ : 0 < τ)
    (hhorizon : Tendsto (fun n => (horizon n : ℝ) / (n : ℝ))
      atTop (𝓝 τ))
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hP : IsStableClockProcessLaw α μ UnitInterval.clock P)
    (hc : 0 < c) (hwidth : 0 < width) (hmargin : 0 < margin)
    (hlimit : TendstoInDistribution
      (RandomWalk.normalizedStepBlockCadlagPathIcc scale
        (fun n => stableBlockLength α ν constant scale n))
      atTop (id : CadlagPath unitInterval ℝ → CadlagPath unitInterval ℝ)
      (fun _ => iidSequenceLaw ν) (P.map (Skorokhod.scalePath c)))
    {q : ℝ} (hq : 0 < q) (_hqOne : q < 1)
    (hbase : P (stableProcessTube ((width + margin) / (2 * c))) < ENNReal.ofReal q)
    (hpositive : ∀ᶠ n : ℕ in atTop,
      0 < openHorizontalTubeProbability (iidSequenceLaw ν) (1 / 2)
        (width * scale n) (horizon n))
    (hlowerCobounded : Filter.IsCoboundedUnder (· ≤ ·) atTop
      (fun n => stableSmallDeviationRate α ν scale n * Real.log
        (openHorizontalTubeProbability (iidSequenceLaw ν)
          (1 / 2) (width * scale n) (horizon n)).toReal)) :
    atTop.limsup (fun n => stableSmallDeviationRate α ν scale n * Real.log
      (openHorizontalTubeProbability (iidSequenceLaw ν)
        (1 / 2) (width * scale n) (horizon n)).toReal) ≤
      (τ / constant) * Real.log q := by
  let blockLength : ℕ → ℕ := stableBlockLength α ν constant scale
  let blockCount : ℕ → ℕ := fun n => horizon n / blockLength n
  let probability : ℕ → ENNReal := fun n =>
    openHorizontalTubeProbability (iidSequenceLaw ν) (1 / 2)
      (width * scale n) (horizon n)
  have hscaleTop : Tendsto scale atTop atTop :=
    IsStableMogulskiiScale.scale_tendsto_atTop hscale
  have hscalePos : ∀ᶠ n : ℕ in atTop, 0 < scale n :=
    IsStableMogulskiiScale.eventually_scale_pos hscale
  have hblockPos : ∀ᶠ n : ℕ in atTop, 0 < blockLength n := by
    simpa [blockLength] using eventually_stableBlockLength_pos_of_slowVariation
      hα hα₂ hslow hconstant hscaleTop
  have hhorizonPos : ∀ᶠ n : ℕ in atTop, 0 < horizon n := by
    have hratioPos : ∀ᶠ n : ℕ in atTop, 0 < (horizon n : ℝ) / (n : ℝ) :=
      hhorizon.eventually (Ioi_mem_nhds hτ)
    filter_upwards [hratioPos, eventually_gt_atTop (0 : ℕ)] with n hratio hn
    have hnReal : 0 < (n : ℝ) := by exact_mod_cast hn
    have hhorReal : 0 < (horizon n : ℝ) :=
      (div_pos_iff_of_pos_right hnReal).mp hratio
    exact_mod_cast hhorReal
  have hblockBound : ∀ᶠ n : ℕ in atTop,
      probability n ≤ ENNReal.ofReal q ^ blockCount n := by
    filter_upwards [eventually_openHorizontalTubeProbability_le_pow_of_blockPathLimit
      hP hscalePos hhorizonPos hblockPos hlimit hc
      hwidth hmargin hbase]
      with n hn
    simpa [probability, blockCount, blockLength] using hn
  have hprobabilityOne : ∀ n, probability n ≤ 1 := by
    intro n
    change iidSequenceLaw ν
      {increment | InOpenHorizontalTube (1 / 2) (width * scale n)
        (horizon n) increment} ≤ 1
    calc
      iidSequenceLaw ν
          {increment | InOpenHorizontalTube (1 / 2) (width * scale n)
            (horizon n) increment} ≤ iidSequenceLaw ν Set.univ :=
        measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  exact limsup_stableSmallDeviationRate_mul_log_probability_le_of_blockPowerBound
    hscale hα hα₂ hslow hconstant hhorizon hq probability hprobabilityOne
    hblockBound hpositive hlowerCobounded

/-- A fixed stable block parameter gives the logarithmic upper rate for the
translation-invariant range event on any macroscopic segment. This is the
same block estimate as for a centered tube, with the one-block range bound
obtained directly from closed-set Portmanteau. -/
theorem limsup_stableSmallDeviationRate_mul_log_partialSumRangeOscillationLTProbability_le_of_blockPathLimit
    {ν μ : Measure ℝ} [IsProbabilityMeasure ν]
    {α constant margin c width τ : ℝ}
    {normalization scale : ℕ → ℝ} {horizon : ℕ → ℕ}
    (hscale : IsStableMogulskiiScale α ν normalization scale)
    (hα : 0 < α) (hα₂ : α ≤ 2)
    (hslow : Asymptotics.IsSlowlyVaryingAtTop
      (stableSlowVariation α ν))
    (hconstant : 0 < constant) (hτ : 0 < τ)
    (hhorizon : Tendsto (fun n => (horizon n : ℝ) / (n : ℝ))
      atTop (𝓝 τ))
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hP : IsStableClockProcessLaw α μ UnitInterval.clock P)
    (hc : 0 < c) (hwidth : 0 < width) (hmargin : 0 < margin)
    (hlimit : TendstoInDistribution
      (RandomWalk.normalizedStepBlockCadlagPathIcc scale
        (fun n => stableBlockLength α ν constant scale n))
      atTop (id : CadlagPath unitInterval ℝ → CadlagPath unitInterval ℝ)
      (fun _ => iidSequenceLaw ν) (P.map (Skorokhod.scalePath c)))
    {q : ℝ} (hq : 0 < q)
    (hbase : P (stableProcessTube ((width + margin) / (2 * c))) <
      ENNReal.ofReal q)
    (hpositive : ∀ᶠ n : ℕ in atTop,
      0 < partialSumRangeOscillationLTProbability (iidSequenceLaw ν)
        (width * scale n) (horizon n))
    (hlowerCobounded : Filter.IsCoboundedUnder (· ≤ ·) atTop
      (fun n => stableSmallDeviationRate α ν scale n * Real.log
        (partialSumRangeOscillationLTProbability (iidSequenceLaw ν)
          (width * scale n) (horizon n)).toReal)) :
    atTop.limsup (fun n => stableSmallDeviationRate α ν scale n * Real.log
      (partialSumRangeOscillationLTProbability (iidSequenceLaw ν)
        (width * scale n) (horizon n)).toReal) ≤
      (τ / constant) * Real.log q := by
  let blockLength : ℕ → ℕ := stableBlockLength α ν constant scale
  let blockCount : ℕ → ℕ := fun n => horizon n / blockLength n
  let probability : ℕ → ENNReal := fun n =>
    partialSumRangeOscillationLTProbability (iidSequenceLaw ν)
      (width * scale n) (horizon n)
  have hscaleTop : Tendsto scale atTop atTop :=
    IsStableMogulskiiScale.scale_tendsto_atTop hscale
  have hscalePos : ∀ᶠ n : ℕ in atTop, 0 < scale n :=
    IsStableMogulskiiScale.eventually_scale_pos hscale
  have hblockPos : ∀ᶠ n : ℕ in atTop, 0 < blockLength n := by
    simpa [blockLength] using eventually_stableBlockLength_pos_of_slowVariation
      hα hα₂ hslow hconstant hscaleTop
  have hhorizonPos : ∀ᶠ n : ℕ in atTop, 0 < horizon n := by
    have hratioPos : ∀ᶠ n : ℕ in atTop, 0 < (horizon n : ℝ) / (n : ℝ) :=
      hhorizon.eventually (Ioi_mem_nhds hτ)
    filter_upwards [hratioPos, eventually_gt_atTop (0 : ℕ)] with n hratio hn
    have hnReal : 0 < (n : ℝ) := by exact_mod_cast hn
    have hhorReal : 0 < (horizon n : ℝ) :=
      (div_pos_iff_of_pos_right hnReal).mp hratio
    exact_mod_cast hhorReal
  have hblockBound : ∀ᶠ n : ℕ in atTop,
      probability n ≤ ENNReal.ofReal q ^ blockCount n := by
    filter_upwards [eventually_partialSumRangeOscillationLTProbability_le_pow_of_blockPathLimit
      hP hscalePos hblockPos hlimit hc hwidth hmargin hbase]
      with n hn
    simpa [probability, blockCount, blockLength] using hn
  have hprobabilityOne : ∀ n, probability n ≤ 1 := by
    intro n
    change iidSequenceLaw ν
      (partialSumRangeOscillationLTEvent (width * scale n) (horizon n)) ≤ 1
    calc
      iidSequenceLaw ν
          (partialSumRangeOscillationLTEvent (width * scale n) (horizon n)) ≤
        iidSequenceLaw ν Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  exact limsup_stableSmallDeviationRate_mul_log_probability_le_of_blockPowerBound
    hscale hα hα₂ hslow hconstant hhorizon hq probability hprobabilityOne
    hblockBound hpositive hlowerCobounded

/-- A fixed stable block parameter bounds the logarithmic rate on a
macroscopic subinterval of arbitrary positive width. The width and duration
enter separately: the escape rate contributes the inverse `α`-power of the
half-width, while the block count contributes the relative duration `τ`.
This is the cell estimate needed before multiplying the finitely many cells
of a step corridor. -/
theorem limsup_stableSmallDeviationRate_mul_log_openHorizontalTubeProbability_le_of_escapeRate_on_segment
    {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {α C width τ : ℝ} {normalization scale : ℕ → ℝ}
    {horizon : ℕ → ℕ}
    (hscale : IsStableMogulskiiScale α ν normalization scale)
    (hα : 0 < α) (hα₂ : α ≤ 2)
    (hslow : Asymptotics.IsSlowlyVaryingAtTop (stableSlowVariation α ν))
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hEscape : HasStableProcessEscapeRate α μ P C)
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization (fun _ => 0))
    (htightBase : IsTightMeasureSet
      (Set.range fun n => RandomWalk.normalizedStepPathLaw ν normalization n))
    (hwidth : 0 < width) (hτ : 0 < τ)
    (hhorizon : Tendsto (fun n => (horizon n : ℝ) / (n : ℝ))
      atTop (𝓝 τ))
    {margin ε : ℝ} (hmargin : 0 < margin) (hε : 0 < ε)
    (hnegative : C / (((width + margin) / 2) ^ α) + 2 * ε < 0)
    (hpositive : ∀ᶠ n : ℕ in atTop,
      0 < openHorizontalTubeProbability (iidSequenceLaw ν) (1 / 2)
        (width * scale n) (horizon n))
    (hlowerCobounded : Filter.IsCoboundedUnder (· ≤ ·) atTop
      (fun n => stableSmallDeviationRate α ν scale n * Real.log
        (openHorizontalTubeProbability (iidSequenceLaw ν)
          (1 / 2) (width * scale n) (horizon n)).toReal)) :
    atTop.limsup (fun n => stableSmallDeviationRate α ν scale n * Real.log
      (openHorizontalTubeProbability (iidSequenceLaw ν)
        (1 / 2) (width * scale n) (horizon n)).toReal) ≤
      τ * (C / (((width + margin) / 2) ^ α) + 2 * ε) := by
  let radius : ℝ := (width + margin) / 2
  let rate : ℝ := C / radius ^ α
  have hradius : 0 < radius := by
    dsimp [radius]
    linarith
  have hbaseEvent : ∀ᶠ c : ℝ in atTop,
      P (stableProcessTube (radius / c)) <
          ENNReal.ofReal (Real.exp ((rate + 2 * ε) * c ^ α)) ∧
        Real.exp ((rate + 2 * ε) * c ^ α) < 1 := by
    have h := hEscape.eventually_tube_lt_of_exp_rate hradius hε (by
      simpa [radius, rate] using hnegative)
    simpa [radius, rate] using h
  obtain ⟨c₀, hc₀⟩ := Filter.eventually_atTop.1
    (hbaseEvent.and (eventually_gt_atTop (0 : ℝ)))
  let c : ℝ := max c₀ 1
  have hc : 0 < c := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hcData := hc₀ c (le_max_left _ _)
  have hbaseData :
      P (stableProcessTube (radius / c)) <
          ENNReal.ofReal (Real.exp ((rate + 2 * ε) * c ^ α)) ∧
        Real.exp ((rate + 2 * ε) * c ^ α) < 1 := hcData.1
  have hconstant : 0 < c ^ α := Real.rpow_pos_of_pos hc α
  have hblockLength : Tendsto
      (stableBlockLength α ν (c ^ α) scale) atTop atTop := by
    exact tendsto_stableBlockLength_atTop_of_slowVariation
      hα hα₂ hslow hconstant (IsStableMogulskiiScale.scale_tendsto_atTop hscale)
  have hblockPos : ∀ᶠ n : ℕ in atTop,
      0 < stableBlockLength α ν (c ^ α) scale n :=
    hblockLength.eventually (eventually_gt_atTop 0)
  have hblockEq : (fun n => stableBlockLength α ν (c ^ α) scale n) =
      Asymptotics.floorBlockLength
        (fun n => c ^ α * stableScaleTime α ν (scale n)) := by
    funext n
    change ⌊stableBlockArgument α ν (c ^ α) scale n⌋₊ =
      ⌊c ^ α * stableScaleTime α ν (scale n)⌋₊
    congr 1
    rw [stableBlockArgument, stableScaleTime, mul_div_assoc]
  have hnorm := IsStableMogulskiiScale.stableNorming hscale
  have hnormRatioBase := hnorm.tendsto_floorBlock_normalization_div_scale
    hα hα₂ hslow (IsStableMogulskiiScale.scale_tendsto_atTop hscale) hconstant
  have hnormRatio : Tendsto
      (fun n => normalization (stableBlockLength α ν (c ^ α) scale n) /
        scale n) atTop (𝓝 c) := by
    have hbase : Tendsto
        (fun n => normalization (stableBlockLength α ν (c ^ α) scale n) /
          scale n) atTop (𝓝 ((c ^ α) ^ (1 / α))) := by
      apply hnormRatioBase.congr'
      filter_upwards [] with n
      simp [hblockEq]
    have hroot : (c ^ α) ^ (1 / α) = c := by
      rw [← Real.rpow_mul (le_of_lt hc) α (1 / α)]
      have hmul : α * (1 / α) = 1 := by field_simp [ne_of_gt hα]
      rw [hmul, Real.rpow_one]
    convert hbase using 1
    exact congrArg nhds hroot.symm
  have hnormBlockPos : ∀ᶠ n : ℕ in atTop,
      0 < normalization (stableBlockLength α ν (c ^ α) scale n) := by
    filter_upwards [hblockPos] with n hn
    exact (IsStableMogulskiiScale.stableNorming hscale).1 _ hn
  have hlimit :=
    RandomWalk.FunctionalLimit.Stable.tendstoInDistribution_normalizedStepBlockPathLaw_of_baseTightness
      hDOA (hEscape.isStableClockProcessLaw) htightBase hblockLength
      (IsStableMogulskiiScale.eventually_scale_pos hscale) hnormBlockPos hnormRatio
  let q : ℝ := Real.exp ((rate + 2 * ε) * c ^ α)
  have hq : 0 < q := Real.exp_pos _
  have hqOne : q < 1 := by simpa [q] using hbaseData.2
  have hbase : P (stableProcessTube ((width + margin) / (2 * c))) <
      ENNReal.ofReal q := by
    simpa [q, radius, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      hbaseData.1
  have hfixed :=
    limsup_stableSmallDeviationRate_mul_log_openHorizontalTubeProbability_le_of_blockPathLimit
      hscale hα hα₂ hslow hconstant (τ := τ) hτ hhorizon hEscape.isStableClockProcessLaw
      hc hwidth hmargin hlimit hq hqOne hbase (by simpa using hpositive)
      (by simpa using hlowerCobounded)
  have hfixed' : atTop.limsup (fun n => stableSmallDeviationRate α ν scale n * Real.log
      (openHorizontalTubeProbability (iidSequenceLaw ν)
        (1 / 2) (width * scale n) (horizon n)).toReal) ≤
        (τ / (c ^ α)) * Real.log q := by
    simpa [one_mul] using hfixed
  calc
    _ ≤ (τ / (c ^ α)) * Real.log q := hfixed'
    _ = τ * (rate + 2 * ε) := by
      rw [show q = Real.exp ((rate + 2 * ε) * c ^ α) by rfl, Real.log_exp]
      field_simp [ne_of_gt hconstant]


/-- The escape-rate estimate transfers to translation-invariant range
probabilities on any macroscopic segment. -/
theorem limsup_stableSmallDeviationRate_mul_log_partialSumRangeOscillationLTProbability_le_of_escapeRate_on_segment
    {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {α C width τ : ℝ} {normalization scale : ℕ → ℝ}
    {horizon : ℕ → ℕ}
    (hscale : IsStableMogulskiiScale α ν normalization scale)
    (hα : 0 < α) (hα₂ : α ≤ 2)
    (hslow : Asymptotics.IsSlowlyVaryingAtTop (stableSlowVariation α ν))
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hEscape : HasStableProcessEscapeRate α μ P C)
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization (fun _ => 0))
    (htightBase : IsTightMeasureSet
      (Set.range fun n => RandomWalk.normalizedStepPathLaw ν normalization n))
    (hwidth : 0 < width) (hτ : 0 < τ)
    (hhorizon : Tendsto (fun n => (horizon n : ℝ) / (n : ℝ))
      atTop (𝓝 τ))
    {margin ε : ℝ} (hmargin : 0 < margin) (hε : 0 < ε)
    (hnegative : C / (((width + margin) / 2) ^ α) + 2 * ε < 0)
    (hpositive : ∀ᶠ n : ℕ in atTop,
      0 < partialSumRangeOscillationLTProbability (iidSequenceLaw ν)
        (width * scale n) (horizon n))
    (hlowerCobounded : Filter.IsCoboundedUnder (· ≤ ·) atTop
      (fun n => stableSmallDeviationRate α ν scale n * Real.log
        (partialSumRangeOscillationLTProbability (iidSequenceLaw ν)
          (width * scale n) (horizon n)).toReal)) :
    atTop.limsup (fun n => stableSmallDeviationRate α ν scale n * Real.log
      (partialSumRangeOscillationLTProbability (iidSequenceLaw ν)
        (width * scale n) (horizon n)).toReal) ≤
      τ * (C / (((width + margin) / 2) ^ α) + 2 * ε) := by
  let radius : ℝ := (width + margin) / 2
  let rate : ℝ := C / radius ^ α
  have hradius : 0 < radius := by
    dsimp [radius]
    linarith
  have hbaseEvent : ∀ᶠ c : ℝ in atTop,
      P (stableProcessTube (radius / c)) <
          ENNReal.ofReal (Real.exp ((rate + 2 * ε) * c ^ α)) ∧
        Real.exp ((rate + 2 * ε) * c ^ α) < 1 := by
    have h := hEscape.eventually_tube_lt_of_exp_rate hradius hε (by
      simpa [radius, rate] using hnegative)
    simpa [radius, rate] using h
  obtain ⟨c₀, hc₀⟩ := Filter.eventually_atTop.1
    (hbaseEvent.and (eventually_gt_atTop (0 : ℝ)))
  let c : ℝ := max c₀ 1
  have hc : 0 < c := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hcData := hc₀ c (le_max_left _ _)
  have hbaseData :
      P (stableProcessTube (radius / c)) <
          ENNReal.ofReal (Real.exp ((rate + 2 * ε) * c ^ α)) ∧
        Real.exp ((rate + 2 * ε) * c ^ α) < 1 := hcData.1
  have hconstant : 0 < c ^ α := Real.rpow_pos_of_pos hc α
  have hblockLength : Tendsto
      (stableBlockLength α ν (c ^ α) scale) atTop atTop := by
    exact tendsto_stableBlockLength_atTop_of_slowVariation
      hα hα₂ hslow hconstant (IsStableMogulskiiScale.scale_tendsto_atTop hscale)
  have hblockPos : ∀ᶠ n : ℕ in atTop,
      0 < stableBlockLength α ν (c ^ α) scale n :=
    hblockLength.eventually (eventually_gt_atTop 0)
  have hblockEq : (fun n => stableBlockLength α ν (c ^ α) scale n) =
      Asymptotics.floorBlockLength
        (fun n => c ^ α * stableScaleTime α ν (scale n)) := by
    funext n
    change ⌊stableBlockArgument α ν (c ^ α) scale n⌋₊ =
      ⌊c ^ α * stableScaleTime α ν (scale n)⌋₊
    congr 1
    rw [stableBlockArgument, stableScaleTime, mul_div_assoc]
  have hnorm := IsStableMogulskiiScale.stableNorming hscale
  have hnormRatioBase := hnorm.tendsto_floorBlock_normalization_div_scale
    hα hα₂ hslow (IsStableMogulskiiScale.scale_tendsto_atTop hscale) hconstant
  have hnormRatio : Tendsto
      (fun n => normalization (stableBlockLength α ν (c ^ α) scale n) /
        scale n) atTop (𝓝 c) := by
    have hbase : Tendsto
        (fun n => normalization (stableBlockLength α ν (c ^ α) scale n) /
          scale n) atTop (𝓝 ((c ^ α) ^ (1 / α))) := by
      apply hnormRatioBase.congr'
      filter_upwards [] with n
      simp [hblockEq]
    have hroot : (c ^ α) ^ (1 / α) = c := by
      rw [← Real.rpow_mul (le_of_lt hc) α (1 / α)]
      have hmul : α * (1 / α) = 1 := by field_simp [ne_of_gt hα]
      rw [hmul, Real.rpow_one]
    convert hbase using 1
    exact congrArg nhds hroot.symm
  have hnormBlockPos : ∀ᶠ n : ℕ in atTop,
      0 < normalization (stableBlockLength α ν (c ^ α) scale n) := by
    filter_upwards [hblockPos] with n hn
    exact (IsStableMogulskiiScale.stableNorming hscale).1 _ hn
  have hlimit :=
    RandomWalk.FunctionalLimit.Stable.tendstoInDistribution_normalizedStepBlockPathLaw_of_baseTightness
      hDOA (hEscape.isStableClockProcessLaw) htightBase hblockLength
      (IsStableMogulskiiScale.eventually_scale_pos hscale) hnormBlockPos hnormRatio
  let q : ℝ := Real.exp ((rate + 2 * ε) * c ^ α)
  have hq : 0 < q := Real.exp_pos _
  have hqOne : q < 1 := by simpa [q] using hbaseData.2
  have hbase : P (stableProcessTube ((width + margin) / (2 * c))) <
      ENNReal.ofReal q := by
    simpa [q, radius, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      hbaseData.1
  have hfixed :=
    limsup_stableSmallDeviationRate_mul_log_partialSumRangeOscillationLTProbability_le_of_blockPathLimit
      hscale hα hα₂ hslow hconstant (τ := τ) hτ hhorizon hEscape.isStableClockProcessLaw
      hc hwidth hmargin hlimit hq hbase (by simpa using hpositive)
      (by simpa using hlowerCobounded)
  have hfixed' : atTop.limsup (fun n => stableSmallDeviationRate α ν scale n * Real.log
      (partialSumRangeOscillationLTProbability (iidSequenceLaw ν)
        (width * scale n) (horizon n)).toReal) ≤
        (τ / (c ^ α)) * Real.log q := by
    simpa [one_mul] using hfixed
  calc
    _ ≤ (τ / (c ^ α)) * Real.log q := hfixed'
    _ = τ * (rate + 2 * ε) := by
      rw [show q = Real.exp ((rate + 2 * ε) * c ^ α) by rfl, Real.log_exp]
      field_simp [ne_of_gt hconstant]


/-- The fixed-parameter block argument proves the stable horizontal-tube
upper rate with arbitrary positive corridor and logarithmic slacks. The
block parameter is chosen large enough that the escape-rate estimate supplies
a strict base below one; the variable-block path limit is obtained from the
stable random-walk functional limit and the rounded inverse norming theorem.
The remaining slow diagonal is only needed when this estimate is assembled
simultaneously with other fixed-parameter estimates. -/
theorem limsup_stableSmallDeviationRate_mul_log_openHorizontalTubeProbability_le_of_escapeRate
    {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {α C : ℝ} {normalization scale : ℕ → ℝ}
    (hscale : IsStableMogulskiiScale α ν normalization scale)
    (hα : 0 < α) (hα₂ : α ≤ 2)
    (hslow : Asymptotics.IsSlowlyVaryingAtTop (stableSlowVariation α ν))
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hEscape : HasStableProcessEscapeRate α μ P C)
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization (fun _ => 0))
    (htightBase : IsTightMeasureSet
      (Set.range fun n => RandomWalk.normalizedStepPathLaw ν normalization n))
    {margin ε : ℝ} (hmargin : 0 < margin) (hε : 0 < ε)
    (hnegative : C / (((1 + margin) / 2) ^ α) + 2 * ε < 0)
    (hpositive : ∀ᶠ n : ℕ in atTop,
      0 < openHorizontalTubeProbability (iidSequenceLaw ν) (1 / 2) (scale n) n)
    (hlowerCobounded : Filter.IsCoboundedUnder (· ≤ ·) atTop
      (fun n => stableSmallDeviationRate α ν scale n * Real.log
        (openHorizontalTubeProbability (iidSequenceLaw ν)
          (1 / 2) (scale n) n).toReal)) :
    atTop.limsup (fun n => stableSmallDeviationRate α ν scale n * Real.log
      (openHorizontalTubeProbability (iidSequenceLaw ν)
        (1 / 2) (scale n) n).toReal) ≤
      C / (((1 + margin) / 2) ^ α) + 2 * ε := by
  have hfullHorizon : Tendsto (fun n : ℕ => (n : ℝ) / (n : ℝ))
      atTop (𝓝 (1 : ℝ)) := by
    have heq : (fun n : ℕ => (n : ℝ) / (n : ℝ)) =ᶠ[atTop]
        fun _ => (1 : ℝ) := by
      filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
      have hnNe : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      field_simp
    exact (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).congr' heq.symm
  simpa [one_mul] using
    limsup_stableSmallDeviationRate_mul_log_openHorizontalTubeProbability_le_of_escapeRate_on_segment
      hscale hα hα₂ hslow hEscape hDOA htightBase
      (width := 1) (by norm_num) (τ := 1) (by norm_num) hfullHorizon
      hmargin hε hnegative (by simpa using hpositive)
      (by simpa using hlowerCobounded)

/-- The centered horizontal-tube upper rate is the stable escape constant
scaled by the inverse `α`-power of the tube's half-width. This is the
constant-width case of the upper half of Mogulskii's theorem. The hypotheses
are the stable path-law escape rate, the stable random-walk `J₁` limit with
its tightness input, and the lower-side positivity/coboundedness needed for
real logarithms. -/
theorem limsup_stableSmallDeviationRate_mul_log_openHorizontalTubeProbability_le
    {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {α C : ℝ} {normalization scale : ℕ → ℝ}
    (hscale : IsStableMogulskiiScale α ν normalization scale)
    (hα : 0 < α) (hα₂ : α ≤ 2)
    (hslow : Asymptotics.IsSlowlyVaryingAtTop (stableSlowVariation α ν))
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hEscape : HasStableProcessEscapeRate α μ P C)
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization (fun _ => 0))
    (htightBase : IsTightMeasureSet
      (Set.range fun n => RandomWalk.normalizedStepPathLaw ν normalization n))
    (hpositive : ∀ᶠ n : ℕ in atTop,
      0 < openHorizontalTubeProbability (iidSequenceLaw ν) (1 / 2) (scale n) n)
    (hlowerCobounded : Filter.IsCoboundedUnder (· ≤ ·) atTop
      (fun n => stableSmallDeviationRate α ν scale n * Real.log
        (openHorizontalTubeProbability (iidSequenceLaw ν)
          (1 / 2) (scale n) n).toReal)) :
    atTop.limsup (fun n => stableSmallDeviationRate α ν scale n * Real.log
      (openHorizontalTubeProbability (iidSequenceLaw ν)
        (1 / 2) (scale n) n).toReal) ≤ C / ((1 / 2 : ℝ) ^ α) := by
  let target : ℝ := C / ((1 / 2 : ℝ) ^ α)
  let marginSeq : ℕ → ℝ := fun k => 1 / ((k + 1 : ℕ) : ℝ)
  have hden : Tendsto (fun m : ℝ => (1 + m) / 2) (𝓝 0) (𝓝 (1 / 2 : ℝ)) := by
    convert (tendsto_id.add_const (1 : ℝ)).div_const (2 : ℝ) using 1
    · ext m
      simp only [id_eq]
      ring
    · norm_num
  have hpow : Tendsto (fun m : ℝ => ((1 + m) / 2) ^ α)
      (𝓝 0) (𝓝 ((1 / 2 : ℝ) ^ α)) := by
    exact (Real.continuousAt_rpow_const (1 / 2 : ℝ) α
      (Or.inl (by norm_num : (1 / 2 : ℝ) ≠ 0))).tendsto.comp hden
  have hdenPos : 0 < (1 / 2 : ℝ) ^ α := by
    exact Real.rpow_pos_of_pos (by norm_num) α
  have hrateMargin : Tendsto
      (fun m : ℝ => C / (((1 + m) / 2) ^ α)) (𝓝 0) (𝓝 target) := by
    convert (tendsto_const_nhds.div hpow hdenPos.ne') using 1
  have hmarginSeqZero : Tendsto marginSeq atTop (𝓝 0) := by
    convert (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).comp
      (tendsto_add_atTop_nat 1) using 1
    funext k
    simp [marginSeq, Nat.cast_add]
  have hmarginSeqPos (k : ℕ) : 0 < marginSeq k := by
    dsimp [marginSeq]
    positivity
  apply le_of_forall_pos_le_add
  intro δ hδ
  have hcloseTarget : target < target + δ / 2 := by linarith
  have hcloseEvent := (hrateMargin.comp hmarginSeqZero).eventually
    (Iio_mem_nhds hcloseTarget)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hcloseEvent
  let margin : ℝ := marginSeq N
  have hmargin : 0 < margin := hmarginSeqPos N
  have hclose : C / (((1 + margin) / 2) ^ α) < target + δ / 2 := by
    exact hN N le_rfl
  have hmarginBase : 0 < (1 + margin) / 2 := by linarith
  have hmarginPow : 0 < ((1 + margin) / 2) ^ α :=
    Real.rpow_pos_of_pos hmarginBase α
  have hrateNeg : C / (((1 + margin) / 2) ^ α) < 0 :=
    div_neg_of_neg_of_pos hEscape.negative hmarginPow
  let ε : ℝ := min (δ / 8) (-(C / (((1 + margin) / 2) ^ α)) / 4)
  have hε : 0 < ε := by
    dsimp [ε]
    apply lt_min
    · positivity
    · apply div_pos
      · exact neg_pos.mpr hrateNeg
      · norm_num
  have hnegative : C / (((1 + margin) / 2) ^ α) + 2 * ε < 0 := by
    have hεbound : ε ≤ -(C / (((1 + margin) / 2) ^ α)) / 4 := by
      dsimp [ε]
      exact min_le_right _ _
    linarith
  have hεsmall : 2 * ε < δ / 2 := by
    have hεbound : ε ≤ δ / 8 := by
      dsimp [ε]
      exact min_le_left _ _
    linarith
  have hslack := limsup_stableSmallDeviationRate_mul_log_openHorizontalTubeProbability_le_of_escapeRate
    hscale hα hα₂ hslow hEscape hDOA htightBase
    hmargin hε hnegative hpositive hlowerCobounded
  have hresult :
      atTop.limsup (fun n => stableSmallDeviationRate α ν scale n *
        Real.log (openHorizontalTubeProbability (iidSequenceLaw ν)
          (1 / 2) (scale n) n).toReal) < target + δ := by
    calc
      atTop.limsup (fun n => stableSmallDeviationRate α ν scale n *
          Real.log (openHorizontalTubeProbability (iidSequenceLaw ν)
            (1 / 2) (scale n) n).toReal) ≤
        C / (((1 + margin) / 2) ^ α) + 2 * ε := hslack
      _ < target + δ := by linarith
  simpa [target] using hresult.le

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable

end
