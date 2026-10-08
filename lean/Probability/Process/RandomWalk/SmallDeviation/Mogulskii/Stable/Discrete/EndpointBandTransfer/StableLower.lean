/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.Process.RandomWalk.FunctionalLimit.Stable.PathLimit.Block
import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.EndpointBandTransfer.StableRate
import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Scale
import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Scale.Rate
import Probability.Process.Stable.SmallDeviation.EscapeRate.PathLaw

/-!
# Stable lower bounds for shifted endpoint-return blocks

This combines the stable escape rate, the variable-block path limit, and
open-set Portmanteau for an arbitrary shifted interval. It supplies the
finite endpoint-band probabilities needed by the discrete return kernel.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

/-- A stable path-law limit transfers a common lower mass for finitely many
shifted open endpoint corridors to discrete IID return-band events. This
interface is independent of how the block-length sequence was selected. -/
theorem eventually_endpointBandReturnBlockProbability_ge_of_stablePathLimit
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (scale : ℕ → ℝ) (blockLength : ℕ → ℕ)
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (Z : Ω → CadlagPath unitInterval ℝ)
    (hlimit : TendstoInDistribution
      (RandomWalk.normalizedStepBlockCadlagPathIcc scale blockLength)
      atTop Z (fun _ => iidSequenceLaw ν) P)
    (hscale : ∀ᶠ n in atTop, 0 < scale n)
    (hblock : ∀ᶠ n in atTop, 0 < blockLength n)
    {lower upper epsilon : ℝ}
    (hlower : lower + 4 * epsilon < 0)
    (hupper : 0 < upper - 4 * epsilon)
    (lowerBound : ENNReal)
    (hbelow : ∀ i ∈ Finset.Icc (-3 : ℤ) 3,
      lowerBound < P.map Z
        (Skorokhod.rangeInOpenIntervalEndsIn
          (lower + 4 * epsilon) (upper - 4 * epsilon)
          (((i : ℝ) - 1) * epsilon) (((i : ℝ) + 1) * epsilon))) :
    ∀ᶠ n : ℕ in atTop,
      ∀ i ∈ Finset.Icc (-3 : ℤ) 3,
        lowerBound ≤ iidSequenceLaw ν
          (endpointBandReturnBlockEvent (lower * scale n) (upper * scale n)
            (epsilon * scale n) i (blockLength n)) :=
  eventually_forall_normalizedEndpointBandReturnProbability_ge_of_pathLawLimit
    ν scale blockLength Z hlimit hscale hblock hlower hupper lowerBound hbelow

/-- Open-set Portmanteau transfers one arbitrary open displacement window,
not only a band centered at one of the seven return indices. -/
theorem eventually_endpointCorridorBlockProbability_ge_of_stablePathLimit
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (scale : ℕ → ℝ) (blockLength : ℕ → ℕ)
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (Z : Ω → CadlagPath unitInterval ℝ)
    (hlimit : TendstoInDistribution
      (RandomWalk.normalizedStepBlockCadlagPathIcc scale blockLength)
      atTop Z (fun _ => iidSequenceLaw ν) P)
    (hscale : ∀ᶠ n in atTop, 0 < scale n)
    (hblock : ∀ᶠ n in atTop, 0 < blockLength n)
    {lower upper endpointLower endpointUpper : ℝ}
    (hlower : lower < 0) (hupper : 0 < upper)
    (lowerBound : ENNReal)
    (hbelow : lowerBound < P.map Z
      (Skorokhod.rangeInOpenIntervalEndsIn
        lower upper endpointLower endpointUpper)) :
    ∀ᶠ n : ℕ in atTop,
      lowerBound ≤ iidSequenceLaw ν
        (endpointCorridorBlockEvent
          (lower * scale n) (upper * scale n)
          (endpointLower * scale n) (endpointUpper * scale n)
          (blockLength n)) := by
  let corridor := Skorokhod.rangeInOpenIntervalEndsIn
    lower upper endpointLower endpointUpper
  have hport := hlimit.measure_skorokhodCorridorEndsIn_le_liminf
    lower upper endpointLower endpointUpper
  have hbelow' : lowerBound < P.map Z corridor := by simpa [corridor] using hbelow
  have hstrict : lowerBound < atTop.liminf
      (fun n => RandomWalk.normalizedStepBlockPathLaw ν scale blockLength n corridor) :=
    hbelow'.trans_le (by
      simpa [corridor, RandomWalk.normalizedStepBlockPathLaw] using hport)
  have hbounded : Filter.IsBoundedUnder (· ≥ ·) atTop
      (fun n => RandomWalk.normalizedStepBlockPathLaw ν scale blockLength n corridor) :=
    Filter.isBoundedUnder_of_eventually_ge
      (Eventually.of_forall fun _ => bot_le)
  have heventuallyPath := eventually_lt_of_lt_liminf hstrict hbounded
  have hsetEq : ∀ᶠ n in atTop,
      {increment : ℕ → ℝ |
        InOpenPartialSumCorridor (lower * scale n) (upper * scale n)
            (Combinatorics.Sequence.blockCoordinates 0 (blockLength n) increment) ∧
          Fin.partialSum
              (Combinatorics.Sequence.blockCoordinates 0 (blockLength n) increment)
              (Fin.last (blockLength n)) / scale n ∈
            Set.Ioo endpointLower endpointUpper} =
        endpointCorridorBlockEvent
          (lower * scale n) (upper * scale n)
          (endpointLower * scale n) (endpointUpper * scale n)
          (blockLength n) := by
    filter_upwards [hscale] with n hs
    ext increment
    change
      (InOpenPartialSumCorridor (lower * scale n) (upper * scale n)
          (Combinatorics.Sequence.blockCoordinates 0 (blockLength n) increment) ∧
        Fin.partialSum
            (Combinatorics.Sequence.blockCoordinates 0 (blockLength n) increment)
            (Fin.last (blockLength n)) / scale n ∈
          Set.Ioo endpointLower endpointUpper) ↔
      (InOpenPartialSumCorridor (lower * scale n) (upper * scale n)
          (Combinatorics.Sequence.blockCoordinates 0 (blockLength n) increment) ∧
        Fin.partialSum
            (Combinatorics.Sequence.blockCoordinates 0 (blockLength n) increment)
            (Fin.last (blockLength n)) ∈
          Set.Ioo (endpointLower * scale n) (endpointUpper * scale n))
    constructor
    · rintro ⟨hpath, hend⟩
      refine ⟨hpath, ?_⟩
      constructor
      · exact (lt_div_iff₀ hs).mp hend.1
      · exact (div_lt_iff₀ hs).mp hend.2
    · rintro ⟨hpath, hend⟩
      refine ⟨hpath, ?_⟩
      constructor
      · exact (lt_div_iff₀ hs).mpr hend.1
      · exact (div_lt_iff₀ hs).mpr hend.2
  have hpathLawEq : ∀ᶠ n in atTop,
      RandomWalk.normalizedStepBlockPathLaw ν scale blockLength n corridor =
        iidSequenceLaw ν
          (endpointCorridorBlockEvent
            (lower * scale n) (upper * scale n)
            (endpointLower * scale n) (endpointUpper * scale n)
            (blockLength n)) := by
    filter_upwards [hblock, hscale, hsetEq] with n hn hs hset
    rw [RandomWalk.normalizedStepBlockPathLaw_apply_shiftedCorridorEndsIn
      ν scale blockLength n hn hs hlower hupper]
    simpa [corridor] using congrArg (iidSequenceLaw ν) hset
  filter_upwards [heventuallyPath, hpathLawEq] with n hpath heq
  rw [heq] at hpath
  exact hpath.le

/-- The endpoint-band lower estimate holds for any block-length sequence
whose stable time ratio tends to the prescribed amplitude. This avoids
requiring the block length to be a particular floor, which is essential when
partitioning a cell into blocks of exactly equal or nearly equal length. -/
theorem eventually_endpointBandReturnBlockProbability_ge_of_stableScaleTimeRatio
    {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {α C : ℝ} {normalization scale : ℕ → ℝ}
    (hscale : IsStableMogulskiiScale α ν normalization scale)
    (hα : 0 < α) (hα₂ : α ≤ 2)
    (hslow : Asymptotics.IsSlowlyVaryingAtTop
      (stableSlowVariation α ν))
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hEscape : HasStableProcessEscapeRate α μ P C)
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization (fun _ => 0))
    (htightBase : IsTightMeasureSet
      (Set.range fun n => RandomWalk.normalizedStepPathLaw ν normalization n))
    (blockLength : ℕ → ℕ)
    (hblockTop : Tendsto blockLength atTop atTop)
    {amplitude : ℝ} (hamplitude : 0 < amplitude)
    (hblockRatio : Tendsto
      (fun n => (blockLength n : ℝ) /
        stableScaleTime α ν (scale n)) atTop (nhds (amplitude ^ α)))
    {lower upper epsilon : ℝ}
    (hlower : lower + 4 * epsilon < 0)
    (hupper : 0 < upper - 4 * epsilon)
    (lowerBound : ENNReal)
    (hbelow : ∀ i ∈ Finset.Icc (-3 : ℤ) 3,
      lowerBound < P.map (Skorokhod.scalePath amplitude)
        (Skorokhod.rangeInOpenIntervalEndsIn
          (lower + 4 * epsilon) (upper - 4 * epsilon)
          (((i : ℝ) - 1) * epsilon) (((i : ℝ) + 1) * epsilon))) :
    ∀ᶠ n : ℕ in atTop,
      ∀ i ∈ Finset.Icc (-3 : ℤ) 3,
        lowerBound ≤ iidSequenceLaw ν
          (endpointBandReturnBlockEvent (lower * scale n) (upper * scale n)
            (epsilon * scale n) i (blockLength n)) := by
  have hscaleTop : Tendsto scale atTop atTop :=
    IsStableMogulskiiScale.scale_tendsto_atTop hscale
  have hscalePos : ∀ᶠ n in atTop, 0 < scale n :=
    IsStableMogulskiiScale.eventually_scale_pos hscale
  have hnormBlockPos : ∀ᶠ n in atTop,
      0 < normalization (blockLength n) :=
    (hscale.stableNorming.2.1.comp hblockTop).eventually
      (eventually_gt_atTop 0)
  have hnormRatio' :=
    hscale.stableNorming.tendsto_normalization_div_scale_of_blockLengthRatio
      hα hα₂ hslow hscaleTop
      (Real.rpow_pos_of_pos hamplitude α) hblockTop hblockRatio
  have hroot : (amplitude ^ α) ^ (1 / α) = amplitude := by
    rw [← Real.rpow_mul (le_of_lt hamplitude) α (1 / α)]
    have hmul : α * (1 / α) = 1 := by field_simp [ne_of_gt hα]
    rw [hmul, Real.rpow_one]
  have hnormRatio : Tendsto
      (fun n => normalization (blockLength n) / scale n)
      atTop (nhds amplitude) := by
    convert hnormRatio' using 1
    exact congrArg nhds hroot.symm
  have hlimit :=
    RandomWalk.FunctionalLimit.Stable.tendstoInDistribution_normalizedStepBlockPathLaw_of_baseTightness
      hDOA hEscape.isStableClockProcessLaw htightBase hblockTop
      hscalePos hnormBlockPos hnormRatio
  have hscaleMapMeas : Measurable (Skorokhod.scalePath amplitude) :=
    (Skorokhod.continuous_scalePath.comp
      (continuous_const.prodMk continuous_id)).measurable
  have hlimit' := hlimit.congr_limit (μ'' := P)
    (Z' := Skorokhod.scalePath amplitude) hscaleMapMeas.aemeasurable (by simp)
  exact eventually_endpointBandReturnBlockProbability_ge_of_stablePathLimit
    ν scale blockLength (Z := Skorokhod.scalePath amplitude) hlimit'
    hscalePos (hblockTop.eventually (eventually_gt_atTop 0)) hlower hupper
    lowerBound hbelow

/-- The variable-block stable limit transfers a fixed arbitrary endpoint
window inside a shifted corridor whenever the block's stable time ratio has a
positive limit. This is the one-block bridge estimate for distinct endpoint
cores. -/
theorem eventually_endpointCorridorBlockProbability_ge_of_stableScaleTimeRatio
    {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {α C : ℝ} {normalization scale : ℕ → ℝ}
    (hscale : IsStableMogulskiiScale α ν normalization scale)
    (hα : 0 < α) (hα₂ : α ≤ 2)
    (hslow : Asymptotics.IsSlowlyVaryingAtTop
      (stableSlowVariation α ν))
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hEscape : HasStableProcessEscapeRate α μ P C)
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization (fun _ => 0))
    (htightBase : IsTightMeasureSet
      (Set.range fun n => RandomWalk.normalizedStepPathLaw ν normalization n))
    (blockLength : ℕ → ℕ)
    (hblockTop : Tendsto blockLength atTop atTop)
    {amplitude : ℝ} (hamplitude : 0 < amplitude)
    (hblockRatio : Tendsto
      (fun n => (blockLength n : ℝ) /
        stableScaleTime α ν (scale n)) atTop (nhds (amplitude ^ α)))
    {lower upper endpointLower endpointUpper : ℝ}
    (hlower : lower < 0) (hupper : 0 < upper)
    (lowerBound : ENNReal)
    (hbelow : lowerBound < P.map (Skorokhod.scalePath amplitude)
      (Skorokhod.rangeInOpenIntervalEndsIn
        lower upper endpointLower endpointUpper)) :
    ∀ᶠ n : ℕ in atTop,
      lowerBound ≤ iidSequenceLaw ν
        (endpointCorridorBlockEvent
          (lower * scale n) (upper * scale n)
          (endpointLower * scale n) (endpointUpper * scale n)
          (blockLength n)) := by
  have hscaleTop : Tendsto scale atTop atTop :=
    IsStableMogulskiiScale.scale_tendsto_atTop hscale
  have hscalePos : ∀ᶠ n in atTop, 0 < scale n :=
    IsStableMogulskiiScale.eventually_scale_pos hscale
  have hnormBlockPos : ∀ᶠ n in atTop,
      0 < normalization (blockLength n) :=
    (hscale.stableNorming.2.1.comp hblockTop).eventually
      (eventually_gt_atTop 0)
  have hnormRatio' :=
    hscale.stableNorming.tendsto_normalization_div_scale_of_blockLengthRatio
      hα hα₂ hslow hscaleTop
      (Real.rpow_pos_of_pos hamplitude α) hblockTop hblockRatio
  have hroot : (amplitude ^ α) ^ (1 / α) = amplitude := by
    rw [← Real.rpow_mul (le_of_lt hamplitude) α (1 / α)]
    have hmul : α * (1 / α) = 1 := by field_simp [ne_of_gt hα]
    rw [hmul, Real.rpow_one]
  have hnormRatio : Tendsto
      (fun n => normalization (blockLength n) / scale n)
      atTop (nhds amplitude) := by
    convert hnormRatio' using 1
    exact congrArg nhds hroot.symm
  have hlimit :=
    RandomWalk.FunctionalLimit.Stable.tendstoInDistribution_normalizedStepBlockPathLaw_of_baseTightness
      hDOA hEscape.isStableClockProcessLaw htightBase hblockTop
      hscalePos hnormBlockPos hnormRatio
  have hscaleMapMeas : Measurable (Skorokhod.scalePath amplitude) :=
    (Skorokhod.continuous_scalePath.comp
      (continuous_const.prodMk continuous_id)).measurable
  have hlimit' := hlimit.congr_limit (μ'' := P)
    (Z' := Skorokhod.scalePath amplitude) hscaleMapMeas.aemeasurable (by simp)
  exact eventually_endpointCorridorBlockProbability_ge_of_stablePathLimit
    ν scale blockLength (Z := Skorokhod.scalePath amplitude) hlimit'
    hscalePos (hblockTop.eventually (eventually_gt_atTop 0))
    hlower hupper lowerBound hbelow

/-- One stable path limit transfers a uniform lower mass for a finite family
of open endpoint windows. This is the form needed for bridges between
different endpoint cores. -/
theorem eventually_endpointCorridorBlockProbabilityFamily_ge_of_stableScaleTimeRatio
    {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {α C : ℝ} {normalization scale : ℕ → ℝ}
    (hscale : IsStableMogulskiiScale α ν normalization scale)
    (hα : 0 < α) (hα₂ : α ≤ 2)
    (hslow : Asymptotics.IsSlowlyVaryingAtTop
      (stableSlowVariation α ν))
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hEscape : HasStableProcessEscapeRate α μ P C)
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization (fun _ => 0))
    (htightBase : IsTightMeasureSet
      (Set.range fun n => RandomWalk.normalizedStepPathLaw ν normalization n))
    (blockLength : ℕ → ℕ)
    (hblockTop : Tendsto blockLength atTop atTop)
    {amplitude : ℝ} (hamplitude : 0 < amplitude)
    (hblockRatio : Tendsto
      (fun n => (blockLength n : ℝ) /
        stableScaleTime α ν (scale n)) atTop (nhds (amplitude ^ α)))
    {ι : Type*} [DecidableEq ι] (indices : Finset ι)
    (lower upper endpointLower endpointUpper : ι → ℝ)
    (hlower : ∀ i ∈ indices, lower i < 0)
    (hupper : ∀ i ∈ indices, 0 < upper i)
    (lowerBound : ENNReal)
    (hbelow : ∀ i ∈ indices,
      lowerBound < P.map (Skorokhod.scalePath amplitude)
        (Skorokhod.rangeInOpenIntervalEndsIn
          (lower i) (upper i) (endpointLower i) (endpointUpper i))) :
    ∀ᶠ n : ℕ in atTop,
      ∀ i ∈ indices,
        lowerBound ≤ iidSequenceLaw ν
          (endpointCorridorBlockEvent
            (lower i * scale n) (upper i * scale n)
            (endpointLower i * scale n) (endpointUpper i * scale n)
            (blockLength n)) := by
  classical
  apply indices.eventually_all.2
  intro i hi
  exact eventually_endpointCorridorBlockProbability_ge_of_stableScaleTimeRatio
    hscale hα hα₂ hslow hEscape hDOA htightBase blockLength hblockTop
    hamplitude hblockRatio (hlower i hi) (hupper i hi) lowerBound
    (hbelow i hi)

/-- In a macroscopic partition cell, split the floor-rounded horizon into
balanced blocks around a stable reference length. Both possible integer
lengths diverge and have the same stable time ratio. This is the asymptotic
input needed to apply one stable endpoint-band estimate to every block in an
exact cell partition. -/
theorem balancedStableCellBlock_asymptotics
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {α : ℝ} {normalization scale : ℕ → ℝ}
    (hscale : IsStableMogulskiiScale α ν normalization scale)
    (hα : 0 < α) (hα₂ : α ≤ 2)
    (hslow : Asymptotics.IsSlowlyVaryingAtTop
      (stableSlowVariation α ν))
    (total : ℕ → ℕ) {duration amplitude : ℝ}
    (hduration : 0 < duration) (hamplitude : 0 < amplitude)
    (htotal : Tendsto (fun n => (total n : ℝ) / (n : ℝ))
      atTop (nhds duration)) :
    Tendsto
        (fun n => (Asymptotics.balancedBlockCount (total n)
          (stableBlockLength α ν (amplitude ^ α) scale n) : ℝ)) atTop atTop ∧
      Tendsto
        (fun n => Asymptotics.balancedBlockShortLength (total n)
          (stableBlockLength α ν (amplitude ^ α) scale n)) atTop atTop ∧
      Tendsto
        (fun n => Asymptotics.balancedBlockShortLength (total n)
          (stableBlockLength α ν (amplitude ^ α) scale n) + 1) atTop atTop ∧
      Tendsto (fun n =>
        (Asymptotics.balancedBlockShortLength (total n)
          (stableBlockLength α ν (amplitude ^ α) scale n) : ℝ) /
          stableScaleTime α ν (scale n)) atTop (nhds (amplitude ^ α)) ∧
      Tendsto (fun n =>
        ((Asymptotics.balancedBlockShortLength (total n)
          (stableBlockLength α ν (amplitude ^ α) scale n) + 1 : ℕ) : ℝ) /
          stableScaleTime α ν (scale n)) atTop (nhds (amplitude ^ α)) := by
  let reference : ℕ → ℕ := fun n => stableBlockLength α ν (amplitude ^ α) scale n
  have hscaleTop : Tendsto scale atTop atTop :=
    IsStableMogulskiiScale.scale_tendsto_atTop hscale
  have hrate : Tendsto (stableSmallDeviationRate α ν scale) atTop (nhds 0) :=
    tendsto_stableSmallDeviationRate_zero_of_slowVariation
      hscale.stableNorming hscaleTop hscale.scale_div_normalization_tendsto_zero
      hα hα₂ hslow
  have hrefTop : Tendsto reference atTop atTop := by
    simpa [reference] using tendsto_stableBlockLength_atTop_of_slowVariation
      hα hα₂ hslow (Real.rpow_pos_of_pos hamplitude α) hscaleTop
  have hrefPos : ∀ᶠ n : ℕ in atTop, 0 < reference n :=
    hrefTop.eventually (eventually_gt_atTop 0)
  have hrefRatioZero : Tendsto (fun n => (reference n : ℝ) / (n : ℝ))
      atTop (nhds 0) := by
    simpa [reference] using tendsto_stableBlockLength_div_nat_zero_of_slowVariation
      hα hα₂ hslow (Real.rpow_pos_of_pos hamplitude α) hscaleTop hrate
  have hcount : Tendsto
      (fun n => (Asymptotics.balancedBlockCount (total n) (reference n) : ℝ))
      atTop atTop := by
    have hnat := Asymptotics.tendsto_nat_div_atTop_of_positive_horizonRatio_of_zero_blockRatio
      htotal hduration hrefRatioZero hrefPos
    exact tendsto_natCast_atTop_atTop.comp hnat
  have hrefTopReal : Tendsto (fun n => (reference n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hrefTop
  have hshortRatio := Asymptotics.tendsto_balancedBlockShortLength_div_referenceLength
    (total := total) (referenceLength := reference) hrefTopReal hcount
  have hlongRatio := Asymptotics.tendsto_balancedBlockLongLength_div_referenceLength
    (total := total) (referenceLength := reference) hrefTopReal hcount
  have hreferenceStableRatio := tendsto_stableBlockLength_div_stableScaleTime_of_slowVariation
    hα hα₂ hslow (Real.rpow_pos_of_pos hamplitude α) hscaleTop
  have hkappaPos : ∀ᶠ n : ℕ in atTop, 0 < stableScaleTime α ν (scale n) := by
    have hkappaTop :=
      (stableScaleTime_tendsto_atTop_of_stableSlowVariation hα hα₂ hslow).comp hscaleTop
    exact hkappaTop.eventually (eventually_gt_atTop 0)
  have hshortStableRatio : Tendsto (fun n =>
      (Asymptotics.balancedBlockShortLength (total n) (reference n) : ℝ) /
        stableScaleTime α ν (scale n)) atTop (nhds (amplitude ^ α)) := by
    have hproduct := hshortRatio.mul hreferenceStableRatio
    have heq : (fun n =>
        (Asymptotics.balancedBlockShortLength (total n) (reference n) : ℝ) /
          stableScaleTime α ν (scale n)) =ᶠ[atTop] fun n =>
        ((Asymptotics.balancedBlockShortLength (total n) (reference n) : ℝ) /
          (reference n : ℝ)) *
          ((reference n : ℝ) / stableScaleTime α ν (scale n)) := by
      filter_upwards [hrefPos, hkappaPos] with n hn hκ
      have hre : (reference n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      have hκne : stableScaleTime α ν (scale n) ≠ 0 := hκ.ne'
      field_simp [hre, hκne]
    simpa using hproduct.congr' heq.symm
  have hlongStableRatio : Tendsto (fun n =>
      ((Asymptotics.balancedBlockShortLength (total n) (reference n) + 1 : ℕ) : ℝ) /
        stableScaleTime α ν (scale n)) atTop (nhds (amplitude ^ α)) := by
    have hproduct := hlongRatio.mul hreferenceStableRatio
    have heq : (fun n =>
        ((Asymptotics.balancedBlockShortLength (total n) (reference n) + 1 : ℕ) : ℝ) /
          stableScaleTime α ν (scale n)) =ᶠ[atTop] fun n =>
        (((Asymptotics.balancedBlockShortLength (total n) (reference n) + 1 : ℕ) : ℝ) /
          (reference n : ℝ)) *
          ((reference n : ℝ) / stableScaleTime α ν (scale n)) := by
      filter_upwards [hrefPos, hkappaPos] with n hn hκ
      have hre : (reference n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      have hκne : stableScaleTime α ν (scale n) ≠ 0 := hκ.ne'
      field_simp [hre, hκne]
    simpa using hproduct.congr' heq.symm
  have hshortTop : Tendsto
      (fun n => Asymptotics.balancedBlockShortLength (total n) (reference n))
      atTop atTop := by
    apply tendsto_atTop_mono' atTop ?_ hrefTop
    filter_upwards [] with n
    exact_mod_cast (Nat.le_add_right (reference n)
      ((total n % reference n) / Asymptotics.balancedBlockCount (total n) (reference n)))
  have hlongTop : Tendsto
      (fun n => Asymptotics.balancedBlockShortLength (total n) (reference n) + 1)
      atTop atTop := by
    apply tendsto_atTop_mono' atTop ?_ hshortTop
    filter_upwards [] with n
    exact_mod_cast (Nat.le_add_right
      (Asymptotics.balancedBlockShortLength (total n) (reference n)) 1)
  exact ⟨hcount, hshortTop, hlongTop, hshortStableRatio, hlongStableRatio⟩

/-- A stable escape rate gives an eventual sharp exponential lower mass for a
fixed open endpoint window strictly inside a corridor containing the origin.
The endpoint location changes the positive prefactor, while the exponent
depends only on the corridor's half-width. -/
theorem eventually_scaledStableEndpointCorridorProbability_ge_exp
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {α C : ℝ}
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hEscape : HasStableProcessEscapeRate α μ P C)
    {Ω : Type*} [MeasurableSpace Ω]
    {X : ℝ≥0 → Ω → ℝ} {Q : Measure Ω} [IsProbabilityMeasure Q]
    (hX : IsStableLevyProcess α μ X Q)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    {lower upper endpointLower endpointUpper delta : ℝ}
    (hlower : lower < 0) (hupper : 0 < upper)
    (hendLower : lower < endpointLower)
    (hendOrder : endpointLower < endpointUpper)
    (hendUpper : endpointUpper < upper) (hdelta : 0 < delta) :
    ∀ᶠ amplitude : ℝ in atTop,
      ENNReal.ofReal (Real.exp
        ((C / (((upper - lower) / 2) ^ α) - delta) * amplitude ^ α)) <
        P.map (Skorokhod.scalePath amplitude)
          (Skorokhod.rangeInOpenIntervalEndsIn
            lower upper endpointLower endpointUpper) := by
  let radius : ℝ := (upper - lower) / 2
  let centerRatio : ℝ := (upper + lower) / (upper - lower)
  let c : ℝ := endpointLower / radius - centerRatio
  let b : ℝ := endpointUpper / radius - centerRatio
  have hwidth : 0 < upper - lower := sub_pos.mpr (lt_trans hlower hupper)
  have hradius : 0 < radius := by dsimp [radius]; linarith
  have hlowerRatio : lower / radius = centerRatio - 1 := by
    dsimp [radius, centerRatio]
    field_simp [ne_of_gt hwidth]
    ring
  have hupperRatio : upper / radius = centerRatio + 1 := by
    dsimp [radius, centerRatio]
    field_simp [ne_of_gt hwidth]
    ring
  have hd : -1 < centerRatio ∧ centerRatio < 1 := by
    constructor
    · have hpos : 0 < upper / radius := div_pos hupper hradius
      rw [hupperRatio] at hpos
      linarith
    · have hneg : lower / radius < 0 := div_neg_of_neg_of_pos hlower hradius
      rw [hlowerRatio] at hneg
      linarith
  have hc : -1 < c := by
    dsimp [c]
    have hdiv := div_lt_div_of_pos_right hendLower hradius
    rw [hlowerRatio] at hdiv
    linarith
  have hb : b < 1 := by
    dsimp [b]
    have hdiv := div_lt_div_of_pos_right hendUpper hradius
    rw [hupperRatio] at hdiv
    linarith
  have hcb : c < b := by
    dsimp [c, b]
    have hdiv := div_lt_div_of_pos_right hendOrder hradius
    linarith
  have hscaled := eventually_scaledStableShiftedEndpointCorridorProbability_ge_exp
    hEscape hX hcdf hradius hdelta hd hc hcb hb
  have hendpointLower : radius * (centerRatio + c) = endpointLower := by
    dsimp [c]
    field_simp [hradius.ne']
    ring
  have hendpointUpper : radius * (centerRatio + b) = endpointUpper := by
    dsimp [b]
    field_simp [hradius.ne']
    ring
  have hleft : radius * (centerRatio - 1) = lower := by
    rw [← hlowerRatio]
    field_simp [hradius.ne']
  have hright : radius * (centerRatio + 1) = upper := by
    rw [← hupperRatio]
    field_simp [hradius.ne']
  have hparams :
      Skorokhod.rangeInOpenIntervalEndsIn
          (radius * (centerRatio - 1)) (radius * (centerRatio + 1))
          (radius * (centerRatio + c)) (radius * (centerRatio + b)) =
        Skorokhod.rangeInOpenIntervalEndsIn lower upper
          endpointLower endpointUpper := by
    rw [hleft, hright, hendpointLower, hendpointUpper]
  filter_upwards [hscaled] with amplitude hmass
  rw [← hparams]
  simpa [radius] using hmass

/-- A finite family of open endpoint windows inside one fixed corridor has a
common eventual stable escape lower bound. The finite intersection is what
allows all entrance and exit bands to use one spatial amplitude. -/
theorem eventually_scaledStableEndpointWindowFamilyProbability_ge_exp
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {α C : ℝ}
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hEscape : HasStableProcessEscapeRate α μ P C)
    {Ω : Type*} [MeasurableSpace Ω]
    {X : ℝ≥0 → Ω → ℝ} {Q : Measure Ω} [IsProbabilityMeasure Q]
    (hX : IsStableLevyProcess α μ X Q)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    {ι : Type*} [DecidableEq ι]
    (indices : Finset ι) (endpointLower endpointUpper : ι → ℝ)
    {lower upper delta : ℝ}
    (hlower : lower < 0) (hupper : 0 < upper)
    (hwindows : ∀ i ∈ indices,
      lower < endpointLower i ∧ endpointLower i < endpointUpper i ∧
        endpointUpper i < upper)
    (hdelta : 0 < delta) :
    ∀ᶠ amplitude : ℝ in atTop,
      ∀ i ∈ indices,
        ENNReal.ofReal (Real.exp
          ((C / (((upper - lower) / 2) ^ α) - delta) * amplitude ^ α)) <
          P.map (Skorokhod.scalePath amplitude)
            (Skorokhod.rangeInOpenIntervalEndsIn
              lower upper (endpointLower i) (endpointUpper i)) := by
  apply indices.eventually_all.2
  intro i hi
  exact eventually_scaledStableEndpointCorridorProbability_ge_exp
    hEscape hX hcdf hlower hupper (hwindows i hi).1 (hwindows i hi).2.1
    (hwindows i hi).2.2 hdelta

/-- A stable escape rate gives the sharp exponential lower mass for any one
fixed open endpoint window strictly inside a corridor containing the origin.
This supplies the finite-cost entrance and exit blocks in the partition
lower bound. -/
theorem exists_stableEndpointCorridorMassLowerBound_of_escapeRate
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {α C : ℝ}
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hEscape : HasStableProcessEscapeRate α μ P C)
    {Ω : Type*} [MeasurableSpace Ω]
    {X : ℝ≥0 → Ω → ℝ} {Q : Measure Ω} [IsProbabilityMeasure Q]
    (hX : IsStableLevyProcess α μ X Q)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    {lower upper endpointLower endpointUpper delta : ℝ}
    (hlower : lower < 0) (hupper : 0 < upper)
    (hendLower : lower < endpointLower)
    (hendOrder : endpointLower < endpointUpper)
    (hendUpper : endpointUpper < upper) (hdelta : 0 < delta) :
    ∃ amplitude : ℝ, 0 < amplitude ∧
      ENNReal.ofReal (Real.exp
        ((C / (((upper - lower) / 2) ^ α) - delta) * amplitude ^ α)) <
        P.map (Skorokhod.scalePath amplitude)
          (Skorokhod.rangeInOpenIntervalEndsIn
            lower upper endpointLower endpointUpper) := by
  let radius : ℝ := (upper - lower) / 2
  let centerRatio : ℝ := (upper + lower) / (upper - lower)
  let c : ℝ := endpointLower / radius - centerRatio
  let b : ℝ := endpointUpper / radius - centerRatio
  have hwidth : 0 < upper - lower := sub_pos.mpr (lt_trans hlower hupper)
  have hradius : 0 < radius := by dsimp [radius]; linarith
  have hlowerRatio : lower / radius = centerRatio - 1 := by
    dsimp [radius, centerRatio]
    field_simp [ne_of_gt hwidth]
    ring
  have hupperRatio : upper / radius = centerRatio + 1 := by
    dsimp [radius, centerRatio]
    field_simp [ne_of_gt hwidth]
    ring
  have hd : -1 < centerRatio ∧ centerRatio < 1 := by
    constructor
    · have hpos : 0 < upper / radius := div_pos hupper hradius
      rw [hupperRatio] at hpos
      linarith
    · have hneg : lower / radius < 0 := div_neg_of_neg_of_pos hlower hradius
      rw [hlowerRatio] at hneg
      linarith
  have hendpointLower : radius * (centerRatio + c) = endpointLower := by
    dsimp [c]
    field_simp [hradius.ne']
    ring
  have hendpointUpper : radius * (centerRatio + b) = endpointUpper := by
    dsimp [b]
    field_simp [hradius.ne']
    ring
  have hc : -1 < c := by
    dsimp [c]
    have hdiv := div_lt_div_of_pos_right hendLower hradius
    rw [hlowerRatio] at hdiv
    linarith
  have hb : b < 1 := by
    dsimp [b]
    have hdiv := div_lt_div_of_pos_right hendUpper hradius
    rw [hupperRatio] at hdiv
    linarith
  have hcb : c < b := by
    dsimp [c, b]
    have hdiv := div_lt_div_of_pos_right hendOrder hradius
    linarith
  have hscaled := eventually_scaledStableShiftedEndpointCorridorProbability_ge_exp
    hEscape hX hcdf hradius (by linarith : 0 < delta / 2) hd hc hcb hb
  obtain ⟨amplitude₀, hmass₀⟩ := Filter.eventually_atTop.1
    (hscaled.and (eventually_gt_atTop (0 : ℝ)))
  let amplitude : ℝ := max amplitude₀ 1
  have hamplitude : 0 < amplitude := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hmass := (hmass₀ amplitude (le_max_left _ _)).1
  have hrate : C / radius ^ α < 0 :=
    div_neg_of_neg_of_pos hEscape.negative (Real.rpow_pos_of_pos hradius α)
  have hlowExponent : (C / radius ^ α - delta) * amplitude ^ α <
      (C / radius ^ α - delta / 2) * amplitude ^ α := by
    have hpower : 0 < amplitude ^ α := Real.rpow_pos_of_pos hamplitude α
    nlinarith
  have hlowENN : ENNReal.ofReal
      (Real.exp ((C / radius ^ α - delta) * amplitude ^ α)) <
      ENNReal.ofReal
        (Real.exp ((C / radius ^ α - delta / 2) * amplitude ^ α)) := by
    apply (ENNReal.ofReal_lt_ofReal_iff (Real.exp_pos _)).2
    exact Real.exp_lt_exp.mpr hlowExponent
  have hleft : radius * (centerRatio - 1) = lower := by
    rw [← hlowerRatio]
    field_simp [hradius.ne']
  have hright : radius * (centerRatio + 1) = upper := by
    rw [← hupperRatio]
    field_simp [hradius.ne']
  have hparams :
      Skorokhod.rangeInOpenIntervalEndsIn
          (radius * (centerRatio - 1)) (radius * (centerRatio + 1))
          (radius * (centerRatio + c)) (radius * (centerRatio + b)) =
        Skorokhod.rangeInOpenIntervalEndsIn lower upper
          endpointLower endpointUpper := by
    rw [hleft, hright, hendpointLower, hendpointUpper]
  refine ⟨amplitude, hamplitude, ?_⟩
  rw [← hparams]
  exact hlowENN.trans hmass

/-- A stable escape rate supplies one common exponential lower mass for the
finite family of open endpoint bands. The amplitude is chosen after the
stable-process estimate and before any discrete block length is selected, so
the same mass can be transferred to several asymptotically equivalent block
sequences. -/
theorem exists_stableEndpointBandReturnMassLowerBound_of_escapeRate
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {α C : ℝ}
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hEscape : HasStableProcessEscapeRate α μ P C)
    {Ω : Type*} [MeasurableSpace Ω]
    {X : ℝ≥0 → Ω → ℝ} {Q : Measure Ω} [IsProbabilityMeasure Q]
    (hX : IsStableLevyProcess α μ X Q)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    {lower upper epsilon delta : ℝ}
    (hlower : lower + 4 * epsilon < 0)
    (hupper : 0 < upper - 4 * epsilon)
    (hepsilon : 0 < epsilon) (hdelta : 0 < delta)
    (hbands : ∀ i ∈ Finset.Icc (-3 : ℤ) 3,
      lower + 4 * epsilon < (((i : ℝ) - 1) * epsilon) ∧
        ((i : ℝ) + 1) * epsilon < upper - 4 * epsilon) :
    ∃ amplitude : ℝ, 0 < amplitude ∧
      ∀ i ∈ Finset.Icc (-3 : ℤ) 3,
        ENNReal.ofReal (Real.exp
          ((C / (((upper - lower - 8 * epsilon) / 2) ^ α) - delta) *
            amplitude ^ α)) <
          P.map (Skorokhod.scalePath amplitude)
            (Skorokhod.rangeInOpenIntervalEndsIn
              (lower + 4 * epsilon) (upper - 4 * epsilon)
              (((i : ℝ) - 1) * epsilon) (((i : ℝ) + 1) * epsilon)) := by
  let corridorLower : ℝ := lower + 4 * epsilon
  let corridorUpper : ℝ := upper - 4 * epsilon
  let radius : ℝ := (corridorUpper - corridorLower) / 2
  have hradiusEq : radius = (upper - lower - 8 * epsilon) / 2 := by
    dsimp [radius, corridorLower, corridorUpper]
    ring
  have hradius : 0 < radius := by
    dsimp [radius, corridorLower, corridorUpper]
    linarith [hlower, hupper]
  have hlower' : corridorLower < 0 := by
    simpa [corridorLower] using hlower
  have hupper' : 0 < corridorUpper := by
    simpa [corridorUpper] using hupper
  have hscaledMass := eventually_scaledStableIntervalEndpointBandsProbability_ge_exp
    (lower := corridorLower) (upper := corridorUpper) (epsilon := epsilon)
    (delta := delta / 2) hEscape hX hcdf hlower' hupper' hepsilon
    (by positivity) (by
      intro i hi
      simpa [corridorLower, corridorUpper] using hbands i hi)
  obtain ⟨amplitude₀, hmass₀⟩ := Filter.eventually_atTop.1
    (hscaledMass.and (eventually_gt_atTop (0 : ℝ)))
  let amplitude : ℝ := max amplitude₀ 1
  have hamplitude : 0 < amplitude := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hstableMass := (hmass₀ amplitude (le_max_left _ _)).1
  have hrate : C / radius ^ α < 0 :=
    div_neg_of_neg_of_pos hEscape.negative (Real.rpow_pos_of_pos hradius α)
  have hlowExponent : (C / radius ^ α - delta) * amplitude ^ α <
      (C / radius ^ α - delta / 2) * amplitude ^ α := by
    have hpower : 0 < amplitude ^ α := Real.rpow_pos_of_pos hamplitude α
    nlinarith
  have hlowENN : ENNReal.ofReal
      (Real.exp ((C / radius ^ α - delta) * amplitude ^ α)) <
      ENNReal.ofReal
        (Real.exp ((C / radius ^ α - delta / 2) * amplitude ^ α)) := by
    apply (ENNReal.ofReal_lt_ofReal_iff (Real.exp_pos _)).2
    exact Real.exp_lt_exp.mpr hlowExponent
  refine ⟨amplitude, hamplitude, ?_⟩
  intro i hi
  have hstableMassI := hstableMass i hi
  have hstableMassI' : ENNReal.ofReal
      (Real.exp ((C / radius ^ α - delta / 2) * amplitude ^ α)) <
      P.map (Skorokhod.scalePath amplitude)
        (Skorokhod.rangeInOpenIntervalEndsIn corridorLower corridorUpper
          (((i : ℝ) - 1) * epsilon) (((i : ℝ) + 1) * epsilon)) := by
    simpa [corridorLower, corridorUpper, radius] using hstableMassI
  have hrateEq : radius = (upper - lower - 8 * epsilon) / 2 := hradiusEq
  rw [← hrateEq]
  simpa [corridorLower, corridorUpper] using hlowENN.trans hstableMassI'

/-- Choose one amplitude that works both for all seven repeated-return bands
and for a finite family of arbitrary entrance/exit windows. This is the
common stable-process input needed before assigning discrete block lengths. -/
theorem exists_commonStableEndpointBandAndBridgeMassLowerBound_of_escapeRate
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {α C : ℝ}
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hEscape : HasStableProcessEscapeRate α μ P C)
    {Ω : Type*} [MeasurableSpace Ω]
    {X : ℝ≥0 → Ω → ℝ} {Q : Measure Ω} [IsProbabilityMeasure Q]
    (hX : IsStableLevyProcess α μ X Q)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    {lower upper epsilon delta : ℝ}
    (hlower : lower + 4 * epsilon < 0)
    (hupper : 0 < upper - 4 * epsilon)
    (hepsilon : 0 < epsilon) (hdelta : 0 < delta)
    (hbands : ∀ i ∈ Finset.Icc (-3 : ℤ) 3,
      lower + 4 * epsilon < (((i : ℝ) - 1) * epsilon) ∧
        ((i : ℝ) + 1) * epsilon < upper - 4 * epsilon)
    {ι : Type*} [DecidableEq ι] (indices : Finset ι)
    (endpointLower endpointUpper : ι → ℝ)
    (hwindows : ∀ i ∈ indices,
      lower + 4 * epsilon < endpointLower i ∧
        endpointLower i < endpointUpper i ∧
        endpointUpper i < upper - 4 * epsilon) :
    ∃ amplitude : ℝ, 0 < amplitude ∧
      (∀ i ∈ Finset.Icc (-3 : ℤ) 3,
        ENNReal.ofReal (Real.exp
          ((C / (((upper - lower - 8 * epsilon) / 2) ^ α) - delta) *
            amplitude ^ α)) <
          P.map (Skorokhod.scalePath amplitude)
            (Skorokhod.rangeInOpenIntervalEndsIn
              (lower + 4 * epsilon) (upper - 4 * epsilon)
              (((i : ℝ) - 1) * epsilon) (((i : ℝ) + 1) * epsilon))) ∧
      (∀ i ∈ indices,
        ENNReal.ofReal (Real.exp
          ((C / (((upper - lower - 8 * epsilon) / 2) ^ α) - delta) *
            amplitude ^ α)) <
          P.map (Skorokhod.scalePath amplitude)
            (Skorokhod.rangeInOpenIntervalEndsIn
              (lower + 4 * epsilon) (upper - 4 * epsilon)
              (endpointLower i) (endpointUpper i))) := by
  let corridorLower : ℝ := lower + 4 * epsilon
  let corridorUpper : ℝ := upper - 4 * epsilon
  let radius : ℝ := (corridorUpper - corridorLower) / 2
  have hradiusEq : radius = (upper - lower - 8 * epsilon) / 2 := by
    dsimp [radius, corridorLower, corridorUpper]
    ring
  have hradius : 0 < radius := by
    dsimp [radius, corridorLower, corridorUpper]
    linarith [hlower, hupper]
  have hleft : corridorLower < 0 := by simpa [corridorLower] using hlower
  have hright : 0 < corridorUpper := by simpa [corridorUpper] using hupper
  have hbandEventually := eventually_scaledStableIntervalEndpointBandsProbability_ge_exp
    (lower := corridorLower) (upper := corridorUpper) (epsilon := epsilon)
    (delta := delta / 2) hEscape hX hcdf hleft hright hepsilon
    (by positivity) (by
      intro i hi
      simpa [corridorLower, corridorUpper] using hbands i hi)
  have hbridgeEventually :=
    eventually_scaledStableEndpointWindowFamilyProbability_ge_exp
      hEscape hX hcdf indices endpointLower endpointUpper
      (lower := corridorLower) (upper := corridorUpper) (delta := delta / 2)
      hleft hright (by
        intro i hi
        simpa [corridorLower, corridorUpper] using hwindows i hi)
      (by positivity)
  obtain ⟨amplitude₀, hmass₀⟩ := Filter.eventually_atTop.1
    ((hbandEventually.and hbridgeEventually).and
      (eventually_gt_atTop (0 : ℝ)))
  let amplitude : ℝ := max amplitude₀ 1
  have hamplitude : 0 < amplitude := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hmass := hmass₀ amplitude (le_max_left _ _)
  have hbandMass := hmass.1.1
  have hbridgeMass := hmass.1.2
  have hpower : 0 < amplitude ^ α := Real.rpow_pos_of_pos hamplitude α
  have hlowExponent : (C / radius ^ α - delta) * amplitude ^ α <
      (C / radius ^ α - delta / 2) * amplitude ^ α := by nlinarith
  have hlowENN : ENNReal.ofReal
      (Real.exp ((C / radius ^ α - delta) * amplitude ^ α)) <
      ENNReal.ofReal
        (Real.exp ((C / radius ^ α - delta / 2) * amplitude ^ α)) := by
    apply (ENNReal.ofReal_lt_ofReal_iff (Real.exp_pos _)).2
    exact Real.exp_lt_exp.mpr hlowExponent
  have hlowENN' : ENNReal.ofReal
      (Real.exp
        ((C / (((upper - lower - 8 * epsilon) / 2) ^ α) - delta) *
          amplitude ^ α)) <
      ENNReal.ofReal
        (Real.exp ((C / radius ^ α - delta / 2) * amplitude ^ α)) := by
    rw [← hradiusEq]
    exact hlowENN
  refine ⟨amplitude, hamplitude, ?_, ?_⟩
  · intro i hi
    exact hlowENN'.trans (by simpa [corridorLower, corridorUpper, radius] using hbandMass i hi)
  · intro i hi
    exact hlowENN'.trans (by simpa [corridorLower, corridorUpper, radius] using hbridgeMass i hi)

/-- A single stable block amplitude gives discrete lower bounds for both the
seven same-core return windows and every member of a finite family of
different-core bridge windows. The returned block length is the canonical
rounded stable length at that amplitude. -/
theorem exists_eventually_commonReturnAndBridgeBlockMassLowerBound_of_stableEscapeRate
    {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {α C : ℝ} {normalization scale : ℕ → ℝ}
    (hscale : IsStableMogulskiiScale α ν normalization scale)
    (hα : 0 < α) (hα₂ : α ≤ 2)
    (hslow : Asymptotics.IsSlowlyVaryingAtTop
      (stableSlowVariation α ν))
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hEscape : HasStableProcessEscapeRate α μ P C)
    {Ω : Type*} [MeasurableSpace Ω]
    {X : ℝ≥0 → Ω → ℝ} {Q : Measure Ω} [IsProbabilityMeasure Q]
    (hX : IsStableLevyProcess α μ X Q)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization (fun _ => 0))
    (htightBase : IsTightMeasureSet
      (Set.range fun n => RandomWalk.normalizedStepPathLaw ν normalization n))
    {lower upper epsilon delta : ℝ}
    (hlower : lower + 4 * epsilon < 0)
    (hupper : 0 < upper - 4 * epsilon)
    (hepsilon : 0 < epsilon) (hdelta : 0 < delta)
    (hreturnWindows : ∀ i ∈ Finset.Icc (-3 : ℤ) 3,
      lower + 4 * epsilon < (((i : ℝ) - 1) * epsilon) ∧
        ((i : ℝ) + 1) * epsilon < upper - 4 * epsilon)
    {ι : Type*} [DecidableEq ι] (indices : Finset ι)
    (sourceCenter targetCenter : ι → ℝ)
    (hbridgeWindows : ∀ i ∈ indices,
      lower + 4 * epsilon < targetCenter i - sourceCenter i - 4 * epsilon ∧
        targetCenter i - sourceCenter i + 4 * epsilon < upper - 4 * epsilon) :
    ∃ amplitude : ℝ, 0 < amplitude ∧
      ∀ᶠ n : ℕ in atTop,
        (∀ j ∈ Finset.Icc (-3 : ℤ) 3,
          ENNReal.ofReal (Real.exp
            ((C / (((upper - lower - 8 * epsilon) / 2) ^ α) - delta) *
              amplitude ^ α)) ≤ iidSequenceLaw ν
            (endpointBandReturnBlockEvent (lower * scale n) (upper * scale n)
              (epsilon * scale n) j
              (stableBlockLength α ν (amplitude ^ α) scale n))) ∧
        (∀ i ∈ indices, ∀ j ∈ Finset.Icc (-3 : ℤ) 3,
          ENNReal.ofReal (Real.exp
            ((C / (((upper - lower - 8 * epsilon) / 2) ^ α) - delta) *
              amplitude ^ α)) ≤ iidSequenceLaw ν
            (endpointCorridorBridgeBlockEvent
              ((sourceCenter i + lower) * scale n)
              ((sourceCenter i + upper) * scale n) (epsilon * scale n)
              (sourceCenter i * scale n) (targetCenter i * scale n) j
              (stableBlockLength α ν (amplitude ^ α) scale n))) := by
  let bridgeIndices := indices.product (Finset.Icc (-3 : ℤ) 3)
  obtain ⟨amplitude, hamplitude, hreturnMass, hbridgeMass⟩ :=
    exists_commonStableEndpointBandAndBridgeMassLowerBound_of_escapeRate
      hEscape hX hcdf hlower hupper hepsilon hdelta hreturnWindows bridgeIndices
      (fun ij => targetCenter ij.1 - sourceCenter ij.1 +
        ((ij.2 : ℝ) - 1) * epsilon)
      (fun ij => targetCenter ij.1 - sourceCenter ij.1 +
        ((ij.2 : ℝ) + 1) * epsilon) (by
        intro ij hij
        rcases Finset.mem_product.mp hij with ⟨hi, hj⟩
        have hji : -3 ≤ (ij.2 : ℝ) ∧ (ij.2 : ℝ) ≤ 3 := by
          exact_mod_cast (Finset.mem_Icc.mp hj)
        have hwindowLower :
            targetCenter ij.1 - sourceCenter ij.1 - 4 * epsilon ≤
              targetCenter ij.1 - sourceCenter ij.1 +
                ((ij.2 : ℝ) - 1) * epsilon := by nlinarith [hji.1, hepsilon]
        have hwindowUpper :
            targetCenter ij.1 - sourceCenter ij.1 +
                ((ij.2 : ℝ) + 1) * epsilon ≤
              targetCenter ij.1 - sourceCenter ij.1 + 4 * epsilon := by
          nlinarith [hji.2, hepsilon]
        constructor
        · exact lt_of_lt_of_le (hbridgeWindows ij.1 hi).1 hwindowLower
        · refine ⟨?_, lt_of_le_of_lt hwindowUpper (hbridgeWindows ij.1 hi).2⟩
          nlinarith [hepsilon])
  let blockLength : ℕ → ℕ :=
    fun n => stableBlockLength α ν (amplitude ^ α) scale n
  have hscaleTop : Tendsto scale atTop atTop :=
    IsStableMogulskiiScale.scale_tendsto_atTop hscale
  have hblockTop : Tendsto blockLength atTop atTop := by
    simpa [blockLength] using tendsto_stableBlockLength_atTop_of_slowVariation
      hα hα₂ hslow (Real.rpow_pos_of_pos hamplitude α) hscaleTop
  have hblockRatio : Tendsto
      (fun n => (blockLength n : ℝ) / stableScaleTime α ν (scale n))
      atTop (nhds (amplitude ^ α)) := by
    simpa [blockLength] using
      tendsto_stableBlockLength_div_stableScaleTime_of_slowVariation
        hα hα₂ hslow (Real.rpow_pos_of_pos hamplitude α) hscaleTop
  let lowerBound : ℝ≥0∞ := ENNReal.ofReal (Real.exp
    ((C / (((upper - lower - 8 * epsilon) / 2) ^ α) - delta) * amplitude ^ α))
  have hreturnEventually :=
    eventually_endpointBandReturnBlockProbability_ge_of_stableScaleTimeRatio
      hscale hα hα₂ hslow hEscape hDOA htightBase blockLength hblockTop
      hamplitude hblockRatio hlower hupper lowerBound hreturnMass
  have hbridgeEventually : ∀ᶠ n : ℕ in atTop,
      ∀ i ∈ indices, ∀ j ∈ Finset.Icc (-3 : ℤ) 3,
        lowerBound ≤ iidSequenceLaw ν
          (endpointCorridorBridgeBlockEvent
            ((sourceCenter i + lower) * scale n)
            ((sourceCenter i + upper) * scale n) (epsilon * scale n)
            (sourceCenter i * scale n) (targetCenter i * scale n) j
            (blockLength n)) := by
    apply indices.eventually_all.2
    intro i hi
    have hfamily :=
      eventually_endpointCorridorBlockProbabilityFamily_ge_of_stableScaleTimeRatio
        hscale hα hα₂ hslow hEscape hDOA htightBase blockLength hblockTop
        hamplitude hblockRatio (Finset.Icc (-3 : ℤ) 3)
        (fun _ => lower + 4 * epsilon) (fun _ => upper - 4 * epsilon)
        (fun j => targetCenter i - sourceCenter i + ((j : ℝ) - 1) * epsilon)
        (fun j => targetCenter i - sourceCenter i + ((j : ℝ) + 1) * epsilon)
        (by intro j hj; exact hlower) (by intro j hj; exact hupper)
        lowerBound (by
          intro j hj
          exact hbridgeMass (i, j) (Finset.mem_product.mpr ⟨hi, hj⟩))
    filter_upwards [hfamily] with n hfamilyN
    intro j hj
    have hprob := hfamilyN j hj
    have hset : endpointCorridorBlockEvent
        ((lower + 4 * epsilon) * scale n)
        ((upper - 4 * epsilon) * scale n)
        ((targetCenter i - sourceCenter i + ((j : ℝ) - 1) * epsilon) * scale n)
        ((targetCenter i - sourceCenter i + ((j : ℝ) + 1) * epsilon) * scale n)
        (blockLength n) =
      endpointCorridorBridgeBlockEvent
        ((sourceCenter i + lower) * scale n)
        ((sourceCenter i + upper) * scale n) (epsilon * scale n)
        (sourceCenter i * scale n) (targetCenter i * scale n) j
        (blockLength n) := by
      rw [endpointCorridorBridgeBlockEvent_scale]
      congr 1 <;> ring
    rw [← hset]
    exact hprob
  refine ⟨amplitude, hamplitude, ?_⟩
  filter_upwards [hreturnEventually, hbridgeEventually] with n hreturnN hbridgeN
  constructor
  · simpa [lowerBound, blockLength] using hreturnN
  · simpa [lowerBound, blockLength] using hbridgeN

/-- The stable escape rate and block functional limit give a sharp lower
bound for a whole floor-rounded partition cell. The cell is split into
balanced adjacent block lengths, so the return-kernel iteration covers every
increment and has no terminal remainder. -/
theorem exists_eventually_balancedEndpointBandSurvival_ge_exp_of_stableEscapeRate
    {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {α C : ℝ} {normalization scale : ℕ → ℝ}
    (hscale : IsStableMogulskiiScale α ν normalization scale)
    (hα : 0 < α) (hα₂ : α ≤ 2)
    (hslow : Asymptotics.IsSlowlyVaryingAtTop
      (stableSlowVariation α ν))
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hEscape : HasStableProcessEscapeRate α μ P C)
    {Ω : Type*} [MeasurableSpace Ω]
    {X : ℝ≥0 → Ω → ℝ} {Q : Measure Ω} [IsProbabilityMeasure Q]
    (hX : IsStableLevyProcess α μ X Q)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization (fun _ => 0))
    (htightBase : IsTightMeasureSet
      (Set.range fun n => RandomWalk.normalizedStepPathLaw ν normalization n))
    {lower upper epsilon delta duration : ℝ}
    (hlower : lower + 4 * epsilon < 0)
    (hupper : 0 < upper - 4 * epsilon)
    (hepsilon : 0 < epsilon) (hdelta : 0 < delta)
    (hbands : ∀ i ∈ Finset.Icc (-3 : ℤ) 3,
      lower + 4 * epsilon < (((i : ℝ) - 1) * epsilon) ∧
        ((i : ℝ) + 1) * epsilon < upper - 4 * epsilon)
    (total : ℕ → ℕ) (hduration : 0 < duration)
    (htotal : Tendsto (fun n => (total n : ℝ) / (n : ℝ))
      atTop (nhds duration)) :
    ∃ amplitude : ℝ, 0 < amplitude ∧
      ∀ᶠ n : ℕ in atTop,
        ∀ x : Set.Icc (-3 * (epsilon * scale n)) (3 * (epsilon * scale n)),
          ENNReal.ofReal (Real.exp
            ((C / (((upper - lower - 8 * epsilon) / 2) ^ α) - delta) *
              amplitude ^ α)) ^
                Asymptotics.balancedBlockCount (total n)
                  (stableBlockLength α ν (amplitude ^ α) scale n)
            ≤ iidSequenceLaw ν
              {increment | StaysIn
                (Set.Icc (lower * scale n) (upper * scale n))
                (total n) (x : ℝ) increment} := by
  obtain ⟨amplitude, hamplitude, hmass⟩ :=
    exists_stableEndpointBandReturnMassLowerBound_of_escapeRate
      hEscape hX hcdf hlower hupper hepsilon hdelta hbands
  let reference : ℕ → ℕ := fun n => stableBlockLength α ν (amplitude ^ α) scale n
  let shortBlock : ℕ → ℕ := fun n =>
    Asymptotics.balancedBlockShortLength (total n) (reference n)
  let longBlock : ℕ → ℕ := fun n => shortBlock n + 1
  have hdata := balancedStableCellBlock_asymptotics hscale hα hα₂ hslow
    total hduration hamplitude htotal
  rcases hdata with ⟨hcount, hshortTop, hlongTop, hshortRatio, hlongRatio⟩
  have hshortProbability :=
    eventually_endpointBandReturnBlockProbability_ge_of_stableScaleTimeRatio
      hscale hα hα₂ hslow hEscape hDOA htightBase shortBlock hshortTop
      hamplitude hshortRatio hlower hupper
      (ENNReal.ofReal (Real.exp
        ((C / (((upper - lower - 8 * epsilon) / 2) ^ α) - delta) * amplitude ^ α)))
      (by
        intro i hi
        exact hmass i hi)
  have hlongProbability :=
    eventually_endpointBandReturnBlockProbability_ge_of_stableScaleTimeRatio
      hscale hα hα₂ hslow hEscape hDOA htightBase longBlock hlongTop
      hamplitude hlongRatio hlower hupper
      (ENNReal.ofReal (Real.exp
        ((C / (((upper - lower - 8 * epsilon) / 2) ^ α) - delta) * amplitude ^ α)))
      (by
        intro i hi
        exact hmass i hi)
  have hscalePos : ∀ᶠ n : ℕ in atTop, 0 < scale n :=
    IsStableMogulskiiScale.eventually_scale_pos hscale
  have hcountPos : ∀ᶠ n : ℕ in atTop,
      0 < Asymptotics.balancedBlockCount (total n) (reference n) := by
    filter_upwards [hcount.eventually (eventually_gt_atTop (0 : ℝ))] with n hn
    exact_mod_cast hn
  refine ⟨amplitude, hamplitude, ?_⟩
  filter_upwards [hshortProbability, hlongProbability, hscalePos, hcountPos]
    with n hshortN hlongN hscaleN hcountN
  intro x
  have hcell :=
    ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.iidSequenceLaw_staysIn_ge_pow_of_balancedEndpointBandBlocks
      ν (mul_pos hepsilon hscaleN) (total n) (reference n) hcountN
      (ENNReal.ofReal (Real.exp
        ((C / (((upper - lower - 8 * epsilon) / 2) ^ α) - delta) * amplitude ^ α)))
      (by
        intro i hi
        simpa [shortBlock, reference] using hshortN i hi)
      (by
        intro i hi
        simpa [longBlock, shortBlock, reference] using hlongN i hi)
  simpa [Asymptotics.balancedBlockCount, reference] using hcell x

/-- For any fixed shifted corridor and a finite family of endpoint bands
strictly inside it, stable escape rates and the variable-block functional
limit give the sharp exponential lower bound for every one-block endpoint
event. The block amplitude is chosen large enough once and then kept fixed
while the walk horizon tends to infinity. -/
theorem exists_eventually_endpointBandReturnBlockProbability_ge_exp_of_stableEscapeRate
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
    {lower upper epsilon delta : ℝ}
    (hlower : lower + 4 * epsilon < 0)
    (hupper : 0 < upper - 4 * epsilon)
    (hepsilon : 0 < epsilon) (hdelta : 0 < delta)
    (hbands : ∀ i ∈ Finset.Icc (-3 : ℤ) 3,
      lower + 4 * epsilon < (((i : ℝ) - 1) * epsilon) ∧
        ((i : ℝ) + 1) * epsilon < upper - 4 * epsilon) :
    ∃ amplitude : ℝ, 0 < amplitude ∧
      ∀ᶠ n : ℕ in atTop,
        ∀ i ∈ Finset.Icc (-3 : ℤ) 3,
          ENNReal.ofReal (Real.exp
            ((C / (((upper - lower - 8 * epsilon) / 2) ^ α) - delta) *
              amplitude ^ α)) ≤
            iidSequenceLaw ν
              (endpointBandReturnBlockEvent (lower * scale n) (upper * scale n)
                (epsilon * scale n) i
                (stableBlockLength α ν (amplitude ^ α) scale n)) := by
  let corridorLower : ℝ := lower + 4 * epsilon
  let corridorUpper : ℝ := upper - 4 * epsilon
  let radius : ℝ := (corridorUpper - corridorLower) / 2
  have hradiusEq : radius = (upper - lower - 8 * epsilon) / 2 := by
    dsimp [radius, corridorLower, corridorUpper]
    ring
  have hradius : 0 < radius := by
    dsimp [radius, corridorLower, corridorUpper]
    linarith [hlower, hupper]
  obtain ⟨amplitude, hamplitude, hstableMass⟩ :=
    exists_stableEndpointBandReturnMassLowerBound_of_escapeRate
      hEscape hX hcdf hlower hupper hepsilon hdelta hbands
  have hbelow : ∀ i ∈ Finset.Icc (-3 : ℤ) 3,
      ENNReal.ofReal (Real.exp
        ((C / radius ^ α - delta) * amplitude ^ α)) <
        P.map (Skorokhod.scalePath amplitude)
          (Skorokhod.rangeInOpenIntervalEndsIn corridorLower corridorUpper
            (((i : ℝ) - 1) * epsilon) (((i : ℝ) + 1) * epsilon)) := by
    intro i hi
    simpa [corridorLower, corridorUpper, radius, hradiusEq] using hstableMass i hi
  let blockLength : ℕ → ℕ := fun n =>
    stableBlockLength α ν (amplitude ^ α) scale n
  have hscaleTop : Tendsto scale atTop atTop :=
    IsStableMogulskiiScale.scale_tendsto_atTop hscale
  have hblockTop : Tendsto blockLength atTop atTop := by
    simpa [blockLength] using tendsto_stableBlockLength_atTop_of_slowVariation
      hα hα₂ hslow (Real.rpow_pos_of_pos hamplitude α) hscaleTop
  have hblockPos : ∀ᶠ n : ℕ in atTop, 0 < blockLength n :=
    hblockTop.eventually (eventually_gt_atTop 0)
  have hscalePos : ∀ᶠ n : ℕ in atTop, 0 < scale n :=
    IsStableMogulskiiScale.eventually_scale_pos hscale
  have hnormBlockPos : ∀ᶠ n : ℕ in atTop,
      0 < normalization (blockLength n) :=
    (hscale.stableNorming.2.1.comp hblockTop).eventually
      (eventually_gt_atTop 0)
  have hblockEq : blockLength = Asymptotics.floorBlockLength
      (fun n => amplitude ^ α * stableScaleTime α ν (scale n)) := by
    funext n
    change ⌊stableBlockArgument α ν (amplitude ^ α) scale n⌋₊ =
      ⌊amplitude ^ α * stableScaleTime α ν (scale n)⌋₊
    rw [stableBlockArgument_eq_constant_mul_stableScaleTime]
  have hnormRatioBase := hscale.stableNorming.tendsto_floorBlock_normalization_div_scale
    hα hα₂ hslow hscaleTop (Real.rpow_pos_of_pos hamplitude α)
  have hnormRatio : Tendsto
      (fun n => normalization (blockLength n) / scale n)
      atTop (𝓝 amplitude) := by
    have hbase : Tendsto
        (fun n => normalization (blockLength n) / scale n)
        atTop (𝓝 ((amplitude ^ α) ^ (1 / α))) := by
      apply hnormRatioBase.congr'
      filter_upwards [] with n
      simp [blockLength, hblockEq]
    have hroot : (amplitude ^ α) ^ (1 / α) = amplitude := by
      rw [← Real.rpow_mul (le_of_lt hamplitude) α (1 / α)]
      have hmul : α * (1 / α) = 1 := by field_simp [ne_of_gt hα]
      rw [hmul, Real.rpow_one]
    convert hbase using 1
    exact congrArg nhds hroot.symm
  have hlimit :=
    RandomWalk.FunctionalLimit.Stable.tendstoInDistribution_normalizedStepBlockPathLaw_of_baseTightness
      hDOA hEscape.isStableClockProcessLaw htightBase hblockTop
      hscalePos hnormBlockPos hnormRatio
  have hscaleMapMeas : Measurable (Skorokhod.scalePath amplitude) :=
    (Skorokhod.continuous_scalePath.comp
      (continuous_const.prodMk continuous_id)).measurable
  have hlimit' := hlimit.congr_limit (μ'' := P)
    (Z' := Skorokhod.scalePath amplitude) hscaleMapMeas.aemeasurable (by simp)
  have hdiscrete :=
    eventually_endpointBandReturnBlockProbability_ge_of_stablePathLimit
      ν scale blockLength (Z := Skorokhod.scalePath amplitude) hlimit'
      hscalePos hblockPos hlower hupper
      (ENNReal.ofReal (Real.exp ((C / radius ^ α - delta) * amplitude ^ α))) hbelow
  refine ⟨amplitude, hamplitude, ?_⟩
  filter_upwards [hdiscrete] with n hdiscreteN
  simpa [blockLength, hradiusEq] using hdiscreteN

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

end
