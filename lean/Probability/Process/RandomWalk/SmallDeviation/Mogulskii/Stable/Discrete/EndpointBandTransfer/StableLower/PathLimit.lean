/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.FunctionalLimit.Stable.PathLimit.Block
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.EndpointBandTransfer.StableRate
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Scale
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Scale.Rate
public import Probability.Process.Stable.SmallDeviation.EscapeRate.PathLaw.Transfer

/-!
# Stable lower bounds for shifted endpoint-return blocks

This combines the stable escape rate, the variable-block path limit, and
open-set Portmanteau for an arbitrary shifted interval. It supplies the
finite endpoint-band probabilities needed by the discrete return kernel.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

@[expose] public section

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

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

end

end
