/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Distributions.Stable.Attraction.Norming.Inverse
public import Probability.Distributions.Stable.Attraction.NormingRatios.Tauberian
public import Probability.Process.RandomWalk.FunctionalLimit.Stable.PathLimit.Block
public import Probability.Process.RandomWalk.FunctionalLimit.Stable.Tightness
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.EndpointBandTransfer

/-! # Stable-domain input for the discrete endpoint-return bound

This adapter connects a zero-centered stable domain-of-attraction limit and
its tightness input to the open endpoint-return estimate. It fixes the block
parameter to one, so the rounded block length is `⌊κν (aₙ)⌋₊` and its stable
spatial normalization is asymptotic to `aₙ`. The endpoint corridor masses are
then obtained from the stable-process entrance estimate; they are not extra
hypotheses on the random walk.
-/

open Filter MeasureTheory ProbabilityTheory
open ProbabilityTheory.RandomWalk.FunctionalLimit.Stable
open scoped ENNReal NNReal Topology

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

/-- The stable-process entrance estimate and a zero-centered stable FCLT
imply the discrete horizontal-tube lower bound at block length
`⌊κν (scale n)⌋₊`. The FCLT is supplied by the already proved finite-grid and
J₁-tightness interface. No endpoint-boundary nullity is needed: the transfer
uses open corridor events and the open-set Portmanteau inequality. -/
theorem eventually_horizontalTubeProbability_ge_pow_of_stableDomain
    {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {α : ℝ} {normalization scale : ℕ → ℝ} {horizon : ℕ → ℕ}
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    {Ω : Type*} [MeasurableSpace Ω]
    {X : ℝ≥0 → Ω → ℝ} {Q : Measure Ω} [IsProbabilityMeasure Q]
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization (fun _ => 0))
    (hP : IsStableClockProcessLaw α μ unitIntervalClock P)
    (hX : IsStableLevyProcess α μ X Q)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    (htight : IsTightMeasureSet (Set.range
      (fun n => RandomWalk.normalizedStepPathLaw ν normalization n)))
    (hnorm : IsStableNorming α ν normalization)
    (hα : 0 < α) (hα₂ : α < 2)
    (hscale : Tendsto scale atTop atTop) :
    ∃ radius : ℝ, ∃ lowerBound : ℝ≥0∞,
      0 < radius ∧ radius < 1 / 2 ∧ 0 < lowerBound ∧
      ∀ᶠ n in atTop,
        lowerBound ^ (horizon n /
            (stableBlockLength α ν 1 scale n) + 1) ≤
          horizontalTubeProbability (iidSequenceLaw ν) (1 / 2)
            (2 * (radius + 4 * (radius / 16)) * scale n)
            (horizon n) := by
  have hstrict := hP.strictlyStable
  have hstable : IsAlphaStable α μ := hstrict.isAlphaStable
  have hαle : α ≤ 2 := hstrict.2.1
  have hslow : Asymptotics.IsSlowlyVaryingAtTop
      (stableSlowVariation α ν) :=
    hDOA.isSlowlyVarying_stableSlowVariation hstable hα hα₂
  let blockLength : ℕ → ℕ := fun n => stableBlockLength α ν 1 scale n
  have hblockEq : blockLength = Asymptotics.floorBlockLength
      (fun n => (1 : ℝ) * stableScaleTime α ν (scale n)) := by
    funext n
    simp [blockLength, stableBlockLength, stableBlockArgument,
      stableScaleTime, Asymptotics.floorBlockLength]
  have hκtop := stableScaleTime_tendsto_atTop_of_stableSlowVariation
    hα hαle hslow
  have hκscale : Tendsto
      (fun n => stableScaleTime α ν (scale n)) atTop atTop := by
    exact hκtop.comp hscale
  have hargumentTop : Tendsto
      (fun n => (1 : ℝ) * stableScaleTime α ν (scale n)) atTop atTop := by
    exact hκscale.const_mul_atTop (by norm_num : (0 : ℝ) < 1)
  have hblockTop : Tendsto blockLength atTop atTop := by
    rw [hblockEq]
    exact Asymptotics.tendsto_floorBlockLength_atTop hargumentTop
  have hblockPos : ∀ᶠ n in atTop, 0 < blockLength n :=
    hblockTop.eventually (eventually_gt_atTop 0)
  have hscalePos : ∀ᶠ n in atTop, 0 < scale n :=
    hscale.eventually (eventually_gt_atTop 0)
  have hnormAtBlock : ∀ᶠ n in atTop,
      0 < normalization (blockLength n) :=
    (hnorm.2.1.comp hblockTop).eventually (eventually_gt_atTop 0)
  have hratio : Tendsto
      (fun n => normalization (blockLength n) / scale n)
      atTop (nhds 1) := by
    have hratio' := hnorm.tendsto_floorBlock_normalization_div_scale
      hα hαle hslow hscale (by norm_num : (0 : ℝ) < 1)
    simpa [blockLength, stableBlockLength, stableBlockArgument,
      stableScaleTime, Asymptotics.floorBlockLength] using hratio'
  have hblockLimit :=
    FunctionalLimit.Stable.tendstoInDistribution_normalizedStepBlockPathLaw_of_baseTightness
      hDOA hP htight hblockTop hscalePos hnormAtBlock hratio
  have hscaleOne : Skorokhod.scalePath 1 = id := by
    funext f
    ext t
    simp [Skorokhod.scalePath_apply]
  have hmap : P.map (Skorokhod.scalePath 1) = P := by
    rw [hscaleOne]
    simp
  have htargetLaw : (P.map (Skorokhod.scalePath 1)).map id = P.map id := by
    rw [hmap]
  have hblockLimitP := hblockLimit.congr_limit aemeasurable_id htargetLaw
  have hPid : IsStableClockProcessLaw α μ unitIntervalClock (P.map id) := by
    simpa using hP
  exact eventually_horizontalTubeProbability_ge_pow_of_stablePathLawLimit
    ν scale blockLength horizon (Z := id) hPid hX hcdf
    hblockLimitP hscalePos hblockPos


/-- Source regime `0 < α < 1`: domain-of-attraction tail estimates and stable
norming provide the J₁ tightness input, so the stable-domain return lower
bound needs no separately supplied tightness proof. -/
theorem eventually_horizontalTubeProbability_ge_pow_of_index_lt_one
    {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {α : ℝ} {normalization scale : ℕ → ℝ} {horizon : ℕ → ℕ}
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    {Ω : Type*} [MeasurableSpace Ω]
    {X : ℝ≥0 → Ω → ℝ} {Q : Measure Ω} [IsProbabilityMeasure Q]
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization (fun _ => 0))
    (hP : IsStableClockProcessLaw α μ unitIntervalClock P)
    (hX : IsStableLevyProcess α μ X Q)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    (hnorm : IsStableNorming α ν normalization)
    (hα : 0 < α) (hαone : α < 1) (hα₂ : α < 2)
    (hscale : Tendsto scale atTop atTop) :
    ∃ radius : ℝ, ∃ lowerBound : ℝ≥0∞,
      0 < radius ∧ radius < 1 / 2 ∧ 0 < lowerBound ∧
      ∀ᶠ n in atTop,
        lowerBound ^ (horizon n /
            (stableBlockLength α ν 1 scale n) + 1) ≤
          horizontalTubeProbability (iidSequenceLaw ν) (1 / 2)
            (2 * (radius + 4 * (radius / 16)) * scale n)
            (horizon n) := by
  have htail := hDOA.isRegularlyVarying_twoSidedTail
    hP.strictlyStable.isAlphaStable hα hα₂
  have htight := isTightMeasureSet_range_normalizedStepPathLaw_of_index_lt_one
      hnorm hα hαone htail
  exact eventually_horizontalTubeProbability_ge_pow_of_stableDomain
    hDOA hP hX hcdf htight hnorm hα hα₂ hscale

/-- Source regime `α = 1`: the sine-centering hypothesis gives J₁ tightness,
and the stable-domain return lower bound follows with the same open-event
endpoint transfer. -/
theorem eventually_horizontalTubeProbability_ge_pow_of_index_one
    {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {normalization scale : ℕ → ℝ} {horizon : ℕ → ℕ}
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    {Ω : Type*} [MeasurableSpace Ω]
    {X : ℝ≥0 → Ω → ℝ} {Q : Measure Ω} [IsProbabilityMeasure Q]
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization (fun _ => 0))
    (hP : IsStableClockProcessLaw 1 μ unitIntervalClock P)
    (hX : IsStableLevyProcess 1 μ X Q)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    (hnorm : IsStableNorming 1 ν normalization)
    (hcenter : IsMogulskiiIndexOneCentered ν normalization)
    (hscale : Tendsto scale atTop atTop) :
    ∃ radius : ℝ, ∃ lowerBound : ℝ≥0∞,
      0 < radius ∧ radius < 1 / 2 ∧ 0 < lowerBound ∧
      ∀ᶠ n in atTop,
        lowerBound ^ (horizon n /
            (stableBlockLength 1 ν 1 scale n) + 1) ≤
          horizontalTubeProbability (iidSequenceLaw ν) (1 / 2)
            (2 * (radius + 4 * (radius / 16)) * scale n)
            (horizon n) := by
  have htail := hDOA.isRegularlyVarying_twoSidedTail
    hP.strictlyStable.isAlphaStable (by norm_num) (by norm_num)
  have htight := isTightMeasureSet_range_normalizedStepPathLaw_of_index_one
      hnorm htail hcenter
  exact eventually_horizontalTubeProbability_ge_pow_of_stableDomain
    hDOA hP hX hcdf htight hnorm (by norm_num) (by norm_num) hscale

/-- Source regime `1 < α < 2`: centered integrable increments give J₁
tightness, which closes the path-law input to the endpoint-return lower
bound. -/
theorem eventually_horizontalTubeProbability_ge_pow_of_index_gt_one
    {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {α : ℝ} {normalization scale : ℕ → ℝ} {horizon : ℕ → ℕ}
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    {Ω : Type*} [MeasurableSpace Ω]
    {X : ℝ≥0 → Ω → ℝ} {Q : Measure Ω} [IsProbabilityMeasure Q]
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization (fun _ => 0))
    (hP : IsStableClockProcessLaw α μ unitIntervalClock P)
    (hX : IsStableLevyProcess α μ X Q)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    (hnorm : IsStableNorming α ν normalization)
    (hα : 0 < α) (hαone : 1 < α) (hα₂ : α < 2)
    (hint : Integrable (fun x : ℝ => x) ν)
    (hmean : (∫ x : ℝ, x ∂ν) = 0)
    (hscale : Tendsto scale atTop atTop) :
    ∃ radius : ℝ, ∃ lowerBound : ℝ≥0∞,
      0 < radius ∧ radius < 1 / 2 ∧ 0 < lowerBound ∧
      ∀ᶠ n in atTop,
        lowerBound ^ (horizon n /
            (stableBlockLength α ν 1 scale n) + 1) ≤
          horizontalTubeProbability (iidSequenceLaw ν) (1 / 2)
            (2 * (radius + 4 * (radius / 16)) * scale n)
            (horizon n) := by
  have htail := hDOA.isRegularlyVarying_twoSidedTail
    hP.strictlyStable.isAlphaStable hα hα₂
  have htight := isTightMeasureSet_range_normalizedStepPathLaw_of_index_gt_one
      hnorm hα hαone hα₂ htail hint hmean
  exact eventually_horizontalTubeProbability_ge_pow_of_stableDomain
    hDOA hP hX hcdf htight hnorm hα hα₂ hscale

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

end
