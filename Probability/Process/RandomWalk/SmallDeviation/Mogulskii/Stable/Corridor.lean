/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Scale
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.BlockScale
public import Probability.Process.RandomWalk.Path.Corridor.Horizontal
public import Probability.Process.RandomWalk.FunctionalLimit.NormalizedStep.Block
public import Probability.Process.RandomWalk.FunctionalLimit.Stable.PathLimit.Block
public import Probability.Distributions.Stable.Attraction.Norming.Inverse
public import Probability.Sequence.IID

/-!
# One-block corridors for the stable Mogulskii route

The one-block step of Mogulskii's stable proof estimates the probability that the increment path stays in a
corridor of normalized width `w` over a block of `stableBlockLength α ν constant a n` steps, which is
`a n ^ α / L* (a n)` steps up to the constant factor `constant`. The small-deviation scale
`n * L* (a n) / a n ^ α` is what turns a per-block constant into the corridor rate of the theorem.

For `α < 2` the limit process has jumps, so the estimate has to go through the stable Lévy process and the
Skorokhod `J₁` topology; the killed-interval spectral expansion used for the Gaussian case is not available
here and is not used. At `α = 2` the slowly varying factor is the truncated second moment, and the block
length reduces to the diffusive block length with the constant rescaled by that moment, which is the link
by which the Gaussian specialization reuses the diffusive estimates.

The one-block estimate is conditional on the block path-law limit: the last
theorem transfers an explicit `J₁` limit to the corridor probability when the
limiting path law gives zero mass to the corridor boundary.
-/

@[expose] public section

open Filter MeasureTheory Set

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii



/-! ## The block length at `α = 2` -/

/-- At `α = 2` the slowly varying factor of (3) is the truncated second moment, so the stable block length
is the floor of `constant * scale n ^ 2` divided by that moment. -/
@[simp] theorem stableBlockLength_two (ν : Measure ℝ) (constant : ℝ) (scale : ℕ → ℝ) (n : ℕ) :
    stableBlockLength 2 ν constant scale n =
      ⌊constant * scale n ^ 2 / truncatedSecondMoment ν (scale n)⌋₊ := by
  simp [stableBlockLength, stableBlockArgument, stableSlowVariation_two]

/-- At `α = 2`, if the truncated second moment at the scale is the constant `c`, the stable block length is
the diffusive block length with the constant rescaled by `c`. This is the link by which the Gaussian
specialization reuses the diffusive estimates. -/
theorem stableBlockLength_two_of_truncatedSecondMoment_eq (ν : Measure ℝ) {constant c : ℝ}
    {scale : ℕ → ℝ} {n : ℕ} (hc : truncatedSecondMoment ν (scale n) = c) :
    stableBlockLength 2 ν constant scale n = diffusiveBlockLength (constant / c) scale n := by
  rw [stableBlockLength_two, hc, diffusiveBlockLength, div_mul_eq_mul_div]

/-! ## The block corridor events -/

/-- The stable block corridor: after spatial normalization by `scale n`, the
increment path stays in the open corridor of normalized width `width` with
lower offset `a`, over a block of `stableBlockLength α ν constant scale n`
steps fixed by the increment law `ν`. -/
def stableBlockTube (ν : Measure ℝ) (α constant a width : ℝ) (scale : ℕ → ℝ) (n : ℕ) :
    Set (ℕ → ℝ) :=
  {increment |
    InOpenHorizontalTube a (width * scale n)
      (stableBlockLength α ν constant scale n) increment}

/-- The closed variant of `stableBlockTube`, used by the upper bounds. -/
def stableClosedBlockTube (ν : Measure ℝ) (α constant a width : ℝ) (scale : ℕ → ℝ)
    (n : ℕ) : Set (ℕ → ℝ) :=
  {increment |
    InHorizontalTube a (width * scale n)
      (stableBlockLength α ν constant scale n) increment}

/-- The probability of the stable block corridor under the i.i.d. increment law. -/
noncomputable def stableBlockCorridorProbability (ν : Measure ℝ)
    (α constant a width : ℝ) (scale : ℕ → ℝ) (n : ℕ) : ENNReal :=
  iidSequenceLaw ν (stableBlockTube ν α constant a width scale n)

/-- The closed block corridor is a measurable event. -/
theorem measurableSet_stableClosedBlockTube (ν : Measure ℝ) (α constant a width : ℝ)
    (scale : ℕ → ℝ) (n : ℕ) :
    MeasurableSet (stableClosedBlockTube ν α constant a width scale n) :=
  measurableSet_inHorizontalTube a (width * scale n) _

/-- The narrower open corridor is contained in the wider one with the same offset. This is the
monotonicity the two-sided bound of the theorem uses when comparing `f + ε`, `g - ε` with `f`, `g`. -/
theorem stableBlockTube_mono_width (ν : Measure ℝ) {α constant a w w' : ℝ}
    {scale : ℕ → ℝ} {n : ℕ} (ha0 : 0 < a) (ha1 : a < 1) (hww : w' < w)
    (hscale : 0 < scale n) :
    stableBlockTube ν α constant a w' scale n ⊆
      stableBlockTube ν α constant a w scale n := by
  have hscaled : w' * scale n < w * scale n :=
    mul_lt_mul_of_pos_right hww hscale
  have hlower : -a * (w * scale n) < -a * (w' * scale n) :=
    mul_lt_mul_of_neg_left hscaled (by linarith)
  have hupper : (1 - a) * (w' * scale n) < (1 - a) * (w * scale n) :=
    mul_lt_mul_of_pos_left hscaled (by linarith)
  intro increment h k
  have hk := h k
  exact ⟨hlower.trans hk.1, hk.2.trans hupper⟩

/-- Monotonicity of the block corridor probability in the corridor width. -/
theorem stableBlockCorridorProbability_mono_width (ν : Measure ℝ)
    {α constant a w w' : ℝ} {scale : ℕ → ℝ} {n : ℕ}
    (ha0 : 0 < a) (ha1 : a < 1) (hww : w' < w) (hscale : 0 < scale n) :
    stableBlockCorridorProbability ν α constant a w' scale n ≤
      stableBlockCorridorProbability ν α constant a w scale n :=
  measure_mono (stableBlockTube_mono_width ν ha0 ha1 hww hscale)

/-- Under an explicit Skorokhod `J₁` path-law limit for the normalized
stable-length blocks, the one-block corridor probability converges whenever
the limiting stable path gives zero mass to the corridor boundary.

The path-law hypothesis records the precise normalization used here:
`stableBlockLength α ν constant scale n` steps, each normalized by `scale n`.
It is the functional-limit input still missing from the stable random-walk
route; this theorem converts that input to the exact finite block event.
-/
theorem stableBlockCorridorProbability_tendsto_of_pathLawLimit
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {α constant a width : ℝ} {scale : ℕ → ℝ}
    (P : Measure (CadlagPath unitInterval ℝ)) [IsProbabilityMeasure P]
    (hscale : ∀ᶠ n in atTop, 0 < scale n)
    (hblock : ∀ᶠ n in atTop,
      0 < stableBlockLength α ν constant scale n)
    (hlimit : TendstoInDistribution
      (RandomWalk.normalizedStepBlockCadlagPathIcc scale
        (fun n => stableBlockLength α ν constant scale n))
      atTop (id : CadlagPath unitInterval ℝ → CadlagPath unitInterval ℝ)
      (fun _ => iidSequenceLaw ν) P)
    (ha : 0 < a) (haOne : a < 1) (hwidth : 0 < width)
    (hboundary : P
      (frontier (Skorokhod.rangeInOpenInterval
        (-(a * width)) ((1 - a) * width))) = 0) :
    Tendsto (fun n => stableBlockCorridorProbability ν α constant a width scale n)
      atTop (nhds (P (Skorokhod.rangeInOpenInterval
        (-(a * width)) ((1 - a) * width)))) := by
  let blockLength : ℕ → ℕ := fun n =>
    stableBlockLength α ν constant scale n
  let corridor : Set (CadlagPath unitInterval ℝ) :=
    Skorokhod.rangeInOpenInterval (-(a * width)) ((1 - a) * width)
  have hboundaryMap : P.map id (frontier corridor) = 0 := by
    simpa [corridor] using hboundary
  have hpathLaw := RandomWalk.tendsto_measure_normalizedStepBlockPathLaw_of_null_frontier
    (ν := ν) (spatialScale := scale) (blockLength := blockLength)
    P id hlimit hboundaryMap
  have heq : (fun n =>
      stableBlockCorridorProbability ν α constant a width scale n) =ᶠ[atTop]
      (fun n => RandomWalk.normalizedStepBlockPathLaw ν scale blockLength n corridor) := by
    filter_upwards [hblock, hscale] with n hblockn hscalen
    rw [stableBlockCorridorProbability, stableBlockTube]
    symm
    exact RandomWalk.normalizedStepBlockPathLaw_apply_horizontalOpenCorridor
      ν scale blockLength n hblockn hscalen ha haOne hwidth
  have hpathLaw' : Tendsto
      (fun n => RandomWalk.normalizedStepBlockPathLaw ν scale blockLength n corridor)
      atTop (nhds (P corridor)) := by
    simpa [corridor] using hpathLaw
  exact hpathLaw'.congr' heq.symm

/-- The stable one-block corridor limit follows from the fixed-horizon
stable-domain input, path tightness, and slow variation of the norming factor.
The inverse-norming theorem identifies the limiting spatial scale as
`constant ^ (1 / α)` without requiring the slowly varying factor to converge. -/
theorem stableBlockCorridorProbability_tendsto_of_stableDomain
    {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {α constant a width : ℝ} {normalization scale : ℕ → ℝ}
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization (fun _ => 0))
    (hP : IsStableClockProcessLaw α μ unitIntervalClock P)
    (htightBase : IsTightMeasureSet
      (Set.range fun n => RandomWalk.normalizedStepPathLaw ν normalization n))
    (hnorm : IsStableNorming α ν normalization)
    (hα : 0 < α) (hα_le_two : α ≤ 2) (hconstant : 0 < constant)
    (hscale : Tendsto scale atTop atTop)
    (hslow : Asymptotics.IsSlowlyVaryingAtTop (stableSlowVariation α ν))
    (ha : 0 < a) (haOne : a < 1) (hwidth : 0 < width)
    (hboundary : (P.map (Skorokhod.scalePath (constant ^ (1 / α))))
      (frontier (Skorokhod.rangeInOpenInterval
        (-(a * width)) ((1 - a) * width))) = 0) :
    Tendsto (fun n => stableBlockCorridorProbability ν α constant a width scale n)
      atTop (nhds ((P.map (Skorokhod.scalePath (constant ^ (1 / α))))
        (Skorokhod.rangeInOpenInterval (-(a * width)) ((1 - a) * width)))) := by
  let block : ℕ → ℕ := fun n => stableBlockLength α ν constant scale n
  have hargumentEq (n : ℕ) : stableBlockArgument α ν constant scale n =
      constant * stableScaleTime α ν (scale n) := by
    rw [stableBlockArgument, stableScaleTime]
    ring
  have hblockEq : block = Asymptotics.floorBlockLength
      (fun n => constant * stableScaleTime α ν (scale n)) := by
    funext n
    simp [block, stableBlockLength, Asymptotics.floorBlockLength, hargumentEq n]
  have hscaleTimeTop : Tendsto (stableScaleTime α ν) atTop atTop :=
    stableScaleTime_tendsto_atTop_of_stableSlowVariation hα hα_le_two hslow
  have hargumentTop : Tendsto
      (fun n => constant * stableScaleTime α ν (scale n)) atTop atTop :=
    (hscaleTimeTop.comp hscale).const_mul_atTop hconstant
  have hblockTop : Tendsto block atTop atTop := by
    rw [hblockEq]
    exact Asymptotics.tendsto_floorBlockLength_atTop hargumentTop
  have hblockPos : ∀ᶠ n in atTop, 0 < block n := by
    simpa [block] using hblockTop.eventually (eventually_gt_atTop 0)
  have hscalePos : ∀ᶠ n in atTop, 0 < scale n :=
    hscale.eventually (eventually_gt_atTop 0)
  have hnormPos : ∀ᶠ m in atTop, 0 < normalization m := by
    filter_upwards [eventually_gt_atTop 0] with m hm
    exact hnorm.1 m hm
  have hnormBlock : ∀ᶠ n in atTop, 0 < normalization (block n) :=
    hblockTop.eventually hnormPos
  have hratio : Tendsto (fun n => normalization (block n) / scale n)
      atTop (nhds (constant ^ (1 / α))) := by
    rw [hblockEq]
    exact hnorm.tendsto_floorBlock_normalization_div_scale
      hα hα_le_two hslow hscale hconstant
  have hlimit :=
    ProbabilityTheory.RandomWalk.FunctionalLimit.Stable.tendstoInDistribution_normalizedStepBlockPathLaw_of_baseTightness
      hDOA hP htightBase hblockTop hscalePos hnormBlock hratio
  exact stableBlockCorridorProbability_tendsto_of_pathLawLimit
    (P := P.map (Skorokhod.scalePath (constant ^ (1 / α))))
    hscalePos hblockPos hlimit ha haOne hwidth hboundary

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii
