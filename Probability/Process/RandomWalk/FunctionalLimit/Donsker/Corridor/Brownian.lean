/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Topology.UnitInterval
public import Probability.Process.RandomWalk.FunctionalLimit.Donsker.Skorokhod
public import Probability.Process.RandomWalk.FunctionalLimit.NormalizedStep

/-!
# Brownian corridor bounds for Donsker limits

This file instantiates the abstract Skorokhod corridor consequences with the
verified Donsker theorem.  The result is a direct interface from centered
unit-variance increments to Brownian open and closed corridor probabilities.
-/

open Filter MeasureTheory ProbabilityTheory

@[expose] public section

namespace ProbabilityTheory.RandomWalk


/-- Brownian open-corridor mass bounds the `liminf` of strict tubes for every
centered unit-variance increment law. -/
theorem brownian_skorokhodCorridor_le_liminf_strictTube
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (hnu : IsCenteredUnitSecondMoment nu)
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {B : NNReal → Omega → ℝ}
    (hB : IsPreBrownianReal B P)
    (hcontinuous : ∀ omega, Continuous (B · omega))
    (hmeasurable : ∀ t, Measurable (B t))
    {a : ℝ} (ha : 0 < a) (haOne : a < 1) :
    P.map (Skorokhod.ofContinuousMap ∘
        continuousunitIntervalPath B hcontinuous)
        (Skorokhod.rangeInOpenInterval (-a) (1 - a)) ≤
      atTop.liminf (fun n : ℕ =>
        iidSequenceLaw nu
          {increment | InOpenHorizontalTube a (Real.sqrt n) n increment}) := by
  apply measure_skorokhodCorridor_le_liminf_strictTube_of_functionalLimit
    P nu (fun n => Real.sqrt n)
    (limit := Skorokhod.ofContinuousMap ∘
      continuousunitIntervalPath B hcontinuous)
    (ha := ha) (haOne := haOne)
  · filter_upwards [eventually_gt_atTop 0] with n hn
    exact Real.sqrt_pos.2 (by exact_mod_cast hn)
  · exact tendstoInDistribution_normalizedStepCadlagPath_brownian
      nu hnu.1 hnu.2 hB hcontinuous hmeasurable

/-- Brownian mass in a centered open corridor of arbitrary positive width
bounds the `liminf` of the matching centered strict random-walk tubes. -/
theorem brownian_centeredSkorokhodCorridor_le_liminf_strictTube
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (hnu : IsCenteredUnitSecondMoment nu)
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {B : NNReal → Omega → ℝ}
    (hB : IsPreBrownianReal B P)
    (hcontinuous : ∀ omega, Continuous (B · omega))
    (hmeasurable : ∀ t, Measurable (B t))
    {width : ℝ} (hwidth : 0 < width) :
    P.map (Skorokhod.ofContinuousMap ∘
        continuousunitIntervalPath B hcontinuous)
        (Skorokhod.rangeInOpenInterval (-(width / 2)) (width / 2)) ≤
      atTop.liminf (fun n : ℕ =>
        iidSequenceLaw nu
          {increment | InOpenHorizontalTube (1 / 2)
            (width * Real.sqrt n) n increment}) := by
  apply measure_centeredSkorokhodCorridor_le_liminf_strictTube_of_functionalLimit
    P nu (fun n => Real.sqrt n)
    (limit := Skorokhod.ofContinuousMap ∘
      continuousunitIntervalPath B hcontinuous)
    (width := width)
  · filter_upwards [eventually_gt_atTop 0] with n hn
    exact Real.sqrt_pos.2 (by exact_mod_cast hn)
  · exact tendstoInDistribution_normalizedStepCadlagPath_brownian
      nu hnu.1 hnu.2 hB hcontinuous hmeasurable
  · exact hwidth

/-- The `limsup` of weak tubes for every centered unit-variance increment law
is bounded by the corresponding Brownian closed-corridor mass. -/
theorem limsup_weakTube_le_brownian_skorokhodCorridor
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (hnu : IsCenteredUnitSecondMoment nu)
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {B : NNReal → Omega → ℝ}
    (hB : IsPreBrownianReal B P)
    (hcontinuous : ∀ omega, Continuous (B · omega))
    (hmeasurable : ∀ t, Measurable (B t))
    {a : ℝ} (ha : 0 ≤ a) (haOne : a ≤ 1) :
    atTop.limsup (fun n : ℕ =>
        iidSequenceLaw nu
          {increment | InHorizontalTube a (Real.sqrt n) n increment}) ≤
      P.map (Skorokhod.ofContinuousMap ∘
        continuousunitIntervalPath B hcontinuous)
        (Skorokhod.rangeInClosedInterval (-a) (1 - a)) := by
  apply limsup_weakTube_le_measure_skorokhodCorridor_of_functionalLimit
    P nu (fun n => Real.sqrt n)
    (limit := Skorokhod.ofContinuousMap ∘
      continuousunitIntervalPath B hcontinuous)
    (ha := ha) (haOne := haOne)
  · filter_upwards [eventually_gt_atTop 0] with n hn
    exact Real.sqrt_pos.2 (by exact_mod_cast hn)
  · exact tendstoInDistribution_normalizedStepCadlagPath_brownian
      nu hnu.1 hnu.2 hB hcontinuous hmeasurable

end ProbabilityTheory.RandomWalk
