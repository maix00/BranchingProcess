/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Topology.UnitInterval
public import Mathlib.Probability.BrownianMotion.Basic
public import Probability.Distributions.Moments.Real
public import Probability.Process.Brownian.PathLaw.ContinuousModification
public import Probability.Process.Brownian.Construction.PreBrownianModification
public import Probability.Process.RandomWalk.FunctionalLimit.Donsker.Path.Skorokhod
public import Probability.Process.RandomWalk.FunctionalLimit.NormalizedStep.Basic

/-!
# Brownian corridor bounds for Donsker limits

This file instantiates the abstract Skorokhod corridor consequences with the
verified Donsker theorem.  The result is a direct interface from centered
unit-variance increments to Brownian open and closed corridor probabilities.

## Public declarations

- `ProbabilityTheory.RandomWalk.brownian_skorokhodCorridor_le_liminf_strictTube`:
  for centered unit-variance increments and $0<a<1$, Brownian path-law mass
  of $\{f:-a<f(t)<1-a\ (0\le t\le1)\}$ is at most
  $\liminf_n\mathbb P(-a\sqrt n<S_j<(1-a)\sqrt n\ (1\le j\le n)$.
- `ProbabilityTheory.RandomWalk.brownian_centeredSkorokhodCorridor_le_liminf_strictTube`:
  for each $w>0$, Brownian path-law mass of
  $\{f:|f(t)|<w/2\ (0\le t\le1)\}$ is at most the liminf of the matching
  strict-tube probabilities at width $w\sqrt n$.
- `ProbabilityTheory.RandomWalk.limsup_weakTube_le_brownian_skorokhodCorridor`:
  for $0\le a\le1$, the limsup probability of the weak tube is at most
  Brownian path-law mass of $\{f:-a\le f(t)\le1-a\ (0\le t\le1)\}$.

These are Portmanteau consequences of
`RandomWalk.tendstoInDistribution_normalizedStepCadlagPath_brownian`, the
Skorokhod-space form of Donsker's Theorem 4.20 in I. Karatzas and S. E. Shreve,
*Brownian Motion and Stochastic Calculus*, 2nd ed., Graduate Texts in
Mathematics 113, Springer (1991), DOI 10.1007/978-1-4612-0949-2.
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
    (hB : IsBrownianReal B P)
    {a : ℝ} (ha : 0 < a) (haOne : a < 1) :
    P.map (Skorokhod.ofContinuousMap ∘
        continuousunitIntervalPath
          (hB.toIsPreBrownianReal.continuousModification)
          (hB.toIsPreBrownianReal.continuous_continuousModification))
        (Skorokhod.rangeInOpenInterval (-a) (1 - a)) ≤
      atTop.liminf (fun n : ℕ =>
        iidSequenceLaw nu
          {increment | InOpenHorizontalTube a (Real.sqrt n) n increment}) := by
  let Bc := hB.toIsPreBrownianReal.continuousModification
  have hBc := hB.toIsPreBrownianReal.isBrownianReal_continuousModification
  have hBccontinuous : ∀ ω, Continuous (Bc · ω) :=
    hB.toIsPreBrownianReal.continuous_continuousModification
  have hBcmeasurable : ∀ t, Measurable (Bc t) :=
    hB.toIsPreBrownianReal.measurable_continuousModification
  apply measure_skorokhodCorridor_le_liminf_strictTube_of_functionalLimit
    P nu (fun n => Real.sqrt n)
    (limit := Skorokhod.ofContinuousMap ∘
      continuousunitIntervalPath Bc hBccontinuous)
    (ha := ha) (haOne := haOne)
  · filter_upwards [eventually_gt_atTop 0] with n hn
    exact Real.sqrt_pos.2 (by exact_mod_cast hn)
  · exact tendstoInDistribution_normalizedStepCadlagPath_brownian
      nu hnu.1 hnu.2 hBc.toIsPreBrownianReal hBccontinuous hBcmeasurable

/-- Brownian mass in a centered open corridor of arbitrary positive width
bounds the `liminf` of the matching centered strict random-walk tubes. -/
theorem brownian_centeredSkorokhodCorridor_le_liminf_strictTube
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (hnu : IsCenteredUnitSecondMoment nu)
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {B : NNReal → Omega → ℝ}
    (hB : IsBrownianReal B P)
    {width : ℝ} (hwidth : 0 < width) :
    P.map (Skorokhod.ofContinuousMap ∘
        continuousunitIntervalPath
          (hB.toIsPreBrownianReal.continuousModification)
          (hB.toIsPreBrownianReal.continuous_continuousModification))
        (Skorokhod.rangeInOpenInterval (-(width / 2)) (width / 2)) ≤
      atTop.liminf (fun n : ℕ =>
        iidSequenceLaw nu
          {increment | InOpenHorizontalTube (1 / 2)
            (width * Real.sqrt n) n increment}) := by
  let Bc := hB.toIsPreBrownianReal.continuousModification
  have hBc := hB.toIsPreBrownianReal.isBrownianReal_continuousModification
  have hBccontinuous : ∀ ω, Continuous (Bc · ω) :=
    hB.toIsPreBrownianReal.continuous_continuousModification
  have hBcmeasurable : ∀ t, Measurable (Bc t) :=
    hB.toIsPreBrownianReal.measurable_continuousModification
  apply measure_centeredSkorokhodCorridor_le_liminf_strictTube_of_functionalLimit
    P nu (fun n => Real.sqrt n)
    (limit := Skorokhod.ofContinuousMap ∘
      continuousunitIntervalPath Bc hBccontinuous)
    (width := width)
  · filter_upwards [eventually_gt_atTop 0] with n hn
    exact Real.sqrt_pos.2 (by exact_mod_cast hn)
  · exact tendstoInDistribution_normalizedStepCadlagPath_brownian
      nu hnu.1 hnu.2 hBc.toIsPreBrownianReal hBccontinuous hBcmeasurable
  · exact hwidth

/-- The `limsup` of weak tubes for every centered unit-variance increment law
is bounded by the corresponding Brownian closed-corridor mass. -/
theorem limsup_weakTube_le_brownian_skorokhodCorridor
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (hnu : IsCenteredUnitSecondMoment nu)
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {B : NNReal → Omega → ℝ}
    (hB : IsBrownianReal B P)
    {a : ℝ} (ha : 0 ≤ a) (haOne : a ≤ 1) :
    atTop.limsup (fun n : ℕ =>
        iidSequenceLaw nu
          {increment | InHorizontalTube a (Real.sqrt n) n increment}) ≤
      P.map (Skorokhod.ofContinuousMap ∘
        continuousunitIntervalPath
          (hB.toIsPreBrownianReal.continuousModification)
          (hB.toIsPreBrownianReal.continuous_continuousModification))
        (Skorokhod.rangeInClosedInterval (-a) (1 - a)) := by
  let Bc := hB.toIsPreBrownianReal.continuousModification
  have hBc := hB.toIsPreBrownianReal.isBrownianReal_continuousModification
  have hBccontinuous : ∀ ω, Continuous (Bc · ω) :=
    hB.toIsPreBrownianReal.continuous_continuousModification
  have hBcmeasurable : ∀ t, Measurable (Bc t) :=
    hB.toIsPreBrownianReal.measurable_continuousModification
  apply limsup_weakTube_le_measure_skorokhodCorridor_of_functionalLimit
    P nu (fun n => Real.sqrt n)
    (limit := Skorokhod.ofContinuousMap ∘
      continuousunitIntervalPath Bc hBccontinuous)
    (ha := ha) (haOne := haOne)
  · filter_upwards [eventually_gt_atTop 0] with n hn
    exact Real.sqrt_pos.2 (by exact_mod_cast hn)
  · exact tendstoInDistribution_normalizedStepCadlagPath_brownian
      nu hnu.1 hnu.2 hBc.toIsPreBrownianReal hBccontinuous hBcmeasurable

end ProbabilityTheory.RandomWalk
