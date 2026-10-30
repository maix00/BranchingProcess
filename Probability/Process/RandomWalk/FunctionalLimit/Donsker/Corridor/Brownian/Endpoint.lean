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
public import Probability.Process.RandomWalk.Path.Corridor.Horizontal.Core
public import Probability.Process.RandomWalk.FunctionalLimit.NormalizedStep.Endpoint

/-!
# Brownian corridor bounds with an endpoint constraint

This file specializes the endpoint-constrained Portmanteau bound to the
verified Donsker theorem for centered unit-variance increments.

## Public declarations

- `ProbabilityTheory.RandomWalk.brownian_centeredSkorokhodCorridorEndsIn_le_liminf_strictTubeEndsIn`:
  for centered unit-variance increments and $w>0$, Brownian path-law mass of
  $\{f:|f(t)|<w/2\ (0\le t\le1),\ f(1)\in(a,b)\}$ is at most
  $\liminf_n\mathbb P(|S_j|<w\sqrt n/2\ (1\le j\le n),\
  S_n/\sqrt n\in(a,b))$.
- `ProbabilityTheory.RandomWalk.limsup_centeredWeakTube_le_brownian_closedCorridor`:
  for centered unit-variance increments and $w\ge0$, the limsup probability
  of the weak centered tube is at most Brownian path-law mass of
  $\{f:|f(t)|\le w/2\ (0\le t\le1)\}$.

These are Portmanteau consequences of
`RandomWalk.tendstoInDistribution_normalizedStepCadlagPath_brownian`, the
Skorokhod-space form of Donsker's Theorem 4.20 in I. Karatzas and S. E. Shreve,
*Brownian Motion and Stochastic Calculus*, 2nd ed., Graduate Texts in
Mathematics 113, Springer (1991), DOI 10.1007/978-1-4612-0949-2.
-/

open Filter MeasureTheory ProbabilityTheory

@[expose] public section

namespace ProbabilityTheory.RandomWalk


/-- Brownian mass in a centered open corridor ending in an open interval
bounds the matching finite random-walk events from below in the limit. -/
theorem brownian_centeredSkorokhodCorridorEndsIn_le_liminf_strictTubeEndsIn
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : IsCenteredUnitSecondMoment ν)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : NNReal → Ω → ℝ}
    (hB : IsBrownianReal B P)
    {width endpointLower endpointUpper : ℝ} (hwidth : 0 < width) :
    P.map (Skorokhod.ofContinuousMap ∘
        continuousunitIntervalPath
          (hB.toIsPreBrownianReal.continuousModification)
          (hB.toIsPreBrownianReal.continuous_continuousModification))
        (Skorokhod.rangeInOpenIntervalEndsIn
          (-(width / 2)) (width / 2) endpointLower endpointUpper) ≤
      atTop.liminf (fun n : ℕ =>
        iidSequenceLaw ν {increment |
          InOpenHorizontalTube (1 / 2) (width * Real.sqrt n) n increment ∧
            AdditivePath.displacement n increment / Real.sqrt n ∈
              Set.Ioo endpointLower endpointUpper}) := by
  let Bc := hB.toIsPreBrownianReal.continuousModification
  have hBc := hB.toIsPreBrownianReal.isBrownianReal_continuousModification
  have hBccontinuous : ∀ ω, Continuous (Bc · ω) :=
    hB.toIsPreBrownianReal.continuous_continuousModification
  have hBcmeasurable : ∀ t, Measurable (Bc t) :=
    hB.toIsPreBrownianReal.measurable_continuousModification
  apply measure_centeredSkorokhodCorridorEndsIn_le_liminf_strictTubeEndsIn_of_functionalLimit
    P ν (fun n => Real.sqrt n)
    (limit := Skorokhod.ofContinuousMap ∘
      continuousunitIntervalPath Bc hBccontinuous)
    (width := width)
  · filter_upwards [eventually_gt_atTop 0] with n hn
    exact Real.sqrt_pos.2 (by exact_mod_cast hn)
  · exact tendstoInDistribution_normalizedStepCadlagPath_brownian
      ν hν.1 hν.2 hBc.toIsPreBrownianReal hBccontinuous hBcmeasurable
  · exact hwidth

/-- The weak centered tube has a closed-corridor `limsup` bound for every
nonnegative width.  The terminal constraint required by the càdlàg
Portmanteau theorem is already part of every nonempty horizontal tube. -/
theorem limsup_centeredWeakTube_le_brownian_closedCorridor
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : IsCenteredUnitSecondMoment ν)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : NNReal → Ω → ℝ}
    (hB : IsBrownianReal B P)
    {width : ℝ} (hwidth : 0 ≤ width) :
    atTop.limsup (fun n : ℕ =>
      horizontalTubeProbability (iidSequenceLaw ν)
        (1 / 2) (width * Real.sqrt n) n) ≤
      P.map (Skorokhod.ofContinuousMap ∘
        continuousunitIntervalPath
          (hB.toIsPreBrownianReal.continuousModification)
          (hB.toIsPreBrownianReal.continuous_continuousModification))
        (Skorokhod.rangeInClosedInterval (-(width / 2)) (width / 2)) := by
  let Bc := hB.toIsPreBrownianReal.continuousModification
  have hBc := hB.toIsPreBrownianReal.isBrownianReal_continuousModification
  have hBccontinuous : ∀ ω, Continuous (Bc · ω) :=
    hB.toIsPreBrownianReal.continuous_continuousModification
  have hBcmeasurable : ∀ t, Measurable (Bc t) :=
    hB.toIsPreBrownianReal.measurable_continuousModification
  let limit := Skorokhod.ofContinuousMap ∘
    continuousunitIntervalPath Bc hBccontinuous
  let tube : ℕ → ENNReal := fun n => horizontalTubeProbability
    (iidSequenceLaw ν) (1 / 2) (width * Real.sqrt n) n
  let tubeEnds : ℕ → ENNReal := fun n => iidSequenceLaw ν
    {increment | InHorizontalTube (1 / 2) (width * Real.sqrt n) n increment ∧
      AdditivePath.displacement n increment / Real.sqrt n ∈
        Set.Icc (-(width / 2)) (width / 2)}
  have hlimit : TendstoInDistribution
      (fun n => normalizedStepCadlagPathIcc (fun n => Real.sqrt n) n)
      atTop limit (fun _ => iidSequenceLaw ν) P :=
    tendstoInDistribution_normalizedStepCadlagPath_brownian
      ν hν.1 hν.2 hBc.toIsPreBrownianReal hBccontinuous hBcmeasurable
  have hport := limsup_weakTubeEndsIn_le_measure_centeredSkorokhodCorridorEndsIn_of_functionalLimit
    P ν (fun n => Real.sqrt n)
    (by
      filter_upwards [eventually_gt_atTop 0] with n hn
      exact Real.sqrt_pos.2 (by exact_mod_cast hn))
    limit hlimit (width := width)
      (endpointLower := -(width / 2)) (endpointUpper := width / 2) hwidth
  have hendset : Skorokhod.rangeInClosedIntervalEndsIn
      (-(width / 2)) (width / 2) (-(width / 2)) (width / 2) =
      Skorokhod.rangeInClosedInterval (-(width / 2)) (width / 2) := by
    ext path
    constructor
    · rintro ⟨hpath, _⟩
      exact hpath
    · intro hpath
      exact ⟨hpath, hpath ⊤⟩
  rw [hendset] at hport
  have htubeEndsBound : Filter.IsBoundedUnder (· ≤ ·) atTop tubeEnds := by
    apply Filter.isBoundedUnder_of_eventually_le (a := 1)
    exact Eventually.of_forall fun n => by
      calc
        tubeEnds n ≤ iidSequenceLaw ν Set.univ := by
          apply measure_mono
          exact Set.subset_univ _
        _ = 1 := measure_univ
  have hterminal : ∀ᶠ n in atTop, tube n ≤ tubeEnds n := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    unfold tube tubeEnds horizontalTubeProbability
    apply measure_mono
    intro increment hincrement
    refine ⟨hincrement, ?_⟩
    have hend := InHorizontalTube.mem_endpoint hincrement hn
    have hsqrt : 0 < Real.sqrt (n : ℝ) :=
      Real.sqrt_pos.2 (by exact_mod_cast hn)
    constructor
    · apply (le_div_iff₀ hsqrt).2
      have h := hend.1
      change -(1 / 2 : ℝ) * (width * Real.sqrt n) ≤
        AdditivePath.displacement n increment at h
      nlinarith
    · apply (div_le_iff₀ hsqrt).2
      have h := hend.2
      change AdditivePath.displacement n increment ≤
        (1 - (1 / 2 : ℝ)) * (width * Real.sqrt n) at h
      nlinarith
  have hlimsup := Filter.limsup_le_limsup hterminal
    (Filter.isCoboundedUnder_le_of_le atTop (fun _ => bot_le))
    htubeEndsBound
  exact (hlimsup.trans hport)

end ProbabilityTheory.RandomWalk
