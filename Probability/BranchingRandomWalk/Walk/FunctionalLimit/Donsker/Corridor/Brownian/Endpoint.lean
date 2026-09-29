import Mathlib.Topology.UnitInterval
import Probability.BranchingRandomWalk.Walk.FunctionalLimit.Donsker.Skorokhod
import Probability.BranchingRandomWalk.Walk.SmallDeviation.Horizontal
import Probability.BranchingRandomWalk.Walk.FunctionalLimit.NormalizedStep.Endpoint

/-!
# Brownian corridor bounds with an endpoint constraint

This file specializes the endpoint-constrained Portmanteau bound to the
verified Donsker theorem for centered unit-variance increments.
-/

open Filter MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.RandomWalk

open Combinatorics.Branching.Walk

/-- Brownian mass in a centered open corridor ending in an open interval
bounds the matching finite random-walk events from below in the limit. -/
theorem brownian_centeredSkorokhodCorridorEndsIn_le_liminf_strictTubeEndsIn
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : IsCenteredUnitSecondMoment ν)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : NNReal → Ω → ℝ}
    (hB : IsPreBrownianReal B P)
    (hcontinuous : ∀ ω, Continuous (B · ω))
    (hmeasurable : ∀ t, Measurable (B t))
    {width endpointLower endpointUpper : ℝ} (hwidth : 0 < width) :
    P.map (Skorokhod.ofContinuousMap ∘
        continuousunitIntervalPath B hcontinuous)
        (Skorokhod.rangeInOpenIntervalEndsIn
          (-(width / 2)) (width / 2) endpointLower endpointUpper) ≤
      atTop.liminf (fun n : ℕ =>
        independentIncrementLaw ν {increment |
          InOpenHorizontalTube (1 / 2) (width * Real.sqrt n) n increment ∧
            partialSum n increment / Real.sqrt n ∈
              Set.Ioo endpointLower endpointUpper}) := by
  apply measure_centeredSkorokhodCorridorEndsIn_le_liminf_strictTubeEndsIn_of_functionalLimit
    P ν (fun n => Real.sqrt n)
    (limit := Skorokhod.ofContinuousMap ∘
      continuousunitIntervalPath B hcontinuous)
    (width := width)
  · filter_upwards [eventually_gt_atTop 0] with n hn
    exact Real.sqrt_pos.2 (by exact_mod_cast hn)
  · exact tendstoInDistribution_normalizedStepCadlagPath_brownian
      ν hν.1 hν.2 hB hcontinuous hmeasurable
  · exact hwidth

/-- The weak centered tube has a closed-corridor `limsup` bound for every
nonnegative width.  The terminal constraint required by the càdlàg
Portmanteau theorem is already part of every nonempty horizontal tube. -/
theorem limsup_centeredWeakTube_le_brownian_closedCorridor
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : IsCenteredUnitSecondMoment ν)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : NNReal → Ω → ℝ}
    (hB : IsPreBrownianReal B P)
    (hcontinuous : ∀ ω, Continuous (B · ω))
    (hmeasurable : ∀ t, Measurable (B t))
    {width : ℝ} (hwidth : 0 ≤ width) :
    atTop.limsup (fun n : ℕ =>
      horizontalTubeProbability (independentIncrementLaw ν)
        (1 / 2) (width * Real.sqrt n) n) ≤
      P.map (Skorokhod.ofContinuousMap ∘
        continuousunitIntervalPath B hcontinuous)
        (Skorokhod.rangeInClosedInterval (-(width / 2)) (width / 2)) := by
  let limit := Skorokhod.ofContinuousMap ∘
    continuousunitIntervalPath B hcontinuous
  let tube : ℕ → ENNReal := fun n => horizontalTubeProbability
    (independentIncrementLaw ν) (1 / 2) (width * Real.sqrt n) n
  let tubeEnds : ℕ → ENNReal := fun n => independentIncrementLaw ν
    {increment | InHorizontalTube (1 / 2) (width * Real.sqrt n) n increment ∧
      partialSum n increment / Real.sqrt n ∈
        Set.Icc (-(width / 2)) (width / 2)}
  have hlimit : TendstoInDistribution
      (fun n => normalizedStepCadlagPathIcc (fun n => Real.sqrt n) n)
      atTop limit (fun _ => independentIncrementLaw ν) P :=
    tendstoInDistribution_normalizedStepCadlagPath_brownian
      ν hν.1 hν.2 hB hcontinuous hmeasurable
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
        tubeEnds n ≤ independentIncrementLaw ν Set.univ := by
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
        partialSum n increment at h
      nlinarith
    · apply (div_le_iff₀ hsqrt).2
      have h := hend.2
      change partialSum n increment ≤
        (1 - (1 / 2 : ℝ)) * (width * Real.sqrt n) at h
      nlinarith
  have hlimsup := Filter.limsup_le_limsup hterminal
    (Filter.isCoboundedUnder_le_of_le atTop (fun _ => bot_le))
    htubeEndsBound
  exact (hlimsup.trans hport)

end ProbabilityTheory.RandomWalk
