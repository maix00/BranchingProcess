/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Topology.UnitInterval
public import Probability.BranchingRandomWalk.Walk.FunctionalLimit.Donsker.Corridor.Brownian.Endpoint
public import Probability.BranchingRandomWalk.Walk.SmallDeviation.Mogulskii.Spectral.Diffusive.Brownian

/-!
# Diffusive corridor estimates with a terminal interval

The principal Brownian corridor constant remains a lower bound after adding
an open terminal interval that contains the closed unit corridor.  Donsker's
theorem then transfers this estimate to centered unit-variance random walks.
-/

open Filter MeasureTheory ProbabilityTheory

@[expose] public section

namespace ProbabilityTheory.RandomWalk.Mogulskii

open Combinatorics.Branching.Walk

/-- The sharp closed-unit-corridor lower bound also applies to every wider
open corridor whose terminal interval contains the closed unit interval. -/
theorem ofReal_exp_neg_pi_sq_div_two_le_brownian_openCorridorEndsIn
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : NNReal → Ω → ℝ}
    (hB : IsPreBrownianReal B P)
    (hcontinuous : ∀ ω, Continuous (B · ω))
    (hmeasurable : ∀ t, Measurable (B t))
    {width endpointLower endpointUpper : ℝ}
    (hwidth : 1 < width)
    (hendpointLower : endpointLower < -(1 / 2 : ℝ))
    (hendpointUpper : (1 / 2 : ℝ) < endpointUpper) :
    ENNReal.ofReal (Real.exp (-(Real.pi ^ 2) / 2)) ≤
      P.map (Skorokhod.ofContinuousMap ∘
        continuousunitIntervalPath B hcontinuous)
        (Skorokhod.rangeInOpenIntervalEndsIn
          (-(width / 2)) (width / 2) endpointLower endpointUpper) := by
  refine (ofReal_exp_neg_pi_sq_div_two_le_brownian_closedCorridor
    hB hcontinuous hmeasurable).trans (measure_mono ?_)
  intro path hpath
  rw [Skorokhod.mem_rangeInOpenIntervalEndsIn_iff]
  constructor
  · refine ⟨(width - 1) / 2, by linarith, fun t => ?_⟩
    have ht := hpath t
    constructor <;> linarith
  · have ht := hpath (⊤ : unitInterval)
    exact ⟨lt_of_lt_of_le hendpointLower ht.1,
      lt_of_le_of_lt ht.2 hendpointUpper⟩

/-- For centered unit-variance increments, the principal Brownian constant
bounds from below the limiting probability of a wider strict diffusive tube
whose normalized endpoint returns to an open interval containing the closed
unit interval. -/
theorem ofReal_exp_neg_pi_sq_div_two_le_liminf_centeredStrictTubeEndsIn
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : IsCenteredUnitSecondMoment ν)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : NNReal → Ω → ℝ}
    (hB : IsPreBrownianReal B P)
    (hcontinuous : ∀ ω, Continuous (B · ω))
    (hmeasurable : ∀ t, Measurable (B t))
    {width endpointLower endpointUpper : ℝ}
    (hwidth : 1 < width)
    (hendpointLower : endpointLower < -(1 / 2 : ℝ))
    (hendpointUpper : (1 / 2 : ℝ) < endpointUpper) :
    ENNReal.ofReal (Real.exp (-(Real.pi ^ 2) / 2)) ≤
      atTop.liminf (fun n : ℕ =>
        independentIncrementLaw ν {increment |
          InOpenHorizontalTube (1 / 2) (width * Real.sqrt n) n increment ∧
            partialSum n increment / Real.sqrt n ∈
              Set.Ioo endpointLower endpointUpper}) := by
  exact (ofReal_exp_neg_pi_sq_div_two_le_brownian_openCorridorEndsIn
    hB hcontinuous hmeasurable hwidth hendpointLower hendpointUpper).trans
      (RandomWalk.brownian_centeredSkorokhodCorridorEndsIn_le_liminf_strictTubeEndsIn
        ν hν hB hcontinuous hmeasurable (by linarith))

end ProbabilityTheory.RandomWalk.Mogulskii
