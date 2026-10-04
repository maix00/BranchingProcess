/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Topology.UnitInterval
public import Probability.Process.RandomWalk.Path.Skorokhod.Corridor.Endpoint
public import Probability.ConvergenceInDistribution.Portmanteau
public import Probability.Process.Path.Skorokhod.Corridor

/-!
# Normalized-step limits with an endpoint constraint

Portmanteau transfers open or closed path corridors together with matching
terminal intervals to the corresponding finite random-walk events.  The
path-space Portmanteau input is supplied by the process layer; this file only
identifies the normalized-step laws with horizontal-tube events.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

@[expose] public section

namespace ProbabilityTheory.RandomWalk

open Combinatorics.Branching.Walk

/-- A càdlàg functional limit theorem gives the `liminf` bound for a centered
strict tube whose normalized endpoint lies in a prescribed open interval. -/
theorem measure_centeredSkorokhodCorridorEndsIn_le_liminf_strictTubeEndsIn_of_functionalLimit
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (scale : ℕ → ℝ) (hscale : ∀ᶠ n in atTop, 0 < scale n)
    (limit : Ω → CadlagPath unitInterval ℝ)
    (hlimit : TendstoInDistribution
      (fun n => normalizedStepCadlagPathIcc scale n)
      atTop limit (fun _ => independentIncrementLaw ν) P)
    {width endpointLower endpointUpper : ℝ} (hwidth : 0 < width) :
    P.map limit
        (Skorokhod.rangeInOpenIntervalEndsIn
          (-(width / 2)) (width / 2) endpointLower endpointUpper) ≤
      atTop.liminf (fun n : ℕ =>
        independentIncrementLaw ν {increment |
          InOpenHorizontalTube (1 / 2) (width * scale n) n increment ∧
            partialSum n increment / scale n ∈
              Set.Ioo endpointLower endpointUpper}) := by
  have hevent := hlimit.measure_skorokhodCorridorEndsIn_le_liminf
    (-(width / 2)) (width / 2) endpointLower endpointUpper
  refine hevent.trans_eq ?_
  apply liminf_congr
  filter_upwards [eventually_gt_atTop 0, hscale] with n hn hscalePos
  change normalizedStepPathLaw ν scale n
      (Skorokhod.rangeInOpenIntervalEndsIn
        (-(width / 2)) (width / 2) endpointLower endpointUpper) = _
  exact normalizedStepPathLaw_apply_centeredOpenIntervalEndsIn
    ν scale hn hscalePos hwidth

/-- A càdlàg functional limit theorem bounds centered weak tubes with a closed
endpoint constraint from above by the corresponding limit event. -/
theorem limsup_weakTubeEndsIn_le_measure_centeredSkorokhodCorridorEndsIn_of_functionalLimit
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (scale : ℕ → ℝ) (hscale : ∀ᶠ n in atTop, 0 < scale n)
    (limit : Ω → CadlagPath unitInterval ℝ)
    (hlimit : TendstoInDistribution
      (fun n => normalizedStepCadlagPathIcc scale n)
      atTop limit (fun _ => independentIncrementLaw ν) P)
    {width endpointLower endpointUpper : ℝ} (hwidth : 0 ≤ width) :
    atTop.limsup (fun n : ℕ =>
      independentIncrementLaw ν {increment |
        InHorizontalTube (1 / 2) (width * scale n) n increment ∧
          partialSum n increment / scale n ∈
            Set.Icc endpointLower endpointUpper}) ≤
      P.map limit
        (Skorokhod.rangeInClosedIntervalEndsIn
          (-(width / 2)) (width / 2) endpointLower endpointUpper) := by
  have hevent := hlimit.limsup_measure_skorokhodCorridorEndsIn_le
    (-(width / 2)) (width / 2) endpointLower endpointUpper
  refine Eq.trans_le ?_ hevent
  apply limsup_congr
  filter_upwards [eventually_gt_atTop 0, hscale] with n hn hscalePos
  change independentIncrementLaw ν {increment |
      InHorizontalTube (1 / 2) (width * scale n) n increment ∧
        partialSum n increment / scale n ∈
          Set.Icc endpointLower endpointUpper} =
    normalizedStepPathLaw ν scale n
      (Skorokhod.rangeInClosedIntervalEndsIn
        (-(width / 2)) (width / 2) endpointLower endpointUpper)
  symm
  exact normalizedStepPathLaw_apply_centeredClosedIntervalEndsIn
    ν scale hn hscalePos hwidth

end ProbabilityTheory.RandomWalk
