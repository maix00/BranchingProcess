/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Topology.UnitInterval
public import Probability.BranchingRandomWalk.Walk.Path.Corridor.Interpolation
public import Probability.Process.Path.Corridor

/-!
# Continuous-path corridor adapters

These statements identify the open and closed corridor events of the
polygonal normalized walk with horizontal-tube events.  They are part of the
finite-variance functional-limit interface and do not depend on Mogulskii's
small-deviation proof.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

@[expose] public section

namespace ProbabilityTheory.RandomWalk

open Combinatorics.Branching.Walk

theorem measure_openCorridor_le_liminf_strictTube_of_functionalLimit
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (limit : Omega → C(unitInterval, ℝ))
    (hlimit : TendstoInDistribution
      (fun n => normalizedLinearContinuousPathIcc (fun n => Real.sqrt n) n)
      atTop limit (fun _ => independentIncrementLaw nu) P)
    {a : ℝ} (ha : 0 < a) (haOne : a < 1) :
    P.map limit (ContinuousMap.rangeInOpenInterval (-a) (1 - a)) ≤
      atTop.liminf (fun n : ℕ =>
        independentIncrementLaw nu
          {increment |
            InOpenHorizontalTube a (Real.sqrt n) n increment}) := by
  have hcorridor := hlimit.measure_horizontalCorridor_le_liminf
    (show -a < 1 - a by linarith)
  refine hcorridor.trans_eq ?_
  apply liminf_congr
  filter_upwards [eventually_gt_atTop 0] with n hn
  change normalizedLinearPathLaw nu (fun n => Real.sqrt n) n
      (ContinuousMap.rangeInOpenInterval (-a) (1 - a)) = _
  exact normalizedLinearPathLaw_apply_rangeInOpenInterval
    nu (fun n => Real.sqrt n) hn
      (Real.sqrt_pos.2 (by exact_mod_cast hn)) ha haOne

/-- A functional limit theorem bounds the `limsup` of weak discrete tube
probabilities by the limiting process's closed-corridor probability. -/
theorem limsup_weakTube_le_measure_closedCorridor_of_functionalLimit
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (limit : Omega → C(unitInterval, ℝ))
    (hlimit : TendstoInDistribution
      (fun n => normalizedLinearContinuousPathIcc (fun n => Real.sqrt n) n)
      atTop limit (fun _ => independentIncrementLaw nu) P)
    {a : ℝ} (ha : 0 ≤ a) (haOne : a ≤ 1) :
    atTop.limsup (fun n : ℕ =>
        independentIncrementLaw nu
          {increment | InHorizontalTube a (Real.sqrt n) n increment}) ≤
      P.map limit (ContinuousMap.rangeInClosedInterval (-a) (1 - a)) := by
  have hcorridor := hlimit.limsup_measure_horizontalCorridor_le (-a) (1 - a)
  refine Eq.trans_le ?_ hcorridor
  apply limsup_congr
  filter_upwards [eventually_gt_atTop 0] with n hn
  change independentIncrementLaw nu
      {increment | InHorizontalTube a (Real.sqrt n) n increment} =
    normalizedLinearPathLaw nu (fun n => Real.sqrt n) n
      (ContinuousMap.rangeInClosedInterval (-a) (1 - a))
  symm
  exact normalizedLinearPathLaw_apply_rangeInClosedInterval
    nu (fun n => Real.sqrt n) hn
      (Real.sqrt_pos.2 (by exact_mod_cast hn)) ha haOne

end ProbabilityTheory.RandomWalk
