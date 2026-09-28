import Probability.BranchingRandomWalk.Walk.Path.Interpolation.Corridor
import Probability.Process.Path.Corridor

/-!
# Functional-limit input for Mogulskii corridor bounds

This module isolates the exact consequences of a functional central limit
theorem needed by the small-deviation proof.  Open and closed path corridors
give respectively the Portmanteau `liminf` and `limsup` bounds for strict and
weak discrete tube probabilities.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

namespace ProbabilityTheory.BranchingRandomWalk.RandomWalk

open Combinatorics.Branching.Walk

theorem measure_openCorridor_le_liminf_strictTube_of_functionalLimit
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (limit : Omega → C(Skorokhod.UnitInterval, ℝ))
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
    (limit : Omega → C(Skorokhod.UnitInterval, ℝ))
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

end ProbabilityTheory.BranchingRandomWalk.RandomWalk
