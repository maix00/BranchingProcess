import Mathlib.Topology.UnitInterval
import Probability.BranchingRandomWalk.Walk.Path.Interpolation.Corridor
import Probability.BranchingRandomWalk.Walk.Path.Skorokhod.Corridor
import Probability.BranchingRandomWalk.Walk.SmallDeviation.Mogulskii.FunctionalLimit.Weighted
import Probability.BranchingRandomWalk.Walk.SmallDeviation.Mogulskii.FunctionalLimit.Endpoint
import Probability.Process.Path.Corridor
import Probability.Process.Path.Skorokhod.Corridor

/-!
# Functional-limit input for Mogulskii corridor bounds

This module isolates the exact consequences of a functional central limit
theorem needed by the small-deviation proof.  Open and closed path corridors
give respectively the Portmanteau `liminf` and `limsup` bounds for strict and
weak discrete tube probabilities.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

namespace ProbabilityTheory.RandomWalk

open Combinatorics.Branching.Walk

/-- A càdlàg functional limit theorem at an arbitrary positive spatial scale
gives the `liminf` bound for strict finite tubes.  The target event uses a
positive uniform margin, which is the correct open event for the Skorokhod
`J₁` topology. -/
theorem measure_skorokhodCorridor_le_liminf_strictTube_of_functionalLimit
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (scale : ℕ → ℝ) (hscale : ∀ᶠ n in atTop, 0 < scale n)
    (limit : Omega → CadlagPath unitInterval ℝ)
    (hlimit : TendstoInDistribution
      (fun n => normalizedStepCadlagPathIcc scale n)
      atTop limit (fun _ => independentIncrementLaw nu) P)
    {a : ℝ} (ha : 0 < a) (haOne : a < 1) :
    P.map limit (Skorokhod.rangeInOpenInterval (-a) (1 - a)) ≤
      atTop.liminf (fun n : ℕ =>
        independentIncrementLaw nu
          {increment | InOpenHorizontalTube a (scale n) n increment}) := by
  have hcorridor := hlimit.measure_skorokhodCorridor_le_liminf (-a) (1 - a)
  refine hcorridor.trans_eq ?_
  apply liminf_congr
  filter_upwards [eventually_gt_atTop 0, hscale] with n hn hscalePos
  change normalizedStepPathLaw nu scale n
      (Skorokhod.rangeInOpenInterval (-a) (1 - a)) = _
  exact normalizedStepPathLaw_apply_rangeInOpenInterval
    nu scale hn hscalePos ha haOne

/-- A càdlàg functional limit theorem gives the `liminf` bound for centered
strict tubes of every positive normalized width. -/
theorem measure_centeredSkorokhodCorridor_le_liminf_strictTube_of_functionalLimit
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (scale : ℕ → ℝ) (hscale : ∀ᶠ n in atTop, 0 < scale n)
    (limit : Omega → CadlagPath unitInterval ℝ)
    (hlimit : TendstoInDistribution
      (fun n => normalizedStepCadlagPathIcc scale n)
      atTop limit (fun _ => independentIncrementLaw nu) P)
    {width : ℝ} (hwidth : 0 < width) :
    P.map limit
        (Skorokhod.rangeInOpenInterval (-(width / 2)) (width / 2)) ≤
      atTop.liminf (fun n : ℕ =>
        independentIncrementLaw nu
          {increment | InOpenHorizontalTube (1 / 2)
            (width * scale n) n increment}) := by
  have hcorridor := hlimit.measure_skorokhodCorridor_le_liminf
    (-(width / 2)) (width / 2)
  refine hcorridor.trans_eq ?_
  apply liminf_congr
  filter_upwards [eventually_gt_atTop 0, hscale] with n hn hscalePos
  change normalizedStepPathLaw nu scale n
      (Skorokhod.rangeInOpenInterval (-(width / 2)) (width / 2)) = _
  exact normalizedStepPathLaw_apply_centeredOpenInterval
    nu scale hn hscalePos hwidth

/-- A càdlàg functional limit theorem at an arbitrary positive spatial scale
bounds the `limsup` of weak finite tubes by the limiting closed-corridor
probability. -/
theorem limsup_weakTube_le_measure_skorokhodCorridor_of_functionalLimit
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (scale : ℕ → ℝ) (hscale : ∀ᶠ n in atTop, 0 < scale n)
    (limit : Omega → CadlagPath unitInterval ℝ)
    (hlimit : TendstoInDistribution
      (fun n => normalizedStepCadlagPathIcc scale n)
      atTop limit (fun _ => independentIncrementLaw nu) P)
    {a : ℝ} (ha : 0 ≤ a) (haOne : a ≤ 1) :
    atTop.limsup (fun n : ℕ =>
        independentIncrementLaw nu
          {increment | InHorizontalTube a (scale n) n increment}) ≤
      P.map limit (Skorokhod.rangeInClosedInterval (-a) (1 - a)) := by
  have hcorridor :=
    hlimit.limsup_measure_skorokhodCorridor_le (-a) (1 - a)
  refine Eq.trans_le ?_ hcorridor
  apply limsup_congr
  filter_upwards [eventually_gt_atTop 0, hscale] with n hn hscalePos
  change independentIncrementLaw nu
      {increment | InHorizontalTube a (scale n) n increment} =
    normalizedStepPathLaw nu scale n
      (Skorokhod.rangeInClosedInterval (-a) (1 - a))
  symm
  exact normalizedStepPathLaw_apply_rangeInClosedInterval
    nu scale hn hscalePos ha haOne

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
