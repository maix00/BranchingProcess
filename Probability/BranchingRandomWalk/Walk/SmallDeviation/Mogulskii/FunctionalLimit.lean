import Probability.BranchingRandomWalk.Walk.Path.Interpolation.Corridor
import Probability.Process.Path.Corridor

/-!
# Functional-limit input for Mogulskii corridor bounds

This module isolates the exact consequence of a functional central limit
theorem needed by the small-deviation proof.  Once polygonal random-walk
paths converge in continuous path space, the limiting process's open-tube
probability is a lower bound for the `liminf` of strict discrete tube
probabilities.
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

end ProbabilityTheory.BranchingRandomWalk.RandomWalk
