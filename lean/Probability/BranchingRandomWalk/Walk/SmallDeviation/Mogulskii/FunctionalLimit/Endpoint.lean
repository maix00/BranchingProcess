import Probability.BranchingRandomWalk.Walk.Path.Skorokhod.Corridor.Endpoint
import Probability.ConvergenceInDistribution.Portmanteau

/-!
# Functional-limit bounds with an endpoint constraint

Portmanteau transfers an open path corridor together with an open terminal
interval to the corresponding finite random-walk event.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

namespace ProbabilityTheory.RandomWalk

open Combinatorics.Branching.Walk

/-- A càdlàg functional limit theorem gives the `liminf` bound for a centered
strict tube whose normalized endpoint lies in a prescribed open interval. -/
theorem measure_centeredSkorokhodCorridorEndsIn_le_liminf_strictTubeEndsIn_of_functionalLimit
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (scale : ℕ → ℝ) (hscale : ∀ᶠ n in atTop, 0 < scale n)
    (limit : Ω → CadlagPath Skorokhod.UnitInterval ℝ)
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
  have hevent := hlimit.measure_map_le_liminf_of_isOpen
    (Skorokhod.isOpen_rangeInOpenIntervalEndsIn
      (-(width / 2)) (width / 2) endpointLower endpointUpper)
  refine hevent.trans_eq ?_
  apply liminf_congr
  filter_upwards [eventually_gt_atTop 0, hscale] with n hn hscalePos
  change normalizedStepPathLaw ν scale n
      (Skorokhod.rangeInOpenIntervalEndsIn
        (-(width / 2)) (width / 2) endpointLower endpointUpper) = _
  exact normalizedStepPathLaw_apply_centeredOpenIntervalEndsIn
    ν scale hn hscalePos hwidth

end ProbabilityTheory.RandomWalk
