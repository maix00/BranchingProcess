import Combinatorics.BranchingWalk.Walk.Path.Skorokhod.Corridor
import Topology.Cadlag.Skorokhod.Corridor.Endpoint

/-!
# Endpoint-constrained corridors for normalized walk paths

This file identifies an open Skorokhod corridor with an open endpoint
constraint with its finite random-walk path formulation.
-/

namespace Combinatorics.Branching.Walk

/-- Membership of the normalized step path in a centered open corridor with
an open terminal interval is exactly a strict finite tube together with the
corresponding normalized endpoint constraint. -/
theorem normalizedStepCadlagPathIcc_mem_centeredOpenIntervalEndsIn_iff
    (scale : ℕ → ℝ) {n : ℕ} (hn : 0 < n) (hscale : 0 < scale n)
    {width endpointLower endpointUpper : ℝ} (hwidth : 0 < width)
    (increment : ℕ → ℝ) :
    normalizedStepCadlagPathIcc scale n increment ∈
        Skorokhod.rangeInOpenIntervalEndsIn
          (-(width / 2)) (width / 2) endpointLower endpointUpper ↔
      InOpenHorizontalTube (1 / 2) (width * scale n) n increment ∧
        partialSum n increment / scale n ∈
          Set.Ioo endpointLower endpointUpper := by
  rw [Skorokhod.mem_rangeInOpenIntervalEndsIn_iff,
    normalizedStepCadlagPathIcc_mem_centeredOpenInterval_iff
      scale hn hscale hwidth]
  change _ ∧ normalizedStepPath scale n increment 1 ∈ _ ↔ _
  rw [normalizedStepPath_one, inv_mul_eq_div]

end Combinatorics.Branching.Walk
