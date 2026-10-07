/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Discrete.EndpointBands
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Scale

/-!
# Stable-block endpoint return lower bound

This is the endpoint-return part of Mogulskii's discrete lower estimate (33),
specialized to the stable block length.  It assumes explicit lower bounds for
the seven one-block endpoint-band probabilities.  It does not derive those
probability bounds from stable path convergence; that analytic input remains
separate.
-/

open MeasureTheory

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

/-- Seven endpoint-band lower bounds for one stable-length block imply a
horizontal-tube lower bound after any number of complete blocks.  The
one-block assumptions are stated on normalized increments, while the
conclusion is returned to the original increment scale.  The resulting tube
has radius `radius + 4 * ε`, accounting for the return core and endpoint
bands in the discrete gluing argument. -/
theorem horizontalTubeProbability_ge_pow_stableEndpointBands
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (radius ε : ℝ) (scale : ℕ → ℝ) (n blocks horizon : ℕ)
    {α constant : ℝ} (hε : 0 < ε) (hscale : 0 < scale n)
    (hcover : horizon ≤ blocks * stableBlockLength α ν constant scale n)
    (lowerBound : ENNReal)
    (hband : ∀ i ∈ Finset.Icc (-3 : ℤ) 3,
      lowerBound ≤ iidSequenceLaw (ν.map fun x : ℝ => x / scale n)
        (endpointBandBlockEvent radius ε i
          (stableBlockLength α ν constant scale n))) :
    lowerBound ^ blocks ≤
      horizontalTubeProbability (iidSequenceLaw ν) (1 / 2)
        (2 * (radius + 4 * ε) * scale n) horizon := by
  have hnormalized := horizontalTubeProbability_ge_pow_endpointBands_of_horizon_le
    (ν.map fun x : ℝ => x / scale n) hε blocks
    (stableBlockLength α ν constant scale n) horizon hcover lowerBound hband
  have hmap := horizontalTubeProbability_map_div ν (1 / 2)
    (2 * (radius + 4 * ε) * scale n) horizon hscale
  have hwidth :
      (2 * (radius + 4 * ε) * scale n) / scale n = 2 * (radius + 4 * ε) := by
    field_simp [hscale.ne']
  rw [hwidth] at hmap
  exact hnormalized.trans_eq hmap

/-- The stable endpoint-return estimate with the source count
`⌊horizon / blockLength⌋ + 1`.  One extra block covers the final incomplete
segment, as in Mogulskii's equation (33). -/
theorem horizontalTubeProbability_ge_pow_stableEndpointBands_of_quotientBlockCount
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (radius ε : ℝ) (scale : ℕ → ℝ) (n horizon : ℕ)
    {α constant : ℝ} (hε : 0 < ε) (hscale : 0 < scale n)
    (hblock : 0 < stableBlockLength α ν constant scale n)
    (lowerBound : ENNReal)
    (hband : ∀ i ∈ Finset.Icc (-3 : ℤ) 3,
      lowerBound ≤ iidSequenceLaw (ν.map fun x : ℝ => x / scale n)
        (endpointBandBlockEvent radius ε i
          (stableBlockLength α ν constant scale n))) :
    lowerBound ^ (horizon / stableBlockLength α ν constant scale n + 1) ≤
      horizontalTubeProbability (iidSequenceLaw ν) (1 / 2)
        (2 * (radius + 4 * ε) * scale n) horizon := by
  let length := stableBlockLength α ν constant scale n
  have hdecomp : horizon = horizon / length * length + horizon % length := by
    simpa [Nat.mul_comm] using (Nat.div_add_mod horizon length).symm
  have hcover : horizon ≤ (horizon / length + 1) * length := by
    calc
      horizon = horizon / length * length + horizon % length := hdecomp
      _ ≤ horizon / length * length + length :=
        Nat.add_le_add_left (Nat.mod_lt horizon hblock).le _
      _ = (horizon / length + 1) * length := by simp [Nat.add_mul]
  simpa [length] using horizontalTubeProbability_ge_pow_stableEndpointBands
    ν radius ε scale n (horizon / length + 1) horizon hε hscale hcover
    lowerBound hband

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete
