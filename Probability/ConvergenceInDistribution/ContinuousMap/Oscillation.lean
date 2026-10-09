/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import MeasureTheory.Measure.ContinuousMap.Oscillation
public import Probability.ConvergenceInDistribution.Portmanteau
public import Topology.ContinuousMap.Oscillation

/-!
# Oscillation bounds under functional convergence

The finite cover is a deterministic path-space estimate. This file supplies
its Portmanteau consequence for convergent continuous-path laws.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory.ContinuousMap

/-- Under functional convergence, the range-oscillation mass of the limit is
bounded by the finite sum of `liminf` masses of the fixed open corridors. -/
theorem TendstoInDistribution.measure_rangeOscillationSet_le_sum_liminf_finiteCorridorCover
    {Ω : ℕ → Type*} {mΩ : ∀ n, MeasurableSpace (Ω n)}
    {μ : (n : ℕ) → Measure (Ω n)} [∀ n, IsProbabilityMeasure (μ n)]
    {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'}
    [IsProbabilityMeasure μ']
    {X : (n : ℕ) → Ω n → C(unitInterval, ℝ)}
    {Z : Ω' → C(unitInterval, ℝ)}
    (h : TendstoInDistribution X atTop Z μ μ')
    {width : ℝ} {count : ℕ}
    (hwidth : 0 < width) (hcount : 0 < count)
    (hstart : ∀ᵐ path ∂μ'.map Z, path (0 : unitInterval) = 0) :
    μ'.map Z (ContinuousMap.rangeOscillationSet width) ≤
      ∑ j : Fin count, atTop.liminf (fun n =>
        (μ n).map (X n)
          (ContinuousMap.rangeInOpenInterval
            (ContinuousMap.oscillationCoverLower width count j)
            (ContinuousMap.oscillationCoverUpper width count j))) := by
  calc
    μ'.map Z (ContinuousMap.rangeOscillationSet width) ≤
        ∑ j : Fin count, μ'.map Z
          (ContinuousMap.rangeInOpenInterval
            (ContinuousMap.oscillationCoverLower width count j)
            (ContinuousMap.oscillationCoverUpper width count j)) :=
      MeasureTheory.ContinuousMap.measure_rangeOscillationSet_le_finiteCorridorCover
        (μ'.map Z) hwidth hcount hstart
    _ ≤ ∑ j : Fin count, atTop.liminf (fun n =>
          (μ n).map (X n)
            (ContinuousMap.rangeInOpenInterval
              (ContinuousMap.oscillationCoverLower width count j)
              (ContinuousMap.oscillationCoverUpper width count j))) := by
      apply Finset.sum_le_sum
      intro j _hj
      exact h.measure_map_le_liminf_of_isOpen
        (ContinuousMap.isOpen_rangeInOpenInterval
          (ContinuousMap.oscillationCoverLower_lt_upper
            width count j hwidth hcount))

end ProbabilityTheory.ContinuousMap

end
