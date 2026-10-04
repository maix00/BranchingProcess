/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Topology.Cadlag.Skorokhod.SmallDeviation.RangeCover
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

/-!
# Finite range cover for path probabilities

The finite union estimate for path-space oscillation events. It is stated
for an arbitrary path measure, independently of any stable-process law.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory

theorem measure_scaledRangeTube_le_sum_scaledCorridors
    (Q : Measure (CadlagPath unitInterval ℝ)) (a : ℝ)
    (k : ℕ) (hk : 0 < k) :
    Q (Skorokhod.scaleSet a (Skorokhod.rangeTubeStartingAtZero 1)) ≤
      ∑ j ∈ Finset.range (2 * k + 1),
        Q (Skorokhod.scaleSet a (Skorokhod.corridorStartingAtZero
          (((j : ℝ) / k - 1) - (1 + 2 / k))
          (((j : ℝ) / k - 1) + (1 + 2 / k)))) := by
  calc
    _ ≤ Q (⋃ j ∈ Finset.range (2 * k + 1),
        Skorokhod.scaleSet a (Skorokhod.corridorStartingAtZero
          (((j : ℝ) / k - 1) - (1 + 2 / k))
          (((j : ℝ) / k - 1) + (1 + 2 / k)))) :=
      measure_mono (Skorokhod.scaledRangeTube_subset_iUnion_scaledCorridors a k hk)
    _ ≤ _ := measure_biUnion_finset_le _ _

end ProbabilityTheory

end
