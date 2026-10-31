/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Topology.Cadlag.Skorokhod.SmallDeviation.RangeCover
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

/-!
# Finite range cover under a path-space measure

The finite union estimate for path-space oscillation events, stated for an
arbitrary measure on càdlàg path space.

## Public declarations

- For k > 0, the measure of the scaled range tube of width 1 is
  bounded by the sum of the measures of its 2k+1 scaled corridor events.
  Explicitly, for a measure \(Q\) and \(k>0\),
  \[
  Q(\operatorname{scaleSet}(a,\operatorname{rangeTubeStartingAtZero}(1)))
  \le \sum_{j=0}^{2k}
  Q\!\left(\operatorname{scaleSet}\!\left(a,
  \operatorname{corridorStartingAtZero}\!\left(
  \frac{j}{k}-1-\left(1+\frac{2}{k}\right),
  \frac{j}{k}-1+\left(1+\frac{2}{k}\right)\right)\right)\right).
  \]
-/

@[expose] public section

namespace MeasureTheory

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

end MeasureTheory

end
