/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Distributions.Moments.Real
public import Probability.Process.RandomWalk.Path.Block.Law.Basic
public import Probability.Process.RandomWalk.Path.Block.Maximal.SecondMoment
public import Probability.Process.RandomWalk.Path.Block.Partition.Core
public import Probability.Process.RandomWalk.Path.Block.Partition.Normalized

/-!
# Finite-variance probability bounds for partitioned paths

For a probability measure $\nu$ on increments with mean zero and second
moment one, write $D_k=\operatorname{AdditivePath.displacement}(k,\cdot)$.
The public declarations in `ProbabilityTheory.RandomWalk` are:

- `measure_partitionStartMargins_le_corridors_add_error`: for block length
  $\ell$, margin $r>0$, and endpoint intervals $[a_j,b_j]$, the probability
  that every block start lies in $[a_j+r,b_j-r]$ is at most the probability
  that every partial sum in every block lies in $[a_j,b_j]$, plus
  $m(\ell+1)/r^2$.
- `measure_normalizedEndpoints_le_corridors_add_error`: after scaling the
  endpoint locations by $c>0$, the same comparison has total error
  $m(\ell+1)/(cr)^2$.

The only probabilistic input is the centered unit-second-moment block maximal
bound. The path and partition comparison itself is independent of any
small-deviation scale.
-/

open MeasureTheory Set

@[expose] public section

namespace ProbabilityTheory.RandomWalk

/-- Under the centered unit-second-moment assumptions, simultaneous margins at
block starts are bounded by the probability of staying inside every block
corridor, plus the sum of the explicit maximal-inequality errors. -/
theorem measure_partitionStartMargins_le_corridors_add_error
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : IsCenteredUnitSecondMoment ν)
    {blocks length : ℕ} {radius : ℝ} (hradius : 0 < radius)
    (lower upper : ℕ → ℝ) :
    (iidSequenceLaw ν) {increment | ∀ j < blocks,
        lower j + radius ≤ AdditivePath.displacement (j * length) increment ∧
          AdditivePath.displacement (j * length) increment ≤ upper j - radius} ≤
      (iidSequenceLaw ν) {increment | ∀ j < blocks, ∀ k ≤ length,
          AdditivePath.displacement (j * length + k) increment ∈
            Set.Icc (lower j) (upper j)} +
        ∑ _j ∈ Finset.range blocks,
          ENNReal.ofReal ((length + 1 : ℝ) / radius ^ 2) := by
  refine (measure_partitionStartMargins_le_corridors_add_sum_largeDeviation
    (iidSequenceLaw ν) hradius.le lower upper).trans ?_
  apply add_le_add_right
  exact Finset.sum_le_sum fun j hj =>
    measure_exists_abs_blockSum_ge_le ν hν (j * length) hradius length

/-- A normalized finite-partition endpoint event controls the full
unnormalized path on every block, with the explicit sum of within-block
oscillation errors. -/
theorem measure_normalizedEndpoints_le_corridors_add_error
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : IsCenteredUnitSecondMoment ν)
    {blocks length : ℕ} {scale radius : ℝ}
    (hscale : 0 < scale) (hradius : 0 < radius)
    (lower upper : ℕ → ℝ) :
    (iidSequenceLaw ν) {increment | ∀ j < blocks,
        AdditivePath.displacement (j * length) increment / scale ∈
          Set.Ioo (lower j + radius) (upper j - radius)} ≤
      (iidSequenceLaw ν) {increment | ∀ j < blocks, ∀ k ≤ length,
          AdditivePath.displacement (j * length + k) increment ∈
            Set.Icc (scale * lower j) (scale * upper j)} +
        ∑ _j ∈ Finset.range blocks,
          ENNReal.ofReal ((length + 1 : ℝ) / (scale * radius) ^ 2) := by
  calc
    _ ≤ (iidSequenceLaw ν) {increment | ∀ j < blocks,
          scale * lower j + scale * radius ≤
              AdditivePath.displacement (j * length) increment ∧
            AdditivePath.displacement (j * length) increment ≤
              scale * upper j - scale * radius} :=
      measure_normalizedEndpoints_le_partitionStartMargins
        (iidSequenceLaw ν) hscale lower upper
    _ ≤ _ := measure_partitionStartMargins_le_corridors_add_error
      ν hν (mul_pos hscale hradius) (fun j => scale * lower j)
        (fun j => scale * upper j)

end ProbabilityTheory.RandomWalk

end
