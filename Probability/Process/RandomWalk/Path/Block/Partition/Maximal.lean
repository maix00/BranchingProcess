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
public import Analysis.Asymptotics.Scale.Block.Length

/-!
# Finite-variance probability bounds for partitioned paths

For a probability measure $\nu$ on increments with mean zero and second
moment one, write $D_k=\operatorname{AdditivePath.displacement}(k,\cdot)$.

## Public declarations

* `measure_partitionStartMargins_le_corridors_add_error` bounds the
  simultaneous shrunken block-start event by the all-block corridor event
  plus `∑ _j ∈ Finset.range blocks,
  ENNReal.ofReal ((length + 1 : ℝ) / radius ^ 2)` under centered unit second
  moment.
* `measure_normalizedEndpoints_le_corridors_add_error` gives the scaled bound
  with error `∑ _j ∈ Finset.range blocks,
  ENNReal.ofReal ((length + 1 : ℝ) / (scale * radius) ^ 2)`.
* `eventually_measure_normalizedEndpoints_le_corridors_add_of_lengthRatio`
  and
  `eventually_measure_normalizedEndpoints_inter_le_corridors_inter_add_of_lengthRatio`
  give the eventual finite-family bounds when
  `((length n + 1 : ℕ) : ℝ) / scale n ^ 2 → limit`, with error
  `ENNReal.ofReal (blocks * (limit / radiusFactor ^ 2 + error))`, with and
  without a common terminal event.
* `exists_scaledBlockConstant_eventually_normalizedEndpoints_le_corridors_add`
  chooses `constant > 0` so the same eventual comparison with
  `length n = floorBlockLength (fun n => constant * scale n ^ 2) n` has error
  at most `ENNReal.ofReal tolerance` as `scale → ∞`.

The only probabilistic input is the centered unit-second-moment block maximal
bound. The path and partition comparison itself is independent of any
small-deviation scale.
-/

open Filter MeasureTheory Set

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

/-- A limiting ratio for block length to squared spatial scale gives an
eventual finite-partition endpoint-to-corridor estimate. -/
theorem eventually_measure_normalizedEndpoints_le_corridors_add_of_lengthRatio
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : IsCenteredUnitSecondMoment ν)
    {scale : ℕ → ℝ} {length : ℕ → ℕ}
    (hscalePos : ∀ᶠ n in atTop, 0 < scale n)
    {limit radiusFactor error : ℝ}
    (hradiusFactor : 0 < radiusFactor) (herror : 0 < error)
    (hlengthRatio : Tendsto (fun n =>
        ((length n + 1 : ℕ) : ℝ) / scale n ^ 2)
      atTop (nhds limit))
    (blocks : ℕ) :
    ∀ᶠ n in atTop, ∀ lower upper : ℕ → ℝ,
      (iidSequenceLaw ν) {increment | ∀ j < blocks,
          AdditivePath.displacement (j * length n) increment / scale n ∈
            Set.Ioo (lower j + radiusFactor) (upper j - radiusFactor)} ≤
        (iidSequenceLaw ν) {increment | ∀ j < blocks, ∀ k ≤ length n,
            AdditivePath.displacement (j * length n + k) increment ∈
              Set.Icc (scale n * lower j) (scale n * upper j)} +
          ENNReal.ofReal (blocks * (limit / radiusFactor ^ 2 + error)) := by
  let threshold : ℕ → ℝ := fun n => radiusFactor * scale n
  have hthresholdPos : ∀ᶠ n in atTop, 0 < threshold n := by
    filter_upwards [hscalePos] with n hn
    exact mul_pos hradiusFactor hn
  have hratioDiv := hlengthRatio.div_const (radiusFactor ^ 2)
  have hratio : Tendsto (fun n =>
      ((length n + 1 : ℕ) : ℝ) / threshold n ^ 2)
      atTop (nhds (limit / radiusFactor ^ 2)) := by
    convert hratioDiv.congr' ?_ using 1
    filter_upwards [hscalePos] with n hn
    dsimp [threshold]
    field_simp [hradiusFactor.ne', hn.ne']
  have hmaximum := eventually_measure_blockMaximum_le_of_tendsto_ratio
    ν hν hthresholdPos herror hratio
  filter_upwards [hmaximum, hscalePos] with n hmaximum hscalePos
  intro lower upper
  let lengthN := length n
  calc
    _ ≤ (iidSequenceLaw ν) {increment | ∀ j < blocks,
          scale n * lower j + scale n * radiusFactor ≤
              AdditivePath.displacement (j * lengthN) increment ∧
            AdditivePath.displacement (j * lengthN) increment ≤
              scale n * upper j - scale n * radiusFactor} :=
      measure_normalizedEndpoints_le_partitionStartMargins
        (iidSequenceLaw ν) hscalePos lower upper
    _ ≤ (iidSequenceLaw ν) {increment | ∀ j < blocks, ∀ k ≤ lengthN,
          AdditivePath.displacement (j * lengthN + k) increment ∈
            Set.Icc (scale n * lower j) (scale n * upper j)} +
        ∑ j ∈ Finset.range blocks,
          (iidSequenceLaw ν) {increment |
            ∃ k ∈ Finset.range (lengthN + 1),
              threshold n ≤
                |AdditivePath.blockSum (j * lengthN) (k + 1) increment|} :=
      (by
        simpa only [threshold, mul_comm] using
          measure_partitionStartMargins_le_corridors_add_sum_largeDeviation
            (iidSequenceLaw ν) (blocks := blocks) (length := lengthN)
            (radius := scale n * radiusFactor)
            (mul_nonneg hscalePos.le hradiusFactor.le)
            (fun j => scale n * lower j) (fun j => scale n * upper j))
    _ ≤ (iidSequenceLaw ν) {increment | ∀ j < blocks, ∀ k ≤ lengthN,
          AdditivePath.displacement (j * lengthN + k) increment ∈
            Set.Icc (scale n * lower j) (scale n * upper j)} +
        ∑ _j ∈ Finset.range blocks,
          ENNReal.ofReal (limit / radiusFactor ^ 2 + error) := by
      apply add_le_add_right
      apply Finset.sum_le_sum
      intro j hj
      simpa only [iidSequenceLaw, threshold, lengthN, mul_comm] using
        hmaximum (j * lengthN)
    _ = _ := by
      congr 1
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      rw [← ENNReal.ofReal_natCast,
        ← ENNReal.ofReal_mul (Nat.cast_nonneg blocks)]

/-- Intersecting both sides with the same terminal event preserves the
finite-partition endpoint-to-corridor estimate. -/
theorem eventually_measure_normalizedEndpoints_inter_le_corridors_inter_add_of_lengthRatio
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : IsCenteredUnitSecondMoment ν)
    {scale : ℕ → ℝ} {length : ℕ → ℕ}
    (hscalePos : ∀ᶠ n in atTop, 0 < scale n)
    {limit radiusFactor error : ℝ}
    (hradiusFactor : 0 < radiusFactor) (herror : 0 < error)
    (hlengthRatio : Tendsto (fun n =>
        ((length n + 1 : ℕ) : ℝ) / scale n ^ 2)
      atTop (nhds limit))
    (blocks : ℕ) :
    ∀ᶠ n in atTop, ∀ lower upper : ℕ → ℝ,
      ∀ final : Set (ℕ → ℝ),
        (iidSequenceLaw ν)
            ({increment | ∀ j < blocks,
              AdditivePath.displacement (j * length n) increment / scale n ∈
                Set.Ioo (lower j + radiusFactor) (upper j - radiusFactor)} ∩ final) ≤
          (iidSequenceLaw ν)
              ({increment | ∀ j < blocks, ∀ k ≤ length n,
                AdditivePath.displacement (j * length n + k) increment ∈
                  Set.Icc (scale n * lower j) (scale n * upper j)} ∩ final) +
            ENNReal.ofReal (blocks * (limit / radiusFactor ^ 2 + error)) := by
  let threshold : ℕ → ℝ := fun n => radiusFactor * scale n
  have hthresholdPos : ∀ᶠ n in atTop, 0 < threshold n := by
    filter_upwards [hscalePos] with n hn
    exact mul_pos hradiusFactor hn
  have hratioDiv := hlengthRatio.div_const (radiusFactor ^ 2)
  have hratio : Tendsto (fun n =>
      ((length n + 1 : ℕ) : ℝ) / threshold n ^ 2)
      atTop (nhds (limit / radiusFactor ^ 2)) := by
    convert hratioDiv.congr' ?_ using 1
    filter_upwards [hscalePos] with n hn
    dsimp [threshold]
    field_simp [hradiusFactor.ne', hn.ne']
  have hmaximum := eventually_measure_blockMaximum_le_of_tendsto_ratio
    ν hν hthresholdPos herror hratio
  filter_upwards [hmaximum, hscalePos] with n hmaximum hscalePos
  intro lower upper final
  let lengthN := length n
  calc
    _ ≤ (iidSequenceLaw ν)
          ({increment | ∀ j < blocks, ∀ k ≤ lengthN,
            AdditivePath.displacement (j * lengthN + k) increment ∈
              Set.Icc (scale n * lower j) (scale n * upper j)} ∩ final) +
        ∑ j ∈ Finset.range blocks,
          (iidSequenceLaw ν) {increment |
            ∃ k ∈ Finset.range (lengthN + 1),
              threshold n ≤
                |AdditivePath.blockSum (j * lengthN) (k + 1) increment|} :=
      (by
        simpa only [lengthN, threshold, mul_comm] using
          measure_normalizedEndpoints_inter_le_corridors_inter_add_sum_largeDeviation
            (iidSequenceLaw ν) (blocks := blocks) (length := lengthN)
            (scale := scale n) (radius := radiusFactor)
            hscalePos hradiusFactor.le lower upper final)
    _ ≤ (iidSequenceLaw ν)
          ({increment | ∀ j < blocks, ∀ k ≤ lengthN,
            AdditivePath.displacement (j * lengthN + k) increment ∈
              Set.Icc (scale n * lower j) (scale n * upper j)} ∩ final) +
        ∑ _j ∈ Finset.range blocks,
          ENNReal.ofReal (limit / radiusFactor ^ 2 + error) := by
      apply add_le_add_right
      apply Finset.sum_le_sum
      intro j hj
      simpa only [iidSequenceLaw, threshold, lengthN, mul_comm] using
        hmaximum (j * lengthN)
    _ = _ := by
      congr 1
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      rw [← ENNReal.ofReal_natCast,
        ← ENNReal.ofReal_mul (Nat.cast_nonneg blocks)]

/-- A diverging spatial scale admits a positive quadratic block constant
for which every fixed finite family of endpoint margins controls all block
corridors with an arbitrarily small total error. -/
theorem exists_scaledBlockConstant_eventually_normalizedEndpoints_le_corridors_add
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : IsCenteredUnitSecondMoment ν)
    {scale : ℕ → ℝ} (hscale : Tendsto scale atTop atTop)
    {blocks : ℕ} (hblocks : 0 < blocks)
    {radiusFactor tolerance : ℝ}
    (hradiusFactor : 0 < radiusFactor) (htolerance : 0 < tolerance) :
    ∃ constant > 0, ∀ᶠ n in atTop, ∀ lower upper : ℕ → ℝ,
      (iidSequenceLaw ν) {increment | ∀ j < blocks,
          AdditivePath.displacement
              (j * Asymptotics.floorBlockLength
                (fun n => constant * scale n ^ 2) n) increment / scale n ∈
            Set.Ioo (lower j + radiusFactor) (upper j - radiusFactor)} ≤
        (iidSequenceLaw ν) {increment | ∀ j < blocks,
            ∀ k ≤ Asymptotics.floorBlockLength
                (fun n => constant * scale n ^ 2) n,
              AdditivePath.displacement
                  (j * Asymptotics.floorBlockLength
                    (fun n => constant * scale n ^ 2) n + k) increment ∈
                Set.Icc (scale n * lower j) (scale n * upper j)} +
          ENNReal.ofReal tolerance := by
  have hblocksReal : 0 < (blocks : ℝ) := by exact_mod_cast hblocks
  have hperBlock : 0 < tolerance / (blocks : ℝ) :=
    div_pos htolerance hblocksReal
  obtain ⟨constant, hconstant, hoscillation⟩ :=
    exists_scaledBlockConstant_eventually_measure_blockMaximum_le
      ν hν hscale hradiusFactor hperBlock
  refine ⟨constant, hconstant, ?_⟩
  have hscalePos : ∀ᶠ n in atTop, 0 < scale n :=
    hscale.eventually (eventually_gt_atTop 0)
  filter_upwards [hoscillation, hscalePos] with n hn hscalePos
  intro lower upper
  let length := Asymptotics.floorBlockLength
    (fun n => constant * scale n ^ 2) n
  calc
    _ ≤ (iidSequenceLaw ν) {increment | ∀ j < blocks,
          scale n * lower j + scale n * radiusFactor ≤
              AdditivePath.displacement (j * length) increment ∧
            AdditivePath.displacement (j * length) increment ≤
              scale n * upper j - scale n * radiusFactor} :=
      measure_normalizedEndpoints_le_partitionStartMargins
        (iidSequenceLaw ν) hscalePos lower upper
    _ ≤ (iidSequenceLaw ν) {increment | ∀ j < blocks, ∀ k ≤ length,
          AdditivePath.displacement (j * length + k) increment ∈
            Set.Icc (scale n * lower j) (scale n * upper j)} +
        ∑ j ∈ Finset.range blocks,
          (iidSequenceLaw ν) {increment |
            ∃ k ∈ Finset.range (length + 1),
              radiusFactor * scale n ≤
                |AdditivePath.blockSum (j * length) (k + 1) increment|} :=
      (by
        simpa only [mul_comm] using
          measure_partitionStartMargins_le_corridors_add_sum_largeDeviation
            (iidSequenceLaw ν) (blocks := blocks) (length := length)
            (radius := scale n * radiusFactor)
            (mul_nonneg hscalePos.le hradiusFactor.le)
            (fun j => scale n * lower j) (fun j => scale n * upper j))
    _ ≤ (iidSequenceLaw ν) {increment | ∀ j < blocks, ∀ k ≤ length,
          AdditivePath.displacement (j * length + k) increment ∈
            Set.Icc (scale n * lower j) (scale n * upper j)} +
        ∑ _j ∈ Finset.range blocks,
          ENNReal.ofReal (tolerance / (blocks : ℝ)) := by
      apply add_le_add_right
      apply Finset.sum_le_sum
      intro j hj
      simpa only [iidSequenceLaw, length, mul_comm] using hn (j * length)
    _ = _ := by
      congr 1
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      rw [← ENNReal.ofReal_natCast,
        ← ENNReal.ofReal_mul (Nat.cast_nonneg blocks)]
      congr 1
      field_simp [hblocksReal.ne']

end ProbabilityTheory.RandomWalk

end
