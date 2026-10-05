/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Path.Block.Corridor
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Tightness

/-!
# One-block corridor approximation

Endpoint control in a corridor shrunk by a positive margin controls the whole
block, up to an error bounded by the centered unit-variance maximal
inequality.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.RandomWalk

open _root_.ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii


/-- One-block corridor approximation under centered unit-second-moment IID
increments. -/
theorem measure_startMargin_le_blockCorridor_add_error
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : IsCenteredUnitSecondMoment ν)
    {lower upper radius : ℝ} (hradius : 0 < radius)
    (start length : ℕ) :
    (iidSequenceLaw ν) {increment |
        lower + radius ≤ AdditivePath.displacement start increment ∧
          AdditivePath.displacement start increment ≤ upper - radius} ≤
      (iidSequenceLaw ν) {increment | ∀ k ≤ length,
          AdditivePath.displacement (start + k) increment ∈ Set.Icc lower upper} +
        ENNReal.ofReal ((length + 1 : ℝ) / radius ^ 2) := by
  calc
    _ ≤ (iidSequenceLaw ν) {increment | ∀ k ≤ length,
          AdditivePath.displacement (start + k) increment ∈ Set.Icc lower upper} +
        (iidSequenceLaw ν) {increment |
          ∃ k ∈ Finset.range (length + 1),
            radius ≤ |AdditivePath.blockSum start (k + 1) increment|} :=
      measure_startMargin_le_blockCorridor_add_largeDeviation
        (iidSequenceLaw ν) hradius.le start length
    _ ≤ _ := add_le_add_right
      (measure_exists_abs_blockSum_ge_le ν hν start hradius length) _

/-- Uniform asymptotic corridor approximation on a suitably short diffusive
block.  The block constant depends only on the requested relative margin and
error tolerance, while the result is uniform over block starts and interval
endpoints. -/
theorem exists_diffusiveBlockConstant_eventually_startMargin_le_corridor_add
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : IsCenteredUnitSecondMoment ν)
    {scale : ℕ → ℝ} (hscale : IsMogulskiiScale scale)
    {radiusFactor tolerance : ℝ}
    (hradiusFactor : 0 < radiusFactor) (htolerance : 0 < tolerance) :
    ∃ constant > 0, ∀ᶠ n in Filter.atTop,
      ∀ (start : ℕ) (lower upper : ℝ),
        (iidSequenceLaw ν) {increment |
            lower + radiusFactor * scale n ≤ AdditivePath.displacement start increment ∧
              AdditivePath.displacement start increment ≤
                upper - radiusFactor * scale n} ≤
          (iidSequenceLaw ν) {increment |
              ∀ k ≤ diffusiveBlockLength constant scale n,
                AdditivePath.displacement (start + k) increment ∈ Set.Icc lower upper} +
            ENNReal.ofReal tolerance := by
  obtain ⟨constant, hconstant, hoscillation⟩ :=
    exists_diffusiveBlockConstant_eventually_measure_max_le
      ν hν hscale hradiusFactor htolerance
  refine ⟨constant, hconstant, ?_⟩
  filter_upwards [hoscillation, _root_.ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.IsMogulskiiScale.eventually_pos hscale]
    with n hn hscalePos
  intro start lower upper
  calc
    _ ≤ (iidSequenceLaw ν) {increment |
            ∀ k ≤ diffusiveBlockLength constant scale n,
              AdditivePath.displacement (start + k) increment ∈ Set.Icc lower upper} +
          (iidSequenceLaw ν) {increment |
            ∃ k ∈ Finset.range
                (diffusiveBlockLength constant scale n + 1),
              radiusFactor * scale n ≤
                |AdditivePath.blockSum start (k + 1) increment|} :=
      measure_startMargin_le_blockCorridor_add_largeDeviation
        (iidSequenceLaw ν)
        (mul_nonneg hradiusFactor.le hscalePos.le)
        start (diffusiveBlockLength constant scale n)
    _ ≤ _ := add_le_add_right (hn start) _

end ProbabilityTheory.RandomWalk
