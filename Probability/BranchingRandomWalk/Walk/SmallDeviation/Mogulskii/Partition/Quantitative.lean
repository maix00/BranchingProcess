import Probability.BranchingRandomWalk.Walk.SmallDeviation.Mogulskii.Partition

/-!
# Quantitative finite-partition tightness

This file keeps the diffusive block constant explicit.  The resulting error
is therefore available for the later numerical choice of a common positive
one-block survival bound.
-/

open Filter MeasureTheory Set

namespace ProbabilityTheory.BranchingRandomWalk.RandomWalk

open Combinatorics.Branching.Walk

/-- With a fixed positive diffusive block constant, normalized endpoint
containment controls all block corridors up to the explicit asymptotic
maximal-inequality error. -/
theorem eventually_normalizedEndpoints_le_corridors_add_explicitError
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : IsCenteredUnitSecondMoment ν)
    {scale : ℕ → ℝ} (hscale : IsMogulskiiScale scale)
    {constant radiusFactor error : ℝ}
    (hconstant : 0 < constant) (hradiusFactor : 0 < radiusFactor)
    (herror : 0 < error) (blocks : ℕ) :
    ∀ᶠ n in atTop, ∀ lower upper : ℕ → ℝ,
      (independentIncrementLaw ν) {increment | ∀ j < blocks,
          partialSum
              (j * diffusiveBlockLength constant scale n) increment /
              scale n ∈
            Set.Ioo (lower j + radiusFactor) (upper j - radiusFactor)} ≤
        (independentIncrementLaw ν) {increment | ∀ j < blocks,
            ∀ k ≤ diffusiveBlockLength constant scale n,
              partialSum
                  (j * diffusiveBlockLength constant scale n + k) increment ∈
                Set.Icc (scale n * lower j) (scale n * upper j)} +
          ENNReal.ofReal
            (blocks * (constant / radiusFactor ^ 2 + error)) := by
  have hoscillation := eventually_measure_diffusiveBlockMaximum_le
    ν hν hscale hconstant hradiusFactor herror
  filter_upwards [hoscillation, hscale.eventually_pos]
    with n hn hscalePos
  intro lower upper
  let length := diffusiveBlockLength constant scale n
  calc
    _ ≤ (independentIncrementLaw ν) {increment | ∀ j < blocks,
          scale n * lower j + scale n * radiusFactor ≤
              partialSum (j * length) increment ∧
            partialSum (j * length) increment ≤
              scale n * upper j - scale n * radiusFactor} :=
      measure_normalizedEndpoints_le_partitionStartMargins
        (independentIncrementLaw ν) hscalePos lower upper
    _ ≤ (independentIncrementLaw ν) {increment | ∀ j < blocks,
          ∀ k ≤ length,
            partialSum (j * length + k) increment ∈
              Set.Icc (scale n * lower j) (scale n * upper j)} +
        ∑ j ∈ Finset.range blocks,
          (independentIncrementLaw ν) {increment |
            ∃ k ∈ Finset.range (length + 1),
              scale n * radiusFactor ≤
                |blockSum (j * length) (k + 1) increment|} :=
      measure_partitionStartMargins_le_corridors_add_sum_largeDeviation
        (independentIncrementLaw ν)
        (mul_nonneg hscalePos.le hradiusFactor.le)
        (fun j => scale n * lower j) (fun j => scale n * upper j)
    _ ≤ (independentIncrementLaw ν) {increment | ∀ j < blocks,
          ∀ k ≤ length,
            partialSum (j * length + k) increment ∈
              Set.Icc (scale n * lower j) (scale n * upper j)} +
        ∑ _j ∈ Finset.range blocks,
          ENNReal.ofReal (constant / radiusFactor ^ 2 + error) := by
      apply add_le_add_right
      apply Finset.sum_le_sum
      intro j hj
      simpa only [independentIncrementLaw, length, mul_comm] using
        hn (j * length)
    _ = _ := by
      congr 1
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      rw [← ENNReal.ofReal_natCast,
        ← ENNReal.ofReal_mul (Nat.cast_nonneg blocks)]

/-- The fixed-constant estimate also preserves an arbitrary final endpoint
event.  This is the form used by an outer-corridor/inner-return block kernel. -/
theorem eventually_normalizedEndpoints_inter_le_corridors_inter_add_explicitError
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : IsCenteredUnitSecondMoment ν)
    {scale : ℕ → ℝ} (hscale : IsMogulskiiScale scale)
    {constant radiusFactor error : ℝ}
    (hconstant : 0 < constant) (hradiusFactor : 0 < radiusFactor)
    (herror : 0 < error) (blocks : ℕ) :
    ∀ᶠ n in atTop, ∀ lower upper : ℕ → ℝ,
      ∀ final : Set (ℕ → ℝ),
      (independentIncrementLaw ν)
          ({increment | ∀ j < blocks,
            partialSum
                (j * diffusiveBlockLength constant scale n) increment /
                scale n ∈
              Set.Ioo (lower j + radiusFactor)
                (upper j - radiusFactor)} ∩ final) ≤
        (independentIncrementLaw ν)
            ({increment | ∀ j < blocks,
              ∀ k ≤ diffusiveBlockLength constant scale n,
                partialSum
                    (j * diffusiveBlockLength constant scale n + k)
                      increment ∈
                  Set.Icc (scale n * lower j)
                    (scale n * upper j)} ∩ final) +
          ENNReal.ofReal
            (blocks * (constant / radiusFactor ^ 2 + error)) := by
  have hoscillation := eventually_measure_diffusiveBlockMaximum_le
    ν hν hscale hconstant hradiusFactor herror
  filter_upwards [hoscillation, hscale.eventually_pos]
    with n hn hscalePos
  intro lower upper final
  let length := diffusiveBlockLength constant scale n
  calc
    _ ≤ (independentIncrementLaw ν)
          ({increment | ∀ j < blocks, ∀ k ≤ length,
            partialSum (j * length + k) increment ∈
              Set.Icc (scale n * lower j) (scale n * upper j)} ∩ final) +
        ∑ j ∈ Finset.range blocks,
          (independentIncrementLaw ν) {increment |
            ∃ k ∈ Finset.range (length + 1),
              scale n * radiusFactor ≤
                |blockSum (j * length) (k + 1) increment|} :=
      measure_normalizedEndpoints_inter_le_corridors_inter_add_sum_largeDeviation
        (independentIncrementLaw ν) hscalePos hradiusFactor.le lower upper final
    _ ≤ (independentIncrementLaw ν)
          ({increment | ∀ j < blocks, ∀ k ≤ length,
            partialSum (j * length + k) increment ∈
              Set.Icc (scale n * lower j) (scale n * upper j)} ∩ final) +
        ∑ _j ∈ Finset.range blocks,
          ENNReal.ofReal (constant / radiusFactor ^ 2 + error) := by
      apply add_le_add_right
      apply Finset.sum_le_sum
      intro j hj
      simpa only [independentIncrementLaw, length, mul_comm] using
        hn (j * length)
    _ = _ := by
      congr 1
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      rw [← ENNReal.ofReal_natCast,
        ← ENNReal.ofReal_mul (Nat.cast_nonneg blocks)]

end ProbabilityTheory.BranchingRandomWalk.RandomWalk
