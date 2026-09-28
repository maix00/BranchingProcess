import Combinatorics.BranchingWalk.Walk.Path.Block.Partition
import Probability.BranchingRandomWalk.Walk.Path.Block.Partition
import Probability.BranchingRandomWalk.Walk.SmallDeviation.Mogulskii.FiniteDimensional
import Probability.BranchingRandomWalk.Walk.SmallDeviation.Mogulskii.Maximal

/-!
# Finite-partition endpoint bounds

Finite-dimensional Gaussian block estimates are transferred to simultaneous
corridor constraints at all endpoints of an equal-length partition.
-/

open Filter MeasureTheory Set

namespace ProbabilityTheory.BranchingRandomWalk.RandomWalk

open Combinatorics.Branching.Walk

/-- If a deterministic reference path has enough margin at every partition
endpoint, then a product of Gaussian block probabilities bounds the liminf
probability that all normalized random-walk endpoints stay in their assigned
open intervals. -/
theorem prod_gaussian_Ioo_le_liminf_measure_partitionEndpoints
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hcentered : ∫ x, x ∂ν = 0)
    (hsecondMoment : ∫ x, x ^ 2 ∂ν = 1)
    {scale : ℕ → ℝ} (hscale : IsMogulskiiScale scale)
    {constant : ℝ} (hconstant : 0 < constant)
    {blocks : ℕ} {radius : ℝ} (hradius : 0 < radius)
    (target lower upper : ℕ → ℝ)
    (hmargin : ∀ k ≤ blocks,
      lower k + (blocks : ℝ) * radius <
          ∑ j ∈ Finset.range k, target j ∧
        ∑ j ∈ Finset.range k, target j <
          upper k - (blocks : ℝ) * radius) :
    (∏ j : Fin blocks,
        gaussianReal 0 1
          (Set.Ioo
            ((target j - radius) / Real.sqrt constant)
            ((target j + radius) / Real.sqrt constant))) ≤
      atTop.liminf (fun n =>
        (independentIncrementLaw ν) {increment |
          ∀ k ≤ blocks,
            partialSum
                (k * diffusiveBlockLength constant scale n) increment /
                scale n ∈ Set.Ioo (lower k) (upper k)}) := by
  let lowerBlock : Fin blocks → ℝ := fun j => target j - radius
  let upperBlock : Fin blocks → ℝ := fun j => target j + radius
  have hbox := prod_gaussian_Ioo_le_liminf_measure_diffusiveBlockSums
    ν hcentered hsecondMoment hscale hconstant blocks lowerBlock upperBlock
  refine hbox.trans (Filter.liminf_le_liminf ?_)
  filter_upwards [] with n
  apply measure_mono
  intro increment hincrement
  apply normalized_partitionEndpoints_mem_Ioo_of_blockApproximation
    (target := target) hradius.le
  · intro j hj
    have hjBox := hincrement ⟨j, hj⟩
    simp only [lowerBlock, upperBlock, Set.mem_Ioo] at hjBox
    apply le_of_lt
    rw [abs_lt]
    constructor <;> linarith
  · exact hmargin

/-- Under the centered unit-second-moment assumptions, simultaneous margins at
the starts of finitely many blocks are bounded by the probability of staying
inside every block corridor, plus the sum of the explicit maximal-inequality
errors. -/
theorem measure_partitionStartMargins_le_corridors_add_error
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : IsCenteredUnitSecondMoment ν)
    {blocks length : ℕ} {radius : ℝ} (hradius : 0 < radius)
    (lower upper : ℕ → ℝ) :
    (independentIncrementLaw ν) {increment | ∀ j < blocks,
        lower j + radius ≤ partialSum (j * length) increment ∧
          partialSum (j * length) increment ≤ upper j - radius} ≤
      (independentIncrementLaw ν) {increment | ∀ j < blocks, ∀ k ≤ length,
          partialSum (j * length + k) increment ∈
            Set.Icc (lower j) (upper j)} +
        ∑ _j ∈ Finset.range blocks,
          ENNReal.ofReal ((length + 1 : ℝ) / radius ^ 2) := by
  refine (measure_partitionStartMargins_le_corridors_add_sum_largeDeviation
    (independentIncrementLaw ν) hradius.le lower upper).trans ?_
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
    (independentIncrementLaw ν) {increment | ∀ j < blocks,
        partialSum (j * length) increment / scale ∈
          Set.Ioo (lower j + radius) (upper j - radius)} ≤
      (independentIncrementLaw ν) {increment | ∀ j < blocks, ∀ k ≤ length,
          partialSum (j * length + k) increment ∈
            Set.Icc (scale * lower j) (scale * upper j)} +
        ∑ _j ∈ Finset.range blocks,
          ENNReal.ofReal ((length + 1 : ℝ) / (scale * radius) ^ 2) := by
  calc
    _ ≤ (independentIncrementLaw ν) {increment | ∀ j < blocks,
          scale * lower j + scale * radius ≤
              partialSum (j * length) increment ∧
            partialSum (j * length) increment ≤
              scale * upper j - scale * radius} :=
      measure_normalizedEndpoints_le_partitionStartMargins
        (independentIncrementLaw ν) hscale lower upper
    _ ≤ _ := measure_partitionStartMargins_le_corridors_add_error
      ν hν (mul_pos hscale hradius) (fun j => scale * lower j)
        (fun j => scale * upper j)

end ProbabilityTheory.BranchingRandomWalk.RandomWalk
