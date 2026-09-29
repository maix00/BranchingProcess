import Probability.BranchingRandomWalk.Walk.Path.Block.Maximal
import Probability.BranchingRandomWalk.Walk.SmallDeviation.Mogulskii.Assumptions

/-!
# Maximal bounds under the Mogulskii moment assumptions

The abstract block maximal inequality is specialized here to centered
unit-second-moment increments.  This is the quantitative input used to control
within-block oscillations in corridor approximations.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace ProbabilityTheory.RandomWalk

open Combinatorics.Branching.Walk

/-- Under the centered unit-second-moment assumptions, every deterministic
increment block satisfies the same squared maximal estimate. -/
theorem maximal_ineq_sq_blockSum_of_centeredUnitSecondMoment
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : IsCenteredUnitSecondMoment ν)
    (start : ℕ) (ε : ℝ≥0) (n : ℕ) :
    ε * (iidSequenceLaw ν) {path | (ε : ℝ) ≤
        (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
          fun k => (blockSum start (k + 1) path) ^ 2} ≤
      ENNReal.ofReal (n + 1 : ℝ) := by
  have hvariance : variance id ν = 1 := by
    rw [variance_of_integral_eq_zero measurable_id.aemeasurable
      (by simpa [id] using hν.1)]
    simpa [id] using hν.2
  simpa [hvariance] using
    maximal_ineq_sq_blockSum_iidSequenceLaw ν hν.memLp_two hν.1
      start ε n

/-- Probability form of the block maximal estimate: during `n + 1` exposed
increments, exceeding a positive radius has probability at most
`(n + 1) / radius²`. -/
theorem measure_sq_le_blockMaximum_le
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : IsCenteredUnitSecondMoment ν)
    (start : ℕ) {radius : ℝ} (hradius : 0 < radius) (n : ℕ) :
    (iidSequenceLaw ν) {path | radius ^ 2 ≤
        (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
          fun k => (blockSum start (k + 1) path) ^ 2} ≤
      ENNReal.ofReal ((n + 1 : ℝ) / radius ^ 2) := by
  let ε : ℝ≥0 := ⟨radius ^ 2, sq_nonneg radius⟩
  have hmax := maximal_ineq_sq_blockSum_of_centeredUnitSecondMoment
    ν hν start ε n
  rw [ENNReal.ofReal_div_of_pos (sq_pos_of_pos hradius)]
  apply (ENNReal.le_div_iff_mul_le
    (Or.inl (ENNReal.ofReal_pos.mpr (sq_pos_of_pos hradius)).ne')
    (Or.inl ENNReal.ofReal_ne_top)).2
  rw [mul_comm]
  have hε : (ε : ENNReal) = ENNReal.ofReal (radius ^ 2) := by
    rw [ENNReal.coe_nnreal_eq]
    rfl
  rw [← hε]
  change (ε : ENNReal) * (iidSequenceLaw ν) {path | (ε : ℝ) ≤
      (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
        fun k => (blockSum start (k + 1) path) ^ 2} ≤
    ENNReal.ofReal (n + 1 : ℝ)
  exact hmax

/-- Equivalent absolute-value formulation of the block maximal estimate. -/
theorem measure_exists_abs_blockSum_ge_le
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : IsCenteredUnitSecondMoment ν)
    (start : ℕ) {radius : ℝ} (hradius : 0 < radius) (n : ℕ) :
    (iidSequenceLaw ν) {path |
        ∃ k ∈ Finset.range (n + 1),
          radius ≤ |blockSum start (k + 1) path|} ≤
      ENNReal.ofReal ((n + 1 : ℝ) / radius ^ 2) := by
  have hevent :
      {path : ℕ → ℝ | radius ^ 2 ≤
          (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
            fun k => (blockSum start (k + 1) path) ^ 2} =
        {path | ∃ k ∈ Finset.range (n + 1),
          radius ≤ |blockSum start (k + 1) path|} := by
    ext path
    simp only [Set.mem_ofPred_eq, Finset.le_sup'_iff]
    constructor
    · rintro ⟨k, hk, hkbound⟩
      exact ⟨k, hk, by
        rw [← abs_of_pos hradius, ← sq_le_sq]
        exact hkbound⟩
    · rintro ⟨k, hk, hkbound⟩
      exact ⟨k, hk, by
        rw [sq_le_sq, abs_of_pos hradius]
        exact hkbound⟩
  rw [← hevent]
  exact measure_sq_le_blockMaximum_le ν hν start hradius n

end ProbabilityTheory.RandomWalk
