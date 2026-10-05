import Probability.Process.RandomWalk.Path.Truncation.Maximal

open MeasureTheory ProbabilityTheory
open ProbabilityTheory.RandomWalk
open scoped NNReal

example (ν : Measure ℝ) [IsProbabilityMeasure ν] (radius : ℝ) :
    Integrable (fun x : ℝ =>
      ProbabilityTheory.RandomWalk.truncatedIncrement radius x ^ 37) ν :=
  ProbabilityTheory.RandomWalk.integrable_truncatedIncrement_pow ν radius 37

example (ν : Measure ℝ) [IsProbabilityMeasure ν] (radius : ℝ) :
    MemLp (ProbabilityTheory.RandomWalk.centeredTruncatedIncrement ν radius) 4 ν :=
  ProbabilityTheory.RandomWalk.memLp_centeredTruncatedIncrement_four ν radius

example (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {radius : ℝ} (hradius : 0 ≤ radius) :
    (∫ x, ProbabilityTheory.RandomWalk.centeredTruncatedIncrement ν radius x ^ 4 ∂ν) ≤
      8 * (radius ^ 2 *
        ∫ x, ProbabilityTheory.RandomWalk.truncatedIncrement radius x ^ 2 ∂ν +
        ProbabilityTheory.RandomWalk.truncatedIncrementMean ν radius ^ 4) :=
  ProbabilityTheory.RandomWalk.integral_centeredTruncatedIncrement_pow_four_le
    ν hradius

example (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {radius : ℝ} (hradius : 0 ≤ radius) (start : ℕ)
    (ε : ℝ≥0) (n : ℕ) :
    ε * (ProbabilityTheory.iidSequenceLaw
        (ν.map (ProbabilityTheory.RandomWalk.centeredTruncatedIncrement ν radius))) {path |
      (ε : ℝ) ≤
        (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
          fun k => (AdditivePath.blockSum start (k + 1) path) ^ 4} ≤
      ENNReal.ofReal
        (ProbabilityTheory.RandomWalk.truncatedCenteredFourthNumerator ν radius n) :=
  ProbabilityTheory.RandomWalk.maximal_ineq_pow_four_blockSum_centeredTruncated_bounded
    ν hradius start ε n

example (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {radius threshold : ℝ} (hradius : 0 ≤ radius)
    (blocks length : ℕ)
    (hgap : ((length + 1 : ℕ) : ℝ) *
        |ProbabilityTheory.RandomWalk.truncatedIncrementMean ν radius| < threshold) :
    (ProbabilityTheory.iidSequenceLaw ν) {path |
      ∃ j < blocks, ∃ k ∈ Finset.range (length + 1),
        threshold ≤ |AdditivePath.blockSum (j * length) (k + 1) path|} ≤
      ((blocks * length + 1 : ℕ) * ν {x | radius < |x|}) +
        (blocks : ℕ) * ProbabilityTheory.RandomWalk.truncatedCenteredFourthBound
          ν radius length
          (threshold - ((length + 1 : ℕ) : ℝ) *
            |ProbabilityTheory.RandomWalk.truncatedIncrementMean ν radius|) :=
  ProbabilityTheory.RandomWalk.measure_exists_block_exists_abs_ge_le_of_truncation_bounded
    ν hradius blocks length hgap

#print axioms ProbabilityTheory.RandomWalk.integrable_truncatedIncrement_pow
#print axioms ProbabilityTheory.RandomWalk.integrable_centeredTruncatedIncrement_pow_four
#print axioms ProbabilityTheory.RandomWalk.integral_partialSum_pow_four_centeredTruncated_le
#print axioms ProbabilityTheory.RandomWalk.maximal_ineq_pow_four_blockSum_centeredTruncated_bounded
#print axioms ProbabilityTheory.RandomWalk.measure_exists_block_exists_abs_ge_le_of_truncation_bounded
