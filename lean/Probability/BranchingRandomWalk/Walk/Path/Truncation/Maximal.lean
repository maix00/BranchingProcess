import Probability.BranchingRandomWalk.Walk.Path.Block.Maximal.Fourth
import Probability.BranchingRandomWalk.Walk.Path.Truncation.Moment

/-!
# Maximal bounds for truncated increments

The fourth-power block maximal inequality is combined here with the moment
bounds for centered hard truncations.  All quantities on the right are
moments of the original increment law.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace ProbabilityTheory.BranchingRandomWalk.RandomWalk

open Combinatorics.Branching.Walk

/-- Fourth-power maximal estimate for a block of centered hard-truncated IID
increments. -/
theorem maximal_ineq_pow_four_blockSum_centeredTruncated
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsq : Integrable (fun x : ℝ => x ^ 2) ν)
    {radius : ℝ} (hradius : 0 ≤ radius)
    (start : ℕ) (ε : ℝ≥0) (n : ℕ) :
    ε * (iidSequenceLaw
        (ν.map (centeredTruncatedIncrement ν radius))) {path |
      (ε : ℝ) ≤
        (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
          fun k => (blockSum start (k + 1) path) ^ 4} ≤
      ENNReal.ofReal
        (((n + 1 : ℕ) : ℝ) *
            (8 * (radius ^ 2 * ∫ x, x ^ 2 ∂ν +
              truncatedIncrementMean ν radius ^ 4)) +
          3 * (((n + 1 : ℕ) : ℝ) ^ 2) *
            (∫ x, x ^ 2 ∂ν) ^ 2) := by
  let f := centeredTruncatedIncrement ν radius
  have hf : Measurable f := measurable_centeredTruncatedIncrement ν radius
  have hmem4Source : MemLp f 4 ν :=
    memLp_centeredTruncatedIncrement_four ν hsq hradius
  have hmem4Map : MemLp id 4 (ν.map f) := by
    rw [memLp_map_measure_iff stronglyMeasurable_id.aestronglyMeasurable
      hf.aemeasurable]
    simpa [Function.comp_def, id] using hmem4Source
  have hcenteredMap : ∫ x, x ∂ν.map f = 0 := by
    calc
      (∫ x, x ∂ν.map f) = ∫ x, f x ∂ν := by
        simpa using integral_map (μ := ν) (φ := f)
          hf.aemeasurable measurable_id.aestronglyMeasurable
      _ = 0 := integral_centeredTruncatedIncrement_of_integrable_sq
        ν hsq radius
  have hraw := maximal_ineq_pow_four_blockSum_iidSequenceLaw
    (ν.map f) hmem4Map hcenteredMap start ε n
  refine hraw.trans ?_
  apply ENNReal.ofReal_le_ofReal
  have hfour : (∫ x, x ^ 4 ∂ν.map f) = ∫ x, f x ^ 4 ∂ν := by
    simpa using integral_map (μ := ν) (φ := f)
      hf.aemeasurable (measurable_id.pow_const 4).aestronglyMeasurable
  have htwo : (∫ x, x ^ 2 ∂ν.map f) = ∫ x, f x ^ 2 ∂ν := by
    simpa using integral_map (μ := ν) (φ := f)
      hf.aemeasurable (measurable_id.pow_const 2).aestronglyMeasurable
  rw [hfour, htwo]
  have hfourLe :=
    integral_centeredTruncatedIncrement_pow_four_le_mean ν hsq hradius
  have htwoLe := integral_centeredTruncatedIncrement_sq_le ν hsq radius
  have hn : 0 ≤ (((n + 1 : ℕ) : ℝ)) := by positivity
  have htwoNonneg : 0 ≤ ∫ x, f x ^ 2 ∂ν :=
    integral_nonneg fun x => sq_nonneg _
  have htwoSq : (∫ x, f x ^ 2 ∂ν) ^ 2 ≤
      (∫ x, x ^ 2 ∂ν) ^ 2 :=
    pow_le_pow_left₀ htwoNonneg htwoLe 2
  nlinarith

end ProbabilityTheory.BranchingRandomWalk.RandomWalk
