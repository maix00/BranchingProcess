module

public import Probability.Process.Stable.SmallDeviation.Blocks.Upper

/-!
# Stable scaling of the block upper bound

The finite-block upper estimate is expressed entirely through unit-time
stable-process tube probabilities. This puts it on the same scale as the
return-block lower estimate.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory
open scoped NNReal

/-- The unit-time tube probability is at most the `blocks`-th power of a
unit-time tube widened by the stable scale of one block. -/
theorem IsStableLevyProcess.measure_rationalTube_le_pow_scaledBlock
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (blocks : ℕ) (hblocks : 0 < blocks) (width : ℝ) :
    let scale : ℝ :=
      ((rationalUniformBlockBoundary blocks 1 hblocks : ℝ≥0) : ℝ) ^ (-(1 / α))
    P (rationalHorizonTubeEvent X 1 width) ≤
      P (rationalHorizonTubeEvent X 1 (width * scale)) ^ blocks := by
  have ht : 0 < rationalUniformBlockBoundary blocks 1 hblocks := by
    apply NNReal.coe_pos.mp
    simp only [rationalUniformBlockBoundary, Nat.cast_one]
    have hb : 0 < (blocks : ℝ) := by exact_mod_cast hblocks
    change 0 < (1 : ℝ) / (blocks : ℝ)
    positivity
  have hbound := h.measure_rationalHorizonTube_le_pow_shortHorizon
    blocks hblocks width
  rw [h.rationalTube_timeSpaceScale_inv
    (rationalUniformBlockBoundary blocks 1 hblocks) ht width] at hbound
  exact hbound

end ProbabilityTheory

end
