/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.BlockScale
public import Probability.Process.RandomWalk.FunctionalLimit.Donsker.Tightness.Maximal

/-!
# Within-block tightness estimates

Diffusive blocks have length asymptotic to `constant * scale n ^ 2`.
Combining this with the block maximal inequality controls oscillations on the
same spatial scale.  Sending the block constant to zero is the tightness step
used in corridor approximation.
-/

open Filter MeasureTheory ProbabilityTheory Topology

@[expose] public section

namespace ProbabilityTheory.RandomWalk

open _root_.ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii


/-- The explicit maximal-inequality bound for a diffusive block converges to
`constant / radiusFactor²`.  The extra increment in the finite maximum is
asymptotically negligible. -/
theorem _root_.ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.IsMogulskiiScale.tendsto_succ_diffusiveBlockLength_div_scaledRadius_sq
    {scale : ℕ → ℝ} (hscale : IsMogulskiiScale scale)
    {constant radiusFactor : ℝ} (hconstant : 0 < constant)
    (hradiusFactor : 0 < radiusFactor) :
    Tendsto (fun n =>
        (diffusiveBlockLength constant scale n + 1 : ℕ) /
          (radiusFactor * scale n) ^ 2)
      atTop (nhds (constant / radiusFactor ^ 2)) := by
  have hinv : Tendsto (fun n => (scale n)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp
      (Asymptotics.IsSmallDeviationScale.tendsto_atTop hscale)
  have hinvSq : Tendsto (fun n => (scale n)⁻¹ ^ 2) atTop (nhds 0) := by
    simpa using hinv.pow 2
  have honeDiv : Tendsto (fun n => 1 / scale n ^ 2) atTop (nhds 0) := by
    convert hinvSq using 1
    funext n
    field_simp
  have hadd :=
    (_root_.ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.IsMogulskiiScale.tendsto_diffusiveBlockLength_div_sq hscale hconstant).add honeDiv
  have hdiv := hadd.div_const (radiusFactor ^ 2)
  convert hdiv using 1
  · funext n
    push_cast
    field_simp [hradiusFactor.ne']
  · simp

/-- At every scale where the spatial normalization is positive, the
probability of an oscillation by `radiusFactor * scale n` during one
diffusive block is bounded by the explicit ratio whose limit is computed
above. -/
theorem measure_diffusiveBlockMaximum_le
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : IsCenteredUnitSecondMoment ν)
    {scale : ℕ → ℝ} {constant radiusFactor : ℝ}
    (hradiusFactor : 0 < radiusFactor) (start n : ℕ)
    (hscalePos : 0 < scale n) :
    (iidSequenceLaw ν) {path |
        ∃ k ∈ Finset.range (diffusiveBlockLength constant scale n + 1),
          radiusFactor * scale n ≤
            |AdditivePath.blockSum start (k + 1) path|} ≤
      ENNReal.ofReal
        ((diffusiveBlockLength constant scale n + 1 : ℕ) /
          (radiusFactor * scale n) ^ 2) := by
  simpa [Nat.cast_add, Nat.cast_one] using
    measure_exists_abs_blockSum_ge_le ν hν start
      (mul_pos hradiusFactor hscalePos)
      (diffusiveBlockLength constant scale n)

/-- The diffusive-block oscillation bound is eventually uniform over the
block's deterministic starting coordinate. -/
theorem eventually_measure_diffusiveBlockMaximum_le
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : IsCenteredUnitSecondMoment ν)
    {scale : ℕ → ℝ} (hscale : IsMogulskiiScale scale)
    {constant radiusFactor error : ℝ}
    (hconstant : 0 < constant) (hradiusFactor : 0 < radiusFactor)
    (herror : 0 < error) :
    ∀ᶠ n in atTop, ∀ start : ℕ,
      (iidSequenceLaw ν) {path |
          ∃ k ∈ Finset.range (diffusiveBlockLength constant scale n + 1),
            radiusFactor * scale n ≤
              |AdditivePath.blockSum start (k + 1) path|} ≤
        ENNReal.ofReal (constant / radiusFactor ^ 2 + error) := by
  have hratio :=
    _root_.ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.IsMogulskiiScale.tendsto_succ_diffusiveBlockLength_div_scaledRadius_sq hscale
      hconstant hradiusFactor
  have hratioUpper : ∀ᶠ n in atTop,
      (diffusiveBlockLength constant scale n + 1 : ℕ) /
          (radiusFactor * scale n) ^ 2 <
        constant / radiusFactor ^ 2 + error :=
    hratio.eventually
      (Iio_mem_nhds (lt_add_of_pos_right _ herror))
  filter_upwards [_root_.ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.IsMogulskiiScale.eventually_pos hscale, hratioUpper]
    with n hscalePos hn start
  exact (measure_diffusiveBlockMaximum_le ν hν hradiusFactor start n
    hscalePos).trans (ENNReal.ofReal_le_ofReal hn.le)

/-- Quantitative within-block tightness: for every positive spatial fraction
and probability tolerance, one can choose a positive diffusive block constant
so that all sufficiently large scales, uniformly over deterministic block
starts, have oscillation probability at most that tolerance. -/
theorem exists_diffusiveBlockConstant_eventually_measure_max_le
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : IsCenteredUnitSecondMoment ν)
    {scale : ℕ → ℝ} (hscale : IsMogulskiiScale scale)
    {radiusFactor tolerance : ℝ}
    (hradiusFactor : 0 < radiusFactor) (htolerance : 0 < tolerance) :
    ∃ constant > 0, ∀ᶠ n in atTop, ∀ start : ℕ,
      (iidSequenceLaw ν) {path |
          ∃ k ∈ Finset.range (diffusiveBlockLength constant scale n + 1),
            radiusFactor * scale n ≤
              |AdditivePath.blockSum start (k + 1) path|} ≤
        ENNReal.ofReal tolerance := by
  let constant := tolerance * radiusFactor ^ 2 / 2
  have hconstant : 0 < constant := by
    dsimp [constant]
    positivity
  refine ⟨constant, hconstant, ?_⟩
  have h := eventually_measure_diffusiveBlockMaximum_le ν hν hscale
    hconstant hradiusFactor (half_pos htolerance)
  have hbound : constant / radiusFactor ^ 2 + tolerance / 2 = tolerance := by
    dsimp [constant]
    field_simp [hradiusFactor.ne']
    ring
  simpa [hbound] using h

end ProbabilityTheory.RandomWalk
