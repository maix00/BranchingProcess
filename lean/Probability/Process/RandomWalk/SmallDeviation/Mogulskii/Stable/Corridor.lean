/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Scale
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.BlockScale
public import Probability.Process.RandomWalk.Path.Corridor.Horizontal
public import Probability.Process.RandomWalk.Law

/-!
# One-block corridors for the stable Mogulskii route

The one-block step of Mogulskii's stable proof estimates the probability that the increment path stays in a
corridor of normalized width `w` over a block of `stableBlockLength α ν constant a n` steps, which is
`a n ^ α / L* (a n)` steps up to the constant factor `constant`. The small-deviation scale
`n * L* (a n) / a n ^ α` is what turns a per-block constant into the corridor rate of the theorem.

For `α < 2` the limit process has jumps, so the estimate has to go through the stable Lévy process and the
Skorokhod `J₁` topology; the killed-interval spectral expansion used for the Gaussian case is not available
here and is not used. At `α = 2` the slowly varying factor is the truncated second moment, and the block
length reduces to the diffusive block length with the constant rescaled by that moment, which is the link
by which the Gaussian specialization reuses the diffusive estimates.

The stable-process estimate itself is not proved here: this module fixes the block event, its probability and
the deterministic properties that the partition and two-sided bound arguments consume.
-/

@[expose] public section

open Filter MeasureTheory Set

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii



/-! ## The block length at `α = 2` -/

/-- At `α = 2` the slowly varying factor of (3) is the truncated second moment, so the stable block length
is the floor of `constant * scale n ^ 2` divided by that moment. -/
@[simp] theorem stableBlockLength_two (ν : Measure ℝ) (constant : ℝ) (scale : ℕ → ℝ) (n : ℕ) :
    stableBlockLength 2 ν constant scale n =
      ⌊constant * scale n ^ 2 / truncatedSecondMoment ν (scale n)⌋₊ := by
  simp [stableBlockLength, stableBlockArgument, stableSlowVariation_two]

/-- At `α = 2`, if the truncated second moment at the scale is the constant `c`, the stable block length is
the diffusive block length with the constant rescaled by `c`. This is the link by which the Gaussian
specialization reuses the diffusive estimates. -/
theorem stableBlockLength_two_of_truncatedSecondMoment_eq (ν : Measure ℝ) {constant c : ℝ}
    {scale : ℕ → ℝ} {n : ℕ} (hc : truncatedSecondMoment ν (scale n) = c) :
    stableBlockLength 2 ν constant scale n = diffusiveBlockLength (constant / c) scale n := by
  rw [stableBlockLength_two, hc, diffusiveBlockLength, div_mul_eq_mul_div]

/-! ## The block corridor events -/

/-- The stable block corridor: the increment path stays in the open corridor of normalized width `width`
with lower offset `a`, over a block of the `stableBlockLength α ν constant scale n` steps fixed by
the increment law `ν`. -/
def stableBlockTube (ν : Measure ℝ) (α constant a width : ℝ) (scale : ℕ → ℝ) (n : ℕ) :
    Set (ℕ → ℝ) :=
  {increment |
    InOpenHorizontalTube a width (stableBlockLength α ν constant scale n) increment}

/-- The closed variant of `stableBlockTube`, used by the upper bounds. -/
def stableClosedBlockTube (ν : Measure ℝ) (α constant a width : ℝ) (scale : ℕ → ℝ)
    (n : ℕ) : Set (ℕ → ℝ) :=
  {increment |
    InHorizontalTube a width (stableBlockLength α ν constant scale n) increment}

/-- The probability of the stable block corridor under the i.i.d. increment law. -/
noncomputable def stableBlockCorridorProbability (ν : Measure ℝ)
    (α constant a width : ℝ) (scale : ℕ → ℝ) (n : ℕ) : ENNReal :=
  independentIncrementLaw ν (stableBlockTube ν α constant a width scale n)

/-- The closed block corridor is a measurable event. -/
theorem measurableSet_stableClosedBlockTube (ν : Measure ℝ) (α constant a width : ℝ)
    (scale : ℕ → ℝ) (n : ℕ) :
    MeasurableSet (stableClosedBlockTube ν α constant a width scale n) :=
  measurableSet_inHorizontalTube a width _

/-- The narrower open corridor is contained in the wider one with the same offset. This is the
monotonicity the two-sided bound of the theorem uses when comparing `f + ε`, `g - ε` with `f`, `g`. -/
theorem stableBlockTube_mono_width (ν : Measure ℝ) {α constant a w w' : ℝ}
    {scale : ℕ → ℝ} {n : ℕ} (ha0 : 0 < a) (ha1 : a < 1) (hww : w' < w) :
    stableBlockTube ν α constant a w' scale n ⊆
      stableBlockTube ν α constant a w scale n := by
  intro increment h k
  have hk := h k
  exact ⟨by nlinarith [hk.1], by nlinarith [hk.2]⟩

/-- Monotonicity of the block corridor probability in the corridor width. -/
theorem stableBlockCorridorProbability_mono_width (ν : Measure ℝ)
    {α constant a w w' : ℝ} {scale : ℕ → ℝ} {n : ℕ}
    (ha0 : 0 < a) (ha1 : a < 1) (hww : w' < w) :
    stableBlockCorridorProbability ν α constant a w' scale n ≤
      stableBlockCorridorProbability ν α constant a w scale n :=
  measure_mono (stableBlockTube_mono_width ν ha0 ha1 hww)

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii
