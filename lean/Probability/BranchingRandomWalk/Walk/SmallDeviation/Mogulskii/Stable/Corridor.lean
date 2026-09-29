import Probability.BranchingRandomWalk.Walk.SmallDeviation.Mogulskii.Stable.Scale
import Probability.BranchingRandomWalk.Walk.SmallDeviation.Mogulskii.BlockScale
import Probability.BranchingRandomWalk.Walk.SmallDeviation.Horizontal
import Probability.BranchingRandomWalk.Walk.Law

/-!
# One-block corridors for the stable Mogulskii route

The one-block step of Mogulskii's stable proof estimates the probability that the increment path stays in a
corridor of normalized width `w` over a block of `stableBlockLength α μ constant a n` steps, which is
`a n ^ α / L* (a n)` steps up to the constant factor `constant`. The small-deviation normalization
`n * L* (a n) / a n ^ α` is what turns a per-block constant into the corridor rate of the theorem.

For `α < 2` the limit process has jumps, so the estimate has to go through the stable Lévy process and the
Skorokhod `J₁` topology; the killed-interval spectral expansion used for the Gaussian case is not available
here and is not used. At `α = 2` the slowly varying factor is the truncated second moment, and the block
length reduces to the diffusive block length with the constant rescaled by that moment, which is the link
by which the Gaussian specialization reuses the diffusive estimates.

The stable-process estimate itself is not proved here: this module fixes the block event, its probability and
the deterministic properties that the partition and two-sided bound arguments consume.
-/

open Filter MeasureTheory Set

namespace ProbabilityTheory.RandomWalk

open Combinatorics.Branching.Walk

/-! ## The block length at `α = 2` -/

/-- At `α = 2` the slowly varying factor of (3) is the truncated second moment, so the stable block length
is the floor of `constant * scale n ^ 2` divided by that moment. -/
@[simp] theorem stableBlockLength_two (μ : Measure ℝ) (constant : ℝ) (scale : ℕ → ℝ) (n : ℕ) :
    stableBlockLength 2 μ constant scale n =
      ⌊constant * scale n ^ 2 / truncatedSecondMoment μ (scale n)⌋₊ := by
  simp [stableBlockLength, stableBlockArgument, stableSlowVariation_two]

/-- At `α = 2`, if the truncated second moment at the scale is the constant `c`, the stable block length is
the diffusive block length with the constant rescaled by `c`. This is the link by which the Gaussian
specialization reuses the diffusive estimates. -/
theorem stableBlockLength_two_of_truncatedSecondMoment_eq (μ : Measure ℝ) {constant c : ℝ}
    {scale : ℕ → ℝ} {n : ℕ} (hc : truncatedSecondMoment μ (scale n) = c) :
    stableBlockLength 2 μ constant scale n = diffusiveBlockLength (constant / c) scale n := by
  rw [stableBlockLength_two, hc, diffusiveBlockLength, div_mul_eq_mul_div]

/-! ## The block corridor events -/

/-- The stable block corridor: the increment path stays in the open corridor of normalized width `width`
with lower offset `a`, over a block of the `stableBlockLength α μ constant normalization n` steps fixed by
the increment law `μ`. -/
def stableBlockTube (μ : Measure ℝ) (α constant a width : ℝ) (normalization : ℕ → ℝ) (n : ℕ) :
    Set (ℕ → ℝ) :=
  {increment |
    InOpenHorizontalTube a width (stableBlockLength α μ constant normalization n) increment}

/-- The closed variant of `stableBlockTube`, used by the upper bounds. -/
def stableClosedBlockTube (μ : Measure ℝ) (α constant a width : ℝ) (normalization : ℕ → ℝ)
    (n : ℕ) : Set (ℕ → ℝ) :=
  {increment |
    InHorizontalTube a width (stableBlockLength α μ constant normalization n) increment}

/-- The probability of the stable block corridor under the i.i.d. increment law. -/
noncomputable def stableBlockCorridorProbability (ν : Measure ℝ)
    (α constant a width : ℝ) (normalization : ℕ → ℝ) (n : ℕ) : ENNReal :=
  independentIncrementLaw ν (stableBlockTube ν α constant a width normalization n)

/-- The closed block corridor is a measurable event. -/
theorem measurableSet_stableClosedBlockTube (μ : Measure ℝ) (α constant a width : ℝ)
    (normalization : ℕ → ℝ) (n : ℕ) :
    MeasurableSet (stableClosedBlockTube μ α constant a width normalization n) :=
  measurableSet_inHorizontalTube a width _

/-- The narrower open corridor is contained in the wider one with the same offset. This is the
monotonicity the two-sided bound of the theorem uses when comparing `f + ε`, `g - ε` with `f`, `g`. -/
theorem stableBlockTube_mono_width (μ : Measure ℝ) {α constant a w w' : ℝ}
    {normalization : ℕ → ℝ} {n : ℕ} (ha0 : 0 < a) (ha1 : a < 1) (hww : w' < w) :
    stableBlockTube μ α constant a w' normalization n ⊆
      stableBlockTube μ α constant a w normalization n := by
  intro increment h k
  have hk := h k
  exact ⟨by nlinarith [hk.1], by nlinarith [hk.2]⟩

/-- Monotonicity of the block corridor probability in the corridor width. -/
theorem stableBlockCorridorProbability_mono_width (ν : Measure ℝ)
    {α constant a w w' : ℝ} {normalization : ℕ → ℝ} {n : ℕ}
    (ha0 : 0 < a) (ha1 : a < 1) (hww : w' < w) :
    stableBlockCorridorProbability ν α constant a w' normalization n ≤
      stableBlockCorridorProbability ν α constant a w normalization n :=
  measure_mono (stableBlockTube_mono_width ν ha0 ha1 hww)

end ProbabilityTheory.RandomWalk
