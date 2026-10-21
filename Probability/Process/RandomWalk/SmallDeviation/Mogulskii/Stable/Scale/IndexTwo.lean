/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Distributions.Moments.Truncated.Basic
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Scale.BlockScale
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Scale.Core

/-!
# Index-two stable block lengths

At stable index $\alpha=2$, the slowly varying factor in the block length is
the truncated second moment $V(x)=\int_{|y|\le x} y^2\,d\nu(y)$. Thus
`stableBlockLength 2 ν c scale n` is the floor of
$c\,\mathrm{scale}(n)^2/V(\mathrm{scale}(n))$. If this truncated moment equals
$v$ at the chosen scale, the block length is exactly the diffusive block
length with parameter $c/v$.

The second identity is a scale bridge used by the branching first-stage
estimate; it requires only the stated pointwise identity for the truncated
second moment.

The source scale is A. A. Mogul'skii, “Small deviations in the sample
function space,” *Teoriya Veroyatnostei i ee Primeneniya* 19(4) (1974),
755--765; English translation, “Small Deviations in a Space of Trajectories,”
*Theory of Probability and Its Applications* 19(4) (1975), 726--736,
DOI 10.1137/1119081, Theorem 3, Section 4.

The public declarations are:

- `stableBlockLength_two`: the index-two block-length formula using the
  truncated second moment.
- `stableBlockLength_two_of_truncatedSecondMoment_eq`: equality with the
  diffusive block length when the truncated second moment has a specified
  value.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii

/-- At `α = 2`, the slowly varying factor is the truncated second moment, so
the stable block length is the floor of `constant * scale n ^ 2` divided by
that moment. -/
@[simp] theorem stableBlockLength_two (ν : Measure ℝ) (constant : ℝ)
    (scale : ℕ → ℝ) (n : ℕ) :
    stableBlockLength 2 ν constant scale n =
      ⌊constant * scale n ^ 2 / truncatedSecondMoment ν (scale n)⌋₊ := by
  simp [stableBlockLength, stableBlockArgument, stableSlowVariation_two]

/-- At `α = 2`, if the truncated second moment at the scale is `c`, then the
stable block length is the diffusive block length with parameter
`constant / c`. -/
theorem stableBlockLength_two_of_truncatedSecondMoment_eq (ν : Measure ℝ)
    {constant c : ℝ} {scale : ℕ → ℝ} {n : ℕ}
    (hc : truncatedSecondMoment ν (scale n) = c) :
    stableBlockLength 2 ν constant scale n =
      diffusiveBlockLength (constant / c) scale n := by
  rw [stableBlockLength_two, hc, diffusiveBlockLength, div_mul_eq_mul_div]

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii
