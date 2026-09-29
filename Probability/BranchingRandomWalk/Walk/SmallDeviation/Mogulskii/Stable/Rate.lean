import Probability.Distributions.Stable.SmallDeviation

/-!
# The normalising factor of Mogulskii's stable small-deviation estimate

The original estimate (Theorem 1 of А. А. Могульский, *Малые уклонения в пространстве траекторий*, ТВП
**XIX**(4), 1974, formula (15), and Лемма 4 there) reads

  `ln P(sₙ(·) ∈ G) ~ C · Hˣₐ(G) · n · L*(x(n)) · x(n)^{-α}`,

where `L*` is the slowly varying function of (3) and `C ∈ (−∞, 0)` is the constant of Лемма 1, which depends
on the law only.  The whole factor multiplying `Hˣₐ(G)` is what this module isolates:

`stableDeviationExponent α μ scale n = n · L*(x(n)) / x(n)^α`.

By (4), `B*(u) = u^α / L*(u)` is the inverse of the stable norming, and `B*(B(n)) ~ n`; a block of `t` steps
of the walk travels the distance `~ B(t)`, so covering the corridor scale `x(n)` takes `B*(x(n))` steps and
`n` steps split into

`n / B*(x(n)) = n · L*(x(n)) / x(n)^α`

blocks.  That is exactly the object below: the number of blocks in the partition of §3 of the paper, and the
factor by which the rate constant `C · Hˣₐ(G)` is scaled.  It is the reciprocal of
`stableSmallDeviationRate`, which the distribution layer stores in the opposite orientation; the two are
related by `stableDeviationExponent_mul_stableSmallDeviationRate`, so a rate statement can be read in either
orientation without changing what it says.
-/

open MeasureTheory

namespace ProbabilityTheory.RandomWalk

open ProbabilityTheory

open ProbabilityTheory

/-- The factor `λₙ = n · L*(x(n)) · x(n)^{-α}` of (15), that is `n` divided by the block length
`B*(x(n)) = x(n)^α / L*(x(n))` of (4): the number of blocks the partition of the path at scale `x(n)`
produces, and the factor by which the rate constant `C · Hˣₐ(G)` of the original estimate is scaled. -/
noncomputable def stableDeviationExponent (α : ℝ) (μ : Measure ℝ) (scale : ℕ → ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) * stableSlowVariation α μ (scale n) / scale n ^ α

/-- The exponent factor is positive along a block scale with a positive slowly varying factor. -/
theorem stableDeviationExponent_pos
    {α : ℝ} {μ : Measure ℝ} {scale : ℕ → ℝ} {n : ℕ}
    (hscale : 0 < scale n) (hn : 0 < n)
    (hvariation : 0 < stableSlowVariation α μ (scale n)) :
    0 < stableDeviationExponent α μ scale n := by
  have hp : 0 < scale n ^ α := Real.rpow_pos_of_pos hscale α
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  rw [stableDeviationExponent]
  exact div_pos (mul_pos hn' hvariation) hp

/-- The exponent factor and the small-deviation rate are reciprocals of each other: the two layers store the
same factor in opposite orientations. -/
theorem stableDeviationExponent_mul_stableSmallDeviationRate
    {α : ℝ} {μ : Measure ℝ} {scale : ℕ → ℝ} {n : ℕ}
    (hscale : 0 < scale n) (hn : (n : ℝ) ≠ 0)
    (hvariation : stableSlowVariation α μ (scale n) ≠ 0) :
    stableDeviationExponent α μ scale n * stableSmallDeviationRate α μ scale n = 1 := by
  have hp : scale n ^ α ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hscale α)
  rw [stableDeviationExponent, stableSmallDeviationRate]
  field_simp

end ProbabilityTheory.RandomWalk
