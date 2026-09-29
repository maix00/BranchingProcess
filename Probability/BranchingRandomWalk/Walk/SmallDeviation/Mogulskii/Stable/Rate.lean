import Probability.BranchingRandomWalk.Walk.SmallDeviation.Mogulskii.Stable.Partition

/-!
# The factor that scales the stable exponent, and the block length it implies

The stable route of the original statement (Могульский, ТВП XIX(4), 1974, (15) and Лемма 4 I) reads

  `ln P(sₙ(·) ∈ G) ~ C · H^a_x(G) · n · x(n)^{-a} · L*(x(n))`,

where `L*` is the slowly varying function of (3) and the constant `C` is the one of Лемма 1 I, namely the
limit `a^α · ln P(ξ(·) ∈ a𝔘) → C` as `a ↓ 0` of the unit tube `𝔘` of the stable process. This module collects
the two objects that carries that normalisation.

* `stableDeviationExponent` is the factor `n · L*(x(n)) · x(n)^{-a}` multiplying the constant and the
  functional. It is the reciprocal of `stableSmallDeviationRate`, which stores `x(n)^a / (n · L*(x(n)))`. Both
  are named here so that a statement can say which of the two it scales by.
* `stableBlockLengthInSteps` is the block length the partition works with. By (4), `B*(u) = u^a / L*(u)` and
  `B*(B(n)) ↝ n`, so travelling the distance `scale n` takes `scale n^a / L*(scale n)` steps and the block
  count is asymptotic to `stableDeviationExponent α μ scale n` divided by the fixed constant. The slowly
  varying factor belongs to the block length: `L*` tends to a constant depending on the law, so leaving it
  out rescales the exponent by that constant.

The predicate `IsStableEscapeRate` records the paper's definition of `C` without asserting that the limit
exists, which is the content of Лемма 1.
-/

open Filter MeasureTheory
open scoped Topology

namespace ProbabilityTheory.RandomWalk

/-- The paper's constant `C` of Лемма 1 I, stated for an abstract tube probability: it is the limit
`a^α · log P(ξ(·) ∈ a𝔘) → C` as `a ↓ 0` along the tube `𝔘` of the stable process. -/
def IsStableEscapeRate (α C : ℝ) (tubeProbability : ℝ → ℝ) : Prop :=
  Tendsto (fun a => a ^ α * Real.log (tubeProbability a)) (𝓝[>] (0 : ℝ)) (𝓝 C)

/-- The factor `n · L*(x(n)) · x(n)^{-a}` by which (15) scales the constant and the functional, the
reciprocal of `stableSmallDeviationRate`. -/
noncomputable def stableDeviationExponent
    (α : ℝ) (μ : Measure ℝ) (scale : ℕ → ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) * stableSlowVariation α μ (scale n) / scale n ^ α

/-- `stableSmallDeviationRate` is the reciprocal of the factor by which (15) scales the constant and the
functional. -/
theorem stableDeviationExponent_mul_stableSmallDeviationRate
    (α : ℝ) (μ : Measure ℝ) (scale : ℕ → ℝ) (n : ℕ)
    (hn : (n : ℝ) ≠ 0) (hpow : scale n ^ α ≠ 0)
    (hslow : stableSlowVariation α μ (scale n) ≠ 0) :
    stableDeviationExponent α μ scale n * stableSmallDeviationRate α μ scale n = 1 := by
  rw [stableDeviationExponent, stableSmallDeviationRate]
  field_simp

/-- The block length of the stable partition, in steps: by (4) a block travelling the distance `scale n`
needs `scale n ^ α / L*(scale n)` steps. -/
noncomputable def stableBlockLengthInSteps
    (α : ℝ) (μ : Measure ℝ) (constant : ℝ) (scale : ℕ → ℝ) (n : ℕ) : ℝ :=
  constant * scale n ^ α / stableSlowVariation α μ (scale n)

/-- The block length is the fixed constant times `n` times the reciprocal of the factor (15) scales by, so
the block count `n / (block length)` is asymptotic to `stableDeviationExponent α μ scale n / constant`. -/
theorem stableBlockLengthInSteps_eq_mul_stableSmallDeviationRate
    (α : ℝ) (μ : Measure ℝ) (constant : ℝ) (scale : ℕ → ℝ) (n : ℕ)
    (hn : (n : ℝ) ≠ 0) (hslow : stableSlowVariation α μ (scale n) ≠ 0) :
    stableBlockLengthInSteps α μ constant scale n =
      constant * (n : ℝ) * stableSmallDeviationRate α μ scale n := by
  rw [stableBlockLengthInSteps, stableSmallDeviationRate]
  field_simp

end ProbabilityTheory.RandomWalk
