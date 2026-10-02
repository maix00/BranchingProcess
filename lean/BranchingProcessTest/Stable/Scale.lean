import Probability.BranchingRandomWalk.Walk.SmallDeviation.Mogulskii.Stable.Partition

open Filter MeasureTheory ProbabilityTheory
open ProbabilityTheory.RandomWalk
open scoped Topology

example {α : ℝ} {μ : Measure ℝ} {τ K : ℝ} {a : ℕ → ℝ}
    (hα : 0 < α) (hτ : 0 < τ) (hK : 0 < K)
    (ha : Tendsto a atTop atTop)
    (hL : ∀ᶠ n in atTop,
      0 < stableSlowVariation α μ (a n) ∧ stableSlowVariation α μ (a n) ≤ K)
    (hrate : Tendsto (stableSmallDeviationRate α μ a) atTop (nhds 0)) :
    Tendsto
      (fun n => stableScaleTime α μ (a n) / (n : ℝ) *
        (stableBlockCount α μ τ a n : ℝ))
      atTop (nhds τ⁻¹) :=
  tendsto_stableScaleTime_div_nat_mul_stableBlockCount
    hα hτ hK ha hL hrate

#print axioms ProbabilityTheory.RandomWalk.tendsto_stableBlockLength_div_stableScaleTime
#print axioms ProbabilityTheory.RandomWalk.tendsto_stableScaleTime_div_nat_mul_stableBlockCount
