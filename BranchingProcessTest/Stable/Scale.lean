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

example {α : ℝ} {μ : Measure ℝ} {b a : ℕ → ℝ} {τ ell : ℝ}
    (hα : 0 < α) (hτ : 0 < τ) (hell : 0 < ell)
    (ha : Tendsto a atTop atTop)
    (hL : Tendsto (stableSlowVariation α μ) atTop (nhds ell))
    (hb : IsStableNorming α μ b) :
    Tendsto (fun n => b (stableBlockLength α μ τ a n) / a n)
      atTop (nhds (τ ^ (1 / α))) :=
  tendsto_stableBlockNorming_div_scale_of_slowVariation_limit
    hα hτ hell ha hL hb

#print axioms ProbabilityTheory.RandomWalk.tendsto_stableBlockNorming_div_scale_of_slowVariation_limit

example {α ell : ℝ} {μ : Measure ℝ} {b a : ℕ → ℝ}
    (hα : 0 < α) (hell : 0 < ell)
    (hscale : IsStableMogulskiiScale α μ b a)
    (hL : Tendsto (stableSlowVariation α μ) atTop (nhds ell)) :
    Tendsto (stableSmallDeviationRate α μ a) atTop (nhds 0) :=
  IsStableMogulskiiScale.tendsto_stableSmallDeviationRate_zero_of_slowVariation_limit
    hα hell hscale hL

example {α ell : ℝ} {μ : Measure ℝ} {b a : ℕ → ℝ} {τ : ℝ}
    (hα : 0 < α) (hτ : 0 < τ) (hell : 0 < ell)
    (hscale : IsStableMogulskiiScale α μ b a)
    (hL : Tendsto (stableSlowVariation α μ) atTop (nhds ell)) :
    Tendsto (fun n => stableScaleTime α μ (a n) / (n : ℝ) *
      (stableBlockCount α μ τ a n : ℝ)) atTop (nhds τ⁻¹) :=
  tendsto_stableScaleTime_div_nat_mul_stableBlockCount_of_slowVariation_limit
    hα hτ hell hscale hL

#print axioms ProbabilityTheory.RandomWalk.IsStableMogulskiiScale.tendsto_stableSmallDeviationRate_zero_of_slowVariation_limit
#print axioms ProbabilityTheory.RandomWalk.tendsto_stableScaleTime_div_nat_mul_stableBlockCount_of_slowVariation_limit
