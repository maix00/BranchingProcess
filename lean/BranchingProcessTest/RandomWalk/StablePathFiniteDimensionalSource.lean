import Probability.Process.RandomWalk.FunctionalLimit.Stable.PathFiniteDimensionalSource

open Filter MeasureTheory ProbabilityTheory
open ProbabilityTheory.RandomWalk.FunctionalLimit.Stable
open scoped Topology

example {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {α : ℝ} {normalization center : ℕ → ℝ}
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization center)
    (hStable : IsStrictlyAlphaStable α μ)
    (blocks : ℕ) (grid : Fin (blocks + 1) → unitInterval)
    (hgrid : StrictMono grid)
    (hcenter : ∀ j : Fin blocks,
      Tendsto (fun n : ℕ => center
        (⌊(n : ℝ) * (grid j.succ : ℝ)⌋₊ -
          ⌊(n : ℝ) * (grid j.castSucc : ℝ)⌋₊) / normalization n)
        atTop (𝓝 0)) :
    TendstoInDistribution
      (fun n (increments : ℕ → ℝ) (j : Fin blocks) =>
        AdditivePath.blockSum (AdditivePath.blockStart
          (unitIntervalGridBlockLength grid n) j.val)
          (unitIntervalGridBlockLength grid n j.val) increments / normalization n)
      atTop id
      (fun _ => iidSequenceLaw ν)
      (stableTimeLawProductProbability (μ := μ) α grid :
        Measure (Fin blocks → ℝ)) := by
  exact tendstoInDistribution_normalizedStepPath_finiteGrid_increments_of_stableDomain
    hDOA hStable blocks grid hgrid hcenter

#print axioms ProbabilityTheory.RandomWalk.FunctionalLimit.Stable.tendstoInDistribution_normalizedStepPath_finiteGrid_increments_of_stableDomain
