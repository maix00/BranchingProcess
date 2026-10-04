import Probability.Distributions.DomainOfAttraction.Block
import Algebra.BigOperators.AdditivePath

open Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators

/-- The stable-domain block endpoint interface is directly callable with a
general centering sequence; the limiting shift is the limit of the scaled
centering term. -/
example {ν limit : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure limit]
    {normalization center : ℕ → ℝ}
    (h : IsInDomainOfAttractionAlong ν limit normalization center)
    (blockLength : ℕ → ℕ) (spatialScale : ℕ → ℝ) {r c : ℝ}
    (hblock : Tendsto blockLength atTop atTop)
    (hspatial : ∀ᶠ n in atTop, spatialScale n ≠ 0)
    (hratio : Tendsto
      (fun n => normalization (blockLength n) / spatialScale n)
      atTop (nhds r))
    (hcenter : Tendsto
      (fun n => center (blockLength n) / spatialScale n)
      atTop (nhds c)) :
    TendstoInDistribution
      (fun n (increments : ℕ → ℝ) =>
        AdditivePath.displacement (blockLength n) increments / spatialScale n)
      atTop (fun x => r * x + c)
      (fun _ => iidSequenceLaw ν) limit :=
  h.tendstoInDistribution_partialSum_div blockLength spatialScale
    hblock hspatial hratio hcenter

#print axioms
  ProbabilityTheory.IsInDomainOfAttractionAlong.tendstoInDistribution_partialSum_div

example (n : ℕ) (increments : ℕ → ℝ) :
    AdditivePath.displacement n increments =
      ∑ k ∈ Finset.range n, increments k := rfl
