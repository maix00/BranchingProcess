import Probability.Distributions.DomainOfAttraction.CharacteristicFunction

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

example (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (scale center : ℕ → ℝ) (n : ℕ) :
    Measurable (normalizedIidSum scale center n) :=
  normalizedIidSum_measurable scale center n

example (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (scale center : ℕ → ℝ) (n : ℕ) (t : ℝ) :
    charFun ((iidSequenceLaw ν).map (normalizedIidSum scale center n)) t =
      (charFun ν ((scale n)⁻¹ * t)) ^ n *
        Complex.exp (inner ℝ (-((scale n)⁻¹ * center n)) t * Complex.I) :=
  charFun_map_normalizedIidSum scale center n t
