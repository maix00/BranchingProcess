import Probability.Process.Stable.SmallDeviation.EscapeRate.PathLaw

open MeasureTheory
open scoped NNReal

section

variable {Ω : Type*} [MeasurableSpace Ω]
variable {α : ℝ} {μ : Measure ℝ}
variable {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
variable {X : ℝ≥0 → Ω → ℝ} {Q : Measure Ω} [IsProbabilityMeasure Q]

example (hP : ProbabilityTheory.IsStableClockProcessLaw α μ
      ProbabilityTheory.unitIntervalClock P)
    (hX : ProbabilityTheory.IsStableLevyProcess α μ X Q)
    (hcdf : 0 < ProbabilityTheory.cdf μ 0 ∧
      ProbabilityTheory.cdf μ 0 < 1) :
    ∃ C, ProbabilityTheory.HasStableProcessEscapeRate α μ P C :=
  hP.hasStableProcessEscapeRate_of_isStableLevyProcess hX hcdf

end

#check ProbabilityTheory.IsStableClockProcessLaw.hasStableProcessEscapeRate_of_isStableLevyProcess

#print axioms
  ProbabilityTheory.IsStableClockProcessLaw.hasStableProcessEscapeRate_of_isStableLevyProcess
