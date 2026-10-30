import Probability.Process.Stable.SmallDeviation.RangeComparison

#check ProbabilityTheory.IsStableLevyProcess.eventually_one_le_log_corridor_div_log_range_of_cdf
#check ProbabilityTheory.IsStableLevyProcess.eventually_one_le_log_corridor_div_log_range_of_measure_Iio_zero
#check ProbabilityTheory.IsStableLevyProcess.eventually_one_sub_le_log_range_div_log_corridor_of_cdf
#check ProbabilityTheory.IsStableLevyProcess.eventually_one_sub_le_log_range_div_log_corridor_of_measure_Iio_zero

open MeasureTheory
open Filter
open scoped NNReal Topology

example {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : ProbabilityTheory.IsStableLevyProcess α μ X P)
    (hcdf : 0 < ProbabilityTheory.cdf μ 0 ∧ ProbabilityTheory.cdf μ 0 < 1) :
    ∀ᶠ a : ℝ in nhdsWithin 0 (Set.Ioi 0),
      1 ≤ Real.log
        ((ProbabilityTheory.centeredCorridorProbability P X a).toReal) /
        Real.log
          ((ProbabilityTheory.rationalRangeProbability P X a).toReal) := by
  exact h.eventually_one_le_log_corridor_div_log_range_of_cdf hcdf

example {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : ProbabilityTheory.IsStableLevyProcess α μ X P)
    (hcdf : 0 < ProbabilityTheory.cdf μ 0 ∧ ProbabilityTheory.cdf μ 0 < 1)
    (ε : ℝ) (hε : 0 < ε) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ a : ℝ in nhdsWithin 0 (Set.Ioi 0),
      1 - δ ≤ Real.log
        ((ProbabilityTheory.rationalRangeProbability P X a).toReal) /
        Real.log
          ((ProbabilityTheory.expandedCenteredCorridorProbability P X ε a).toReal) := by
  exact h.eventually_one_sub_le_log_range_div_log_corridor_of_cdf
    hcdf ε hε δ hδ

example {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : ProbabilityTheory.IsStableLevyProcess α μ X P)
    (hleft : 0 < μ (Set.Iio 0) ∧ μ (Set.Iio 0) < 1) :
    ∀ᶠ a : ℝ in nhdsWithin 0 (Set.Ioi 0),
      1 ≤ Real.log
        ((ProbabilityTheory.centeredCorridorProbability P X a).toReal) /
        Real.log
          ((ProbabilityTheory.rationalRangeProbability P X a).toReal) := by
  exact h.eventually_one_le_log_corridor_div_log_range_of_measure_Iio_zero hleft

example {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : ProbabilityTheory.IsStableLevyProcess α μ X P)
    (hleft : 0 < μ (Set.Iio 0) ∧ μ (Set.Iio 0) < 1)
    (ε : ℝ) (hε : 0 < ε) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ a : ℝ in nhdsWithin 0 (Set.Ioi 0),
      1 - δ ≤ Real.log
        ((ProbabilityTheory.rationalRangeProbability P X a).toReal) /
        Real.log
          ((ProbabilityTheory.expandedCenteredCorridorProbability P X ε a).toReal) := by
  exact h.eventually_one_sub_le_log_range_div_log_corridor_of_measure_Iio_zero
    hleft ε hε δ hδ

#print axioms ProbabilityTheory.IsStableLevyProcess.eventually_one_le_log_corridor_div_log_range_of_cdf
#print axioms ProbabilityTheory.IsStableLevyProcess.eventually_one_le_log_corridor_div_log_range_of_measure_Iio_zero
#print axioms ProbabilityTheory.IsStableLevyProcess.eventually_one_sub_le_log_range_div_log_corridor_of_cdf
#print axioms ProbabilityTheory.IsStableLevyProcess.eventually_one_sub_le_log_range_div_log_corridor_of_measure_Iio_zero
